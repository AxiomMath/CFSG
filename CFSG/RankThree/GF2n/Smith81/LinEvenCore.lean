module

public import CFSG.RankThree.GF2n.Smith81.LinOddAssembly

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem hasDim_of_sit' (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) {m : ℕ}
    (hn : n = 2 * m) (hm : 2 ≤ m) {A : Subgroup G} {t : G} (hs : Sit M Q Z A t)
    (hQA : Q ⊓ QB A = ⊥) (hL : t ∈ Lgen M (LB M Q B)) :
    HasDimOn V₁ Z m t ∧ HasDimOn V₂ Z m t := by
  have h := lin115RankStatement_holds G M Q Z B A t n V₁ V₂ hc hS (by omega) hs hL hQA
  have e : n / 2 = m := by omega
  rwa [e] at h

theorem step5_core_even {W V : Subgroup G} {gA x : G} (hVW : conjSubgroup gA⁻¹ V ≤ W)
    (hdim : HasDimOn W Z 1 (gA⁻¹ * x * gA)) :
    Nat.card ↥⁅V, Subgroup.zpowers x⁆ ≤ Nat.card Z ^ 2 := by
  have h1 : ⁅conjSubgroup gA⁻¹ V, Subgroup.zpowers (gA⁻¹ * x * gA)⁆ =
      conjSubgroup gA⁻¹ ⁅V, Subgroup.zpowers x⁆ := by
    have := commutator_zpowers_conj gA⁻¹ V x
    simpa using this
  have h2 : Nat.card ↥⁅conjSubgroup gA⁻¹ V, Subgroup.zpowers (gA⁻¹ * x * gA)⁆ ≤
      Nat.card ↥(⁅W, Subgroup.zpowers (gA⁻¹ * x * gA)⁆ ⊔ Z) :=
    Subgroup.card_le_of_le (le_trans (Subgroup.commutator_mono hVW le_rfl) le_sup_left)
  rw [h1, card_conjSubgroup] at h2
  have h3 : Nat.card ↥(⁅W, Subgroup.zpowers (gA⁻¹ * x * gA)⁆ ⊔ Z) = Nat.card Z ^ (1 + 1) := hdim
  rw [h3] at h2
  exact h2

theorem OddSetup.QB_inf_QB_eq_bot_even {V V' : Subgroup G} (S : OddSetup M Q Z B V V')
    (hcond : Lin212CondProp M Q Z B V V') {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hQX : Q ⊓ QB X = ⊥) {m : ℕ} (hm : 3 ≤ m)
    (hVcard : Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card Z ^ m)
    {A : Subgroup G} (hA : IsZConjugate Z A) {a : G} (haA : a ∈ A) (haV : a ∈ V)
    (haC : a * x = x * a) (haZ : a ∉ Z) : QB A ⊓ QB X = ⊥ := by
  by_contra hne
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ Z.one_mem)
  have h3 := S.V_le_QB hcond.c4 hA haA haV haZ
  have hxN : x ∈ Subgroup.normalizer (A : Set G) :=
    hA.mem_normalizer_of_commute S.hyp ha1 haA haC.symm
  have hxQ := S.x_not_mem_QB hs hQX hA haA (S.VQ haV) ha1
  have hX : IsZConjugate Z X := hs.conj
  obtain ⟨gA, rfl⟩ := hA
  have hV := S.V_le_conj h3
  obtain ⟨-, hd1, hd2, -, -⟩ := cond_conj hcond S.hyp hX hs.mem hs.ne_one hxN hxQ hne
  have hq : 2 ≤ Nat.card Z := by have := S.hyp.q4; omega
  have hle : Nat.card ↥⁅V, Subgroup.zpowers x⁆ ≤ Nat.card Z ^ 2 := by
    rcases hV with h | h
    · have hVW : conjSubgroup gA⁻¹ V ≤ V := by
        have := (conjSubgroup_le_conjSubgroup_iff gA⁻¹).mpr h
        rwa [conjSubgroup_inv_conj] at this
      exact step5_core_even hVW hd1
    · have hVW : conjSubgroup gA⁻¹ V ≤ V' := by
        have := (conjSubgroup_le_conjSubgroup_iff gA⁻¹).mpr h
        rwa [conjSubgroup_inv_conj] at this
      exact step5_core_even hVW hd2
  rw [hVcard] at hle
  have hpow : Nat.card Z ^ 3 ≤ Nat.card Z ^ m := Nat.pow_le_pow_right (by omega) hm
  have h2 : Nat.card Z ^ 2 < Nat.card Z ^ 3 := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

theorem exists_sit_lgen (hF : LinSwapStatement) (hN : LinNonswapStatement)
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn3 : 3 ≤ n) {Y : Subgroup G} {y₁ : G}
    (hsY : Sit M Q Z Y y₁) : ∃ y₀, Sit M Q Z Y y₀ ∧ y₀ ∈ Lgen M (LB M Q B) := by
  have h12 := smith_1_12 hsY
  have hY4 : 4 ≤ Nat.card Y := by
    rw [IsZConjugate.card_eq (Z := Z) hsY.conj]; exact hc.hyp.q4
  obtain ⟨y₀, hy₀Y, hy₀1, hy₀V₁, -⟩ := exists_nonswap hY4 hsY.X_sq
    (fun t ht => hF G M Q Z B n V₁ V₂ hc hS hn3 t (h12.1 ht))
  have hsY0 : Sit M Q Z Y y₀ :=
    ⟨hsY.hyp, hsY.conj, hy₀Y, hy₀1, (h12.1 hy₀Y).1, fun hyQ => hy₀1 (by
      have : y₀ ∈ Y ⊓ Q := ⟨hy₀Y, hyQ⟩
      rw [h12.2, Subgroup.mem_bot] at this
      exact this)⟩
  exact ⟨y₀, hsY0,
    hN G M Q Z B n V₁ V₂ hc hS hn3 y₀ (h12.1 hy₀Y) (by rw [hsY0.x_sq]; exact Q.one_mem) hy₀V₁⟩

theorem step6_even (hF : LinSwapStatement) (hN : LinNonswapStatement)
    (hΓe : LinGammaEvenStatement) (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (S : OddSetup M Q Z B V₁ V₂) {m : ℕ} (hn : n = 2 * m) (hm : 2 ≤ m)
    {Y : Subgroup G} {y₁ : G} (hsY : Sit M Q Z Y y₁) (hQY : Q ⊓ QB Y = ⊥) (T : Subgroup G)
    (hTL : T ≤ Lx M Y)
    (hrank : ∀ a ∈ T, a ≠ 1 → a ∈ Lgen M (LB M Q B) → HasDimOn V₁ Z m a)
    (hcard : Nat.card Z ^ m < Nat.card T) : False := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨y₀, hsY0, hy₀L⟩ := exists_sit_lgen hF hN hc hS hn3 hsY
  obtain ⟨-, hV⟩ := hΓe G M Q Z B Y y₀ n m V₁ V₂ hc hS hn hm S.sqV S.sqV' hsY0 hy₀L hQY
  obtain ⟨hD, -, -⟩ := hV V₁ (Set.mem_insert _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hcard₁, -⟩ := hS.basic
  have hc₁ : Nat.card V₁ = Nat.card Z ^ (2 * m + 1) := by rw [hcard₁, hn]
  exact step6_aux S (e := 2 * m + 1) (d := m + 1) (r := m + 1) (by omega) (by omega)
    (by omega) (hF G M Q Z B n V₁ V₂ hc hS hn3) (hN G M Q Z B n V₁ V₂ hc hS hn3)
    hc₁ hsY0 hQY hD T hTL hrank (by rw [show m + 1 - 1 = m by omega]; exact hcard)

theorem lin28aEven_core (hF : LinSwapStatement) (hN : LinNonswapStatement)
    (hΓe : LinGammaEvenStatement) (hFour : LinFourCountStatement)
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) {m : ℕ} (hn : n = 2 * m)
    (hm : 2 ≤ m) (S : OddSetup M Q Z B V₁ V₂) (hcond : Lin212CondProp M Q Z B V₁ V₂)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) : Q ⊓ QB X ≠ ⊥ := by
  intro hQX
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hn3 : 3 ≤ n := by omega
  have hX4 : 4 ≤ Nat.card X := by
    rw [IsZConjugate.card_eq (Z := Z) hs.conj]; exact H.q4
  obtain ⟨x₀, hx₀X, hx₀1, hx₀V₁, -⟩ := exists_nonswap hX4 hs.X_sq
    (fun t ht => hF G M Q Z B n V₁ V₂ hc hS hn3 t (h12.1 ht))
  have hs0 : Sit M Q Z X x₀ :=
    ⟨hs.hyp, hs.conj, hx₀X, hx₀1, (h12.1 hx₀X).1, fun hxQ => hx₀1 (by
      have : x₀ ∈ X ⊓ Q := ⟨hx₀X, hxQ⟩
      rw [h12.2, Subgroup.mem_bot] at this
      exact this)⟩
  have hx₀L : x₀ ∈ Lgen M (LB M Q B) :=
    hN G M Q Z B n V₁ V₂ hc hS hn3 x₀ (h12.1 hx₀X) (by rw [hs0.x_sq]; exact Q.one_mem) hx₀V₁
  obtain ⟨hKx, hV⟩ := hΓe G M Q Z B X x₀ n m V₁ V₂ hc hS hn hm S.sqV S.sqV' hs0 hx₀L hQX
  obtain ⟨hD₁, hz₁, hc₁⟩ := hV V₁ (Set.mem_insert _ _)
  obtain ⟨g, hg⟩ := hs.conj
  obtain ⟨y₁, hsY, hQY⟩ := exists_sit_Y hs hQX hg
  have hQXg : QB X = conjSubgroup g Q := by rw [hg]; exact QB_conj_eq H g
  have hnormX : Subgroup.normalizer (X : Set G) = conjSubgroup g M := by
    rw [hg]; exact normalizer_conj_eq H g
  have hQYg : QB (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ Q := QB_conj_eq H g⁻¹
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm2 : m = 2 := by omega
    subst hm2
    have hn4 : n = 4 := by omega
    subst hn4
    obtain ⟨y₀, hsY0, hy₀L⟩ := exists_sit_lgen hF hN hc hS hn3 hsY
    have hLx : Lx M (conjSubgroup g⁻¹ Z) = conjSubgroup g⁻¹ (Kx Q X) := by
      unfold Lx Kx
      rw [conjSubgroup_inf, hnormX, conjSubgroup_inv_conj, hQYg]
    have hle := hFour G M Q Z B (conjSubgroup g⁻¹ Z) y₀ V₁ V₂ hc hS S.sqV S.sqV' hsY0 hy₀L hQY
    rw [hLx, card_conjSubgroup, hKx] at hle
    have hq : 2 ≤ Nat.card Z := by have := H.q4; omega
    have := Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z) |>.mp hle
    omega
  ·
    set S₁ : Subgroup G := V₁ ⊓ Subgroup.centralizer ({x₀} : Set G) with hS₁
    have hclaim : ∀ a ∈ S₁, a ∉ Z → ∀ A : Subgroup G, IsZConjugate Z A → a ∈ A →
        QB A ⊓ QB X = ⊥ := fun a ha haZ A hA haA =>
      S.QB_inf_QB_eq_bot_even hcond hs0 hQX hm3 hc₁ hA haA ha.1
        (Subgroup.mem_centralizer_singleton_iff.mp ha.2) haZ
    have hmemT : ∀ t ∈ conjSubgroup g⁻¹ S₁, g * t * g⁻¹ ∈ S₁ := fun t ht => by
      have := mem_conjSubgroup.mp ht
      simpa using this
    have hTL : conjSubgroup g⁻¹ S₁ ≤ Lx M (conjSubgroup g⁻¹ Z) := by
      intro t ht
      have ha := hmemT t ht
      refine ⟨?_, ?_⟩
      · have h1 : t ∈ conjSubgroup g⁻¹ Q := mem_conjSubgroup.mpr (by simpa using S.VQ ha.1)
        rw [← hQYg] at h1
        exact h1
      · have hcomm : g * t * g⁻¹ * x₀ = x₀ * (g * t * g⁻¹) :=
          Subgroup.mem_centralizer_singleton_iff.mp ha.2
        have hnorm := Tim77.mem_normalizer_of_commute_of_isTI hs0.X_isTI hs0.mem hs0.ne_one
          hcomm
        rw [hnormX, mem_conjSubgroup] at hnorm
        simpa [mul_assoc] using hnorm
    refine step6_even hF hN hΓe hc hS S hn hm hsY hQY (conjSubgroup g⁻¹ S₁) hTL ?_ ?_
    · intro t ht ht1 htL
      have ha := hmemT t ht
      have ha1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
        have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
        rw [this, h]; group)
      have htQ : t ∉ Q := by
        intro htQ
        have : t ∈ Q ⊓ QB (conjSubgroup g⁻¹ Z) := ⟨htQ, (hTL ht).1⟩
        rw [hQY, Subgroup.mem_bot] at this
        exact ht1 this
      by_cases haZ : g * t * g⁻¹ ∈ Z
      · have htY : t ∈ conjSubgroup g⁻¹ Z := by
          rw [mem_conjSubgroup]; simpa using haZ
        have h12Y := smith_1_12 hsY
        have hsYt : Sit M Q Z (conjSubgroup g⁻¹ Z) t :=
          ⟨hsY.hyp, hsY.conj, htY, ht1, (h12Y.1 htY).1, htQ⟩
        exact (hasDim_of_sit' hc hS hn hm hsYt hQY htL).1
      · obtain ⟨ga, z, hz, hz1, hae⟩ :=
          (S.p31 _ (S.VQ ha.1) ha1).mpr (Or.inl ha.1)
        have hA : IsZConjugate Z (conjSubgroup ga Z) := ⟨ga, rfl⟩
        have haA : g * t * g⁻¹ ∈ conjSubgroup ga Z := by
          rw [mem_conjSubgroup, hae]; simpa [mul_assoc] using hz
        have hQA := hclaim _ ha haZ _ hA haA
        have hAt : IsZConjugate Z (conjSubgroup g⁻¹ (conjSubgroup ga Z)) := hA.conj g⁻¹
        have htA : t ∈ conjSubgroup g⁻¹ (conjSubgroup ga Z) := by
          rw [mem_conjSubgroup]; simpa using haA
        have hsAt : Sit M Q Z (conjSubgroup g⁻¹ (conjSubgroup ga Z)) t :=
          ⟨H, hAt, htA, ht1, (hTL ht).2, htQ⟩
        have hQAt : Q ⊓ QB (conjSubgroup g⁻¹ (conjSubgroup ga Z)) = ⊥ := by
          rw [QB_conj_of_isZConjugate H hA]
          have h1 : Q = conjSubgroup g⁻¹ (QB X) := by rw [hQXg, conjSubgroup_inv_conj]
          have h2 : conjSubgroup g⁻¹ (QB X ⊓ QB (conjSubgroup ga Z)) = ⊥ := by
            rw [inf_comm, hQA]; exact Subgroup.map_bot _
          rw [conjSubgroup_inf] at h2
          rw [h1]; exact h2
        exact (hasDim_of_sit' hc hS hn hm hsAt hQAt htL).1
    · rw [card_conjSubgroup, hS₁, hD₁]
      exact Nat.pow_lt_pow_right (by have := H.q4; omega) (by omega)

end CFSG.RankThree.GF2n.Smith81

module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.LocalAnalysis.RankThreeUC.S15 (card_le_pRank_of_components_aux1_gen
  card_le_pRank_of_components_aux2 card_le_pRank_of_components_aux3
  card_le_pRank_of_components_gen perfect_le_normalizer_component_aux2
  perfect_le_normalizer_component_aux3 layerIn_normal_aux1)

section Orbits

variable {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω]

theorem uc22s206m_pow_smul_inj {t : Γ} (ht7 : t ^ 7 = 1) {ω : Ω} (htω : t • ω ≠ ω) {a b : ℕ}
    (ha : a < 7) (hb : b < 7) (h : t ^ a • ω = t ^ b • ω) : a = b := by
  have key : ∀ d : ℕ, 0 < d → d < 7 → t ^ d • ω ≠ ω := by
    intro d hd0 hd7 hd
    apply htω
    have h1 : ∀ u : ℕ, t ^ (d * u) • ω = ω := fun u => by
      rw [pow_mul]
      exact MulAction.mem_stabilizer_iff.mp
        ((MulAction.stabilizer Γ ω).pow_mem (MulAction.mem_stabilizer_iff.mpr hd) u)
    have hmod : ∀ n : ℕ, t ^ n = t ^ (n % 7) := fun n => by
      conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, ht7, one_pow, one_mul]
    interval_cases d
    · simpa using hd
    · have h2 := h1 4
      rwa [hmod, show 2 * 4 % 7 = 1 from rfl, pow_one] at h2
    · have h2 := h1 5
      rwa [hmod, show 3 * 5 % 7 = 1 from rfl, pow_one] at h2
    · have h2 := h1 2
      rwa [hmod, show 4 * 2 % 7 = 1 from rfl, pow_one] at h2
    · have h2 := h1 3
      rwa [hmod, show 5 * 3 % 7 = 1 from rfl, pow_one] at h2
    · have h2 := h1 6
      rwa [hmod, show 6 * 6 % 7 = 1 from rfl, pow_one] at h2
  rcases lt_trichotomy a b with hab | hab | hab
  · refine absurd ?_ (key (b - a) (by omega) (by omega))
    rw [show b = a + (b - a) by omega, pow_add, mul_smul] at h
    exact (smul_left_cancel _ h).symm
  · exact hab
  · refine absurd ?_ (key (a - b) (by omega) (by omega))
    rw [show a = b + (a - b) by omega, pow_add, mul_smul] at h
    exact smul_left_cancel _ h

theorem uc22s206m_two_orbits {s t : Γ} (hs3 : s ^ 3 = 1) (ht7 : t ^ 7 = 1)
    (hst : s * t = t ^ 2 * s) {ω : Ω} (htω : t • ω ≠ ω) :
    ∃ α β : Ω, (∃ g : Γ, α = g • ω) ∧ (∃ g : Γ, β = g • ω) ∧ s • α ≠ α ∧ s • β ≠ β ∧
      β ≠ α ∧ β ≠ s • α ∧ β ≠ s • s • α := by
  have hpow : ∀ n : ℕ, s * t ^ n = t ^ (2 * n) * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hst, ← mul_assoc, ← pow_add,
        show 2 * n + 2 = 2 * (n + 1) by omega]
  have hsm : ∀ (n : ℕ) (ω' : Ω), s • t ^ n • ω' = t ^ (2 * n) • s • ω' := fun n ω' => by
    rw [smul_smul, hpow, mul_smul]
  by_cases hfix : ∃ j : ℕ, s • t ^ j • ω = t ^ j • ω
  · obtain ⟨j, hj⟩ := hfix
    obtain ⟨ω', hω'⟩ : ∃ ω' : Ω, t ^ j • ω = ω' := ⟨_, rfl⟩
    rw [hω'] at hj
    have ht' : t • ω' ≠ ω' := by
      intro h
      apply htω
      rw [← hω', smul_smul, (Commute.self_pow t j).eq, mul_smul] at h
      exact smul_left_cancel _ h
    have hne : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → t ^ a • ω' ≠ t ^ b • ω' :=
      fun a b ha hb hab h => hab (uc22s206m_pow_smul_inj ht7 ht' ha hb h)
    have e : ∀ n : ℕ, s • t ^ n • ω' = t ^ (2 * n) • ω' := fun n => by rw [hsm, hj]
    refine ⟨t ^ 1 • ω', t ^ 3 • ω', ⟨t ^ 1 * t ^ j, by rw [mul_smul, hω']⟩,
      ⟨t ^ 3 * t ^ j, by rw [mul_smul, hω']⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e]; exact hne _ _ (by norm_num) (by norm_num) (by norm_num)
    · rw [e]; exact hne _ _ (by norm_num) (by norm_num) (by norm_num)
    · exact hne _ _ (by norm_num) (by norm_num) (by norm_num)
    · rw [e]; exact hne _ _ (by norm_num) (by norm_num) (by norm_num)
    · rw [e, e]; exact hne _ _ (by norm_num) (by norm_num) (by norm_num)
  · push Not at hfix
    have hne : ∀ a b : ℕ, a < 7 → b < 7 → a ≠ b → t ^ a • ω ≠ t ^ b • ω :=
      fun a b ha hb hab h => hab (uc22s206m_pow_smul_inj ht7 htω ha hb h)
    refine ⟨t ^ 0 • ω, t ^ 1 • ω, ⟨t ^ 0, rfl⟩, ⟨t ^ 1, rfl⟩, hfix 0, hfix 1,
      hne _ _ (by norm_num) (by norm_num) (by norm_num), fun he => ?_, fun he => ?_⟩
    · rw [pow_zero, one_smul] at he
      apply hfix 6
      rw [hsm, ← he, smul_smul, ← pow_add, show 2 * 6 + 1 = 7 + 6 from rfl, pow_add t 7 6, ht7,
        one_mul]
    · rw [pow_zero, one_smul] at he
      have e1 : t ^ (2 * 1) • s • ω = ω := by
        rw [← hsm 1 ω, he, smul_smul, smul_smul, ← pow_three', hs3, one_smul]
      have e2 : s • ω = t ^ 5 • ω := by
        have h : t ^ 5 • t ^ (2 * 1) • s • ω = t ^ 5 • ω := by rw [e1]
        rw [smul_smul, ← pow_add, show 5 + 2 * 1 = 7 from rfl, ht7, one_smul] at h
        exact h
      apply hfix 2
      rw [hsm, e2, smul_smul, ← pow_add, show 2 * 2 + 5 = 7 + 2 from rfl, pow_add t 7 2, ht7,
        one_mul]

end Orbits

theorem uc22s206m_smul_component {Y : Type} [Group Y] {J : Subgroup Y} (hJ : IsComponentOf J ⊤)
    (g : ConjAct Y) :
    IsComponentOf (g • J) ⊤ ∧
      Nat.card (↥(g • J) ⧸ center ↥(g • J)) = Nat.card (↥J ⧸ center ↥J) := by
  obtain ⟨y, rfl⟩ := ConjAct.toConjAct.surjective g
  rw [perfect_le_normalizer_component_aux3]
  exact ⟨layerIn_normal_aux1 ⊤ hJ y, perfect_le_normalizer_component_aux2 J y⟩

theorem uc22s206m_exists_elem {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr : r.Prime)
    {A : Subgroup Y} (hrA : r ∣ Nat.card (↥A ⧸ center ↥A)) :
    ∃ a ∈ A, a ∉ centralizer (A : Set Y) ∧ ∃ n : ℕ, a ^ r ^ n = 1 := by
  obtain ⟨a, haZ, n, han⟩ := card_le_pRank_of_components_aux2 hr hrA
  refine ⟨a, a.2, fun hc => haZ ?_, n, by simpa using congrArg Subtype.val han⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) g.1 g.2)

theorem uc22s206m_two_le_pRank {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hr : r.Prime)
    {a u b v : Y} {k l : ℕ} (ha : a ^ r ^ k = 1) (hb : b ^ r ^ l = 1) (hau : Commute a u)
    (hbv : Commute b v) (hd : Commute (a * u) (b * v)) {Z₁ Z₂ : Subgroup Y} (haZ : a ∉ Z₁)
    (huZ : u ∈ Z₁) (hdZ₁ : b * v ∈ Z₁) (hbZ : b ∉ Z₂) (hvZ : v ∈ Z₂) (hdZ₂ : a * u ∈ Z₂)
    {H : Subgroup Y} (h₁ : a * u ∈ H) (h₂ : b * v ∈ H) : 2 ≤ pRank r H := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hker : ∀ m n : ℤ, (a * u) ^ m * (b * v) ^ n = 1 → (r : ℤ) ∣ m ∧ (r : ℤ) ∣ n := by
    intro m n h
    refine ⟨?_, ?_⟩
    · rw [hau.mul_zpow, mul_assoc] at h
      refine card_le_pRank_of_components_aux3 hr ha Z₁ haZ ?_
      rw [eq_inv_of_mul_eq_one_left h]
      exact Z₁.inv_mem (Z₁.mul_mem (Z₁.zpow_mem huZ m) (Z₁.zpow_mem hdZ₁ n))
    · rw [hbv.mul_zpow] at h
      refine card_le_pRank_of_components_aux3 hr hb Z₂ hbZ ?_
      rw [eq_mul_inv_of_mul_eq (eq_inv_of_mul_eq_one_right h)]
      exact Z₂.mul_mem (Z₂.inv_mem (Z₂.zpow_mem hdZ₂ m)) (Z₂.inv_mem (Z₂.zpow_mem hvZ n))
  let Ψ : Multiplicative ℤ × Multiplicative ℤ →* Y :=
    (zpowersHom Y (a * u)).noncommCoprod (zpowersHom Y (b * v)) fun m n => by
      rw [zpowersHom_apply, zpowersHom_apply]
      exact (hd.zpow_left _).zpow_right _
  have hΨ : ∀ g, Ψ g = (a * u) ^ Multiplicative.toAdd g.1 * (b * v) ^ Multiplicative.toAdd g.2 :=
    fun g => by rw [MonoidHom.noncommCoprod_apply, zpowersHom_apply, zpowersHom_apply]
  let q : Multiplicative ℤ →* Multiplicative (ZMod r) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod r))
  have hq : ∀ z : Multiplicative ℤ, (r : ℤ) ∣ Multiplicative.toAdd z → q z = 1 := by
    intro z hz
    show Multiplicative.ofAdd ((Multiplicative.toAdd z : ℤ) : ZMod r) = 1
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ r).2 hz]
    rfl
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨c, hc⟩ := ZMod.intCast_surjective (n := r) (Multiplicative.toAdd z)
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    show Multiplicative.ofAdd ((c : ℤ) : ZMod r) = z
    rw [hc]
    rfl
  let Q : Multiplicative ℤ × Multiplicative ℤ →*
      Multiplicative (ZMod r) × Multiplicative (ZMod r) := q.prodMap q
  have hkerQ : Ψ.rangeRestrict.ker ≤ Q.ker := by
    rintro ⟨m, n⟩ hg
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hΨ] at hg
    obtain ⟨hm, hn⟩ := hker _ _ hg
    rw [MonoidHom.mem_ker]
    show (q m, q n) = (1, 1)
    rw [hq m hm, hq n hn]
  have hQsurj : Function.Surjective Q := by
    rintro ⟨z₁, z₂⟩
    obtain ⟨c₁, rfl⟩ := hqsurj z₁
    obtain ⟨c₂, rfl⟩ := hqsurj z₂
    exact ⟨(c₁, c₂), rfl⟩
  have hexp : ∀ z : Multiplicative (ZMod r), z ^ r = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    simp
  have hQexp : ∀ z : Multiplicative (ZMod r) × Multiplicative (ZMod r), z ^ r = 1 :=
    fun z => Prod.ext (hexp z.1) (hexp z.2)
  have hQcard : Nat.card (Multiplicative (ZMod r) × Multiplicative (ZMod r)) = r ^ 2 := by
    rw [Nat.card_prod, (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod r), sq]
  have hAcomm : ∀ c ∈ Ψ.range, ∀ c' ∈ Ψ.range, c * c' = c' * c := by
    rintro _ ⟨g, rfl⟩ _ ⟨g', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm g g']
  have hΨH : Ψ.range ≤ H := by
    rintro _ ⟨g, rfl⟩
    rw [hΨ]
    exact H.mul_mem (H.zpow_mem h₁ _) (H.zpow_mem h₂ _)
  let ψ := Ψ.rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective Ψ) ⟨Q, hkerQ⟩
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨g, hg⟩ := hQsurj z
    refine ⟨Ψ.rangeRestrict g, ?_⟩
    have h1 := MonoidHom.liftOfRightInverse_comp_apply Ψ.rangeRestrict _
      (Function.rightInverse_surjInv (MonoidHom.rangeRestrict_surjective Ψ)) ⟨Q, hkerQ⟩ g
    rw [← hg]
    exact h1
  exact card_le_pRank_of_components_aux1_gen hr Ψ.range hAcomm hQcard hQexp ψ hψ hΨH

theorem uc22s206m_diag {Y : Type} [Group Y] [Finite Y] {x y : Y} (hx3 : x ^ 3 = 1)
    (hy7 : y ^ 7 = 1) (hxy : x * y * x⁻¹ = y ^ 2) {J : Subgroup Y} (hJ : IsComponentOf J ⊤)
    (hyJ : y ∉ normalizer (J : Set Y)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrJ : r ∣ Nat.card (↥J ⧸ center ↥J)) :
    7 ≤ pRank r (⊤ : Subgroup Y) ∧
      (∃ D : Subgroup Y, IsPGroup r D ∧ x ∈ normalizer (D : Set Y) ∧ ⁅zpowers x, D⁆ ≠ ⊥) ∧
      ∃ E : Subgroup Y, E ≤ centralizer (zpowers x : Set Y) ∧ IsElemAbelian r E ∧
        Nat.card E = r ^ 2 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨s, hs⟩ : ∃ s : ConjAct Y, ConjAct.toConjAct x = s := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ConjAct Y, ConjAct.toConjAct y = t := ⟨_, rfl⟩
  have hsc : ∀ c : Y, s • c = x * c * x⁻¹ := fun c => by rw [← hs, ConjAct.toConjAct_smul]
  have hs3 : s ^ 3 = 1 := by rw [← hs, ← map_pow, hx3, map_one]
  have ht7 : t ^ 7 = 1 := by rw [← ht, ← map_pow, hy7, map_one]
  have hst : s * t = t ^ 2 * s := by
    rw [← hs, ← ht, ← map_pow, ← map_mul, ← map_mul, ← hxy]
    congr 1
    group
  have htJ : t • J ≠ J := fun h =>
    hyJ (Subgroup.conjAct_pointwise_smul_iff.mp (by rw [ht]; exact h))
  have hcK : ∀ K : Subgroup Y, (∃ g : ConjAct Y, K = g • J) →
      IsComponentOf K ⊤ ∧ r ∣ Nat.card (↥K ⧸ center ↥K) := by
    rintro K ⟨g, rfl⟩
    obtain ⟨h1, h2⟩ := uc22s206m_smul_component hJ g
    refine ⟨h1, ?_⟩
    rw [h2]
    exact hrJ
  have hsK : ∀ K : Subgroup Y, (∃ g : ConjAct Y, K = g • J) →
      ∃ g : ConjAct Y, s • K = g • J := by
    rintro K ⟨g, rfl⟩
    exact ⟨s * g, smul_smul s g J⟩
  have h7 : 7 ≤ CFSG.Open.pRank r (⊤ : Subgroup Y) := by
    have hinj : Set.InjOn (fun n : ℕ => t ^ n • J) (Finset.range 7 : Set ℕ) :=
      fun a ha b hb hab => uc22s206m_pow_smul_inj ht7 htJ
        (Finset.mem_range.mp (Finset.mem_coe.mp ha)) (Finset.mem_range.mp (Finset.mem_coe.mp hb))
        hab
    have hcard := (Finset.card_image_of_injOn hinj).trans (Finset.card_range 7)
    have h := card_le_pRank_of_components_gen ((Finset.range 7).image fun n : ℕ => t ^ n • J)
      (fun K hK => by
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hK
        exact (hcK _ ⟨t ^ n, rfl⟩).1)
      ⊤ (fun _ _ => le_top) hr hr2 (fun K hK => by
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hK
        exact (hcK _ ⟨t ^ n, rfl⟩).2)
    rwa [hcard] at h
  obtain ⟨A, B, hA, hB, hA01, hB01, hBA, hBsA, hBssA⟩ := uc22s206m_two_orbits hs3 ht7 hst htJ
  obtain ⟨hAc, hAr⟩ := hcK A hA
  obtain ⟨hsAc, -⟩ := hcK _ (hsK A hA)
  obtain ⟨hssAc, -⟩ := hcK _ (hsK _ (hsK A hA))
  obtain ⟨hBc, hBr⟩ := hcK B hB
  obtain ⟨hsBc, -⟩ := hcK _ (hsK B hB)
  obtain ⟨hssBc, -⟩ := hcK _ (hsK _ (hsK B hB))
  have hsss : ∀ K : Subgroup Y, s • s • s • K = K := fun K => by
    rw [smul_smul, smul_smul, ← pow_three', hs3, one_smul]
  have hA02 : s • s • A ≠ A := fun h =>
    hA01 ((by rw [h] : s • A = s • s • s • A).trans (hsss A))
  have hA12 : s • s • A ≠ s • A := fun h => hA01 (smul_left_cancel s h)
  have hB02 : s • s • B ≠ B := fun h =>
    hB01 ((by rw [h] : s • B = s • s • s • B).trans (hsss B))
  have hsBA : s • B ≠ A := fun h => hBssA (by rw [← h, hsss])
  have hsBsA : s • B ≠ s • A := fun h => hBA (smul_left_cancel s h)
  have hsBssA : s • B ≠ s • s • A := fun h => hBsA (smul_left_cancel s h)
  have hssBA : s • s • B ≠ A := fun h => hBsA (by rw [← h, hsss])
  have hssBsA : s • s • B ≠ s • A := fun h => hsBA (smul_left_cancel s h)
  have hssBssA : s • s • B ≠ s • s • A := fun h => hsBsA (smul_left_cancel s h)
  obtain ⟨a, haA, haZ, ka, ha⟩ := uc22s206m_exists_elem hr hAr
  obtain ⟨b, hbB, hbZ, kb, hb⟩ := uc22s206m_exists_elem hr hBr
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, x * a * x⁻¹ = a₁ := ⟨_, rfl⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, x * a₁ * x⁻¹ = a₂ := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, x * b * x⁻¹ = b₁ := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b₂, x * b₁ * x⁻¹ = b₂ := ⟨_, rfl⟩
  have hx3c : ∀ c : Y, x * (x * (x * c * x⁻¹) * x⁻¹) * x⁻¹ = c := fun c => by
    rw [← hsc c, ← hsc (s • c), ← hsc (s • s • c), smul_smul, smul_smul, ← pow_three', hs3,
      one_smul]
  have ha₃ : x * a₂ * x⁻¹ = a := by rw [← ha₂, ← ha₁]; exact hx3c a
  have hb₃ : x * b₂ * x⁻¹ = b := by rw [← hb₂, ← hb₁]; exact hx3c b
  have hmem : ∀ {c : Y} {K : Subgroup Y}, c ∈ K → x * c * x⁻¹ ∈ s • K := fun {c K} hc => by
    rw [← hsc]
    exact Subgroup.smul_mem_pointwise_smul c s K hc
  have ha₁A : a₁ ∈ s • A := by rw [← ha₁]; exact hmem haA
  have ha₂A : a₂ ∈ s • s • A := by rw [← ha₂]; exact hmem ha₁A
  have hb₁B : b₁ ∈ s • B := by rw [← hb₁]; exact hmem hbB
  have hb₂B : b₂ ∈ s • s • B := by rw [← hb₂]; exact hmem hb₁B
  have hcm : ∀ {K₁ K₂ : Subgroup Y}, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ → K₁ ≠ K₂ →
      ∀ {c₁ c₂ : Y}, c₁ ∈ K₁ → c₂ ∈ K₂ → Commute c₁ c₂ := by
    intro K₁ K₂ h₁ h₂ hne c₁ c₂ hc₁ hc₂
    have h := Subgroup.commutator_mem_commutator hc₁ hc₂
    rw [CFSG.ComponentClassification.LocalComponents.commute_of_ne K₁ K₂ h₁ h₂ hne,
      Subgroup.mem_bot] at h
    exact commutatorElement_eq_one_iff_commute.mp h
  have hcz : ∀ {K₁ K₂ : Subgroup Y}, IsComponentOf K₁ ⊤ → IsComponentOf K₂ ⊤ → K₁ ≠ K₂ →
      ∀ {c : Y}, c ∈ K₂ → c ∈ centralizer (K₁ : Set Y) := fun h₁ h₂ hne _ hc =>
    mem_centralizer_iff.mpr fun _ hk => (hcm h₁ h₂ hne hk hc).eq
  have hau : Commute a (a₁ * a₂) :=
    (hcm hAc hsAc hA01.symm haA ha₁A).mul_right (hcm hAc hssAc hA02.symm haA ha₂A)
  have hbv : Commute b (b₁ * b₂) :=
    (hcm hBc hsBc hB01.symm hbB hb₁B).mul_right (hcm hBc hssBc hB02.symm hbB hb₂B)
  have hdB : ∀ {K : Subgroup Y}, IsComponentOf K ⊤ → K ≠ B → K ≠ s • B → K ≠ s • s • B →
      ∀ {c : Y}, c ∈ K → Commute c (b * (b₁ * b₂)) := fun hK h0 h1 h2 _ hc =>
    (hcm hK hBc h0 hc hbB).mul_right
      ((hcm hK hsBc h1 hc hb₁B).mul_right (hcm hK hssBc h2 hc hb₂B))
  have hd : Commute (a * (a₁ * a₂)) (b * (b₁ * b₂)) :=
    (hdB hAc hBA.symm hsBA.symm hssBA.symm haA).mul_left
      ((hdB hsAc hBsA.symm hsBsA.symm hssBsA.symm ha₁A).mul_left
        (hdB hssAc hBssA.symm hsBssA.symm hssBssA.symm ha₂A))
  have huZ : a₁ * a₂ ∈ centralizer (A : Set Y) :=
    mul_mem (hcz hAc hsAc hA01.symm ha₁A) (hcz hAc hssAc hA02.symm ha₂A)
  have hdZ₁ : b * (b₁ * b₂) ∈ centralizer (A : Set Y) :=
    mul_mem (hcz hAc hBc hBA.symm hbB)
      (mul_mem (hcz hAc hsBc hsBA.symm hb₁B) (hcz hAc hssBc hssBA.symm hb₂B))
  have hvZ : b₁ * b₂ ∈ centralizer (B : Set Y) :=
    mul_mem (hcz hBc hsBc hB01.symm hb₁B) (hcz hBc hssBc hB02.symm hb₂B)
  have hdZ₂ : a * (a₁ * a₂) ∈ centralizer (B : Set Y) :=
    mul_mem (hcz hBc hAc hBA haA) (mul_mem (hcz hBc hsAc hBsA ha₁A) (hcz hBc hssAc hBssA ha₂A))
  have hcx : ∀ {d : Y}, x * d * x⁻¹ = d → d ∈ centralizer (zpowers x : Set Y) := by
    intro d hd
    have hxd : Commute x d := mul_inv_eq_iff_eq_mul.mp hd
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (hxd.zpow_left k).eq
  have hconj : ∀ c₁ c₂ : Y, x * (c₁ * c₂) * x⁻¹ = x * c₁ * x⁻¹ * (x * c₂ * x⁻¹) := fun _ _ => by
    group
  have hd₁ : a * (a₁ * a₂) ∈ centralizer (zpowers x : Set Y) := by
    refine hcx ?_
    rw [hconj, hconj, ha₁, ha₂, ha₃, ← mul_assoc]
    exact hau.eq.symm
  have hd₂ : b * (b₁ * b₂) ∈ centralizer (zpowers x : Set Y) := by
    refine hcx ?_
    rw [hconj, hconj, hb₁, hb₂, hb₃, ← mul_assoc]
    exact hbv.eq.symm
  obtain ⟨E, hEH, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (uc22s206m_two_le_pRank hr ha hb hau hbv hd haZ huZ hdZ₁ hbZ hvZ hdZ₂ hd₁ hd₂)
  have hzp : ∀ {c : Y} {n : ℕ}, c ^ r ^ n = 1 → IsPGroup r (zpowers c) := by
    intro c n hc
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one hc)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hconjr : ∀ {c : Y}, c ^ r ^ ka = 1 → (x * c * x⁻¹) ^ r ^ ka = 1 := fun hc => by
    rw [conj_pow, hc, mul_one, mul_inv_cancel]
  have ha₁r : a₁ ^ r ^ ka = 1 := by rw [← ha₁]; exact hconjr ha
  have ha₂r : a₂ ^ r ^ ka = 1 := by rw [← ha₂]; exact hconjr ha₁r
  have hzn : ∀ {c₁ c₂ : Y}, Commute c₁ c₂ → zpowers c₁ ≤ normalizer (zpowers c₂ : Set Y) := by
    intro c₁ c₂ hc
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (hc.symm.zpow_left k).eq
  refine ⟨h7, ⟨zpowers a ⊔ zpowers a₁ ⊔ zpowers a₂, ?_, ?_, ?_⟩, E, hEH, hE, hEcard⟩
  · exact IsPGroup.to_sup_of_normal_right' (IsPGroup.to_sup_of_normal_right' (hzp ha) (hzp ha₁r)
      (hzn (hcm hAc hsAc hA01.symm haA ha₁A))) (hzp ha₂r)
      (sup_le (hzn (hcm hAc hssAc hA02.symm haA ha₂A)) (hzn (hcm hsAc hssAc hA12.symm ha₁A ha₂A)))
  · rw [← Subgroup.conjAct_pointwise_smul_iff, perfect_le_normalizer_component_aux3]
    simp only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [ha₁, ha₂, ha₃, sup_comm, ← sup_assoc]
  · intro hbot
    have hc := Subgroup.commutator_mem_commutator (mem_zpowers x)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers a)) :
        a ∈ zpowers a ⊔ zpowers a₁ ⊔ zpowers a₂)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one, ha₁] at hc
    apply haZ
    rw [← hc]
    exact hcz hAc hsAc hA01.symm ha₁A

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

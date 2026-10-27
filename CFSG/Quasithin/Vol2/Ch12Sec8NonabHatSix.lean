module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatVec
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatSwap
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

theorem mem_normalizer_of_conj_mem_of_finite {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {x : G} (hx : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  classical
  let φ : K → K := fun k => ⟨x * k * x⁻¹, hx k k.2⟩
  have hφ : Function.Injective φ := fun a b hab => by
    have h1 : x * (a : G) * x⁻¹ = x * b * x⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hφs := Finite.surjective_of_injective hφ
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hx y hy, fun hy => ?_⟩
  obtain ⟨k, hk⟩ := hφs ⟨x * y * x⁻¹, hy⟩
  have h1 : x * (k : G) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hk
  have h2 : (k : G) = y := mul_left_cancel (mul_right_cancel h1)
  rw [← h2]
  exact k.2

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem not_rconj_wOfU_le_wOfU (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) : ¬ rconj (wOfU T M) g ≤ wOfU T M := by
  classical
  intro hXW
  have hE : wOfU T M ⊓ rconj (wOfU T M) g = rconj (wOfU T M) g := inf_eq_right.mpr hXW
  have hEabel := (h.lemma_12_8_11_two hU hg).1
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := h.lemma_12_8_13_one hU hg
  have hXV : rconj (wOfU T M) g ≤ VZ T M := by
    intro x hx
    have hxE : x ∈ wOfU T M ⊓ rconj (wOfU T M) g := by rw [hE]; exact hx
    rw [← h.lemma_12_8_11_four hU hg]
    refine ⟨hxE, normalizer_le_normalizer_centerOf _
      (Subgroup.le_normalizer (wOfU_le_uOfL22 T M (hXW hx))), fun x' hx' => ?_⟩
    have hx'E : x' ∈ wOfU T M ⊓ rconj (wOfU T M) g := by rw [hE]; exact hx'
    have hcomm : x * x' = x' * x :=
      congrArg Subtype.val (hEabel.1.is_comm.comm ⟨x, hxE⟩ ⟨x', hx'E⟩)
    have e : x * x' * x⁻¹ * x'⁻¹ = 1 := by
      calc x * x' * x⁻¹ * x'⁻¹ = (x' * x) * x⁻¹ * x'⁻¹ := by rw [hcomm]
        _ = 1 := by group
    rw [e]
    exact Subgroup.one_mem _
  have hXeqV : rconj (wOfU T M) g = VZ T M := le_antisymm hXV (hVE.trans inf_le_right)
  have hWV : wOfU T M = VZ T M := by
    have h2 : Nat.card (rconj (wOfU T M) g) = Nat.card (VZ T M) := by rw [hXeqV]
    have hcard : Nat.card (wOfU T M) ≤ Nat.card (VZ T M) :=
      ((card_rconj_eq (wOfU T M) g).symm.trans h2).le
    exact (Subgroup.eq_of_le_of_card_ge h.VZ_le_wOfU hcard).symm
  obtain ⟨z, hzZ, hz1, hall⟩ := h.exists_zgen
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  have hcases := h.VZ_cases hzZ hz1 haV haZ
  have hzV : z ∈ VZ T M := omegaOneCenter_le_VZ T M hzZ
  have haU : a ∈ uOfL22 T M := VZ_le_uOfL22 T M haV
  have hV1 : ∀ w ∈ VZ T M, w * w = 1 := fun w hw => by
    simpa [sq] using h.almostSpecialHyp_g1.sq_eq_one_of_mem_V hw
  have haa : a * a = 1 := hV1 a haV
  have hzz : z * z = 1 := hV1 z hzV
  have hzc : ∀ u ∈ uOfL22 T M, z * u = u * z := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hzZ).2 u hu).symm
  have hHN : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      x ∈ Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx => h.g1_le_normalizer_uOfL22 hx
  have hHz : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      x * z * x⁻¹ = z := by
    intro x hx
    have h1 := Subgroup.mem_centralizer_iff.mp hx z hzZ
    calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [h1]
      _ = z := by group
  have hb : ∀ x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      x ∉ Subgroup.normalizer (VZ T M : Set G) →
        x * a * x⁻¹ ∈ uOfL22 T M ∧ x * a * x⁻¹ ∉ VZ T M ∧
          (x * a * x⁻¹) * (x * a * x⁻¹) = 1 := by
    intro x hx hxN
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHN x hx) a).mp haU, fun hbV => hxN ?_, ?_⟩
    · apply mem_normalizer_of_conj_mem_of_finite
      intro k hk
      rcases hcases k hk with h1 | h1 | h1 | h1
      · rw [h1]
        simp
      · rw [h1, hHz x hx]
        exact hzV
      · rw [h1]
        exact hbV
      · rw [h1]
        have e : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
        rw [e, hHz x hx]
        exact (VZ T M).mul_mem hzV hbV
    · calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
        _ = 1 := by rw [haa]; group
  have hK : ∀ x₁ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      x₁ ∉ Subgroup.normalizer (VZ T M : Set G) →
      ∀ x₂ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      x₂ ∉ Subgroup.normalizer (VZ T M : Set G) →
        x₁⁻¹ * x₂ ∈ Subgroup.normalizer (VZ T M : Set G) := by
    intro x₁ hx₁ hx₁N x₂ hx₂ hx₂N
    obtain ⟨hb₁U, hb₁V, hb₁sq⟩ := hb x₁ hx₁ hx₁N
    obtain ⟨hb₂U, hb₂V, hb₂sq⟩ := hb x₂ hx₂ hx₂N
    obtain ⟨b₁, hb₁def⟩ : ∃ b, b = x₁ * a * x₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨b₂, hb₂def⟩ : ∃ b, b = x₂ * a * x₂⁻¹ := ⟨_, rfl⟩
    rw [← hb₁def] at hb₁U hb₁V hb₁sq
    rw [← hb₂def] at hb₂U hb₂V hb₂sq
    have hb₁W : b₁ ∉ wOfU T M := by rw [hWV]; exact hb₁V
    have hvV : b₁⁻¹ * b₂ ∈ VZ T M := by
      rcases h.mem_wOfU_or_inv_mul_mem hb₁U hb₂U hb₁W with h1 | h1
      · rw [hWV] at h1
        exact absurd h1 hb₂V
      · rw [hWV] at h1
        exact h1
    have hb₁N : b₁ ∈ Subgroup.normalizer (VZ T M : Set G) := h.uOfL22_le_normalizer_VZ hb₁U
    have hb₁Z : b₁ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      h.uOfL22_le_g1 hb₁U
    have hb₁C : b₁ ∉ Subgroup.centralizer (VZ T M : Set G) := fun hc => hb₁W ⟨hb₁U, hc⟩
    have hconj_a : b₁ * a * b₁⁻¹ = z * a :=
      h.conj_eq_of_not_centralizes hzZ hz1 haV haZ hb₁N hb₁Z hb₁C
    have hb₁z : b₁ * z * b₁⁻¹ = z := by
      have h1 := hzc b₁ hb₁U
      calc b₁ * z * b₁⁻¹ = (z * b₁) * b₁⁻¹ := by rw [h1]
        _ = z := by group
    have hconjV : ∀ v ∈ VZ T M, v ≠ 1 → v ≠ z → b₁ * v * b₁⁻¹ = z * v := by
      intro v hv hv1 hvz
      rcases hcases v hv with h1 | h1 | h1 | h1
      · exact absurd h1 hv1
      · exact absurd h1 hvz
      · rw [h1]
        exact hconj_a
      · rw [h1]
        have e : b₁ * (z * a) * b₁⁻¹ = (b₁ * z * b₁⁻¹) * (b₁ * a * b₁⁻¹) := by group
        rw [e, hb₁z, hconj_a]
    obtain ⟨v, hvdef⟩ : ∃ v, v = b₁⁻¹ * b₂ := ⟨_, rfl⟩
    rw [← hvdef] at hvV
    have hb₂eq : b₂ = b₁ * v := by rw [hvdef]; group
    have hv1z : v = 1 ∨ v = z := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hv1, hvz⟩ := hcon
      have h1 := hconjV v hvV hv1 hvz
      have h2 : b₂ * b₂ = z := by
        calc b₂ * b₂ = (b₁ * v * b₁⁻¹) * (b₁ * b₁) * v := by rw [hb₂eq]; group
          _ = (z * v) * 1 * v := by rw [h1, hb₁sq]
          _ = z * (v * v) := by group
          _ = z := by rw [hV1 v hvV, mul_one]
      exact hz1 (h2.symm.trans hb₂sq)
    have hvx : x₁⁻¹ * v * x₁ = v := by
      rcases hv1z with h1 | h1
      · rw [h1]
        group
      · rw [h1]
        have := hHz x₁⁻¹ (Subgroup.inv_mem _ hx₁)
        simpa using this
    have hcH : x₁⁻¹ * x₂ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hx₁) hx₂
    have hcz := hHz _ hcH
    have hca : (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = a * v := by
      calc (x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹ = x₁⁻¹ * (x₂ * a * x₂⁻¹) * x₁ := by group
        _ = x₁⁻¹ * b₂ * x₁ := by rw [hb₂def]
        _ = x₁⁻¹ * (b₁ * v) * x₁ := by rw [hb₂eq]
        _ = x₁⁻¹ * (x₁ * a * x₁⁻¹ * v) * x₁ := by rw [hb₁def]
        _ = a * (x₁⁻¹ * v * x₁) := by group
        _ = a * v := by rw [hvx]
    have hvV' : v ∈ VZ T M := hvV
    apply mem_normalizer_of_conj_mem_of_finite
    intro w hw
    rcases hcases w hw with h1 | h1 | h1 | h1
    · rw [h1]
      simp
    · rw [h1, hcz]
      exact hzV
    · rw [h1, hca]
      exact (VZ T M).mul_mem haV hvV'
    · rw [h1]
      have e : (x₁⁻¹ * x₂) * (z * a) * (x₁⁻¹ * x₂)⁻¹ =
          ((x₁⁻¹ * x₂) * z * (x₁⁻¹ * x₂)⁻¹) * ((x₁⁻¹ * x₂) * a * (x₁⁻¹ * x₂)⁻¹) := by group
      rw [e, hcz, hca]
      exact (VZ T M).mul_mem hzV ((VZ T M).mul_mem haV hvV')
  have hHle : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (VZ T M : Set G) := by
    by_contra hnot
    obtain ⟨x₁, hx₁, hx₁N⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    set Hc := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hHc
    set N : Subgroup G := Hc ⊓ Subgroup.normalizer (VZ T M : Set G) with hNdef
    have hNH : N ≤ Hc := inf_le_left
    have hTN : T ≤ N := fun t ht =>
      ⟨h.almostSpecialHyp_g1.T_le_H ht, by rw [h.normalizer_VZ]; exact h.inM.2 ht⟩
    have h2 : N.relIndex Hc = 2 := by
      unfold Subgroup.relIndex
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x₁, hx₁⟩, fun b => ?_⟩
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hNdef, Subgroup.mem_inf]
      by_cases hbN : (b : G) ∈ Subgroup.normalizer (VZ T M : Set G)
      · right
        refine ⟨⟨b.2, hbN⟩, fun hh => hx₁N ?_⟩
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbN) hh.2
        simpa using this
      · left
        refine ⟨⟨Hc.mul_mem b.2 hx₁, ?_⟩, fun hh => hbN hh.2⟩
        have hbinv : (b : G)⁻¹ ∉ Subgroup.normalizer (VZ T M : Set G) := fun hh =>
          hbN (by simpa using Subgroup.inv_mem _ hh)
        have := hK (b : G)⁻¹ (Hc.inv_mem b.2) hbinv x₁ hx₁ hx₁N
        simpa using this
    have h3 : T.relIndex N * N.relIndex Hc = T.relIndex Hc :=
      Subgroup.relIndex_mul_relIndex T N Hc hTN hNH
    have h4 : T.relIndex Hc ∣ T.index :=
      Subgroup.relIndex_dvd_index_of_le (h.almostSpecialHyp_g1.T_le_H)
    apply h.sylow.2
    rw [h2] at h3
    exact (Dvd.intro_left _ h3).trans h4
  exact h.not_le (by rw [← h.normalizer_VZ]; exact hHle)

theorem lemma_12_8_11_six (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M)
    (hF : D.hat (VZ T M) < D.fixSpace (rconj (wOfU T M) g)) :
    ∃ γ ∈ D.img (rconj (wOfU T M) g), γ ≠ 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≤ 2 ∧
        D.hat (VZ T M) ≤ LinearMap.range (γ.toLinearMap - LinearMap.id) := by
  classical
  obtain ⟨a, haV, haZ⟩ := h.exists_mem_VZ_not_mem
  obtain ⟨hπa, -, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
  have hXT : rconj (wOfU T M) g ≤ T := h.rconj_wOfU_le_T hU hg
  have hXN : rconj (wOfU T M) g ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
    hXT.trans h.T_le_normalizer_uOfL22
  have hrho_ne : ∀ (x : G) (hxX : x ∈ rconj (wOfU T M) g),
      x ∉ wOfU T M ⊓ rconj (wOfU T M) g → D.rho ⟨x, hXN hxX⟩ ≠ 1 := by
    intro x hxX hxE h1
    apply hxE
    rw [← (h.lemma_12_8_9_five hU hg).1]
    exact ⟨hxX, normalizer_le_normalizer_centerOf _ (hXN hxX),
      (D.rho_eq_one_iff ⟨x, hXN hxX⟩).mp h1⟩
  have hπ_mem : ∀ {x u : G} (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
      (hu : u ∈ uOfL22 T M), D.rho ⟨x, hxN⟩ (D.π u) = D.π u →
        x * u * x⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M) := by
    intro x u hxN hu hfix
    have h1 := HatModel.rho_sub_π (D := D) hxN hu
    rw [hfix, sub_self] at h1
    have hmem : x * u * x⁻¹ * u⁻¹ ∈ uOfL22 T M :=
      (uOfL22 T M).mul_mem (HatModel.conj_mem_uOfL22 hxN hu) ((uOfL22 T M).inv_mem hu)
    exact (D.π_eq_zero_iff hmem).mp h1.symm
  have key : ∀ (x : G) (hxX : x ∈ rconj (wOfU T M) g), D.rho ⟨x, hXN hxX⟩ ≠ 1 →
      (∀ w ∈ wOfU T M, x * w * x⁻¹ * w⁻¹ ∈ centerOf (uOfL22 T M) ⊔ VZ T M) →
        ∃ γ ∈ D.img (rconj (wOfU T M) g), γ ≠ 1 ∧
          Module.finrank (ZMod 2) (LinearMap.range (γ.toLinearMap - LinearMap.id)) ≤ 2 ∧
            D.hat (VZ T M) ≤ LinearMap.range (γ.toLinearMap - LinearMap.id) := by
    intro x hxX hne hxw
    have hxN := hXN hxX
    have hW : ∀ v, D.B (D.π a) v = 0 →
        D.rho ⟨x, hxN⟩ v - v ∈ Submodule.span (ZMod 2) {D.π a} := by
      intro v hv
      obtain ⟨w, hwW, hwU, hwv⟩ := D.mem_hat.mp ((h.mem_hat_wOfU_iff D haV haZ).mpr hv)
      rw [← hwv, HatModel.rho_sub_π (D := D) hxN hwU]
      exact h.π_mem_span_of_mem_sup D haV haZ (hxw w hwW)
    have hLA := isometry_range_of_fixing_point D.B (fun v hv => D.B_nondegenerate v hv)
      (D.rho ⟨x, hxN⟩) (D.B_rho ⟨x, hxN⟩) hπa hW hne
    refine ⟨D.rho ⟨x, hxN⟩, HatModel.rho_mem_img hxX hxN, hne, hLA.1, ?_⟩
    intro v hv
    rcases hhatV v hv with h0 | h0
    · rw [h0]
      exact Submodule.zero_mem _
    · rw [h0]
      exact hLA.2
  by_cases hZE : rconj (centerOf (uOfL22 T M)) g ≤ wOfU T M ⊓ rconj (wOfU T M) g
  swap
  ·
    obtain ⟨x, hxZ, hxE⟩ := IsConcreteLE.not_le_iff_exists.mp hZE
    have hxX : x ∈ rconj (wOfU T M) g := rconj_centerOf_le_rconj_wOfU T M g hxZ
    refine key x hxX (hrho_ne x hxX hxE) (fun w hw => ?_)
    have hcomm : ⁅w, x⁆ ∈ centerOf (uOfL22 T M) ⊔ VZ T M :=
      h.lemma_12_8_10_four hU hg (Subgroup.commutator_mem_commutator hw hxZ)
    have hinv : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hinv]
    exact (centerOf (uOfL22 T M) ⊔ VZ T M).inv_mem hcomm
  ·
    obtain ⟨v₀, hv₀F, hv₀V⟩ := (IsConcreteLE.lt_iff_le_and_exists.mp hF).2
    obtain ⟨f, hfU, hπf⟩ := D.π_surj v₀
    have hXnW := h.not_rconj_wOfU_le_wOfU hU hg
    have hfix : ∀ (x : G) (hxX : x ∈ rconj (wOfU T M) g),
        D.rho ⟨x, hXN hxX⟩ (D.π f) = D.π f := by
      intro x hxX
      rw [hπf]
      exact D.mem_fixSpace.mp hv₀F _ (HatModel.rho_mem_img hxX (hXN hxX))
    have hfW : f ∈ wOfU T M := by
      by_contra hfW
      apply hXnW
      intro x hxX
      have hcomm := hπ_mem (hXN hxX) hfU (hfix x hxX)
      have h9 := h.lemma_12_8_9_six hU hg hfU hfW hxX hcomm
      rw [sup_eq_right.mpr hZE] at h9
      exact h9.1
    have hπfE : D.π f ∉ D.hat (wOfU T M ⊓ rconj (wOfU T M) g) := by
      intro hmem
      obtain ⟨e, heE, heU, hπe⟩ := D.mem_hat.mp hmem
      have heV : e ∈ VZ T M := by
        rw [← h.lemma_12_8_11_four hU hg]
        refine ⟨heE, normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer heU),
          fun x hx => ?_⟩
        have hfixe : D.rho ⟨x, hXN hx⟩ (D.π e) = D.π e := by
          rw [hπe]
          exact hfix x hx
        have hc := hπ_mem (hXN hx) heU hfixe
        have e1 : e * x * e⁻¹ * x⁻¹ = (x * e * x⁻¹ * e⁻¹)⁻¹ := by group
        rw [e1]
        exact (centerOf (uOfL22 T M)).inv_mem hc
      apply hv₀V
      rw [← hπf, ← hπe]
      exact D.π_mem_hat heV heU
    have hP3 : ∀ y ∈ rconj (wOfU T M) g, y * f * y⁻¹ * f⁻¹ ∈ quasithinOmegaOneCenter T := by
      intro y hyX
      have hZ := hπ_mem (hXN hyX) hfU (hfix y hyX)
      have hfN : f ∈ Subgroup.normalizer (rconj (wOfU T M) g : Set G) :=
        h.pCoreOf_sup_uOfL22_le_normalizer_X hU hg (h.wOfU_le_pCoreOf hU hg hfW)
      have hcX : y * f * y⁻¹ * f⁻¹ ∈ rconj (wOfU T M) g := by
        have e : y * f * y⁻¹ * f⁻¹ = y * (f * y⁻¹ * f⁻¹) := by group
        rw [e]
        exact (rconj (wOfU T M) g).mul_mem hyX
          ((Subgroup.mem_normalizer_iff.mp hfN _).mp ((rconj (wOfU T M) g).inv_mem hyX))
      have hcUg : y * f * y⁻¹ * f⁻¹ ∈ rconj (uOfL22 T M) g :=
        rconj_le_rconj (wOfU_le_uOfL22 T M) g hcX
      have hmem : y * f * y⁻¹ * f⁻¹ ∈ centerOf (uOfL22 T M) ⊓ rconj (uOfL22 T M) g :=
        ⟨hZ, hcUg⟩
      rw [h.lemma_12_8_10_one hU hg, h.centerOf_inf_rconj_centerOf_eq_bot hU hg, bot_sup_eq]
        at hmem
      exact hmem
    obtain ⟨t, htN, htZ, htW, htX⟩ := h.exists_swap hU hg
    have hXWt : rconj (wOfU T M) t = rconj (wOfU T M) g := by
      have h1 := congrArg (fun K => rconj K t) htX
      simp only [rconj_rconj_eq, inv_mul_cancel_right] at h1
      exact h1.symm
    have hx₀X : t * f * t⁻¹ ∈ rconj (wOfU T M) g := by
      have h1 := inv_mul_mul_mem_rconj (X := wOfU T M) (g := t⁻¹) hfW
      rw [htW, inv_inv] at h1
      exact h1
    have hx₀E : t * f * t⁻¹ ∉ wOfU T M ⊓ rconj (wOfU T M) g := by
      intro hx₀E
      have hfX : f ∈ rconj (wOfU T M) g := by
        rw [← hXWt, mem_rconj]
        exact hx₀E.1
      exact hπfE (D.π_mem_hat (A := wOfU T M ⊓ rconj (wOfU T M) g) ⟨hfW, hfX⟩ hfU)
    refine key (t * f * t⁻¹) hx₀X (hrho_ne _ hx₀X hx₀E) (fun w hw => ?_)
    have hyX : t⁻¹ * w * t ∈ rconj (wOfU T M) g := by
      have h1 : w ∈ rconj (rconj (wOfU T M) g) t⁻¹ := by
        rw [htX]
        exact hw
      have h2 := mem_rconj.mp h1
      simpa using h2
    have hc : (t * f * t⁻¹) * w * (t * f * t⁻¹)⁻¹ * w⁻¹ ∈ VZ T M := by
      have hy1 := hP3 _ hyX
      have hy2 : f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹ ∈ quasithinOmegaOneCenter T := by
        have e : f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹ =
            ((t⁻¹ * w * t) * f * (t⁻¹ * w * t)⁻¹ * f⁻¹)⁻¹ := by group
        rw [e]
        exact (quasithinOmegaOneCenter T).inv_mem hy1
      have hy3 := inv_mul_mul_mem_rconj (X := quasithinOmegaOneCenter T) (g := t⁻¹) hy2
      rw [htZ, inv_inv] at hy3
      have hy4 : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
        (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
      have e2 : (t * f * t⁻¹) * w * (t * f * t⁻¹)⁻¹ * w⁻¹ =
          t * (f * (t⁻¹ * w * t) * f⁻¹ * (t⁻¹ * w * t)⁻¹) * t⁻¹ := by group
      rw [e2]
      exact hy4 hy3
    exact (le_sup_right : VZ T M ≤ centerOf (uOfL22 T M) ⊔ VZ T M) hc

end Hyp1281Two

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Xb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_exists_X_cover (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil ⊥ V) {K₁ K₂ : Subgroup G} (hK₁M : K₁ ≤ D.M) (hK₂M : K₂ ≤ D.M)
    (hn₁₂ : K₁ ≤ normalizer (K₂ : Set G))
    (hMN : D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) {a b : ℕ}
    (h₁ : Nat.card K₁ = 2 ^ a * 168) (h₂ : Nat.card K₂ = 2 ^ b * 168)
    {Y₁ Y₂ : Subgroup (Vtil ⊥ V hV)} {A₁ A₂ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcore : C23Core Y₁ Y₂ A₁ A₂ (Mbar D.M ⊥ V hV))
    (hbarA : barSub ⊥ V hV (K₁ ⊔ K₂) = A₁ ⊔ A₂) :
    ∃ (z : IntMod V hV) (X : Subgroup G), mkTil ⊥ V hV z ∈ c23Omega Y₁ Y₂ ∧
      (∀ t ∈ D.T, t * z.val = z.val * t) ∧ (∀ x ∈ X, x * z.val = z.val * x) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧
      (∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val = z.val * n) ∧
      ∀ j ∈ K₁ ⊔ K₂, j * z.val = z.val * j → ∃ x ∈ X, ∃ t ∈ D.T, j = x * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h𝓛M : K₁ ⊔ K₂ ≤ D.M := sup_le hK₁M hK₂M
  have h𝓛s : K₁ ⊔ K₂ ≤ stabTil ⊥ V := h𝓛M.trans hMs
  have hTs : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMs
  have hA : Nat.card (barSub ⊥ V hV (K₁ ⊔ K₂)) = 168 * 168 := by
    rw [hbarA]; exact c23_core_card_sup hcore
  have hN2 : IsPGroup 2 ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) :=
    s16c7_isPGroup_two_inf_centralizer V hV hn₁₂ h𝓛s hA h₁ h₂
  have hNT : (K₁ ⊔ K₂) ⊓ centralizer (V : Set G) ≤ D.T :=
    s16c7_inf_centralizer_le h𝓛M hMN (hMs.trans (stabTil_le_normalizer ⊥ V)) D.sylowM hN2
  have h4 : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ (K₁ ⊔ K₂)) (K₁ ⊔ K₂) :=
    D.sylowM.inf_of_le_normalizer h𝓛M hMN
  have h5 := s16c7_isSylowOf_barSub ⊥ V hV h4 h𝓛s
  have hTbar : IsPGroup 2 (barSub ⊥ V hV D.T) := by
    have h0 : IsPGroup 2 (D.T.subgroupOf (stabTil ⊥ V)) := D.sylowM.isPGroup.comap_subtype
    exact h0.map (actTil ⊥ V hV)
  have hS : CFSG.ABGLocalTools.IsSylowOf 2
      (barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂))) (A₁ ⊔ A₂) := by
    rw [← hbarA]; exact h5
  have hTb : barSub ⊥ V hV D.T ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV D.sylowM.le
  obtain ⟨u₀, hΩ, hfixT⟩ := c23_exists_fixed_omega hcore hTb hTbar
  have hSfix : ∀ s ∈ barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂)), s u₀ = u₀ :=
    fun s hs => hfixT s (barSub_mono ⊥ V hV inf_le_left hs)
  obtain ⟨Xb, hXbA, hXb9, hXbfix, hXbcov⟩ := c23_exists_fixed_sylow hcore hΩ hS hSfix
  have hXbp : IsPGroup 3 Xb := IsPGroup.of_card (n := 2) (by rw [hXb9]; norm_num)
  have hSyl3 : CFSG.ABGLocalTools.IsSylowOf 3 Xb (barSub ⊥ V hV (K₁ ⊔ K₂)) := by
    rw [hbarA, CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hXbA, hXbp, ?_⟩
    have e := Subgroup.relIndex_mul_card (H := Xb) (K := A₁ ⊔ A₂)
    rw [inf_eq_left.2 hXbA, hXb9, c23_core_card_sup hcore] at e
    have hr : Xb.relIndex (A₁ ⊔ A₂) = 3136 := by omega
    rw [hr]; norm_num
  obtain ⟨X, hXsyl, hXb⟩ := s16c7_exists_lift_sylow (p := 3) ⊥ V hV h𝓛s hSyl3
  have hXs : X ≤ stabTil ⊥ V := hXsyl.le.trans h𝓛s
  obtain ⟨z, rfl⟩ := mkTil_surjective ⊥ V hV u₀
  refine ⟨z, X, hΩ, ?_, ?_, hXsyl, ?_, ?_⟩
  ·
    intro t ht
    have h1 : t * z.val * t⁻¹ = z.val :=
      (s16c7_mem_fixV_barSub_iff V hV hTs z).1 (mem_fixV.2 hfixT) t ht
    exact mul_inv_eq_iff_eq_mul.1 h1
  ·
    intro x hx
    have hxXb : actTil ⊥ V hV ⟨x, hXs hx⟩ ∈ Xb := by
      rw [← hXb]
      exact actTil_mem_barSub ⊥ V hV hx (hXs hx)
    have h1 : actTil ⊥ V hV ⟨x, hXs hx⟩ (mkTil ⊥ V hV z) = mkTil ⊥ V hV z :=
      hXbfix _ hxXb
    have h2 : x * z.val * x⁻¹ = z.val :=
      (s16c7_act_mkTil_eq_iff V hV ⟨x, hXs hx⟩ z).1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  ·
    intro n hn
    obtain ⟨hnL, hnN⟩ := Subgroup.mem_inf.1 hn
    have hns : n ∈ stabTil ⊥ V := h𝓛s hnL
    have hnXmap : X.map (MulAut.conj n).toMonoidHom = X := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.1 hnN
    have hconj := s16c7_barSub_map_conj ⊥ V hV hns X
    rw [hnXmap, hXb] at hconj
    have hnbN : actTil ⊥ V hV ⟨n, hns⟩ ∈
        normalizer (Xb : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa using hconj.symm
    have hnbM : actTil ⊥ V hV ⟨n, hns⟩ ∈ Mbar D.M ⊥ V hV :=
      actTil_mem_barSub ⊥ V hV (h𝓛M hnL) hns
    have h1 : actTil ⊥ V hV ⟨n, hns⟩ (mkTil ⊥ V hV z) = mkTil ⊥ V hV z :=
      c23_fixed_of_mem_normalizer hcore hXbA hXb9 hΩ hXbfix hnbM hnbN
    have h2 : n * z.val * n⁻¹ = z.val :=
      (s16c7_act_mkTil_eq_iff V hV ⟨n, hns⟩ z).1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  ·
    intro j hj hjz
    have hjs : j ∈ stabTil ⊥ V := h𝓛s hj
    have hjb : actTil ⊥ V hV ⟨j, hjs⟩ ∈ barSub ⊥ V hV (K₁ ⊔ K₂) :=
      actTil_mem_barSub ⊥ V hV hj hjs
    have hjfix : actTil ⊥ V hV ⟨j, hjs⟩ (mkTil ⊥ V hV z) = mkTil ⊥ V hV z := by
      rw [s16c7_act_mkTil_eq_iff]
      calc j * z.val * j⁻¹ = (z.val * j) * j⁻¹ := by rw [hjz]
        _ = z.val := by group
    rw [hbarA] at hjb
    obtain ⟨xb, hxb, tb, htb, hxt⟩ := hXbcov _ hjb hjfix
    rw [← hXb] at hxb
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub ⊥ V hV X xb).1 hxb
    obtain ⟨s, hsTL, rfl⟩ := (mem_barSub ⊥ V hV (D.T ⊓ (K₁ ⊔ K₂)) tb).1 htb
    have hxL : (x : G) ∈ K₁ ⊔ K₂ := hXsyl.le hxX
    have hsL : (s : G) ∈ K₁ ⊔ K₂ := (Subgroup.mem_inf.1 hsTL).2
    have hsT : (s : G) ∈ D.T := (Subgroup.mem_inf.1 hsTL).1
    have hker : actTil ⊥ V hV ((x * s)⁻¹ * ⟨j, hjs⟩) = 1 := by
      rw [map_mul, map_inv, map_mul, hxt]
      simp
    have hn : (((x * s)⁻¹ * ⟨j, hjs⟩ : ↥(stabTil ⊥ V)) : G) ∈
        (K₁ ⊔ K₂) ⊓ centralizer (V : Set G) := by
      refine Subgroup.mem_inf.2 ⟨?_, (s16c7_actTil_eq_one_iff_mem_centralizer V hV _).1 hker⟩
      show ((x : G) * (s : G))⁻¹ * j ∈ K₁ ⊔ K₂
      exact (K₁ ⊔ K₂).mul_mem ((K₁ ⊔ K₂).inv_mem ((K₁ ⊔ K₂).mul_mem hxL hsL)) hj
    refine ⟨x, hxX, (s : G) * (((x * s)⁻¹ * ⟨j, hjs⟩ : ↥(stabTil ⊥ V)) : G),
      D.T.mul_mem hsT (hNT hn), ?_⟩
    show j = (x : G) * ((s : G) * (((x : G) * (s : G))⁻¹ * j))
    group

theorem c23_exists_X_z (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil ⊥ V) {K₁ K₂ : Subgroup G} (hK₁M : K₁ ≤ D.M) (hK₂M : K₂ ≤ D.M)
    (hn₁₂ : K₁ ≤ normalizer (K₂ : Set G))
    (hMN : D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) {a b : ℕ}
    (h₁ : Nat.card K₁ = 2 ^ a * 168) (h₂ : Nat.card K₂ = 2 ^ b * 168)
    {Y₁ Y₂ : Subgroup (Vtil ⊥ V hV)} {A₁ A₂ : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hcore : C23Core Y₁ Y₂ A₁ A₂ (Mbar D.M ⊥ V hV))
    (hbarA : barSub ⊥ V hV (K₁ ⊔ K₂) = A₁ ⊔ A₂) :
    ∃ (z : IntMod V hV) (X : Subgroup G), mkTil ⊥ V hV z ∈ c23Omega Y₁ Y₂ ∧
      (∀ t ∈ D.T, t * z.val = z.val * t) ∧ (∀ x ∈ X, x * z.val = z.val * x) ∧
      CFSG.ABGLocalTools.IsSylowOf 3 X (K₁ ⊔ K₂) ∧ Permutes X D.T ∧
      ∀ n ∈ (K₁ ⊔ K₂) ⊓ normalizer (X : Set G), n * z.val = z.val * n := by
  obtain ⟨z, X, hΩ, hzT, hzX, hXsyl, hN, hcov⟩ :=
    c23_exists_X_cover D hV hMs hK₁M hK₂M hn₁₂ hMN h₁ h₂ hcore hbarA
  exact ⟨z, X, hΩ, hzT, hzX, hXsyl,
    s16c7_permutes_of_cover hXsyl.le (D.sylowM.le.trans hMN) hzT hzX hcov, hN⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

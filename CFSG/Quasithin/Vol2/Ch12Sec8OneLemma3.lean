module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Quasithin.H13.LinearS3Hull
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint Subgroup
open scoped IsMulCommutative

theorem exists_linearEquiv_map_eq {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {U U' : Submodule K W}
    (h : Module.finrank K U = Module.finrank K U') :
    ∃ g : W ≃ₗ[K] W, U.map (g : W →ₗ[K] W) = U' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl U'
  have hCC : Module.finrank K C = Module.finrank K C' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := Submodule.finrank_add_eq_of_isCompl hC'
    omega
  let e₁ : U ≃ₗ[K] U' := LinearEquiv.ofFinrankEq U U' h
  let e₂ : C ≃ₗ[K] C' := LinearEquiv.ofFinrankEq C C' hCC
  let g : W ≃ₗ[K] W := ((Submodule.prodEquivOfIsCompl U C hC).symm.trans
    (e₁.prodCongr e₂)).trans (Submodule.prodEquivOfIsCompl U' C' hC')
  have hg : ∀ u : U, g u = e₁ u := by
    intro u
    simp [g]
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    have := hg ⟨u, hu⟩
    simp only [LinearEquiv.coe_coe] at this ⊢
    rw [this]
    exact (e₁ ⟨u, hu⟩).2
  · intro u' hu'
    refine ⟨(e₁.symm ⟨u', hu'⟩ : W), (e₁.symm ⟨u', hu'⟩).2, ?_⟩
    have := hg (e₁.symm ⟨u', hu'⟩)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    rw [this]

variable {G : Type} [Group G]

section Lin

variable {V : Subgroup G} [IsMulCommutative ↥V] [Module (ZMod 2) (Additive ↥V)]

@[expose] def mulAutOfLin (g : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) : MulAut ↥V where
  toFun x := Additive.toMul (g (Additive.ofMul x))
  invFun x := Additive.toMul (g.symm (Additive.ofMul x))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp only [ofMul_mul, map_add, toMul_add]

theorem mulAutOfLin_apply (g : Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) (x : ↥V) :
    mulAutOfLin g x = Additive.toMul (g (Additive.ofMul x)) := rfl

theorem card_subOf {W : Subgroup G} (hWV : W ≤ V) : Nat.card (subOf (V := V) W) = Nat.card W :=
  Nat.card_congr
    { toFun := fun x => ⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G), mem_subOf.1 x.2⟩
      invFun := fun w => ⟨Additive.ofMul ⟨w, hWV w.2⟩, mem_subOf.2 w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finrank_subOf [Finite G] {W : Subgroup G} (hWV : W ≤ V) {i : ℕ}
    (hW : Nat.card W = 2 ^ i) : Module.finrank (ZMod 2) (subOf (V := V) W) = i := by
  have : Module.Finite (ZMod 2) (subOf (V := V) W) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subOf (V := V) W)
  rw [Nat.card_zmod, card_subOf hWV, hW] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

end Lin

theorem lemma12_8_3_two [Finite G] {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {i : ℕ} {W₁ W₂ : Subgroup G} (hW₁ : W₁ ≤ V) (hW₂ : W₂ ≤ V) (h1 : Nat.card W₁ = 2 ^ i)
    (h2 : Nat.card W₂ = 2 ^ i) : ∃ l ∈ L, CFSG.conjugate W₁ l = W₂ := by
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  let _ := zmodModuleOf hsq
  have : Module.Finite (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have hf : Module.finrank (ZMod 2) (subOf (V := V) W₂) =
      Module.finrank (ZMod 2) (subOf (V := V) W₁) := by
    rw [finrank_subOf hW₂ h2, finrank_subOf hW₁ h1]
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq hf
  have hαL : mulAutOfLin g ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, ?_⟩
  have hle : W₂ ≤ CFSG.conjugate W₁ l := by
    intro w hw
    rw [SteinbergBS.mem_conjugate_iff]
    have hwV := hW₂ hw
    have e : l * w * l⁻¹ = ((mulAutOfLin g ⟨w, hwV⟩ : ↥V) : G) := by
      rw [← hlα]
      rfl
    rw [e, mulAutOfLin_apply]
    have hmem : g (Additive.ofMul ⟨w, hwV⟩) ∈ subOf (V := V) W₁ := by
      rw [← hg]
      exact ⟨Additive.ofMul ⟨w, hwV⟩, mem_subOf.2 hw, rfl⟩
    exact mem_subOf.1 hmem
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [LinearS3.card_conjugate, h1, h2])).symm

theorem lemma12_8_3_three [Finite G] {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {i : ℕ} {Vi : Subgroup G} (hVi : IsTSub T V Vi i) {g : G}
    (hg : Vi ≤ CFSG.conjugate V g) :
    ∃ k ∈ Subgroup.normalizer (Vi : Set G), CFSG.conjugate V k = CFSG.conjugate V g := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  refine SteinbergBS.exists_normalizer_conjugate_eq hVi.1 hVi.2.1 ?_ hg
  intro Z₁ hZ₁ hc₁ Z₂ hZ₂ hc₂
  obtain ⟨l, hl, hlZ⟩ := lemma12_8_3_two h hZ₁ hZ₂ hc₁ hc₂
  exact ⟨l, hLV hl, hlZ⟩

theorem lemma12_8_3_four (h12213 : Stmt12_2_13) [Finite G] {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨e⟩ := h.quot
  rcases (stmt12_2_13_iff.mp h12213) G T L V h.hyp with ⟨v, hvV, hv1, hvM⟩ |
      ⟨n', hn', ⟨e'⟩, hlie⟩ | ⟨-, hA9⟩ | ⟨-, hM24⟩
  · apply hvM
    have hv2 : Nat.card (Subgroup.zpowers v) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (hsq v hvV) hv1
    obtain ⟨l, hl, hlZ⟩ := lemma12_8_3_two h hV₁.1 ((Subgroup.zpowers_le).2 hvV) hV₁.2.1
      (by rw [hv2, pow_one])
    have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    intro x hx
    have hxn : x ∈ Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hx
    have key : ∀ w, w ∈ V₁ ↔ l⁻¹ * w * l ∈ Subgroup.zpowers v := by
      intro w
      rw [← hlZ, SteinbergBS.mem_conjugate_iff, show l * (l⁻¹ * w * l) * l⁻¹ = w by group]
    have hy : l * x * l⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [key, key, Subgroup.mem_normalizer_iff.1 hxn,
        show x * (l⁻¹ * z * l) * x⁻¹ = l⁻¹ * (l * x * l⁻¹ * z * (l * x * l⁻¹)⁻¹) * l by group]
    have h2 : l⁻¹ * (l * x * l⁻¹) * l ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (mul_mem (inv_mem hlM) (hle hy)) hlM
    rwa [show l⁻¹ * (l * x * l⁻¹) * l = x by group] at h2
  · have hc := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
    have hnn : n = n' := by
      rcases h.n_mem with rfl | rfl | rfl <;> rcases hn' with rfl | rfl
      · rfl
      · rw [card_sl_three_zmod_two, card_sl_four_zmod_two] at hc
        omega
      · rw [card_sl_four_zmod_two, card_sl_three_zmod_two] at hc
        omega
      · rfl
      · rw [card_sl_five_zmod_two, card_sl_three_zmod_two] at hc
        omega
      · rw [card_sl_five_zmod_two, card_sl_four_zmod_two] at hc
        omega
    subst hnn
    exact h.not_linear hlie
  · exact h.not_alt9 hA9
  · exact h.not_m24 hM24

theorem lemma12_8_3 (h12213 : Stmt12_2_13) : Lemma12_8_3 := by
  intro G _ _ T L V n h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have htop := autOn_eq_top_of_hyp1281One h
  have hMV : autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = ⊤ :=
    top_le_iff.1 (htop ▸ autOn_mono (le_inf Subgroup.le_normalizer hLV))
  exact ⟨⟨hMV, hMV.trans htop.symm⟩, fun i W₁ W₂ h1 h2 hc1 hc2 => lemma12_8_3_two h h1 h2 hc1 hc2,
    fun i Vi hVi g hg => lemma12_8_3_three h hVi hg, fun V₁ hV₁ => lemma12_8_3_four h12213 h hV₁⟩

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqBase
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def isoForm (x y : Vc σ) : K :=
  (x.2.2.2 : K) * y.1 + (y.2.2.2 : K) * x.1 + trT σ (x.2.2.1 * y.2.1) + trT σ (y.2.2.1 * x.2.1)

theorem isoForm_comm (x y : Vc σ) : isoForm σ x y = isoForm σ y x := by
  unfold isoForm
  ring

theorem isoForm_mem (hσ : ∀ c, σ (σ (σ c)) = c) (x y : Vc σ) : isoForm σ x y ∈ d4k K σ :=
  add_mem (add_mem (add_mem (mul_mem x.2.2.2.2 y.1.2) (mul_mem y.2.2.2.2 x.1.2))
    (trT_mem σ hσ _)) (trT_mem σ hσ _)

@[expose] def isoK (hσ : ∀ c, σ (σ (σ c)) = c) (x y : Vc σ) : d4k K σ :=
  ⟨isoForm σ x y, isoForm_mem σ hσ x y⟩

theorem isoK_add_left (hσ : ∀ c, σ (σ (σ c)) = c) (x x' y : Vc σ) :
    isoK σ hσ (x + x') y = isoK σ hσ x y + isoK σ hσ x' y := by
  refine Subtype.ext ?_
  simp only [isoK, isoForm, Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, add_mul, mul_add,
    trT_add]
  ring

theorem isoK_add_right (hσ : ∀ c, σ (σ (σ c)) = c) (x y y' : Vc σ) :
    isoK σ hσ x (y + y') = isoK σ hσ x y + isoK σ hσ x y' := by
  refine Subtype.ext ?_
  simp only [isoK, isoForm, Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, add_mul, mul_add,
    trT_add]
  ring

theorem isoK_comm (hσ : ∀ c, σ (σ (σ c)) = c) (x y : Vc σ) :
    isoK σ hσ x y = isoK σ hσ y x :=
  Subtype.ext (isoForm_comm σ x y)

theorem isoK_smul_left (hσ : ∀ c, σ (σ (σ c)) = c) (l : d4k K σ) (x y : Vc σ) :
    isoK σ hσ (l • x) y = l • isoK σ hσ x y := by
  refine Subtype.ext ?_
  have h1 : ∀ a : K, trT σ ((l : K) * a) = (l : K) * trT σ a := fun a => trT_smul σ l.2 a
  simp only [isoK, isoForm, Prod.smul_fst, Prod.smul_snd, trialityFixedField_smul,
    smul_eq_mul, Subfield.coe_mul]
  rw [show (l : K) * x.2.2.1 * y.2.1 = l * (x.2.2.1 * y.2.1) by ring,
    show y.2.2.1 * ((l : K) * x.2.1) = l * (y.2.2.1 * x.2.1) by ring, h1, h1]
  ring

theorem isoK_smul_right (hσ : ∀ c, σ (σ (σ c)) = c) (l : d4k K σ) (x y : Vc σ) :
    isoK σ hσ x (l • y) = l • isoK σ hσ x y := by
  rw [isoK_comm σ hσ, isoK_smul_left σ hσ, isoK_comm σ hσ]

section Bound

variable (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def isoBil : LinearMap.BilinForm (d4k K σ) (Vc σ) :=
  LinearMap.mk₂ (d4k K σ) (isoK σ hσ) (isoK_add_left σ hσ) (isoK_smul_left σ hσ)
    (isoK_add_right σ hσ) (isoK_smul_right σ hσ)

theorem isoBil_apply (x y : Vc σ) : isoBil σ hσ x y = isoK σ hσ x y := rfl

theorem isoBil_sep_left [CharP K 2] {x : Vc σ} (h : ∀ y, isoBil σ hσ x y = 0) : x = 0 := by
  have hv : ∀ y : Vc σ, isoForm σ x y = 0 := fun y => congrArg Subtype.val (h y)
  have hT1 : trT σ 1 ≠ 0 := by rw [trT_one]; exact one_ne_zero
  have he : (x.2.2.2 : K) = 0 := by
    have := hv (1, 0, 0, 0)
    simpa [isoForm, trT] using this
  have hb : (x.1 : K) = 0 := by
    have := hv (0, 0, 0, 1)
    simpa [isoForm, trT] using this
  have hd : x.2.2.1 = 0 := by
    by_contra hd
    have := hv (0, x.2.2.1⁻¹, 0, 0)
    simp only [isoForm, trT, zero_mul, add_zero, map_zero] at this
    rw [mul_inv_cancel₀ hd] at this
    exact hT1 (by simpa [trT] using this)
  have hc : x.2.1 = 0 := by
    by_contra hc
    have := hv (0, 0, x.2.1⁻¹, 0)
    simp only [isoForm, trT, mul_zero, add_zero, map_zero] at this
    rw [inv_mul_cancel₀ hc] at this
    exact hT1 (by simpa [trT] using this)
  exact Prod.ext (Subtype.ext hb) (Prod.ext hc (Prod.ext hd (Subtype.ext he)))

theorem isoBil_nondegenerate [CharP K 2] : (isoBil σ hσ).Nondegenerate :=
  ⟨fun x hx => isoBil_sep_left σ hσ hx, fun y hy => isoBil_sep_left σ hσ fun x => by
    rw [isoBil_apply, isoK_comm σ hσ]
    exact hy x⟩

theorem finrank_d4k [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 3)
    (hk : Nat.card (d4k K σ) = q) : Module.finrank (d4k K σ) K = 3 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (d4k K σ) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := d4k K σ) (V := K)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hk] at h
  have hq : 2 ≤ q := by
    rw [← hk]
    exact Nat.succ_le_of_lt (Finite.one_lt_card (α := d4k K σ))
  exact (Nat.pow_right_injective hq h).symm

include hσ in
theorem card_le_of_isotropic [Finite K] [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 3)
    (hk : Nat.card (d4k K σ) = q) (E : AddSubgroup (Vc σ))
    (hE : ∀ x ∈ E, ∀ y ∈ E, isoForm σ x y = 0) : Nat.card E ≤ q ^ 4 := by
  have hd := finrank_d4k σ hK hk
  have hdim : Module.finrank (d4k K σ) (Vc σ) = 8 := by
    simp only [Module.finrank_prod, Module.finrank_self, hd]
  have hq : 2 ≤ q := by
    rw [← hk]
    exact Nat.succ_le_of_lt (Finite.one_lt_card (α := d4k K σ))
  let W : Submodule (d4k K σ) (Vc σ) := Submodule.span (d4k K σ) (E : Set (Vc σ))
  have h1 : ∀ x ∈ E, ∀ y ∈ W, isoBil σ hσ x y = 0 := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun y _ => isoBil σ hσ x y = 0) ?_ ?_ ?_ ?_ hy
    · intro y hy'
      exact Subtype.ext (hE x hx y hy')
    · exact map_zero _
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro l a _ ha
      rw [map_smul, ha, smul_zero]
  have h2 : ∀ x ∈ W, ∀ y ∈ W, isoBil σ hσ x y = 0 := by
    intro x hx y hy
    refine Submodule.span_induction (p := fun x _ => isoBil σ hσ x y = 0) ?_ ?_ ?_ ?_ hx
    · intro x hx'
      exact h1 x hx' y hy
    · simp
    · intro a b _ _ ha hb
      rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    · intro l a _ ha
      rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
  have hle : W ≤ (isoBil σ hσ).orthogonal W := fun v hv => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    exact h2 u hu v hv
  have h3 := LinearMap.BilinForm.finrank_orthogonal (isoBil_nondegenerate σ hσ) W
  have h4 := Submodule.finrank_mono hle
  have h5 := Submodule.finrank_le W
  have h6 : Module.finrank (d4k K σ) W ≤ 4 := by omega
  have : Fintype W := Fintype.ofFinite W
  have : Fintype (d4k K σ) := Fintype.ofFinite _
  have h7 := Module.card_eq_pow_finrank (K := d4k K σ) (V := W)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk] at h7
  calc Nat.card E ≤ Nat.card W :=
        Nat.card_mono (Set.toFinite _) (fun x hx => Submodule.subset_span hx)
    _ = q ^ Module.finrank (d4k K σ) W := h7
    _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) h6

end Bound

end CFSG.Quasithin.H13.F431.D4q.NFq

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement Matrix

section Symplectic

variable {d : ℕ} {K : Type} [Field K]

private def spFix_form (d : ℕ) (K : Type) [Field K] :
    (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) →ₗ[K] K :=
  Matrix.toLinearMap₂' K (Matrix.J (Fin d) K)

private theorem spFix_form_apply (x y : Fin d ⊕ Fin d → K) :
    spFix_form d K x y =
      ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i)) := by
  simp [spFix_form, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Matrix.J,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply, Finset.sum_sub_distrib]
  ring

private theorem spFix_form_self (x : Fin d ⊕ Fin d → K) : spFix_form d K x x = 0 := by
  rw [spFix_form_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

private theorem spFix_form_swap (x y : Fin d ⊕ Fin d → K) :
    spFix_form d K y x = -spFix_form d K x y := by
  rw [spFix_form_apply, spFix_form_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem spFix_form_single_inl (x : Fin d ⊕ Fin d → K) (i : Fin d) :
    spFix_form d K x (Pi.single (Sum.inl i) 1) = x (Sum.inr i) := by
  rw [spFix_form_apply]
  simp [Pi.single_apply]

private theorem spFix_form_single_inr (x : Fin d ⊕ Fin d → K) (i : Fin d) :
    spFix_form d K x (Pi.single (Sum.inr i) 1) = -x (Sum.inl i) := by
  rw [spFix_form_apply]
  simp [Pi.single_apply]

private theorem spFix_eq_zero_of_form_eq_zero {x : Fin d ⊕ Fin d → K}
    (h : ∀ y, spFix_form d K x y = 0) : x = 0 := by
  funext k
  rcases k with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    rw [spFix_form_single_inr] at this
    simpa using this
  · have := h (Pi.single (Sum.inl i) 1)
    rwa [spFix_form_single_inl] at this

private theorem spFix_exists_form_ne_zero {x : Fin d ⊕ Fin d → K} (hx : x ≠ 0) :
    ∃ y, spFix_form d K x y ≠ 0 := by
  by_contra h
  exact hx (spFix_eq_zero_of_form_eq_zero fun y => not_not.mp fun hy => h ⟨y, hy⟩)

private theorem spFix_mem_iff_form (A : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) :
    A ∈ Matrix.symplecticGroup (Fin d) K ↔
      ∀ x y, spFix_form d K (A *ᵥ x) (A *ᵥ y) = spFix_form d K x y := by
  have key : ∀ x y, spFix_form d K (A *ᵥ x) (A *ᵥ y) =
      Matrix.toLinearMap₂' K (Aᵀ * Matrix.J (Fin d) K * A) x y := by
    intro x y
    rw [← Matrix.toLinearMap₂'_comp]
    simp [spFix_form, Matrix.toLin'_apply]
  rw [SymplecticGroup.mem_iff']
  constructor
  · intro h x y
    rw [key, h]
    rfl
  · intro h
    have h2 : (Matrix.toLinearMap₂' K (Aᵀ * Matrix.J (Fin d) K * A) :
        (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K) →ₗ[K] K) = spFix_form d K := by
      apply LinearMap.ext₂
      intro x y
      rw [← key, h]
    have h3 := congrArg (LinearMap.toMatrix₂' K) h2
    rwa [spFix_form, LinearMap.toMatrix'_toLinearMap₂', LinearMap.toMatrix'_toLinearMap₂'] at h3

private def spFix_ofLin (f : (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K))
    (hf : ∀ x y, spFix_form d K (f x) (f y) = spFix_form d K x y) :
    TauCeti.GLSymplectic (Fin d) K :=
  ⟨TauCeti.GLSymplectic.ofSymplecticGroup (Fin d) K
    ⟨LinearMap.toMatrix' f, (spFix_mem_iff_form _).mpr (by
      simpa [LinearMap.toMatrix'_mulVec] using hf)⟩,
    TauCeti.GLSymplectic.ofSymplecticGroup_mem _ _ _⟩

private theorem spFix_ofLin_smul (f : (Fin d ⊕ Fin d → K) →ₗ[K] (Fin d ⊕ Fin d → K))
    (hf : ∀ x y, spFix_form d K (f x) (f y) = spFix_form d K x y)
    (x : Fin d ⊕ Fin d → K) : spFix_ofLin f hf • x = f x := by
  change (TauCeti.GLSymplectic.ofSymplecticGroup (Fin d) K _ :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) *ᵥ x = f x
  rw [TauCeti.GLSymplectic.coe_ofSymplecticGroup]
  exact LinearMap.toMatrix'_mulVec f x

private def spFix_tv (u : Fin d ⊕ Fin d → K) (c : K) : TauCeti.GLSymplectic (Fin d) K :=
  spFix_ofLin (LinearMap.id + (c • (spFix_form d K).flip u).smulRight u) (by
    intro x y
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul, map_add, map_smul,
      spFix_form_self]
    rw [spFix_form_swap u y]
    ring)

private theorem spFix_tv_smul (u : Fin d ⊕ Fin d → K) (c : K) (x : Fin d ⊕ Fin d → K) :
    spFix_tv u c • x = x + (c * spFix_form d K x u) • u := by
  rw [spFix_tv, spFix_ofLin_smul]
  simp

private theorem spFix_natAct_eq (g : TauCeti.GLSymplectic (Fin d) K)
    (x : Fin d ⊕ Fin d → K) :
    natAct (StatedSp d K)
      ⟨(g : Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K), by
        rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]; exact g.2⟩
      (Multiplicative.ofAdd x) = Multiplicative.ofAdd (g • x) := rfl

private theorem spFix_fixed_eq_zero {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    {v : Fin d ⊕ Fin d → K}
    (hv : ∀ γ : ↥(StatedSp d K),
      natAct (StatedSp d K) γ (Multiplicative.ofAdd v) = Multiplicative.ofAdd v) : v = 0 := by
  by_contra hv0
  obtain ⟨w, hw⟩ := spFix_exists_form_ne_zero hv0
  have hgmem : (spFix_tv w (spFix_form d K v w)⁻¹ :
      Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K) ∈ StatedSp d K := by
    rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
    exact (spFix_tv w (spFix_form d K v w)⁻¹).2
  have hfix := hv ⟨(spFix_tv w (spFix_form d K v w)⁻¹ :
    Matrix.GeneralLinearGroup (Fin d ⊕ Fin d) K), hgmem⟩
  rw [spFix_natAct_eq (spFix_tv w (spFix_form d K v w)⁻¹) v, spFix_tv_smul,
    inv_mul_cancel₀ hw, one_smul] at hfix
  have hvw : v + w = v := Multiplicative.ofAdd.injective hfix
  have hw0 : w = 0 := add_left_cancel (a := v) (by simpa using hvw)
  rw [hw0] at hw
  exact hw (map_zero (spFix_form d K v))

end Symplectic

theorem s16c167_cfg2_fix_sp {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {n : ℕ} (hn : 2 ≤ n) (h : NatSpn H U ⊥ n 1) : U ⊓ fixV H = ⊥ := by
  obtain ⟨hEven, K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hstab : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := R.U_inv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hdiv : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hEven
  have hn2 : 1 ≤ n / 2 := by omega
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hbeta : β ⟨w, hwU⟩ = 1 := by
    have h2 : Multiplicative.toAdd (β ⟨w, hwU⟩) = 0 := by
      refine spFix_fixed_eq_zero hn2 (K := K) fun γ => ?_
      have hfixw : ((π γ : ↥H) : MulAut W) w = w := (mem_fixV.1 hwfix) _ (π γ).2
      have h3 := hβe γ ⟨w, hwU⟩ (hstab (π γ) w hwU)
      have h4 : β ⟨((π γ : ↥H) : MulAut W) w, hstab (π γ) w hwU⟩ = β ⟨w, hwU⟩ :=
        congrArg β (Subtype.ext hfixw)
      have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
      simpa using h5
    exact Multiplicative.toAdd.injective (by simpa using h2)
  have h6 : (⟨w, hwU⟩ : ↥U) = 1 := hβinj (by rw [hbeta]; exact (map_one β).symm)
  simpa using congrArg Subtype.val h6

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

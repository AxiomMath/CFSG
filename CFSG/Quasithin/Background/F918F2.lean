module

public import CFSG.Quasithin.SteinbergCBI16Alt8
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank CFSG.GH74.Exceptional
  CFSG.ComponentClassification.PresentationLocal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def pr4' : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def minors4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun k l => g (pr4' k).1 (pr4' l).1 * g (pr4' k).2 (pr4' l).2 -
    g (pr4' k).1 (pr4' l).2 * g (pr4' k).2 (pr4' l).1

theorem minors4_mul (g h : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    minors4 (g * h) = minors4 g * minors4 h := by
  ext k l
  fin_cases k <;> fin_cases l <;>
  · simp only [minors4, pr4', Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_six,
      Matrix.of_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
      Fin.zero_eta, Fin.mk_one]
    ring

theorem minors4_one : minors4 1 = 1 := by decide +kernel

@[expose] def alt8WedgeDual : GL (Fin 4) (ZMod 2) →* Matrix (Fin 6) (Fin 6) (ZMod 2) where
  toFun g := (minors4 ((g⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ
  map_one' := by simp [minors4_one]
  map_mul' g h := by
    simp only [_root_.mul_inv_rev, Units.val_mul, minors4_mul, Matrix.transpose_mul]

@[expose] def alt8WedgeB : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 1, 1, 1; 1, 1, 0, 0, 0, 1; 1, 0, 0, 0, 1, 1; 0, 1, 0, 1, 1, 0; 1, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 1, 0]

@[expose] def alt8WedgeBInv : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 1, 1; 1, 0, 1, 1, 0, 1; 0, 1, 1, 0, 0, 1; 0, 1, 1, 1, 0, 0; 1, 1, 0, 1, 0, 1;
    1, 1, 1, 0, 1, 0]

theorem alt8WedgeBInv_mul : alt8WedgeBInv * alt8WedgeB = 1 := by decide +kernel

theorem alt8WedgeB_mul_inv : alt8WedgeB * alt8WedgeBInv = 1 := by decide +kernel

@[expose] def alt8WedgeBEquiv : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun x := alt8WedgeB *ᵥ x
  invFun x := alt8WedgeBInv *ᵥ x
  left_inv x := by
    show alt8WedgeBInv *ᵥ (alt8WedgeB *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, alt8WedgeBInv_mul, Matrix.one_mulVec]
  right_inv x := by
    show alt8WedgeB *ᵥ (alt8WedgeBInv *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, alt8WedgeB_mul_inv, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ _ _

@[expose] def alt8WedgeN : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 2)
  | 0 => !![0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 1 => !![0, 0, 0, 1, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 2 => !![0, 0, 0, 0, 1, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
      0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1]
  | 3 => !![0, 0, 0, 0, 0, 1; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0; 0, 1, 0, 0, 0, 0]
  | 4 => !![1, 1, 1, 1, 1, 1; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1]
  | 5 => !![0, 1, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0; 0, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0;
      0, 1, 0, 0, 1, 0; 0, 1, 0, 0, 0, 1]

theorem coords8_actA_carmichaelCycle (k : CarmichaelIndex 8) (y : Fin 6 → ZMod 2) :
    SteinbergCB.I16.coords8.actA (carmichaelCycle k) y =
      alt8WedgeN (carmichaelIndexToFin6 k) *ᵥ y := by
  revert k y
  decide +kernel

theorem alt8WedgeB_intertwine (j : Fin 6) :
    alt8WedgeB * (minors4 (l42Mat j ^ 2))ᵀ = alt8WedgeN j * alt8WedgeB := by
  revert j
  decide +kernel

theorem alt8WedgeDual_l42Gen (k : CarmichaelIndex 8) :
    alt8WedgeDual (l42Gen k) = (minors4 (l42Mat (carmichaelIndexToFin6 k) ^ 2))ᵀ := rfl

theorem alt8WedgeB_dual_l42Gen (k : CarmichaelIndex 8) (x : Fin 6 → ZMod 2) :
    alt8WedgeB *ᵥ (alt8WedgeDual (l42Gen k) *ᵥ x) =
      alt8WedgeN (carmichaelIndexToFin6 k) *ᵥ (alt8WedgeB *ᵥ x) := by
  rw [alt8WedgeDual_l42Gen, Matrix.mulVec_mulVec, alt8WedgeB_intertwine, ← Matrix.mulVec_mulVec]

theorem exists_iso_alt8_carm :
    ∃ φ : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2),
      ∀ k : CarmichaelIndex 8, φ (carmichaelCycle k) = l42Gen k := by
  classical
  obtain ⟨φ, hφx⟩ := exists_hom_carmichaelCycle (n := 8) (by norm_num) l42Gen l42Gen_pow_three
    l42Gen_mul_sq
  have hinj : Function.Injective φ := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      let k₀ : CarmichaelIndex 8 := ⟨2, by decide⟩
      have hk : carmichaelCycle k₀ ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφx] at hk
      have : l42Mat 0 = 1 := by
        have := congrArg Units.val hk
        simpa [l42Gen, l42Unit, carmichaelIndexToFin6, k₀] using this
      exact absurd this (by decide)
  have hcard : Nat.card (alternatingGroup (Fin 8)) = Nat.card (GL (Fin 4) (ZMod 2)) := by
    rw [card_GL_four_two, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact ⟨MulEquiv.ofBijective φ (Function.Injective.bijective_of_nat_card_le hinj hcard.ge), hφx⟩

theorem alt8WedgeDual_intertwine (φ : ↥(alternatingGroup (Fin 8)) →* GL (Fin 4) (ZMod 2))
    (hφ : ∀ k : CarmichaelIndex 8, φ (carmichaelCycle k) = l42Gen k)
    (σ : ↥(alternatingGroup (Fin 8))) :
    ∀ x : Fin 6 → ZMod 2,
      alt8WedgeB *ᵥ (alt8WedgeDual (φ σ) *ᵥ x) =
        SteinbergCB.I16.coords8.actA σ (alt8WedgeB *ᵥ x) := by
  have hσ : σ ∈ Subgroup.closure (Set.range (carmichaelCycle (n := 8))) := by
    rw [closure_range_carmichaelCycle (by norm_num)]
    exact Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
    obtain ⟨k, rfl⟩ := hσ
    intro x
    rw [hφ k, coords8_actA_carmichaelCycle k, alt8WedgeB_dual_l42Gen]
  | one =>
    intro x
    rw [map_one, map_one, map_one, Matrix.one_mulVec]
    rfl
  | mul σ τ _ _ ihσ ihτ =>
    intro x
    rw [map_mul φ, map_mul alt8WedgeDual, ← Matrix.mulVec_mulVec, ihσ, ihτ,
      map_mul SteinbergCB.I16.coords8.actA]
    rfl
  | inv σ _ ih =>
    intro x
    have h1 : alt8WedgeDual (φ σ) *ᵥ (alt8WedgeDual (φ σ⁻¹) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
        Matrix.one_mulVec]
    have h2 := ih (alt8WedgeDual (φ σ⁻¹) *ᵥ x)
    rw [h1] at h2
    rw [h2]
    show _ = (SteinbergCB.I16.coords8.actA σ⁻¹ * SteinbergCB.I16.coords8.actA σ) _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl

theorem exists_alt8_iso_wedgeDual :
    ∃ (θ : ↥(StatedSL 4 (ZMod 2)) ≃* ↥(alternatingGroup (Fin 8)))
      (B : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2)),
      ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (x : Fin 6 → ZMod 2),
        B ((minors4 (((γ⁻¹ : ↥(StatedSL 4 (ZMod 2))) : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)))ᵀ *ᵥ x) =
          SteinbergCB.I16.coords8.actA (θ γ) (B x) := by
  obtain ⟨φ, hφ⟩ := exists_iso_alt8_carm
  let θ : ↥(StatedSL 4 (ZMod 2)) ≃* ↥(alternatingGroup (Fin 8)) :=
    ((MulEquiv.subgroupCongr (statedSL_eq_top_of_card_two (by simp) 4)).trans
      Subgroup.topEquiv).trans φ.symm
  refine ⟨θ, alt8WedgeBEquiv, fun γ x => ?_⟩
  have hθ : φ (θ γ) = (γ : GL (Fin 4) (ZMod 2)) := by
    simp [θ]
  have h := alt8WedgeDual_intertwine φ.toMonoidHom hφ (θ γ) x
  have h' : alt8WedgeB *ᵥ (alt8WedgeDual (γ : GL (Fin 4) (ZMod 2)) *ᵥ x) =
      SteinbergCB.I16.coords8.actA (θ γ) (alt8WedgeB *ᵥ x) := by
    rw [← hθ]
    exact h
  exact h'

end CFSG.Quasithin

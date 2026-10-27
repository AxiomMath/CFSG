module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
import CFSG.LieType.SpecialLinear.ExteriorModel.AdjointHeart

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Layer
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {K : Type} [Field K] [Fintype K] [CharP K 2]

@[expose] noncomputable def pointsEquivFour : Fin 4 ≃ Set.powersetCard (Fin 4) 1 :=
  Equiv.ofBijective (fun a => ⟨{a}, Finset.card_singleton a⟩)
    ⟨fun a b h => Finset.singleton_injective (congrArg Subtype.val h), fun s => by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
      exact ⟨a, Subtype.ext ha.symm⟩⟩

theorem coe_pointsEquivFour (a : Fin 4) :
    ((pointsEquivFour a : Set.powersetCard (Fin 4) 1) : Finset (Fin 4)) = {a} := rfl

@[expose] noncomputable def complsEquivFour : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective (fun a => ⟨{a}ᶜ, by simp [Finset.card_compl]⟩)
    ⟨fun a b h => Finset.singleton_injective (compl_injective (congrArg Subtype.val h)),
      fun s => by
        have hc : (s : Finset (Fin 4))ᶜ.card = 1 := by
          rw [Finset.card_compl, s.2]
          rfl
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
        refine ⟨a, Subtype.ext ?_⟩
        show ({a}ᶜ : Finset (Fin 4)) = s
        rw [← ha, compl_compl]⟩

@[expose] noncomputable def slFrobAut (n r : ℕ) (K : Type) [Field K] [Fintype K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (iterateFrobeniusEquiv K 2 r : K →+* K))
    (Matrix.SpecialLinearGroup.map ((iterateFrobeniusEquiv K 2 r).symm : K →+* K))
    (by
      ext g i j
      exact (iterateFrobeniusEquiv K 2 r).symm_apply_apply _)
    (by
      ext g i j
      exact (iterateFrobeniusEquiv K 2 r).apply_symm_apply _)

theorem coe_slFrobAut (n r : ℕ) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ((slFrobAut n r K g : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K).map (iterateFrobenius K 2 r) := by
  ext i j
  simp [slFrobAut, Matrix.SpecialLinearGroup.map_apply_coe]

theorem extTwist_one_pointsEquivFour (r : ℕ) (g : Matrix.SpecialLinearGroup (Fin 4) K)
    (a b : Fin 4) :
    extTwist 4 1 r K g (pointsEquivFour a) (pointsEquivFour b) =
      ((slFrobAut 4 r K g : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        a b := by
  rw [coe_slFrobAut]
  exact AdjointHeartModel.minor_singleton rfl _ _ _ (coe_pointsEquivFour a)
    (coe_pointsEquivFour b)

theorem realizes_natSL4_of_extTwist_one (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)}
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) K) (r : ℕ)
    (β : W ≃+ (Set.powersetCard (Fin 4) 1 → K))
    (hβ : ∀ (l : ↥L) (w : W), β (binPsi θ (l : MulAut I) w) = extTwist 4 1 r K (ψ l) *ᵥ β w) :
    (FFModel.nat (StatedSL 4 K)).Realizes L ⊤ ⊥ := by
  classical
  let Θ : ↥L ≃* ↥(StatedSL 4 K) :=
    (ψ.trans (slFrobAut 4 r K)).trans (specialLinearGroupEquivStatedSL 4 K)
  let β' : W ≃+ (Fin 4 → K) :=
    β.trans (LinearEquiv.funCongrLeft K K pointsEquivFour).toAddEquiv
  refine realizes_nat_of_equiv θ Θ β' fun l w => ?_
  funext a
  have hl : ((Θ l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((slFrobAut 4 r K (ψ l) : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) := rfl
  change (β (binPsi θ (l : MulAut I) w)) (pointsEquivFour a) =
    (((Θ l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ fun b => β w (pointsEquivFour b)) a
  rw [hβ, hl, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← Equiv.sum_comp pointsEquivFour]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [extTwist_one_pointsEquivFour]

@[expose] noncomputable def slTransposeInvAut (n : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  let T := fun g : Matrix.SpecialLinearGroup (Fin n) K => Matrix.SpecialLinearGroup.transpose g
  have hT1 : T 1 = 1 := Subtype.ext (by
    simp [T, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_one])
  have hTmul : ∀ a b, T (a * b) = T b * T a := fun a b => Subtype.ext (by
    simp [T, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_mul])
  have hTT : ∀ a, T (T a) = a := fun a => Subtype.ext (by
    simp [T, Matrix.SpecialLinearGroup.coe_transpose])
  have hTinv : ∀ a, (T a)⁻¹ = T a⁻¹ := fun a =>
    (eq_inv_of_mul_eq_one_left (by rw [← hTmul, mul_inv_cancel, hT1])).symm
  let f : Matrix.SpecialLinearGroup (Fin n) K →* Matrix.SpecialLinearGroup (Fin n) K :=
    { toFun := fun g => T g⁻¹
      map_one' := by simp only [inv_one, hT1]
      map_mul' := fun g h => by simp only [_root_.mul_inv_rev, hTmul] }
  MonoidHom.toMulEquiv f f
    (by
      ext g : 1
      change T (T g⁻¹)⁻¹ = g
      rw [hTinv, inv_inv, hTT])
    (by
      ext g : 1
      change T (T g⁻¹)⁻¹ = g
      rw [hTinv, inv_inv, hTT])

omit [Fintype K] [CharP K 2] in
theorem coe_slTransposeInvAut (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin n) K) :
    ((slTransposeInvAut n K g : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (adjugate (g : Matrix (Fin n) (Fin n) K))ᵀ := by
  simp [slTransposeInvAut, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_inv]

theorem extTwist_three_complsEquivFour (r : ℕ) (g : Matrix.SpecialLinearGroup (Fin 4) K)
    (a b : Fin 4) :
    extTwist 4 3 r K g (complsEquivFour a) (complsEquivFour b) =
      ((slTransposeInvAut 4 K (slFrobAut 4 r K g) : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) a b := by
  rw [coe_slTransposeInvAut, coe_slFrobAut, Matrix.transpose_apply]
  exact AdjointHeartModel.minor_compl_eq_adjugate (n := 4) (by norm_num) _ a b

theorem realizes_natSL4_of_extTwist_three (θ : I ≃* Multiplicative W) {L : Subgroup (MulAut I)}
    (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) K) (r : ℕ)
    (β : W ≃+ (Set.powersetCard (Fin 4) 3 → K))
    (hβ : ∀ (l : ↥L) (w : W), β (binPsi θ (l : MulAut I) w) = extTwist 4 3 r K (ψ l) *ᵥ β w) :
    (FFModel.nat (StatedSL 4 K)).Realizes L ⊤ ⊥ := by
  classical
  let Θ : ↥L ≃* ↥(StatedSL 4 K) :=
    ((ψ.trans (slFrobAut 4 r K)).trans (slTransposeInvAut 4 K)).trans
      (specialLinearGroupEquivStatedSL 4 K)
  let β' : W ≃+ (Fin 4 → K) :=
    β.trans (LinearEquiv.funCongrLeft K K complsEquivFour).toAddEquiv
  refine realizes_nat_of_equiv θ Θ β' fun l w => ?_
  funext a
  have hl : ((Θ l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((slTransposeInvAut 4 K (slFrobAut 4 r K (ψ l)) : Matrix.SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) := rfl
  change (β (binPsi θ (l : MulAut I) w)) (complsEquivFour a) =
    (((Θ l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ fun b => β w (complsEquivFour b)) a
  rw [hβ, hl, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← Equiv.sum_comp complsEquivFour]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [extTwist_three_complsEquivFour]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

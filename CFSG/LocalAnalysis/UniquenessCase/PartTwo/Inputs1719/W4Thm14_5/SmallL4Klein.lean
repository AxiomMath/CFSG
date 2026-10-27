module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Nat
public import CFSG.RankThree.PartOne.K159.KleinModel
import CFSG.RankThree.GF2n.Stroth80.Sec717KleinRel
import CFSG.RankThree.PartOne.KF.ClsOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup.Layer
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.RankThree.PartOne.K159
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {K : Type} [Field K] [Fintype K] [CharP K 2]

@[expose] def kleinFst : Fin 3 ⊕ Fin 3 → Fin 4 := Sum.elim ![0, 0, 0] ![2, 1, 1]

@[expose] def kleinSnd : Fin 3 ⊕ Fin 3 → Fin 4 := Sum.elim ![1, 2, 3] ![3, 3, 2]

theorem kleinFst_lt_kleinSnd (i : Fin 3 ⊕ Fin 3) : kleinFst i < kleinSnd i := by
  rcases i with i | i <;> fin_cases i <;> decide

@[expose] def kleinPair (i : Fin 3 ⊕ Fin 3) : Set.powersetCard (Fin 4) 2 :=
  ⟨{kleinFst i, kleinSnd i}, Finset.card_pair (kleinFst_lt_kleinSnd i).ne⟩

theorem kleinPair_injective : Function.Injective kleinPair := by
  intro i j h
  have h' : ({kleinFst i, kleinSnd i} : Finset (Fin 4)) = {kleinFst j, kleinSnd j} :=
    congrArg Subtype.val h
  revert h'
  revert i j
  decide

@[expose] noncomputable def pairsEquivFour : Fin 3 ⊕ Fin 3 ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective kleinPair (kleinPair_injective.bijective_of_nat_card_le (by
    rw [Set.powersetCard.card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    decide))

theorem ofFinEmbEquiv_symm_kleinPair (i : Fin 3 ⊕ Fin 3) :
    (Set.powersetCard.ofFinEmbEquiv.symm (pairsEquivFour i) : Fin 2 → Fin 4) =
      ![kleinFst i, kleinSnd i] := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  refine (Finset.orderEmbOfFin_unique (pairsEquivFour i).prop (f := ![kleinFst i, kleinSnd i])
    (fun x => ?_) ?_).symm
  · fin_cases x
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · rw [Fin.strictMono_iff_lt_succ]
    intro x
    fin_cases x
    exact kleinFst_lt_kleinSnd i

theorem minor_pairsEquivFour {R : Type*} [CommRing R] (h : Matrix (Fin 4) (Fin 4) R)
    (i j : Fin 3 ⊕ Fin 3) :
    minor h (pairsEquivFour i) (pairsEquivFour j) =
      h (kleinFst i) (kleinFst j) * h (kleinSnd i) (kleinSnd j) -
        h (kleinFst i) (kleinSnd j) * h (kleinSnd i) (kleinFst j) := by
  rw [minor, ofFinEmbEquiv_symm_kleinPair, ofFinEmbEquiv_symm_kleinPair, Matrix.det_fin_two]
  simp

omit [Fintype K] [CharP K 2] in
theorem cong_apply_eq_sum_minor (h : Matrix (Fin 4) (Fin 4) K) (v : Fin 3 ⊕ Fin 3 → K)
    (i : Fin 3 ⊕ Fin 3) :
    Klein.cong h v i = ∑ j, minor h (pairsEquivFour i) (pairsEquivFour j) * v j := by
  simp only [minor_pairsEquivFour, Klein.cong_apply, Fintype.sum_sum_type, Fin.sum_univ_three]
  rcases i with i | i <;> fin_cases i <;>
    simp [Klein.coords, Klein.alt, CFSG.LocalAnalysis.antiMat, Matrix.mul_apply,
      Fin.sum_univ_four, kleinFst, kleinSnd] <;> ring

noncomputable def kleinOmegaEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 4) K ≃* ↥(StatedOmega (StatedQuadPlus 3 K)) :=
  let κ₀ : Matrix.SpecialLinearGroup (Fin 4) K →* GL (Fin 3 ⊕ Fin 3) K :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).symm.toMonoidHom.comp
      Klein.rho
  have hinj : Function.Injective κ₀ :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).symm.injective.comp
      Klein.rho_injective
  have hrange : κ₀.range = StatedOmega (StatedQuadPlus 3 K) := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      refine (CFSG.RankThree.GF2n.Stroth80.mem_statedOmega_quadPlus_three_iff _).mpr ⟨g, ?_⟩
      simp [κ₀]
    · intro hA
      obtain ⟨g, hg⟩ := (CFSG.RankThree.GF2n.Stroth80.mem_statedOmega_quadPlus_three_iff A).mp hA
      refine ⟨g, ?_⟩
      simp [κ₀, hg]
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem kleinOmegaEquiv_mulVec (g : Matrix.SpecialLinearGroup (Fin 4) K)
    (u : Fin 3 ⊕ Fin 3 → K) :
    (((kleinOmegaEquiv K g : ↥(StatedOmega (StatedQuadPlus 3 K))) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u = Klein.rho g u := by
  rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K)
    ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3) K).symm (Klein.rho g)) u = _
  rw [MulEquiv.apply_symm_apply]

theorem realizes_natOmegaPlus_of_extTwist_two (θ : I ≃* Multiplicative W)
    {L : Subgroup (MulAut I)} (ψ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 4) K) (r : ℕ)
    (β : W ≃+ (Set.powersetCard (Fin 4) 2 → K))
    (hβ : ∀ (l : ↥L) (w : W), β (binPsi θ (l : MulAut I) w) = extTwist 4 2 r K (ψ l) *ᵥ β w) :
    (FFModel.nat (StatedOmega (StatedQuadPlus 3 K))).Realizes L ⊤ ⊥ := by
  classical
  let Θ : ↥L ≃* ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    (ψ.trans (slFrobAut 4 r K)).trans (kleinOmegaEquiv K)
  let β' : W ≃+ (Fin 3 ⊕ Fin 3 → K) :=
    β.trans (LinearEquiv.funCongrLeft K K pairsEquivFour).toAddEquiv
  refine realizes_nat_of_equiv θ Θ β' fun l w => ?_
  have hΘ : ∀ u : Fin 3 ⊕ Fin 3 → K,
      (((Θ l : ↥(StatedOmega (StatedQuadPlus 3 K))) : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u =
        Klein.rho (slFrobAut 4 r K (ψ l)) u := fun u => kleinOmegaEquiv_mulVec _ u
  funext i
  change (β (binPsi θ (l : MulAut I) w)) (pairsEquivFour i) =
    ((((Θ l : ↥(StatedOmega (StatedQuadPlus 3 K))) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ fun j => β w (pairsEquivFour j)) i
  rw [hΘ, Klein.rho_apply, cong_apply_eq_sum_minor, hβ, Matrix.mulVec, dotProduct,
    ← Equiv.sum_comp pairsEquivFour]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_slFrobAut]
  rfl

theorem isOmegaPlus_six_of_mulEquiv {X : Type} [Group X] {e : ℕ} (hK : Nat.card K = 2 ^ e)
    (ψ : X ≃* Matrix.SpecialLinearGroup (Fin 4) K) : IsOmegaPlus X 6 e :=
  ⟨by decide, K, inferInstance, inferInstance, hK,
    ⟨(ψ.trans (kleinOmegaEquiv K)).trans
      (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
        (CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
          (n := 3) (by norm_num)))⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B5FinTransport
import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Omega4Plus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open CFSG.ComponentClassification.RankTwoClassical
open scoped MatrixGroups Matrix

theorem natOmegaPlus_of_natTensor {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {a : ℕ} (ha : 2 ≤ a) (h : NatTensor H U Z 2 a) :
    NatOmegaPlus H U Z 4 a := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  refine ⟨⟨2, rfl⟩, K, inferInstance, inferInstance, hK, ?_⟩
  show (FFModel.nat (StatedOmega (StatedQuadPlus 2 K))).Realizes H U Z
  let g : SL(2, K) × SL(2, K) →* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    thetaHom.codRestrict _ (thetaHom_mem h4)
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => thetaHom_injective (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨Y, hY⟩
    obtain ⟨x, hx⟩ := thetaHom_surj hY
    exact ⟨x, Subtype.ext hx⟩
  let e : SL(2, K) × SL(2, K) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) := MulEquiv.ofBijective g hg
  let s : SL(2, K) × SL(2, K) ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    MulEquiv.prodCongr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
  let θ : ↥(StatedOmega (StatedQuadPlus 2 K)) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    (e.symm.trans s).toMonoidHom
  let o : Multiplicative (Fin 2 ⊕ Fin 2 → K) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
    AddEquiv.toMultiplicative (oMat K).toAddEquiv
  let E : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) ≃*
      ↥(⊤ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K))) :=
    (Subgroup.topEquiv.trans o).trans Subgroup.topEquiv.symm
  refine ⟨π.comp θ, FFModel.RealizesVia.of_surjHom (FFModel.nat_isActionModel _) hπ θ
    (e.symm.trans s).surjective E.toMonoidHom E.surjective ?_ ?_⟩
  · intro (σ : ↥(StatedOmega (StatedQuadPlus 2 K)))
      (m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)))) hm
    have hσ : (σ : GL (Fin 2 ⊕ Fin 2) K) = thetaHom (e.symm σ) := by
      conv_lhs => rw [← e.apply_symm_apply σ]
      rfl
    show Multiplicative.ofAdd (oMat K
        (((σ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd (m : Multiplicative (Fin 2 ⊕ Fin 2 → K)))) =
      Multiplicative.ofAdd (((e.symm σ).1 : Matrix (Fin 2) (Fin 2) K) *
        oMat K (Multiplicative.toAdd (m : Multiplicative (Fin 2 ⊕ Fin 2 → K))) *
          ((e.symm σ).2 : Matrix (Fin 2) (Fin 2) K)ᵀ)
    rw [hσ, ← oMat_thetaHom (e.symm σ).1 (e.symm σ).2, Prod.mk.eta]
  · intro (m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))))
    have h1 : ∀ y : Multiplicative (Matrix (Fin 2) (Fin 2) K),
        y ∈ (⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K))) ↔ y = 1 :=
      fun y => Subgroup.mem_bot
    have h2 : ∀ y : Multiplicative (Fin 2 ⊕ Fin 2 → K),
        y ∈ (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) ↔ y = 1 :=
      fun y => Subgroup.mem_bot
    exact (h1 (o (m : Multiplicative (Fin 2 ⊕ Fin 2 → K)))).trans
      ((MulEquiv.map_eq_one_iff o).trans (h2 _).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

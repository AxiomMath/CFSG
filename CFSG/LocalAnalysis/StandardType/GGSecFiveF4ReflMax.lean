module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfType
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
import CFSG.LocalAnalysis.StandardType.GGLargeRowCard
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem GGSecFiveRouteCfg.card_eq_of_typeF4
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M) :
    Nat.card (ggAutomizerJoin L Bs 𝒦) = 1152 ∧ Nat.card Bs ≤ p ^ 4 := by
  obtain ⟨σ, rfl⟩ := hM
  have hcard : Nat.card (ggAutomizerJoin L Bs 𝒦) = 1152 := by
    calc Nat.card (ggAutomizerJoin L Bs 𝒦) =
          Nat.card ((CoxeterMatrix.F₄).reindex σ).Group := (Nat.card_congr e.toEquiv).symm
      _ = Nat.card (CoxeterMatrix.F₄).Group :=
          Nat.card_congr ((CoxeterMatrix.F₄).reindexGroupEquiv σ).toEquiv
      _ = 1152 := l04fFRC_ord_card_coxeterF4
  refine ⟨hcard, ?_⟩
  have hW : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs 𝒦) :=
    GGWeylOfType.of_reindex (M := CoxeterMatrix.F₄) (e := σ) ⟨e, hP.2⟩
  simpa using hR.card_le_pow_of_weylOfType hTBF hWI (le_refl _) hW

private theorem false_of_weylInf_typeB_of_F4
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    {ι' : Type} {M' : CoxeterMatrix ι'} (hB : GGIsWeylMatrixB M')
    (f : M'.Group ≃* ↥(ggAInf p B Bs x L D J))
    (hf : ∀ i : ι', GGIsReflection p
      ((f (M'.simple i) : ↥(ggAInf p B Bs x L D J)) : MulAut ↥Bs)) : False := by
  obtain ⟨m, σ, hm, rfl⟩ := hB
  obtain ⟨hcardK, hBs_le4⟩ := hR.card_eq_of_typeF4 hTBF hWI e hP hM
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hWeylB : GGWeylOfType p (CoxeterMatrix.B m) (ggAInf p B Bs x L D J) :=
    GGWeylOfType.of_reindex (M := CoxeterMatrix.B m) (e := σ) ⟨f, hf⟩
  have hpm : p ^ m ≤ Nat.card Bs := pow_le_card_of_weylOfType_B hp hp2 hBs hm hWeylB
  have hm4 : m ≤ 4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hpm.trans hBs_le4)
  have hcardA : Nat.card (ggAInf p B Bs x L D J) = 2 ^ m * m.factorial := by
    rw [← Nat.card_congr f.toEquiv]
    rw [Nat.card_congr ((CoxeterMatrix.B m).reindexGroupEquiv σ).toEquiv,
      ggCoxeterB_card m hm]
  have hle : 1152 ≤ Nat.card (ggAInf p B Bs x L D J) := by
    rw [← hcardK]
    exact Subgroup.card_le_of_le (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1)
  have hupper : Nat.card (ggAInf p B Bs x L D J) ≤ 384 := by
    rw [hcardA]
    calc 2 ^ m * m.factorial ≤ 2 ^ 4 * (4 : ℕ).factorial :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hm4) (Nat.factorial_le hm4)
      _ = 384 := by norm_num
  omega

theorem GGSecFiveRouteCfg.ggAInf_eq_of_weylInf_F4
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hM : GGIsWeylMatrixF4 M)
    (hW : GGWeylReflectionGroup p (ggAInf p B Bs x L D J)) :
    ggAInf p B Bs x L D J = ggAutomizerJoin L Bs 𝒦 := by
  obtain ⟨ι', M', hM', f, hf⟩ := hW
  rcases hR.weylInf_isWeylMatrixB_or_F4 hTBF hWI e hP (Or.inr hM) hM' f hf with hB | hF
  · exact (false_of_weylInf_typeB_of_F4 hR hTBF hWI e hP hM hB f hf).elim
  · obtain ⟨σ, rfl⟩ := hF
    have hcardA : Nat.card (ggAInf p B Bs x L D J) = 1152 := by
      calc Nat.card (ggAInf p B Bs x L D J) =
            Nat.card ((CoxeterMatrix.F₄).reindex σ).Group := (Nat.card_congr f.toEquiv).symm
        _ = Nat.card (CoxeterMatrix.F₄).Group :=
            Nat.card_congr ((CoxeterMatrix.F₄).reindexGroupEquiv σ).toEquiv
        _ = 1152 := l04fFRC_ord_card_coxeterF4
    have hcardK : Nat.card (ggAutomizerJoin L Bs 𝒦) = 1152 :=
      (hR.card_eq_of_typeF4 hTBF hWI e hP hM).1
    refine (Subgroup.eq_of_le_of_card_ge (GGNbrSet.automizerJoin_le_ggAInf hR.2.2.2.1) ?_).symm
    rw [hcardA, hcardK]

theorem ggSecFiveReflMaxAt_F4_of_weylInfAt
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hW : GGSecFiveWeylInfAt fun M => GGIsWeylMatrixF4 M) :
    GGSecFiveReflMaxAt fun M => GGIsWeylMatrixF4 M := by
  intro G _ _ p B Bs x L D J 𝒦 hR ι M e hP hM
  have hW' := hW G p B Bs x L D J 𝒦 hR ι M e hP hM
  exact ggRM_of_witness hR.2.2.2
    ⟨hW', ⟨𝒦, hR.2.2.2.1, (hR.ggAInf_eq_of_weylInf_F4 hTBF hWI e hP hM hW').symm⟩⟩

end CFSG.StandardType

end

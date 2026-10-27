module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Seven
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Three
public import CFSG.Quasithin.Vol2.Ch8Sec2L822A
public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22Xi

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319
open scoped IsMulCommutative

@[expose] def Res822CoverV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I → Row711M22Code T L I →
      ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
      (∃ _ : ((pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L)).Normal,
        IsHat (↥(fsuL0 T L) ⧸ (pCoreOf 2 (fsuL0 T L)).subgroupOf (fsuL0 T L))
          (CFSG.Blueprint.NativeSporadic.Carrier .M22)) →
      ∀ H : Subgroup G, IsHStar T (fsuM T L) H → fsuV T I ≤ pCoreOf 2 H →
        ∀ L' N : Subgroup G, IsChiefStep H (conjClosure (fsuV T I) H) L' N →
          ¬ IsCentralStep H L' N →
          ¬ (∃ _ : (L'.subgroupOf N).Normal,
              QuotIsoWith H (cSecIn H L' N) (thompsonJ H) (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 5)) ∧
                NaturalSn 5 H L' N) ∧
          ¬ (∃ _ : (L'.subgroupOf N).Normal,
              QuotIsoWith H (cSecIn H L' N) (thompsonJ H) (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))
                (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5)) ∧ NaturalSnPair 5 H L' N)

theorem step822M22_ofV (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK)
    (hSix : Lemma319SixPlusD) (hKer : Lemma319KerNoThree) (hNoS5 : Lemma319NoS5)
    (hM22 : M22Facts822) (h3cov : Res822ThreeCover) (hcJ3 : Res822CoverJ3)
    (hcov : Res822CoverV) (hKz : Res822Kz) : Step822M22 := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  obtain ⟨hmin, hsq, hchar, hHMN⟩ :=
    setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp hTL hH
  have h318 := hyp318_of_normal h37 h38 h39 h3228 hyp hTL hH
  have h315 := h318.hyp315 hyp.fsu.sylow hH
  have hbase : Hyp315Base T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) := h315.toHyp315Base
  obtain ⟨hq, hdual, h6i, h6ii, h6iii⟩ :=
    hM22 G T L I hyp h731 h821 hc hrow hrowM hnot hbase.reduced.2.2.1
  have hII : Hyp315.CaseII (fsuM T L) H (fsuV T I) := hHMN
  have h319 : Hyp319 T (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) :=
    ⟨hbase, hII, hq, h318.unique, hVH, hdual⟩
  have hconcl := Hyp319.concl_core hC58 hD15 hS316 hD125 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow h318.inM h319
  have hKS : KerNoThree (fsuM T L) H ∧ NoS5Shape (fsuV T I) H := by
    by_cases hn : NoThreeInCV (fsuM T L) (fsuV T I)
    · exact ⟨hKer G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
          (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM hbase hII hq h318.unique hVH
          (fun ⟨_, hd⟩ => hdual hd) hconcl hn,
        hNoS5 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
          (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM hbase hII hq h318.unique hVH
          (fun ⟨_, hd⟩ => hdual hd) hconcl h6i h6iii hn⟩
    · have hcover := h3cov G T L I hyp h731 h821 hc hrow hrowM hnot hn
      exact ⟨hcJ3 G T L I hyp h731 h821 hc hrow hrowM hnot hcover H hH hVH,
        hcov G T L I hyp h731 h821 hc hrow hrowM hnot hcover H hH hVH⟩
  obtain ⟨-, φ, hφs, hφk⟩ := hSix G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hyp.fsu.sylow
    (fsuM T L) (fsuL0 T L ⊔ T) H (fsuV T I) h318.inM hbase hII hq h318.unique hVH
    (fun ⟨_, hd⟩ => hdual hd) hconcl h6i h6ii h6iii hKS.1 hKS.2
  have hXi : IsXi T (twoResidual H) :=
    isXi_of_quot_S3Wr (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1) hH.1.2 φ hφs hφk
  exact hKz G T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH hXi ⟨φ, hφs, hφk⟩

end CFSG.Quasithin.H13

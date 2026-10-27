module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Fixed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Sylow
import CFSG.Quasithin.Background.OrderingMax
import CFSG.GroupTheory.HuppertProduct.Quotient
import CFSG.GroupTheory.PCoreJoin
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_notationB8103 (hK2 : KU45Syl3) {L P B : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hB : F08.NotationB8103 L P n B) :
    P ≤ centralizer (B : Set G) := by
  intro p hpP
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hb3 : b ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := B) (x := ⟨b, hb⟩)
    rw [hB.1] at h
    simpa using congrArg Subtype.val h
  have hbc : b ∈ centralizer (P : Set G) :=
    mem_centralizer_of_isSylowOf hK2 hX hP hP.isPGroup
      (hP.le.trans Subgroup.le_normalizer) le_rfl (hB.2.1 hb) hb3
  exact ((Subgroup.mem_centralizer_iff.mp hbc) p hpP).symm

private theorem le_pCoreOf_and_coe_eq_mul_of_le_normalizer {V K P : Subgroup G}
    (hV2 : IsPGroup 2 V) (hKV : K ≤ normalizer (V : Set G))
    (hPV : P ≤ normalizer (V : Set G)) (hPK : P ≤ normalizer (K : Set G)) :
    V ≤ pCoreOf 2 (V ⊔ K ⊔ P) ∧
      ((V ⊔ K ⊔ P : Subgroup G) : Set G) =
        (pCoreOf 2 (V ⊔ K ⊔ P) : Set G) * (K : Set G) * (P : Set G) := by
  have hPKV : K ⊔ P ≤ normalizer (V : Set G) := sup_le hKV hPV
  have hVcore : V ≤ pCoreOf 2 (V ⊔ K ⊔ P) := by
    have h := CFSG.GroupTheory.pCoreOf_sup_le_pCoreOf_sup (Y := K ⊔ P) (U := V) hV2 hPKV
    rw [show (K ⊔ P) ⊔ V = V ⊔ K ⊔ P by rw [sup_comm (K ⊔ P) V, sup_assoc]] at h
    exact (le_sup_right : V ≤ pCoreOf 2 (K ⊔ P) ⊔ V).trans h
  have hPsup : P ≤ normalizer ((V ⊔ K : Subgroup G) : Set G) :=
    CFSG.GroupTheory.HuppertProduct.le_normalizer_sup hPV hPK
  have hHset : ((V ⊔ K ⊔ P : Subgroup G) : Set G) =
      (V : Set G) * (K : Set G) * (P : Set G) := by
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (V ⊔ K) P hPsup,
      Subgroup.coe_mul_of_right_le_normalizer_left V K hKV]
  refine ⟨hVcore, le_antisymm ?_ ?_⟩
  · rw [hHset]
    exact Set.mul_subset_mul (Set.mul_subset_mul hVcore (le_refl _)) (le_refl _)
  · intro x hx
    rw [Set.mem_mul] at hx
    obtain ⟨y, hy, z, hz, hxy⟩ := hx
    rw [Set.mem_mul] at hy
    obtain ⟨o, ho, k, hk, hyk⟩ := hy
    rw [← hxy, ← hyk]
    have hkH : k ∈ V ⊔ K ⊔ P := Subgroup.mem_sup_left (Subgroup.mem_sup_right hk)
    have hzH : z ∈ V ⊔ K ⊔ P := Subgroup.mem_sup_right hz
    exact (V ⊔ K ⊔ P).mul_mem
      ((V ⊔ K ⊔ P).mul_mem ((CFSG.LieType.BorelTits.pCoreOf_le 2 _) ho) hkH) hzH

private theorem sup_sup_le_and_le_normalizer_of_hyp8102 (hK2 : KU45Syl3) {D : Data G}
    {L P B : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n)
    (hB : F08.NotationB8103 L P n B) :
    (pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P ≤ D.M) ∧
      F08.KOf8103 L B ≤ normalizer (pCoreOf 2 D.M ⊓ centralizer (B : Set G) : Set G) ∧
      P ≤ normalizer (pCoreOf 2 D.M ⊓ centralizer (B : Set G) : Set G) ∧
      P ≤ normalizer (F08.KOf8103 L B : Set G) := by
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  have hLDM : L ≤ D.M := hH.1.1.le
  have hKX : F08.KOf8103 L B ≤ L ⊓ centralizer (B : Set G) := by
    rw [F08.KOf8103]
    exact Subgroup.map_subtype_le _
  have hKDM : F08.KOf8103 L B ≤ D.M := hKX.trans (inf_le_left.trans hLDM)
  have hKC : F08.KOf8103 L B ≤ centralizer (B : Set G) := hKX.trans inf_le_right
  have hPC : P ≤ centralizer (B : Set G) := le_centralizer_of_notationB8103 hK2 hX hP hB
  have hPDM : P ≤ D.M := hP.le.trans hLDM
  have hVDM : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≤ D.M :=
    inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hO2M : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  refine ⟨sup_le (sup_le hVDM hKDM) hPDM, ?_, ?_, ?_⟩
  · exact (le_inf (hKDM.trans hO2M) (hKC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · exact (le_inf (hPDM.trans hO2M) (hPC.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · rw [F08.KOf8103]
    exact (le_inf hP.le hPC).trans
      (Subgroup.le_normalizer.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _))

theorem sup_mem_calK8104 (hK2 : KU45Syl3) {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hB : F08.NotationB8103 L P n B)
    (hV : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≠ ⊥) :
    pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P ∈
      PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B) := by
  obtain ⟨hHDM, hKV, hPV, hPK⟩ :=
    sup_sup_le_and_le_normalizer_of_hyp8102 hK2 hH hX hB
  have hV2 : IsPGroup 2 (pCoreOf 2 D.M ⊓ centralizer (B : Set G) : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M).to_le inf_le_left
  obtain ⟨hVcore, hHset⟩ :=
    le_pCoreOf_and_coe_eq_mul_of_le_normalizer hV2 hKV hPV hPK
  have hKH : F08.KOf8103 L B ≤
      pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P :=
    le_sup_right.trans le_sup_left
  refine ⟨hHDM, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot] at hVcore
    exact hV (le_bot_iff.mp hVcore)
  · exact hKH
  · rw [inf_eq_left.mpr hKH]
    exact hHset

theorem pCoreOf_two_centralizer_eq_bot_at (hK2 : KU45Syl3) {D : Data G}
    {L P B : Subgroup G} {p n : ℕ} (h8105 : R8105.R8105At D L P n)
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hB : F08.NotationB8103 L P n B)
    (hBM : ¬ centralizer (B : Set G) ≤ D.M) (hV : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≠ ⊥) :
    pCoreOf 2 (centralizer (B : Set G)) = ⊥ := by
  set X : Subgroup G := centralizer (B : Set G) with hXdef
  set O : Subgroup G := pCoreOf 2 X with hOdef
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  by_contra hO
  have hO2 : IsPGroup 2 O := by
    rw [hOdef]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hloc : IsTwoLocal (normalizer (O : Set G)) := ⟨O, hO, hO2, rfl⟩
  obtain ⟨N, hN, hNge⟩ := CFSG.Quasithin.exists_maxTwoLocal_ge hloc
  have hXN : X ≤ N :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans hNge
  have hPC : P ≤ X := by
    rw [hXdef]
    exact le_centralizer_of_notationB8103 hK2 hX hP hB
  have hVX : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ≤ X := by
    rw [hXdef]
    exact inf_le_right
  have hKX : F08.KOf8103 L B ≤ X := by
    rw [F08.KOf8103]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hHleX : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P ≤ X :=
    sup_le (sup_le hVX hKX) hPC
  have hHleN : pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P ≤ N :=
    hHleX.trans hXN
  have hmem : (pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P) ∈
      PartTwo.Inputs1719.PartOne.calK8104 D P (F08.KOf8103 L B) :=
    sup_mem_calK8104 hK2 hH hX hB hV
  have huniq := h8105 B hB _ hmem
  have hNmem : N ∈ calMOf (pCoreOf 2 D.M ⊓ centralizer (B : Set G) ⊔ F08.KOf8103 L B ⊔ P) :=
    ⟨hN, hHleN⟩
  rw [huniq] at hNmem
  have hNDM : N = D.M := by simpa using hNmem
  exact hBM (hXN.trans (le_of_eq hNDM))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentPermutesGeneric
public import CFSG.LocalAnalysis.WeakClosure81.OrbitClosureCentreQuot
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarImageCalC
import CFSG.GroupTheory.BarImageConj
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barImage_centerQuot_A6 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    Nonempty ((↥(UC22.barImage (L ⊔ D.T) L) ⧸
      Subgroup.center ↥(UC22.barImage (L ⊔ D.T) L)) ≃* alternatingGroup (Fin 6)) := by
  have hHM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hHM
  obtain ⟨e, -⟩ := UC22.uc22p20d_bar2Equiv le_sup_left hsub
  obtain ⟨e6⟩ := centerQuot_of_barO2Z (X := alternatingGroup (Fin 6)) hL hshape
  have eZ : (Bar2 L ⧸ Subgroup.center (Bar2 L)) ≃*
      (↥(UC22.barImage (L ⊔ D.T) L) ⧸
        Subgroup.center ↥(UC22.barImage (L ⊔ D.T) L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact ⟨eZ.symm.trans e6⟩

theorem exists_barImage_pow_four_not_mem_centralizer {D : Data G} {L : Subgroup G}
    (hexp : ¬ ExpFourAut17 D L) :
    ∃ t ∈ UC22.barImage (L ⊔ D.T) D.T,
      t ∈ Subgroup.normalizer (UC22.barImage (L ⊔ D.T) L :
        Set (Bar2 (L ⊔ D.T))) ∧
      t ^ 4 ∉ Subgroup.centralizer (UC22.barImage (L ⊔ D.T) L :
        Set (Bar2 (L ⊔ D.T))) := by
  classical
  change ¬ ∀ t ∈ NTL17 D L, t ^ 4 ∈ centSection (L ⊔ D.T) L
    (CFSG.Open.pCoreOf 2 L) at hexp
  push Not at hexp
  obtain ⟨t, htNTL, ht4⟩ := hexp
  have htT : t ∈ D.T := htNTL.1
  have htNorm : t ∈ Subgroup.normalizer (L : Set G) := htNTL.2
  have htN : t ∈ L ⊔ D.T := Subgroup.mem_sup_right htT
  let N : Subgroup G := L ⊔ D.T
  let tN : ↥N := ⟨t, htN⟩
  let tbar : Bar2 N := QuotientGroup.mk tN
  have htbar_mem : tbar ∈ UC22.barImage N D.T :=
    Subgroup.mem_map.mpr ⟨tN, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
  have htbar_norm : tbar ∈ Subgroup.normalizer
      (UC22.barImage N L : Set (Bar2 N)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconjL : L.map (MulAut.conj t).toMonoidHom = L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp htNorm
    have hbar : (UC22.barImage N L).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨t, htN⟩)).toMonoidHom =
        UC22.barImage N (L.map (MulAut.conj t).toMonoidHom) :=
      (CFSG.GroupTheory.barImage_map_conj N L le_sup_left htN).symm
    rw [hconjL] at hbar
    simpa [tbar, tN, QuotientGroup.mk'_apply] using hbar
  refine ⟨tbar, htbar_mem, htbar_norm, ?_⟩
  intro hcent
  have hcentSection : t ^ 4 ∈ centSection N L (CFSG.Open.pCoreOf 2 L) := by
    refine ⟨Subgroup.pow_mem N htN 4, Subgroup.pow_mem _ htNorm 4,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
        (Subgroup.pow_mem _ htNorm 4), ?_⟩
    intro a ha
    let aN : ↥N := ⟨a, Subgroup.mem_sup_left ha⟩
    have haK : (QuotientGroup.mk aN : Bar2 N) ∈ UC22.barImage N L :=
      Subgroup.mem_map.mpr ⟨aN, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hcomm : (QuotientGroup.mk aN : Bar2 N) * tbar ^ 4 =
        tbar ^ 4 * (QuotientGroup.mk aN : Bar2 N) :=
      Subgroup.mem_centralizer_iff.mp hcent _ haK
    let w : G := t ^ 4 * a * (t ^ 4)⁻¹ * a⁻¹
    have hwN : w ∈ N := by
      exact N.mul_mem (N.mul_mem (N.mul_mem (Subgroup.pow_mem N htN 4) (Subgroup.mem_sup_left ha))
        (N.inv_mem (Subgroup.pow_mem N htN 4))) (N.inv_mem (Subgroup.mem_sup_left ha))
    let wN : ↥N := ⟨w, hwN⟩
    have hwq : (QuotientGroup.mk wN : Bar2 N) = 1 := by
      have h1 : wN = tN ^ 4 * aN * (tN ^ 4)⁻¹ * aN⁻¹ := by
        ext
        simp [wN, w, tN, aN]
      rw [h1]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      calc (QuotientGroup.mk tN : Bar2 N) ^ 4 * (QuotientGroup.mk aN : Bar2 N) *
            ((QuotientGroup.mk tN : Bar2 N) ^ 4)⁻¹ *
            (QuotientGroup.mk aN : Bar2 N)⁻¹
          = ((QuotientGroup.mk aN : Bar2 N) * (QuotientGroup.mk tN : Bar2 N) ^ 4) *
            ((QuotientGroup.mk tN : Bar2 N) ^ 4)⁻¹ *
            (QuotientGroup.mk aN : Bar2 N)⁻¹ := by rw [← hcomm]
        _ = 1 := by group
    have hwmem : wN ∈ CFSG.pCore 2 ↥N := (QuotientGroup.eq_one_iff wN).mp hwq
    have hwP : ((wN : ↥N) : G) ∈ CFSG.Open.pCoreOf 2 N :=
      Subgroup.mem_map_of_mem N.subtype hwmem
    have hwPN : w ∈ CFSG.Open.pCoreOf 2 N := by simpa [wN] using hwP
    have hconjL : t ^ 4 * a * (t ^ 4)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htNorm 4) a).mp ha
    have hwL : w ∈ L := by
      have hweq : w = (t ^ 4 * a * (t ^ 4)⁻¹) * a⁻¹ := rfl
      rw [hweq]
      exact L.mul_mem hconjL (L.inv_mem ha)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left ⟨hwL, hwPN⟩
  exact absurd (show t ^ 4 ∈ centSection (L ⊔ D.T) L (CFSG.Open.pCoreOf 2 L)
    from hcentSection) ht4

theorem inFSq_one_of_not_expFour (h410 : W4Lem4_10) (h43c : W3Lem45_2Chief)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hshape : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin 6)))
    (hexp : ¬ ExpFourAut17 D L) : InFSq 1 (L ⊔ D.T) := by
  have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 (L ⊔ D.T))) = ⊥ := by
    rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot]
  refine inFSq_of_components h43c (m := 1) (by norm_num)
    (barImage_component_of_calC hL) (barImage_T_sylow_of_calC hL)
    (orbitClosure_sup_of_calC hL) ?_
  exact compFactorAutInF_one_of_orbitClosure_A6 h410 hO2
    (barImage_component_of_calC hL) (barImage_T_sylow_of_calC hL)
    (orbitClosure_sup_of_calC hL) (barImage_centerQuot_A6 hL hshape)
    (exists_barImage_pow_four_not_mem_centralizer hexp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

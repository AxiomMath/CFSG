module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.Module
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFiveA
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xf
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22P22x

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private def modO2Centralizer (M L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ M ∧ ∀ x ∈ L, ⁅x, g⁆ ∈ pCoreOf 2 M}
  one_mem' := ⟨M.one_mem, fun x _ => by simpa using (pCoreOf 2 M).one_mem⟩
  mul_mem' := by
    rintro g h ⟨hgM, hg⟩ ⟨hhM, hh⟩
    refine ⟨M.mul_mem hgM hhM, fun x hx => ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using (pCoreOf 2 M).mul_mem (hg x hx)
      (CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hgM (hh x hx))
  inv_mem' := by
    rintro g ⟨hgM, hg⟩
    refine ⟨M.inv_mem hgM, fun x hx => ?_⟩
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa using CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (M.inv_mem hgM)
      ((pCoreOf 2 M).inv_mem (hg x hx))

private theorem mem_modO2Centralizer {M L : Subgroup G} {g : G} :
    g ∈ modO2Centralizer M L ↔ g ∈ M ∧ ∀ x ∈ L, ⁅x, g⁆ ∈ pCoreOf 2 M := Iff.rfl

theorem exists_isMaxElemAbelian_not_mem {M T L : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hL : F12.IsComponentModO2 M L)
    (hJ : ¬ ⁅F12.jOf T, L⁆ ≤ pCoreOf 2 L) :
    ∃ A : Subgroup G, IsMaxElemAbelian M A ∧ ∃ x ∈ L, ∃ a ∈ A, ⁅x, a⁆ ∉ pCoreOf 2 M := by
  classical
  by_contra hcon
  push Not at hcon
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf T M :=
    QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT
  have hle : ∀ A : Subgroup G, IsMaxElemAbelian T A → A ≤ modO2Centralizer M L := by
    intro A hA
    have hAM : IsMaxElemAbelian M A := isMaxElemAbelian_of_isSylowTwoOf hT' hA
    exact fun a ha => mem_modO2Centralizer.mpr
      ⟨hAM.1 ha, fun x hx => hcon A hAM x hx a ha⟩
  have hj : F12.jOf T ≤ modO2Centralizer M L := P22x.jOf_le_of_forall_isMax hle
  have hcomm : ⁅F12.jOf T, L⁆ ≤ pCoreOf 2 M := by
    rw [Subgroup.commutator_le]
    intro g hg x hx
    have h1 : ⁅x, g⁆ ∈ pCoreOf 2 M := (mem_modO2Centralizer.mp (hj hg)).2 x hx
    rw [← commutatorElement_inv]
    exact (pCoreOf 2 M).inv_mem h1
  exact hJ (hcomm.trans (le_of_eq (TwelveTwentyFive.pCoreOf_eq hL).symm))

theorem isFFStarOffender_autI {M V A : Subgroup G} (hVe : IsElemAbelian 2 V) (hVM : V ≤ M)
    (hMN : M ≤ normalizer (V : Set G)) (hA : IsMaxElemAbelian M A) (hne : autI hVe A ≠ ⊥) :
    IsFFStarOffender (autI hVe M) (autI hVe A) :=
  ⟨autI_mono hVe hA.1, hne, isElemAbelian2_autI hVe hA.2.1 (hA.1.trans hMN), fun B hB =>
    (offender_core hVe hVM hMN hA hB).1⟩

theorem commutator_autI_ne_bot {M V L A : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ normalizer (V : Set G)) (hP : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hL : F12.IsComponentModO2 M L) (hLV : ⁅L, V⁆ ≠ ⊥) (hAM : A ≤ M)
    (hA : ∃ x ∈ L, ∃ a ∈ A, ⁅x, a⁆ ∉ pCoreOf 2 M) :
    ⁅autI hVe L, autI hVe A⁆ ≠ ⊥ := by
  intro hbot
  have hLM : L ≤ M := hL.2.1
  set K : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hK
  have hKM : K ≤ M := by rw [hK]; exact inf_le_left
  have hCVn : M ≤ normalizer ((Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    hMN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (V : Set G))).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (V : Set G)))
  have hKn : M ≤ normalizer (K : Set G) := by
    rw [hK]
    exact (le_inf (Subgroup.le_normalizer (H := M)) hCVn).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPK : pCoreOf 2 M ≤ K := by
    rw [hK]
    exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hP
  have hLK : ¬ L ≤ K := by
    intro hle
    apply hLV
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [hK] at hle
    exact hle.trans inf_le_right
  have hLA : ∀ x ∈ L, ∀ a ∈ A, ⁅x, a⁆ ∈ K := by
    intro x hx a ha
    have hxM : x ∈ M := hLM hx
    have haM : a ∈ M := hAM ha
    set xM : ↥M := ⟨x, hxM⟩ with hxMdef
    set aM : ↥M := ⟨a, haM⟩ with haMdef
    have hxI : convHom hVe M hMN xM ∈ autI hVe L := by
      rw [autI_eq_map_convHom hVe hMN hLM]
      exact Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have haI : convHom hVe M hMN aM ∈ autI hVe A := by
      rw [autI_eq_map_convHom hVe hMN hAM]
      exact Subgroup.mem_map.mpr ⟨aM, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hmem := Subgroup.commutator_mem_commutator hxI haI
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : convHom hVe M hMN ⁅xM, aM⁆ = 1 := by
      rw [map_commutatorElement]
      exact hmem
    have h2 : ⁅xM, aM⁆ ∈ (M ⊓ Subgroup.centralizer (V : Set G)).subgroupOf M := by
      rw [← ker_convHom hVe M hMN]
      exact h1
    have h3 : ((⁅xM, aM⁆ : ↥M) : G) ∈ M ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.mem_subgroupOf.mp h2
    have h4 : ((⁅xM, aM⁆ : ↥M) : G) = ⁅x, a⁆ := by
      show M.subtype ⁅xM, aM⁆ = ⁅x, a⁆
      rw [map_commutatorElement, hxMdef, haMdef]
      rfl
    rw [hK, ← h4]
    exact h3
  obtain ⟨x, hx, a, ha, hne⟩ := hA
  exact hne (TwelveTwentyFive.commutator_mem_pCoreOf hL hKM hKn hPK hLK hAM hLA x hx a ha)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

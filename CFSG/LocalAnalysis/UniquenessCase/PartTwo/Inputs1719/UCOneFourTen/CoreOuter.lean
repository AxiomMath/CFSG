module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreOuterSetup
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OuterQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OuterTorus
import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OddCentre
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private lemma coreOuter_center_eq_bot_of_lieModel_psp {K : Type} [Group K] [Finite K]
    (hKq : CFSG.IsQuasisimple K) (hodd : Odd (Nat.card ↥(Subgroup.center K)))
    {n : ℕ} (h : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp 2 2 n)
    (hn3 : 3 ≤ n) :
    Subgroup.center K = ⊥ := by
  obtain ⟨F, hField, hFinite, hFcard, he⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psp_of_lieModel
      h.admissible h
  have hFge : 5 ≤ Nat.card F := by
    rw [hFcard]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨e⟩ := he
  exact @CFSG.SectionRank.QTK.Insp443.center_eq_bot_of_psp4 K _ _ hKq hodd
    F hField hFinite hFge e

theorem coreOuterSlice :
    CoreOuterSlice := by
  intro X _ _ K L T Y n h hev hL2 hodd
  classical
  have hKn : K.Normal := h.normal
  obtain ⟨_, z, _, _, hz2, _, _, _, hcomp, hout⟩ :=
    h.exists_outer_involution hL2 hodd
  have hn : Odd n := h.odd_three_le.1
  have hn3 : 3 ≤ n := h.odd_three_le.2
  have hpsp : CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSp 2 2 n :=
    h.lieModel_psp_of_outer hev hL2 hz2 hcomp hout
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mpr
        h.quasisimple)
  have hZbot : Subgroup.center ↥K = ⊥ :=
    coreOuter_center_eq_bot_of_lieModel_psp hKq h.odd_card_center hpsp hn3
  have hK : CFSG.Blueprint.LieModel ↥K .PSp 2 2 n :=
    CFSG.Blueprint.LieModel.of_quotient_center hZbot hpsp
  let ψ : MulAut ↥K := @MulAut.conjNormal X _ K hKn z
  have hψ2 : orderOf ψ = 2 :=
    @orderOf_conjNormal_eq_two X _ K hKn z hz2 hout
  have hψout : ψ ∉ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    @conjNormal_not_mem_range X _ K hKn z hout
  have hfix : (fixedSubgroup ψ).map K.subtype = K ⊓ centralizer ({z} : Set X) :=
    @map_fixedSubgroup_conjNormal X _ K hKn z
  obtain ⟨hsimp, A, hAF, hAp, hA2, g, hgA, hgN⟩ :=
    exists_prime_centralizer_not_le_normalizer_psp hK hn ψ hψ2 hψout
  have hKCsimp : IsSimpleGroup ↥(K ⊓ centralizer ({z} : Set X)) := by
    have hmap : IsSimpleGroup ↥((fixedSubgroup ψ).map K.subtype) :=
      @MulEquiv.isSimpleGroup _ _ _ _ hsimp
        (Subgroup.equivMapOfInjective (fixedSubgroup ψ) K.subtype
          K.subtype_injective).symm
    rwa [hfix] at hmap
  have hcompA : CFSG.Assembly.IsComponentOf L (K ⊓ centralizer ({z} : Set X)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L
      (K ⊓ centralizer ({z} : Set X))).mpr hcomp
  have hL_eq : L = K ⊓ centralizer ({z} : Set X) :=
    @CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup
      X _ L (K ⊓ centralizer ({z} : Set X)) hKCsimp hcompA
  let A' : Subgroup X := A.map K.subtype
  have hA'L : A' ≤ L := by
    intro x hx
    rw [hL_eq, ← hfix]
    exact Subgroup.map_mono hAF hx
  have hA'p : (Nat.card ↥A').Prime := by
    change (Nat.card ↥(A.map K.subtype)).Prime
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hA'2 : Nat.card ↥A' ≠ 2 := by
    change Nat.card ↥(A.map K.subtype) ≠ 2
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hNA' : normalizer (A' : Set X) ≤ normalizer (L : Set X) :=
    h.normalizer_le_normalizer hA'L hA'p hA'2
  have hgA' : (g : X) ∈ centralizer (A' : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x ∈ A.map K.subtype at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hgA a ha)
  have hgNL : (g : X) ∈ normalizer (L : Set X) :=
    hNA' (Subgroup.centralizer_le_normalizer (A' : Set X) hgA')
  apply hgN
  rw [CFSG.Glauberman.mem_normalizer_map_subtype_iff (M := K) (fixedSubgroup ψ) g]
  rw [hfix, ← hL_eq]
  exact hgNL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

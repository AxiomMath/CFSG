module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSections
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCoreAlgebra
public import CFSG.ClassicalInvolution.Asc77.IsSylow2InIsSylowOf
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2P
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationFrattini
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.AS81.Sec2
open scoped Pointwise

theorem twoCore_preimage_quotient_isPGroup {H : Type} [Group H] [Finite H] :
    let O := classicalInvolutionOddCore H
    let N := (CFSG.pCore 2 (H ⧸ O)).comap (QuotientGroup.mk' O)
    IsPGroup 2 (N ⧸ O.subgroupOf N) := by
  intro O N
  let π : H →* H ⧸ O := QuotientGroup.mk' O
  let φ : N →* CFSG.pCore 2 (H ⧸ O) :=
    (π.comp N.subtype).codRestrict _ (fun x => x.2)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (y : H ⧸ O)
    exact ⟨⟨x, show π x ∈ CFSG.pCore 2 (H ⧸ O) from hx.symm ▸ y.2⟩,
      Subtype.ext hx⟩
  have hker : O.subgroupOf N = φ.ker := by
    ext x
    change (x : H) ∈ O ↔ φ x = 1
    constructor
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : H)).mpr hx
    · intro hx
      exact (QuotientGroup.eq_one_iff (x : H)).mp (congrArg Subtype.val hx)
  exact (CFSG.pCore_isPGroup (p := 2) (G := H ⧸ O)).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).symm



theorem mapsTo_funSet_of_oddCore_fixes_involutions
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hL2 : ¬ IsL2Over17 (X ⧸ center X) (p ^ e))
    (hΩ : HypOmegaGen {J : Subgroup X | IsFundamentalOver (p ^ e) J})
    (P : Sylow 2 X) (H : Subgroup X) (hPH : (P : Subgroup X) ≤ H)
    (hHsolv : Group.IsSolvable H) (hH3 : ¬ 3 ∣ Nat.card H)
    (hfix : ∀ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      ∀ z : X, IsUniqueInvolution J z →
        ∀ o ∈ (classicalInvolutionOddCore H).map H.subtype, o * z = z * o) :
    ∀ g ∈ H, Set.MapsTo (Subgroup.map (MulAut.conj g).toMonoidHom)
      (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
      (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) := by
  let O : Subgroup H := classicalInvolutionOddCore H
  let N : Subgroup H := (CFSG.pCore 2 (H ⧸ O)).comap (QuotientGroup.mk' O)
  have hON : O ≤ N := by
    rw [← QuotientGroup.ker_mk' O]
    exact MonoidHom.ker_le_comap _ _
  have hN2 : IsPGroup 2 (N ⧸ O.subgroupOf N) := twoCore_preimage_quotient_isPGroup
  have hconj : ∀ (g : X) {J : Subgroup X},
      fundPred (p ^ e) ⊤ J → fundPred (p ^ e) ⊤ (J.map (MulAut.conj g).toMonoidHom) :=
    fun g _ hJ => isFundamentalOver_map_mulEquiv (MulAut.conj g) hJ
  apply F14.mapsTo_funSet_conj_of_normal_two_quotient hconj P H hPH O N hON hN2
  · intro J hJ o ho
    obtain ⟨z, hz⟩ := (hΩ.omega1 J hJ.1).1
    exact mem_normalizer_of_fundamental_involution_of_odd hp2 hL2 hJ.1 hz
      (Odd.of_dvd_nat (odd_card_classicalInvolutionOddCore_map H)
        (Subgroup.orderOf_dvd_natCard _ ho)) (hfix J hJ z hz o ho)
  · intro J hJ
    exact sylow_le_twoCore_preimage_of_hypOmegaGen hΩ H hHsolv hH3 hJ.1
      (IsSylow2In.of_isSylowOf hJ.2) (inf_le_left.trans hPH)

end CFSG.LocalAnalysis.UniquenessCase.UC22

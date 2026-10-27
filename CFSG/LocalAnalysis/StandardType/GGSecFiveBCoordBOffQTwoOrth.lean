module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabelOfJDefs
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthFourHomDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRestLeafDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseCoords
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorChart
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorPerm
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseEndpoint
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinDense
import CFSG.LocalAnalysis.StandardType.GGQTwoSpinEndpoint
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrLabel
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcSixCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcStd
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniQTwoExcFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveUnitarySixCenterAction
import CFSG.LocalAnalysis.StandardType.GGSecFiveUnitarySixCentralizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7DStab
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootRed
import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixCover
public import Certificates.Certificate4091

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

section Inputs

section DenseNbr

private theorem card_bstar_inf_centralizer_le_three_of_aPermutationFull
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {m : ℕ}
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod 3)))
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      aPermutationFull (m + 1) 3) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 := by
  have hfix : Nat.card {v : Fin (m + 1) → Multiplicative (ZMod 3) //
      ∀ u ∈ aPermutationFull (m + 1) 3, u v = v} ≤ 3 := by
    have h := card_fix_aPermutationOn (p := 3) (n := m + 1) (I := Finset.univ)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    rw [aPermutationOn_univ, Finset.card_univ, Fintype.card_fin] at h
    simpa using h.le
  exact card_bstar_inf_centralizer_le_of_fixedPoints eta
    (H := aPermutationFull (m + 1) 3) (by rw [hA]) hfix

private theorem ggSecFiveData_of_ordinaryModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m : ℕ}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hm : 4 ≤ m)
    (e : (CoxeterMatrix.B (m + 1)).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B (m + 1)) e)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod 3))) (i0 : Fin (m + 1))
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel (m + 1) p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 (m + 1) eta K)
    (hBJ : BMaxJoinInput)
    (eta' : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod 3)))
    (hAjoin' : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta').toMonoidHom =
      bSignedFull (m + 1) 3)
    (hAL' : (ggAutomizer L Bs).map (MulAut.congr eta').toMonoidHom =
      bCoordinateBlock (m + 1) 3 i0)
    (hAK' : (ggAutomizer K Bs).map (MulAut.congr eta').toMonoidHom =
      aPermutationFull (m + 1) 3)
    {Fld : Type} [Field Fld] [Finite Fld] [CharP Fld 2]
    (ψ : ↥(unitarySU 2 1 Fld (m + 1)) →* ↥K)
    (hM : UnitTB.Model ψ)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hdiag : ∀ a ∈ (ggGamma K hN).range, ∃ t : Fin (m + 1) → Fld,
      LineU.ActsDiagU ψ a t) :
    GGSecFiveData 3 B x L D J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have hcard4 : Nat.card Fld = 4 := by
    rw [hM.field.card]
    norm_num
  have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
    card_bstar_inf_centralizer_le_three_of_aPermutationFull eta' hAK'
  obtain ⟨-, -, -, F0, hFieldF0, hAlgF0K, E, hF0card, π, hπ, κ, χK, hκ⟩ :=
    exists_omKFrame_of_qTwoOrth_over (K := Fld) hcfg (by omega) eta' hAL' hLab hcard4
  letI : Field F0 := hFieldF0
  letI : Algebra F0 Fld := hAlgF0K
  haveI : Finite F0 := Nat.finite_of_card_ne_zero (by rw [hF0card]; norm_num)
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hX : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := by
    have hS' := hS
    unfold LargeEvenSStar LargeEvenIsBmax at hS'
    obtain ⟨⟨hBelem, -, -⟩, hxB, hx1, hLcomp, -⟩ := hS'
    exact CFSG.Assembly.isComponentOf_iff_open.mp hLcomp
  obtain ⟨σ, χ, hσ⟩ :=
    exists_uniLFrame_of_model (p := 3) (n := m + 1) (K := Fld) (f := 1) (X := K)
      Nat.prime_three (by norm_num) hcfg.2.1.2.1 hcfg.2.1.2.2.2 hC (by omega)
      eta' hAK' hN ψ hM hdiag π
  have hJK : (σ.comp (CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.uniCast hM.field m)).range ≤ L :=
    GGSecFiveBPermUniLFrame.range_comp_uniCast_le_of_omKFrame
      (X := L) (L := K) (y := x) hcfg.2.1.2.2.2 hxBs hX hκ hσ hM.field hm
  obtain ⟨Ψ, hΨ, hΨr⟩ :=
    ggSecFiveBPermUniOm_of_frames (p := 3) (f := 1) (m := m)
      (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) hm
      (F := F0) (K := Fld) hM.field hcfg.2.1.2.2.2 hxBs hX hAK' hσ hκ hJK
  have hG0 : ggG0 3 B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_aPermutationFull hBJ hR e hP (by omega) hRM eta' hAjoin' hAL'
      hK.1 hAK'
  have hrange : Ψ.range = ggG0 3 B x L D J := by
    rw [hΨr]
    rw [sup_comm]
    exact hG0.symm
  exact ggSecFiveData_of_injective_normOmega_of_card_two E hF0card (by omega) Ψ hΨ hrange

theorem GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_denseNbr_marking_ge_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs) (hn : 5 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hAjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K)
    (hKU : GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = n - 1 ∧
      lab.n = 1 ∧ p ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hLB : GGLBalanceInput) (hStdP : GGStdSubPrimeInput) (hU62 : GGU62OuterDiagInput)
    (hBJ : BMaxJoinInput) :
    GGSecFiveData 3 B x L D J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 4 ≤ m := by omega
  obtain ⟨eta', hAjoin', hAL', hAK'⟩ :=
    GGSecFiveBCoordBDenseNbr.exists_coords hAjoin hAL hK
  obtain ⟨y, hyNbr⟩ := hR.2.2.2.1.2 K hK.1
  have hW : GGSecFiveWeylCase' 3 B Bs x D J := hR.2.1
  have hH : GGResHyp 3 B Bs x L D J y K :=
    ⟨hcfg, hR.1.2.1, hR.1.2.2.1, hR.1.2.2.2.1, hyNbr, hW y K hyNbr, Or.inr hW⟩
  by_cases hm5 : m = 5
  · subst m
    have hcell : GGInnerDiagOnLabel
        (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs K :=
      GGInnerDiagOnLabel.mono_label
        (fun lab h => ⟨h.1, by simpa using h.2.1, h.2.2.1⟩) hKU
    have hcell3 : GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1 ∧ p = 3) 3 Bs K :=
      GGInnerDiagOnLabel.mono_label
        (fun lab h => ⟨h.1, h.2.1, h.2.2, rfl⟩) hcell
    have hU63 : GGInnerDiagOnLabel GGNbrInner937U63Label 3 Bs K :=
      GGResHyp.u63_marking_of_cell hcell3
    obtain ⟨Fld, hFieldF, hFiniteF, hF4, θ, hN, hact⟩ :=
      GGResHyp.unitary_six_two_K_marking_data hH hcell
    letI : Field Fld := hFieldF
    letI : Finite Fld := hFiniteF
    have hCharF : CharP Fld 2 :=
      charP_two_of_card (by simpa using hF4 : Nat.card Fld = 2 ^ 2)
    letI : CharP Fld 2 := hCharF
    have hLp : commutator ↥K = ⊤ := hcell.1
    have hgamma : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
      GGResHyp.gamma_four_of_unitary_six_two_K hLB hStdP hH hN rfl hU63
    obtain ⟨hNbar, φ, hMred, hdiagred⟩ :=
      exists_diagonal_cover_of_unitary_six_two_red hF4 hLp θ hN hcfg.2.1.2.1 hact hgamma
    have hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ 3 :=
      card_bstar_inf_centralizer_le_three_of_aPermutationFull eta' hAK'
    obtain ⟨eta_red, σred, χred, heta_red, hframe_red⟩ :=
      exists_redUniLFrame_of_model hN hcfg.2.1.2.1 hLp hcfg.2.1.2.2.2 hC
        (by omega : 4 ≤ 6) eta' hAK' hNbar φ hMred hdiagred
    have hfix := ggSecFiveBPermUniQTwoExc_fixed_free_b1_of_redFrame hU62 hN eta'
      eta_red heta_red hF4 hframe_red hLp
    have hcent := QTwoExcSix.exists_eq_mul_central_of_commute_redFrame hN eta'
      eta_red heta_red hF4 hframe_red hLp
      (fun v hv => QTwoExcSix.mem_of_prod_eq_one hN eta' hAK' hv)
    have hyB : y ∈ Bs := hB ▸ hH.2.2.2.2.1.1.2.1
    have hyC : y ∈ Subgroup.centralizer (K : Set G) := hH.data_K.1
    have hLx : K ≤ Subgroup.centralizer ({y} : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hyC k hk
    have hzy : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hyB, hyC⟩
    have horder : orderOf y = 3 := by
      have hdvd : orderOf y ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hH.data_K.2.2.1)
      have hne : orderOf y ≠ 1 := fun h => hH.data_K.2.1 (orderOf_eq_one_iff.mp h)
      exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
    have hcenEq : Subgroup.zpowers y = Bs ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzy (by rw [Nat.card_zpowers, horder]; exact hC)
    have hcen : ∀ e ∈ Bs ⊓ Subgroup.centralizer (K : Set G), e ∈ Subgroup.zpowers y := by
      intro e he
      simpa [hcenEq] using he
    have hS : LargeEvenSStar 3 B y K := hH.sstar_K_of_centralizer_axis hyB hcen
    obtain ⟨t, ht, -, hteta⟩ :=
      exists_ggConjAut_eq_of_mem_bSignedFull eta' hAjoin' QTwoExcSix.sgn345_mem
    have hZbot : Line63.H5.twoCenter K = ⊥ := by
      by_contra hZ
      exact QTwoExcSix.false_of_twoCenter_ne_bot_of_sstar hcfg.2.1.2.1 hyB hLx hS hB
        hN eta' hAK' t ht hteta hZ hfix hcent
    obtain ⟨ψ, hM, hdiag⟩ :=
      exists_model_of_redMkL_of_twoCenter_eq_bot hZbot hN hNbar hMred hdiagred
    exact ggSecFiveData_of_ordinaryModel hR hm e hP eta i0 hLab hRM hK hBJ
      eta' hAjoin' hAL' hAK' ψ hM hN hdiag
  ·
    obtain ⟨Fld, hFieldF, hFiniteF, ψ, hM, hdiag⟩ :=
      GGResHyp.exists_unitaryModel_K_qTwo_of_marking_rank (r := m) hH hKU
        (by omega) (by omega)
    letI : Field Fld := hFieldF
    letI : Finite Fld := hFiniteF
    letI : CharP Fld 2 := hM.field.charP
    have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
      (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
    exact ggSecFiveData_of_ordinaryModel hR hm e hP eta i0 hLab hRM hK hBJ
      eta' hAjoin' hAL' hAK' ψ hM hN hdiag

theorem GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_denseNbr
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hAjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K)
    (hLB : GGLBalanceInput) (hStdP : GGStdSubPrimeInput) (hU62 : GGU62OuterDiagInput)
    (hBJ : BMaxJoinInput) (hLJ : GGSecFivePermNbrLabelOfJInput)
    (hRig : GGLabelRigidInput) :
    GGSecFiveData 3 B x L D J := by
  obtain ⟨hn5, hJ⟩ :=
    GGSecFiveRouteCfg.qTwoOrth_denseNbr_J_label hRig hR hB hn hAjoin hAL hLab hK
  have hKU := GGSecFiveRouteCfg.qTwoOrth_denseNbr_marking hLJ hRig hR hn5
    hAjoin hAL hK hJ
  exact GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_denseNbr_marking_ge_five
    hR hB hn5 e hP eta i0 hAjoin hAL hLab hRM hK hKU hLB hStdP hU62 hBJ

end DenseNbr

section Sparse

private theorem ggG0_eq_sup_range_of_normPerm
    {G : Type} [Group G] [Finite G] {k : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin (k + 4) → Multiplicative (ZMod 3)))
    (i0 : Fin (k + 4))
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull (k + 4) 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock (k + 4) 3 i0)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {w : G} (hwG0 : w ∈ ggG0 3 B x L D J) (π : Fin (k + 4) ≃ Fin (k + 4))
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    (E : CFSG.ClassicalInvolution.Models.OrthogonalPairs.QuadExt F Kf
      (CFSG.LieType.BorelTits.unitaryInvolution Kf 2 1))
    (κ₁ κ₂ : normOmega E (k + 3) →* G)
    (χ : Multiplicative (ZMod 3) →* Kfˣ)
    (t : Equiv.Perm (Fin (k + 4)) →* G)
    (hframe1 : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hframe2 : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
      ((finRotate (k + 4)).trans π) κ₂ χ)
    (ht1 : t.comp (Equiv.Perm.viaEmbeddingHom
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4))) =
      κ₁.comp (normPerm E (by omega : 3 ≤ k + 3)))
    (ht2 : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3))) =
      κ₂.comp (normPerm E (by omega : 3 ≤ k + 3)))
    (hAct1 : ∀ (σ : Equiv.Perm (Fin (k + 3)))
      (hσ : κ₁ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (p := 3)
        (Equiv.Perm.viaEmbeddingHom
          ((Fin.castSuccEmb (n := k + 3)).trans π.toEmbedding) σ))
    (hAct2 : ∀ (σ : Equiv.Perm (Fin (k + 3)))
      (hσ : κ₂ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (p := 3)
        (Equiv.Perm.viaEmbeddingHom
          ((Fin.castSuccEmb (n := k + 3)).trans
            ((finRotate (k + 4)).trans π).toEmbedding) σ)) :
    ggG0 3 B x L D J = L ⊔ t.range := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  let f : Equiv.Perm (Fin (k + 3)) →* G := κ₁.comp (normPerm E (by omega : 3 ≤ k + 3))
  let g : Equiv.Perm (Fin (k + 3)) →* G := κ₂.comp (normPerm E (by omega : 3 ≤ k + 3))
  have hfL : f.range ≤ L := by
    rintro _ ⟨σ, rfl⟩
    change κ₁ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ L
    rw [← hframe1.2.1]
    exact ⟨_, rfl⟩
  have hgLw : g.range ≤ L.map (MulAut.conj w).toMonoidHom := by
    rintro _ ⟨σ, rfl⟩
    change κ₂ (normPerm E (by omega : 3 ≤ k + 3) σ) ∈ L.map (MulAut.conj w).toMonoidHom
    rw [← hframe2.2.1]
    exact ⟨_, rfl⟩
  have hfN : ∀ σ, f σ ∈ Subgroup.normalizer (Bs : Set G) := fun σ =>
    GGSecFiveBPermOmKFrame.normPerm_mem_normalizer (hframe := hframe1)
      (hr := (by omega : 3 ≤ k + 3)) (hSC := hSC) σ
  have hgN : ∀ σ, g σ ∈ Subgroup.normalizer (Bs : Set G) := fun σ =>
    GGSecFiveBPermOmKFrame.normPerm_mem_normalizer (hframe := hframe2)
      (hr := (by omega : 3 ≤ k + 3)) (hSC := hSC) σ
  have hfAct : ∀ σ, MulAut.congr eta (ggConjAut Bs (hfN σ)) =
      SpCoord.permAut (p := 3) (π.permCongr (Equiv.Perm.viaEmbeddingHom
        (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) σ)) := by
    intro σ
    rw [hAct1 σ (hfN σ)]
    congr 1
    exact viaEmbeddingHom_trans_equiv (Fin.castSuccEmb : Fin (k + 3) ↪ Fin (k + 4)) π σ
  have hgAct : ∀ σ, MulAut.congr eta (ggConjAut Bs (hgN σ)) =
      SpCoord.permAut (p := 3) (π.permCongr (Equiv.Perm.viaEmbeddingHom
        (Fin.succEmb (k + 3)) σ)) := by
    intro σ
    rw [hAct2 σ (hgN σ)]
    congr 1
    exact viaEmbeddingHom_castSuccEmb_finRotate_trans (k + 3) π σ
  exact GGSecFiveRouteCfg.ggG0_eq_sup_range_of_permHom hX hTCJ hRig hTPn hA8 hraw hiso hFC
    hR hB eta i0 hSigned hAL hSparse hRM w hwG0 π f g t ht1 ht2 hfL hgLw hfN hgN hfAct hgAct

theorem GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_bCoordSparse_ge_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs) (hn : 5 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (i0 : Fin n)
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveData 3 B x L D J := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hk : 1 ≤ k := by omega
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  obtain ⟨K, hKmem, -⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull (p := 3) (n := k + 4)
      Nat.prime_three (by decide) eta hSigned hAL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := (ggNbr_facts hcfg hnb).1
  have hKle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hKmem)
  obtain ⟨j, hj, -, w, hw, hwG0, hact, -, -⟩ :=
    GGSecFiveRouteCfg.exists_ggG0_eq_map_conj_swap_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw
      hiso hFC hR hB (by omega : 4 ≤ k + 4) eta i0 hSigned hAL hSparse hy hnb hKle
  obtain ⟨-, hZ, hN, F, Kf, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2,
    π, κ₁, κ₂, χ, t, Ψ, hπlast, hπzero, hframe1, hframe2, ht1, ht2, hoverlap,
    hAct1, hAct2, hPsiInj, hPsiCast, hPsiPerm, hPsiRange⟩ :=
    exists_normOmega_hom_of_qTwoOrth hcfg hk eta hAL hLab hSigned hG0 hw hj hact
  letI : Field F := hFieldF
  letI : Field Kf := hFieldK
  letI : Algebra F Kf := hAlgFK
  letI : Finite Kf := hFinK
  letI : CharP Kf 2 := hCharK
  have hRange : ggG0 3 B x L D J = L ⊔ t.range :=
    ggG0_eq_sup_range_of_normPerm (k := k) (F := F) (Kf := Kf)
      hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB eta i0 hSigned hAL hSparse hRM
      hwG0 π E κ₁ κ₂ χ t hframe1 hframe2 ht1 ht2 hAct1 hAct2
  exact ggSecFiveData_of_injective_normOmega_of_card_two E hF2
    (by omega : 3 ≤ k + 4) Ψ hPsiInj (hPsiRange.trans hRange.symm)

theorem GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_ge_five
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {n : ℕ}
    (hLB : GGLBalanceInput) (hStdP : GGStdSubPrimeInput)
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hBJ : BMaxJoinInput) (hLJ : GGSecFivePermNbrLabelOfJInput)
    (hU62 : GGU62OuterDiagInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hB : B = Bs) (hn : 5 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveData p B x L D J := by
  classical
  have hp3 : p = 3 := by
    obtain ⟨lab, hΛ, hHas, _, _, _, _, _, hPred⟩ :=
      largeEvenMarking_exists_hasLabel hLab
    exact QTwo.ggQTwoD_p_eq_three hRig hR hΛ hHas hPred.1.2.1
  subst p
  by_cases hDense : ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K
  · obtain ⟨K, hK⟩ := hDense
    exact GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_denseNbr
      hR hB (by omega) e hP eta i0 hSigned hAL hLab hRM hK
      hLB hStdP hU62 hBJ hLJ hRig
  · have hLabBC : GGInnerDiagOnLabel
        (fun p lab => GGSecFiveBCoordBLabel n p lab) 3 Bs L :=
      GGInnerDiagOnLabel.mono_label (fun _ h => h.1) hLab
    have hSparse : GGSecFiveBCoordSparse eta i0 D :=
      GGSecFiveRouteCfg.bCoordSparse_of_no_denseNbr
        hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB (by omega)
        eta i0 hSigned hAL hLabBC hDense
    exact GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_bCoordSparse_ge_five
      hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB hn
      eta i0 hSigned hAL hLab hSparse hRM hG0

theorem GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_bCoordSparse_four
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput) (hHom : GGQTwoOrthFourHomInput)
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4)
    (hSigned : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull 4 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock 4 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hSparse : GGSecFiveBCoordSparse eta i0 D)
    (hRM : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K) :
    GGSecFiveData 3 B x L D J := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  obtain ⟨K, hKmem, -⟩ :=
    exists_mem_not_le_ggAutomizer_of_bSignedFull (p := 3) (n := 4)
      Nat.prime_three (by decide) eta hSigned hAL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  have hy : y ∈ Bs := (ggNbr_facts hcfg hnb).1
  have hKle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hKmem)
  obtain ⟨j, hj, -, w, hw, hwG0, hact, -, -⟩ :=
    GGSecFiveRouteCfg.exists_ggG0_eq_map_conj_swap_of_bCoordSparse hX hTCJ hRig hTPn hA8 hraw
      hiso hFC hR hB (by omega : 4 ≤ 4) eta i0 hSigned hAL hSparse hy hnb hKle
  obtain ⟨-, -, F, Kf, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2,
    π, κ₁, κ₂, χ, t, Ψ, hπlast, hπzero, hframe1, hframe2, ht1, ht2, hoverlap,
    hAct1, hAct2, hPsiInj, hPsiCast, hPsiPerm, hPsiRange⟩ :=
    hHom hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hR hB eta i0 hSigned hAL hLab hRM hG0
      hw hj hact
  letI : Field F := hFieldF
  letI : Field Kf := hFieldK
  letI : Algebra F Kf := hAlgFK
  letI : Finite Kf := hFinK
  letI : CharP Kf 2 := hCharK
  have hRange : ggG0 3 B x L D J = L ⊔ t.range :=
    ggG0_eq_sup_range_of_normPerm (k := 0) (F := F) (Kf := Kf)
      hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB eta i0 hSigned hAL hSparse hRM
      hwG0 π E κ₁ κ₂ χ t hframe1 hframe2 ht1 ht2 hAct1 hAct2
  exact ggSecFiveData_of_injective_normOmega_of_card_two E hF2
    (by decide : 3 ≤ 4) Ψ hPsiInj (hPsiRange.trans hRange.symm)

theorem ggSecFiveBCoordBOffQTwoOrthRouteInput_of_fourHom
    (hHom : GGQTwoOrthFourHomInput) : GGSecFiveBCoordBOffQTwoOrthRouteInput := by
  intro hID hLB hStdP hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ hLJ hU62
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 hSigned hAL hLab hB hRM hG0 hcell
  by_cases hn5 : 5 ≤ n
  · exact GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_ge_five
      hLB hStdP hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ hLJ hU62
      hR hB hn5 e hP eta i0 hSigned hAL hLab hRM hG0
  · have hn4 : n = 4 := by omega
    subst n
    have hp3 : p = 3 := by
      obtain ⟨lab, hΛ, hHas, _, _, _, _, _, hPred⟩ :=
        largeEvenMarking_exists_hasLabel hLab
      exact QTwo.ggQTwoD_p_eq_three hRig hR hΛ hHas hPred.1.2.1
    subst p
    have hDense : ¬ ∃ K : Subgroup G, GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 4 eta K := by
      rintro ⟨K, hK⟩
      obtain ⟨h5, -⟩ :=
        GGSecFiveRouteCfg.qTwoOrth_denseNbr_J_label hRig hR hB (by decide : 4 ≤ 4)
          hSigned hAL hLab hK
      omega
    have hLabBC : GGInnerDiagOnLabel
        (fun p lab => GGSecFiveBCoordBLabel 4 p lab) 3 Bs L :=
      GGInnerDiagOnLabel.mono_label (fun _ h => h.1) hLab
    have hSparse : GGSecFiveBCoordSparse eta i0 D :=
      GGSecFiveRouteCfg.bCoordSparse_of_no_denseNbr
        hX hTCJ hRig hTPn hA8 hraw hiso hFC hR hB (by decide : 4 ≤ 4)
        eta i0 hSigned hAL hLabBC hDense
    exact GGSecFiveRouteCfg.ggSecFiveData_of_qTwoOrth_bCoordSparse_four
      hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB hHom hR hB eta i0 hSigned hAL hLab
      hSparse hRM hG0

end Sparse

end Inputs

end CFSG.StandardType

end

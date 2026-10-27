module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection10.PFsection10_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection11.PFsection11_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.RealVirtualParity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_8_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_16
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.SourceTypePBridge
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_1
import Mathlib.GroupTheory.Schreier
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 12: Theorem (12.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section12
universe u v

/-! ## (12.10) -/

private theorem theorem_12_10_centralizer_le_of_tiWithNormalizer
    {G : Type u} [Group G]
    {X : Set G} {N : Subgroup G} {y : G}
    (hTI : section16TISubsetWithNormalizer X N)
    (hyX : y ∈ X) (hyne : y ≠ 1) :
    Subgroup.centralizer ({y} : Set G) ≤ N := by
  intro c hc
  rcases hTI with ⟨hTI, hNorm⟩
  have hyConj : y ∈ section16ConjugateSet X c := by
    refine ⟨y, hyX, ?_⟩
    have hcomm : c * y = y * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hfix : c * y * c⁻¹ = y := by
      rw [hcomm]
      simp [mul_assoc]
    exact hfix.symm
  have hcNorm : c ∈ Subgroup.normalizer X := by
    rcases hTI c with hsame | hsmall
    · change ∀ z : G, z ∈ X ↔ c * z * c⁻¹ ∈ X
      intro z
      constructor
      · intro hz
        have hzConj : c * z * c⁻¹ ∈ section16ConjugateSet X c :=
          ⟨z, hz, rfl⟩
        rw [hsame] at hzConj
        exact hzConj
      · intro hz
        rw [← hsame] at hz
        rcases hz with ⟨w, hw, hwz⟩
        have hzw : z = w := by
          calc
            z = c⁻¹ * (c * z * c⁻¹) * c := by group
            _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [hwz]
            _ = w := by group
        simpa [hzw] using hw
    · have hyOne : y ∈ ({1} : Set G) := hsmall ⟨hyX, hyConj⟩
      exact False.elim (hyne (by simpa using hyOne))
  simpa [hNorm] using hcNorm

private theorem theorem_12_10_p0_le_mf_of_typeIIIIV
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {L H P0 U W1 W2 : Subgroup G} {p : ℕ}
    (hp : Nat.Prime p)
    (hL : L ∈ section9MaximalSubgroups G)
    (hP : Section8.typePDefinitionData L H U W1 W2)
    (hP0D : P0 ≤ ambientDerivedSubgroup L)
    (hP0p : IsPGroup p P0) (hP0rank : groupRank P0 = 2)
    (hUcyc : IsCyclic U) :
    P0 ≤ H := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup L
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompL, _hUleD, _hUnil,
      _hW1norm, hCompD, _hHnoncyc, _hSecond, _hFitEq, _hFitLeD,
      _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
  have hHD : H ≤ D := by simpa [D] using hCompD.1
  have hUD : U ≤ D := by simpa [D] using hCompD.2.1
  have hDL : D ≤ L := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := L))
  have hHHallD :
      IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf D) := by
    have hHHallL :
        IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf L) :=
      section16MFSubgroup_subgroupOf_isHall hMF
    refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet H)
      (H := H.subgroupOf D) ?_ ?_
    · intro q hq
      have hcardD : Nat.card (H.subgroupOf D) = Nat.card H :=
        natCard_subgroupOf_eq H D hHD
      have hcardDF : Fintype.card (H.subgroupOf D) = Fintype.card H := by
        simpa [Nat.card_eq_fintype_card] using hcardD
      have hqH : q.val ∣ Fintype.card H := by
        simpa [hcardDF] using hq
      simpa [subgroupPrimeSet, Nat.card_eq_fintype_card] using hqH
    · intro q hqH hqidx
      let DsubL : Subgroup L := D.subgroupOf L
      have hHsub_le_Dsub : H.subgroupOf L ≤ DsubL := by
        intro z hz
        exact hHD hz
      have hrel_eq :
          (H.subgroupOf D).index = (H.subgroupOf L).relIndex DsubL := by
        have hsub :=
          Subgroup.relIndex_subgroupOf (H := H) (K := D) (L := L) hDL
        simpa [DsubL, Subgroup.relIndex] using hsub.symm
      have hidx_dvd : (H.subgroupOf D).index ∣ (H.subgroupOf L).index := by
        have hrel_dvd :
            (H.subgroupOf L).relIndex DsubL ∣ (H.subgroupOf L).index :=
          Subgroup.relIndex_dvd_index_of_le hHsub_le_Dsub
        simpa [hrel_eq] using hrel_dvd
      exact (hHHallL.p_in_pi_of_p_dvd_index q (hqidx.trans hidx_dvd)) hqH
  have hHnormalD : (H.subgroupOf D).Normal := by
    have hHnormalL : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hMF
    have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (section16MFSubgroup_le hMF)).1 hHnormalL
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hHD).2
      (hDL.trans hLnormH)
  have hCompLocal :
      (H.subgroupOf D).IsComplement' (U.subgroupOf D) := by
    exact section12ComplementIn_left_normal_isComplement'
      (by simpa [D] using hCompD) hHnormalD
  have hUHallD :
      IsHallSubgroup (subgroupPrimeSet H)ᶜ (U.subgroupOf D) := by
    refine isHallSubgroup_of (G := D) (π := (subgroupPrimeSet H)ᶜ)
      (H := U.subgroupOf D) ?_ ?_
    · intro q hqU hqHc
      have hqHidx : q.val ∣ (H.subgroupOf D).index := by
        simpa [hCompLocal.symm.index_eq_card] using hqU
      exact (hHHallD.p_in_pi_of_p_dvd_index q hqHidx) hqHc
    · intro q hqHc hqUidx
      have hqH : q.val ∣ Nat.card (H.subgroupOf D) := by
        simpa [hCompLocal.index_eq_card] using hqUidx
      exact hqHc (hHHallD.p_in_pi_of_p_dvd_card q hqH)
  let P0D : Subgroup D := P0.subgroupOf D
  have hP0Dp : IsPGroup p P0D :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0D).symm
  let pp : Nat.Primes := ⟨p, hp⟩
  by_cases hpH : pp ∈ subgroupPrimeSet H
  · have hP0Dle : P0D ≤ H.subgroupOf D :=
      section12_pSubgroup_le_normal_hall_of_prime_mem
        hHHallD hpH (by simpa [pp] using hP0Dp)
    intro z hzP0
    have hzD : z ∈ D := hP0D hzP0
    have hzHloc : (⟨z, hzD⟩ : D) ∈ H.subgroupOf D :=
      hP0Dle (by simpa [P0D, Subgroup.mem_subgroupOf] using hzP0)
    simpa [Subgroup.mem_subgroupOf] using hzHloc
  · have hP0Dpi : IsPiSubgroup (subgroupPrimeSet H)ᶜ P0D := by
      have hsingle : IsPiSubgroup ({pp} : Set Nat.Primes) P0D :=
        section8_isPiSubgroup_singleton_of_isPGroup (q := pp)
          (by simpa [pp] using hP0Dp)
      intro q hqP0
      have hqpp : q ∈ ({pp} : Set Nat.Primes) := hsingle q hqP0
      have hqeq : q = pp := by simpa using hqpp
      subst q
      simpa using hpH
    letI : MulDistribMulAction Unit D := {
      smul := fun _ z => z
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
    have hP0Dinv : IsInvariant Unit D P0D := by
      refine ⟨?_⟩
      intro _ z
      simp [P0D]
    have hDneTop : D ≠ ⊤ := by
      intro hDtop
      apply hL.1
      apply top_unique
      intro z _hz
      exact hDL (by simp [hDtop])
    have hDsolv : IsSolvable D :=
      IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
    obtain ⟨Q, hQHall, _hQinv, hP0DQ⟩ :=
      exists_isHallSubgroup_isInvariant_of_isPiSubgroup
        (G := D) (A := Unit) hDsolv (by simp)
        (subgroupPrimeSet H)ᶜ P0D hP0Dpi hP0Dinv
    obtain ⟨d, hd⟩ :=
      exists_conj_eq_of_isHallSubgroup_of_solvable
        (G := D) hDsolv hQHall hUHallD
    have hP0Dmap_le :
        P0D.map (MulAut.conj d).toMonoidHom ≤ U.subgroupOf D := by
      rw [hd]
      exact Subgroup.map_mono hP0DQ
    have hUsubCyc : IsCyclic (U.subgroupOf D) :=
      (Subgroup.subgroupOfEquivOfLe hUD).isCyclic.2 hUcyc
    have hP0DmapCyc :
        IsCyclic (P0D.map (MulAut.conj d).toMonoidHom) := by
      letI : IsCyclic (U.subgroupOf D) := hUsubCyc
      exact Subgroup.isCyclic_of_le hP0Dmap_le
    let eP0D : P0D ≃* P0D.map (MulAut.conj d).toMonoidHom :=
      Subgroup.equivMapOfInjective
        (f := (MulAut.conj d).toMonoidHom) P0D (MulAut.conj d).injective
    have hP0Dcyc : IsCyclic P0D := eP0D.isCyclic.2 hP0DmapCyc
    have hP0cyc : IsCyclic P0 :=
      (Subgroup.subgroupOfEquivOfLe hP0D).isCyclic.1 hP0Dcyc
    have hRankLe : groupRank P0 ≤ 1 := groupRank_le_one_of_isCyclic P0
    omega

/-- The source-data package for PF `(12.10)` implies the public Frobenius
conclusion. -/
public theorem theorem_12_10_of_source_data
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (hsrc : theorem_12_10_source_data M K K' P0 L H Ls x p)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p) :
    Section7.frobeniusWithKernel L H :=
  hsrc h128 h129

/-- Source leaf for the first PF `(12.10)` phase: excluding the non-Type-I
alternatives for `L`. -/
public theorem theorem_12_10_typeI_reduction_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) :
    theorem_12_10_typeI_reduction_source_data M K K' P0 L H Ls x p := by
  intro h128 h129
  rcases h129 with
    ⟨_hP0comm, _hP0rank, hL, hH, hLs, hP0Ls, _hxL,
      ⟨hp, hxOmega, hxne⟩, _hCK, _hNxM, hCnotL⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have h128copy := h128
  rcases h128copy with
    ⟨_hp128, _hbad, _hmin, _hM, _hK, _hTypeI, _hMs, _hK', _hnoncyc,
      hP0Sylow⟩
  have hP0p : IsPGroup p P0 := by
    rcases hP0Sylow with ⟨P, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hyOmega, hyx⟩
    have hyP0 : (y : G) ∈ P0 := y.property
    simpa using hyx ▸ hyP0
  have hLateFalse :
      ¬ (section16TypeIII L H ∨ section16TypeIV L H) := by
    intro hLate
    have hLateBG := hLate
    obtain ⟨U, W1, W2, hP, hCond⟩ :
        ∃ U W1 W2 : Subgroup G,
          Section8.typePDefinitionData L H U W1 W2 ∧
            Section8.typeIIToIVSourceCondition L U W1 := by
      rcases hLate with hTypeIII | hTypeIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) hL hH hTypeIII with
          ⟨U, W1, W2, hP, hCond, _hUcomm, _hUnorm⟩
        exact ⟨U, W1, W2, hP, hCond⟩
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) hL hH hTypeIV with
          ⟨U, W1, W2, hP, hCond, _hUcomm, _hUnorm⟩
        exact ⟨U, W1, W2, hP, hCond⟩
    have hUcyc : IsCyclic U := by
      exact Section11.theorem_11_complement_isCyclic_of_typeP_typeIIIIV
        hL hH hP hCond hLateBG
    rcases section15_exists_KUData_for_maximal (G := G) (M := L) hL with
      ⟨K0, U0, hKU15⟩
    have hKU : section16KUData L K0 U0 := by
      simpa [section16KUData] using hKU15
    have hProp :=
      proposition_16_1 (G := G) (M := L) (MF := H) (K := K0) (U := U0)
        hL hH hKU
    have hCaseP1 : section16CaseP1 K0 U0 ∧ H ≠ section10Msigma L :=
      hProp.2.2.1.mp hLateBG
    have hnotTypeI : ¬ section16TypeI L H := by
      intro hTypeI
      have hCaseF : section16CaseF K0 U0 := hProp.1.mp hTypeI
      exact hCaseP1.1.1 hCaseF.1
    have hDsigma : ambientDerivedSubgroup L = section10Msigma L := by
      have hD := hProp.2.2.2.2.1.mpr hnotTypeI
      simpa [hCaseP1.1.2] using hD
    have hLsSigma : Ls = section10Msigma L :=
      Section8.theorem_8_11_msChoice_eq_msigma (G := G) hL hH hLs
    have hP0D : P0 ≤ ambientDerivedSubgroup L := by
      simpa [hLsSigma, hDsigma] using hP0Ls
    have hP0H : P0 ≤ H :=
      theorem_12_10_p0_le_mf_of_typeIIIIV hp hL hP hP0D hP0p _hP0rank hUcyc
    have hPcopy := hP
    rcases hPcopy with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hCompL, _hUleD, _hUnil,
        _hW1norm, _hCompD, _hHnoncyc, _hSecond, hFittingEq, _hFitLeD,
        hW2le, _hW2cyc, hW2ne, _hCent, _hHatW⟩
    let F : Subgroup G := section8FittingSubgroup L
    have hHleF : H ≤ F := by
      intro z hz
      change z ∈ section8FittingSubgroup L
      rw [← hFittingEq]
      exact (show H ≤ H ⊔ subgroupCentralizerIn L H from le_sup_left) hz
    have hFnormalizer : Subgroup.normalizer (F : Set G) = L := by
      have hW2card : Nat.card W2 ≠ 1 := by
        intro hcard
        exact hW2ne ((Subgroup.eq_bot_iff_card (H := W2)).2 hcard)
      rcases Nat.exists_prime_and_dvd (n := Nat.card W2) hW2card with
        ⟨q, hqprime, hqdiv⟩
      let qq : Nat.Primes := ⟨q, hqprime⟩
      have hqW2 : qq ∈ subgroupPrimeSet W2 := by
        change q ∣ Nat.card W2
        exact hqdiv
      have hqF : qq ∈ subgroupPrimeSet F :=
        section8_subgroupPrimeSet_mono
          (fun z hz => hHleF ((hW2le hz).1)) hqW2
      have hL8 : L ∈ section8MaximalSubgroups G := by
        simpa [section8MaximalSubgroups, section9MaximalSubgroups] using hL
      exact section8_normalizer_fittingSubgroup_eq
        (G := G) (M := L) (q := qq) hL8 hqF
    have hxF : x ∈ F := hHleF (hP0H hxP0)
    have hxFsharp :
        x ∈ section16NonidentityElements (F : Set G) := ⟨hxF, hxne⟩
    have hcent : Subgroup.centralizer ({x} : Set G) ≤ L := by
      intro c hc
      have hxFix : c * x * c⁻¹ = x := by
        have hcomm : c * x = x * c :=
          Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [hcomm]
        simp [mul_assoc]
      have hxConj :
          x ∈ section16ConjugateSet
            (section16NonidentityElements (F : Set G)) c :=
        ⟨x, hxFsharp, hxFix.symm⟩
      rcases hCond.2.2 c with hsame | hsmall
      · have hcNormF : c ∈ Subgroup.normalizer (F : Set G) := by
          change ∀ z : G, z ∈ F ↔ c * z * c⁻¹ ∈ F
          intro z
          constructor
          · intro hzF
            by_cases hz1 : z = 1
            · simp [hz1]
            · have hzSharp :
                  z ∈ section16NonidentityElements (F : Set G) := ⟨hzF, hz1⟩
              have hzConj :
                  c * z * c⁻¹ ∈
                    section16ConjugateSet
                      (section16NonidentityElements (F : Set G)) c :=
                ⟨z, hzSharp, rfl⟩
              have hzConjSharp :
                  c * z * c⁻¹ ∈ section16NonidentityElements (F : Set G) := by
                rw [hsame] at hzConj
                exact hzConj
              exact hzConjSharp.1
          · intro hzConjF
            by_cases hz1 : z = 1
            · simp [hz1]
            · have hzConjNe : c * z * c⁻¹ ≠ 1 := by
                intro hz
                apply hz1
                have hz' := congrArg (fun y : G => c⁻¹ * y * c) hz
                simpa [mul_assoc] using hz'
              have hzConjSharp :
                  c * z * c⁻¹ ∈ section16NonidentityElements (F : Set G) :=
                ⟨hzConjF, hzConjNe⟩
              have hzConjMem :
                  c * z * c⁻¹ ∈
                    section16ConjugateSet
                      (section16NonidentityElements (F : Set G)) c := by
                rw [hsame]
                exact hzConjSharp
              rcases hzConjMem with ⟨w, hwSharp, hwz⟩
              have hzw : z = w := by
                calc
                  z = c⁻¹ * (c * z * c⁻¹) * c := by group
                  _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [hwz]
                  _ = w := by group
              simpa [hzw] using hwSharp.1
        simpa [hFnormalizer] using hcNormF
      · have hxOne : x ∈ ({1} : Set G) := hsmall ⟨hxFsharp, hxConj⟩
        exact False.elim (hxne (by simpa using hxOne))
    exact hCnotL (by simpa [elementCentralizerIn] using hcent)
  rcases section16_type_exhaustive_of_maximal (G := G) hL hH with
    hTypeI | hTypeII | hTypeIII | hTypeIV | hTypeV
  · exact Section8.theorem_8_8_typeI_to_source_public (G := G) hL hH hTypeI
  · have hSrcII : Section8.typeIIDefinitionData L H :=
      Section8.theorem_8_8_typeII_to_source_public (G := G) hL hH hTypeII
    have hLsH : Ls = H := by
      rcases hLs with hEarly | hLate
      · exact hEarly.2
      · exact False.elim
          (Section8.section16_not_typeIII_or_typeIV_of_typeII
            hL hH hTypeII hLate.1)
    have hxH : x ∈ H := by
      rw [← hLsH]
      exact hP0Ls hxP0
    have hTI :
        section16TISubsetWithNormalizer
          (section16NonidentityElements (H : Set G)) L :=
      Section8.theorem_8_16_typeII_mf_punctured_tiWithNormalizer hL hSrcII
    have hcent : Subgroup.centralizer ({x} : Set G) ≤ L :=
      theorem_12_10_centralizer_le_of_tiWithNormalizer
        hTI ⟨hxH, hxne⟩ hxne
    exact False.elim (hCnotL (by simpa [elementCentralizerIn] using hcent))
  · exact False.elim (hLateFalse (Or.inl hTypeIII))
  · exact False.elim (hLateFalse (Or.inr hTypeIV))
  · have hSrcV : Section8.typeVDefinitionData L H :=
      Section8.theorem_8_8_typeV_to_source_public (G := G) hL hH hTypeV
    exact False.elim (Section10.theorem_10_10 ⟨L, H, hL, hH, hSrcV⟩)

/-- Source leaf for the second PF `(12.10)` phase: the Type-I case forces
`L` to be Frobenius with kernel `H`. -/
public theorem theorem_12_10_typeI_frobenius_source_leaf
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ) :
    theorem_12_10_typeI_frobenius_source_data M K K' P0 L H Ls x p := by
  classical
  intro h128 h129 hTypeI
  rcases h129 with
    ⟨hP0comm, hP0rank, hL, hH, hLs, hP0Ls, _hxL,
      ⟨hp, hxOmega, hxne⟩, _hCK, _hNxM, hCnotL⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hxP0 : x ∈ P0 := by
    rcases hxOmega with ⟨y, _hyOmega, hyx⟩
    have hyP0 : (y : G) ∈ P0 := y.property
    simpa using hyx ▸ hyP0
  have hLsEq : Ls = H := by
    rcases hLs with hEarly | hLate
    · exact hEarly.2
    · rcases hLate.1 with hIII | hIV
      · rcases Section8.theorem_8_8_typeIII_to_source_public
          (G := G) hL hH hIII with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeI)
      · rcases Section8.theorem_8_8_typeIV_to_source_public
          (G := G) hL hH hIV with
          ⟨U, W1, W2, hP, _hCond, _hUcomm, _hUnorm⟩
        exact False.elim
          (Section8.not_typeIDefinitionData_of_typeP_source_data hP hTypeI)
  have hP0H : P0 ≤ H := by simpa [hLsEq] using hP0Ls
  have hxH : x ∈ H := hP0H hxP0
  rcases hTypeI with ⟨U, U1, U0, hF, hCases⟩
  have hnotTI :
      ¬ section16TISubset (section16NonidentityElements (H : Set G)) := by
    intro hTI
    have hHL : H ≤ L := section16MFSubgroup_le hH
    have hHnorm : (H.subgroupOf L).Normal :=
      section16MFSubgroup_subgroupOf_normal hH
    have hHne : H.subgroupOf L ≠ ⊥ := by
      intro hbot
      have hcard : Nat.card H = 1 := by
        calc
          Nat.card H = Nat.card (H.subgroupOf L) :=
            (natCard_subgroupOf_eq H L hHL).symm
          _ = 1 := by simp [hbot]
      exact (ne_of_gt hF.2.2.2.1) ((Subgroup.eq_bot_iff_card (H := H)).2 hcard)
    have hTI2 :=
      theorem_12_6_isTISubsetWithNormalizer_subgroupImagePuncturedSet
        L H hL hHL hHnorm hHne hTI
    have hHmap : (H.subgroupOf L).map L.subtype = H :=
      Subgroup.map_subgroupOf_eq_of_le hHL
    have hAeq :
        Section6.subgroupImagePuncturedSet L (H.subgroupOf L) =
          section16NonidentityElements (H : Set G) := by
      rw [Section6.theorem_6_8_subgroupImagePuncturedSet_eq_map_punctured, hHmap]
      ext z
      rfl
    have hSetNormEq :
        Section2.setNormalizer
            (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) =
          Subgroup.normalizer
            (Section6.subgroupImagePuncturedSet L (H.subgroupOf L)) := by
      ext g
      simp [Section2.setNormalizer, Section2.normalizesSet, Section2.conjBy,
        Subgroup.normalizer, iff_comm]
    have hNorm :
        Subgroup.normalizer (section16NonidentityElements (H : Set G)) = L := by
      rw [← hAeq, ← hSetNormEq]
      exact hTI2.2.2.2
    have hTIWith :
        section16TISubsetWithNormalizer
          (section16NonidentityElements (H : Set G)) L :=
      ⟨hTI, hNorm⟩
    have hcent : Subgroup.centralizer ({x} : Set G) ≤ L :=
      theorem_12_10_centralizer_le_of_tiWithNormalizer
        hTIWith ⟨hxH, hxne⟩ hxne
    exact hCnotL (by simpa [elementCentralizerIn] using hcent)
  rcases hCases with hTI | hCases
  · exact False.elim (hnotTI hTI)
  have h128copy := h128
  rcases h128copy with
    ⟨_hp128, _hbadp, hmin, _hM, _hK, _hTypeIM, _hMs, _hK',
      _hnoncyc, hP0Sylow⟩
  have hP0p : IsPGroup p P0 := by
    rcases hP0Sylow with ⟨P, hP0eq⟩
    rw [← hP0eq]
    dsimp [section10AmbientSylowSubgroup]
    exact IsPGroup.map (p := p) (H := (P : Subgroup M)) P.isPGroup' M.subtype
  have hP0ne : P0 ≠ ⊥ := by
    intro hbot
    have hcyc : IsCyclic P0 := by
      rw [hbot]
      infer_instance
    letI : IsCyclic P0 := hcyc
    have hle : groupRank P0 ≤ 1 := groupRank_le_one_of_isCyclic P0
    omega
  have hpP0 : p ∣ Nat.card P0 := by
    have hP0nontrivial : Nontrivial P0 :=
      (Subgroup.nontrivial_iff_ne_bot P0).2 hP0ne
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := P0) (hG := hP0p)).1
        hP0nontrivial with ⟨n, hnpos, hcard⟩
    rw [hcard]
    exact dvd_pow_self p hnpos.ne'
  let pp : Nat.Primes := ⟨p, hp⟩
  have hpH : pp ∈ subgroupPrimeSet H := by
    have hpCardH : p ∣ Nat.card H :=
      hpP0.trans (Subgroup.card_dvd_of_le hP0H)
    change p ∣ Nat.card H
    exact hpCardH
  have hpOdd : Odd p := by
    exact Odd.of_dvd_nat IsMinCE.odd_order
      (hpP0.trans (Subgroup.card_subgroup_dvd_card P0))
  refine frobeniusWithKernel_of_typeFData_cyclicSylow hF ?_
  intro q Q
  by_contra hQnoncyc
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hTypeI' : Section8.typeIDefinitionData L H :=
    ⟨U, U1, U0, hF, Or.inr hCases⟩
  have hbadq : badPrimeForHypothesis12 G q.val := by
    refine ⟨q.property, L, H, hL, hH, hTypeI', ?_⟩
    exact quotientHasNoncyclicSylow_of_typeFData_noncyclic_sylow
      (M := L) (MF := H) (U := U) (U1 := U1) (U0 := U0)
      hF Q hQnoncyc
  have hpq : p ≤ q.val := hmin q.val hbadq
  have hQne : (Q : Subgroup U) ≠ ⊥ := by
    intro hbot
    apply hQnoncyc
    rw [hbot]
    infer_instance
  have hqQ : q.val ∣ Nat.card (Q : Subgroup U) := by
    have hQnontrivial : Nontrivial (Q : Subgroup U) :=
      (Subgroup.nontrivial_iff_ne_bot (Q : Subgroup U)).2 hQne
    rcases (IsPGroup.nontrivial_iff_card
        (p := q.val) (G := (Q : Subgroup U)) (hG := Q.isPGroup')).1
        hQnontrivial with ⟨n, hnpos, hcard⟩
    rw [hcard]
    exact dvd_pow_self q.val hnpos.ne'
  have hqU : q.val ∣ Nat.card U :=
    hqQ.trans (Subgroup.card_subgroup_dvd_card (Q : Subgroup U))
  have hqOdd : Odd q.val := by
    exact Odd.of_dvd_nat IsMinCE.odd_order
      (hqU.trans (Subgroup.card_subgroup_dvd_card U))
  have hqExp : q.val ∣ Monoid.exponent U := by
    rcases exists_prime_orderOf_dvd_card' (G := U) q.val hqU with
      ⟨a, haorder⟩
    simpa [haorder] using Monoid.order_dvd_exponent a
  have hq_lt_of_pm
      (hpm : q.val ∣ p - 1 ∨ q.val ∣ p + 1) : q.val < p := by
    rcases hpm with hpred | hsucc
    · have hle : q.val ≤ p - 1 :=
        Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hpred
      have hq2 := q.property.two_le
      omega
    · have hle : q.val ≤ p + 1 :=
        Nat.le_of_dvd (by omega) hsucc
      have hnep : q.val ≠ p := by
        intro heq
        have hqp : q.val ∣ p := by simp [heq]
        have hqone : q.val ∣ 1 :=
          (Nat.dvd_add_iff_left hqp).2 (by simpa [Nat.add_comm] using hsucc)
        exact q.property.not_dvd_one hqone
      have hnesucc : q.val ≠ p + 1 := by
        intro heq
        rcases hpOdd with ⟨a, ha⟩
        rcases hqOdd with ⟨b, hb⟩
        have hp2 := hp.two_le
        have hq2 := q.property.two_le
        omega
      have hp2 := hp.two_le
      have hq2 := q.property.two_le
      omega
  rcases hCases with hRank | hExp
  · letI : IsMulCommutative H := hRank.1
    let P : Subgroup G := (pCore p H).map H.subtype
    have hPH : P ≤ H := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨zH, _hzcore, rfl⟩
      exact zH.property
    have hPp : IsPGroup p P := by
      simpa [P] using
        IsPGroup.map (p := p) (H := pCore p H) (pCore_isPGroup (G := H))
          H.subtype
    have hPcomm : IsMulCommutative P := by infer_instance
    letI : IsMulCommutative P := hPcomm
    letI : Fact (IsPGroup p P) := ⟨hPp⟩
    let P0H : Subgroup H := P0.subgroupOf H
    have hP0Hp : IsPGroup p P0H :=
      hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
    have hP0Hnormal : P0H.Normal := by infer_instance
    have hP0Hcore : P0H ≤ pCore p H :=
      le_sSup ⟨hP0Hnormal, hP0Hp⟩
    have hP0P : P0 ≤ P := by
      intro z hz
      let zH : H := ⟨z, hP0H hz⟩
      have hzP0H : zH ∈ P0H := by
        simpa [P0H, Subgroup.mem_subgroupOf] using hz
      exact Subgroup.mem_map.mpr
        ⟨zH, hP0Hcore hzP0H, rfl⟩
    have hPrank : groupRank P = 2 := by
      apply le_antisymm
      · exact (section10_groupRank_le_of_le hPH).trans_eq hRank.2
      · rw [← hP0rank]
        exact section10_groupRank_le_of_le hP0P
    have hPgen : generatorRank P = 2 := by
      apply le_antisymm
      · exact
          (generatorRank_le_groupRank_of_commutative_pgroup (p := p) P).trans_eq
            hPrank
      · rw [← hPrank]
        exact groupRank_le_generatorRank_of_commutative_pgroup hPp hPcomm
    let P1 : Subgroup G := section12OmegaOneSubgroup pp P
    have hP1P : P1 ≤ P := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨zP, _hzOmega, rfl⟩
      exact zP.property
    have hP1H : P1 ≤ H := hP1P.trans hPH
    have hP1card : Nat.card P1 = p ^ 2 := by
      calc
        Nat.card P1 = Nat.card (omega₁ (G := P) (p := p)) := by
          exact Subgroup.card_map_of_injective
            (K := omega₁ (G := P) (p := p)) (f := P.subtype)
            P.subtype_injective
        _ = p ^ generatorRank P :=
          omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) P
        _ = p ^ 2 := by rw [hPgen]
    have hFcopy := hF
    rcases hFcopy with
      ⟨_hsolvL, _hoddL, _hHsrc, _hHne, _hHlt, _hUne, hcomp,
        _hU1le, _hU1comm, _hU1norm, _hcent, hU0le, hExpEq, hfrob0⟩
    have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.1).1
        (section16MFSubgroup_subgroupOf_normal hH)
    have hU0normH : U0 ≤ Subgroup.normalizer (H : Set G) :=
      hU0le.trans (hcomp.2.1.trans hLnormH)
    haveI : (pCore p H).Characteristic :=
      pCore_characteristic (G := H) (p := p)
    have hNormHleP :
        Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (P : Set G) := by
      simpa [P] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := H) (K := pCore p H))
    haveI : (omega₁ (G := P) (p := p)).Characteristic :=
      omega₁_characteristic (G := P) (p := p)
    have hNormPleP1 :
        Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (P1 : Set G) := by
      simpa [P1, section12OmegaOneSubgroup] using
        (section8_normalizer_map_subtype_le_of_characteristic
          (G := G) (H := P) (K := omega₁ (G := P) (p := p)))
    have hU0normP1 : U0 ≤ Subgroup.normalizer (P1 : Set G) :=
      hU0normH.trans (hNormHleP.trans hNormPleP1)
    have hHnormP1 : H ≤ Subgroup.normalizer (P1 : Set G) := by
      have hnormal : (P1.subgroupOf H).Normal := by infer_instance
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP1H).1 hnormal
    let S : Subgroup G := H ⊔ U0
    have hHS : H ≤ S := le_sup_left
    have hU0S : U0 ≤ S := le_sup_right
    have hP1S : P1 ≤ S := hP1H.trans hHS
    have hP1normalS : (P1.subgroupOf S).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hP1S).2
        (sup_le hHnormP1 hU0normP1)
    letI : (P1.subgroupOf S).Normal := hP1normalS
    have hfrobS :
        IsFrobeniusGroupWithKernelComplement
          (H.subgroupOf S) (U0.subgroupOf S) := by
      simpa [S, section12FrobeniusJoinWithKernel] using hfrob0
    have hcentS :
        ∀ r : U0.subgroupOf S, r ≠ 1 →
          Section2.centralizerIn (H.subgroupOf S) (r : S) = ⊥ := by
      have hcent :=
        (lemma_3_1 (H.subgroupOf S) (U0.subgroupOf S)
          hfrobS.kernel_ne_bot hfrobS.complement_ne_bot hfrobS.normal
          hfrobS.isComplement').1 hfrobS
      simpa [elementCentralizerIn, Section2.centralizerIn, Section2.elementCentralizer] using hcent
    have hP1subleHsub : P1.subgroupOf S ≤ H.subgroupOf S := by
      intro z hz
      exact hP1H hz
    have hdivLocal :
        Nat.card (U0.subgroupOf S) ∣ Nat.card (P1.subgroupOf S) - 1 :=
      Section6.frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
        hP1subleHsub hcentS
    have hcardU0S : Nat.card (U0.subgroupOf S) = Nat.card U0 :=
      natCard_subgroupOf_eq U0 S hU0S
    have hcardP1S : Nat.card (P1.subgroupOf S) = Nat.card P1 :=
      natCard_subgroupOf_eq P1 S hP1S
    have hdiv : Nat.card U0 ∣ Nat.card P1 - 1 := by
      rw [hcardU0S, hcardP1S] at hdivLocal
      exact hdivLocal
    have hqExpU0 : q.val ∣ Monoid.exponent U0 := by
      simpa [hExpEq] using hqExp
    have hqU0 : q.val ∣ Nat.card U0 :=
      hqExpU0.trans (Group.exponent_dvd_nat_card (G := U0))
    have hqSqPred : q.val ∣ p ^ 2 - 1 := by
      have hdiv' := hqU0.trans hdiv
      rw [hP1card] at hdiv'
      exact hdiv'
    have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      simpa [pow_two, Nat.mul_comm] using (Nat.pow_two_sub_pow_two p 1)
    have hpm : q.val ∣ p - 1 ∨ q.val ∣ p + 1 := by
      rw [hfactor] at hqSqPred
      exact q.property.dvd_mul.mp hqSqPred
    exact (not_lt_of_ge hpq) (hq_lt_of_pm hpm)
  · have hqPred : q.val ∣ p - 1 :=
      hqExp.trans (hExp.1 pp hpH)
    exact (not_lt_of_ge hpq) (hq_lt_of_pm (Or.inl hqPred))

/-- Peterfalvi `(12.10)`.

Let `H = L_F`.  Then `L` is a Frobenius group with kernel `H`. -/
public theorem theorem_12_10
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M K K' P0 L H Ls : Subgroup G)
    (x : G) (p : ℕ)
    (h128 : hypothesis_12_8_data M K K' P0 p)
    (h129 : theorem_12_9_data M K K' P0 L H Ls x p) :
    Section7.frobeniusWithKernel L H := by
  have hsrc : theorem_12_10_source_data M K K' P0 L H Ls x p :=
    theorem_12_10_source_data_of_typeI_source_data M K K' P0 L H Ls x p
      (theorem_12_10_typeI_reduction_source_leaf M K K' P0 L H Ls x p)
      (theorem_12_10_typeI_frobenius_source_leaf M K K' P0 L H Ls x p)
  exact theorem_12_10_of_source_data M K K' P0 L H Ls x p hsrc h128 h129

end CFSG.Section12

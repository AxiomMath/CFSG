module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGappendixC.theorem_C
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_II
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.MinCE
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_8
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection12.PFsection12_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_Conclusion

namespace CFSG
end CFSG
open CFSG

/-!
# Final odd-order theorem wiring

This module records the final interface between Peterfalvi Section 14 and BG
Appendix C. The remaining mathematical bridge is the identification of the PF
Section 14 configuration with Appendix C hypothesis `(B)`.
-/

noncomputable section

open scoped BigOperators Pointwise

universe u

/-- The Feit-Thompson odd order theorem, as a proposition. -/
@[expose] public def CFSG.oddOrderTheorem : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G

/-- The standard minimal-counterexample reduction for the odd order theorem. -/
@[expose] public def CFSG.minimalCounterexampleReduction : Prop :=
  ¬ oddOrderTheorem.{u} →
    ∃ (G : Type u) (hG : Group G) (hfin : Finite G), @IsMinCE G hG hfin


/-- A group is solvable if a normal subgroup and the corresponding quotient are
solvable. This is the extension step used in the minimal-counterexample
reduction. -/
public theorem CFSG.isSolvable_of_normal_subgroup_and_quotient
    {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] [Group.IsSolvable (G ⧸ N)] : Group.IsSolvable G := by
  refine Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
  rw [QuotientGroup.ker_mk']
  simpa [MonoidHom.range_eq_map] using (N.range_subtype : N.subtype.range = N).symm.le

/-- Quotienting by a nontrivial normal subgroup strictly lowers cardinality. -/
public theorem CFSG.natCard_quotient_lt_of_ne_bot
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) :
    Nat.card (G ⧸ N) < Nat.card G := by
  have hNcard : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN
  have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  have hlt : Nat.card (G ⧸ N) < Nat.card (G ⧸ N) * Nat.card N := by
    simpa using Nat.mul_lt_mul_of_pos_left hNcard hQpos
  have hcard :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G) (s := N)).symm
  exact hlt.trans_eq hcard


/-- The PF Section 14 data package that supplies `q < p` and the conclusion of
PF `(14.2)`. -/
@[expose] public def CFSG.pfSection14FinalData
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∃ (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ),
      Section13.hypothesis_13_1_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d ∧
      Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d ∧
      (Section14.hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
          Sfam Tfam τS τT p q u v c d →
        Section14.theorem_14_2_a_data P U W2 p q ∧
          Section14.theorem_14_2_b_data Q W1 W2 U q) ∧
      Section14.hypothesis_14_1_statement p q

/-- The all-Type-I branch in the BG Section 16 final alternative. -/
@[expose] public def CFSG.bg16AllMaximalTypeI
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
    ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF

/-- The non-Type-I structural branch in the BG Section 16 final alternative,
using the PF Section 8 case `(8.8)(b)` package. -/
@[expose] public def CFSG.bg16CaseBData
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∃ W W1 W2 S T SF TF : Subgroup G,
    Section8.theorem_8_8_case_b_data W W1 W2 S T SF TF

/-- The remaining bridge from the completed local-analysis alternative to the
PF Section 14 final data. The first component rules out the all-Type-I branch;
the second extracts the Section 13/14 source data from the case `(8.8)(b)`
branch. -/
@[expose] public def CFSG.pfSection14FinalDataBridge
    (G : Type u) [Group G] [Finite G] : Prop :=
  IsMinCE G →
    (bg16AllMaximalTypeI G → False) ∧
      (bg16CaseBData G → pfSection14FinalData G)

/-- The Section 13 setup data that should be extracted from BG16 case `(8.8)(b)`,
together with the final inequality `q < p`. -/
@[expose] public def CFSG.pfSection13CaseBFinalData
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∃ (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ),
      Section13.hypothesis_13_1_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d ∧
      Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d ∧
      Section14.hypothesis_14_1_statement p q


/-- The raw-aligned Type-P common-complement data needed once the case `(8.8)(b)`
subgroups `W, W1, W2, S, T, P, Q` are fixed. -/
@[expose] public def CFSG.pfSection13TypePDataForCaseB
    {G : Type u} [Group G] [Finite G]
    (_W W1 W2 Smax Tmax P Q : Subgroup G) : Prop :=
  ∃ U V : Subgroup G,
    Section8.typePData Smax P U W1 W2 ∧
      Section8.typePData Tmax Q V W2 W1

/-- The additional Section 13 setup data needed once the raw case `(8.8)(b)`
subgroups `W, W1, W2, S, T, P, Q` are fixed. This isolates the
raw-aligned Type-P witnesses, character-family, cardinal, centralizer, and
`q < p` choices that are not part of `Section8.theorem_8_8_case_b_data`
itself. -/
@[expose] public def CFSG.pfSection13SetupDataForCaseB
    {G : Type u} [Group G] [Finite G]
    (_W W1 W2 Smax Tmax P Q : Subgroup G) : Prop :=
  ∃ (U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ),
      p = Nat.card W2 ∧
      q = Nat.card W1 ∧
      C = subgroupCentralizerIn U P ∧
      D = subgroupCentralizerIn V Q ∧
      Section8.typePData Smax P U W1 W2 ∧
      Section8.typePData Tmax Q V W2 W1 ∧
      Nat.card U = u * c ∧
      Nat.card V = v * d ∧
      Section5.hypothesis_5_2_b_statement Sfam τS ∧
      Section5.hypothesis_5_2_b_statement Tfam τT ∧
      Section13.nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
      Section13.nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
      Section13.dadeIsometryRelativeToAZero Smax P Sfam τS ∧
      Section13.dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
      Section13.hypothesis_13_1_characterNotationData Smax Tmax _W W1 W2 p q ∧
        Section13.hypothesis_13_1_dadeDifferenceDataFor Smax Tmax _W W1 W2
          τS τT p q ∧
        Section13.hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax _W W1 W2 p q ∧
        Section13.hypothesis_13_1_conjugateIndexDataFor Smax Tmax _W W1 W2 p q ∧
        Section13.hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax _W W1 W2
          P Q τS τT p q ∧
          Section13.hypothesis_13_1_sourceChoiceData G ∧
          Section13.typePFourSixTauSourceData Smax P U W1 W2 τS ∧
          Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT ∧
          c = Nat.card C ∧
          d = Nat.card D ∧
        Section14.hypothesis_14_1_statement p q


/-- The compatible source PF `(13.1)` tail package for a case-B branch.

The families are chosen together with the nonkernel, `A₀`-relative Dade, and
character-notation data; choosing a generic punctured family first is too weak
for the later PF13 source fields. -/
@[expose] public def CFSG.pfSection13SourceTailSetupForCaseB
    {G : Type u} [Group G] [Finite G]
    (W W1 W2 Smax Tmax P Q U V : Subgroup G) : Prop :=
  ∃ (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G),
      Section5.hypothesis_5_2_b_statement Sfam τS ∧
      Section5.hypothesis_5_2_b_statement Tfam τT ∧
      Section13.nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
      Section13.nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
      Section13.dadeIsometryRelativeToAZero Smax P Sfam τS ∧
      Section13.dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
        Section13.hypothesis_13_1_characterNotationData Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        Section13.hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2
          τS τT (Nat.card W2) (Nat.card W1) ∧
        Section13.hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        Section13.hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2
          (Nat.card W2) (Nat.card W1) ∧
        Section13.hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2
          P Q τS τT (Nat.card W2) (Nat.card W1) ∧
        Section13.hypothesis_13_1_sourceChoiceData G ∧
          Section13.typePFourSixTauSourceData Smax P U W1 W2 τS ∧
          Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT


/-- PF Section 14 theorem `(14.2)` for the final Section 13 setup. -/
@[expose] public def CFSG.pfSection14StatementBridge
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ},
      Section13.hypothesis_13_1_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section14.hypothesis_14_1_statement p q →
        Section14.hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
            Sfam Tfam τS τT p q u v c d →
          Section14.theorem_14_2_a_data P U W2 p q ∧
            Section14.theorem_14_2_b_data Q W1 W2 U q


/-- Assemble full PF Section 14 final data from the explicit Section 13 data
and PF `(14.2)` bridge. -/
public theorem CFSG.pfSection14FinalData_of_pfSection13CaseBFinalData
    {G : Type u} [Group G] [Finite G]
    (hdata : pfSection13CaseBFinalData G)
    (h14 : pfSection14StatementBridge G) :
    pfSection14FinalData G := by
  rcases hdata with
    ⟨Smax, Tmax, W, W1, W2, P, Q, U, V, C, D,
      Sfam, Tfam, τS, τT, p, q, u, v, c, d, h13, hsource, h14_1⟩
  exact ⟨Smax, Tmax, W, W1, W2, P, Q, U, V, C, D,
    Sfam, Tfam, τS, τT, p, q, u, v, c, d, h13, hsource,
    h14 h13 h14_1, h14_1⟩

/-- The exact source-facing type fields still missing in the conversion from
the BG16-aligned PF `(8.8)(b)` package to the literal source package.

The debt is case-B-specific: the broad reverse implications
`section16Type* M MF → Section8.type*DefinitionData M MF` are not valid with
the currently recorded hypotheses, because the source definitions also need
Type-F/Type-P witnesses and source complement fields. The PF `(8.8)` source
theorem supplies an existential source case, but not for these already-selected
BG16 case-B witnesses. -/
public theorem CFSG.section8_source_type_fields_of_case_b_data_core
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q) :
    (Section8.typeIIDefinitionData Smax P ∨
        Section8.typeIIDefinitionData Tmax Q) ∧
      (Section8.typeIIDefinitionData Smax P ∨
        Section8.typeIIIDefinitionData Smax P ∨
          Section8.typeIVDefinitionData Smax P ∨
            Section8.typeVDefinitionData Smax P) ∧
      (Section8.typeIIDefinitionData Tmax Q ∨
        Section8.typeIIIDefinitionData Tmax Q ∨
          Section8.typeIVDefinitionData Tmax Q ∨
            Section8.typeVDefinitionData Tmax Q) ∧
      (∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        (∃ g : G, M = Smax.conjBy g) ∨
          (∃ g : G, M = Tmax.conjBy g) ∨
            ∃ MF : Subgroup G, section16MFSubgroup M MF ∧
              Section8.typeIDefinitionData M MF) := by
  letI : IsMinCE G := hmin
  exact Section8.theorem_8_8_source_type_fields_of_case_b_data hcase

/-- In a complement decomposition, if the left factor is Hall then the right
factor is Hall for its own prime set. -/
public theorem CFSG.section12ComplementIn_right_isHall_of_left_hall_for_final
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    (hHnormal : (H.subgroupOf M).Normal)
    (hHHall : section16HallSubgroupOf H M) :
    section16HallSubgroupOf K M := by
  classical
  letI : (H.subgroupOf M).Normal := hHnormal
  rcases hcomp with ⟨hHM, hKM, hsup, hdisj⟩
  have hcomp' : (K.subgroupOf M).IsComplement' (H.subgroupOf M) := by
    have hsup_local : K.subgroupOf M ⊔ H.subgroupOf M = ⊤ := by
      calc
        K.subgroupOf M ⊔ H.subgroupOf M = (K ⊔ H).subgroupOf M := by
          symm
          exact Subgroup.subgroupOf_sup (A := K) (A' := H) (B := M) hKM hHM
        _ = ⊤ := by
          rw [sup_comm, hsup]
          simp
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxH
      apply Subtype.ext
      exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxH,
        by simpa [Subgroup.mem_subgroupOf] using hxK⟩
    · simpa [hsup_local] using
        (Subgroup.mul_normal (K.subgroupOf M) (H.subgroupOf M)).symm
  rcases hHHall with ⟨_hHM, hHHallSub⟩
  refine ⟨hKM, ?_⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet K)
    (H := K.subgroupOf M) ?_ ?_
  · intro p hpK
    have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M hKM
    simpa [subgroupPrimeSet, hcardK] using hpK
  · intro p hpK hpidxK
    have hpHcard : p.val ∣ Nat.card (H.subgroupOf M) := by
      simpa [hcomp'.symm.index_eq_card] using hpidxK
    have hpHπ : p ∈ subgroupPrimeSet H :=
      hHHallSub.p_in_pi_of_p_dvd_card p (by
        have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
          natCard_subgroupOf_eq H M hHM
        simpa [subgroupPrimeSet, hcardH] using hpHcard)
    have hpKcard : p.val ∣ Nat.card (K.subgroupOf M) := by
      have hcardK : Nat.card (K.subgroupOf M) = Nat.card K :=
        natCard_subgroupOf_eq K M hKM
      simpa [subgroupPrimeSet, hcardK] using hpK
    have hpHidx : p.val ∣ (H.subgroupOf M).index := by
      simpa [hcomp'.index_eq_card] using hpKcard
    exact (hHHallSub.p_in_pi_of_p_dvd_index p hpHidx) hpHπ

/-- Source-facing PF `(8.8)(b)` data from the BG16-aligned case-B package.
This is a genuine source/BG bridge, not just projection from the raw data. -/
public theorem CFSG.section8_source_case_b_data_of_case_b_data_core
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q) :
    Section8.theorem_8_8_source_case_b_data W W1 W2 Smax Tmax P Q := by
  rcases section8_source_type_fields_of_case_b_data_core hmin hcase with
    ⟨hTypeII', hSType', hTType', hCover'⟩
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
      _hSnotTypeI, _hTnotTypeI, hSeq, hTeq, hSinf, hTinf,
      _hSW2leSecond, _hTW1leSecond, hST, _hCover, _hTypeII, _hSType, _hTType,
      _haligned⟩
  have hSeq' : Smax = ambientDerivedSubgroup Smax ⊔ W1 := by
    calc
      Smax = W1 ⊔ ambientDerivedSubgroup Smax := hSeq
      _ = ambientDerivedSubgroup Smax ⊔ W1 := sup_comm W1 (ambientDerivedSubgroup Smax)
  have hTeq' : Tmax = ambientDerivedSubgroup Tmax ⊔ W2 := by
    calc
      Tmax = W2 ⊔ ambientDerivedSubgroup Tmax := hTeq
      _ = ambientDerivedSubgroup Tmax ⊔ W2 := sup_comm W2 (ambientDerivedSubgroup Tmax)
  have hSdisj : Disjoint (ambientDerivedSubgroup Smax) W1 := by
    simpa [disjoint_iff] using hSinf
  have hTdisj : Disjoint (ambientDerivedSubgroup Tmax) W2 := by
    simpa [disjoint_iff] using hTinf
  exact ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
    hSeq', hTeq', hSdisj, hTdisj, hST, hTypeII', hSType', hTType', hCover'⟩

/-- Convert the BG16-aligned Type-P package used by final wiring into the
literal source-facing PF Definition `(8.4)` package, once the source complement
and second-derived containment fields are supplied explicitly. -/
public theorem CFSG.section8_typePDefinitionData_of_typePData_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hMcomp : section12ComplementIn M (ambientDerivedSubgroup M) W1)
    (hW1ne : W1 ≠ ⊥)
    (hW2leSecond : W2 ≤ section16SecondDerivedSubgroup M)
    (hP : Section8.typePData M MF U W1 W2) :
    Section8.typePDefinitionData M MF U W1 W2 := by
  rcases hP with ⟨hMF, hCommon⟩
  rcases hCommon with
    ⟨hDHall, _hMFleD, hDercomp, hUnil, hW1norm, hW1cyc, _hW1card,
      hMFnotcyc, hSecond, hFit, hFitDer, hW2leMF, hW2ne, hW2cyc,
      hCent, hNorm, _hT6⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hW1Hall : section16HallSubgroupOf W1 M :=
    section12ComplementIn_right_isHall_of_left_hall_for_final
      (M := M) (H := ambientDerivedSubgroup M) (K := W1)
      hMcomp hDnormal hDHall
  have hUle : U ≤ ambientDerivedSubgroup M := hDercomp.2.1
  have hW2leInf : W2 ≤ MF ⊓ section16SecondDerivedSubgroup M :=
    le_inf hW2leMF hW2leSecond
  exact ⟨hMF, hW1cyc, hW1ne, hW1Hall, hMcomp, hUle, hUnil, hW1norm,
    hDercomp, hMFnotcyc, hSecond, hFit.symm, hFitDer, hW2leInf, hW2cyc,
    hW2ne, hCent, hNorm⟩


/-- The source-specific PF `(13.1)` fields not supplied by the coarse
BG-aligned case-B setup. Equality and cardinality fields are filled directly in
`section13_hypothesis_13_1_sourceData_of_caseB_setup_fields`; this core names
the remaining source case-B, source Type-P, nonkernel-family, Dade-relative,
and character-notation content. -/
public theorem CFSG.section13_hypothesis_13_1_sourceFields_of_caseB_setup_core
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q : ℕ}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (_hp : p = Nat.card W2)
    (_hq : q = Nat.card W1)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (_hτS : Section5.hypothesis_5_2_b_statement Sfam τS)
    (_hτT : Section5.hypothesis_5_2_b_statement Tfam τT)
    (hSnonkernel : Section13.nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonkernel : Section13.nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : Section13.dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : Section13.dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationData Smax Tmax W W1 W2 p q) :
      Section13.hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2
        τS τT p q →
      Section13.hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2 p q →
      Section13.hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2 p q →
      Section13.hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2
        P Q τS τT p q →
      Section13.hypothesis_13_1_sourceChoiceData G →
      Section8.theorem_8_8_source_case_b_data W W1 W2 Smax Tmax P Q ∧
      Section8.typePDefinitionData Smax P U W1 W2 ∧
      Section8.typePDefinitionData Tmax Q V W2 W1 ∧
      Section13.nonkernelInducedFamily Smax (P ⊔ U) P Sfam ∧
      Section13.nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam ∧
      Section13.dadeIsometryRelativeToAZero Smax P Sfam τS ∧
      Section13.dadeIsometryRelativeToAZero Tmax Q Tfam τT ∧
      Section13.hypothesis_13_1_characterNotationData Smax Tmax W W1 W2 p q ∧
        Section13.hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2
          τS τT p q ∧
        Section13.hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2 p q ∧
        Section13.hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2 p q ∧
        Section13.hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2
          P Q τS τT p q ∧
        Section13.hypothesis_13_1_sourceChoiceData G := by
  intro hDadeDiff hZeroDegree hConjIndex hConjBetaTau hChoice
  have hsourceCase :
      Section8.theorem_8_8_source_case_b_data W W1 W2 Smax Tmax P Q :=
    section8_source_case_b_data_of_case_b_data_core hmin hcase
  rcases hcase with
    ⟨_hprod, _hcyc, hW1ne, hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSnotTypeI, _hTnotTypeI, hSeq, hTeq, hSinf, hTinf, hSW2leSecond,
      hTW1leSecond, _hST, _hCover, _hTypeII, _hSType, _hTType, _haligned⟩
  have hScomp :
      section12ComplementIn Smax (ambientDerivedSubgroup Smax) W1 := by
    refine ⟨section12_ambientDerivedSubgroup_le (G := G) (E := Smax), ?_, ?_, ?_⟩
    · rw [hSeq]
      exact le_sup_left
    · calc
        Smax = W1 ⊔ ambientDerivedSubgroup Smax := hSeq
        _ = ambientDerivedSubgroup Smax ⊔ W1 :=
          sup_comm W1 (ambientDerivedSubgroup Smax)
    · simpa [disjoint_iff] using hSinf
  have hTcomp :
      section12ComplementIn Tmax (ambientDerivedSubgroup Tmax) W2 := by
    refine ⟨section12_ambientDerivedSubgroup_le (G := G) (E := Tmax), ?_, ?_, ?_⟩
    · rw [hTeq]
      exact le_sup_left
    · calc
        Tmax = W2 ⊔ ambientDerivedSubgroup Tmax := hTeq
        _ = ambientDerivedSubgroup Tmax ⊔ W2 :=
          sup_comm W2 (ambientDerivedSubgroup Tmax)
    · simpa [disjoint_iff] using hTinf
  have hsourceSTypeP :
      Section8.typePDefinitionData Smax P U W1 W2 :=
    section8_typePDefinitionData_of_typePData_core
      hScomp hW1ne hSW2leSecond hSTypeP
  have hsourceTTypeP :
      Section8.typePDefinitionData Tmax Q V W2 W1 :=
    section8_typePDefinitionData_of_typePData_core
      hTcomp hW2ne hTW1leSecond hTTypeP
  exact ⟨hsourceCase, hsourceSTypeP, hsourceTTypeP, hSnonkernel,
    hTnonkernel, hDadeS, hDadeT, hnotation, hDadeDiff, hZeroDegree,
    hConjIndex, hConjBetaTau, hChoice⟩

/-- The source-facing PF `(13.1)` fields still missing after the raw case-B and
setup packages have fixed the final-data witnesses. This is the exact bridge
from the BG-aligned setup data to the source `(13.1)` package. -/
public theorem CFSG.section13_hypothesis_13_1_sourceData_of_caseB_setup_fields
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (_hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hp : p = Nat.card W2)
    (hq : q = Nat.card W1)
    (hC : C = subgroupCentralizerIn U P)
    (hD : D = subgroupCentralizerIn V Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1)
    (hUcard : Nat.card U = u * c)
    (hVcard : Nat.card V = v * d)
    (hτS : Section5.hypothesis_5_2_b_statement Sfam τS)
    (hτT : Section5.hypothesis_5_2_b_statement Tfam τT)
    (hSnonkernel : Section13.nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hTnonkernel : Section13.nonkernelInducedFamily Tmax (Q ⊔ V) Q Tfam)
    (hDadeS : Section13.dadeIsometryRelativeToAZero Smax P Sfam τS)
    (hDadeT : Section13.dadeIsometryRelativeToAZero Tmax Q Tfam τT)
    (hnotation :
      Section13.hypothesis_13_1_characterNotationData Smax Tmax W W1 W2 p q)
    (hDadeDiff :
      Section13.hypothesis_13_1_dadeDifferenceDataFor Smax Tmax W W1 W2
        τS τT p q)
      (hZeroDegree :
        Section13.hypothesis_13_1_zeroBaseDegreeDataFor Smax Tmax W W1 W2 p q)
      (hConjIndex :
        Section13.hypothesis_13_1_conjugateIndexDataFor Smax Tmax W W1 W2 p q)
      (hConjBetaTau :
        Section13.hypothesis_13_1_conjugateBetaTauDataFor Smax Tmax W W1 W2
          P Q τS τT p q)
        (hChoice : Section13.hypothesis_13_1_sourceChoiceData G)
        (hFourSixS : Section13.typePFourSixTauSourceData Smax P U W1 W2 τS)
        (hFourSixT : Section13.typePFourSixTauSourceData Tmax Q V W2 W1 τT)
      (hc : c = Nat.card C)
      (hd : d = Nat.card D)
      (hmin : IsMinCE G) :
    Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := by
    rcases section13_hypothesis_13_1_sourceFields_of_caseB_setup_core hmin hcase hp hq
        hSTypeP hTTypeP hτS hτT hSnonkernel hTnonkernel hDadeS
        hDadeT hnotation hDadeDiff hZeroDegree hConjIndex hConjBetaTau hChoice with
      ⟨hsourceCase, hsourceSTypeP, hsourceTTypeP, hSnonkernel, hTnonkernel,
        hDadeS, hDadeT, hnotation, hDadeDiff, hZeroDegree, hConjIndex,
        hConjBetaTau, hChoice⟩
    exact ⟨hsourceCase, hsourceSTypeP, hsourceTTypeP, hp, hq, hC, hD, hc, hd,
      hUcard, hVcard, hSnonkernel, hTnonkernel, hDadeS, hDadeT, hnotation,
      hDadeDiff, hZeroDegree, hConjIndex, hConjBetaTau, hChoice, hmin,
      hFourSixS, hFourSixT⟩

/-- Raw case `(8.8)(b)` data plus the explicit Section 13 setup choices package
the final Section 13 data used by PF Section 14. -/
public theorem CFSG.pfSection13CaseBFinalData_of_caseB_setupData
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hsetup : pfSection13SetupDataForCaseB W W1 W2 Smax Tmax P Q) :
    pfSection13CaseBFinalData G := by
  rcases hsetup with
    ⟨U, V, C, D, Sfam, Tfam, τS, τT, p, q, u, v, c, d,
          hp, hq, hC, hD, hSTypeP, hTTypeP, hUcard, hVcard,
          hτS, hτT, hSnonkernel, hTnonkernel, hDadeS, hDadeT, hnotation,
          hDadeDiff, hZeroDegree, hConjIndex, hConjBetaTau, hChoice,
          hFourSixS, hFourSixT, hc, hd, h14_1⟩
  have hcaseForData := hcase
  rcases hcase with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax,
      _hSF, _hTF, _hSnotTypeI, _hTnotTypeI, _hSeq, _hTeq, _hSinf, _hTinf,
      _hSW2leSecond, _hTW1leSecond, _hST, _hCover, _hTypeII, _hSType, _hTType,
      _hAligned⟩
  have hW : W = W1 ⊔ W2 := hprod.2.2.1
  have h13 : Section13.hypothesis_13_1_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := by
    exact ⟨hcaseForData, hSTypeP, hTTypeP, hW, hp, hq, hC, hD, hUcard, hVcard,
      hτS, hτT, hc, hd⟩
  have hsource :
      Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d :=
    section13_hypothesis_13_1_sourceData_of_caseB_setup_fields hmin hcaseForData
          hp hq hC hD hSTypeP hTTypeP hUcard hVcard hτS hτT hSnonkernel
          hTnonkernel hDadeS hDadeT hnotation hDadeDiff hZeroDegree hConjIndex
          hConjBetaTau hChoice hFourSixS hFourSixT hc hd hmin
  exact ⟨Smax, Tmax, W, W1, W2, P, Q, U, V, C, D,
    Sfam, Tfam, τS, τT, p, q, u, v, c, d, h13, hsource, h14_1⟩

/-- The compatible source-only PF `(13.1)` tail data for a raw case-B branch.

These fields must be chosen together: a coarse punctured-family and `(5.2)(b)`
map do not by themselves identify the PF13 nonkernel family, the `A₀(M)`-
relative Dade field, or the character notation. -/
public theorem CFSG.pfSection13SourceTailSetupForCaseB_core
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 Smax Tmax P Q U V : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q)
    (hSTypeP : Section8.typePData Smax P U W1 W2)
    (hTTypeP : Section8.typePData Tmax Q V W2 W1) :
    pfSection13SourceTailSetupForCaseB W W1 W2 Smax Tmax P Q U V := by
  exact Section13.hypothesis_13_1_source_tail_setup_of_case_b_typeP
    hmin hcase hSTypeP hTTypeP

/-- The structural part of the PF13 case-B setup: once the raw-aligned Type-P
data, compatible source-tail package, and cardinal orientation are supplied,
the remaining centralizer and cardinality fields are bookkeeping.

This is not just bookkeeping: the later PF `(13.2)` consumer needs the actual
Frobenius-kernel data, so the subgroups `U` and `V` cannot be chosen
canonically. -/
public theorem CFSG.pfSection13SetupDataForCaseB_of_typePData
    {G : Type u} [Group G] [Finite G]
    {_W W1 W2 Smax Tmax P Q : Subgroup G}
    (hmin : IsMinCE G)
    (hcase : Section8.theorem_8_8_case_b_data _W W1 W2 Smax Tmax P Q)
    (htypeP : pfSection13TypePDataForCaseB _W W1 W2 Smax Tmax P Q)
    (hqp : Nat.card W1 < Nat.card W2) :
    pfSection13SetupDataForCaseB _W W1 W2 Smax Tmax P Q := by
  classical
  rcases htypeP with ⟨U, V, hSTypeP, hTTypeP⟩
  rcases pfSection13SourceTailSetupForCaseB_core hmin hcase hSTypeP hTTypeP with
    ⟨Sfam, Tfam, τS, τT, hτS, hτT, hSnonkernel, hTnonkernel, hDadeS, hDadeT,
      hnotation, hDadeDiff, hZeroDegree, hConjIndex, hConjBetaTau, hChoice,
      hFourSixS, hFourSixT⟩
  let C : Subgroup G := subgroupCentralizerIn U P
  let D : Subgroup G := subgroupCentralizerIn V Q
  have hCleU : C ≤ U := by
    intro x hx
    exact hx.1
  have hDleV : D ≤ V := by
    intro x hx
    exact hx.1
  have hCdivU : Nat.card C ∣ Nat.card U :=
    Subgroup.card_dvd_of_le hCleU
  have hDdivV : Nat.card D ∣ Nat.card V :=
    Subgroup.card_dvd_of_le hDleV
  have hUcard : Nat.card U = (Nat.card U / Nat.card C) * Nat.card C := by
    exact (Nat.div_mul_cancel hCdivU).symm
  have hVcard : Nat.card V = (Nat.card V / Nat.card D) * Nat.card D := by
    exact (Nat.div_mul_cancel hDdivV).symm
  refine ⟨U, V, subgroupCentralizerIn U P, subgroupCentralizerIn V Q,
    Sfam, Tfam, τS, τT, Nat.card W2, Nat.card W1,
    Nat.card U / Nat.card C, Nat.card V / Nat.card D, Nat.card C, Nat.card D,
    rfl, rfl, rfl, rfl, hSTypeP, hTTypeP, ?_, ?_, hτS, hτT, hSnonkernel,
    hTnonkernel, hDadeS, hDadeT, hnotation,
    hDadeDiff, hZeroDegree, hConjIndex, hConjBetaTau, hChoice, hFourSixS,
    hFourSixT, rfl, rfl, ?_⟩
  · exact hUcard
  · exact hVcard
  · simpa [Section14.hypothesis_14_1_statement] using hqp

/-- In a cyclic internal direct product, the two factors have coprime orders. -/
public theorem CFSG.natCard_coprime_of_section12InternalDirectProduct_cyclic
    {G : Type u} [Group G] [Finite G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W)
    (hcyc : IsCyclic W) :
    Nat.Coprime (Nat.card W1) (Nat.card W2) := by
  classical
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  let J : Subgroup G := W1 ⊔ W2
  have hW1_norm_W2 : W1 ≤ Subgroup.normalizer (W2 : Set G) :=
    hcent.trans (centralizer_le_normalizer W2)
  let W1J : Subgroup J := W1.subgroupOf J
  let W2J : Subgroup J := W2.subgroupOf J
  haveI : W2J.Normal := by
    simpa [J, W2J] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := W2) hW1_norm_W2)
  let f : W1 × W2 →* W :=
    { toFun := fun p =>
        ⟨(p.1 : G) * (p.2 : G), W.mul_mem (hW1le p.1.2) (hW2le p.2.2)⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro p q
        ext
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          (Subgroup.mem_centralizer_iff.mp (hcent q.1.2) (p.2 : G) p.2.2).symm
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
              (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by
                simp [mul_assoc]
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by
                rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by
                simp [mul_assoc] }
  have hf_inj : Function.Injective f := by
    rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
    have hmul : (h₁ : G) * (k₁ : G) = (h₂ : G) * (k₂ : G) :=
      Subtype.ext_iff.mp heq
    have hleft_eq_right : (h₂ : G)⁻¹ * (h₁ : G) = (k₂ : G) * (k₁ : G)⁻¹ := by
      calc
        (h₂ : G)⁻¹ * (h₁ : G) =
            (h₂ : G)⁻¹ * ((h₁ : G) * (k₁ : G)) * (k₁ : G)⁻¹ := by
              simp [mul_assoc]
        _ = (h₂ : G)⁻¹ * ((h₂ : G) * (k₂ : G)) * (k₁ : G)⁻¹ := by
              rw [hmul]
        _ = (k₂ : G) * (k₁ : G)⁻¹ := by
              simp
    have hmemW1 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W1 :=
      W1.mul_mem (W1.inv_mem h₂.2) h₁.2
    have hmemW2 : (h₂ : G)⁻¹ * (h₁ : G) ∈ W2 := by
      rw [hleft_eq_right]
      exact W2.mul_mem k₂.2 (W2.inv_mem k₁.2)
    have hh_eq_one : (h₂ : G)⁻¹ * (h₁ : G) = 1 :=
      Subgroup.disjoint_def.mp hdisj hmemW1 hmemW2
    have hh : h₁ = h₂ := by
      apply Subtype.ext
      calc
        (h₁ : G) = (h₂ : G) * ((h₂ : G)⁻¹ * (h₁ : G)) := by simp
        _ = (h₂ : G) := by simp [hh_eq_one]
    have hk : k₁ = k₂ := by
      apply Subtype.ext
      have hmul' := congrArg (fun z : G => (h₂ : G)⁻¹ * z) hmul
      simpa [hh, mul_assoc] using hmul'
    exact Prod.ext hh hk
  have hf_surj : Function.Surjective f := by
    intro w
    let j : J := ⟨(w : G), by simp [J, ← hW, w.2]⟩
    have htop : W1J ⊔ W2J = ⊤ := by
      simpa [J, W1J, W2J] using
        (Subgroup.subgroupOf_sup (A := W1) (A' := W2) (B := J)
          le_sup_left le_sup_right).symm
    have hjmem : j ∈ W1J ⊔ W2J := by
      rw [htop]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right.mp hjmem) with ⟨x, hx, y, hy, hxy⟩
    refine ⟨(⟨(x : G), by simpa [W1J, Subgroup.mem_subgroupOf] using hx⟩,
      ⟨(y : G), by simpa [W2J, Subgroup.mem_subgroupOf] using hy⟩), ?_⟩
    ext
    change (x : G) * (y : G) = (w : G)
    simpa [j] using congrArg Subtype.val hxy
  let e : W1 × W2 ≃* W := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hprodcyc : IsCyclic (W1 × W2) := e.isCyclic.mpr hcyc
  letI : IsCyclic (W1 × W2) := hprodcyc
  simpa [Nat.card_eq_fintype_card] using coprime_card_of_isCyclic_prod W1 W2

/-- The Section 12 internal-direct-product package is symmetric in its two
factors. -/
public theorem CFSG.section12InternalDirectProduct_swap
    {G : Type u} [Group G]
    {W1 W2 W : Subgroup G}
    (hprod : section12InternalDirectProduct W1 W2 W) :
    section12InternalDirectProduct W2 W1 W := by
  rcases hprod with ⟨hW1le, hW2le, hW, hdisj, hcent⟩
  refine ⟨hW2le, hW1le, ?_, hdisj.symm, ?_⟩
  · simpa [sup_comm] using hW
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) x hx).symm

/-- The raw PF `(8.8)(b)` case package can be reoriented by swapping the two
cyclic factors and the two distinguished maximal subgroups. -/
public theorem CFSG.section8_caseBData_swap
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 S T SF TF) :
    Section8.theorem_8_8_case_b_data W W2 W1 T S TF SF := by
  rcases hcase with
    ⟨hprod, hcyc, hW1ne, hW2ne, hnorm, hSmax, hTmax, hSF, hTF,
      hSnotTypeI, hTnotTypeI, hSeq, hTeq, hSinf, hTinf, hSW2leSecond,
      hTW1leSecond, hST, hCover, hTypeII, hSType, hTType, hAligned⟩
  refine ⟨section12InternalDirectProduct_swap hprod, hcyc, hW2ne, hW1ne,
    ?_, hTmax, hSmax, hTF, hSF, hTnotTypeI, hSnotTypeI, hTeq, hSeq,
    hTinf, hSinf, hTW1leSecond, hSW2leSecond, ?_, ?_, ?_, hTType, hSType, ?_⟩
  · intro W0 hW0ne hW0sub
    exact hnorm W0 hW0ne (by
      intro x hx
      simpa [Set.union_comm] using hW0sub hx)
  · simpa [inf_comm] using hST
  · intro M hM
    rcases hCover M hM with hS | hT | hI
    · exact Or.inr (Or.inl hS)
    · exact Or.inl hT
    · exact Or.inr (Or.inr hI)
  · rcases hTypeII with hSII | hTII
    · exact Or.inr hSII
    · exact Or.inl hTII
  · rcases hAligned with ⟨U, V, hSCommon, hTCommon⟩
    exact ⟨V, U, hTCommon, hSCommon⟩

/-- In the raw PF `(8.8)(b)` case, the two cyclic direct-product factors cannot
have the same cardinality. The final PF13/PF14 route chooses the orientation
after this comparison. -/
public theorem CFSG.caseB_cardW1_ne_cardW2
    {G : Type u} [Group G] [Finite G]
    {W W1 W2 S T SF TF : Subgroup G}
    (hcase : Section8.theorem_8_8_case_b_data W W1 W2 S T SF TF) :
    Nat.card W1 ≠ Nat.card W2 := by
  rcases hcase with ⟨hprod, hcyc, _hW1ne, hW2ne, _⟩
  have hcop := natCard_coprime_of_section12InternalDirectProduct_cyclic hprod hcyc
  intro hEq
  have hW2gt : 1 < Nat.card W2 :=
    (Subgroup.one_lt_card_iff_ne_bot (H := W2)).2 hW2ne
  rw [hEq] at hcop
  exact (Nat.not_coprime_of_dvd_of_dvd hW2gt (dvd_refl _) (dvd_refl _)) hcop


/-- BG Section 16 supplies the final local-analysis alternative for a minimal
counterexample. -/
public theorem CFSG.bg16_final_alternative_of_isMinCE
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G) :
    bg16AllMaximalTypeI G ∨ bg16CaseBData G := by
  letI : IsMinCE G := hmin
  simpa [bg16AllMaximalTypeI, bg16CaseBData, Section8.theorem_8_8_case_b_data]
    using (theorem_16_I (G := G)).2

/-- A TI condition on the nonidentity elements of a set implies the same TI
condition on the whole set. -/
public theorem CFSG.section16TISubset_of_nonidentityElements
    {G : Type u} [Group G] [Finite G] {X : Set G}
    (h : section16TISubset (section16NonidentityElements X)) :
    section16TISubset X := by
  have hsharp_conj : ∀ g : G,
      section16NonidentityElements (section16ConjugateSet X g) =
        section16ConjugateSet (section16NonidentityElements X) g := by
    intro g
    ext z
    constructor
    · rintro ⟨hz, hz1⟩
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hx1
      apply hz1
      simp [hx1]
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      intro hconj_one
      apply hx1
      have := congrArg (fun t => g⁻¹ * t * g) hconj_one
      simpa [mul_assoc] using this
  intro g
  rcases h g with hconj | hdisj
  · left
    ext y
    constructor
    · intro hy
      by_cases hy1 : y = 1
      · rcases hy with ⟨x, hx, hxy⟩
        rw [hy1] at hxy
        have hx1 : x = 1 := by
          have := congrArg (fun t => g⁻¹ * t * g) hxy.symm
          simpa [mul_assoc] using this
        simpa [hy1, hx1] using hx
      · have hysharp : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hsharp_conj g] using hysharp
        have : y ∈ section16NonidentityElements X := by
          simpa [hconj] using this
        exact this.1
    · intro hy
      by_cases hy1 : y = 1
      · refine ⟨1, ?_, ?_⟩
        · simpa [← hy1] using hy
        · simp [hy1]
      · have : y ∈ section16NonidentityElements X := ⟨hy, hy1⟩
        have : y ∈ section16ConjugateSet (section16NonidentityElements X) g := by
          simpa [hconj] using this
        rcases this with ⟨x, hx, rfl⟩
        exact ⟨x, hx.1, rfl⟩
  · right
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · apply hdisj
      constructor
      · exact ⟨hy.1, hy1⟩
      · have : y ∈ section16NonidentityElements (section16ConjugateSet X g) :=
          ⟨hy.2, hy1⟩
        simpa [hsharp_conj g] using this

/-- The source common condition for PF Types II--IV supplies BG Section 16's
extra Type II--IV condition. -/
public theorem CFSG.section16TypeIIToIVExtra_of_sourceCondition
    {G : Type u} [Group G] [Finite G]
    {M U W1 : Subgroup G}
    (h : Section8.typeIIToIVSourceCondition M U W1) :
    section16TypeIIToIVExtra M W1 :=
  ⟨h.2.1, section16TISubset_of_nonidentityElements h.2.2⟩

/-- A complement relation inside an overgroup gives the corresponding local
complement relation on subgroups. -/
public theorem CFSG.section12ComplementIn_isComplement'_subgroupOf_for_final
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    [hHNormal : (H.subgroupOf M).Normal] :
    (K.subgroupOf M).IsComplement' (H.subgroupOf M) := by
  rcases hcomp with ⟨hHM, hKM, hsup, hdisj⟩
  have hsup_local : K.subgroupOf M ⊔ H.subgroupOf M = ⊤ := by
    calc
      K.subgroupOf M ⊔ H.subgroupOf M = (K ⊔ H).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := H) (B := M) hKM hHM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxK hxH
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxH,
      by simpa [Subgroup.mem_subgroupOf] using hxK⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (K.subgroupOf M) (H.subgroupOf M)).symm

/-- In a complement decomposition, if the complement is Hall then the other
factor is Hall for its own prime set. -/
public theorem CFSG.section12ComplementIn_left_isHall_of_right_hall_for_final
    {G : Type u} [Group G] [Finite G]
    {M H K : Subgroup G}
    (hcomp : section12ComplementIn M H K)
    (hHnormal : (H.subgroupOf M).Normal)
    (hKHall : section16HallSubgroupOf K M) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) := by
  classical
  letI : (H.subgroupOf M).Normal := hHnormal
  have hcomp' : (K.subgroupOf M).IsComplement' (H.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := H) (K := K) hcomp
  rcases hcomp with ⟨hHM, _hKM, _hsup, _hdisj⟩
  rcases hKHall with ⟨_hKM, hKHallSub⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet H)
    (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
      natCard_subgroupOf_eq H M hHM
    simpa [subgroupPrimeSet, hcardH] using hpH
  · intro p hpH hpidxH
    have hpKcard : p.val ∣ Nat.card (K.subgroupOf M) := by
      simpa [hcomp'.index_eq_card] using hpidxH
    have hpKπ : p ∈ subgroupPrimeSet K :=
      hKHallSub.p_in_pi_of_p_dvd_card p hpKcard
    have hpHcard : p.val ∣ Nat.card (H.subgroupOf M) := by
      have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
        natCard_subgroupOf_eq H M hHM
      simpa [subgroupPrimeSet, hcardH] using hpH
    have hpKidx : p.val ∣ (K.subgroupOf M).index := by
      simpa [hcomp'.symm.index_eq_card] using hpHcard
    exact (hKHallSub.p_in_pi_of_p_dvd_index p hpKidx) hpKπ

/-- Restrict a Hall subgroup in an ambient subgroup to an intermediate
overgroup. -/
public theorem CFSG.section12HallSubgroupIn_of_le_overgroup_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {K E M : Subgroup G}
    (hHall : section12HallSubgroupIn π K M)
    (hKE : K ≤ E) (hEM : E ≤ M) :
    section12HallSubgroupIn π K E := by
  classical
  rcases hHall with ⟨_hKM, hHallM⟩
  refine ⟨hKE, ?_⟩
  refine isHallSubgroup_of (G := E) (π := π) (H := K.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (K.subgroupOf E) = Nat.card K :=
      natCard_subgroupOf_eq K E hKE
    have hcardM : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M (hKE.trans hEM)
    exact hHallM.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardM] using hp)
  · intro p hpπ hpidx
    let EsubM : Subgroup M := E.subgroupOf M
    have hKsub_le_Esub : K.subgroupOf M ≤ EsubM := by
      intro x hx
      exact hKE hx
    have hrel_eq :
        (K.subgroupOf E).index = (K.subgroupOf M).relIndex EsubM := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := K) (K := E) (L := M) hEM
      simpa [EsubM, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (K.subgroupOf E).index ∣ (K.subgroupOf M).index := by
      have hrel_dvd :
          (K.subgroupOf M).relIndex EsubM ∣ (K.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hKsub_le_Esub
      simpa [hrel_eq] using hrel_dvd
    exact (hHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

/-- Transfer a Hall-in-`M` field across subgroups of equal cardinality. -/
public theorem CFSG.section12HallSubgroupIn_of_natCard_eq_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {H K M : Subgroup G}
    (hKHall : section12HallSubgroupIn π K M)
    (hHM : H ≤ M)
    (hcard : Nat.card H = Nat.card K) :
    section12HallSubgroupIn π H M := by
  classical
  rcases hKHall with ⟨hKM, hKHallSub⟩
  refine ⟨hHM, ?_⟩
  have hcardHsub : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHM
  have hcardKsub : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKM
  have hcardSub : Nat.card (H.subgroupOf M) = Nat.card (K.subgroupOf M) := by
    rw [hcardHsub, hcardKsub, hcard]
  have hidxEq : (H.subgroupOf M).index = (K.subgroupOf M).index := by
    have hmulH :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := H.subgroupOf M)
    have hmulK :
        (K.subgroupOf M).index * Nat.card (K.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := K.subgroupOf M)
    have hmul :
        (H.subgroupOf M).index * Nat.card (H.subgroupOf M) =
          (K.subgroupOf M).index * Nat.card (K.subgroupOf M) :=
      hmulH.trans hmulK.symm
    rw [hcardSub] at hmul
    exact Nat.mul_right_cancel (Nat.card_pos (α := K.subgroupOf M)) hmul
  refine isHallSubgroup_of (G := M) (π := π) (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    exact hKHallSub.p_in_pi_of_p_dvd_card p (by
      simpa [hcardSub] using hpH)
  · intro p hpπ hpidx
    exact (hKHallSub.p_in_pi_of_p_dvd_index p (by
      simpa [hidxEq] using hpidx)) hpπ

/-- A nontrivial finite subgroup contains a subgroup of prime order. -/
public theorem CFSG.section12_exists_primeOrderSubgroup_of_ne_bot_for_final
    {G : Type u} [Group G] [Finite G]
    {H : Subgroup G}
    (hHne : H ≠ ⊥) :
    ∃ X : Subgroup G, X ∈ section12PrimeOrderSubgroups H := by
  classical
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdiv⟩
  haveI : Fact p.Prime := ⟨hpprime⟩
  rcases exists_prime_orderOf_dvd_card' (G := H) p hpdiv with ⟨zH, hzH_order⟩
  let z : G := zH
  refine ⟨Subgroup.zpowers z, ?_⟩
  have hzH : z ∈ H := zH.property
  have hz_order : orderOf z = p := by
    simpa [z, Subgroup.orderOf_coe] using hzH_order
  refine ⟨Subgroup.zpowers_le.mpr hzH, ⟨⟨p, hpprime⟩, ?_⟩⟩
  simp [z, Nat.card_zpowers, hz_order]

/-- A Sylow subgroup of a Hall subgroup is also a Sylow subgroup of the
ambient group. -/
public theorem CFSG.isHallSubgroup_sylow_map_to_overgroup_sylow_for_final
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

/-- If one Sylow `p`-subgroup is cyclic, then the `p`-rank is at most one. -/
public theorem CFSG.primeRank_le_one_of_cyclic_sylow_for_final
    {p : ℕ} {R : Type*} [Group R] [Finite R] [Fact p.Prime]
    (S : Sylow p R) (hS_cyc : IsCyclic (S : Subgroup R)) :
    primeRank p R ≤ 1 := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · letI : IsCyclic (S : Subgroup R) := hS_cyc
    refine ⟨0, ?_⟩
    exact ⟨(S : Subgroup R), S.isPGroup', inferInstance, by simp⟩
  · intro n hn
    rcases hn with ⟨A, hAp, _hAcomm, hnA⟩
    obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S T
    have hT_cyc : IsCyclic (T : Subgroup R) := by
      let e :
          (S : Subgroup R) ≃* ((g • S : Sylow p R) : Subgroup R) :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj g).toMonoidHom) (S : Subgroup R)
          (EquivLike.injective (MulAut.conj g))
      have hconj_cyc : IsCyclic (((g • S : Sylow p R) : Subgroup R)) :=
        e.isCyclic.mp hS_cyc
      rw [← hg]
      exact hconj_cyc
    have hA_cyc : IsCyclic A := Subgroup.isCyclic_of_le hA_le_T
    exact hnA.trans (generatorRank_le_one_of_isCyclic (G := A) hA_cyc)

/-- A cyclic Hall subgroup forces every prime in its Hall set to have rank at
most one in the ambient group. -/
public theorem CFSG.primeRank_le_one_of_cyclic_hall_subgroup_for_final
    {R : Type*} [Group R] [Finite R]
    {π : Set Nat.Primes} {K : Subgroup R} {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K)
    (hpπ : p ∈ π)
    (hKcyc : IsCyclic K) :
    primeRank p.val R ≤ 1 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PK : Sylow p.val K := Classical.choice (Sylow.nonempty (p := p.val) (G := K))
  rcases isHallSubgroup_sylow_map_to_overgroup_sylow_for_final
      (H := R) (K := K) hKHall hpπ PK with
    ⟨PR, hPReq⟩
  have hPKcyclic : IsCyclic (PK : Subgroup K) := by
    letI : IsCyclic K := hKcyc
    exact Subgroup.isCyclic_of_le (show (PK : Subgroup K) ≤ ⊤ from le_top)
  let Pmap : Subgroup R := (PK : Subgroup K).map K.subtype
  have hPmapCyclic : IsCyclic Pmap := by
    let e :
        (PK : Subgroup K) ≃* Pmap :=
      Subgroup.equivMapOfInjective
        (f := K.subtype) (PK : Subgroup K) K.subtype_injective
    exact e.isCyclic.mp hPKcyclic
  have hPRcyclic : IsCyclic (PR : Subgroup R) := by
    rw [hPReq]
    simpa [Pmap] using hPmapCyclic
  exact primeRank_le_one_of_cyclic_sylow_for_final PR hPRcyclic

/-- Two complements to the same normal subgroup have equal cardinality. -/
public theorem CFSG.natCard_eq_of_section12ComplementIn_same_normal_left_for_final
    {G : Type u} [Group G] [Finite G]
    {M D H K : Subgroup G}
    (hDnormal : (D.subgroupOf M).Normal)
    (hHcomp : section12ComplementIn M D H)
    (hKcomp : section12ComplementIn M K D) :
    Nat.card H = Nat.card K := by
  classical
  letI : (D.subgroupOf M).Normal := hDnormal
  have hKcompSymm : section12ComplementIn M D K := by
    refine ⟨hKcomp.2.1, hKcomp.1, ?_, hKcomp.2.2.2.symm⟩
    rw [sup_comm]
    exact hKcomp.2.2.1
  have hHlocal : (H.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := D) (K := H) hHcomp
  have hKlocal : (K.subgroupOf M).IsComplement' (D.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := D) (K := K) hKcompSymm
  have hDindexH : (D.subgroupOf M).index = Nat.card (H.subgroupOf M) :=
    hHlocal.index_eq_card
  have hDindexK : (D.subgroupOf M).index = Nat.card (K.subgroupOf M) :=
    hKlocal.index_eq_card
  have hHcard : Nat.card (H.subgroupOf M) = Nat.card H :=
    natCard_subgroupOf_eq H M hHcomp.2.1
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKcomp.1
  calc
    Nat.card H = Nat.card (H.subgroupOf M) := hHcard.symm
    _ = (D.subgroupOf M).index := hDindexH.symm
    _ = Nat.card (K.subgroupOf M) := hDindexK
    _ = Nat.card K := hKcard

/-- In a complement decomposition, if the left factor is Hall for `π` and the
right factor is normal, then the right factor is Hall for `πᶜ`. -/
public theorem CFSG.section12ComplementIn_right_isHall_compl_of_left_hall_for_final
    {G : Type u} [Group G] [Finite G]
    {π : Set Nat.Primes} {R K U : Subgroup G}
    (hcomp : section12ComplementIn R K U)
    (hUnormal : section10NormalIn U R)
    (hKHall : section12HallSubgroupIn π K R) :
    section12HallSubgroupIn πᶜ U R := by
  classical
  rcases hcomp with ⟨hKR, hUR, hsup, hdisj⟩
  rcases hKHall with ⟨_hKR', hKHallSub⟩
  have hcompSymm : section12ComplementIn R U K := by
    refine ⟨hUR, hKR, ?_, hdisj.symm⟩
    calc
      R = K ⊔ U := hsup
      _ = U ⊔ K := sup_comm K U
  letI : (U.subgroupOf R).Normal := hUnormal.2
  have hcompLocal : (K.subgroupOf R).IsComplement' (U.subgroupOf R) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := R) (H := U) (K := K) hcompSymm
  refine ⟨hUR, ?_⟩
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := U.subgroupOf R) ?_ ?_
  · intro q hqU hqπ
    have hqKidx : q.val ∣ (K.subgroupOf R).index := by
      simpa [hcompLocal.symm.index_eq_card] using hqU
    exact (hKHallSub.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqUidx
    have hqK : q.val ∣ Nat.card (K.subgroupOf R) := by
      simpa [hcompLocal.index_eq_card] using hqUidx
    exact hqπc (hKHallSub.p_in_pi_of_p_dvd_card q hqK)

/-- Source-facing Type-P data supplies the BG Section 16 common package once
the remaining BG T6 condition is available. -/
public theorem CFSG.section16TypeCommon_of_source_typeP_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : Section8.typePDefinitionData M MF U W1 W2)
    (hT6 : ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeCommon M MF U W1 W2 := by
  rcases hP with
    ⟨_hMF, hW1cyc, _hW1ne, hW1Hall, hMcomp, hUle, hUnil, hW1norm,
      hDercomp, hMFnotcyc, hSecond, hFit, hFitDer, hW2leInf, hW2cyc,
      hW2ne, hCent, hNorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hDHall : section16HallSubgroupOf (ambientDerivedSubgroup M) M := by
    refine ⟨section12_ambientDerivedSubgroup_le (G := G) (E := M), ?_⟩
    exact section12ComplementIn_left_isHall_of_right_hall_for_final
      (M := M) (H := ambientDerivedSubgroup M) (K := W1)
      hMcomp hDnormal hW1Hall
  have hW1card : Nat.card W1 = (ambientDerivedSubgroup M).relIndex M := by
    letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
    have hcomp' : (W1.subgroupOf M).IsComplement'
        ((ambientDerivedSubgroup M).subgroupOf M) :=
      section12ComplementIn_isComplement'_subgroupOf_for_final
        (M := M) (H := ambientDerivedSubgroup M) (K := W1) hMcomp
    have hW1subcard : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
      natCard_subgroupOf_eq W1 M hMcomp.2.1
    have hidx : ((ambientDerivedSubgroup M).subgroupOf M).index =
        Nat.card (W1.subgroupOf M) := hcomp'.index_eq_card
    simpa [Subgroup.relIndex, hW1subcard] using hidx.symm
  have hW2le : W2 ≤ MF := hW2leInf.trans inf_le_left
  exact ⟨hDHall, hDercomp.1, hDercomp, hUnil, hW1norm, hW1cyc, hW1card,
    hMFnotcyc, hSecond, hFit.symm, hFitDer, hW2le, hW2ne, hW2cyc, hCent, hNorm,
    ⟨hT6, hW2leInf.trans inf_le_right⟩⟩

/-- Source Type III data becomes BG Type III data when the missing BG T6 field
is supplied. -/
public theorem CFSG.section16TypeIII_of_source_typeIII_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : Section8.typeIIIDefinitionData M MF)
    (hT6 : ∀ {U W1 W2 : Subgroup G},
      Section8.typePDefinitionData M MF U W1 W2 →
        ∀ A0 A1 : Subgroup G,
          section16PrimeOrderSubgroupOf A0 U →
            section16PrimeOrderSubgroupOf A1 U →
              section16ConjugateSubgroupsIn ⊤ A0 A1 →
                ¬ section16ConjugateSubgroupsIn M A0 A1 →
                  subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeIII M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hcomm, hnorm⟩
  exact ⟨U, W1, W2, section16TypeCommon_of_source_typeP_with_T6 hP (hT6 hP),
    section16TypeIIToIVExtra_of_sourceCondition hExtra, hcomm, hnorm⟩

/-- Source Type IV data becomes BG Type IV data when the missing BG T6 field is
supplied. -/
public theorem CFSG.section16TypeIV_of_source_typeIV_with_T6
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (h : Section8.typeIVDefinitionData M MF)
    (hT6 : ∀ {U W1 W2 : Subgroup G},
      Section8.typePDefinitionData M MF U W1 W2 →
        ∀ A0 A1 : Subgroup G,
          section16PrimeOrderSubgroupOf A0 U →
            section16PrimeOrderSubgroupOf A1 U →
              section16ConjugateSubgroupsIn ⊤ A0 A1 →
                ¬ section16ConjugateSubgroupsIn M A0 A1 →
                  subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeIV M MF := by
  rcases h with ⟨U, W1, W2, hP, hExtra, hncomm, hnorm⟩
  exact ⟨U, W1, W2, section16TypeCommon_of_source_typeP_with_T6 hP (hT6 hP),
    section16TypeIIToIVExtra_of_sourceCondition hExtra, hncomm, hnorm⟩


/-- If the source Type-P subgroup `U` is trivial, the BG T6 condition is
vacuous: no subgroup of `U` has prime order. -/
public theorem CFSG.source_typeP_T6_of_U_eq_bot
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hUbot : U = ⊥) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  intro A0 _A1 hA0 _hA1 _hConj _hNotM
  rcases hA0.2 with ⟨p, hcard⟩
  have hA0bot : A0 = ⊥ := by
    rw [hUbot] at hA0
    exact le_bot_iff.mp hA0.1
  rw [hA0bot] at hcard
  have hpone : p.val = 1 := by
    simpa using hcard.symm
  exact False.elim (p.property.ne_one hpone)

/-- In the source Type-P branch with `U` not contained in `M_sigma`, the
recorded nilpotent Hall subgroup `M_F` must be exactly `M_sigma`.

If `M_F` were properly smaller, Theorem 15.2(d) identifies
`M_sigma = M'`; the source Type-P containment `U ≤ M'` would then put `U`
inside `M_sigma`, contradicting the branch hypothesis. -/
public theorem CFSG.source_typeP_MF_eq_msigma_of_not_le_msigma
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    MF = section10Msigma M := by
  letI : IsMinCE G := hmin
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hMF15 : section15MFSubgroup M MF := by
    simpa [section16MFSubgroup, section16NilpotentNormalHallIn,
      section15MFSubgroup, section15NilpotentNormalHallIn] using hMF
  by_contra hMFne
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U0, hKU⟩
  rcases theorem_15_2_c (G := G) (M := M) (MF := MF) (K := K)
      hM hMF15 hKU.1 hMFne with
    ⟨q, hq, Q, hQ, hQnormal, hQMF⟩
  rcases theorem_15_2_d (G := G) (M := M) (MF := MF) (K := K)
      (Q := Q) hM hMF15 hKU.1 hMFne hq hQ hQnormal hQMF with
    ⟨D0, hD0⟩
  have hUσ : U ≤ section10Msigma M := by
    intro x hx
    simpa [hD0.1] using hUleD hx
  exact hUnotσ hUσ

/-- Once source Type-P data has been reduced to `M_F = M_sigma`, the
complement and normality fields in the candidate `KUData` package with
`K = W1` are formal consequences of the recorded source complements. -/
public theorem CFSG.source_typeP_W1_KUData_structural_fields
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section12ComplementIn M W1 (U ⊔ section10Msigma M) ∧
      section12ComplementIn M (section10Msigma M) (W1 ⊔ U) ∧
      section10NormalIn (U ⊔ section10Msigma M) M ∧
      section10NormalIn U (W1 ⊔ U) := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hD_eq : ambientDerivedSubgroup M = MF ⊔ U := hDercomp.2.2.1
  have hD_eq_sigma : ambientDerivedSubgroup M = section10Msigma M ⊔ U := by
    simpa [hMFeq] using hD_eq
  have hD_eq_USigma : ambientDerivedSubgroup M = U ⊔ section10Msigma M := by
    calc
      ambientDerivedSubgroup M = MF ⊔ U := hD_eq
      _ = section10Msigma M ⊔ U := by rw [hMFeq]
      _ = U ⊔ section10Msigma M := sup_comm (section10Msigma M) U
  rcases hMcomp with ⟨hDM, hW1M, hM_eq, hD_W1_disj⟩
  rcases hDercomp with ⟨hMFD, hUD, _hD_eq', hMF_U_disj⟩
  have hSigmaM : section10Msigma M ≤ M := by
    intro x hx
    exact hDM (by simpa [hMFeq] using hMFD (by simpa [hMFeq] using hx))
  have hW1U_M : W1 ⊔ U ≤ M :=
    sup_le hW1M (hUD.trans hDM)
  have hW1_norm_U : W1 ≤ Subgroup.normalizer (U : Set G) := by
    intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  have hcompW1USigma : section12ComplementIn M W1 (U ⊔ section10Msigma M) := by
    refine ⟨hW1M, ?_, ?_, ?_⟩
    · rw [← hD_eq_USigma]
      exact hDM
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = W1 ⊔ ambientDerivedSubgroup M := sup_comm (ambientDerivedSubgroup M) W1
        _ = W1 ⊔ (U ⊔ section10Msigma M) := by rw [← hD_eq_USigma]
    · rw [← hD_eq_USigma]
      exact hD_W1_disj.symm
  have hcompSigmaW1U : section12ComplementIn M (section10Msigma M) (W1 ⊔ U) := by
    refine ⟨hSigmaM, hW1U_M, ?_, ?_⟩
    · calc
        M = ambientDerivedSubgroup M ⊔ W1 := hM_eq
        _ = (section10Msigma M ⊔ U) ⊔ W1 := by rw [hD_eq_sigma]
        _ = section10Msigma M ⊔ (W1 ⊔ U) := by
          simp [sup_comm, sup_left_comm]
    · rw [Subgroup.disjoint_def]
      intro x hxSigma hxW1U
      have hW1U_mul :
          ((W1 ⊔ U : Subgroup G) : Set G) = (W1 : Set G) * (U : Set G) := by
        exact Subgroup.coe_mul_of_left_le_normalizer_right
          (H := W1) (N := U) hW1_norm_U
      have hxW1Uset : x ∈ ((W1 ⊔ U : Subgroup G) : Set G) := hxW1U
      rw [hW1U_mul, Set.mem_mul] at hxW1Uset
      rcases hxW1Uset with ⟨w, hwW1, u, huU, hwu⟩
      have hxD : x ∈ ambientDerivedSubgroup M := by
        simpa [hMFeq] using hMFD (by simpa [hMFeq] using hxSigma)
      have hwD : w ∈ ambientDerivedSubgroup M := by
        have hw_eq : w = x * u⁻¹ := by
          rw [← hwu]
          simp [mul_assoc]
        rw [hw_eq]
        exact (ambientDerivedSubgroup M).mul_mem hxD (hUD (U.inv_mem huU))
      have hw_bot : w ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hD_W1_disj hwD hwW1
      have hw_one : w = 1 := by
        simpa using hw_bot
      have hxU : x ∈ U := by
        have hx_eq : x = u := by
          simpa [hw_one] using hwu.symm
        simpa [hx_eq] using huU
      have hxMF : x ∈ MF := by
        simpa [hMFeq] using hxSigma
      exact Subgroup.disjoint_def.mp hMF_U_disj hxMF hxU
  have hUSigmaNormal : section10NormalIn (U ⊔ section10Msigma M) M := by
    have hnormD : section10NormalIn (ambientDerivedSubgroup M) M :=
      section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)
    simpa [← hD_eq_USigma] using hnormD
  have hUnormal : section10NormalIn U (W1 ⊔ U) := by
    refine ⟨le_sup_right, ?_⟩
    simpa using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := W1) (N := U) hW1_norm_U)
  exact ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩

/-- The source Type-P centralizer field makes the action of `W1` on `U`
regular: a nontrivial element of `W1` has centralizer `W2` in `M'`, and
`W2 ≤ MF` is disjoint from the complement `U`. -/
public theorem CFSG.source_typeP_W1_actsRegularlyOn_U
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section14ActsRegularlyOn W1 U := by
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, hW1norm, hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, _hW2ne, hCent, _hNorm⟩
  rcases hDercomp with ⟨_hMFD, hUD, _hD_eq, hMF_U_disj⟩
  refine ⟨?_, ?_⟩
  · intro w hw
    exact (mem_subgroupNormalizerIn.mp (hW1norm hw)).1
  · intro x hxW1 hxne
    apply le_antisymm
    · intro y hy
      have hyU : y ∈ U := hy.1
      have hyD : y ∈ ambientDerivedSubgroup M := hUD hyU
      have hycent : y ∈ Subgroup.centralizer ({x} : Set G) := hy.2
      have hyDcent :
          y ∈ elementCentralizerIn (ambientDerivedSubgroup M) x := ⟨hyD, hycent⟩
      have hyW2 : y ∈ W2 := by
        simpa [hCent x hxW1 hxne] using hyDcent
      have hyMF : y ∈ MF := (hW2leInf hyW2).1
      have hybot : y ∈ (⊥ : Subgroup G) :=
        Subgroup.disjoint_def.mp hMF_U_disj hyMF hyU
      simpa using hybot
    · exact bot_le

/-- Once `W1` is known to be the Hall `kappa(M)` subgroup, the source
complement decompositions force the same source `U` to be Hall away from
`kappa(M) ∪ sigma(M)`.

The proof first views `E = W1 ⊔ U` as the sigma-complement in `M`; then `U`
is the normal complement to the Hall `kappa(M)` subgroup inside `E`. -/
public theorem CFSG.source_typeP_U_hall_from_W1_kappa_hall
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M) :
    section12HallSubgroupIn ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ)
      U M := by
  classical
  let E : Subgroup G := W1 ⊔ U
  rcases source_typeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, _hUSigmaNormal, hUnormal⟩
  have hEM : E ≤ M := by
    simpa [E] using hcompSigmaW1U.2.1
  have hUE : U ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_right : U ≤ W1 ⊔ U) hx)
  have hW1E : W1 ≤ E := by
    intro x hx
    exact (show x ∈ W1 ⊔ U from (le_sup_left : W1 ≤ W1 ⊔ U) hx)
  have hW1HallE : section12HallSubgroupIn (section14KappaPrimes M) W1 E :=
    section12HallSubgroupIn_of_le_overgroup_for_final hW1Hallκ hW1E hEM
  have hW1Udisj : Disjoint W1 U := by
    rw [Subgroup.disjoint_def]
    intro x hxW1 hxU
    exact Subgroup.disjoint_def.mp hcompW1USigma.2.2.2 hxW1
      (show x ∈ U ⊔ section10Msigma M from
        (le_sup_left : U ≤ U ⊔ section10Msigma M) hxU)
  have hcompW1U : section12ComplementIn E W1 U := by
    refine ⟨hW1E, hUE, ?_, hW1Udisj⟩
    simp [E]
  have hUnormalE : section10NormalIn U E := by
    simpa [E] using hUnormal
  have hUHallE : section12HallSubgroupIn (section14KappaPrimes M)ᶜ U E :=
    section12ComplementIn_right_isHall_compl_of_left_hall_for_final
      hcompW1U hUnormalE hW1HallE
  have hEHallM : section12HallSubgroupIn (section10SigmaPrimes M)ᶜ E M := by
    refine ⟨hEM, ?_⟩
    simpa [E] using
      (section12_msigma_complement_isHall_sigma_compl (G := G) hM hcompSigmaW1U)
  have hUM : U ≤ M := hUE.trans hEM
  refine ⟨hUM, ?_⟩
  refine isHallSubgroup_of (G := M)
    (π := ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ))
    (H := U.subgroupOf M) ?_ ?_
  · intro p hpUsub
    have hcardUM : Nat.card (U.subgroupOf M) = Nat.card U :=
      natCard_subgroupOf_eq U M hUM
    have hpU : p.val ∣ Nat.card U := by
      simpa [hcardUM] using hpUsub
    have hcardUE : Nat.card (U.subgroupOf E) = Nat.card U :=
      natCard_subgroupOf_eq U E hUE
    have hpUE : p.val ∣ Nat.card (U.subgroupOf E) := by
      simpa [hcardUE] using hpU
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ :=
      hUHallE.2.p_in_pi_of_p_dvd_card p hpUE
    have hpE : p.val ∣ Nat.card E := hpU.trans (Subgroup.card_dvd_of_le hUE)
    have hcardEM : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hEM
    have hpEM : p.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcardEM] using hpE
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ :=
      hEHallM.2.p_in_pi_of_p_dvd_card p hpEM
    rw [Set.mem_compl_iff, Set.mem_union]
    intro hpκσ
    exact hpκσ.elim hpκc hpσc
  · intro p hpπ hpidx
    have hpκc : p ∈ (section14KappaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpκ
      exact hpπ (Or.inl hpκ)
    have hpσc : p ∈ (section10SigmaPrimes M)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hpσ
      exact hpπ (Or.inr hpσ)
    change p.val ∣ U.relIndex M at hpidx
    have hmul : U.relIndex E * E.relIndex M = U.relIndex M :=
      Subgroup.relIndex_mul_relIndex U E M hUE hEM
    have hprod : p.val ∣ U.relIndex E * E.relIndex M := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidxUE | hpidxEM
    · exact (hUHallE.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxUE)) hpκc
    · exact (hEHallM.2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidxEM)) hpσc

/-- A prime-order subgroup of the source Type-P complement `W1` has prime in
`τ₁(M) ∪ τ₃(M)`. -/
public theorem CFSG.source_typeP_tau13_of_W1_prime_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  letI : IsMinCE G := hmin
  rcases hsourceP with
    ⟨_hMFsource, hW1cyc, _hW1ne, hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, hW1HallSub⟩
  rcases hX with ⟨hXW1, hXcard⟩
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpM : p.val ∣ Nat.card M := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXM)
  have hpW1 : p.val ∣ Nat.card W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  have hpW1π : p ∈ subgroupPrimeSet W1 := by
    simpa [subgroupPrimeSet] using hpW1
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : ((ambientDerivedSubgroup M).subgroupOf M).Normal := hDnormal
  have hCompLocal : (W1.subgroupOf M).IsComplement'
      ((ambientDerivedSubgroup M).subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf_for_final
      (M := M) (H := ambientDerivedSubgroup M) (K := W1) hMcomp
  have hpNotSigma : p ∉ section10SigmaPrimes M := by
    intro hpSigma
    have hSigmaHallM :
        IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
      (theorem_10_2_b (G := G) hM).2
    have hpSigmaSub : p.val ∣ Nat.card (section10MsigmaSubgroup M) := by
      have hprod :
          (section10MsigmaSubgroup M).index * Nat.card (section10MsigmaSubgroup M) =
            Nat.card M :=
        Subgroup.index_mul_card (H := section10MsigmaSubgroup M)
      have hpProd :
          p.val ∣ (section10MsigmaSubgroup M).index *
              Nat.card (section10MsigmaSubgroup M) := by
        simpa [hprod] using hpM
      by_contra hpNotCard
      have hpNotIndex : ¬ p.val ∣ (section10MsigmaSubgroup M).index :=
        fun hpidx => (hSigmaHallM.p_in_pi_of_p_dvd_index p hpidx) hpSigma
      exact (Nat.Prime.not_dvd_mul p.property hpNotIndex hpNotCard) hpProd
    have hMsigmaLeM : section10Msigma M ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hpSigmaSubgroupOf :
        p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
      simpa [section12Msigma_subgroupOf_eq (G := G) (M := M)] using hpSigmaSub
    have hpSigmaAmb : p.val ∣ Nat.card (section10Msigma M) := by
      have hcard :
          Nat.card ((section10Msigma M).subgroupOf M) = Nat.card (section10Msigma M) :=
        natCard_subgroupOf_eq (section10Msigma M) M hMsigmaLeM
      simpa [hcard] using hpSigmaSubgroupOf
    have hMsigmaLeDer : section10Msigma M ≤ ambientDerivedSubgroup M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨y, (theorem_10_2_c (G := G) hM).2 hy, rfl⟩
    have hpDcard : p.val ∣ Nat.card (ambientDerivedSubgroup M) :=
      hpSigmaAmb.trans (Subgroup.card_dvd_of_le hMsigmaLeDer)
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (G := G) (E := M)
    have hpDsub : p.val ∣ Nat.card ((ambientDerivedSubgroup M).subgroupOf M) := by
      have hcard :
          Nat.card ((ambientDerivedSubgroup M).subgroupOf M) =
            Nat.card (ambientDerivedSubgroup M) :=
        natCard_subgroupOf_eq (ambientDerivedSubgroup M) M hDleM
      simpa [hcard] using hpDcard
    have hpW1idx : p.val ∣ (W1.subgroupOf M).index := by
      simpa [hCompLocal.symm.index_eq_card] using hpDsub
    exact (hW1HallSub.p_in_pi_of_p_dvd_index p hpW1idx) hpW1π
  have hW1subCyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.2 hW1cyc
  have hRankLe : primeRank p.val M ≤ 1 :=
    primeRank_le_one_of_cyclic_hall_subgroup_for_final
      (R := M) (π := subgroupPrimeSet W1) (K := W1.subgroupOf M)
      hW1HallSub hpW1π hW1subCyclic
  have hRankPos : 0 < primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hRank : primeRank p.val M = 1 := by omega
  by_cases hpDer : p ∈ subgroupPrimeSet (derivedSubgroup M)
  · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hpNotSigma, hpDer, hRank⟩)
  · exact Or.inl (by simpa [section12Tau1Primes] using ⟨hpNotSigma, hpDer, hRank⟩)

/-- The source Type-P centralizer field gives a nontrivial centralizer in
`M_sigma` for every prime-order subgroup of `W1`, once `MF = M_sigma`. -/
public theorem CFSG.source_typeP_msigma_centralizer_ne_bot_of_W1_prime_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
  classical
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, hW2leInf, _hW2cyc, hW2ne, hCent, _hNorm⟩
  rcases hX with ⟨hXW1, _hXcard⟩
  haveI : Nontrivial W2 := (Subgroup.nontrivial_iff_ne_bot W2).2 hW2ne
  obtain ⟨yW2, hyW2ne⟩ := exists_ne (1 : W2)
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMsigma : y ∈ section10Msigma M := by
    have hyMF : y ∈ MF := (hW2leInf hyW2).1
    simpa [hMFeq] using hyMF
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMsigma, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hzX
    by_cases hz : z = 1
    · subst hz
      simp
    · have hzW1 : z ∈ W1 := hXW1 hzX
      have hyCentZ : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) z := by
        simpa [hCent z hzW1 hz] using hyW2
      have hcomm : Commute y z :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentZ.2
      exact hcomm.eq.symm
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, hyCentX⟩, ?_⟩
  intro hybot
  exact hyne (by simpa using congrArg Subtype.val hybot)

/-- Source Type-P data with `MF = M_sigma` places the maximal subgroup in
Section 14's family `𝓜_P`. -/
public theorem CFSG.source_typeP_MFamilyP_of_msigma_eq_for_final
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    M ∈ section14MFamilyP G := by
  classical
  have hsourceP' : Section8.typePDefinitionData M MF U W1 W2 := hsourceP
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, hW1ne, hW1Hall, _hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  rcases hW1Hall with ⟨hW1M, _hW1HallSub⟩
  rcases section12_exists_primeOrderSubgroup_of_ne_bot_for_final
      (G := G) hW1ne with
    ⟨X, hXprime⟩
  rcases hXprime with ⟨hXW1, p, hXcard⟩
  have hXprimeW1 : X ∈ section10PrimeOrderSubgroupsIn p W1 := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXW1, hXcard⟩
  have hTau13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    source_typeP_tau13_of_W1_prime_for_final
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hmin hM hsourceP' hXprimeW1
  have hCent :
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ :=
    source_typeP_msigma_centralizer_ne_bot_of_W1_prime_for_final
      (G := G) (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hMFeq hsourceP' hXprimeW1
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpκ : p ∈ section14KappaPrimes M := by
    exact ⟨hTau13, X, ⟨hXM, hXcard⟩, hCent⟩
  exact ⟨hM, ⟨p, hpκ⟩⟩

/-- The remaining source-specific field needed to upgrade the source Type-P
pair `(W1, U)` to a Section 16 `KUData` package after `MF = M_sigma` is known.

The structural complement and normality fields are handled separately by
`source_typeP_W1_KUData_structural_fields`, the regular action is handled
by `source_typeP_W1_actsRegularlyOn_U`, and the `U` Hall-away field follows
from `source_typeP_U_hall_from_W1_kappa_hall` once this core supplies the
source/BG identification of `W1` as the Hall `kappa(M)` subgroup. -/
public theorem CFSG.source_typeP_W1_KUData_hard_fields_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section16MFSubgroup M MF)
    (_hUne : U ≠ ⊥)
    (_hUnotσ : ¬ U ≤ section10Msigma M)
    (hMFeq : MF = section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    section12HallSubgroupIn (section14KappaPrimes M) W1 M := by
  classical
  letI : IsMinCE G := hmin
  have hMP : M ∈ section14MFamilyP G :=
    source_typeP_MFamilyP_of_msigma_eq_for_final hmin hM hMFeq hsourceP
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U0, hKU⟩
  have hKHall : section12HallSubgroupIn (section14KappaPrimes M) K M := hKU.1
  have hKcomp : section12ComplementIn M K (ambientDerivedSubgroup M) :=
    theorem_14_7_h (G := G) (M := M) (K := K) hMP hKHall
  rcases hsourceP with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD,
      _hUnil, _hW1norm, _hDercomp, _hMFnotcyc, _hSecond, _hFit,
      _hFitDer, _hW2leInf, _hW2cyc, _hW2ne, _hCent, _hNorm⟩
  have hDnormal : ((ambientDerivedSubgroup M).subgroupOf M).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hcard : Nat.card W1 = Nat.card K :=
    natCard_eq_of_section12ComplementIn_same_normal_left_for_final
      (G := G) (M := M) (D := ambientDerivedSubgroup M) (H := W1) (K := K)
      hDnormal hMcomp hKcomp
  exact section12HallSubgroupIn_of_natCard_eq_for_final hKHall hMcomp.2.1 hcard

/-- Source Type-P data in the non-`M_sigma` branch supplies some Section 16
`KUData` complement for the same source subgroup `U`.

This is the exact remaining source/BG bridge needed for the Type-P T6 branch;
the final all-Type-I exclusion does not require identifying the source pair
`(W1, U)` with a prescribed Proposition 14.2(a) pair. -/
public theorem CFSG.source_typeP_exists_KUData_of_not_le_msigma_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∃ K : Subgroup G, section16KUData M K U := by
  have hMFeq : MF = section10Msigma M :=
    source_typeP_MF_eq_msigma_of_not_le_msigma hmin hM hMF hUnotσ hsourceP
  have hW1Hallκ : section12HallSubgroupIn (section14KappaPrimes M) W1 M :=
    source_typeP_W1_KUData_hard_fields_core
      hmin hM hMF hUne hUnotσ hMFeq hsourceP
  have hUHall : section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M :=
    letI : IsMinCE G := hmin
    source_typeP_U_hall_from_W1_kappa_hall hM hMFeq hsourceP hW1Hallκ
  rcases source_typeP_W1_KUData_structural_fields hMFeq hsourceP with
    ⟨hcompW1USigma, hcompSigmaW1U, hUSigmaNormal, hUnormal⟩
  have hregular : section14ActsRegularlyOn W1 U :=
    source_typeP_W1_actsRegularlyOn_U hsourceP
  exact ⟨W1, hW1Hallκ, hcompW1USigma, hcompSigmaW1U, hUHall, hregular,
    hUSigmaNormal, hUnormal⟩

/-- The BG T6 centralizer alternative for source Type-P data in the
non-`M_sigma` branch, reduced to the exact `KUData`-existence bridge. -/
public theorem CFSG.source_typeP_T6_of_not_le_msigma_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hUnotσ : ¬ U ≤ section10Msigma M)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  letI : IsMinCE G := hmin
  rcases source_typeP_exists_KUData_of_not_le_msigma_core
      hmin hM hMF hUne hUnotσ hsourceP with
    ⟨K, hKU⟩
  exact section16_typeCommon_T6_of_KUData_ne_bot
    (G := G) (M := M) (MF := MF) (K := K) (U := U) hM hMF hKU hUne

/-- The remaining nontrivial-`U` BG T6 centralizer condition needed to turn
source Type-P data into BG `section16TypeCommon` data. If the source
complement lies in `M_sigma`, Section 16 fusion control gives T6 directly;
otherwise the remaining source debt is the direct non-`M_sigma` T6 transfer. -/
public theorem CFSG.source_typeP_T6_of_U_ne_bot_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hUne : U ≠ ⊥)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  letI : IsMinCE G := hmin
  by_cases hUσ : U ≤ section10Msigma M
  · rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
      ⟨K, U0, hKU15⟩
    have hKU : section16KUData M K U0 := by
      simpa [section16KUData] using hKU15
    exact section16_typeCommon_T6_of_le_msigma
      (G := G) (M := M) (MF := MF) (K := K) (U := U0) (V := U)
      hM hMF hKU hUσ
  · exact source_typeP_T6_of_not_le_msigma_core hmin hM hMF hUne hUσ hsourceP

/-- The missing BG T6 centralizer condition needed to turn source Type-P data
into BG `section16TypeCommon` data. The trivial-`U` case is closed locally, so
the remaining source debt is the nontrivial-`U` core. -/
public theorem CFSG.source_typeP_T6_for_not_typeI_core
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hmin : IsMinCE G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hsourceP : Section8.typePDefinitionData M MF U W1 W2) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  by_cases hUbot : U = ⊥
  · exact source_typeP_T6_of_U_eq_bot hUbot
  · exact source_typeP_T6_of_U_ne_bot_core hmin hM hMF hUbot hsourceP


/-- The all-Type-I branch in the BG Section 16 alternative cannot occur for a
minimal counterexample. This is the precise remaining branch-exclusion input;
the case-B data then follows from the proved BG16 alternative. -/
public theorem CFSG.not_bg16AllMaximalTypeI_of_isMinCE
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G → bg16AllMaximalTypeI G → False := by
  intro hmin hAll
  letI : IsMinCE G := hmin
  exact Section12.theorem_12_17_all_typeI_contradiction hmin (by
    intro M hM
    rcases hAll M hM with ⟨MF, hMF, hTypeI⟩
    exact ⟨MF, hMF, hTypeI,
      Section8.theorem_8_8_typeI_to_source_public (G := G) hM hMF hTypeI⟩)


/-- The bridge converts the BG Section 16 alternative into PF Section 14 final
data. -/
public theorem CFSG.pfSection14FinalData_of_bg16_alternative
    {G : Type u} [Group G] [Finite G]
    (hbridge : pfSection14FinalDataBridge G)
    (hmin : IsMinCE G)
    (halt : bg16AllMaximalTypeI G ∨ bg16CaseBData G) :
    pfSection14FinalData G := by
  rcases hbridge hmin with ⟨hAllTypeI, hCaseB⟩
  rcases halt with hAllTypeI' | hCaseB'
  · exact False.elim (hAllTypeI hAllTypeI')
  · exact hCaseB hCaseB'

/-- A minimal counterexample supplies PF Section 14 final data once the explicit
local-analysis bridge is available. -/
public theorem CFSG.pfSection14FinalData_of_isMinCE_of_bridge
    {G : Type u} [Group G] [Finite G]
    (hbridge : pfSection14FinalDataBridge G)
    (hmin : IsMinCE G) :
    pfSection14FinalData G :=
  pfSection14FinalData_of_bg16_alternative hbridge hmin
    (bg16_final_alternative_of_isMinCE hmin)


/-- The PF Section 14 final data rules out a minimal counterexample. -/
public theorem CFSG.not_isMinCE_of_pfSection14FinalData
    {G : Type u} [Group G] [Finite G]
    (hdata : pfSection14FinalData G) :
    ¬ IsMinCE G := by
  intro _hmin
  rcases hdata with
    ⟨Smax, Tmax, W, W1, W2, P, Q, U, V, C, D,
      Sfam, Tfam, τS, τT, p, q, u, v, c, d, _h13, hsource, h14, h14_1⟩
  have hqp : q < p := by
    simpa [Section14.hypothesis_14_1_statement] using h14_1
  have hctx :
      Section14.hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d := ⟨hsource, hqp⟩
  exact Section14.theorem_14_conclusion Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hctx (h14 hctx)

/-- The standard reduction from a counterexample to the odd order theorem to a
minimal counterexample. -/
public theorem CFSG.minimalCounterexampleReduction_theorem :
    minimalCounterexampleReduction.{u} := by
  classical
  intro hnotTheorem
  let Bad : ℕ → Prop := fun n =>
    ∃ (G : Type u), ∃ (_ : Group G), ∃ (_ : Finite G),
      Nat.card G = n ∧ Odd (Nat.card G) ∧ ¬ Group.IsSolvable G
  have hBadExists : ∃ n, Bad n := by
    dsimp [oddOrderTheorem] at hnotTheorem
    push Not at hnotTheorem
    rcases hnotTheorem with ⟨G, hG, hfin, hodd, hnotSolv⟩
    exact ⟨Nat.card G, G, hG, hfin, rfl, hodd, hnotSolv⟩
  let n := Nat.find hBadExists
  rcases Nat.find_spec hBadExists with ⟨G, hG, hfin, hcardG, hoddG, hnotSolvG⟩
  letI : Group G := hG
  letI : Finite G := hfin
  have hminimal : ∀ {H : Type u} [Group H] [Finite H],
      Nat.card H < Nat.card G → Odd (Nat.card H) → Group.IsSolvable H := by
    intro H hHgroup hHfin hlt hoddH
    by_contra hnotH
    have hBadH : Bad (Nat.card H) := ⟨H, hHgroup, hHfin, rfl, hoddH, hnotH⟩
    have hn_le_H : n ≤ Nat.card H := Nat.find_min' hBadExists hBadH
    have hlt' : Nat.card H < n := by
      simpa [n, hcardG] using hlt
    exact (Nat.not_lt_of_ge hn_le_H) hlt'
  have hproper_solvable : ∀ (H : Subgroup G), H < ⊤ → Group.IsSolvable H := by
    intro H hHlt
    have hcard_lt : Nat.card H < Nat.card G := by
      simpa using natCard_lt_of_subgroup_lt hHlt
    exact hminimal hcard_lt
      (Odd.of_dvd_nat hoddG (Subgroup.card_subgroup_dvd_card H))
  have hnontrivial : Nontrivial G := by
    by_contra hnt
    haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hnt
    exact hnotSolvG (inferInstance : Group.IsSolvable G)
  have hsimple : IsSimpleGroup G := by
    letI : Nontrivial G := hnontrivial
    refine ⟨?_⟩
    intro N hNnormal
    by_cases hNbot : N = ⊥
    · exact Or.inl hNbot
    · by_cases hNtop : N = ⊤
      · exact Or.inr hNtop
      · exfalso
        letI : N.Normal := hNnormal
        have hNsolv : Group.IsSolvable N := by
          have hNlt : N < ⊤ := lt_top_iff_ne_top.2 hNtop
          exact hproper_solvable N hNlt
        have hQsolv : Group.IsSolvable (G ⧸ N) := by
          have hQlt : Nat.card (G ⧸ N) < Nat.card G :=
            natCard_quotient_lt_of_ne_bot N hNbot
          have hQodd : Odd (Nat.card (G ⧸ N)) :=
            Odd.of_dvd_nat hoddG (Subgroup.card_quotient_dvd_card (s := N))
          exact hminimal hQlt hQodd
        exact hnotSolvG (isSolvable_of_normal_subgroup_and_quotient N)
  exact ⟨G, hG, hfin, IsMinCE.mk hoddG hsimple hnotSolvG hproper_solvable⟩


/-- The raw case `(8.8)(b)` cyclic factors admit a strict orientation. The
ordered PF13/PF14 route chooses the smaller one as `W1`. -/
public theorem CFSG.caseB_cardW1_lt_or_cardW2_lt_of_bg16CaseB
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G →
      ∀ {W W1 W2 Smax Tmax P Q : Subgroup G},
        Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q →
          Nat.card W1 < Nat.card W2 ∨ Nat.card W2 < Nat.card W1 := by
  intro _hmin W W1 W2 Smax Tmax P Q hcase
  have hne : Nat.card W1 ≠ Nat.card W2 := caseB_cardW1_ne_cardW2 hcase
  omega

/-- The raw case `(8.8)(b)` data determine the Type-P common-complement
witnesses aligned with the ordered final factors. This is the exact
source-shape bridge behind the final PF13 setup choices. -/
public theorem CFSG.pfSection13TypePDataForCaseB_of_bg16CaseB_of_card_lt
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G →
      ∀ {W W1 W2 Smax Tmax P Q : Subgroup G},
        Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q →
          Nat.card W1 < Nat.card W2 →
          pfSection13TypePDataForCaseB W W1 W2 Smax Tmax P Q := by
  intro _hmin W W1 W2 Smax Tmax P Q hcase _hlt
  rcases hcase with
    ⟨_hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax,
      hSF, hTF, _hSnotTypeI, _hTnotTypeI, _hSeq, _hTeq, _hSinf, _hTinf,
      _hSW2leSecond, _hTW1leSecond, _hST, _hCover, _hTypeII, _hSType, _hTType,
      hAligned⟩
  rcases hAligned with ⟨U, V, hSCommon, hTCommon⟩
  exact ⟨U, V, ⟨hSF, hSCommon⟩, ⟨hTF, hTCommon⟩⟩

/-- The final-theorem-facing Section 13 setup choices attached to a case
`(8.8)(b)` branch after choosing the cardinal orientation. -/
public theorem CFSG.pfSection13SetupDataForCaseB_of_bg16CaseB_of_card_lt
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G →
      ∀ {W W1 W2 Smax Tmax P Q : Subgroup G},
        Section8.theorem_8_8_case_b_data W W1 W2 Smax Tmax P Q →
          Nat.card W1 < Nat.card W2 →
          pfSection13SetupDataForCaseB W W1 W2 Smax Tmax P Q := by
  intro hmin W W1 W2 Smax Tmax P Q hcase hlt
  exact pfSection13SetupDataForCaseB_of_typePData
    hmin
    hcase
    (pfSection13TypePDataForCaseB_of_bg16CaseB_of_card_lt hmin hcase hlt)
    hlt

/-- BG Section 16 case `(8.8)(b)` supplies the PF Section 13 setup data
needed for the final Section 14 application. -/
public theorem CFSG.pfSection13CaseBFinalData_of_bg16CaseB
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G → bg16CaseBData G → pfSection13CaseBFinalData G := by
  intro hmin hcaseB
  rcases hcaseB with ⟨W, W1, W2, Smax, Tmax, P, Q, hcase⟩
  rcases caseB_cardW1_lt_or_cardW2_lt_of_bg16CaseB hmin hcase with hlt | hgt
  · exact pfSection13CaseBFinalData_of_caseB_setupData hmin hcase
      (pfSection13SetupDataForCaseB_of_bg16CaseB_of_card_lt hmin hcase hlt)
  · have hcase' :
        Section8.theorem_8_8_case_b_data W W2 W1 Tmax Smax Q P :=
      section8_caseBData_swap hcase
    exact pfSection13CaseBFinalData_of_caseB_setupData hmin hcase'
      (pfSection13SetupDataForCaseB_of_bg16CaseB_of_card_lt hmin hcase' hgt)

/-- PF Section 14 theorem `(14.2)` applies to the final Section 13 data. -/
public theorem CFSG.pfSection14StatementBridge_theorem_of_isMinCE
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinCE G) :
    pfSection14StatementBridge G := by
  letI : IsMinCE G := hmin
  intro Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
    _h13 _h14_1 hctx
  exact Section14.theorem_14_2_from_minCE (G := G)
    Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d hctx


/-- In the non-Type-I branch of BG Section 16, the PF Section 13/14 setup and
the Appendix C condition `(B)` bridge are available. -/
public theorem CFSG.pfSection14FinalData_of_bg16CaseB
    {G : Type u} [Group G] [Finite G] :
    IsMinCE G → bg16CaseBData G → pfSection14FinalData G := by
  intro hmin hcaseB
  exact pfSection14FinalData_of_pfSection13CaseBFinalData
    (pfSection13CaseBFinalData_of_bg16CaseB hmin hcaseB)
    (pfSection14StatementBridge_theorem_of_isMinCE hmin)

/-- The remaining local-analysis-to-PF bridge, assembled from the two explicit
branch bridges. -/
public theorem CFSG.pfSection14FinalDataBridge_theorem
    {G : Type u} [Group G] [Finite G] :
    pfSection14FinalDataBridge G := by
  intro hmin
  exact ⟨not_bg16AllMaximalTypeI_of_isMinCE hmin,
    pfSection14FinalData_of_bg16CaseB hmin⟩


/-- The odd order theorem follows once every minimal counterexample supplies the
PF Section 14 final data. -/
public theorem CFSG.odd_order_theorem_of_minimalCounterexampleReduction
    (hreduction : minimalCounterexampleReduction.{u})
    (hpf14 : ∀ {G : Type u} [Group G] [Finite G],
      IsMinCE G → pfSection14FinalData G) :
    oddOrderTheorem.{u} := by
  by_contra hnot
  rcases hreduction hnot with ⟨G, hG, hfin, hmin⟩
  letI : Group G := hG
  letI : Finite G := hfin
  exact not_isMinCE_of_pfSection14FinalData (hpf14 hmin) hmin

/-- The odd order theorem follows from the explicit final local-analysis bridge. -/
public theorem CFSG.odd_order_theorem_of_pfSection14FinalDataBridge
    (hbridge : ∀ {G : Type u} [Group G] [Finite G],
      pfSection14FinalDataBridge G) :
    oddOrderTheorem.{u} :=
  odd_order_theorem_of_minimalCounterexampleReduction
    minimalCounterexampleReduction_theorem
    (fun {G} [Group G] [Finite G] hmin =>
      pfSection14FinalData_of_isMinCE_of_bridge (hbridge (G := G)) hmin)

/-- The Feit-Thompson odd order theorem. -/
public theorem CFSG.odd_order_theorem : ∀ (G : Type u) [Group G] [Finite G], Odd (Nat.card G) → Group.IsSolvable G :=
  odd_order_theorem_of_pfSection14FinalDataBridge
    (fun {G} [Group G] [Finite G] =>
      pfSection14FinalDataBridge_theorem (G := G))

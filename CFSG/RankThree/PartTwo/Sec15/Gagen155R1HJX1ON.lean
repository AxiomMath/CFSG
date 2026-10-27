module

public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofMax
public import CFSG.RankThree.PartTwo.Sec14.Item1417
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sSup_thetaComponentsAt (h45 : Sec4.Item4_5) (hTF : TheoremFourHyp G)
    {A : Subgroup G} (hA : Late.IsE27 A) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) :
    A ≤ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy d hdA)
  have hM : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hTF.sectionFourHyp
      (Sec14.centralizer_singleton_ne_top hTF.isSimpleGroup hTF.nonabelian hd1)
  refine Sec14.le_normalizer_sSup (A := A) (S := 𝒳) fun Q hQ => ?_
  exact Sec6.le_normalizer_of_mem_thetaComponentsIn_of_item4_5 h45 hM hAC hA.1
    ⟨3, le_rfl, by rw [hA.2]; norm_num⟩ Q (h𝒳 hQ)

section ON


theorem isQuasisimple_thetaQuotient_sSup {d : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (hON : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
      CFSG.Blueprint.NativeSporadic.ON) :
    IsQuasisimple (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) := by
  have hperf : Group.IsPerfect ↥(sSup 𝒳) :=
    Sec17.Proof171Steps.isPerfect_sSup fun M hM =>
      Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hM)
  have hperfQ : Group.IsPerfect (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) := by
    haveI := hperf
    exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup
      ((↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) ⧸
        Subgroup.center (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
    haveI : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON :=
      CFSG.Sporadic.ON.isSimpleGroup_ON
    obtain ⟨e⟩ := hON.2
    exact e.isSimpleGroup
  have hnc : ∃ a b : ((↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) ⧸
      Subgroup.center (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))), a * b ≠ b * a := by
    obtain ⟨e⟩ := hON.2
    by_contra hc
    push Not at hc
    haveI : IsMulCommutative CFSG.Blueprint.NativeSporadic.ON :=
      ⟨⟨fun a b => by simpa using congrArg e (hc (e.symm a) (e.symm b))⟩⟩
    have hprime : Nat.Prime (Nat.card CFSG.Blueprint.NativeSporadic.ON) :=
      (Group.is_simple_iff_prime_card (α := CFSG.Blueprint.NativeSporadic.ON)).mp
        CFSG.Sporadic.ON.isSimpleGroup_ON
    rw [CFSG.Sporadic.ON.card_ON_eq] at hprime
    norm_num at hprime
  exact ⟨hperfQ, hsimple, hnc⟩

theorem le_sSup_of_on (h45 : Sec4.Item4_5) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d)
    (hON : Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
      CFSG.Blueprint.NativeSporadic.ON) :
    A ≤ sSup 𝒳 := by
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hR.mem_partTwoE
  have hTF : TheoremFourHyp G := hR.toSec14Std.toSec13Data.toPartTwoStanding.toTheoremFourHyp
  have hle : sSup 𝒳 ≤ Subgroup.centralizer ({d} : Set G) :=
    sSup_le fun Q hQ => Sec14.le_centralizer_of_mem_thetaComponentsAt (h𝒳 hQ)
  have hAL : A ≤ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) :=
    le_normalizer_sSup_thetaComponentsAt h45 hTF hA hdA hd1 h𝒳
  refine ONLoc.le_of_forall_mem (Γ := G) (A := A) (L := sSup 𝒳) (e := d)
    hA hdA hd1 hle hAL ?_ hON ?_
  · exact isQuasisimple_thetaQuotient_sSup h𝒳 hON
  · intro x hx3 hx
    exact mem_of_mem_partTwoF hR.mem_partTwoF hx3 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hx a ha)

end ON

theorem exists_kd (h48 : Sec4.Item4_8) (h134 : Item134) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) :
    ∃ Kd ∈ thetaComponentsAt 3 d,
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Kd ∧
      Sec4.IsTripleCover (↥Kd ⧸ aschbacherSolvableCore 3 ↥Kd) (alternatingGroup (Fin 6)) := by
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hR.mem_partTwoE
  obtain ⟨hcA, hc3, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hR.zpowers_mem_omegaA
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc3
    norm_num at hc3
  have hTF : TheoremFourHyp G := hR.toSec14Std.toSec13Data.toPartTwoStanding.toTheoremFourHyp
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    hTF.sectionFourHyp
      (Sec14.centralizer_singleton_ne_top hTF.isSimpleGroup hTF.nonabelian hd1)
  have hchar := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hJq : IsQuasisimple
      (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) :=
    Sec14.residual_inf_centralizer_quasisimple_of_quot (L := L) h415 hchar.2.2.1 hchar.1 hJ
      hdL hd1 ⟨S, hdS, hSd⟩
  obtain ⟨Kd, hKd, hJKd⟩ :=
    Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hR.mem_lA.1 hJq
  have h3c : ∃ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 T L ∧
      (Subgroup.center T).map T.subtype = Subgroup.zpowers d := by
    obtain ⟨h1, h2⟩ :=
      Sec14.center_sylow_eq_zpowers_of_quot_j2 h415 hchar.2.2.1 hJ hdL hd1 S hdS hSd
    exact ⟨(S : Subgroup ↥L).map L.subtype, h1, h2⟩
  obtain ⟨-, h6, -⟩ | ⟨-, h6, -⟩ | ⟨-, -, -, h12⟩ :=
    h134 G A c L hR.toSec14Std.toSec13Data hJ d hdA hd1 h3c Kd hKd hJKd
  · exact ⟨Kd, hKd, hJKd, h6⟩
  · exact ⟨Kd, hKd, hJKd, h6⟩
  · exfalso
    rw [hΩ, Set.ncard_singleton] at h12
    norm_num at h12

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJX1

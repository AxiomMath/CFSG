module

import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.Sporadic.ON
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidualOf_mono_three {K K' : Subgroup G} (h : K ≤ K') :
    oPrimeResidualOf 3 K ≤ oPrimeResidualOf 3 K' := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure]
  exact Subgroup.closure_mono fun x ⟨hx, k, hk⟩ => ⟨h hx, k, hk⟩

theorem three_dvd_card_quot_of_three_dvd {L : Subgroup G} (h3 : 3 ∣ Nat.card L) :
    3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hθ := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)] at h3
  exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_right hθ

omit [Finite G] in
theorem theta_le (X : Subgroup G) : inSubgroup (aschbacherSolvableCore 3) X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_normalizer_theta (X : Subgroup G) :
    X ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) := by
  have hchar := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.1
  exact Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (aschbacherSolvableCore 3 ↥X))

theorem isSolvable_theta (X : Subgroup G) :
    Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) X) := by
  have hθs := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  exact Group.isSolvable_of_surjective (f := ((aschbacherSolvableCore 3 ↥X).equivMapOfInjective
    X.subtype X.subtype_injective).toMonoidHom) (MulEquiv.surjective _)

theorem isHyperplane_closure_pair {A : Subgroup G} (hA : Late.IsE27 A) {x y : G} (hx : x ∈ A)
    (hy : y ∈ A) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : Subgroup.zpowers x ≠ Subgroup.zpowers y) :
    IsHyperplane A (Subgroup.closure {x, y}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hox : orderOf x = 3 := orderOf_eq_prime (hA.1.2 x hx) hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime (hA.1.2 y hy) hy1
  have hyx : y ∉ Subgroup.zpowers x := by
    intro hmem
    apply hxy
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoy]
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hoy hyx
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers x)
    (Subgroup.zpowers y) fun u hu v hv =>
      hcomm u ((Subgroup.zpowers_le.mpr hx) hu) v ((Subgroup.zpowers_le.mpr hy) hv)
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hox, hoy] at hcard
  have hcl : Subgroup.closure {x, y} = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [show ({x, y} : Set G) = {x} ∪ {y} from rfl, Subgroup.closure_union,
      ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hx, hy]
  · rw [hA.2, hcl, hcard]

theorem delta_normalizer_le {A : Subgroup G} {b : G} (hbA : b ∈ A) (hb3 : orderOf b = 3) :
    delta A (lB A) (Subgroup.normalizer (Subgroup.zpowers b : Set G)) ≤
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) :=
  sSup_le fun _ hQ => le_delta hQ.1 (le_centralizer_of_mem_invariantPiSubgroups hbA hb3
    ⟨hQ.2, hQ.1.1.2.1, hQ.1.1.2.2⟩)

theorem pPrimeCoreOf_normalizer_le {A : Subgroup G} {b : G} (hbA : b ∈ A) (hb3 : orderOf b = 3)
    (hAb : A ≤ Subgroup.centralizer ({b} : Set G)) :
    pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers b : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hH
  have hCH : Subgroup.centralizer ({b} : Set G) ≤ H := by
    rw [hH, ← centralizer_zpowers148]
    exact Subgroup.centralizer_le_normalizer _
  have hcop := coprime_card_pPrimeCoreOf 3 H
  have hPb : pPrimeCoreOf 3 H ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_invariantPiSubgroups hbA hb3
      ⟨pPrimeCoreOf_le 3 H, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop),
        (hAb.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)⟩
  exact le_pPrimeCoreOf hPb (hCH.trans (le_normalizer_pPrimeCoreOf 3 H)) hcop

theorem oPrimeResidual_quot_eq_top_of_types
    {b : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 b)
    (hT : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    oPrimeResidual 3 (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊤ := by
  have h3 := three_dvd_card_quot_of_three_dvd (three_dvd_card_of_types148 hT)
  have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, -⟩ := Sec13.sporadicModels131
  rcases hT with ⟨⟨φ⟩⟩ | ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := φ.isSimpleGroup
    exact oPrimeResidual_eq_top_of_isSimpleGroup h3
  · have : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso).1
    exact oPrimeResidual_eq_top_of_isSimpleGroup h3
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    have : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := φ.isSimpleGroup
    exact oPrimeResidual_eq_top_of_isSimpleGroup h3
  · have hz : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
      have hmap := Subgroup.map_center_eq φ
      rw [hM22z] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
    exact oPrimeResidual_eq_top_of_isQuasisimple hq hz h3
  · have hz : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ := by
      have hmap := Subgroup.map_center_eq φ
      rw [hM12z] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
    exact oPrimeResidual_eq_top_of_isQuasisimple hq hz h3

theorem eq_oPrimeResidualOf_of_types
    {b : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 b)
    (hT : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    L = oPrimeResidualOf 3 L :=
  eq_oPrimeResidualOf_of_quot (Sec6.isPerfect_of_mem_thetaComponentsAt hL)
    (oPrimeResidual_quot_eq_top_of_types hL hT)

theorem residual_eq_oPrimeResidualOf
    {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) =
      oPrimeResidualOf 3
        (inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G))) := by
  obtain ⟨-, -, -, -, -, htc, -⟩ := Item148HJ.resProj_facts h hB hc
  have hperf := Item148HJ.residual_isPerfect Lb d
  have hrange : oPrimeResidual 3 ↥(Item148HJ.resProj Lb d).range = ⊤ :=
    oPrimeResidual_eq_top_of_isTripleCover htc oPrimeResidual_alternatingGroup_six
  refine eq_oPrimeResidualOf_of_hom hperf (Item148HJ.resProj Lb d) ?_ hrange
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  let ι : ↥(Item148HJ.resProj Lb d).ker →* ↥(inSubgroup (aschbacherSolvableCore 3) Lb) :=
    { toFun := fun k => ⟨((k : ↥J) : G), (Item148HJ.mem_ker_resProj k.1).mp k.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  have := isSolvable_theta Lb
  exact Group.isSolvable_of_isSolvable_injective hι

theorem oPrimeResidual_eq_top_of_types143 {X : Type*} [Group X]
    [Finite X]
    (h : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨ IsCentralProductA6Covers X) :
    oPrimeResidual 3 X = ⊤ := by
  rcases h with h | h | h
  · obtain ⟨hfin, -, hsimp⟩ := CFSG.Sporadic.ON.fam_on_simplicity
    refine oPrimeResidual_eq_top_of_isTripleCover h ?_
    exact oPrimeResidual_eq_top_of_isSimpleGroup (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  · exact oPrimeResidual_eq_top_of_isTripleCover h oPrimeResidual_alternatingGroup_six
  · exact oPrimeResidual_eq_top_of_isCentralProductA6Covers h

section Delta

theorem lB_le_oPrimeResidualOf {A L B : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) {D : Subgroup G} (hBD : lB A B ≤ D) :
    lB A B ≤ oPrimeResidualOf 3 D := by
  refine iSup_le fun b'' => iSup_le fun d'' => iSup_le fun L'' => iSup_le fun hc => ?_
  have hJ := residual_eq_oPrimeResidualOf h hB hc
  rw [hJ]
  exact oPrimeResidualOf_mono_three
    ((Item148HJ.residual_le_lB hc).trans hBD)

end Delta

end CFSG.RankThree.PartTwo.Sec17.Proof171Steps

module

public import CFSG.RankThree.PartTwo.J2Residue.Config
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma resProj_ker_eq_pCore {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
    (hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L) :
    (Item148HJ.resProj L d).ker =
      (inSubgroup (CFSG.pCore 2) L).subgroupOf
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) := by
  obtain ⟨-, -, -, ⟨φJ⟩, -⟩ := hcfg
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hJ2s := CFSG.Sporadic.J2.isSimpleGroup_J2
  have hJ2c := KFacts.KS14.center_nativeJ2_eq_bot h415
  have hc0 : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    have hmap := Subgroup.map_center_eq φJ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φJ.injective).mp hmap
  have hqL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_mulEquiv_nativeJ2 hJ2s hJ2c φJ
  have hθO : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
    aschbacherSolvableCore_eq_pCore_two hqL hc0
  have hsub : inSubgroup (aschbacherSolvableCore 3) L =
      inSubgroup (CFSG.pCore 2) L := by
    simp only [inSubgroup, hθO]
  ext j
  exact (Item148HJ.mem_ker_resProj j).trans (by
    rw [hsub]
    exact Subgroup.mem_subgroupOf.symm)

private lemma pCore_le_resProj_ker {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {d : G}
    (hB : IsHyperplane A (Subgroup.closure {c, d}))
    (hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L) :
    CFSG.pCore 2 ↥(inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer ({d} : Set G))) ≤ (Item148HJ.resProj L d).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  obtain ⟨-, -, hq, hZ, -, -, -⟩ := Item148HJ.resProj_facts h hB hcfg
  refine Item148HJ.le_ker_of_normal (Item148HJ.resProj L d) hq hZ
    (CFSG.pCore_normal (p := 2) (G := ↥J)) ?_
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
  intro h3
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h3
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

private lemma pCoreOf_lB_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {d : G}
    (hB : IsHyperplane A (Subgroup.closure {c, d}))
    (hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L) :
    CFSG.Open.pCoreOf 2 (lB A (Subgroup.closure {c, d})) ≤ CFSG.Open.pCoreOf 2 L := by
  rw [Item148HJ.lB_eq_residual h hB hcfg]
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  change (CFSG.pCore 2 ↥J).map J.subtype ≤ (CFSG.pCore 2 ↥L).map L.subtype
  have hker := resProj_ker_eq_pCore hcfg
  have hpcore := pCore_le_resProj_ker h hB hcfg
  intro x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨j, hj, rfl⟩ := hx
  have hmem : j ∈ (Item148HJ.resProj L d).ker := hpcore hj
  rw [hker, Subgroup.mem_subgroupOf, inSubgroup, Subgroup.mem_map] at hmem
  exact hmem

section


theorem j2Config_lB_closure {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    CFSG.RankThree.PartTwo.J2Residue.J2Config L d (lB A (Subgroup.closure {c, d})) := by
  have hB : IsHyperplane A (Subgroup.closure {c, d}) :=
    isHyperplane_closure_cd h hJ hdA hd1 hdc
  have hcfg : IsLBConfig A (Subgroup.closure {c, d}) c d L :=
    isLBConfig_closure_cd_of_threeCentral h hJ hdc
  refine
    { perfect := Sec6.isPerfect_of_mem_thetaComponentsAt h.toSec13Data.mem_lA.1
      j2 := hcfg.2.2.2.1
      mem_d := hdc.choose
      orderOf_d := ?_
      threeCentral := hdc.choose_spec
      lB_eq := lB_closure_eq_residual h hJ hdA hd1 hdc
      tripleCover := isTripleCover_lB h.toSec14Std hB hcfg
      mem_lB := mem_lB_closure h hJ hdA hd1 hdc
      pCoreOf_le := pCoreOf_lB_le h.toSec14Std hB hcfg }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (h.toSec14Std.isE27.1.2 d hdA) hd1

end

end CFSG.RankThree.PartTwo.Sec16.Ctr166


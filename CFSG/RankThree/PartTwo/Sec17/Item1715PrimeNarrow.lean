module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec17.HeadProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isoLThreePi (hP : Sec4.Item4_1PRankLargePrime) {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) : e = 1 := by
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  set T := CFSG.Open.pCoreOf 2 Y₀ with hT
  have hT1 : T ≠ ⊥ := h.mem_y0Star.prop.2.2
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  set K := Subgroup.normalizer (T : Set G) with hK
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hT1 hT2
  have hLK : L ≤ K := h.le_y0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  have hK4 : SectionFourHyp K := h.toTheoremFourHyp.sectionFourHyp hKtop
  have hpK : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    have h1 := open_pRank_top_le_localRank hT1 hT2 hp
    have h2 := h.localRank_lt p hp hp3
    rw [← hK] at h1
    omega
  set H : Subgroup K := L.subgroupOf K with hH
  have eH : H ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  set N : Subgroup H := aschbacherSolvableCore 3 H with hN
  have hNc : N.Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).2.1
  have : N.Normal := inferInstance
  have hθ : N.map eH.toMonoidHom = aschbacherSolvableCore 3 L :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eH
  have eQ : (H ⧸ N) ≃* (L ⧸ aschbacherSolvableCore 3 L) := QuotientGroup.congr N _ eH hθ
  have hqL := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_lA.1
  have hq : CFSG.IsQuasisimple (H ⧸ N) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ.symm hqL
  have hlayer : layer (H ⧸ N) = ⊤ := CFSG.RankThree.Coprime.layer_eq_top_of_isQuasisimple hq
  have h5 := hP K hK4 H N hlayer p hp hp3 (hpK.trans (by norm_num))
  have h6 := two_mul_le_open_pRank_of_isoLThreePi hp2 he hiso
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eQ] at h6
  omega

theorem claim1715Prime_narrow (hP : Sec4.Item4_1PRankLargePrime) : Claim1715Prime := by
  intro G _ _ A c L Y₀ h p e _ hp3 he hiso
  exact eq_one_of_isoLThreePi hP h hp3 he hiso

section Griess

theorem claim1715Prime_of_griess (hGA : GriessMultipliersAllModels) : Claim1715Prime :=
  claim1715Prime_narrow (Sec4.Item41Narrow.item4_1PRankLargePrime_of_griess hGA)

end Griess

end CFSG.RankThree.PartTwo.Sec17.HeadProof


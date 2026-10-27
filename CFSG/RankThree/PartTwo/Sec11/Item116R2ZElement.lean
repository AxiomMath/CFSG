module

public import CFSG.RankThree.PartTwo.Sec11.Item116R1H1bCfg
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZBar
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZStep
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZSylow
import CFSG.RankThree.PartTwo.KFacts.K71Coprime

public section

open CFSG Subgroup CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem zElement_holds : ZElement := by
  intro G _ _ A c L a R Y d h hAT hR1 hSurv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHyp : Sec8.Hyp81 G A c L a := h.toSec11StdLocal.toHyp81
  have hAel : CFSG.Assembly.IsElemAbelian 3 A := hHyp.mem_partTwoF.1
  have ha : a ∈ Subgroup.normalizer (L : Set G) := Sec8.Hyp81.a_mem_normalizer hHyp
  have ha3 : a ^ 3 = 1 := hAel.2 a hHyp.a_mem
  have hdAL : d ∈ A ⊓ L := by
    rw [h.inf_eq_zpowers]
    exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAL.1
  have hdL : d ∈ L := hdAL.2
  have hd3 : d ^ 3 = 1 := hAel.2 d hdA
  have hd1 : d ≠ 1 := fun h1 => h.not_mem_zpowers (h1 ▸ Subgroup.one_mem _)
  have had : a * d = d * a := by
    have := hAel.1.is_comm.comm (⟨a, hHyp.a_mem⟩ : A) ⟨d, hdA⟩
    exact congrArg Subtype.val this
  have hout : Sec4.InducesOuterTheta a L := by
    rcases hHyp.inducesStdKind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk (by decide)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hHyp.mem_thetaComponentsAt
  set N : Subgroup L := aschbacherSolvableCore 3 L
  haveI := Sec4.aschbacherSolvableCore_characteristic L
  haveI : N.Normal := inferInstance
  have hN : ¬ 3 ∣ Nat.card N := KFacts.not_three_dvd_card_aschbacherSolvableCore L
  set φ : MulAut L := Sec4.compAction L ⟨a, ha⟩ with hφdef
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφdef, ← map_pow]
    have h1 : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext ha3
    rw [h1, map_one]
  have hφN : ∀ n ∈ N, φ n ∈ N := by
    intro n hn
    have h1 : N.map (φ : L →* L) = N := Sec4.map_aschbacherSolvableCore φ
    have h2 : φ n ∈ N.map (φ : L →* L) := Subgroup.mem_map_of_mem _ hn
    rwa [h1] at h2
  have hφapply : ∀ x : L, ((φ x : L) : G) = a * x * a⁻¹ := fun x =>
    Sec4.normalizerMonoidHom_apply_coe ha x
  set dL : L := ⟨d, hdL⟩
  have hdL3 : dL ^ 3 = 1 := Subtype.ext hd3
  have hdL1 : dL ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hφd : φ dL = dL := by
    apply Subtype.ext
    rw [hφapply]
    show a * d * a⁻¹ = d
    rw [had, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨hnine, hfix⟩ := zNumeric_of_surviving ha ha3 hout hSurv
  have hcyc : ∀ S : Sylow 3 (L ⧸ N), IsCyclic ↥(S : Subgroup (L ⧸ N)) := fun S =>
    isCyclic_sylow_three_of_isList1016 h.isList1016 S
  set α : MulAut (L ⧸ N) := Sec4.thetaQuotMulAut L φ with hαdef
  have hx3 : (QuotientGroup.mk dL : L ⧸ N) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hdL3, QuotientGroup.mk_one]
  have hfact : ∀ Pb : Subgroup (L ⧸ N),
      Pb ≤ Subgroup.centralizer ({(QuotientGroup.mk dL : L ⧸ N)} : Set (L ⧸ N)) →
      Nat.card Pb = 3 ^ (Nat.card (Subgroup.centralizer
        ({(QuotientGroup.mk dL : L ⧸ N)} : Set (L ⧸ N)))).factorization 3 →
        IsCyclic ↥Pb ∧ 9 ≤ Nat.card Pb ∧
          ∃ y ∈ Pb, ∃ x : L, (QuotientGroup.mk x : L ⧸ N) = y ∧
            (QuotientGroup.mk (φ x) : L ⧸ N) ≠ y := by
    intro Pb _ hPcard
    obtain ⟨hPc, hP9, y, hy, hmov⟩ := zq_of_cyclic_sylow α hx3 hcyc hnine hfix Pb hPcard
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨hPc, hP9, _, hy, x, rfl, hmov⟩
  obtain ⟨z, v, k, hv, hz, hzC, hzd, hzφ, hk1, hk2⟩ :=
    exists_z_of_quotient N hN φ hφ3 hφN hdL3 hdL1 hφd hfact
  refine ⟨(z : G), v, k, z.2, hv, ?_, ?_, ?_, ?_, ?_, hk1, hk2⟩
  · rw [Subgroup.orderOf_coe]
    exact hz
  · have h1 := congrArg Subtype.val hzd
    rwa [Subgroup.coe_pow] at h1
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hLc z.2)
  · exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hzC)
  · calc a * (z : G) * a⁻¹ = ((φ z : L) : G) := (hφapply z).symm
      _ = ((z ^ k : L) : G) := congrArg Subtype.val hzφ
      _ = (z : G) ^ k := by rw [Subgroup.coe_pow]

end Certified

end CFSG.RankThree.PartTwo.Sec11

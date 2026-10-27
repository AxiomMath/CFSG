module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Extraction.FrontHalf
public import CFSG.RankThree.PartOne.S9.Extraction.Tail

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.PartOne.Extract CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem centralizerConstrainedCriticalAction : CentralizerConstrainedCriticalAction := by
  intro H _ _ p hp hp2 A hAe hA3 b hbA _ hXS hXJ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hSs, -, hpS, -, -, -, hScore⟩ :=
    solvable_prime_complement_core_characterization (H := H) hp
  have hJS : pCore 2 H ≤ aschbacherSolvableCore p H := hScore 2 Nat.prime_two (Ne.symm hp2)
  have hAp : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hJ2 : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  set C : Subgroup H := centralizer ({b} : Set H) with hC
  set V : Subgroup H := inSubgroup (pCore 2) C with hV
  have hVC : V ≤ C := map_subtype_le _
  have hV2 : IsPGroup 2 V := pCore_isPGroup.map C.subtype
  have hbc : ∀ a ∈ A, a * b = b * a := fun a ha =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hbA⟩)
  have hAC : A ≤ C := fun a ha => mem_centralizer_singleton_iff.mpr (hbc a ha)
  have hVn : C ≤ normalizer (V : Set H) := by
    have hsub : V.subgroupOf C = pCore 2 C := comap_map_eq_self_of_injective C.subtype_injective _
    have hn : (V.subgroupOf C).Normal := by
      rw [hsub]
      exact pCore_normal
    exact (normal_subgroupOf_iff_le_normalizer hVC).mp hn
  have hAV : A ≤ normalizer (V : Set H) := hAC.trans hVn
  have hJC : pCore 2 H ⊓ C ≤ V := by
    set K : Subgroup C := (pCore 2 H).subgroupOf C with hK
    have hKn : K.Normal := Normal.subgroupOf inferInstance C
    have hK2 : IsPGroup 2 K := fun x => by
      obtain ⟨k, hk⟩ := hJ2 ⟨(x : H), x.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    have hKle : K ≤ pCore 2 C := le_sSup ⟨hKn, hK2⟩
    have hmapK : K.map C.subtype = pCore 2 H ⊓ C := subgroupOf_map_subtype _ _
    rw [← hmapK]
    exact map_mono hKle
  have hXV : ⁅V, A⁆ ≤ V := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing V A hAV
  have hXA : A ≤ normalizer ((⁅V, A⁆ : Subgroup H) : Set H) :=
    CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A V hAV
  have hX2 : IsPGroup 2 (⁅V, A⁆ : Subgroup H) := hV2.to_le hXV
  have hXc : ⁅⁅V, A⁆, A⁆ = ⁅V, A⁆ := commutator_commutator_eq hp hp2 hAp hV2 hAV
  have hbX : ∀ x ∈ (⁅V, A⁆ : Subgroup H), b * x = x * b := fun x hx =>
    (mem_centralizer_singleton_iff.mp (hVC (hXV hx))).symm
  obtain ⟨q, hq, hq2, hqp, R, Q, hRX, hAR, hRc, hRJ, hRmin, hQ, hRQ, hAQ, hRQ', hbR⟩ :=
    front_half hp hp2 A (aschbacherSolvableCore p H) ⁅V, A⁆ b hAp inferInstance hSs hpS hbA hbc
      hXA hX2 hXS hXc hXJ hbX
  have hRS : R ≤ aschbacherSolvableCore p H := hRX.trans (sup_le hJS hXS)
  have hRV : R ≤ V := by
    intro x hx
    have hx' : x ∈ ((pCore 2 H ⊔ ⁅V, A⁆ : Subgroup H) : Set H) := hRX hx
    rw [normal_mul] at hx'
    obtain ⟨j, hj, r, hr, rfl⟩ := hx'
    have hbx : Commute b (j * r) := (hbR _ hx)
    have hbr : Commute b r := hbX r hr
    have hbj : Commute b j := by
      have := hbx.mul_right hbr.inv_right
      rwa [mul_inv_cancel_right] at this
    have hjC : j ∈ C := mem_centralizer_singleton_iff.mpr hbj.symm.eq
    exact mul_mem (hJC ⟨hj, hjC⟩) (hXV hr)
  have hR2 : IsPGroup 2 R := hV2.to_le hRV
  obtain ⟨D, hDQ, hDchar, hDne, hRD, hDexp, hDQ', hRD', hcard, hCn⟩ :=
    critical_tail hp2 hq hq2 hA3 inferInstance hpS hRS hR2 hAR hRc hRJ hRmin hQ.2.1 hRQ hRQ'
  exact ⟨q, hq, hq2, hqp, R, Q, D, le_inf hRV hRS, hAR, hRc, hRJ, hRD', hQ, hRQ, hAQ,
    hDQ, hDchar, hDne, hRD, hDexp, hDQ', hcard,
    mem_centralizer_iff.mpr fun r hr => (hbR r hr).symm, hCn⟩

end CFSG.RankThree.PartOne

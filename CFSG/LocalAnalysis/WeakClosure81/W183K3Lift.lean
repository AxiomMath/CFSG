module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6SigOdd
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreLift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open Subgroup

variable {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]

private theorem w183K3Lift_ker_odd (hN : Odd (Nat.card ↥N)) :
    Odd (Nat.card (QuotientGroup.mk' N).ker) := by
  rwa [QuotientGroup.ker_mk']

theorem card_map_mk_of_isPGroup (hN : Odd (Nat.card ↥N)) {A : Subgroup Y} (hA : IsPGroup 2 A) :
    Nat.card ↥(A.map (QuotientGroup.mk' N)) = Nat.card ↥A :=
  CFSG.OddStandard.Solomon75.Sec6SigOdd.card_map_of_inf_ker
    (CFSG.OddStandard.Solomon75.Sec6SigOdd.inf_ker_eq_bot (w183K3Lift_ker_odd hN) hA)

theorem exists_isPGroup_map_mk_eq (hN : Odd (Nat.card ↥N)) {R : Subgroup (Y ⧸ N)}
    (hR : IsPGroup 2 R) :
    ∃ A : Subgroup Y, IsPGroup 2 A ∧ A.map (QuotientGroup.mk' N) = R :=
  CFSG.RankThree.PartTwo.Sec15.KS1424.exists_isPGroup_map_eq (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hR

theorem exists_conj_of_map_mk_eq (hN : Odd (Nat.card ↥N)) {A B : Subgroup Y} (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, B = A.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨k, hk, hc⟩ :=
    CFSG.OddStandard.Solomon75.Sec6SigOdd.exists_conj_of_map_eq (f := QuotientGroup.mk' N)
      (w183K3Lift_ker_odd hN) hA hB h
  refine ⟨k, ?_, hc⟩
  rwa [QuotientGroup.ker_mk'] at hk

theorem centralizer_map_mk (hN : Odd (Nat.card ↥N)) {t : Y} {k : ℕ} (ht : t ^ (2 ^ k) = 1) :
    (Subgroup.centralizer ({t} : Set Y)).map (QuotientGroup.mk' N) =
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
  have hu : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card_dvd_pow
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_iff_pow_eq_one.mpr ht)
  exact (CFSG.ComponentClassification.AschbacherToolkit.centralizer_quotient_of_isPGroup
    N hN hu).symm

theorem normalizer_map_mk (hN : Odd (Nat.card ↥N)) {A : Subgroup Y} (hA : IsPGroup 2 A) :
    (Subgroup.normalizer (A : Set Y)).map (QuotientGroup.mk' N) =
      Subgroup.normalizer ((A.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) :=
  (CFSG.ComponentClassification.AschbacherToolkit.normalizer_quotient_of_isPGroup
    N hN hA).symm

theorem isTISub_map_mk (hN : Odd (Nat.card ↥N)) {A : Subgroup Y} (hA : IsPGroup 2 A)
    (h : IsTISub Y A) : IsTISub (Y ⧸ N) (A.map (QuotientGroup.mk' N)) := by
  intro t ht ht1 g hg
  obtain ⟨t0, ht0A, rfl⟩ := Subgroup.mem_map.mp ht
  have ht0ne : t0 ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
  obtain ⟨k, hk⟩ := hA ⟨t0, ht0A⟩
  have ht0k : t0 ^ (2 ^ k) = 1 := by
    have := congrArg (fun x : ↥A => (x : Y)) hk
    simpa using this
  have hgC : g ∈ Subgroup.centralizer ({QuotientGroup.mk' N t0} : Set (Y ⧸ N)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hg
  rw [← centralizer_map_mk hN ht0k] at hgC
  obtain ⟨g0, hg0C, hg0eq⟩ := Subgroup.mem_map.mp hgC
  have hnorm : g0 ∈ Subgroup.normalizer (A : Set Y) :=
    h t0 ht0A ht0ne g0 (Subgroup.mem_centralizer_singleton_iff.mp hg0C)
  rw [← normalizer_map_mk hN hA]
  exact Subgroup.mem_map.mpr ⟨g0, hnorm, hg0eq⟩

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end

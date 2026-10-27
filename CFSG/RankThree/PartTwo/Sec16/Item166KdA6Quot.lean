module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11

theorem inSubgroup_theta_le_centralizer_of_mem_thetaComponentsAt {G : Type} [Group G] {d : G}
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d) :
    inSubgroup (aschbacherSolvableCore 3) K ≤ Subgroup.centralizer ({d} : Set G) :=
  (Sec6.theta_le K).trans (Sec14.le_centralizer_of_mem_thetaComponentsAt hK)

theorem exists_alternatingGroup_quotient_lB
    {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) :
    ∃ π : ↥(lB A (Subgroup.closure {c, d})) →* alternatingGroup (Fin 6),
      Function.Surjective π ∧
      ∀ x : ↥(lB A (Subgroup.closure {c, d})), π x = 1 →
        (x : G) ∈ CFSG.Open.pCoreOf 2 (lB A (Subgroup.closure {c, d})) ⊔
          Subgroup.zpowers d := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTC : Sec4.IsTripleCover
      (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})))
      (alternatingGroup (Fin 6)) :=
    Ctr166.isTripleCover_lB h.toSec14Std (Ctr166.isHyperplane_closure_cd h hJ hdA hd1 hdc)
      (Ctr166.isLBConfig_closure_cd_of_threeCentral h hJ hdc)
  obtain ⟨hZ3, ⟨e⟩⟩ := hTC
  let q : ↥(lB A (Subgroup.closure {c, d})) →*
      ↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) :=
    QuotientGroup.mk' _
  let r := QuotientGroup.mk' (Subgroup.center
    (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))))
  refine ⟨e.toMonoidHom.comp (r.comp q), ?_, ?_⟩
  · exact e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  intro x hx
  have hrx : r (q x) = 1 := e.map_eq_one_iff.mp hx
  have hxZ : q x ∈ Subgroup.center
      (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) :=
    (QuotientGroup.eq_one_iff (q x)).mp hrx
  have hdLB : d ∈ lB A (Subgroup.closure {c, d}) := Ctr166.mem_lB_closure h hJ hdA hd1 hdc
  have hLBC : lB A (Subgroup.closure {c, d}) ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_le_centralizer_singleton L d
  let dd : ↥(lB A (Subgroup.closure {c, d})) := ⟨d, hdLB⟩
  have hdZ : q dd ∈ Subgroup.center
      (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) y
    have hyd : y * dd = dd * y := by
      apply Subtype.ext
      have hcomm := Subgroup.mem_centralizer_iff.mp (hLBC y.2) d (Set.mem_singleton d)
      simpa [dd] using hcomm.symm
    change q y * q dd = q dd * q y
    rw [← map_mul, ← map_mul, hyd]
  have hd3 : d ^ 3 = 1 := h.toSec14Std.isE27.1.2 d hdA
  have hqd1 : q dd ≠ 1 := by
    intro h1
    have hmem : dd ∈ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) :=
      (QuotientGroup.eq_one_iff dd).mp h1
    have hP : IsPGroup 2 ↥(CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) :=
      CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP ⟨dd, hmem⟩
    have hdk : d ^ 2 ^ k = 1 := by
      have hk' := congrArg
        (fun z : ↥(CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) =>
          ((z : ↥(lB A (Subgroup.closure {c, d}))) : G)) hk
      simpa [dd] using hk'
    have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have h32 : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hdk
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h32) (by norm_num)
  have hZeq : Subgroup.zpowers (q dd) = Subgroup.center
      (↥(lB A (Subgroup.closure {c, d})) ⧸ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d}))) := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hdZ)
    have hqd3 : q dd ^ 3 = 1 := by
      have hdd3 : dd ^ 3 = 1 := Subtype.ext (by simpa [dd] using hd3)
      rw [← map_pow, hdd3, map_one]
    rw [hZ3, Nat.card_zpowers, orderOf_eq_prime hqd3 hqd1]
  rw [← hZeq] at hxZ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  have hk' : q (dd ^ k) = q x := by rw [map_zpow]; exact hk
  have hmem : (dd ^ k)⁻¹ * x ∈ CFSG.pCore 2 ↥(lB A (Subgroup.closure {c, d})) :=
    QuotientGroup.eq.mp hk'
  have hx' : (x : G) = d ^ k * (((dd ^ k)⁻¹ * x : ↥(lB A (Subgroup.closure {c, d}))) : G) := by
    simp [dd]
  rw [sup_comm, hx']
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers d k)
    (Subgroup.mem_map.mpr ⟨(dd ^ k)⁻¹ * x, hmem, rfl⟩)

end CFSG.RankThree.PartTwo.Sec16.Kd166

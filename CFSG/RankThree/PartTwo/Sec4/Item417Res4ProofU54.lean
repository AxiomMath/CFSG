module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofCenters
import CFSG.RankThree.CentralLift.EvenScalarCover
import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Four

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU localRank)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj StatedScalars)

theorem theta_le_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hY : IsQuasisimple Y) : aschbacherSolvableCore p Y ≤ Subgroup.center Y := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hY
    (inferInstance : (aschbacherSolvableCore p Y).Normal) with h | h
  · exfalso
    have hsol : Group.IsSolvable (aschbacherSolvableCore p Y) :=
      (solvable_prime_complement_core_characterization (H := Y) hp).1
    rw [h] at hsol
    have hsolY : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := Y)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := Y)).symm.injective
    have := hY.1
    have := CFSG.LocalCores.isQuasisimple_nontrivial hY
    exact Group.IsPerfect.not_isSolvable _ hsolY
  · exact h

theorem isPGroup_center_quot_theta5 {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) :
    IsPGroup 5 (Subgroup.center (Y ⧸ aschbacherSolvableCore 5 Y)) := by
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  set θ := aschbacherSolvableCore 5 Y with hθ
  obtain ⟨-, -, hθ5, hmax, -⟩ := solvable_prime_complement_core_characterization (H := Y) hp5
  have hθZ : θ ≤ Subgroup.center Y := theta_le_center hp5 hY
  obtain ⟨-, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hY θ hθZ
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrdvd => ?_⟩
  by_contra hr5
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  have hxmem : (x : Y ⧸ θ) ∈ (Subgroup.center Y).map (QuotientGroup.mk' θ) := hcen ▸ x.2
  obtain ⟨y, hyZ, hyx⟩ := hxmem
  have hyr : y ^ r ∈ θ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change (QuotientGroup.mk' θ y) ^ r = 1
    rw [hyx]
    have h1 := pow_orderOf_eq_one x
    rw [hx] at h1
    exact congrArg Subtype.val h1
  have hy5 : ¬ 5 ∣ orderOf y := by
    intro h5
    have hd : orderOf y ∣ r * orderOf (y ^ r) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    have hdθ : orderOf (y ^ r) ∣ Nat.card θ := by
      have := orderOf_dvd_natCard (⟨y ^ r, hyr⟩ : θ)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.Prime.dvd_mul hp5).mp (h5.trans hd) with h | h
    · exact hr5 ((Nat.prime_dvd_prime_iff_eq hp5 hr).mp h).symm
    · exact hθ5 (h.trans hdθ)
  set S : Subgroup Y := Subgroup.zpowers y ⊔ θ with hS
  have hSZ : S ≤ Subgroup.center Y := sup_le (Subgroup.zpowers_le.mpr hyZ) hθZ
  have hSn : S.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_center_iff.mp (hSZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hSs : Group.IsSolvable S := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hSZ b.2) a)
  have hS5 : ¬ 5 ∣ Nat.card S := by
    have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ θ, a * b = b * a := fun a _ b hb =>
      (Subgroup.mem_center_iff.mp (hθZ hb) a)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    intro h5
    have h5' : 5 ∣ Nat.card (Subgroup.zpowers y) * Nat.card θ := by
      rw [← hcard]
      exact dvd_mul_of_dvd_left h5 _
    rw [Nat.card_zpowers] at h5'
    rcases (Nat.Prime.dvd_mul hp5).mp h5' with h | h
    · exact hy5 h
    · exact hθ5 h
  have hSθ : S ≤ θ := hmax S hSn hSs hS5
  have hyθ : y ∈ θ := hSθ (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
  have hx1 : x = 1 := by
    apply Subtype.ext
    rw [← hyx]
    exact (QuotientGroup.eq_one_iff y).mpr hyθ
  rw [hx1, orderOf_one] at hx
  exact hr.one_lt.ne hx

theorem k417CenterU54_holds :
    Res417Three.K417CenterU54 := by
  intro Y _ _ hY hS ⟨φ⟩ h5
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := aschbacherSolvableCore 5 Y with hθ
  have hθ5 : ¬ 5 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := Y) hp5).2.2.1
  have hθZ : θ ≤ Subgroup.center Y := theta_le_center hp5 hY
  obtain ⟨hLq, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hY θ hθZ
  have : Group.IsPerfect (Y ⧸ θ) := hLq.1
  have h5L : 5 ∣ Nat.card (Subgroup.center (Y ⧸ θ)) := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hzc : ((z : Y) : Y ⧸ θ) ∈ Subgroup.center (Y ⧸ θ) := by
      rw [hcen]
      exact ⟨z, z.2, rfl⟩
    have hz1 : ((z : Y) : Y ⧸ θ) ≠ 1 := by
      intro h1
      have hzθ : (z : Y) ∈ θ := (QuotientGroup.eq_one_iff _).mp h1
      apply hθ5
      have := orderOf_dvd_natCard (⟨(z : Y), hzθ⟩ : θ)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz] at this
    have hz5' : z ^ 5 = 1 := hz ▸ pow_orderOf_eq_one z
    have hz5 : ((z : Y) : Y ⧸ θ) ^ 5 = 1 := by
      rw [← QuotientGroup.mk_pow, ← Subgroup.coe_pow, hz5']
      rfl
    have hord : orderOf (⟨((z : Y) : Y ⧸ θ), hzc⟩ : Subgroup.center (Y ⧸ θ)) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hz5 hz1
    have hdvd := orderOf_dvd_natCard (⟨((z : Y) : Y ⧸ θ), hzc⟩ : Subgroup.center (Y ⧸ θ))
    rwa [hord] at hdvd
  set K := GaloisField 2 (2 * 2)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
    Sec4.unitaryFieldData_galoisField 2 2 (by norm_num)
  have : Finite K := inferInstance
  let e1 : (Y ⧸ θ) ⧸ Subgroup.center (Y ⧸ θ) ≃* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient θ (Subgroup.center Y) hθZ)
  let e2 : (Y ⧸ θ) ⧸ Subgroup.center (Y ⧸ θ) ≃* StatedProj (StatedSU 5 (2 ^ 2) K) :=
    (e1.trans φ).trans (Sec4.projSUEquivStatedProj 5 2 2)
  let η : Y ⧸ θ →* StatedProj (StatedSU 5 (2 ^ 2) K) :=
    e2.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Y ⧸ θ)))
  have hη : Function.Surjective η := e2.surjective.comp (QuotientGroup.mk'_surjective _)
  have hηker : η.ker = Subgroup.center (Y ⧸ θ) := by
    ext x
    rw [MonoidHom.mem_ker]
    change e2 (x : (Y ⧸ θ) ⧸ Subgroup.center (Y ⧸ θ)) = 1 ↔ _
    rw [map_eq_one_iff _ e2.injective, QuotientGroup.eq_one_iff]
  have hZ5 := isPGroup_center_quot_theta5 hY
  obtain ⟨⟨ψ, hψ, -⟩, hall⟩ :=
    CFSG.RankThree.CentralLift.even_field_unitary_perfect_central_large_prime_scalar_cover
      (p := 5) hp5 (by norm_num) hU (by norm_num : 3 ≤ 5) η hη (hηker ▸ le_rfl)
      (hηker ▸ hZ5)
  obtain ⟨hψs, hψker, hDmap, -⟩ := hall ψ hψ
  have hrel : 5 ∣ ψ.ker.relIndex ((StatedScalars (Fin 5) K).subgroupOf
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 2 K 5)) := by
    rw [Subgroup.relIndex_ker]
    change 5 ∣ Nat.card (((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)).map ψ)
    rw [hDmap, hηker]
    exact h5L
  obtain ⟨-, -, -, hloc, -⟩ := CFSG.RankThree.Classical.even_unitary_surviving_scalar_local_rank
    hp5 (by norm_num) hU (by norm_num) ψ.ker hψker hrel
  have e3 : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 2 K 5 ⧸ ψ.ker ≃* Y ⧸ θ :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  rw [Census.localRank_eq_of_mulEquiv e3 hp5] at hloc
  have hle := CFSG.RankThree.Classical2.localRank_quotient_le hp5 (by norm_num) θ hθ5
  have hlt := hS.localRank_lt 5 hp5 (by norm_num)
  omega

end CFSG.RankThree.PartTwo.Sec4.Res417Four

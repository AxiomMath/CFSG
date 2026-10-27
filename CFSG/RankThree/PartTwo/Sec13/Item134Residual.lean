module

public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section General

variable {X : Type*} [Group X]

theorem eq_one_of_pow_three_pow_of_not_dvd {N : Subgroup X} [Finite N]
    (hN : ¬ 3 ∣ Nat.card N) {x : X} (hx : x ∈ N) {k : ℕ} (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hcop : Nat.Coprime (3 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  have h3 : orderOf x ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem pow_three_pow_mul_eq_one {x y : X} (hxy : Commute x y) {i j : ℕ} (hx : x ^ 3 ^ i = 1)
    (hy : y ^ 3 ^ j = 1) : (x * y) ^ 3 ^ (i + j) = 1 := by
  rw [hxy.mul_pow, pow_add, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

end General

section Theta

theorem aschbacherSolvableCore_eq_bot_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) (hZ : IsPGroup 3 (Subgroup.center Q)) :
    aschbacherSolvableCore 3 Q = ⊥ := by
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Q) Nat.prime_three
  have hqo : CFSG.Open.IsQuasisimple Q :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQ
  have hle : aschbacherSolvableCore 3 Q ≤ Subgroup.center Q := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqo
      (aschbacherSolvableCore 3 Q) with h | h
    · exact h
    · exfalso
      have hsol : Group.IsSolvable ↥(aschbacherSolvableCore 3 Q) := hθs
      have hsol' : Group.IsSolvable Q := by
        rw [h] at hsol
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom) (MulEquiv.surjective _)
      have : Group.IsPerfect Q := hQ.1
      have : Nontrivial Q := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
      exact (Group.IsPerfect.not_isSolvable Q) hsol'
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hZ ⟨x, hle hx⟩
  exact (Subgroup.mem_bot).mpr
    (eq_one_of_pow_three_pow_of_not_dvd hθp hx (by simpa using congrArg Subtype.val hk))

theorem aschbacherSolvableCore_eq_ker {Y Q : Type*} [Group Y] [Group Q] [Finite Y] [Finite Q]
    (f : Y →* Q) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (hk3 : ¬ 3 ∣ Nat.card f.ker) (hQ : aschbacherSolvableCore 3 Q = ⊥) :
    aschbacherSolvableCore 3 Y = f.ker := by
  obtain ⟨hθs, -, hθp, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  refine le_antisymm ?_ (hθmax _ f.normal_ker hks hk3)
  have hmax := (solvable_prime_complement_core_characterization (H := Q) Nat.prime_three).2.2.2.1
  have hn : ((aschbacherSolvableCore 3 Y).map f).Normal :=
    (aschbacherSolvableCore_normal 3 Y).map f hf
  have hs : Group.IsSolvable ((aschbacherSolvableCore 3 Y).map f) := by
    have := hθs
    exact Group.isSolvable_of_surjective (f.subgroupMap_surjective _)
  have hp : ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3 Y).map f) := fun h3 =>
    hθp (h3.trans (Subgroup.card_map_dvd _ f))
  have h := hmax _ hn hs hp
  rw [hQ, le_bot_iff, Subgroup.map_eq_bot_iff] at h
  exact h

theorem nonempty_quotTheta_equiv_of_surjective {Y Q : Type*} [Group Y] [Group Q] [Finite Y]
    [Finite Q] (f : Y →* Q) (hf : Function.Surjective f) (hks : Group.IsSolvable f.ker)
    (hk3 : ¬ 3 ∣ Nat.card f.ker) (hQ : aschbacherSolvableCore 3 Q = ⊥) :
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* Q) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (aschbacherSolvableCore_eq_ker f hf hks hk3 hQ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end Theta

section Kernel

theorem ker_facts_of_injective {Y Q Z : Type*} [Group Y] [Group Q] [Group Z]
    (f : Y →* Q) (g : Y →* Z) (hg : Function.Injective g) (N : Subgroup Z)
    (hfg : ∀ y, f y = 1 → g y ∈ N) (hNs : Group.IsSolvable N) (hN3 : ¬ 3 ∣ Nat.card N) :
    Group.IsSolvable f.ker ∧ ¬ 3 ∣ Nat.card f.ker := by
  let φ : f.ker →* N := (g.comp f.ker.subtype).codRestrict N fun y => hfg y y.2
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext (hg (congrArg Subtype.val hab))
  refine ⟨?_, fun h3 => hN3 (h3.trans (Subgroup.card_dvd_of_injective φ hφ))⟩
  have := hNs
  exact Group.isSolvable_of_isSolvable_injective hφ

end Kernel

section Lambda

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem bar_facts_of_central {z : Λ} (hz1 : z ≠ 1)
    (hz : ∃ S : Sylow 3 Λ, z ∈ (S : Subgroup Λ) ∧
      (S : Subgroup Λ) ≤ Subgroup.centralizer ({z} : Set Λ)) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) z ≠ 1 ∧
      ∃ P' : Sylow 3 (Λ ⧸ aschbacherSolvableCore 3 Λ),
        QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) z ∈ (P' : Subgroup _) ∧
        (P' : Subgroup _) ≤
          Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) z} : Set _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hzS, hSz⟩ := hz
  set N := aschbacherSolvableCore 3 Λ with hN
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hθp := (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
  refine ⟨fun h => hz1 ?_, S.mapSurjective hπs, ?_, ?_⟩
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨z, hzS⟩
    exact eq_one_of_pow_three_pow_of_not_dvd hθp h (by simpa using congrArg Subtype.val hk)
  · rw [Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_of_mem π hzS
  · rw [Sylow.coe_mapSurjective]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hSz hy)]

theorem map_residual_centralizer_eq (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (Λ ⧸ aschbacherSolvableCore 3 Λ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : Λ} (hz1 : z ≠ 1)
    (hz : ∃ S : Sylow 3 Λ, z ∈ (S : Subgroup Λ) ∧
      (S : Subgroup Λ) ≤ Subgroup.centralizer ({z} : Set Λ)) :
    (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 Λ)) =
      Subgroup.centralizer ({QuotientGroup.mk' (aschbacherSolvableCore 3 Λ) z} : Set _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hz1', hzP⟩ := bar_facts_of_central hz1 hz
  set N := aschbacherSolvableCore 3 Λ with hN
  set π := QuotientGroup.mk' N with hπ
  have hθp := (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
  obtain ⟨S, hzS, -⟩ := hz
  have hz3 : IsPGroup 3 (Subgroup.zpowers z) := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hzS)
  have hCmap : (Subgroup.centralizer ({z} : Set Λ)).map π =
      Subgroup.centralizer ({π z} : Set (Λ ⧸ N)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 N hθp
      (Subgroup.zpowers z) hz3
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  set CL := Subgroup.centralizer ({z} : Set Λ) with hCL
  set Cbar := Subgroup.centralizer ({π z} : Set (Λ ⧸ N)) with hCbar
  have htop : perfectResidual ↥Cbar = ⊤ :=
    KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hJ2 hz1' hzP
  let ψ : ↥CL →* ↥Cbar := (π.comp CL.subtype).codRestrict Cbar fun c =>
    hCmap ▸ Subgroup.mem_map_of_mem π c.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    rw [← hCmap] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact ⟨⟨c, hc⟩, rfl⟩
  have h : (perfectResidual ↥CL).map ψ = perfectResidual ↥Cbar :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
  rw [htop] at h
  have hcomp : π.comp CL.subtype = Cbar.subtype.comp ψ := rfl
  rw [inSubgroup, Subgroup.map_map, hcomp, ← Subgroup.map_map, h, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem residual_quotTheta_facts (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (Λ ⧸ aschbacherSolvableCore 3 Λ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : Λ} (hz1 : z ≠ 1)
    (hz : ∃ S : Sylow 3 Λ, z ∈ (S : Subgroup Λ) ∧
      (S : Subgroup Λ) ≤ Subgroup.centralizer ({z} : Set Λ)) :
    IsQuasisimple (↥(inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)))) ∧
      Sec4.IsTripleCover (↥(inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ))))
        (alternatingGroup (Fin 6)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJQ := map_residual_centralizer_eq h415 hJ2 hz1 hz
  obtain ⟨hz1', hzP⟩ := bar_facts_of_central hz1 hz
  set N := aschbacherSolvableCore 3 Λ with hN
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three
  set Cbar := Subgroup.centralizer ({π z} : Set (Λ ⧸ N)) with hCbar
  set J' := inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)) with hJ'
  have htop : perfectResidual ↥Cbar = ⊤ :=
    KFacts.KS14.j2_perfectResidual_centralizer_eq_top h415 hJ2 hz1' hzP
  have hCtc : Sec4.IsTripleCover ↥Cbar (alternatingGroup (Fin 6)) :=
    KFacts.KS14.j2_centralizer_isTripleCover h415 hJ2 hz1' hzP
  have hCq : IsQuasisimple ↥Cbar :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      (Sec14.j2_centralizer_residual_quasisimple h415 hJ2 hz1' hzP)
  have hCθ : aschbacherSolvableCore 3 ↥Cbar = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_isQuasisimple hCq
      (IsPGroup.of_card (n := 1) (by rw [hCtc.1, pow_one]))
  let ρ : ↥J' →* ↥Cbar := (π.comp J'.subtype).codRestrict Cbar fun x =>
    hJQ ▸ Subgroup.mem_map_of_mem π x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨hks, hk3⟩ := ker_facts_of_injective ρ J'.subtype J'.subtype_injective N
    (fun y hy => by
      have h2 : π (y : Λ) = 1 := congrArg Subtype.val hy
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2) hθs hθp
  obtain ⟨e⟩ := nonempty_quotTheta_equiv_of_surjective ρ hρ hks hk3 hCθ
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hCq,
    isTripleCover_of_mulEquiv e.symm hCtc⟩

theorem mem_residual_centralizer (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (Λ ⧸ aschbacherSolvableCore 3 Λ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : Λ} (hz1 : z ≠ 1)
    (hz : ∃ S : Sylow 3 Λ, z ∈ (S : Subgroup Λ) ∧
      (S : Subgroup Λ) ≤ Subgroup.centralizer ({z} : Set Λ)) :
    z ∈ inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJQ := map_residual_centralizer_eq h415 hJ2 hz1 hz
  set N := aschbacherSolvableCore 3 Λ with hN
  set π := QuotientGroup.mk' N with hπ
  have hθp := (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
  set J' := inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)) with hJ'
  have hJC : J' ≤ Subgroup.centralizer ({z} : Set Λ) := Subgroup.map_subtype_le _
  obtain ⟨S, hzS, -⟩ := hz
  obtain ⟨j, hj⟩ := S.isPGroup' ⟨z, hzS⟩
  have hzj : z ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hB : IsPGroup 3 (Subgroup.zpowers (π z)) :=
    (S.isPGroup'.map π).to_le (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem π hzS))
  have hBM : Subgroup.zpowers (π z) ≤ J'.map π := by
    rw [hJQ]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨R, -, hRJ, hR3, hRB⟩ := exists_isPGroup_le_map_eq hB hBM IsPGroup.of_bot bot_le
    (by rw [Subgroup.map_bot]; exact bot_le)
  have hzR : π z ∈ R.map π := hRB ▸ Subgroup.mem_zpowers _
  obtain ⟨r, hr, hrz⟩ := hzR
  have hrc : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hJC (hRJ hr))
  obtain ⟨i, hi⟩ := hR3 ⟨r, hr⟩
  have hri : r ^ 3 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hθ : r⁻¹ * z ∈ N := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hrz
    exact QuotientGroup.eq.mp hrz
  have h1 : (r⁻¹ * z) ^ 3 ^ (i + j) = 1 :=
    pow_three_pow_mul_eq_one (Commute.inv_left hrc) (by rw [inv_pow, hri, inv_one]) hzj
  have h2 := eq_one_of_pow_three_pow_of_not_dvd hθp hθ h1
  rw [inv_mul_eq_one] at h2
  rw [← h2]
  exact hRJ hr

theorem mem_zpowers_of_mem_residual_centralizer (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (Λ ⧸ aschbacherSolvableCore 3 Λ ≃* CFSG.Blueprint.NativeSporadic.J2))
    {z : Λ} (hz1 : z ≠ 1)
    (hz : ∃ S : Sylow 3 Λ, z ∈ (S : Subgroup Λ) ∧
      (S : Subgroup Λ) ≤ Subgroup.centralizer ({z} : Set Λ)) {x : Λ}
    (hxJ : x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)))
    (hxC : x ∈ Subgroup.centralizer
      ((inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)) : Subgroup Λ) : Set Λ))
    {k : ℕ} (hk : x ^ 3 ^ k = 1) : x ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJQ := map_residual_centralizer_eq h415 hJ2 hz1 hz
  obtain ⟨hz1', hzP⟩ := bar_facts_of_central hz1 hz
  set N := aschbacherSolvableCore 3 Λ with hN
  set π := QuotientGroup.mk' N with hπ
  have hθp := (solvable_prime_complement_core_characterization (H := Λ) Nat.prime_three).2.2.1
  set J' := inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set Λ)) with hJ'
  set Cbar := Subgroup.centralizer ({π z} : Set (Λ ⧸ N)) with hCbar
  have hcen := KFacts.KS14.j2_center_centralizer h415 hJ2 hz1' hzP
  have hJC : J' ≤ Subgroup.centralizer ({z} : Set Λ) := Subgroup.map_subtype_le _
  obtain ⟨S, hzS, -⟩ := hz
  obtain ⟨j, hj⟩ := S.isPGroup' ⟨z, hzS⟩
  have hzj : z ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hxCbar : π x ∈ Cbar := hJQ ▸ Subgroup.mem_map_of_mem π hxJ
  have hxZ : (⟨π x, hxCbar⟩ : ↥Cbar) ∈ Subgroup.center ↥Cbar := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    apply Subtype.ext
    change π y * π x = π x * π y
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxC y hy]
  rw [hcen, Subgroup.mem_subgroupOf] at hxZ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  have hθ : x⁻¹ * z ^ m ∈ N := by
    have hm' : π x = π (z ^ m) := by rw [map_zpow]; exact hm.symm
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hm'
    exact QuotientGroup.eq.mp hm'
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hJC hxJ)
  have h1 : (x⁻¹ * z ^ m) ^ 3 ^ (k + j) = 1 := by
    refine pow_three_pow_mul_eq_one ((Commute.zpow_right hxz m).inv_left)
      (by rw [inv_pow, hk, inv_one]) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzj, one_zpow]
  have h2 := eq_one_of_pow_three_pow_of_not_dvd hθp hθ h1
  rw [inv_mul_eq_one] at h2
  rw [h2]
  exact Subgroup.zpow_mem_zpowers z m

end Lambda


section GSide

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem residual_inf_centralizer_eq_map {d : G} (hdL : d ∈ L) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) =
      (inSubgroup perfectResidual (Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L))).map
        L.subtype := by
  rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      L.subtype L.subtype_injective,
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]

theorem residual_facts (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L)) :
    IsQuasisimple (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
        aschbacherSolvableCore 3 ↥(inSubgroup perfectResidual
          (L ⊓ Subgroup.centralizer ({d} : Set G)))) ∧
      Sec4.IsTripleCover (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
        aschbacherSolvableCore 3 ↥(inSubgroup perfectResidual
          (L ⊓ Subgroup.centralizer ({d} : Set G)))) (alternatingGroup (Fin 6)) ∧
      d ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ∧
      ∀ x ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)),
        x ∈ Subgroup.centralizer
          ((inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) : Subgroup G) :
            Set G) →
        ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ Subgroup.zpowers d := by
  have hd'1 : (⟨d, hdL⟩ : ↥L) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  rw [residual_inf_centralizer_eq_map hdL]
  set J' := inSubgroup perfectResidual (Subgroup.centralizer ({(⟨d, hdL⟩ : ↥L)} : Set ↥L))
    with hJ'
  obtain ⟨hq, htc⟩ := residual_quotTheta_facts h415 hJ2 hd'1 hc
  let e := J'.equivMapOfInjective L.subtype L.subtype_injective
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Sec14.quotThetaEquiv e) hq,
    isTripleCover_of_mulEquiv (Sec14.quotThetaEquiv e) htc,
    ⟨_, mem_residual_centralizer h415 hJ2 hd'1 hc, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxC k hk
  have hx' : x ∈ Subgroup.centralizer (J' : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : G) ⟨y, hy, rfl⟩)
  have hk' : x ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_mem_residual_centralizer h415 hJ2 hd'1 hc hx hx' hk')
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [← hm]; rfl⟩

end GSide


end CFSG.RankThree.PartTwo.Sec13

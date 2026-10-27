module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Aux
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

theorem isQuasisimple_thetaQuot_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (hA : CFSG.IsQuasisimple (A ⧸ aschbacherSolvableCore 3 A)) :
    CFSG.IsQuasisimple (B ⧸ aschbacherSolvableCore 3 B) :=
  LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hA

namespace J2Facts

variable {J : Type} [Group J]

theorem isQuasisimple (hJ : J2Facts J) : CFSG.IsQuasisimple J := by
  haveI := hJ.simple
  haveI := hJ.perfect
  let e : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hJ.center).trans QuotientGroup.quotientBot
  have hnc : ∃ a b : J, a * b ≠ b * a := by
    by_contra hcon
    push_neg at hcon
    haveI : Group.IsSolvable J := Group.isSolvable_of_comm hcon
    exact Group.IsPerfect.not_isSolvable J inferInstance
  refine ⟨hJ.perfect, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem exists_thetaQuot_equiv (hJ : J2Facts J) {M : Type*} [Group M] [Finite M] (ρ : M →* J)
    (hρ : Function.Surjective ρ) (hsol : Group.IsSolvable ρ.ker) (h3 : ¬ 3 ∣ Nat.card ρ.ker) :
    Nonempty (M ⧸ aschbacherSolvableCore 3 M ≃* J) := by
  have hθ := solvable_prime_complement_core_characterization (H := M) Nat.prime_three
  have h1 : ρ.ker ≤ aschbacherSolvableCore 3 M := hθ.2.2.2.1 ρ.ker inferInstance hsol h3
  have h2 : aschbacherSolvableCore 3 M ≤ ρ.ker := hJ.le_ker_of_solvable ρ hρ _ hθ.1
  have heq : aschbacherSolvableCore 3 M = ρ.ker := le_antisymm h2 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

theorem residual_component (hJ : J2Facts J) {X : Type*} [Group X] [Finite X] (ρ : X →* J)
    (hρ : Function.Surjective ρ) (hsol : Group.IsSolvable ρ.ker) (h3 : ¬ 3 ∣ Nat.card ρ.ker) :
    Function.Surjective (ρ.comp (perfectResidual X).subtype) ∧
    CFSG.IsQuasisimple (↥(perfectResidual X) ⧸ aschbacherSolvableCore 3 ↥(perfectResidual X)) ∧
    ∀ d : X, d ^ 3 = 1 → d ∈ perfectResidual X := by
  haveI := hJ.perfect
  haveI := hJ.finite
  obtain ⟨-, hchar, -⟩ := perfect_residual_characterization (G := X)
  have hrange : ρ.range = ⊤ := MonoidHom.range_eq_top.mpr hρ
  have hperfT : Group.IsPerfect ρ.range := by rw [hrange]; infer_instance
  have hRJ : (perfectResidual X).map ρ = ⊤ := by
    have h1 := (perfect_residual_transport ρ).1
    have h2 : (perfectResidual ρ.range).map ρ.range.subtype = ρ.range :=
      inSubgroup_perfectResidual_of_isPerfect hperfT
    rw [h1, h2, hrange]
  have hsurj : Function.Surjective (ρ.comp (perfectResidual X).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hRJ
  have hker : Group.IsSolvable (ρ.comp (perfectResidual X).subtype).ker ∧
      ¬ 3 ∣ Nat.card (ρ.comp (perfectResidual X).subtype).ker := by
    haveI := hsol
    let f : (ρ.comp (perfectResidual X).subtype).ker →* ρ.ker :=
      ((perfectResidual X).subtype.comp
        (ρ.comp (perfectResidual X).subtype).ker.subtype).codRestrict ρ.ker (fun x => x.2)
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun x : ρ.ker => (x : X)) hab))
    exact ⟨Group.isSolvable_of_isSolvable_injective hf,
      fun h => h3 (h.trans (Subgroup.card_dvd_of_injective f hf))⟩
  obtain ⟨e⟩ := hJ.exists_thetaQuot_equiv (ρ.comp (perfectResidual X).subtype) hsurj hker.1 hker.2
  refine ⟨hsurj, LocalCores.isQuasisimple_of_mulEquiv e.symm hJ.isQuasisimple, fun d hd3 => ?_⟩
  obtain ⟨m, hm, hρm⟩ : ∃ m ∈ perfectResidual X, ρ m = ρ d := by
    have : ρ d ∈ (perfectResidual X).map ρ := hRJ ▸ Subgroup.mem_top _
    exact this
  have ht : d * m⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρm, mul_inv_cancel]
  have hq1 : QuotientGroup.mk' (perfectResidual X) (d * m⁻¹) =
      QuotientGroup.mk' (perfectResidual X) d := by
    have hm1 : QuotientGroup.mk' (perfectResidual X) m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [map_mul, map_inv, hm1, inv_one, mul_one]
  have h1 : orderOf (QuotientGroup.mk' (perfectResidual X) (d * m⁻¹)) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (by rw [hq1, ← map_pow, hd3, map_one])
  have h2 : orderOf (QuotientGroup.mk' (perfectResidual X) (d * m⁻¹)) ∣ Nat.card ρ.ker :=
    (orderOf_map_dvd _ _).trans (Subgroup.orderOf_dvd_natCard _ ht)
  have hcop : Nat.Coprime 3 (Nat.card ρ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have h4 : orderOf (QuotientGroup.mk' (perfectResidual X) (d * m⁻¹)) = 1 := by
    have := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have h5 := orderOf_eq_one_iff.mp h4
  have h6 : d * m⁻¹ ∈ perfectResidual X := (QuotientGroup.eq_one_iff _).mp h5
  have h7 := (perfectResidual X).mul_mem h6 hm
  rwa [inv_mul_cancel_right] at h7

end J2Facts

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

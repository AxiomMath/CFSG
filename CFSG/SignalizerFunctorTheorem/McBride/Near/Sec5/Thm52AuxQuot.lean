module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Basic
public import CFSG.SignalizerFunctorTheorem.NearModels.Main

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

section Model

variable {Γ : Type*} [Group Γ]

theorem isSolvable_inf_centralizer_of_model
    {p : ℕ} (hp : p.Prime) {J : Subgroup Γ} {b : Γ}
    [Finite J] (hmodel : signalizerNearSimpleModel p ↥J) (hcop : Nat.Coprime p (Nat.card J))
    (hbJ : b ∈ Subgroup.normalizer (J : Set Γ)) (hbp : b ^ p = 1)
    (hnc : ¬ J ≤ Subgroup.centralizer {b}) :
    Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b}) := by
  have : Fact p.Prime := ⟨hp⟩
  let f : MulAut ↥J := J.normalizerMonoidHom ⟨b, hbJ⟩
  have hfc : ∀ t : J, ((f t : J) : Γ) = b * t * b⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe J ⟨b, hbJ⟩
  have hf1 : f ≠ 1 := by
    intro h1
    refine hnc fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h2 : (t : Γ) = b * t * b⁻¹ := by simpa [h1] using hfc ⟨t, ht⟩
    calc t * b = b * t * b⁻¹ * b := by rw [← h2]
      _ = b * t := by group
  have hfp : f ^ p = 1 := by
    rw [← map_pow]
    have : (⟨b, hbJ⟩ : Subgroup.normalizer (J : Set Γ)) ^ p = 1 :=
      Subtype.ext (by simpa using hbp)
    rw [this, map_one]
  have hf : orderOf f = p := orderOf_eq_prime hfp hf1
  have hsol := NearModels.nearSimpleModel_fixedSubgroup_solvable hp hmodel hcop f hf
  have hfix : ∀ x : ↥(J ⊓ Subgroup.centralizer {b}),
      Subgroup.inclusion (inf_le_left : J ⊓ Subgroup.centralizer {b} ≤ J) x ∈
        signalizerFixedSubgroup f := by
    intro x
    obtain ⟨hxJ, hxc⟩ := Subgroup.mem_inf.mp x.2
    show f ⟨x, hxJ⟩ = ⟨x, hxJ⟩
    refine Subtype.ext ?_
    rw [hfc]
    have := Subgroup.mem_centralizer_singleton_iff.mp hxc
    change b * (x : Γ) * b⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion (inf_le_left : J ⊓ Subgroup.centralizer {b} ≤ J)).codRestrict _ hfix)
    fun x y h => Subtype.ext (congrArg (fun z : ↥(signalizerFixedSubgroup f) => ((z : J) : Γ)) h)

end Model

section Quotient

variable {Γ : Type u} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isSectionOf_of_mem_lcal_qimg {R Y : Subgroup Γ} {J : Subgroup (AChief.QG R)}
    (hYN : Y ≤ AChief.nrm R) (hJ : J ∈ lcal (AChief.qimg R Y)) : IsSectionOf ↥J ↥Y :=
  (isSectionOf_of_le (mem_lcal_iff.mp hJ).1 (IsSectionOf.refl ↥J)).trans
    (IsSectionOf.of_surjective (SolQuot.qres R Y hYN) (SolQuot.qres_surjective hYN))

theorem isSolvable_inf_centralizer_qimg
    {p : ℕ} (hp : p.Prime) {R Y : Subgroup Γ}
    (hYN : Y ≤ AChief.nrm R) (hnear : signalizerNearPSolvable p ↥Y)
    {b : AChief.QG R} (hbp : b ^ p = 1) {J : Subgroup (AChief.QG R)}
    (hJ : J ∈ lcal (AChief.qimg R Y)) (hbJ : b ∈ Subgroup.normalizer (J : Set (AChief.QG R)))
    (hnc : ¬ J ≤ Subgroup.centralizer {b}) : Group.IsSolvable ↥(J ⊓ Subgroup.centralizer {b}) := by
  obtain ⟨hJZ, -, hs, hJnc⟩ := mem_lcal_iff.mp hJ
  have hnc' : ∃ x y : ↥J, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact hJnc (isMulCommutative_iff.mpr hcon)
  have hsec := isSectionOf_of_mem_lcal_qimg hYN hJ
  obtain ⟨hcopY, hmodel⟩ := signalizerNearPSolvable_iff.mp hnear
  have hcop : Nat.Coprime p (Nat.card J) := by
    refine hcopY.coprime_dvd_right ?_
    exact (Subgroup.card_dvd_of_le hJZ).trans
      (Subgroup.card_dvd_of_surjective (SolQuot.qres_surjective hYN))
  exact isSolvable_inf_centralizer_of_model hp (hmodel ↥J hsec hnc') hcop hbJ hbp hnc

end Quotient

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm52Aux

module

public import CFSG.RankThree.PartTwo.KFacts.KS18M12
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem ks18M12 :
    KS18M12 := by
  intro X _ _ ⟨e⟩
  have hsM : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hsX : IsSimpleGroup X := e.isSimpleGroup
  obtain ⟨-, -, -, hc6, -, -, -⟩ := CFSG.Sporadic.Schreier.at_m12_image_pair_count
  have habM : CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b ≠
      CFSG.Sporadic.Mathieu.m12b * CFSG.Sporadic.Mathieu.m12a :=
    CFSG.Sporadic.Schreier.mul_ne_mul_of_orderOf_commutator hc6 (by norm_num)
  have habX : e.symm CFSG.Sporadic.Mathieu.m12a * e.symm CFSG.Sporadic.Mathieu.m12b ≠
      e.symm CFSG.Sporadic.Mathieu.m12b * e.symm CFSG.Sporadic.Mathieu.m12a := by
    intro h
    apply habM
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h
  refine ⟨?_, CFSG.Sporadic.Schreier.center_eq_bot_of_simple hsX habX, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.m12_card]
    norm_num
  · rintro σ ⟨k, hk⟩
    set σ' : MulAut NativeSporadic.M12 := MulAut.congr e σ with hσ'
    have hk' : σ' ^ 3 ^ k = 1 := by
      rw [hσ', ← map_pow, hk, map_one]
    set o : Outer NativeSporadic.M12 := QuotientGroup.mk σ' with ho
    have hdvd3 : orderOf o ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [ho, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
    have hdvd2 : orderOf o ∣ 2 := by
      rw [← CFSG.ComponentClassification.M12Cover.card_outer]
      exact orderOf_dvd_natCard o
    have h1 : orderOf o = 1 := by
      have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
      have h := Nat.dvd_gcd hdvd3 hdvd2
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      exact Nat.dvd_one.mp h
    have hinner :
        σ' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M12 := by
      rw [← QuotientGroup.eq_one_iff, ← orderOf_eq_one_iff]
      exact h1
    obtain ⟨m, hm⟩ := hinner
    refine ⟨e.symm m, ?_⟩
    apply MulEquiv.ext
    intro x
    have hx := congrArg (fun f : MulAut NativeSporadic.M12 => f (e x)) hm
    change m * e x * m⁻¹ = e (σ (e.symm (e x))) at hx
    rw [MulEquiv.symm_apply_apply] at hx
    change σ x = e.symm m * x * (e.symm m)⁻¹
    apply e.injective
    rw [← hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · intro N hN hsol
    have := hN
    rcases hsX.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      subst h
      have hX : Group.IsSolvable X :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).toMonoidHom)
          Subgroup.topEquiv.surjective
      exact habX ((IsSimpleGroup.comm_iff_isSolvable.mpr hX) _ _)

end CFSG.RankThree.PartTwo.KFacts

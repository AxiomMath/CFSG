module

public import CFSG.Permutation.FiveTransitive.A9PrimeFreeOrbitImage

public section

namespace CFSG

namespace FiveTransitive.A9SevenFreeOrbitImage
open A9PrimeFreeOrbitImage
variable {L F E : Type} [Group L] [Fintype F] [DecidableEq F]

private theorem seven_not_dvd_kernel [Finite L]
    (rho : L →* Equiv.Perm F) (sigma : L →* Equiv.Perm E)
    (hfree : ¬ 7 ∣ Nat.card sigma.ker) : ¬ 7 ∣ Nat.card (labelHom rho sigma).ker := by
  let j : (labelHom rho sigma).ker →* sigma.ker :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    have hh : x.val.val = y.val.val := congrArg (fun z : sigma.ker => z.val) he
    exact Subtype.ext (Subtype.ext hh)
  intro hd
  exact hfree (hd.trans (Subgroup.card_dvd_of_injective j hj))

private theorem kernel_le [Finite L]
    (hF : Nat.card F = 9) (rho : L →* Equiv.Perm F)
    (hAlt : alternatingGroup F ≤ rho.range) (sigma : L →* Equiv.Perm E)
    (hfree : ¬ 7 ∣ Nat.card sigma.ker) :
    (labelHom rho sigma).ker ≤ (fixedHom rho).ker := by
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  apply SimplePrimeFreeKernel.ker_le (fixedHom rho) (fixedHom_surjective rho hAlt)
    (labelHom rho sigma) 7
  · rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  · exact seven_not_dvd_kernel rho sigma hfree

theorem exists_surjective_factor [Finite L]
    (hF : Nat.card F = 9) (rho : L →* Equiv.Perm F)
    (hAlt : alternatingGroup F ≤ rho.range) (sigma : L →* Equiv.Perm E)
    (hfree : ¬ 7 ∣ Nat.card sigma.ker) :
    ∃ r : (labelHom rho sigma).range →* alternatingGroup F,
      Function.Surjective r ∧ ∀ n : AltPreimage rho,
        r ((labelHom rho sigma).rangeRestrict n) = fixedHom rho n := by
  exact SimplePrimeFreeKernel.exists_surjective_range_factor
    (fixedHom rho) (fixedHom_surjective rho hAlt) (labelHom rho sigma)
    (kernel_le hF rho hAlt sigma hfree)

theorem exists_seven_with_label_order [Finite L]
    (hF : Nat.card F = 9) (rho : L →* Equiv.Perm F)
    (hAlt : alternatingGroup F ≤ rho.range) (sigma : L →* Equiv.Perm E)
    (hfree : ¬ 7 ∣ Nat.card sigma.ker) :
    ∃ n : AltPreimage rho, orderOf n = 7 ∧ orderOf (labelHom rho sigma n) = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdiv : 7 ∣ Nat.card (alternatingGroup F) := by
    rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  obtain ⟨n,hn⟩ := exists_prime_orderOf_dvd_card' (G := AltPreimage rho) 7
    (hdiv.trans (Subgroup.card_dvd_of_surjective (fixedHom_surjective rho hAlt)))
  refine ⟨n,hn,?_⟩
  apply orderOf_eq_prime
  · rw [← map_pow,← hn,pow_orderOf_eq_one,map_one]
  · intro he
    let z : (labelHom rho sigma).ker := ⟨n,he⟩
    have hz : orderOf z = 7 := (Subgroup.orderOf_coe z).symm.trans hn
    exact seven_not_dvd_kernel rho sigma hfree (hz ▸ orderOf_dvd_natCard z)

end FiveTransitive.A9SevenFreeOrbitImage

end CFSG

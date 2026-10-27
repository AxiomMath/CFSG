module

public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.E3

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_involution_rkIdx_fixV_eq_mParam (X : Subgroup (MulAut W))
    (hX : Even (Nat.card X)) :
    ∃ t ∈ X, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) = mParam X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.1 hX)
    exact ⟨_, ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩⟩
  obtain ⟨t, htX, htord, htval⟩ := Nat.sInf_mem hne
  refine ⟨t, htX, htord, ?_⟩
  rw [mParam, if_pos hX]
  exact htval.symm

end CFSG.Quasithin.E3

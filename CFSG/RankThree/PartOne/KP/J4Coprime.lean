module

public import CFSG.Sporadic.Schreier.J4SOuter

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem j4_coprime_automorphism_subgroups_trivial (T : Type) [Group T] [Finite T]
    [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hJ4 : Nonempty (T ≃* Carrier .J4))
    (A : Subgroup (MulAut T)) (hA : Nat.Coprime (Nat.card A) (Nat.card T)) : A = ⊥ := by
  by_contra hne
  have hcen : Subgroup.center T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center T := by rw [h]; exact Subgroup.mem_top a
      exact absurd ((Subgroup.mem_center_iff.mp ha) b).symm hab
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : x ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun f : MulAut T => f z) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc z * x = (x * z * x⁻¹) * x := by rw [this]
        _ = x * z := by group
    rw [hcen] at hxc
    exact hxc
  have hA1 : Nat.card A ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq A h)
  obtain ⟨p, hp, hpA⟩ := Nat.exists_prime_and_dvd hA1
  have hpT : ¬ p ∣ Nat.card T := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hA hpA h)
  have hcardT : Nat.card T = 86775571046077562880 := by
    obtain ⟨e⟩ := hJ4
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have hlt' : p < 5 := not_le.1 hlt
    have h2 := hp.two_le
    interval_cases p
    · exact hpT (by rw [hcardT]; norm_num)
    · exact hpT (by rw [hcardT]; norm_num)
    · exact absurd hp (by norm_num)
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut T) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut T))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpA
  have hxo : orderOf (x : MulAut T) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hP : IsPGroup p (Subgroup.zpowers (x : MulAut T)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hin := (CFSG.Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes hJ4).2 p hp
    hp5 _ hP
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (hin (Subgroup.mem_zpowers (x : MulAut T)))
  have hog : orderOf g = p := by
    rw [← hxo, ← hg]
    exact (orderOf_injective _ hinj g).symm
  exact hpT (by rw [← hog]; exact orderOf_dvd_natCard g)

end CFSG.RankThree.PartOne

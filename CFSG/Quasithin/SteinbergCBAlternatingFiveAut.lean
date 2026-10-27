module

public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem A7_A5_odd_automorphism_subgroups_inner :
    center (alternatingGroup (Fin 5)) = ⊥ ∧
    (MulAut.conj : alternatingGroup (Fin 5) →* MulAut (alternatingGroup (Fin 5))).range.index ∣
      2 ∧
    ∀ H : Subgroup (MulAut (alternatingGroup (Fin 5))), Odd (Nat.card H) →
      H ≤ (MulAut.conj : alternatingGroup (Fin 5) →* MulAut (alternatingGroup (Fin 5))).range := by
  have hindex : (inner (alternatingGroup (Fin 5))).index ∣ 2 := index_inner_dvd_two (Or.inl rfl)
  refine ⟨alternatingGroup.center_eq_bot (by simp), hindex, fun H hH h hh => ?_⟩
  have : Finite (MulAut (alternatingGroup (Fin 5))) :=
    Finite.of_injective (fun f : MulAut (alternatingGroup (Fin 5)) =>
      (f : alternatingGroup (Fin 5) → alternatingGroup (Fin 5))) fun _ _ h =>
        MulEquiv.ext (congrFun h)
  set I := inner (alternatingGroup (Fin 5)) with hI
  have hIn : I.Normal := inner_normal _
  have h1 : orderOf (QuotientGroup.mk' I h) ∣ Nat.card H := by
    refine (orderOf_map_dvd _ h).trans ?_
    rw [← Subgroup.orderOf_mk h hh]
    exact _root_.orderOf_dvd_natCard _
  have h2 : orderOf (QuotientGroup.mk' I h) ∣ 2 :=
    (_root_.orderOf_dvd_natCard _).trans hindex
  have h3 : orderOf (QuotientGroup.mk' I h) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h' | h'
    · exact h'
    · rw [h'] at h1
      exact absurd (even_iff_two_dvd.2 h1) (Nat.not_even_iff_odd.2 hH)
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.Quasithin.SteinbergCB

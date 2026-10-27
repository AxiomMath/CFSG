module

public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem relIndex_le_mul [Finite G] {A U C : Subgroup G} (hAU : A ≤ U) :
    C.relIndex U ≤ A.relIndex U * C.relIndex A := by
  have h1 : (A ⊓ C).relIndex A * A.relIndex U = (A ⊓ C).relIndex U :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hAU
  rw [Subgroup.inf_relIndex_left] at h1
  have h2 : C.relIndex U ∣ (A ⊓ C).relIndex U := Subgroup.relIndex_dvd_of_le_left U inf_le_right
  rw [← h1, mul_comm] at h2
  have hpos : 0 < A.relIndex U * C.relIndex A := by
    refine Nat.mul_pos (Nat.pos_of_ne_zero ?_) (Nat.pos_of_ne_zero ?_)
    · exact Subgroup.index_ne_zero_of_finite
    · exact Subgroup.index_ne_zero_of_finite
  exact Nat.le_of_dvd hpos h2

theorem relIndex_le_mul_inf [Finite G] {P U C : Subgroup G} :
    C.relIndex U ≤ P.relIndex U * C.relIndex (P ⊓ U) := by
  have := relIndex_le_mul (A := P ⊓ U) (U := U) (C := C) inf_le_right
  rwa [Subgroup.inf_relIndex_right] at this

theorem relIndex_conjSub (g : G) (K L : Subgroup G) :
    (conjSub g K).relIndex (conjSub g L) = K.relIndex L :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) K L
    (MulEquiv.injective _)

theorem relIndex_centralizer_conjSub (g : G) (X U : Subgroup G) :
    (Subgroup.centralizer (conjSub g X : Set G)).relIndex (conjSub g U) =
      (Subgroup.centralizer (X : Set G)).relIndex U := by
  rw [conjSub_centralizer, relIndex_conjSub]

theorem le_lambdaOf_of_isElemAbelian {D Q : Subgroup G} (hD : IsElemAbelian 2 D) (hDQ : D ≤ Q) :
    D ≤ lambdaOf Q := by
  intro x hx
  by_cases h1 : x = 1
  · rw [h1]; exact Subgroup.one_mem _
  · apply Subgroup.subset_closure
    refine ⟨hDQ hx, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (F7.isElemAbelian_pow_eq_one hD hx) h1

theorem le_conjSub_lambdaOf {D Q : Subgroup G} (a : G) (hD : IsElemAbelian 2 D)
    (hDQ : D ≤ conjSub a Q) : D ≤ conjSub a (lambdaOf Q) := by
  rw [le_conjSub_iff]
  exact le_lambdaOf_of_isElemAbelian (F7.isElemAbelian_conjSub hD) ((le_conjSub_iff a).mp hDQ)

end S152Fin

end CFSG.Quasithin

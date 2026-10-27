module

public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass
public import Certificates.Certificate260405
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.Quasithin.B45Mat.M12

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
  CFSG.Certificates CFSG.Blueprint

abbrev oddReps : List (Equiv.Perm (Fin 12)) := oddReps3 ++ oddReps5 ++ oddReps11

theorem oddClass_checks :
    (∀ g ∈ NativeSporadic.M12, Odd (orderOf g) →
      g = 1 ∨ ∃ r ∈ oddReps, ∃ c ∈ NativeSporadic.M12, g = c * r * c⁻¹) ∧
    (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps11, orderOf r = 11) :=
  Certificates.certificate260405

theorem orderOf_oddReps :
    ∀ r ∈ oddReps, orderOf r ∈ [3, 5, 11] := by
  obtain ⟨-, h3, h5, h11⟩ := oddClass_checks
  intro r hr
  simp only [oddReps, List.mem_append, or_assoc] at hr
  rcases hr with hr | hr | hr
  · simp [h3 r hr]
  · simp [h5 r hr]
  · simp [h11 r hr]

theorem orderOf_mem_of_odd {g : Equiv.Perm (Fin 12)}
    (hg : g ∈ NativeSporadic.M12) (ho : Odd (orderOf g)) : orderOf g ∈ [1, 3, 5, 11] := by
  rcases oddClass_checks.1 g hg ho with rfl | ⟨r, hr, c, -, rfl⟩
  · simp
  · have e : orderOf (c * r * c⁻¹) = orderOf r := (MulAut.conj c).orderOf_eq r
    rw [e]
    exact List.mem_cons_of_mem _ (orderOf_oddReps r hr)

theorem orderOf_ne_of_mem
    {g : Equiv.Perm (Fin 12)} (hg : g ∈ m12Certificate.originalSubgroup) {m : ℕ}
    (hm : m ∈ [9, 15, 33, 55]) : orderOf g ≠ m := by
  intro ho
  rw [m12Certificate_originalSubgroup] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have hodd : Odd (orderOf g) := by
    rw [ho]
    rcases hm with rfl | rfl | rfl | rfl <;> decide
  have h := orderOf_mem_of_odd hg hodd
  rw [ho] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem orderOf_mem_of_isPRegular
    (g : ↥NativeSporadic.M12) (hg : IsPRegular 2 g) :
    orderOf g ∈ [1, 3, 5, 11] := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_mem_of_odd g.2 (by rw [Subgroup.orderOf_coe]; exact Nat.coprime_two_right.1 hg)

theorem exists_conj_of_isPRegular
    (g : ↥NativeSporadic.M12) (hg : IsPRegular 2 g) :
    ∃ r ∈ (1 : Equiv.Perm (Fin 12)) :: oddReps, ∃ c ∈ NativeSporadic.M12,
      (g : Equiv.Perm (Fin 12)) = c * r * c⁻¹ := by
  have ho : Odd (orderOf (g : Equiv.Perm (Fin 12))) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.1 hg
  rcases oddClass_checks.1 g g.2 ho with h | ⟨r, hr, c, hc, e⟩
  · exact ⟨1, List.mem_cons_self, 1, NativeSporadic.M12.one_mem, by rw [h]; simp⟩
  · exact ⟨r, List.mem_cons_of_mem _ hr, c, hc, e⟩

theorem card_pRegularClass_m12 :
    Fintype.card (PRegularClass 2 ↥NativeSporadic.M12) ≤ 6 := by
  classical
  have hrep : ∀ C : PRegularClass 2 ↥NativeSporadic.M12,
      ∃ r ∈ (1 : Equiv.Perm (Fin 12)) :: oddReps, ∃ c ∈ NativeSporadic.M12,
        ((PRegularClass.repr C : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = c * r * c⁻¹ :=
    fun C => exists_conj_of_isPRegular _ (PRegularClass.repr_isPRegular C)
  choose r hr c hc hrc using hrep
  let f : PRegularClass 2 ↥NativeSporadic.M12 →
      ↥((1 : Equiv.Perm (Fin 12)) :: oddReps).toFinset :=
    fun C => ⟨r C, List.mem_toFinset.2 (hr C)⟩
  have hinj : Function.Injective f := by
    intro C C' hCC'
    have hr' : r C = r C' := congrArg Subtype.val hCC'
    have hIsConj : IsConj (PRegularClass.repr C) (PRegularClass.repr C') := by
      rw [isConj_iff]
      refine ⟨⟨c C' * (c C)⁻¹, NativeSporadic.M12.mul_mem (hc C')
        (NativeSporadic.M12.inv_mem (hc C))⟩, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hrc C, hrc C', hr']
      group
    apply PRegularClass.ext
    have h1 : ConjClasses.mk (PRegularClass.repr C) = C.1 := Quotient.out_eq C.1
    have h2 : ConjClasses.mk (PRegularClass.repr C') = C'.1 := Quotient.out_eq C'.1
    rw [← h1, ← h2]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hIsConj
  have h := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe] at h
  exact h.trans (List.toFinset_card_le _)

end CFSG.Quasithin.B45Mat.M12

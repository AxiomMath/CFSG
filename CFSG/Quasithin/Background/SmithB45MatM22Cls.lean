module

public import CFSG.ThirdParty.BrauerInduction.Background.Group.PRegularClass
public import Certificates.Certificate260403
public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
  CFSG.Certificates CFSG.Blueprint

abbrev oddReps : List (Equiv.Perm (Fin 22)) := oddReps3 ++ oddReps5 ++ oddReps7 ++ oddReps11

theorem oddClass_checks :
    (∀ g ∈ NativeSporadic.M22, Odd (orderOf g) →
      g = 1 ∨ ∃ r ∈ oddReps, ∃ c ∈ NativeSporadic.M22, g = c * r * c⁻¹) ∧
    (∀ r ∈ oddReps3, orderOf r = 3) ∧ (∀ r ∈ oddReps5, orderOf r = 5) ∧
    (∀ r ∈ oddReps7, orderOf r = 7) ∧ (∀ r ∈ oddReps11, orderOf r = 11) :=
  Certificates.certificate260403

theorem orderOf_oddReps :
    ∀ r ∈ oddReps, orderOf r ∈ [3, 5, 7, 11] := by
  obtain ⟨-, h3, h5, h7, h11⟩ := oddClass_checks
  intro r hr
  simp only [oddReps, List.mem_append, or_assoc] at hr
  rcases hr with hr | hr | hr | hr
  · simp [h3 r hr]
  · simp [h5 r hr]
  · simp [h7 r hr]
  · simp [h11 r hr]

theorem orderOf_mem_of_odd {g : Equiv.Perm (Fin 22)}
    (hg : g ∈ NativeSporadic.M22) (ho : Odd (orderOf g)) : orderOf g ∈ [1, 3, 5, 7, 11] := by
  rcases oddClass_checks.1 g hg ho with rfl | ⟨r, hr, c, -, rfl⟩
  · simp
  · have e : orderOf (c * r * c⁻¹) = orderOf r := (MulAut.conj c).orderOf_eq r
    rw [e]
    exact List.mem_cons_of_mem _ (orderOf_oddReps r hr)

theorem orderOf_mem_of_isPRegular
    (g : ↥NativeSporadic.M22) (hg : IsPRegular 2 g) :
    orderOf g ∈ [1, 3, 5, 7, 11] := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_mem_of_odd g.2 (by rw [Subgroup.orderOf_coe]; exact Nat.coprime_two_right.1 hg)

theorem exists_conj_of_isPRegular
    (g : ↥NativeSporadic.M22) (hg : IsPRegular 2 g) :
    ∃ r ∈ (1 : Equiv.Perm (Fin 22)) :: oddReps, ∃ c ∈ NativeSporadic.M22,
      (g : Equiv.Perm (Fin 22)) = c * r * c⁻¹ := by
  have ho : Odd (orderOf (g : Equiv.Perm (Fin 22))) := by
    rw [Subgroup.orderOf_coe]
    exact Nat.coprime_two_right.1 hg
  rcases oddClass_checks.1 g g.2 ho with h | ⟨r, hr, c, hc, e⟩
  · exact ⟨1, List.mem_cons_self, 1, NativeSporadic.M22.one_mem, by rw [h]; simp⟩
  · exact ⟨r, List.mem_cons_of_mem _ hr, c, hc, e⟩

theorem card_pRegularClass_m22 :
    Fintype.card (PRegularClass 2 ↥NativeSporadic.M22) ≤ 7 := by
  classical
  have hrep : ∀ C : PRegularClass 2 ↥NativeSporadic.M22, ∃ r ∈ (1 : Equiv.Perm (Fin 22)) :: oddReps,
      ∃ c ∈ NativeSporadic.M22,
        ((PRegularClass.repr C : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) = c * r * c⁻¹ :=
    fun C => exists_conj_of_isPRegular _ (PRegularClass.repr_isPRegular C)
  choose r hr c hc hrc using hrep
  let f : PRegularClass 2 ↥NativeSporadic.M22 → ↥((1 : Equiv.Perm (Fin 22)) :: oddReps).toFinset :=
    fun C => ⟨r C, List.mem_toFinset.2 (hr C)⟩
  have hinj : Function.Injective f := by
    intro C C' hCC'
    have hr' : r C = r C' := congrArg Subtype.val hCC'
    have hIsConj : IsConj (PRegularClass.repr C) (PRegularClass.repr C') := by
      rw [isConj_iff]
      refine ⟨⟨c C' * (c C)⁻¹, NativeSporadic.M22.mul_mem (hc C')
        (NativeSporadic.M22.inv_mem (hc C))⟩, ?_⟩
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

end CFSG.Quasithin.B45Mat.M22

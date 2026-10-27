module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Setup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

@[expose] def eFourSum (i : Fin 5) : Fin 5 → ZMod 2 := Pi.single i 1 + Pi.single 4 1

theorem eq_sum_eFourSum : ∀ x : Fin 5 → ZMod 2, isEven x →
    x = ((if x 0 = 1 then eFourSum 0 else 0) + (if x 1 = 1 then eFourSum 1 else 0)) +
      ((if x 2 = 1 then eFourSum 2 else 0) + (if x 3 = 1 then eFourSum 3 else 0)) := by
  decide +kernel

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)} {θ : ↥K ≃* Equiv.Perm (Fin 5)}
  {β : ↥(commV K) ≃* Multiplicative (evenWeight 5)}

theorem commV_oTwoUpper_eq (hβ : A5Equivariant θ β) : commV (oTwoUpper K) = commV K := by
  classical
  refine le_antisymm (Subgroup.closure_mono ?_) fun w hw => ?_
  · rintro _ ⟨k, hk, v, rfl⟩
    exact ⟨k, oTwoUpper_le K hk, v, rfl⟩
  have hu : ∀ i : Fin 5, i ≠ 4 → ∃ (u : W) (hu : u ∈ commV K), u ∈ commV (oTwoUpper K) ∧
      ((Multiplicative.toAdd (β ⟨u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) = eFourSum i :=
    fun i hi => exists_mem_commV_oTwoUpper hβ hi
  choose u huK huO hcu using hu
  set x := ((Multiplicative.toAdd (β ⟨w, hw⟩) : evenWeight 5) : Fin 5 → ZMod 2)
  let g : (i : Fin 5) → i ≠ 4 → ↥(commV K) := fun i hi => if x i = 1 then ⟨u i hi, huK i hi⟩ else 1
  have hgO : ∀ i hi, ((g i hi : ↥(commV K)) : W) ∈ commV (oTwoUpper K) := by
    intro i hi
    by_cases h : x i = 1
    · simp only [g, h, ite_true]; exact huO i hi
    · simp only [g, h, ite_false]; exact Subgroup.one_mem _
  have hgc : ∀ i hi, ((Multiplicative.toAdd (β (g i hi)) : evenWeight 5) : Fin 5 → ZMod 2) =
      if x i = 1 then eFourSum i else 0 := by
    intro i hi
    by_cases h : x i = 1
    · simp only [g, h, ite_true]; exact hcu i hi
    · simp only [g, h, ite_false, map_one, toAdd_one]; rfl
  set p := (g 0 (by decide) * g 1 (by decide)) * (g 2 (by decide) * g 3 (by decide))
  have hp : β p = β ⟨w, hw⟩ := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [p, map_mul, toAdd_mul, AddSubgroup.coe_add, hgc]
    exact (eq_sum_eFourSum x (Multiplicative.toAdd (β ⟨w, hw⟩)).2).symm
  have hpw : (p : W) = w := congrArg Subtype.val (β.injective hp)
  rw [← hpw]
  simp only [p, Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgO _ _) (hgO _ _))
    (Subgroup.mul_mem _ (hgO _ _) (hgO _ _))

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

theorem mem_commV₁_iff (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    w ∈ commV D.K₁ ↔ w.val ∈ fsuUL T L I := by
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  rw [← commV_oTwoUpper_eq D.equiv₁, D.oTwo₁]
  refine ⟨val_mem_commutator_of_mem_commV _, fun h => ?_⟩
  have h1 := mk_mem_commV_of_mem_commutator (SecA.isElemAbelian_fsuVM hyp) hLN h w.val_mem
  exact h1

theorem mem_commV₂_iff (ht : t ∈ T) (w : IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :
    w ∈ commV D.K₂ ↔ w.val ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
  have hLN : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.conjugate_le_fsuL0 ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  rw [← commV_oTwoUpper_eq D.equiv₂, D.oTwo₂]
  refine ⟨val_mem_commutator_of_mem_commV _, fun h => ?_⟩
  have h1 := mk_mem_commV_of_mem_commutator (SecA.isElemAbelian_fsuVM hyp) hLN h w.val_mem
  exact h1

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE

module

public import CFSG.Quasithin.Background.B1MoreSevenB

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B1Red

section Offender

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_isFFStarMin_below {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    ∃ B, IsFFStarMin X B ∧ B ≤ A :=
  (B1.exists_isFFStarMin_le hA).imp fun _ h => ⟨h.2, h.1.2.2.1⟩

omit [Finite V] in
theorem fixV_inv_of_normalizes {B L : Subgroup (MulAut V)}
    (hn : ∀ b ∈ B, ∀ x ∈ L, b * x * b⁻¹ ∈ L) :
    ∀ b ∈ B, ∀ v ∈ fixV L, b v ∈ fixV L := by
  intro b hb v hv x hx
  have h1 := hv _ (hn b⁻¹ (B.inv_mem hb) x hx)
  have h2 : b⁻¹ (x (b v)) = v := by simpa [MulAut.mul_apply] using h1
  have h3 : x (b v) = b (b⁻¹ (x (b v))) := by simp
  rw [h3, h2]

end Offender

section Irr

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_mem_irrPlus {X : Subgroup (MulAut V)} (hX : ⁅X, X⁆ = X) (hne : commV X ≠ ⊥) :
    ∃ I, I ∈ IrrPlus X (⊤ : Subgroup V) := by
  classical
  let S : Set (Subgroup V) := {J | (∀ x ∈ X, ∀ w ∈ J, x w ∈ J) ∧ commSub J X ≠ ⊥}
  have hSne : S.Nonempty := ⟨⊤, fun _ _ _ _ => trivial, by rwa [← commV_eq_commSub]⟩
  obtain ⟨I, hI, hmin⟩ := Set.exists_min_image S (fun J => Nat.card J) (Set.toFinite S) hSne
  obtain ⟨hIinv, hIne⟩ := hI
  have hmin' : ∀ J : Subgroup V, (∀ x ∈ X, ∀ w ∈ J, x w ∈ J) → J < I → commSub J X = ⊥ := by
    intro J hJinv hJI
    by_contra hJne
    have hc : Nat.card I ≤ Nat.card J := hmin J ⟨hJinv, hJne⟩
    exact hJI.ne (Subgroup.eq_of_le_of_card_ge hJI.le hc)
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.2 hX
  have hcomm : commSub I X = I := by
    apply le_antisymm (commSub_le_of_invariant hIinv)
    by_contra hnot
    have hlt : commSub I X < I :=
      lt_of_le_of_ne (commSub_le_of_invariant hIinv) fun h => hnot h.ge
    have hfix : commSub I X ≤ fixV X :=
      commSub_eq_bot_iff.1 (hmin' _ (commSub_inv_H X I) hlt)
    apply hIne
    rw [commSub_eq_bot_iff]
    intro i hi x hx
    let c : ↥X →* ↥(commSub I X) :=
      { toFun := fun y => ⟨(y : MulAut V) i * i⁻¹,
          Subgroup.subset_closure ⟨y, y.2, i, hi, rfl⟩⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun y z => by
          apply Subtype.ext
          have hz : (z : MulAut V) i * i⁻¹ ∈ commSub I X :=
            Subgroup.subset_closure ⟨z, z.2, i, hi, rfl⟩
          have hy : (y : MulAut V) ((z : MulAut V) i * i⁻¹) = (z : MulAut V) i * i⁻¹ :=
            hfix hz y y.2
          have e : (y : MulAut V) ((z : MulAut V) i) =
              (y : MulAut V) ((z : MulAut V) i * i⁻¹) * (y : MulAut V) i := by
            rw [← map_mul]
            simp
          show ((y : MulAut V) * (z : MulAut V)) i * i⁻¹ =
            ((y : MulAut V) i * i⁻¹) * ((z : MulAut V) i * i⁻¹)
          rw [MulAut.mul_apply, e, hy]
          cgroup }
    have hker : commutator ↥X ≤ c.ker := Abelianization.commutator_subset_ker c
    have h1 : (⟨x, hx⟩ : ↥X) ∈ c.ker := hker (by rw [hperf.commutator_eq_top]; trivial)
    have h2 := congrArg Subtype.val h1
    simpa [c, mul_inv_eq_one] using h2
  have hlt : I ⊓ fixV X < I := by
    refine lt_of_le_of_ne inf_le_left fun h => hIne ?_
    rw [commSub_eq_bot_iff]
    intro i hi
    have hmem : i ∈ I ⊓ fixV X := by rw [h]; exact hi
    exact hmem.2
  refine ⟨I, (mem_irrPlus_top_iff).2 ⟨hIinv, hcomm, hlt, ?_⟩⟩
  intro J hJinv hJ1 hJ2
  by_cases hJI : J = I
  · exact Or.inr hJI
  · left
    have hJlt : J < I := lt_of_le_of_ne hJ2 hJI
    have hJfix : J ≤ fixV X := commSub_eq_bot_iff.1 (hmin' J hJinv hJlt)
    exact le_antisymm (le_inf hJ2 hJfix) hJ1

end Irr

end B1Red

end CFSG.Quasithin

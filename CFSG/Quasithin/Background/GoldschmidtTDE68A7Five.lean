module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Fix

public section

namespace CFSG.Quasithin.E6.Alt.A7

open Equiv Equiv.Perm CFSG.Quasithin.E6.Bar

abbrev Pts5 : Type := {x : Fin 7 // x ≠ 4 ∧ x ≠ 5}

@[expose] def N7 : Subgroup G7 where
  carrier := {g | (g : Perm (Fin 7)) 4 = 4 ∧ (g : Perm (Fin 7)) 5 = 5}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨?_, ?_⟩
    · show (a : Perm (Fin 7)) ((b : Perm (Fin 7)) 4) = 4
      rw [hb.1, ha.1]
    · show (a : Perm (Fin 7)) ((b : Perm (Fin 7)) 5) = 5
      rw [hb.2, ha.2]
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := fun {a} ha => by
    refine ⟨?_, ?_⟩
    · show (a : Perm (Fin 7))⁻¹ 4 = 4
      rw [Equiv.Perm.inv_eq_iff_eq, ha.1]
    · show (a : Perm (Fin 7))⁻¹ 5 = 5
      rw [Equiv.Perm.inv_eq_iff_eq, ha.2]

theorem pres_N7 (g : Perm (Fin 7)) (h4 : g 4 = 4) (h5 : g 5 = 5) (x : Fin 7) :
    ((g x ≠ 4 ∧ g x ≠ 5) ↔ (x ≠ 4 ∧ x ≠ 5)) := by
  constructor
  · rintro ⟨a, b⟩
    refine ⟨fun hx => a ?_, fun hx => b ?_⟩
    · rw [hx, h4]
    · rw [hx, h5]
  · rintro ⟨a, b⟩
    refine ⟨fun hx => a ?_, fun hx => b ?_⟩
    · exact g.injective (hx.trans h4.symm)
    · exact g.injective (hx.trans h5.symm)

noncomputable def N7equiv : N7 ≃ alternatingGroup Pts5 where
  toFun g := ⟨(g.1 : Perm (Fin 7)).subtypePerm (fun x => pres_N7 _ g.2.1 g.2.2 x), by
    rw [mem_alternatingGroup, Equiv.Perm.sign_subtypePerm _ _ (fun x hx => by
      refine ⟨fun h => hx ?_, fun h => hx ?_⟩
      · rw [h]; exact g.2.1
      · rw [h]; exact g.2.2)]
    exact (mem_alternatingGroup.1 g.1.2)⟩
  invFun f := ⟨⟨Equiv.Perm.ofSubtype f.1, by
    rw [mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact mem_alternatingGroup.1 f.2⟩, by
    refine ⟨?_, ?_⟩
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp)
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp)⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.Perm.ofSubtype_subtypePerm (fun x => pres_N7 _ g.2.1 g.2.2 x) (fun x hx => by
      refine ⟨fun h => hx ?_, fun h => hx ?_⟩
      · rw [h]; exact g.2.1
      · rw [h]; exact g.2.2)
  right_inv f := by
    apply Subtype.ext
    exact Equiv.Perm.subtypePerm_ofSubtype f.1

theorem card_Pts5 : Nat.card Pts5 = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_N7 : Nat.card N7 = 60 := by
  rw [Nat.card_congr N7equiv]
  have hn : Nontrivial Pts5 := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩
  have h := two_mul_nat_card_alternatingGroup (α := Pts5)
  rw [Nat.card_eq_fintype_card (α := Perm Pts5), Fintype.card_perm,
    ← Nat.card_eq_fintype_card, card_Pts5] at h
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

theorem pb_four : pb 4 = 5 := by decide

theorem pb_five : pb 5 = 4 := by decide

theorem pb_of_ne (x : Fin 7) (h4 : x ≠ 4) (h5 : x ≠ 5) : pb x = x := by
  revert x
  decide

theorem N7_le_fixedSub_pb : N7 ≤ fixedSub (cj pb) := by
  intro g hg
  rw [mem_fixedSub_cj]
  refine Equiv.ext fun y => ?_
  show pb ((g : Perm (Fin 7)) y) = (g : Perm (Fin 7)) (pb y)
  by_cases h4 : y = 4
  · subst h4
    rw [hg.1, pb_four, hg.2]
  · by_cases h5 : y = 5
    · subst h5
      rw [hg.2, pb_five, hg.1]
    · rw [pb_of_ne y h4 h5]
      refine pb_of_ne _ (fun h => h4 ?_) (fun h => h5 ?_)
      · exact (g : Perm (Fin 7)).injective (h.trans hg.1.symm)
      · exact (g : Perm (Fin 7)).injective (h.trans hg.2.symm)

theorem apply_four_of_comm (g : Perm (Fin 7)) (hc : pb * g = g * pb) :
    g 4 = 4 ∨ g 4 = 5 := by
  by_contra hne
  push Not at hne
  have h1 : pb (g 4) = g 5 := by
    have := congrArg (fun τ : Perm (Fin 7) => τ 4) hc
    simpa [pb_four] using this
  rw [pb_of_ne _ hne.1 hne.2] at h1
  exact absurd (g.injective h1) (by decide)

theorem apply_five_of_comm (g : Perm (Fin 7)) (hc : pb * g = g * pb) : g 5 = pb (g 4) := by
  have := congrArg (fun τ : Perm (Fin 7) => τ 4) hc
  simpa [pb_four] using this.symm

theorem le_N7_of_perfect (H : Subgroup G7) (hH : H ≤ fixedSub (cj pb))
    (hperf : Group.IsPerfect ↥H) : H ≤ N7 := by
  have hc : ∀ h : ↥H, pb * ((h : G7) : Perm (Fin 7)) = ((h : G7) : Perm (Fin 7)) * pb :=
    fun h => (mem_fixedSub_cj pb h.1).1 (hH h.2)
  let eps : ↥H →* ℤˣ :=
    { toFun := fun h => if ((h : G7) : Perm (Fin 7)) 4 = 4 then 1 else -1
      map_one' := by simp
      map_mul' := fun a b => by
        have ha := apply_four_of_comm _ (hc a)
        have hb := apply_four_of_comm _ (hc b)
        have ha5 := apply_five_of_comm _ (hc a)
        rcases hb with hb | hb <;> rcases ha with ha | ha <;>
          simp [hb, ha, ha5, pb_four, pb_five] }
  have hker : commutator ↥H ≤ eps.ker := Abelianization.commutator_subset_ker eps
  rw [Group.isPerfect_def.1 hperf] at hker
  intro g hg
  have h1 : eps ⟨g, hg⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  have h4 : (g : Perm (Fin 7)) 4 = 4 := by
    by_contra hne
    have : eps ⟨g, hg⟩ = -1 := by simp [eps, hne]
    rw [this] at h1
    exact absurd h1 (by decide)
  refine ⟨h4, ?_⟩
  rw [apply_five_of_comm _ (hc ⟨g, hg⟩), h4, pb_four]

end CFSG.Quasithin.E6.Alt.A7

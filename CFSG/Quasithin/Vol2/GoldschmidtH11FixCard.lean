module

public import CFSG.Quasithin.Vol2.GoldschmidtH11Fix
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Vol2.GoldschmidtH11Perp

public section

open scoped Matrix MatrixGroups

namespace CFSG.Quasithin.H11

variable {F : Type} [Field F] [Finite F] [CharP F 2] (a : ℕ) (h : Nat.card F = 2 ^ (2 * a))

@[expose] def Tset (A : Subgroup (MulAut (HV F a))) : Set F := {d | actHom a h (uSL d) ∈ A}

@[expose] def UType (A : Subgroup (MulAut (HV F a))) : Prop :=
  ∀ x ∈ A, ∃ d, x = actHom a h (uSL d)

variable {a h}

theorem card_eq_card_Tset {A : Subgroup (MulAut (HV F a))} (hA : UType a h A) :
    Nat.card A = Nat.card (Tset a h A) := by
  let f : Tset a h A → A := fun d => ⟨actHom a h (uSL d.1), d.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun d d' hdd => ?_, fun x => ?_⟩
    · exact Subtype.ext (uSL_injective ((actHom_injective a h) (congrArg Subtype.val hdd)))
    · obtain ⟨d, hd⟩ := hA x.1 x.2
      exact ⟨⟨d, by show actHom a h (uSL d) ∈ A; rw [← hd]; exact x.2⟩, Subtype.ext hd.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem exists_ne_zero_of_ne_bot {A : Subgroup (MulAut (HV F a))} (hA : UType a h A)
    (hA1 : A ≠ ⊥) : ∃ d ∈ Tset a h A, d ≠ 0 := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  obtain ⟨d, hd⟩ := hA x.1 x.2
  refine ⟨d, by show actHom a h (uSL d) ∈ A; rw [← hd]; exact x.2, ?_⟩
  rintro rfl
  apply hx1
  apply Subtype.ext
  rw [hd, uSL_zero, map_one]; rfl

theorem fix_entries {A : Subgroup (MulAut (HV F a))} {v : HV F a} (hv : v ∈ fixV A) {d : F}
    (hd : d ∈ Tset a h A) (hd0 : d ≠ 0) :
    hm a v 1 1 = 0 ∧ d * sg a (hm a v 0 1) = sg a d * hm a v 0 1 := by
  obtain ⟨e1, e2⟩ := (actHom_uSL_fix_iff a h v d).mp (hv _ hd)
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  refine ⟨(mul_eq_zero.mp e1).resolve_left hd0, ?_⟩
  linear_combination e2 - (hm a v 0 1 * sg a d) * h2

theorem card_fixV_le {A : Subgroup (MulAut (HV F a))} (hA : UType a h A) (hA1 : A ≠ ⊥) :
    Nat.card (fixV A) ≤
      Nat.card ((Kf a : Subfield F) : Set F) * Nat.card (perp a (Tset a h A)) := by
  obtain ⟨d₀, hd₀, hd₀0⟩ := exists_ne_zero_of_ne_bot hA hA1
  have hy : ∀ v : fixV A, hm a v.1 1 1 = 0 := fun v => (fix_entries v.2 hd₀ hd₀0).1
  have hp : ∀ v : fixV A, hm a v.1 0 1 ∈ perp a (Tset a h A) := fun v d hd => by
    by_cases hd0 : d = 0
    · simp [hd0]
    · exact (fix_entries v.2 hd hd0).2
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun v : fixV A => ((⟨hm a v.1 0 0, (mem_Kf a).mpr (hm_entry a v.1 0 0)⟩ :
      ((Kf a : Subfield F) : Set F)), (⟨hm a v.1 0 1, hp v⟩ : perp a (Tset a h A)))) ?_
  intro v w hvw
  have h1 := congrArg (fun p => p.1.1) hvw
  have h2 := congrArg (fun p => p.2.1) hvw
  simp only at h1 h2
  apply Subtype.ext
  apply hm_injective a
  rw [hm_eq a v.1, hm_eq a w.1, h1, h2, hy v, hy w]

theorem card_fixV_le_of_sub {A : Subgroup (MulAut (HV F a))} (hA : UType a h A) (hA1 : A ≠ ⊥)
    (hK : Tset a h A ⊆ ((Kf a : Subfield F) : Set F)) :
    Nat.card (fixV A) ≤
      Nat.card ((Kf a : Subfield F) : Set F) * Nat.card ((Kf a : Subfield F) : Set F) := by
  obtain ⟨d₀, hd₀, hd₀0⟩ := exists_ne_zero_of_ne_bot hA hA1
  have hy : ∀ v : fixV A, hm a v.1 1 1 = 0 := fun v => (fix_entries v.2 hd₀ hd₀0).1
  have hp : ∀ v : fixV A, hm a v.1 0 1 ∈ ((Kf a : Subfield F) : Set F) := fun v => by
    have e := (fix_entries v.2 hd₀ hd₀0).2
    have hk : sg a d₀ = d₀ := (mem_Kf a).mp (hK hd₀)
    rw [hk] at e
    exact (mem_Kf a).mpr (mul_left_cancel₀ hd₀0 e)
  refine Nat.card_le_card_of_injective
    (fun v : fixV A => ((⟨hm a v.1 0 0, (mem_Kf a).mpr (hm_entry a v.1 0 0)⟩ :
      ((Kf a : Subfield F) : Set F)), (⟨hm a v.1 0 1, hp v⟩ : ((Kf a : Subfield F) : Set F))))
    ?_ |>.trans_eq (Nat.card_prod _ _)
  intro v w hvw
  have h1 := congrArg (fun p => p.1.1) hvw
  have h2 := congrArg (fun p => p.2.1) hvw
  simp only at h1 h2
  apply Subtype.ext
  apply hm_injective a
  rw [hm_eq a v.1, hm_eq a w.1, h1, h2, hy v, hy w]

end CFSG.Quasithin.H11

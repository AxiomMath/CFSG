module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieTwoB
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieCtr

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
  CFSG.Quasithin.H13.F431.Lift

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem stdTwo_Xg : StdTwo (Xg h) (Psy h) (Pt h) (Ln h) (z1X h) (z2X h) where
  z_mem := z1X_mem_Psy h
  t_mem := z2X_mem_Psy h
  z_two := orderOf_z1X h
  t_two := orderOf_z2X h
  cls := cls_Xg h
  noconj := noconj_Xg h
  center := fun _ hw hc hw1 => center_Xg h hw hc hw1
  aut_z := aut_z_Xg h
  aut_t := aut_t_Xg h
  cent_z := Or.inl (cz_Xg h)
  cent_t := Or.inr (ct_Xg h)

theorem A1X_le_Psy : A1X h ≤ Psy h := fun _ hx => miyamotoA1_le_P h hx

theorem A1X_ab {a b : Xg h} (ha : a ∈ A1X h) (hb : b ∈ A1X h) : a * b = b * a :=
  Subtype.ext (mul_comm_of_mem_miyamotoA1 h ha hb)

theorem A1X_sq {a : Xg h} (ha : a ∈ A1X h) : a ^ 2 = 1 := by
  obtain ⟨b, c, d, hb, -, hxa⟩ := (mem_A1 h).1 ha
  have hxa' : (a : GL (Fin 4) K) = miyamotoXGL h 0 b c d := hxa
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [sq, hxa', miyamotoXGL_A1_mul_self h hb]

theorem card_A1X : Nat.card (A1X h) = (2 ^ f) ^ 4 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (miyamotoUnipotent_le_SU h true false)).toEquiv]
  exact card_miyamotoA1 h

theorem V4_unique_Xg {E : Subgroup (Xg h)} (hE : E ≤ Psy h)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a ^ 2 = 1)
    (hcard : Nat.card E = Nat.card (A1X h)) : E = A1X h := by
  have := h.finite
  let E' : Subgroup (GL (Fin 4) K) := E.map (gramSU h (miyamotoJ4 K)).subtype
  have hE'P : E' ≤ miyamotoP h := by
    rintro _ ⟨x, hx, rfl⟩
    exact hE hx
  have hE'mem : ∀ {y : GL (Fin 4) K}, y ∈ E' ↔ ∃ x : Xg h, x ∈ E ∧ (x : GL (Fin 4) K) = y :=
    Subgroup.mem_map
  have hEA' : CFSG.IsElementaryAbelian 2 E' := by
    refine isElementaryAbelian_two_of_forall (fun x hx y hy => ?_) fun x hx => ?_
    · obtain ⟨x', hx', rfl⟩ := hE'mem.1 hx
      obtain ⟨y', hy', rfl⟩ := hE'mem.1 hy
      exact congrArg Subtype.val (hab x' hx' y' hy')
    · obtain ⟨x', hx', rfl⟩ := hE'mem.1 hx
      have := congrArg Subtype.val (hsq x' hx')
      simpa [sq] using this
  have hcard' : (2 ^ f) ^ 4 ≤ Nat.card E' := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcard, card_A1X]
  have hEA := ((card_le_and_eq_A1_of_isElementaryAbelian h hE'P).2 hcard')
  ext x
  constructor
  · intro hx
    have : (x : GL (Fin 4) K) ∈ E' := hE'mem.2 ⟨x, hx, rfl⟩
    rw [hEA] at this
    exact this
  · intro hx
    have : (x : GL (Fin 4) K) ∈ E' := by rw [hEA]; exact hx
    obtain ⟨x', hx', e⟩ := hE'mem.1 this
    rwa [← Subtype.ext e]

end CFSG.Quasithin.H13.F431.Un.OL

module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

omit [Finite D] in
theorem card_Vv_B_of_card {n : ℕ} (hU : Nat.card (conjClosure V B) = n)
    {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) : Nat.card (Vv V v) = n := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hv
  rw [Vv_smul h.natural.reduced.2.1, Vv_γ₁ le_sup_right h.natural.reduced.2.1, card_conjSub]
  exact hU

theorem inf_Zv_eq_bot {u β β' : CosetGeom (A ⊔ B) A B} (hu : vtype u = false)
    (hβ : (graph (A ⊔ B) A B).Adj u β) (hβ' : (graph (A ⊔ B) A B).Adj u β') (hne : β ≠ β') :
    Zv z β ⊓ Zv z β' = ⊥ := by
  have hβt : vtype β = true := vtype_eq_true_of_adj hβ hu
  have hβ't : vtype β' = true := vtype_eq_true_of_adj hβ' hu
  by_contra hcon
  have hd : Nat.card ↥(Zv z β ⊓ Zv z β') ∣ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Zv z β ⊓ Zv z β' ≤ Zv z β)
    rwa [h.card_Zv hβt] at this
  have h1 : Nat.card ↥(Zv z β ⊓ Zv z β') ≠ 1 := fun e =>
    hcon (Subgroup.eq_bot_of_card_eq _ e)
  have h2 : Nat.card ↥(Zv z β ⊓ Zv z β') = 2 := by
    have hpos : 0 < Nat.card ↥(Zv z β ⊓ Zv z β') := Nat.card_pos
    have hle2 := Nat.le_of_dvd (by norm_num) hd
    omega
  have e1 : Zv z β ⊓ Zv z β' = Zv z β :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, h.card_Zv hβt])
  have e2 : Zv z β ⊓ Zv z β' = Zv z β' :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, h.card_Zv hβ't])
  exact hne (h.eq_of_Zv_eq hu hβ hβ' (e1.symm.trans e2))

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

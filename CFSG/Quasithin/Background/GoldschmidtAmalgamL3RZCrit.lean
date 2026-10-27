module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem Zv_le_ballStab_one_of_dist_le {b : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {β δ : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true) (hd : CosetGeom.dist β δ ≤ b) :
    Zv z β ≤ ballStab 1 δ := by
  have h3 : 3 ≤ b := hb ▸ h.three_le_critDist
  obtain ⟨α, hα, hαδ⟩ : ∃ α, (graph (A ⊔ B) A B).Adj β α ∧ CosetGeom.dist α δ + 1 ≤ b := by
    rcases Nat.eq_zero_or_pos (CosetGeom.dist β δ) with h0 | hpos
    · obtain rfl : β = δ := (dist_eq_zero_iff rfl).mp h0
      obtain ⟨α, hα⟩ := exists_adj β
      refine ⟨α, hα, ?_⟩
      have : CosetGeom.dist α β = 1 := dist_eq_one_iff_adj.mpr hα.symm
      omega
    · obtain ⟨d, hdd⟩ : ∃ d, CosetGeom.dist β δ = d + 1 := ⟨CosetGeom.dist β δ - 1, by omega⟩
      obtain ⟨α, hα, hαd⟩ := exists_adj_dist_eq (rfl : A ⊔ B = A ⊔ B) (α := δ) (δ := β) (d := d)
        (by rw [CosetGeom.dist_comm]; exact hdd)
      refine ⟨α, hα, ?_⟩
      rw [CosetGeom.dist_comm]
      omega
  have hαt : vtype α = false := vtype_eq_false_of_adj hα hβ
  calc Zv z β ≤ Vv V α := h.Zv_le_Vv hα.symm hαt
    _ ≤ ballStab b α := h.Vv_le_ballStab_A hb hαt
    _ ≤ ballStab 1 δ := ballStab_le_ballStab_of_dist rfl hαδ

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

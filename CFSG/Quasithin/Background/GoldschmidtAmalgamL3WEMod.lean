module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZRank
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WBase

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

theorem exists_third_nbr {β u₁ u₂ : CosetGeom (A ⊔ B) A B}
    (h₁ : (graph (A ⊔ B) A B).Adj β u₁) (h₂ : (graph (A ⊔ B) A B).Adj β u₂) (h12 : u₁ ≠ u₂) :
    ∃ u₃ : CosetGeom (A ⊔ B) A B, (graph (A ⊔ B) A B).Adj β u₃ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
      ∀ x, (graph (A ⊔ B) A B).Adj β x → x = u₁ ∨ x = u₂ ∨ x = u₃ := by
  obtain ⟨a, b, ha, hb, hau, hbu, hab⟩ := h.exists_other_nbrs h₁
  rcases h.eq_or_eq_of_adj h₁ ha hb h₂ hau.symm hbu.symm hab with e | e | e
  · exact absurd e.symm h12
  · subst e
    refine ⟨b, hb, hbu.symm, hab, fun x hx => ?_⟩
    rcases h.eq_or_eq_of_adj h₁ ha hb hx hau.symm hbu.symm hab with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)
  · subst e
    refine ⟨a, ha, hau.symm, hab.symm, fun x hx => ?_⟩
    rcases h.eq_or_eq_of_adj h₁ ha hb hx hau.symm hbu.symm hab with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr e)
    · exact Or.inr (Or.inl e)

theorem card_Vv_sup_eq {β u u' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (hu : (graph (A ⊔ B) A B).Adj β u) (hu' : (graph (A ⊔ B) A B).Adj β u') (hne : u ≠ u') :
    Nat.card ↥(Vv V u ⊔ Vv V u') = 8 := by
  have hut : vtype u = false := vtype_eq_false_of_adj hu hβ
  have hut' : vtype u' = false := vtype_eq_false_of_adj hu' hβ
  have hU := h.isElemAbelian_Vv_B (V := V) hβ
  have huU : Vv V u ≤ Vv V β := Vv_le_Vv_of_adj hu.symm hut
  have hu'U : Vv V u' ≤ Vv V β := Vv_le_Vv_of_adj hu'.symm hut'
  obtain ⟨a, ha, ha'⟩ := h.exists_mem_Vv_not_mem_Zv hut' hu'.symm
  have hle : Vv V u' ≤ Zv z β ⊔ Subgroup.zpowers a := h.Vv_le_sup_zpowers hut' hu'.symm ha ha'
  have hZ : Zv z β ≤ Vv V u := h.Zv_le_Vv hu.symm hut
  have hsub : Vv V u ⊔ Vv V u' ≤ Vv V u ⊔ Subgroup.zpowers a :=
    sup_le le_sup_left (hle.trans (sup_le (hZ.trans le_sup_left) le_sup_right))
  have hnorm : Vv V u ≤ Subgroup.normalizer (Subgroup.zpowers a : Set D) := fun v hv =>
    mem_normalizer_zpowers_of_mul_comm (isElemAbelian_comm hU (huU hv) (hu'U ha))
  have c1 := GoldAmN.card_sup_le_of_le_normalizer (Vv V u) (Subgroup.zpowers a) hnorm
  have c2 := card_zpowers_le_two (hU.2 a (hu'U ha))
  rw [h.card_Vv_A hut] at c1
  have hle8 : Nat.card ↥(Vv V u ⊔ Vv V u') ≤ 8 :=
    calc Nat.card ↥(Vv V u ⊔ Vv V u') ≤ Nat.card ↥(Vv V u ⊔ Subgroup.zpowers a) :=
          Subgroup.card_le_of_le hsub
      _ ≤ 4 * Nat.card (Subgroup.zpowers a) := c1
      _ ≤ 4 * 2 := Nat.mul_le_mul_left 4 c2
  have hd : 4 ∣ Nat.card ↥(Vv V u ⊔ Vv V u') := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Vv V u ≤ Vv V u ⊔ Vv V u')
    rwa [h.card_Vv_A hut] at this
  have hne4 : Nat.card ↥(Vv V u ⊔ Vv V u') ≠ 4 := fun e => by
    have h1 : Vv V u = Vv V u ⊔ Vv V u' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [e, h.card_Vv_A hut])
    have h2 : Vv V u' ≤ Vv V u := h1 ▸ (le_sup_right : Vv V u' ≤ Vv V u ⊔ Vv V u')
    have h3 : Vv V u' = Vv V u :=
      Subgroup.eq_of_le_of_card_ge h2 (by rw [h.card_Vv_A hut, h.card_Vv_A hut'])
    exact hne (h.eq_of_Vv_eq hβ hu hu' h3.symm)
  have hpos : 0 < Nat.card ↥(Vv V u ⊔ Vv V u') := Nat.card_pos
  obtain ⟨k, hk⟩ := hd
  omega

theorem inf_sup_Vv_eq (hU : Nat.card (conjClosure V B) = 16) {β u₁ u₂ u₃ : CosetGeom (A ⊔ B) A B}
    (hβ : vtype β = true) (h₁ : (graph (A ⊔ B) A B).Adj β u₁)
    (h₂ : (graph (A ⊔ B) A B).Adj β u₂) (h₃ : (graph (A ⊔ B) A B).Adj β u₃) (h12 : u₁ ≠ u₂)
    (h13 : u₁ ≠ u₃) (hall : ∀ x, (graph (A ⊔ B) A B).Adj β x → x = u₁ ∨ x = u₂ ∨ x = u₃) :
    (Vv V u₁ ⊔ Vv V u₂) ⊓ (Vv V u₁ ⊔ Vv V u₃) = Vv V u₁ := by
  have hu1 : vtype u₁ = false := vtype_eq_false_of_adj h₁ hβ
  have c12 := h.card_Vv_sup_eq hβ h₁ h₂ h12
  have c13 := h.card_Vv_sup_eq hβ h₁ h₃ h13
  have c4 := h.card_Vv_A hu1
  have hU16 : Nat.card ↥(Vv V β) = 16 := h.card_Vv_B_of_card hU hβ
  set Y := (Vv V u₁ ⊔ Vv V u₂) ⊓ (Vv V u₁ ⊔ Vv V u₃) with hY
  have hV1Y : Vv V u₁ ≤ Y := le_inf le_sup_left le_sup_left
  have hd : 4 ∣ Nat.card ↥Y := by
    have := Subgroup.card_dvd_of_le hV1Y
    rwa [c4] at this
  have hd8 : Nat.card ↥Y ∣ 8 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Y ≤ Vv V u₁ ⊔ Vv V u₂)
    rwa [c12] at this
  have hle8 := Nat.le_of_dvd (by norm_num) hd8
  have hpos : 0 < Nat.card ↥Y := Nat.card_pos
  have hcases : Nat.card ↥Y = 4 ∨ Nat.card ↥Y = 8 := by
    obtain ⟨k, hk⟩ := hd
    omega
  rcases hcases with e | e
  · exact (Subgroup.eq_of_le_of_card_ge hV1Y (by rw [e, c4])).symm
  · exfalso
    have e12 : Y = Vv V u₁ ⊔ Vv V u₂ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [e, c12])
    have e13 : Y = Vv V u₁ ⊔ Vv V u₃ :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [e, c13])
    have h2le : Vv V u₂ ≤ Vv V u₁ ⊔ Vv V u₃ := by
      rw [← e13, e12]
      exact le_sup_right
    have hUle : Vv V β ≤ Vv V u₁ ⊔ Vv V u₃ := by
      refine (Vv_B_le_iff hβ).mpr fun l hl => ?_
      rcases hall l hl with rfl | rfl | rfl
      · exact le_sup_left
      · exact h2le
      · exact le_sup_right
    have := Subgroup.card_le_of_le hUle
    rw [hU16, c13] at this
    omega

theorem le_Zv_of_stab_invariant (hU : Nat.card (conjClosure V B) = 16)
    {β u₁ u₂ : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h₁ : (graph (A ⊔ B) A B).Adj β u₁) (h₂ : (graph (A ⊔ B) A B).Adj β u₂) (h12 : u₁ ≠ u₂)
    {X : Subgroup D} (hX : X ≤ Vv V u₁ ⊔ Vv V u₂) (hinv : ∀ g ∈ stab β, conjSub g X ≤ X) :
    X ≤ Zv z β := by
  obtain ⟨u₃, h₃, h13, h23, hall⟩ := h.exists_third_nbr h₁ h₂ h12
  have hu1 : vtype u₁ = false := vtype_eq_false_of_adj h₁ hβ
  have hu2 : vtype u₂ = false := vtype_eq_false_of_adj h₂ hβ
  have hX_le : ∀ g ∈ stab β, X ≤ conjSub g X := fun g hg => by
    have := conjSub_mono g (hinv g⁻¹ (inv_mem hg))
    rwa [conjSub_inv_conjSub] at this
  obtain ⟨t₁, ht₁, ht₁Q⟩ := h.exists_swap_edge hu1 h₁.symm
  lift t₁ to ↥(A ⊔ B) using stab_le β ht₁.2 with g₁
  have hg₁ : g₁ • u₂ = u₃ :=
    h.smul_eq_of_not_mem_ballStab h₁ h₂ h₃ h12.symm h13.symm h23 ht₁.2 ht₁.1 ht₁Q
  have hg₁u : g₁ • u₁ = u₁ := smul_eq_of_mem_stab ht₁.1
  have e1 : conjSub (g₁ : D) (Vv V u₁ ⊔ Vv V u₂) = Vv V u₁ ⊔ Vv V u₃ := by
    rw [conjSub_sup, ← Vv_smul h.natural.reduced.2.1 g₁ u₁, ← Vv_smul h.natural.reduced.2.1 g₁ u₂,
      hg₁, hg₁u]
  have hX1 : X ≤ Vv V u₁ := by
    have h1 := (hX_le (g₁ : D) ht₁.2).trans (conjSub_mono (g₁ : D) hX)
    rw [e1] at h1
    exact (le_inf hX h1).trans (h.inf_sup_Vv_eq hU hβ h₁ h₂ h₃ h12 h13 hall).le
  obtain ⟨t₂, ht₂, ht₂Q⟩ := h.exists_swap_edge hu2 h₂.symm
  lift t₂ to ↥(A ⊔ B) using stab_le β ht₂.2 with g₂
  have hg₂ : g₂ • u₁ = u₃ :=
    h.smul_eq_of_not_mem_ballStab h₂ h₁ h₃ h12 h23.symm h13 ht₂.2 ht₂.1 ht₂Q
  have hX3 : X ≤ Vv V u₃ := by
    have h1 := (hX_le (g₂ : D) ht₂.2).trans (conjSub_mono (g₂ : D) hX1)
    rwa [← Vv_smul h.natural.reduced.2.1 g₂ u₁, hg₂] at h1
  intro x hx
  exact h.mem_Zv_of_mem_Vv_of_mem_Vv hβ h₁ h₃ h13 (hX1 hx) (hX3 hx)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin

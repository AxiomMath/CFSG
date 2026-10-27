module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesExtra

public section

namespace CFSG.Quasithin.A312Words

open CFSG.Quasithin CFSG.Quasithin.A312ExtShapes

section Gens

variable {V : Type} [Group V]

def czSub (z : V) (hzc : ∀ y : V, y * z = z * y) (hzz : z * z = 1) (x : V) : Subgroup V where
  carrier := {y | x * y = y * x ∨ x * y = z * (y * x)}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left
      calc x * (a * b) = (x * a) * b := by group
        _ = (a * x) * b := by rw [ha]
        _ = a * (x * b) := by group
        _ = a * (b * x) := by rw [hb]
        _ = (a * b) * x := by group
    · right
      calc x * (a * b) = (x * a) * b := by group
        _ = (a * x) * b := by rw [ha]
        _ = a * (x * b) := by group
        _ = a * (z * (b * x)) := by rw [hb]
        _ = (a * z) * (b * x) := by group
        _ = z * ((a * b) * x) := by rw [hzc a]; group
    · right
      calc x * (a * b) = (x * a) * b := by group
        _ = (z * (a * x)) * b := by rw [ha]
        _ = z * (a * (x * b)) := by group
        _ = z * (a * (b * x)) := by rw [hb]
        _ = z * ((a * b) * x) := by group
    · left
      calc x * (a * b) = (x * a) * b := by group
        _ = (z * (a * x)) * b := by rw [ha]
        _ = z * (a * (x * b)) := by group
        _ = z * (a * (z * (b * x))) := by rw [hb]
        _ = z * ((a * z) * (b * x)) := by group
        _ = z * (z * ((a * b) * x)) := by rw [hzc a]; group
        _ = (z * z) * ((a * b) * x) := by group
        _ = (a * b) * x := by rw [hzz, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with ha | ha
    · left
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [← ha]
        _ = a⁻¹ * x := by group
    · right
      have h' : a * x = z * (x * a) := by rw [ha, ← mul_assoc, hzz, one_mul]
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (z * (x * a)) * a⁻¹ := by rw [h']
        _ = (a⁻¹ * z) * (x * a) * a⁻¹ := by group
        _ = (z * a⁻¹) * (x * a) * a⁻¹ := by rw [hzc a⁻¹]
        _ = z * (a⁻¹ * x) := by group

theorem mem_czSub {z : V} {hzc : ∀ y : V, y * z = z * y} {hzz : z * z = 1} {x y : V} :
    y ∈ czSub z hzc hzz x ↔ x * y = y * x ∨ x * y = z * (y * x) := Iff.rfl

theorem ext_of_gens (G : Set V) (hG : Subgroup.closure G = ⊤) (z : V) (hzz : z * z = 1)
    (hzc : ∀ g ∈ G, g * z = z * g) (hsq : ∀ g ∈ G, g * g = 1 ∨ g * g = z)
    (hcomm : ∀ g ∈ G, ∀ h ∈ G, g * h = h * g ∨ g * h = z * (h * g)) :
    (∀ x : V, x * z = z * x) ∧ (∀ x : V, x * x = 1 ∨ x * x = z) ∧
      ∀ x y : V, x * y = y * x ∨ x * y = z * (y * x) := by
  have hzc' : ∀ x : V, x * z = z * x := by
    intro x
    have hle : Subgroup.closure G ≤ Subgroup.centralizer {z} := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hzc g hg).symm
    have hx : x ∈ Subgroup.centralizer {z} := hle (hG ▸ Subgroup.mem_top x)
    exact (Subgroup.mem_centralizer_iff.mp hx z rfl).symm
  have hsym : ∀ x y : V, (x * y = y * x ∨ x * y = z * (y * x)) →
      (y * x = x * y ∨ y * x = z * (x * y)) := by
    intro x y h
    rcases h with h | h
    · exact Or.inl h.symm
    · right
      rw [h, ← mul_assoc, hzz, one_mul]
  have hA : ∀ g ∈ G, ∀ y : V, g * y = y * g ∨ g * y = z * (y * g) := by
    intro g hg y
    have hle : Subgroup.closure G ≤ czSub z (fun y => hzc' y) hzz g := by
      rw [Subgroup.closure_le]
      intro h hh
      exact hcomm g hg h hh
    exact hle (hG ▸ Subgroup.mem_top y)
  have hB : ∀ x y : V, x * y = y * x ∨ x * y = z * (y * x) := by
    intro x y
    have hle : Subgroup.closure G ≤ czSub z (fun y => hzc' y) hzz x := by
      rw [Subgroup.closure_le]
      intro g hg
      exact hsym g x (hA g hg x)
    exact hle (hG ▸ Subgroup.mem_top y)
  refine ⟨hzc', ?_, hB⟩
  let Sq : Subgroup V :=
    { carrier := {x | x * x = 1 ∨ x * x = z}
      one_mem' := Or.inl (by simp)
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        have hab : (a * b) * (a * b) = (a * a) * (b * b) ∨
            (a * b) * (a * b) = z * ((a * a) * (b * b)) := by
          rcases hB b a with h | h
          · left
            calc a * b * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [← h]
              _ = (a * a) * (b * b) := by group
          · right
            calc a * b * (a * b) = a * (b * a) * b := by group
              _ = a * (z * (a * b)) * b := by rw [← h]
              _ = (a * z) * (a * b) * b := by group
              _ = (z * a) * (a * b) * b := by rw [hzc' a]
              _ = z * ((a * a) * (b * b)) := by group
        have hP : (a * a) * (b * b) = 1 ∨ (a * a) * (b * b) = z := by
          rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
          · left; simp
          · right; simp
          · right; simp
          · left; exact hzz
        rcases hab with hab | hab
        · rw [hab]; exact hP
        · rw [hab]
          rcases hP with h | h
          · right; rw [h, mul_one]
          · left; rw [h]; exact hzz
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [← mul_inv_rev]
        rcases ha with ha | ha
        · left; rw [ha, inv_one]
        · right; rw [ha, inv_eq_of_mul_eq_one_right hzz] }
  have hle : Subgroup.closure G ≤ Sq := by
    rw [Subgroup.closure_le]
    exact hsq
  intro x
  exact hle (hG ▸ Subgroup.mem_top x)

end Gens

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isExtraspecial2_of_gens (wl : List Γ) (z : Γ)
    (hzW : z ∈ Subgroup.closure {w | w ∈ wl}) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzc : ∀ a ∈ wl, a * z = z * a) (hsq : ∀ a ∈ wl, a * a = 1 ∨ a * a = z)
    (hcomm : ∀ a ∈ wl, ∀ b ∈ wl, a * b = b * a ∨ a * b = z * (b * a))
    (hcen : ∀ c ∈ Subgroup.closure {w | w ∈ wl},
      (∀ q ∈ Subgroup.closure {w | w ∈ wl}, c * q = q * c) → c = 1 ∨ c = z)
    (hcard : Nat.card (Subgroup.closure {w | w ∈ wl}) = 2 ^ 7) :
    IsExtraspecial2 3 (Subgroup.closure {w | w ∈ wl}) := by
  let G : Set (Subgroup.closure {w | w ∈ wl}) := Subtype.val ⁻¹' {w | w ∈ wl}
  have hG : Subgroup.closure G = ⊤ := Subgroup.closure_closure_coe_preimage
  let z' : Subgroup.closure {w | w ∈ wl} := ⟨z, hzW⟩
  obtain ⟨hzcen, hsqall, hcommall⟩ := ext_of_gens G hG z' (Subtype.ext hzz)
    (fun g hg => Subtype.ext (hzc g.1 hg))
    (fun g hg => by
      rcases hsq g.1 hg with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h))
    (fun g hg h hh => by
      rcases hcomm g.1 hg h.1 hh with e | e
      · exact Or.inl (Subtype.ext e)
      · exact Or.inr (Subtype.ext e))
  exact isExtraspecial2_of_central_involution z' (fun h => hz1 (congrArg Subtype.val h)) hzcen
    hsqall hcommall
    (fun x hx => by
      rcases hcen x.1 x.2 (fun q hq => congrArg Subtype.val (hx ⟨q, hq⟩)) with e | e
      · exact Or.inl (Subtype.ext e)
      · exact Or.inr (Subtype.ext e))
    (by rw [hcard]) (by norm_num)

end CFSG.Quasithin.A312Words

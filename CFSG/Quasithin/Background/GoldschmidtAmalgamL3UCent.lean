module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem IsGeo.vtype_false_of_even_start {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ}
    (hG : G₀ = G₁ ⊔ G₂) (hp : IsGeo p n) (hp0 : vtype (p 0) = false) {i : ℕ} (hi : i ≤ n)
    (he : Even i) : vtype (p i) = false := by
  have h := (vtype_eq_iff_even_dist hG (p 0) (p i)).mpr
    (by rwa [hp 0 i (Nat.zero_le _) hi, Nat.sub_zero])
  rw [hp0] at h
  exact h.symm

theorem IsGeo.vtype_true_of_odd_start {p : ℕ → CosetGeom G₀ G₁ G₂} {n : ℕ}
    (hG : G₀ = G₁ ⊔ G₂) (hp : IsGeo p n) (hp0 : vtype (p 0) = false) {i : ℕ} (hi : i ≤ n)
    (ho : Odd i) : vtype (p i) = true := by
  have h : ¬ Even (CosetGeom.dist (p 0) (p i)) := by
    rw [hp 0 i (Nat.zero_le _) hi, Nat.sub_zero]
    exact Nat.not_even_iff_odd.mpr ho
  have h1 := (vtype_eq_iff_even_dist hG (p 0) (p i)).not.mpr h
  rw [hp0] at h1
  cases hv : vtype (p i)
  · exact absurd hv.symm h1
  · rfl

end CosetGeom

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem mem_Γ0_of_vtype_eq_false {γ : CosetGeom (A ⊔ B) A B} (hγ : vtype γ = false) :
    γ ∈ Γ0 (A ⊔ B) A B := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hγ
  exact mem_Γ0_iff_exists.mpr ⟨g, rfl⟩

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem Vv_le_ballStab_one_of_dist {b : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {u y : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) (hd : CosetGeom.dist u y + 1 ≤ b) :
    Vv V u ≤ ballStab 1 y :=
  (h.Vv_le_ballStab_A hb hu).trans (ballStab_le_ballStab_of_dist rfl hd)

theorem VvB_le_ballStab_one_of_dist {n : ℕ} (hb : critDist (A ⊔ B) A B V = n + 1)
    {v y : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) (hd : CosetGeom.dist v y + 1 ≤ n) :
    Vv V v ≤ ballStab 1 y :=
  (h.Vv_le_ballStab_B hb hv).trans (ballStab_le_ballStab_of_dist rfl hd)

theorem Vv_le_centralizer_of_dist {b : ℕ} (hb : critDist (A ⊔ B) A B V = b)
    {u u' : CosetGeom (A ⊔ B) A B} (hu : vtype u = false) (hu' : vtype u' = false)
    (hd : CosetGeom.dist u u' < b) : Vv V u ≤ Subgroup.centralizer (Vv V u' : Set D) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (commutator_Vv_Vv_eq_bot (h.gold.amalgamHypV h.natural) h.natural.natural.ne_bot
      (mem_Γ0_of_vtype_eq_false hu) (mem_Γ0_of_vtype_eq_false hu') (by rw [hb]; exact hd))

end GoldHyp3

theorem le_of_card_two_of_mem {X Y : Subgroup D} (hX : Nat.card X = 2) {c : D} (hcX : c ∈ X)
    (hcY : c ∈ Y) (hc : c ≠ 1) : X ≤ Y := by
  have h1 : orderOf c ≠ 1 := fun e => hc (orderOf_eq_one_iff.mp e)
  have hz : Nat.card (Subgroup.zpowers c) = orderOf c := Nat.card_zpowers c
  have hpos : 0 < orderOf c := orderOf_pos c
  have hXz : Subgroup.zpowers c = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcX) (by omega)
  rw [← hXz]
  exact Subgroup.zpowers_le.mpr hcY

end GoldAmL3

end F6

end CFSG.Quasithin

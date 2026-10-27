module

public import CFSG.Monster.GMS.S365Cent
public import CFSG.Monster.GMS.S365CenterCtr
public import CFSG.Monster.GMS.S365CenterOrb

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native

section Vec

theorem linearIndependent_of_pattern {a b ω : Fin 24 → ZMod 2} {i j k l : Fin 3}
    (ha : a ∈ co1Orbit 0) (hb : b ∈ co1Orbit 0) (hab : a + b ∈ co1Orbit 0)
    (hω : ω ∈ co1Orbit i) (hωa : ω + a ∈ co1Orbit j) (hωb : ω + b ∈ co1Orbit k)
    (hωab : ω + a + b ∈ co1Orbit l) : LinearIndependent (ZMod 2) ![a, b, ω] := by
  refine Leech.linearIndependent_fin_three (Leech.ne_zero_of_mem_co1Orbit ha)
    (Leech.ne_zero_of_mem_co1Orbit hb) (Leech.ne_zero_of_mem_co1Orbit hω) ?_ ?_ ?_ ?_
  · intro h
    rw [← h, vec_add_self] at hab
    exact Leech.ne_zero_of_mem_co1Orbit hab rfl
  · intro h
    rw [← h, vec_add_self] at hωa
    exact Leech.ne_zero_of_mem_co1Orbit hωa rfl
  · intro h
    rw [← h, vec_add_self] at hωb
    exact Leech.ne_zero_of_mem_co1Orbit hωb rfl
  · intro h
    rw [← h, show a + b + a + b = (a + a) + (b + b) by abel, vec_add_self, vec_add_self,
      add_zero] at hωab
    exact Leech.ne_zero_of_mem_co1Orbit hωab rfl

theorem eightPatterns :
    (toVecD 24 1 ∈ co1Orbit 2 ∧ toVecD 24 1 + toVecD 24 2 ∈ co1Orbit 0 ∧
      toVecD 24 1 + toVecD 24 4 ∈ co1Orbit 0 ∧
      toVecD 24 1 + toVecD 24 2 + toVecD 24 4 ∈ co1Orbit 0) ∧
    (toVecD 24 28 ∈ co1Orbit 0 ∧ toVecD 24 28 + toVecD 24 2 ∈ co1Orbit 2 ∧
      toVecD 24 28 + toVecD 24 4 ∈ co1Orbit 2 ∧
      toVecD 24 28 + toVecD 24 2 + toVecD 24 4 ∈ co1Orbit 2) := by
  have h := eightCheck_ok
  simp only [eightCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨-, -, -, h1, h3, h5, h7, h28, h30, h32, h34, -⟩ := h
  refine ⟨⟨mem_co1Orbit_two_of_lbl (by norm_num) h1, ?_, ?_, ?_⟩,
    ⟨mem_co1Orbit_zero_of_lbl (by norm_num) h28, ?_, ?_, ?_⟩⟩
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 2) (by decide) h3
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 4) (by decide) h5
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_zero_of_lbl (w := 1 ^^^ 2 ^^^ 4) (by decide) h7
    rwa [toVecD_xor, toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 2) (by decide) h30
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 4) (by decide) h32
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 28 ^^^ 2 ^^^ 4) (by decide) h34
    rwa [toVecD_xor, toVecD_xor] at this

theorem card_stab_le_pair
    (v : Fin 24 → ZMod 2) :
    Nat.card ↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4) ⊓ co1Stab v) ≤ 9196830720 := by
  obtain ⟨hx, hy, hxy⟩ := refPair
  rw [← card_inf_stab_pair hx hy hxy]
  exact Subgroup.card_le_of_le inf_le_left

theorem card_stab_three_lt :
    Nat.card ↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4) ⊓ co1Stab (toVecD 24 28)) <
      23224320 := by
  obtain ⟨hx, hy, hxy⟩ := refPair
  have hK := card_inf_stab_pair hx hy hxy
  have horb := ncard_orbit_mul_card_inf_stabilizer
    (co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4)) (toVecD 24 28)
  rw [← co1Stab_eq, hK] at horb
  have h397 := orbit3_ncard
  have hmul := Nat.mul_le_mul_right
    (Nat.card ↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4) ⊓ co1Stab (toVecD 24 28))) h397
  omega

end Vec

section Model

variable {G : Type*} [Group G]

@[expose] def CenterIn (x y t : G) : Prop :=
  ∀ h ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G),
    (∀ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G), h * g = g * h) →
    h ∈ ({1, x, y, t, x * y, x * t, y * t, x * y * t} : Set G)

theorem centerIn_of_card_lt
    {u x y t : G} (L : LeechSystem u) (hxQ : x ∈ leechQ u)
    (hyQ : y ∈ leechQ u) (htQ : t ∈ leechQ u)
    (hind : LinearIndependent (ZMod 2) ![L.vec x, L.vec y, L.vec t])
    (hcard : 2 ^ 22 * Nat.card ↥(co1Stab (L.vec x) ⊓ co1Stab (L.vec y) ⊓ co1Stab (L.vec t)) <
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({t} : Set G))) :
    CenterIn x y t := by
  have hmove : ∃ g₀ ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G), g₀ * u ≠ u * g₀ := by
    by_contra hcon
    push Not at hcon
    have heq : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
          Subgroup.centralizer ({t} : Set G) := by
      ext g
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨⟨-, hx⟩, hy⟩, ht⟩
        exact ⟨⟨hx, hy⟩, ht⟩
      · intro hg
        exact ⟨⟨⟨Subgroup.mem_centralizer_singleton_iff.2
          (hcon g (Subgroup.mem_inf.2 hg)), hg.1.1⟩, hg.1.2⟩, hg.2⟩
    have hc := L.card_inf_centralizer_three hxQ hyQ htQ hind
    rw [heq] at hc
    omega
  obtain ⟨g₀, hg₀, hg₀u⟩ := hmove
  obtain ⟨hg₀xy, hg₀t⟩ := Subgroup.mem_inf.1 hg₀
  obtain ⟨hg₀x, hg₀y⟩ := Subgroup.mem_inf.1 hg₀xy
  intro h hh hcen
  obtain ⟨hhxy, hht⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨hhx, hhy⟩ := Subgroup.mem_inf.1 hhxy
  refine mem_ext_of_central L hxQ hyQ htQ (Subgroup.mem_centralizer_singleton_iff.1 hg₀x)
    (Subgroup.mem_centralizer_singleton_iff.1 hg₀y)
    (Subgroup.mem_centralizer_singleton_iff.1 hg₀t) hg₀u
    (Subgroup.mem_centralizer_singleton_iff.1 hhx) (Subgroup.mem_centralizer_singleton_iff.1 hhy)
    (Subgroup.mem_centralizer_singleton_iff.1 hht) fun g hgx hgy hgt => ?_
  exact hcen g (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 hgx, Subgroup.mem_centralizer_singleton_iff.2 hgy⟩,
    Subgroup.mem_centralizer_singleton_iff.2 hgt⟩)

end Model

section Models

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem modelCenter_one
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ x y t : G, IsLineTriple a x y ∧ IsEightExt x y t ∧ twoBCount z₀ x y t = 1 ∧
      CenterIn x y t := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG (IsConj.refl z₀)
  obtain ⟨hx0, hy0, hxy0⟩ := refPair
  obtain ⟨⟨h1a, h1b, h1c, h1d⟩, -⟩ := eightPatterns
  obtain ⟨x, hxQ, hx⟩ := L.vec_surj (toVecD 24 2)
  obtain ⟨y, hyQ, hy⟩ := L.vec_surj (toVecD 24 4)
  obtain ⟨t, htQ, ht⟩ := L.vec_surj (toVecD 24 1)
  have hxo : L.vec x ∈ co1Orbit 0 := by rw [hx]; exact hx0
  have hyo : L.vec y ∈ co1Orbit 0 := by rw [hy]; exact hy0
  have hxyo : L.vec x + L.vec y ∈ co1Orbit 0 := by rw [hx, hy]; exact hxy0
  have k := isEightExt_of_pattern I hG L hxQ hyQ htQ hxo hyo hxyo (p₀ := true) (p₁ := false)
    (p₂ := false) (p₃ := false) (Or.inl ⟨rfl, by rw [ht]; exact h1a⟩)
    (Or.inr ⟨rfl, by rw [ht, hx]; exact h1b⟩) (Or.inr ⟨rfl, by rw [ht, hy]; exact h1c⟩)
    (Or.inr ⟨rfl, by rw [ht, hx, hy]; exact h1d⟩)
  have hcnt : twoBCount z₀ x y t = 1 := k.2.2
  have hind : LinearIndependent (ZMod 2) ![L.vec x, L.vec y, L.vec t] := by
    rw [hx, hy, ht]
    exact linearIndependent_of_pattern hx0 hy0 hxy0 h1a h1b h1c h1d
  refine ⟨x, y, t, k.1, k.2.1, hcnt, centerIn_of_card_lt L hxQ hyQ htQ hind ?_⟩
  rw [eightCentOrders_of I hG x y t k.1 k.2.1, hcnt, hx, hy, ht]
  have h := card_stab_le_pair (toVecD 24 1)
  generalize Nat.card ↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4) ⊓ co1Stab (toVecD 24 1)) = N
    at h ⊢
  norm_num [eightCentOrder]
  omega

theorem modelCenter_three
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ x y t : G, IsLineTriple a x y ∧ IsEightExt x y t ∧ twoBCount z₀ x y t = 3 ∧
      CenterIn x y t := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG (IsConj.refl z₀)
  obtain ⟨hx0, hy0, hxy0⟩ := refPair
  obtain ⟨h3, h3a, h3b, h3c⟩ := (eightPatterns).2
  obtain ⟨x, hxQ, hx⟩ := L.vec_surj (toVecD 24 2)
  obtain ⟨y, hyQ, hy⟩ := L.vec_surj (toVecD 24 4)
  obtain ⟨t, htQ, ht⟩ := L.vec_surj (toVecD 24 28)
  have hxo : L.vec x ∈ co1Orbit 0 := by rw [hx]; exact hx0
  have hyo : L.vec y ∈ co1Orbit 0 := by rw [hy]; exact hy0
  have hxyo : L.vec x + L.vec y ∈ co1Orbit 0 := by rw [hx, hy]; exact hxy0
  have k := isEightExt_of_pattern I hG L hxQ hyQ htQ hxo hyo hxyo (p₀ := false) (p₁ := true)
    (p₂ := true) (p₃ := true) (Or.inr ⟨rfl, by rw [ht]; exact h3⟩)
    (Or.inl ⟨rfl, by rw [ht, hx]; exact h3a⟩) (Or.inl ⟨rfl, by rw [ht, hy]; exact h3b⟩)
    (Or.inl ⟨rfl, by rw [ht, hx, hy]; exact h3c⟩)
  have hcnt : twoBCount z₀ x y t = 3 := k.2.2
  have hind : LinearIndependent (ZMod 2) ![L.vec x, L.vec y, L.vec t] := by
    rw [hx, hy, ht]
    exact linearIndependent_of_pattern hx0 hy0 hxy0 h3 h3a h3b h3c
  refine ⟨x, y, t, k.1, k.2.1, hcnt, centerIn_of_card_lt L hxQ hyQ htQ hind ?_⟩
  rw [eightCentOrders_of I hG x y t k.1 k.2.1, hcnt, hx, hy, ht]
  have h := card_stab_three_lt
  generalize Nat.card ↥(co1Stab (toVecD 24 2) ⊓ co1Stab (toVecD 24 4) ⊓ co1Stab (toVecD 24 28)) = N
    at h ⊢
  norm_num [eightCentOrder]
  omega

theorem modelCenter_four
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∃ x y t : G, IsLineTriple a x y ∧ IsEightExt x y t ∧ twoBCount z₀ x y t = 4 ∧
      CenterIn x y t := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG (IsConj.refl z₀)
  obtain ⟨hx0, hy0, hxy0, h4, h4a, h4b, h4c⟩ := refPattern
  obtain ⟨x, hxQ, hx⟩ := L.vec_surj (toVecD 24 2)
  obtain ⟨y, hyQ, hy⟩ := L.vec_surj (toVecD 24 4)
  obtain ⟨t, htQ, ht⟩ := L.vec_surj (toVecD 24 cosetBase)
  have hxo : L.vec x ∈ co1Orbit 0 := by rw [hx]; exact hx0
  have hyo : L.vec y ∈ co1Orbit 0 := by rw [hy]; exact hy0
  have hxyo : L.vec x + L.vec y ∈ co1Orbit 0 := by rw [hx, hy]; exact hxy0
  have k := isEightExt_of_pattern I hG L hxQ hyQ htQ hxo hyo hxyo (p₀ := true) (p₁ := true)
    (p₂ := true) (p₃ := true) (Or.inl ⟨rfl, by rw [ht]; exact h4⟩)
    (Or.inl ⟨rfl, by rw [ht, hx]; exact h4a⟩) (Or.inl ⟨rfl, by rw [ht, hy]; exact h4b⟩)
    (Or.inl ⟨rfl, by rw [ht, hx, hy]; exact h4c⟩)
  have hcnt : twoBCount z₀ x y t = 4 := k.2.2
  have hind : LinearIndependent (ZMod 2) ![L.vec x, L.vec y, L.vec t] := by
    rw [hx, hy, ht]
    exact refPattern.linearIndependent
  refine ⟨x, y, t, k.1, k.2.1, hcnt, centerIn_of_card_lt L hxQ hyQ htQ hind ?_⟩
  rw [eightCentOrders_of I hG x y t k.1 k.2.1, hcnt, hx, hy, ht, card_inf_stab_three refPattern]
  norm_num [eightCentOrder]

theorem exists_model_center
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (n : ℕ)
    (hn : n = 1 ∨ n = 3 ∨ n = 4) :
    ∃ x y t : G, IsLineTriple a x y ∧ IsEightExt x y t ∧ twoBCount z₀ x y t = n ∧
      CenterIn x y t := by
  rcases hn with rfl | rfl | rfl
  · exact modelCenter_one I hG
  · exact modelCenter_three I hG
  · exact modelCenter_four I hG

end Models

end S365

end CFSG.Monster.GMS

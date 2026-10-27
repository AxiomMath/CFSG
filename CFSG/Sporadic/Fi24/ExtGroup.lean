module

public import CFSG.Sporadic.Fi24.ExtInvolution

public section

namespace CFSG.Sporadic.Fi24

open CFSG.F3.Native Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def R :
    Subgroup (GL (Fin 781) (ZMod 3)) :=
  Subgroup.closure ((J : Set (GL (Fin 781) (ZMod 3))) ∪ {tT})

theorem J_le_R :
    J ≤ R := fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem tT_mem_R :
    tT ∈ R := Subgroup.subset_closure (Or.inr rfl)

theorem conj_mem'
    {g : GL (Fin 781) (ZMod 3)} (hg : g * tT ∈ J) : tT * g ∈ J := by
  have := conj_mem hg
  simp only [mul_assoc, tT_mul_tT, mul_one] at this
  exact this

@[expose] noncomputable def JT :
    Subgroup (GL (Fin 781) (ZMod 3)) where
  carrier := {x | x ∈ J ∨ x * tT ∈ J}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (J.mul_mem hx hy)
    · right; rw [mul_assoc]; exact J.mul_mem hx hy
    · right
      have e : x * y * tT = (x * tT) * (tT * y * tT) := by
        simp only [mul_assoc]; rw [← mul_assoc tT tT, tT_mul_tT, one_mul]
      rw [e]; exact J.mul_mem hx (conj_mem hy)
    · left
      have e : x * y = (x * tT) * (tT * y) := by
        rw [mul_assoc, ← mul_assoc tT tT, tT_mul_tT, one_mul]
      rw [e]; exact J.mul_mem hx (conj_mem' hy)
  one_mem' := Or.inl J.one_mem
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (J.inv_mem hx)
    · right
      have e : x⁻¹ * tT = tT * (x * tT)⁻¹ * tT := by
        rw [mul_inv_rev, tT_inv]; simp only [mul_assoc]; rw [← mul_assoc tT tT, tT_mul_tT, one_mul]
      rw [e]; exact conj_mem (J.inv_mem hx)

theorem mem_R_iff
    (x : GL (Fin 781) (ZMod 3)) : x ∈ R ↔ x ∈ J ∨ x * tT ∈ J := by
  have hle : R ≤ JT := by
    rw [R, Subgroup.closure_le]
    rintro y (hy | rfl)
    · exact Or.inl hy
    · exact Or.inr (by rw [tT_mul_tT]; exact J.one_mem)
  constructor
  · intro hx; exact hle hx
  · rintro (hx | hx)
    · exact J_le_R hx
    · have : x = (x * tT) * tT := by rw [mul_assoc, tT_mul_tT, mul_one]
      rw [this]; exact R.mul_mem (J_le_R hx) tT_mem_R

theorem exists_of_mem_R
    {x : GL (Fin 781) (ZMod 3)} (hx : x ∈ R) :
    ∃ j ∈ J, x = j ∨ x = j * tT := by
  rcases (mem_R_iff x).1 hx with h | h
  · exact ⟨x, h, Or.inl rfl⟩
  · exact ⟨x * tT, h, Or.inr (by rw [mul_assoc, tT_mul_tT, mul_one])⟩

theorem not_mem_and_mul_mem
    {x : GL (Fin 781) (ZMod 3)} (h1 : x ∈ J) (h2 : x * tT ∈ J) : False := by
  apply tT_not_mem
  have : tT = x⁻¹ * (x * tT) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]; exact J.mul_mem (J.inv_mem h1) h2

@[expose] noncomputable def tR :
    R := ⟨tT, tT_mem_R⟩

@[expose] noncomputable def jR :
    J →* R := Subgroup.inclusion J_le_R

theorem coe_jR
    (g : J) : ((jR g : R) : GL (Fin 781) (ZMod 3)) = g := rfl

theorem jR_injective :
    Function.Injective jR := Subgroup.inclusion_injective J_le_R

theorem tR_mul_tR :
    tR * tR = 1 := Subtype.ext tT_mul_tT

theorem tR_inv :
    tR⁻¹ = tR := inv_eq_of_mul_eq_one_right tR_mul_tR

theorem tR_mul_tR_mul
    (x : R) : tR * (tR * x) = x := by rw [← mul_assoc, tR_mul_tR, one_mul]

theorem tR_ne_one :
    tR ≠ 1 := fun h => tT_ne_one (by have := congrArg Subtype.val h; exact this)

theorem orderOf_tR :
    orderOf tR = 2 := orderOf_eq_prime (by rw [pow_two]; exact tR_mul_tR) tR_ne_one

theorem tR_mul_jR_mul_tR
    (g : J) : tR * jR g * tR = jR (tAut g) := rfl

theorem eq_jR_or
    (x : R) : ∃ g : J, x = jR g ∨ x = jR g * tR := by
  obtain ⟨j, hj, h | h⟩ := exists_of_mem_R x.2
  · exact ⟨⟨j, hj⟩, Or.inl (Subtype.ext h)⟩
  · exact ⟨⟨j, hj⟩, Or.inr (Subtype.ext h)⟩

noncomputable abbrev JR :
    Subgroup R := J.subgroupOf R

theorem mem_JR_iff
    (x : R) : x ∈ JR ↔ (x : GL (Fin 781) (ZMod 3)) ∈ J := Subgroup.mem_subgroupOf

theorem jR_mem_JR
    (g : J) : jR g ∈ JR := (mem_JR_iff (jR g)).2 g.2

theorem range_jR : jR.range = JR := by
  ext x
  rw [mem_JR_iff]
  constructor
  · rintro ⟨g, rfl⟩; exact g.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem tR_not_mem_JR :
    tR ∉ JR := fun h => tT_not_mem ((mem_JR_iff tR).1 h)

theorem normal_JR : JR.Normal := by
  constructor
  intro n hn g
  rw [mem_JR_iff] at hn ⊢
  obtain ⟨j, hj, h | h⟩ := exists_of_mem_R g.2
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h]
    exact J.mul_mem (J.mul_mem hj hn) (J.inv_mem hj)
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, mul_inv_rev, tT_inv]
    have e : j * tT * n * (tT * j⁻¹) = j * (tT * n * tT) * j⁻¹ := by simp only [mul_assoc]
    rw [e]
    exact J.mul_mem (J.mul_mem hj (conj_mem hn)) (J.inv_mem hj)

theorem index_JR : JR.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨tR, fun b => ?_⟩
  rw [mem_JR_iff, mem_JR_iff, Subgroup.coe_mul]
  rcases (mem_R_iff b).1 b.2 with h | h
  · exact Or.inr ⟨h, fun h' => not_mem_and_mul_mem h h'⟩
  · exact Or.inl ⟨h, fun h' => not_mem_and_mul_mem h' h⟩

theorem card_JR :
    Nat.card JR = Nat.card J :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe J_le_R).toEquiv

theorem card_R :
    Nat.card R = 2510411418381323442585600 := by
  rw [← JR.card_mul_index, card_JR, index_JR, card_J]

instance :
    Finite R := Nat.finite_of_card_ne_zero (by rw [card_R]; norm_num)

end CFSG.Sporadic.Fi24

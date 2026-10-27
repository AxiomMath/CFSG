module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4RepGL
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.GL42

open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def xorF (m n : Fin 16) : Fin 16 := ⟨(m.val ^^^ n.val) % 16, Nat.mod_lt _ (by decide)⟩

theorem xorF_bits : ∀ m n : Fin 16,
    (xorF m n).val % 2 = (m.val % 2 + n.val % 2) % 2 ∧
      (xorF m n).val / 2 % 2 = (m.val / 2 % 2 + n.val / 2 % 2) % 2 ∧
      (xorF m n).val / 4 % 2 = (m.val / 4 % 2 + n.val / 4 % 2) % 2 ∧
      (xorF m n).val / 8 % 2 = (m.val / 8 % 2 + n.val / 8 % 2) % 2 := by
  decide

theorem xorF_self : ∀ m : Fin 16, xorF m m = 0 := by decide

theorem eq_of_xorF_eq_zero : ∀ m n : Fin 16, xorF m n = 0 → m = n := by decide

theorem lt_sixteen_xor {x y : ℕ} (hx : x < 16) (hy : y < 16) : x ^^^ y < 16 :=
  Nat.xor_lt_two_pow (n := 4) hx hy

@[expose] def sel (b : ℕ) (v : Fin 16) : Fin 16 := if b = 1 then v else 0

theorem app_eq (c : Code) (n : Fin 16) :
    c.app n = xorF (xorF (xorF (sel (n.val % 2) c.v0) (sel (n.val / 2 % 2) c.v1))
      (sel (n.val / 4 % 2) c.v2)) (sel (n.val / 8 % 2) c.v3) := by
  have h0 : (sel (n.val % 2) c.v0).val < 16 := (sel _ _).isLt
  have h1 : (sel (n.val / 2 % 2) c.v1).val < 16 := (sel _ _).isLt
  have h2 : (sel (n.val / 4 % 2) c.v2).val < 16 := (sel _ _).isLt
  have h3 : (sel (n.val / 8 % 2) c.v3).val < 16 := (sel _ _).isLt
  apply Fin.ext
  simp only [Code.app, xorF]
  rw [Nat.mod_eq_of_lt (lt_sixteen_xor h0 h1),
    Nat.mod_eq_of_lt (lt_sixteen_xor (lt_sixteen_xor h0 h1) h2)]
  congr 1
  congr 1
  · congr 1
    · congr 1
      · unfold sel; split_ifs <;> rfl
      · unfold sel; split_ifs <;> rfl
    · unfold sel; split_ifs <;> rfl
  · unfold sel; split_ifs <;> rfl

@[expose] def coord (z a p d : G) (n : Fin 16) : G :=
  z ^ (n.val % 2) * a ^ (n.val / 2 % 2) * p ^ (n.val / 4 % 2) * d ^ (n.val / 8 % 2)

structure Frame (z a p d : G) : Prop where
  comm : ∀ x ∈ ({z, a, p, d} : Set G), ∀ y ∈ ({z, a, p, d} : Set G), x * y = y * x
  sq : ∀ x ∈ ({z, a, p, d} : Set G), x ^ 2 = 1
  inj : ∀ n : Fin 16, coord z a p d n = 1 → n = 0

theorem pow_mod_two {x : G} (hx : x ^ 2 = 1) (k : ℕ) : x ^ k = x ^ (k % 2) := by
  conv_lhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, hx, one_pow, mul_one]

namespace Frame

variable {z a p d : G} (hF : Frame z a p d)

include hF

theorem coord_mul (m n : Fin 16) :
    coord z a p d m * coord z a p d n = coord z a p d (xorF m n) := by
  set A := Subgroup.closure ({z, a, p, d} : Set G) with hA
  have hpair : ({z, a, p, d} : Set G).Pairwise Commute := fun x hx y hy _ => hF.comm x hx y hy
  have := Subgroup.isMulCommutative_closure hpair
  have hz : z ∈ A := Subgroup.subset_closure (by simp)
  have ha : a ∈ A := Subgroup.subset_closure (by simp)
  have hp : p ∈ A := Subgroup.subset_closure (by simp)
  have hd : d ∈ A := Subgroup.subset_closure (by simp)
  have hsq : ∀ (x : G) (hx : x ∈ A), x ^ 2 = 1 → (⟨x, hx⟩ : ↥A) ^ 2 = 1 := fun x hx h =>
    Subtype.ext (by simpa using h)
  have hz2 := hsq z hz (hF.sq z (by simp))
  have ha2 := hsq a ha (hF.sq a (by simp))
  have hp2 := hsq p hp (hF.sq p (by simp))
  have hd2 := hsq d hd (hF.sq d (by simp))
  have hc : ∀ k : Fin 16, coord z a p d k =
      (((⟨z, hz⟩ : ↥A) ^ (k.val % 2) * (⟨a, ha⟩ : ↥A) ^ (k.val / 2 % 2) *
        (⟨p, hp⟩ : ↥A) ^ (k.val / 4 % 2) * (⟨d, hd⟩ : ↥A) ^ (k.val / 8 % 2) : ↥A) : G) :=
    fun k => by simp [coord]
  obtain ⟨e0, e1, e2, e3⟩ := xorF_bits m n
  rw [hc, hc, hc, ← Subgroup.coe_mul, e0, e1, e2, e3,
    ← pow_mod_two hz2 (m.val % 2 + n.val % 2), ← pow_mod_two ha2 (m.val / 2 % 2 + n.val / 2 % 2),
    ← pow_mod_two hp2 (m.val / 4 % 2 + n.val / 4 % 2),
    ← pow_mod_two hd2 (m.val / 8 % 2 + n.val / 8 % 2)]
  congr 1
  simp only [pow_add]
  ac_rfl

theorem coord_injective : Function.Injective (coord z a p d) := by
  intro m n h
  apply eq_of_xorF_eq_zero
  apply hF.inj
  rw [← hF.coord_mul, ← h, hF.coord_mul, xorF_self]
  simp [coord]

end Frame

theorem coord_sel (z a p d : G) (b : ℕ) (hb : b < 2) (v : Fin 16) :
    coord z a p d (sel b v) = coord z a p d v ^ b := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · simp [sel, coord]
  · simp [sel]


@[expose] def HasCode (z a p d x : G) (c : Code) : Prop :=
  x * z * x⁻¹ = coord z a p d c.v0 ∧ x * a * x⁻¹ = coord z a p d c.v1 ∧
    x * p * x⁻¹ = coord z a p d c.v2 ∧ x * d * x⁻¹ = coord z a p d c.v3

theorem coord_one_eq (z a p d : G) : coord z a p d 1 = z := by simp [coord]

theorem coord_two_eq (z a p d : G) : coord z a p d 2 = a := by simp [coord]

theorem coord_four_eq (z a p d : G) : coord z a p d 4 = p := by simp [coord]

theorem coord_eight_eq (z a p d : G) : coord z a p d 8 = d := by simp [coord]

theorem hasCode_one (z a p d : G) : HasCode z a p d 1 idC := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [idC, coord]

namespace HasCode

variable {z a p d x y : G} {c e : Code}

theorem conj (hF : Frame z a p d) (h : HasCode z a p d x c) (n : Fin 16) :
    x * coord z a p d n * x⁻¹ = coord z a p d (c.app n) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  rw [app_eq, ← hF.coord_mul, ← hF.coord_mul, ← hF.coord_mul,
    coord_sel z a p d _ (Nat.mod_lt _ (by decide)), coord_sel z a p d _ (Nat.mod_lt _ (by decide)),
    coord_sel z a p d _ (Nat.mod_lt _ (by decide)), coord_sel z a p d _ (Nat.mod_lt _ (by decide)),
    ← h0, ← h1, ← h2, ← h3, conj_pow, conj_pow, conj_pow, conj_pow]
  simp only [coord]
  group

theorem mul (hF : Frame z a p d) (hx : HasCode z a p d x c) (hy : HasCode z a p d y e) :
    HasCode z a p d (x * y) (c.comp e) := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  have e0 : x * y * z * (x * y)⁻¹ = x * (y * z * y⁻¹) * x⁻¹ := by group
  have e1 : x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
  have e2 : x * y * p * (x * y)⁻¹ = x * (y * p * y⁻¹) * x⁻¹ := by group
  have e3 : x * y * d * (x * y)⁻¹ = x * (y * d * y⁻¹) * x⁻¹ := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e0, h0, hx.conj hF]; rfl
  · rw [e1, h1, hx.conj hF]; rfl
  · rw [e2, h2, hx.conj hF]; rfl
  · rw [e3, h3, hx.conj hF]; rfl

theorem unique (hF : Frame z a p d) (h : HasCode z a p d x c) (h' : HasCode z a p d x e) :
    c = e := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨h0', h1', h2', h3'⟩ := h'
  cases c
  cases e
  simp only [Code.mk.injEq]
  exact ⟨hF.coord_injective (h0.symm.trans h0'), hF.coord_injective (h1.symm.trans h1'),
    hF.coord_injective (h2.symm.trans h2'), hF.coord_injective (h3.symm.trans h3')⟩

theorem inv (hF : Frame z a p d) (h : HasCode z a p d x c) (hc : c.comp c = idC) :
    HasCode z a p d x⁻¹ c := by
  have hxx : HasCode z a p d (x * x) idC := hc ▸ h.mul hF h
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨k0, k1, k2, k3⟩ := hxx
  have key : ∀ b : G, x * x * b * (x * x)⁻¹ = b → x⁻¹ * b * x⁻¹⁻¹ = x * b * x⁻¹ := by
    intro b hb
    calc x⁻¹ * b * x⁻¹⁻¹ = x⁻¹ * (x * x * b * (x * x)⁻¹) * x := by rw [hb, inv_inv]
      _ = x * b * x⁻¹ := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key z (by rw [k0]; simp [idC, coord]), h0]
  · rw [key a (by rw [k1]; simp [idC, coord]), h1]
  · rw [key p (by rw [k2]; simp [idC, coord]), h2]
  · rw [key d (by rw [k3]; simp [idC, coord]), h3]

theorem exists_preimage (hF : Frame z a p d) (h : HasCode z a p d x c) (n : Fin 16) :
    ∃ m : Fin 16, x * coord z a p d m * x⁻¹ = coord z a p d n := by
  have hinj : Function.Injective c.app := by
    intro m m' hm
    have := h.conj hF m
    rw [hm, ← h.conj hF m'] at this
    exact hF.coord_injective (by simpa using this)
  obtain ⟨m, hm⟩ := (Finite.injective_iff_surjective.mp hinj) n
  exact ⟨m, by rw [h.conj hF, hm]⟩

end HasCode

theorem false_of_index_two {T Q : Subgroup G} (hT : ¬ 2 ∣ T.index) (hTQ : T ≤ Q) {g : G}
    (hg : g ∉ Q) (hg2 : g * g ∈ Q) (hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : False := by
  have hinv : ∀ x ∈ Q, g⁻¹ * x * g ∈ Q := fun x hx => by
    have e : g⁻¹ * x * g = (g * g)⁻¹ * (g * x * g⁻¹) * (g * g) := by group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hg2) (hgQ x hx)) hg2
  let Y : Subgroup G :=
    { carrier := {x | x ∈ Q ∨ g⁻¹ * x ∈ Q}
      one_mem' := Or.inl Q.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (Q.mul_mem hx hy)
        · right
          have e : g⁻¹ * (x * y) = g⁻¹ * x * g * (g⁻¹ * y) := by group
          rw [e]
          exact Q.mul_mem (hinv x hx) hy
        · right
          rw [← mul_assoc]
          exact Q.mul_mem hx hy
        · left
          have e : x * y = g * (g⁻¹ * x) * g⁻¹ * (g * g) * (g⁻¹ * y) := by group
          rw [e]
          exact Q.mul_mem (Q.mul_mem (hgQ _ hx) hg2) hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (Q.inv_mem hx)
        · right
          have e : g⁻¹ * x⁻¹ = g⁻¹ * (g⁻¹ * x)⁻¹ * g * (g * g)⁻¹ := by group
          rw [e]
          exact Q.mul_mem (hinv _ (Q.inv_mem hx)) (Q.inv_mem hg2) }
  have hQY : Q ≤ Y := fun x hx => Or.inl hx
  have hgY : g ∈ Y := Or.inr (by rw [inv_mul_cancel]; exact Q.one_mem)
  have h2 : Q.relIndex Y = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgY⟩, fun b => ?_⟩
    rcases b.2 with hb | hb
    · have h1 : (b : G) * g ∉ Q := fun h => hg (by
        have := Q.mul_mem (Q.inv_mem hb) h
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      exact Or.inr ⟨hb, h1⟩
    · have h1 : (b : G) ∉ Q := fun h => hg (by
        have := Q.mul_mem h (Q.inv_mem hb)
        rwa [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at this)
      have h3 : (b : G) * g ∈ Q := by
        have e : (b : G) * g = g * (g⁻¹ * b) * g⁻¹ * (g * g) := by group
        rw [e]
        exact Q.mul_mem (hgQ _ hb) hg2
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      exact Or.inl ⟨h3, h1⟩
  have hTY := Subgroup.relIndex_mul_relIndex T Q Y hTQ hQY
  have hTi := Subgroup.relIndex_mul_index (hTQ.trans hQY)
  apply hT
  rw [← hTi, ← hTY, h2]
  exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _

end CFSG.Quasithin.H13.GL42

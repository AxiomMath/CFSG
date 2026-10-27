module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType.UnitTv

variable {p : ℕ}

section Biadd

variable {G : Type*} [AddCommGroup G]

theorem biadd_nsmul_right (B : G → G → ZMod p) (hBr : ∀ a b b', B a (b + b') = B a b + B a b')
    (a b : G) (n : ℕ) : B a (n • b) = n * B a b := by
  have h0 : B a 0 = 0 := by
    have := hBr a 0 0
    rw [add_zero] at this
    linear_combination (-1 : ZMod p) * this
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [succ_nsmul, hBr, ih]
    push_cast
    ring

theorem biadd_nsmul_left (B : G → G → ZMod p) (hBl : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (a b : G) (n : ℕ) : B (n • a) b = n * B a b := by
  have h0 : B 0 b = 0 := by
    have := hBl 0 0 b
    rw [add_zero] at this
    linear_combination (-1 : ZMod p) * this
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [succ_nsmul, hBl, ih]
    push_cast
    ring

theorem biadd_zero_right (B : G → G → ZMod p) (hBr : ∀ a b b', B a (b + b') = B a b + B a b')
    (a : G) : B a 0 = 0 := by
  simpa using biadd_nsmul_right B hBr a 0 0

theorem biadd_zero_left (B : G → G → ZMod p) (hBl : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (b : G) : B 0 b = 0 := by
  simpa using biadd_nsmul_left B hBl 0 b 0

theorem biadd_neg_right (B : G → G → ZMod p) (hBr : ∀ a b b', B a (b + b') = B a b + B a b')
    (a b : G) : B a (-b) = - B a b := by
  have := hBr a b (-b)
  rw [add_neg_cancel, biadd_zero_right B hBr] at this
  linear_combination (-1 : ZMod p) * this

theorem biadd_neg_left (B : G → G → ZMod p) (hBl : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (a b : G) : B (-a) b = - B a b := by
  have := hBl a (-a) b
  rw [add_neg_cancel, biadd_zero_left B hBl] at this
  linear_combination (-1 : ZMod p) * this

end Biadd

theorem iso_identity {G : Type*} [AddCommGroup G] (B : G → G → ZMod p)
    (hBl : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (hBr : ∀ a b b', B a (b + b') = B a b + B a b') (x y nx ny : G) {Tx Ty : G}
    (hx : Tx = x + nx) (hy : Ty = y + ny) (h : B Tx Ty = B x y) :
    B x ny + B nx y + B nx ny = 0 := by
  rw [hx, hy, hBl, hBr, hBr] at h
  linear_combination h

theorem false_of_similitude_transvection [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*}
    [AddCommGroup G] (M : AddSubgroup G) (B : G → G → ZMod p)
    (hBl : ∀ a a' b, B (a + a') b = B a b + B a' b)
    (hBr : ∀ a b b', B a (b + b') = B a b + B a b')
    (hsymm : ∀ a b, B a b = B b a)
    (hnd : ∀ a ∈ M, (∀ b ∈ M, B a b = 0) → a = 0)
    (T : G →+ G) (hTM : ∀ a ∈ M, T a ∈ M) (μ : ZMod p)
    (hsim : ∀ a ∈ M, ∀ b ∈ M, B (T a) (T b) = μ * B a b)
    (hN : ∀ a ∈ M, T (T a - a) = T a - a)
    (hrank : ∀ a ∈ M, ∀ b ∈ M, T a - a ≠ 0 → ∃ c : ℕ, T b - b = c • (T a - a))
    (hne : ∃ u ∈ M, T u - u ≠ 0) : False := by
  obtain ⟨u, hu, hNu⟩ := hne
  set v := T u - u with hv
  have hvM : v ∈ M := M.sub_mem (hTM u hu) hu
  have hNv : T v = v := hN u hu
  have hy : ∀ y ∈ M, ∃ c : ℕ, T y - y = c • v := fun y hy => hrank u hu y hy hNu
  have hTy : ∀ y ∈ M, ∀ c : ℕ, T y - y = c • v → T y = y + c • v := fun y _ c hc => by
    rw [← hc]
    abel
  have hE1 : ∀ y ∈ M, ∀ c : ℕ, T y - y = c • v →
      (1 - μ) * B v y + (c : ZMod p) * B v v = 0 := by
    intro y hyM c hc
    have h := hsim v hvM y hyM
    rw [hNv, hTy y hyM c hc, hBr, biadd_nsmul_right B hBr] at h
    linear_combination h
  have hE2 : (1 - μ) * B v v = 0 := by
    have h := hsim v hvM v hvM
    rw [hNv] at h
    linear_combination h
  have hμ : μ = 1 := by
    by_contra hμ1
    have h1μ : (1 - μ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ1)
    have hvv : B v v = 0 := (mul_eq_zero.mp hE2).resolve_left h1μ
    have hBv : ∀ y ∈ M, B v y = 0 := by
      intro y hyM
      obtain ⟨c, hc⟩ := hy y hyM
      have h := hE1 y hyM c hc
      rw [hvv, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1μ
    exact hNu (hnd v hvM hBv)
  have hiso : ∀ x ∈ M, ∀ y ∈ M, B x (T y - y) + B (T x - x) y + B (T x - x) (T y - y) = 0 := by
    intro x hx y hy'
    have h := hsim x hx y hy'
    rw [hμ, one_mul] at h
    exact iso_identity B hBl hBr x y _ _ (by abel) (by abel) h
  have hNv0 : T v - v = 0 := by rw [hNv]; exact sub_self v
  have hvv : B v v = 0 := by
    have h := hiso u hu v hvM
    rw [hNv0, biadd_zero_right B hBr, biadd_zero_right B hBr, ← hv] at h
    linear_combination h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have huv : B u v = 0 := by
    have h := hiso u hu u hu
    rw [hsymm v u, hvv] at h
    have h' : 2 * B u v = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hBv : ∀ y ∈ M, B v y = 0 := by
    intro y hyM
    obtain ⟨c, hc⟩ := hy y hyM
    have h := hiso u hu y hyM
    rw [hc, biadd_nsmul_right B hBr, biadd_nsmul_right B hBr, huv, hvv] at h
    linear_combination h
  exact hNu (hnd v hvM hBv)

theorem exists_perm_apply_apply {d : ℕ} {a b i j : Fin d} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ a = i ∧ σ b = j := by
  refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hab ?_) hij
    have h2 : Equiv.swap a i b = Equiv.swap a i a := by rw [Equiv.swap_apply_left]; exact h.symm
    exact ((Equiv.swap a i).injective h2).symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem form_vanish [Fact p.Prime] (hp2 : p ≠ 2) {d : ℕ} {G : Type*} [AddCommGroup G]
    (M : AddSubgroup G) (m : Fin d → Fin d → G) (k₀ i₀ i₁ : Fin d) (hi : i₀ ≠ i₁)
    (hmadd : ∀ i j k, m i j + m j k = m i k)
    (hspan : ∀ a ∈ M, a ∈ AddSubgroup.closure (Set.range fun i : Fin d => m i k₀))
    (ρ : Equiv.Perm (Fin d) → G →+ G) (hρm : ∀ σ i j, ρ σ (m i j) = m (σ i) (σ j))
    (hmM : ∀ i j, m i j ∈ M) (D : G → G → ZMod p)
    (hDl : ∀ a a' b, D (a + a') b = D a b + D a' b)
    (hDr : ∀ a b b', D a (b + b') = D a b + D a b') (hsym : ∀ a b, D a b = D b a)
    (hinv : ∀ σ, ∀ a ∈ M, ∀ b ∈ M, D (ρ σ a) (ρ σ b) = D a b)
    (h01 : D (m i₀ i₁) (m i₀ i₁) = 0) : ∀ a ∈ M, ∀ b ∈ M, D a b = 0 := by
  have hmzero : ∀ a, m a a = 0 := fun a => by
    have := hmadd a a a
    exact add_eq_right.mp this
  have hmsub : ∀ a b, m a b = m a k₀ - m b k₀ := fun a b => by
    have := hmadd a b k₀
    rw [← this]
    abel
  have hdiag : ∀ a b, D (m a b) (m a b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hmzero, biadd_zero_left D hDl]
    · obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_apply_apply hi hab
      have h := hinv σ _ (hmM i₀ i₁) _ (hmM i₀ i₁)
      simp only [hρm, hσ0, hσ1] at h
      rw [h, h01]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hbase : ∀ a b, D (m a k₀) (m b k₀) = 0 := by
    intro a b
    have h1 := hdiag a b
    rw [hmsub a b] at h1
    have hxx := hdiag a k₀
    have hyy := hdiag b k₀
    simp only [sub_eq_add_neg, hDl, hDr, biadd_neg_left D hDl, biadd_neg_right D hDr] at h1
    rw [hsym (m b k₀) (m a k₀)] at h1
    have h3 : 2 * D (m a k₀) (m b k₀) = 0 := by linear_combination -h1 + hxx + hyy
    exact (mul_eq_zero.mp h3).resolve_left h2
  intro a ha b hb
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => D x y = 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hspan a ha) (hspan b hb)
  · rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hbase i j
  · intro x _
    exact biadd_zero_left D hDl x
  · intro x _
    exact biadd_zero_right D hDr x
  · intro x y z _ _ _ hxz hyz
    rw [hDl, hxz, hyz, add_zero]
  · intro y z x _ _ _ hxy hxz
    rw [hDr, hxy, hxz, add_zero]
  · intro x y _ _ hxy
    rw [biadd_neg_left D hDl, hxy, neg_zero]
  · intro x y _ _ hxy
    rw [biadd_neg_right D hDr, hxy, neg_zero]

theorem exists_nsmul_of_card_fix [Fact p.Prime] {G : Type*} [AddCommGroup G] [Finite G]
    (hGp : ∀ a : G, p • a = 0) (T : G →+ G)
    (hfix : Nat.card {a // T a = a} * p = Nat.card G) :
    ∀ a b : G, T a - a ≠ 0 → ∃ c : ℕ, T b - b = c • (T a - a) := by
  intro a b ha
  let N : G →+ G := AddMonoidHom.mk' (fun x => T x - x) (fun x y => by rw [map_add]; abel)
  have hker : Nat.card N.ker = Nat.card {x // T x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]
      exact sub_eq_zero)
  have hcard := AddSubgroup.card_ker_mul_card_range N
  rw [hker, ← hfix] at hcard
  have hpos : 0 < Nat.card {x // T x = x} := by
    have : Nonempty {x // T x = x} := ⟨⟨0, map_zero T⟩⟩
    exact Nat.card_pos
  have hR : Nat.card N.range = p := Nat.eq_of_mul_eq_mul_left hpos hcard
  have hvR : AddSubgroup.zmultiples (T a - a) ≤ N.range := by
    rw [AddSubgroup.zmultiples_le]
    exact ⟨a, rfl⟩
  have hZ : Nat.card (AddSubgroup.zmultiples (T a - a)) = p := by
    rw [Nat.card_zmultiples]
    exact addOrderOf_eq_prime (hGp _) ha
  have heq : AddSubgroup.zmultiples (T a - a) = N.range :=
    AddSubgroup.eq_of_le_of_card_ge hvR (by rw [hR, hZ])
  have hb : T b - b ∈ AddSubgroup.zmultiples (T a - a) := heq ▸ ⟨b, rfl⟩
  rw [← mem_multiples_iff_mem_zmultiples, AddSubmonoid.mem_multiples_iff] at hb
  exact ⟨hb.choose, hb.choose_spec.symm⟩

end CFSG.StandardType.UnitTv

end

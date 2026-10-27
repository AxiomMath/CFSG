module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ReflExt

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem coords_dim_n {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) [Module.Finite (ZMod 3) V]
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = C i j)
    (hind : LinearIndependent (ZMod 3) h) (hdim : finrank (ZMod 3) V = n) :
    ∃ ε : V ≃ₗ[ZMod 3] (Fin n → ZMod 3), (∀ i, ε (h i) = Pi.single i 1) ∧
      ∀ i w, α i w = ∑ j, C i j * ε w j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let b := basisOfLinearIndependentOfCardEqFinrank' (K := ZMod 3) h hind (by simp [hdim])
  have hb : ∀ i, b i = h i := fun i => by simp [b]
  refine ⟨b.equivFun, ?_, ?_⟩
  · intro i
    funext j
    rw [← hb i, Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  · intro i w
    conv_lhs => rw [← b.sum_equivFun w]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb j, hpair i j]
    ring

theorem coords_dim_succ {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) [Module.Finite (ZMod 3) V]
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = C i j)
    (hind : LinearIndependent (ZMod 3) h) (e : V)
    (he : e ∉ Submodule.span (ZMod 3) (Set.range h)) (hdim : finrank (ZMod 3) V = n + 1) :
    ∃ ε : V ≃ₗ[ZMod 3] (Fin (n + 1) → ZMod 3),
      (∀ i, ε (h i) = Pi.single (Fin.castSucc i) 1) ∧ ε e = Pi.single (Fin.last n) 1 ∧
      ∀ i w, α i w = ∑ j : Fin n, C i j * ε w (Fin.castSucc j) + α i e * ε w (Fin.last n) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let v : Fin (n + 1) → V := Fin.snoc h e
  have hv : LinearIndependent (ZMod 3) v := linearIndependent_finSnoc.mpr ⟨hind, he⟩
  let b := basisOfLinearIndependentOfCardEqFinrank' (K := ZMod 3) v hv (by simp [hdim])
  have hb : ∀ k, b k = v k := fun k => by simp [b]
  have hvc : ∀ i : Fin n, v (Fin.castSucc i) = h i := fun i => by simp [v]
  have hvl : v (Fin.last n) = e := by simp [v]
  refine ⟨b.equivFun, ?_, ?_, ?_⟩
  · intro i
    funext j
    rw [← hvc i, ← hb, Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  · funext j
    rw [← hvl, ← hb, Basis.equivFun_self]
    simp [Pi.single_apply, eq_comm]
  · intro i w
    conv_lhs => rw [← b.sum_equivFun w]
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Fin.sum_univ_castSucc]
    have hj : ∀ j : Fin n, b.equivFun w (Fin.castSucc j) * α i (b (Fin.castSucc j)) =
        C i j * b.equivFun w (Fin.castSucc j) := by
      intro j
      rw [hb, hvc, hpair]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hj j), hb, hvl]
    ring

theorem normalize_e_aux {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) (B : Matrix (Fin n) (Fin n) (ZMod 3))
    (x₀ : Fin n → ZMod 3) (i0 : Fin n) (hx0 : x₀ i0 = 1)
    (hB : ∀ u : Fin n → ZMod 3, x₀ ⬝ᵥ u = 0 → C.mulVec (B.mulVec u) = u)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = C i j)
    (e' : V) (l s : ZMod 3)
    (hts : l * (x₀ ⬝ᵥ (fun i => α i e')) = s) :
    ∃ w : Fin n → ZMod 3, ∀ i, α i (l • e' - ∑ j, w j • h j) = if i = i0 then s else 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let t : Fin n → ZMod 3 := fun i => l * α i e' - if i = i0 then s else 0
  have ht : x₀ ⬝ᵥ t = 0 := by
    have : x₀ ⬝ᵥ t = l * (x₀ ⬝ᵥ (fun i => α i e')) - s := by
      simp only [t, dotProduct, mul_sub, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · simp [mul_ite, Finset.sum_ite_eq', hx0]
    rw [this, hts, sub_self]
  refine ⟨B.mulVec t, ?_⟩
  intro i
  have hCw := congrFun (hB t ht) i
  have hsum : α i (∑ j, (B.mulVec t) j • h j) = (C.mulVec (B.mulVec t)) i := by
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, hpair]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [map_sub, map_smul, hsum, hCw]
  simp only [t, smul_eq_mul]
  ring

theorem normalize_e {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) (B : Matrix (Fin n) (Fin n) (ZMod 3))
    (x₀ : Fin n → ZMod 3) (i0 : Fin n) (hx0 : x₀ i0 = 1)
    (hB : ∀ u : Fin n → ZMod 3, x₀ ⬝ᵥ u = 0 → C.mulVec (B.mulVec u) = u)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = C i j)
    (e' : V) :
    ∃ (l s : ZMod 3) (w : Fin n → ZMod 3), l ≠ 0 ∧ (s = 0 ∨ s = 1) ∧
      (s = 0 ↔ x₀ ⬝ᵥ (fun i => α i e') = 0) ∧
      ∀ i, α i (l • e' - ∑ j, w j • h j) = if i = i0 then s else 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hs : x₀ ⬝ᵥ (fun i => α i e') = 0
  · obtain ⟨w, hw⟩ := normalize_e_aux C B x₀ i0 hx0 hB h α hpair e' 1 0 (by rw [hs]; ring)
    exact ⟨1, 0, w, one_ne_zero, Or.inl rfl, ⟨fun _ => hs, fun _ => rfl⟩, hw⟩
  · obtain ⟨w, hw⟩ := normalize_e_aux C B x₀ i0 hx0 hB h α hpair e'
      ((x₀ ⬝ᵥ (fun i => α i e'))⁻¹) 1 (by rw [inv_mul_cancel₀ hs])
    exact ⟨_, 1, w, inv_ne_zero hs, Or.inr rfl,
      ⟨fun h1 => absurd h1 one_ne_zero, fun h2 => absurd h2 hs⟩, hw⟩

theorem x_coords {n : ℕ} (C : Matrix (Fin n) (Fin n) (ZMod 3)) (x₀ : Fin n → ZMod 3)
    (hker : ∀ y : Fin n → ZMod 3, C.mulVec y = 0 → ∃ c : ZMod 3, y = c • x₀)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = C i j)
    (x : V) (hx : x ≠ 0) (hxker : ∀ i, α i x = 0)
    (hxmem : x ∈ Submodule.span (ZMod 3) (Set.range h)) :
    ∃ c : ZMod 3, c ≠ 0 ∧ x = ∑ j, (c * x₀ j) • h j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hxmem
  have hCy : C.mulVec y = 0 := by
    funext i
    have := hxker i
    rw [← hy] at this
    simp only [map_sum, map_smul, smul_eq_mul, hpair] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨c, hc⟩ := hker y hCy
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx
    rw [← hy, hc]
    simp
  · rw [← hy, hc]
    simp [smul_eq_mul]

end CFSG.ReflExt

end

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Sylow
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRefl

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Module

variable {𝕜 : Type*} [Field 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V]

private theorem mem_ker_sub_one_iff {u : Module.End 𝕜 V} {x : V} :
    x ∈ LinearMap.ker (u - 1) ↔ u x = x := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

private theorem mem_ker_add_one_iff {u : Module.End 𝕜 V} {x : V} :
    x ∈ LinearMap.ker (u + 1) ↔ u x = -x := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]

private theorem isCompl_ker_sub_one_ker_add_one (h2 : (2 : 𝕜) ≠ 0)
    {s : Module.End 𝕜 V} (hs : s * s = 1) :
    IsCompl (LinearMap.ker (s - 1)) (LinearMap.ker (s + 1)) := by
  simpa [Module.End.eigenspace_def, sub_neg_eq_add] using
    CFSG.StandardType.SpFrame.isCompl_eigenspace_one_neg_one (V := V) h2 hs

private theorem commute_apply {s t : Module.End 𝕜 V} (h : s * t = t * s) (x : V) :
    s (t x) = t (s x) := by
  have := congrArg (fun f : Module.End 𝕜 V => f x) h
  simpa [Module.End.mul_apply] using this

private theorem mapsTo_ker_sub_one_of_commute {u q : Module.End 𝕜 V} (h : Commute u q) :
    ∀ x ∈ LinearMap.ker (q - 1), u x ∈ LinearMap.ker (q - 1) := by
  intro x hx
  rw [mem_ker_sub_one_iff] at hx ⊢
  have hq : q (u x) = u (q x) := by
    have := congrArg (fun f : Module.End 𝕜 V => f x) h.eq
    simpa [Module.End.mul_apply] using this.symm
  rw [hq, hx]

private theorem mapsTo_ker_add_one_of_commute {u q : Module.End 𝕜 V} (h : Commute u q) :
    ∀ x ∈ LinearMap.ker (q + 1), u x ∈ LinearMap.ker (q + 1) := by
  intro x hx
  rw [mem_ker_add_one_iff] at hx ⊢
  have hq : q (u x) = u (q x) := by
    have := congrArg (fun f : Module.End 𝕜 V => f x) h.eq
    simpa [Module.End.mul_apply] using this.symm
  rw [hq, hx, map_neg]

private theorem mapsTo_sub_one {P : Submodule 𝕜 V} {u : Module.End 𝕜 V}
    (h : ∀ x ∈ P, u x ∈ P) : ∀ x ∈ P, (u - 1) x ∈ P := by
  intro x hx
  rw [LinearMap.sub_apply, Module.End.one_apply]
  exact P.sub_mem (h x hx) hx

private theorem mapsTo_add_one {P : Submodule 𝕜 V} {u : Module.End 𝕜 V}
    (h : ∀ x ∈ P, u x ∈ P) : ∀ x ∈ P, (u + 1) x ∈ P := by
  intro x hx
  rw [LinearMap.add_apply, Module.End.one_apply]
  exact P.add_mem (h x hx) hx

private theorem mul_sub_one_apply_of_mem_ker_sub_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) {x : V} (hx : x ∈ LinearMap.ker (s - 1)) :
    (s * t - 1) x = (t - 1) x := by
  have hx1 : s x = x := (mem_ker_sub_one_iff (u := s)).1 hx
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, commute_apply hst x, hx1,
    LinearMap.sub_apply, Module.End.one_apply]

private theorem mul_sub_one_apply_of_mem_ker_add_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) {x : V} (hx : x ∈ LinearMap.ker (s + 1)) :
    (s * t - 1) x = -((t + 1) x) := by
  have hx1 : s x = -x := (mem_ker_add_one_iff (u := s)).1 hx
  have hstx : s (t x) = -t x := by rw [commute_apply hst, hx1, map_neg]
  calc (s * t - 1) x = s (t x) - x := by
        rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
    _ = -t x - x := by rw [hstx]
    _ = -((t + 1) x) := by
        rw [LinearMap.add_apply, Module.End.one_apply]
        abel

private theorem mul_sub_one_mapsTo_ker_sub_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) :
    ∀ x ∈ LinearMap.ker (s - 1), (s * t - 1) x ∈ LinearMap.ker (s - 1) := by
  intro x hx
  rw [mul_sub_one_apply_of_mem_ker_sub_one hst hx]
  exact mapsTo_sub_one (mapsTo_ker_sub_one_of_commute hst.symm) x hx

private theorem mul_sub_one_mapsTo_ker_add_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) :
    ∀ x ∈ LinearMap.ker (s + 1), (s * t - 1) x ∈ LinearMap.ker (s + 1) := by
  intro x hx
  rw [mul_sub_one_apply_of_mem_ker_add_one hst hx]
  exact Submodule.neg_mem _
    (mapsTo_add_one (mapsTo_ker_add_one_of_commute hst.symm) x hx)

private theorem ker_mul_sub_one_inf_ker_sub_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) :
    LinearMap.ker (s * t - 1) ⊓ LinearMap.ker (s - 1) =
      LinearMap.ker (t - 1) ⊓ LinearMap.ker (s - 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx1' : (s * t - 1) x = 0 := hx1
    rw [mul_sub_one_apply_of_mem_ker_sub_one hst hx2] at hx1'
    exact Submodule.mem_inf.2 ⟨hx1', hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨?_, hx2⟩
    show (s * t - 1) x = 0
    rw [mul_sub_one_apply_of_mem_ker_sub_one hst hx2]
    exact hx1

private theorem ker_mul_sub_one_inf_ker_add_one {s t : Module.End 𝕜 V}
    (hst : s * t = t * s) :
    LinearMap.ker (s * t - 1) ⊓ LinearMap.ker (s + 1) =
      LinearMap.ker (t + 1) ⊓ LinearMap.ker (s + 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hx1' : (s * t - 1) x = 0 := hx1
    rw [mul_sub_one_apply_of_mem_ker_add_one hst hx2] at hx1'
    have hsum : (t + 1) x = 0 := neg_eq_zero.mp hx1'
    exact Submodule.mem_inf.2 ⟨hsum, hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨?_, hx2⟩
    show (s * t - 1) x = 0
    rw [mul_sub_one_apply_of_mem_ker_add_one hst hx2, hx1, neg_zero]

private theorem ker_eq_sup_inf_of_isCompl {A A' : Submodule 𝕜 V} (h : IsCompl A A')
    {q : Module.End 𝕜 V} (hqA : ∀ x ∈ A, q x ∈ A) (hqA' : ∀ x ∈ A', q x ∈ A') :
    LinearMap.ker q = (LinearMap.ker q ⊓ A) ⊔ (LinearMap.ker q ⊓ A') := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro x hx
  have hxmem : x ∈ A ⊔ A' := by rw [h.sup_eq_top]; trivial
  obtain ⟨u, huA, v, hvA', huv⟩ := Submodule.mem_sup.1 hxmem
  have hqx : q x = 0 := hx
  have hsum : q u + q v = 0 := by rw [← map_add, huv, hqx]
  have hquA : q u ∈ A := hqA u huA
  have hquA' : q u ∈ A' := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact A'.neg_mem (hqA' v hvA')
  have hqu0 : q u = 0 := by
    have hmem : q u ∈ A ⊓ A' := Submodule.mem_inf.2 ⟨hquA, hquA'⟩
    rw [h.inf_eq_bot] at hmem
    simpa using hmem
  have hqv0 : q v = 0 := by
    rw [hqu0, zero_add] at hsum
    exact hsum
  rw [← huv]
  exact Submodule.add_mem_sup ⟨hqu0, huA⟩ ⟨hqv0, hvA'⟩

private theorem disjoint_inf_of_isCompl {A A' : Submodule 𝕜 V} (h : IsCompl A A')
    (q : Module.End 𝕜 V) :
    Disjoint (LinearMap.ker q ⊓ A) (LinearMap.ker q ⊓ A') := by
  rw [disjoint_iff, eq_bot_iff]
  calc (LinearMap.ker q ⊓ A) ⊓ (LinearMap.ker q ⊓ A') ≤ A ⊓ A' := by
        refine le_inf ?_ ?_
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right
    _ = ⊥ := h.inf_eq_bot

private theorem finrank_ker_eq_add_of_isCompl [FiniteDimensional 𝕜 V]
    {A A' : Submodule 𝕜 V} (h : IsCompl A A')
    {q : Module.End 𝕜 V} (hqA : ∀ x ∈ A, q x ∈ A) (hqA' : ∀ x ∈ A', q x ∈ A') :
    Module.finrank 𝕜 (LinearMap.ker q) =
      Module.finrank 𝕜 ↥(LinearMap.ker q ⊓ A) +
        Module.finrank 𝕜 ↥(LinearMap.ker q ⊓ A') := by
  have hsup := ker_eq_sup_inf_of_isCompl h hqA hqA'
  have hdisj := disjoint_inf_of_isCompl h q
  have hkey := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker q ⊓ A)
    (LinearMap.ker q ⊓ A')
  rw [hdisj.eq_bot, ← hsup, finrank_bot, add_zero] at hkey
  exact hkey

theorem finrank_add_two_mul_finrank_inf {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    {s t : V →ₗ[𝕜] V} (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s) :
    Module.finrank 𝕜 V +
        2 * Module.finrank 𝕜 ↥(LinearMap.ker (s - 1) ⊓ LinearMap.ker (t - 1)) =
      Module.finrank 𝕜 (LinearMap.ker (s - 1)) + Module.finrank 𝕜 (LinearMap.ker (t - 1)) +
        Module.finrank 𝕜 (LinearMap.ker (s * t - 1)) := by
  classical
  set A : Submodule 𝕜 V := LinearMap.ker (s - 1) with hA
  set A' : Submodule 𝕜 V := LinearMap.ker (s + 1) with hA'
  set B : Submodule 𝕜 V := LinearMap.ker (t - 1) with hB
  set B' : Submodule 𝕜 V := LinearMap.ker (t + 1) with hB'
  have hAA' : IsCompl A A' := by
    rw [hA, hA']
    exact isCompl_ker_sub_one_ker_add_one h2 hs
  have hBB' : IsCompl B B' := by
    rw [hB, hB']
    exact isCompl_ker_sub_one_ker_add_one h2 ht
  have htA : ∀ x ∈ A, t x ∈ A := by
    rw [hA]
    exact mapsTo_ker_sub_one_of_commute hst.symm
  have htA' : ∀ x ∈ A', t x ∈ A' := by
    rw [hA']
    exact mapsTo_ker_add_one_of_commute hst.symm
  have hsB : ∀ x ∈ B, s x ∈ B := by
    rw [hB]
    exact mapsTo_ker_sub_one_of_commute hst
  have hsB' : ∀ x ∈ B', s x ∈ B' := by
    rw [hB']
    exact mapsTo_ker_add_one_of_commute hst
  have ht_subA : ∀ x ∈ A, (t - 1) x ∈ A := mapsTo_sub_one htA
  have ht_subA' : ∀ x ∈ A', (t - 1) x ∈ A' := mapsTo_sub_one htA'
  have hs_addB : ∀ x ∈ B, (s + 1) x ∈ B := mapsTo_add_one hsB
  have hs_addB' : ∀ x ∈ B', (s + 1) x ∈ B' := mapsTo_add_one hsB'
  have hst_presA : ∀ x ∈ A, (s * t - 1) x ∈ A := by
    rw [hA]
    exact mul_sub_one_mapsTo_ker_sub_one hst
  have hst_presA' : ∀ x ∈ A', (s * t - 1) x ∈ A' := by
    rw [hA']
    exact mul_sub_one_mapsTo_ker_add_one hst
  have hkerA : LinearMap.ker (s * t - 1) ⊓ A = B ⊓ A := by
    rw [hA, hB]
    exact ker_mul_sub_one_inf_ker_sub_one hst
  have hkerA' : LinearMap.ker (s * t - 1) ⊓ A' = B' ⊓ A' := by
    rw [hA', hB']
    exact ker_mul_sub_one_inf_ker_add_one hst
  have hVdim : Module.finrank 𝕜 V = Module.finrank 𝕜 A + Module.finrank 𝕜 A' :=
    (Submodule.finrank_add_eq_of_isCompl hAA').symm
  have hBdim : Module.finrank 𝕜 B =
      Module.finrank 𝕜 ↥(B ⊓ A) + Module.finrank 𝕜 ↥(B ⊓ A') := by
    have h := finrank_ker_eq_add_of_isCompl hAA' ht_subA ht_subA'
    rw [hB]
    exact h
  have hA'dim : Module.finrank 𝕜 A' =
      Module.finrank 𝕜 ↥(B ⊓ A') + Module.finrank 𝕜 ↥(B' ⊓ A') := by
    have h := finrank_ker_eq_add_of_isCompl hBB' hs_addB hs_addB'
    rw [hA', inf_comm B, inf_comm B']
    exact h
  have hCdim : Module.finrank 𝕜 (LinearMap.ker (s * t - 1)) =
      Module.finrank 𝕜 ↥(B ⊓ A) + Module.finrank 𝕜 ↥(B' ⊓ A') := by
    have h := finrank_ker_eq_add_of_isCompl hAA' hst_presA hst_presA'
    rw [hkerA, hkerA'] at h
    exact h
  rw [hVdim, hBdim, hA'dim, hCdim, inf_comm A B]
  omega

theorem finrank_le_nine_of_commute {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) {s t : Γ} (hs : s ^ 2 = 1) (ht : t ^ 2 = 1)
    (hst : s * t = t * s)
    (hr3 : ∀ x ∈ ({s, t, s * t} : Set Γ), Module.finrank 𝕜 (LinearMap.ker (ρ x - 1)) ≤ 3) :
    Module.finrank 𝕜 V ≤ 9 := by
  have hs' : ρ s * ρ s = 1 := by
    simpa [pow_two, map_mul] using congrArg ρ hs
  have ht' : ρ t * ρ t = 1 := by
    simpa [pow_two, map_mul] using congrArg ρ ht
  have hst' : ρ s * ρ t = ρ t * ρ s := by
    simpa [map_mul] using congrArg ρ hst
  have hmain := finrank_add_two_mul_finrank_inf h2 hs' ht' hst'
  have h1 : Module.finrank 𝕜 (LinearMap.ker (ρ s - 1)) ≤ 3 := hr3 s (by simp)
  have h2' : Module.finrank 𝕜 (LinearMap.ker (ρ t - 1)) ≤ 3 := hr3 t (by simp)
  have h3 : Module.finrank 𝕜 (LinearMap.ker (ρ s * ρ t - 1)) ≤ 3 := by
    have h := hr3 (s * t) (by simp)
    rwa [show ρ (s * t) = ρ s * ρ t from map_mul ρ s t] at h
  omega

private theorem exists_pow_involution {Γ : Type*} [Group Γ] [Finite Γ] (S : Sylow 2 Γ)
    {w : Γ} (hwS : w ∈ S) (hw1 : w ≠ 1) (hw2 : w * w ≠ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ (w ^ 2 ^ (n - 1)) ^ 2 = 1 ∧ w ^ 2 ^ (n - 1) ≠ 1 := by
  classical
  let W : ↥S := ⟨w, hwS⟩
  have h_exists : ∃ k : ℕ, W ^ 2 ^ k = 1 := S.isPGroup'.exists_pow_pow_eq_one W
  set n : ℕ := Nat.find h_exists with hn_def
  have hn : W ^ 2 ^ n = 1 := by
    rw [hn_def]
    exact Nat.find_spec h_exists
  have hn_min : ∀ m < n, W ^ 2 ^ m ≠ 1 := by
    intro m hm
    exact Nat.find_min h_exists (hn_def ▸ hm)
  have hW1 : W ≠ 1 := by
    intro hW
    exact hw1 (by
      have := congrArg (fun z : ↥S => (z : Γ)) hW
      simpa [W] using this)
  have hn0 : n ≠ 0 := by
    intro h
    exact hW1 (by simpa [h] using hn)
  have hW2 : W ^ 2 ≠ 1 := by
    intro hW2
    exact hw2 (by
      have := congrArg (fun z : ↥S => (z : Γ)) hW2
      simpa [W, pow_two] using this)
  have hn1 : n ≠ 1 := by
    intro h
    exact hW2 (by simpa [h] using hn)
  have hn2 : 2 ≤ n := by omega
  refine ⟨n, hn2, ?_, ?_⟩
  · calc (w ^ 2 ^ (n - 1)) ^ 2 = w ^ (2 ^ (n - 1) * 2) := by rw [pow_mul]
      _ = w ^ 2 ^ n := by
          congr 1
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
      _ = 1 := by
          have := congrArg (fun t : ↥S => (t : Γ)) hn
          simpa [W] using this
  · intro hz1
    apply hn_min (n - 1) (by omega)
    apply Subtype.ext
    simpa [W] using hz1

private theorem commute_of_conj_eq_inv {Γ : Type*} [Group Γ] {x w z : Γ}
    (hxw : x * w * x⁻¹ = w⁻¹)
    (hz : ∃ k : ℕ, z = w ^ k) (hz2 : z * z = 1) : x * z = z * x := by
  obtain ⟨k, rfl⟩ := hz
  have hconj : x * w ^ k * x⁻¹ = (w ^ k)⁻¹ := by
    rw [← conj_pow (a := x) (b := w) (i := k), hxw, inv_pow]
  have hzinv : (w ^ k)⁻¹ = w ^ k := inv_eq_of_mul_eq_one_right hz2
  rw [hzinv] at hconj
  calc x * w ^ k = x * w ^ k * x⁻¹ * x := by
        rw [mul_assoc (x * w ^ k) x⁻¹ x, inv_mul_cancel, mul_one]
    _ = w ^ k * x := by rw [hconj]

private theorem ne_of_pow_eq_of_not_commute {Γ : Type*} [Group Γ] {x y w z : Γ}
    (hx2 : x * x = 1)
    (hw : w = x * y) (hnc : x * y ≠ y * x) (hz : ∃ k : ℕ, z = w ^ k) : z ≠ x := by
  intro hzx
  obtain ⟨k, hk⟩ := hz
  have hxw : x * w = w * x := by
    rw [← hzx]
    rw [hk]
    exact (Commute.refl w).pow_left k |>.eq
  have h1 : y = w * x := by
    rw [← hxw, hw, ← mul_assoc, hx2, one_mul]
  have h2 : x * y = y * x := by
    have hyx : y * x = w := by
      rw [h1, mul_assoc, hx2, mul_one]
    rw [hyx, ← hw]
  exact hnc h2

theorem eq_of_isInvolution_of_noKlein {Γ : Type*} [Group Γ] [Finite Γ]
    (hno : ∀ s t : Γ, s ^ 2 = 1 → t ^ 2 = 1 → s ≠ 1 → t ≠ 1 → s * t = t * s → s = t)
    (S : Sylow 2 Γ) {x y : Γ} (hx : x ∈ (S : Subgroup Γ)) (hy : y ∈ (S : Subgroup Γ))
    (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  by_contra hxy
  have hnc : x * y ≠ y * x := by
    intro hc
    exact hxy (hno x y hx2 hy2 hx1 hy1 hc)
  have hx2' : x * x = 1 := by simpa [pow_two] using hx2
  have hy2' : y * y = 1 := by simpa [pow_two] using hy2
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2'
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2'
  set w : Γ := x * y with hw
  have hwS : w ∈ (S : Subgroup Γ) := by rw [hw]; exact (S : Subgroup Γ).mul_mem hx hy
  have hw1 : w ≠ 1 := by
    intro hw1
    apply hxy
    calc x = x * 1 := (mul_one x).symm
      _ = x * w := by rw [hw1]
      _ = (x * x) * y := by rw [hw, mul_assoc]
      _ = y := by rw [hx2', one_mul]
  have hw_inv : x * w * x⁻¹ = w⁻¹ := by
    rw [hw]
    have hxy' : x * (x * y) * x⁻¹ = y * x := by
      calc x * (x * y) * x⁻¹ = (x * x) * y * x⁻¹ := by rw [← mul_assoc x x y]
        _ = y * x⁻¹ := by rw [hx2', one_mul]
        _ = y * x := by rw [hxinv]
    rw [hxy', mul_inv_rev, hxinv, hyinv]
  have hw2 : w * w ≠ 1 := by
    intro hww
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hcomm : x * w = w * x := by
      have h' := hw_inv
      rw [hwinv] at h'
      calc x * w = x * w * x⁻¹ * x := by
            rw [mul_assoc (x * w) x⁻¹ x, inv_mul_cancel, mul_one]
        _ = w * x := by rw [h']
    have hx_eq : x = w := hno x w hx2 (by simpa [pow_two] using hww) hx1 hw1 hcomm
    have hx_eq' : x * 1 = x * y := by
      rw [mul_one]
      exact hx_eq.trans hw
    exact hy1 (mul_left_cancel hx_eq').symm
  obtain ⟨n, hn2, hz2, hz1⟩ := exists_pow_involution S hwS hw1 hw2
  set z : Γ := w ^ 2 ^ (n - 1) with hz
  have hzp : ∃ k : ℕ, z = w ^ k := ⟨2 ^ (n - 1), hz⟩
  have hz2' : z * z = 1 := by simpa [pow_two] using hz2
  have hxz_comm : x * z = z * x := commute_of_conj_eq_inv hw_inv hzp hz2'
  have hzx : z ≠ x := ne_of_pow_eq_of_not_commute hx2' hw hnc hzp
  exact hzx (hno x z hx2 hz2 hx1 hz1 hxz_comm).symm

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end

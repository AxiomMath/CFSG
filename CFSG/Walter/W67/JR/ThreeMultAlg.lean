module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Walter.W67

namespace ThreeMult

open scoped BigOperators

theorem sum_pow_eq_zero_of_le_one {d : ℕ} (hd : d ≤ 1) : ∑ x : ZMod 3, x ^ d = 0 := by
  interval_cases d <;> decide

theorem sum_diag_eq_zero {E M : Type*} [AddCommGroup E] [Module (ZMod 3) E] [Fintype E]
    [AddCommGroup M] [Module (ZMod 3) M] {k : ℕ}
    (Ψ : MultilinearMap (ZMod 3) (fun _ : Fin k => E) M)
    (hk : k < 2 * Module.finrank (ZMod 3) E) : ∑ s : E, Ψ (fun _ => s) = 0 := by
  classical
  set n := Module.finrank (ZMod 3) E
  let b : Module.Basis (Fin n) (ZMod 3) E := Module.finBasis (ZMod 3) E
  have hexp : ∀ s : E, Ψ (fun _ => s) = ∑ r : Fin k → Fin n,
      (∏ j, b.repr s (r j)) • Ψ (fun j => b (r j)) := by
    intro s
    have hs : (fun _ : Fin k => s) = fun _ => ∑ i, b.repr s i • b i := by
      ext j
      exact (b.sum_repr s).symm
    rw [hs, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact Ψ.map_smul_univ (fun j => b.repr s (r j)) (fun j => b (r j))
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← Finset.sum_smul]
  convert zero_smul (ZMod 3) (Ψ (fun j => b (r j)))
  set d : Fin n → ℕ := fun i => (Finset.univ.filter fun j => r j = i).card with hd
  have hfib : ∀ c : Fin n → ZMod 3, ∏ j, c (r j) = ∏ i, c i ^ d i := by
    intro c
    rw [← Finset.prod_fiberwise Finset.univ r (fun j => c (r j))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
      Finset.prod_const]
  have hcoord : ∑ s : E, ∏ j, b.repr s (r j) = ∑ c : Fin n → ZMod 3, ∏ j, c (r j) :=
    Fintype.sum_equiv b.equivFun _ _ (fun s => by simp [Module.Basis.equivFun_apply])
  rw [hcoord]
  simp_rw [hfib]
  rw [← Fintype.prod_sum (fun i (x : ZMod 3) => x ^ d i)]
  obtain ⟨i, hi⟩ : ∃ i, d i ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hsum : ∑ i, d i = k := by
      rw [hd]
      have := (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := r) (fun j _ => Finset.mem_univ (r j))).symm
      simpa using this
    have hge : ∑ _i : Fin n, 2 ≤ ∑ i, d i := Finset.sum_le_sum fun i _ => hcon i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hge
    omega
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sum_pow_eq_zero_of_le_one hi)

theorem eq_zero_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] {n : ℕ}
    (hn : 1 ≤ n) {m : M} (h : (3 ^ n - 1) • m = 0) : m = 0 := by
  have h3 : ((3 ^ n - 1 : ℕ) : ZMod 3) = 2 := by
    have h1 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Nat.cast_sub h1, Nat.cast_pow, show ((3 : ℕ) : ZMod 3) = 0 from rfl,
      zero_pow (by omega)]
    rfl
  rw [← Nat.cast_smul_eq_nsmul (ZMod 3), h3] at h
  calc m = ((2 : ZMod 3) * 2) • m := by
        rw [show ((2 : ZMod 3) * 2) = 1 from rfl, one_smul]
    _ = 0 := by rw [mul_smul, h, smul_zero]

theorem eq_zero_of_free_invariant {V M : Type*} [AddCommGroup V] [Module (ZMod 3) V] [Fintype V]
    [AddCommGroup M] [Module (ZMod 3) M] {n : ℕ} (hV : Fintype.card V = 3 ^ n)
    (T : V →ₗ[ZMod 3] V) (hT : T ^ (3 ^ n - 1) = 1)
    (hfree : ∀ j, 0 < j → j < 3 ^ n - 1 → ∀ v, (T ^ j) v = v → v = 0)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k < 2 * n) (Φ : MultilinearMap (ZMod 3) (fun _ : Fin k => V) M)
    (hΦ : ∀ x : Fin k → V, Φ (fun i => T (x i)) = Φ x) (x : Fin k → V) : Φ x = 0 := by
  classical
  have hn : 1 ≤ n := by omega
  have hq3 : 3 ≤ 3 ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set q := 3 ^ n with hqdef
  have hTinj : Function.Injective T := by
    intro v w hvw
    have h1 : (T ^ (q - 1)) v = (T ^ (q - 1)) w := by
      rw [show q - 1 = (q - 2) + 1 by omega, pow_succ, Module.End.mul_apply,
        Module.End.mul_apply, hvw]
    rwa [hT, Module.End.one_apply, Module.End.one_apply] at h1
  have hTjinj : ∀ j : ℕ, Function.Injective (T ^ j) := by
    intro j
    rw [Module.End.coe_pow]
    exact hTinj.iterate j
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by
      rw [hcon a, hcon b]
    omega
  have horbit : ∀ v : V, v ≠ 0 → ∃ j < q - 1, (T ^ j) v₀ = v := by
    let o : Fin (q - 1) → {v : V // v ≠ 0} := fun j => ⟨(T ^ (j : ℕ)) v₀, fun h0 => hv₀ (by
      have := hTjinj j (h0.trans (map_zero (T ^ (j : ℕ))).symm)
      exact this)⟩
    have hoinj : Function.Injective o := by
      intro i j hij
      have hij' : (T ^ (i : ℕ)) v₀ = (T ^ (j : ℕ)) v₀ := congrArg Subtype.val hij
      by_contra hne
      rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · have : (T ^ (i : ℕ)) ((T ^ ((j : ℕ) - i)) v₀) = (T ^ (i : ℕ)) v₀ := by
          rw [← Module.End.mul_apply, ← pow_add, show (i : ℕ) + ((j : ℕ) - i) = j by omega,
            hij']
        exact hv₀ (hfree _ (by omega) (by omega) v₀ (hTjinj i this))
      · have : (T ^ (j : ℕ)) ((T ^ ((i : ℕ) - j)) v₀) = (T ^ (j : ℕ)) v₀ := by
          rw [← Module.End.mul_apply, ← pow_add, show (j : ℕ) + ((i : ℕ) - j) = i by omega,
            hij'.symm]
        exact hv₀ (hfree _ (by omega) (by omega) v₀ (hTjinj j this))
    have hcard : Fintype.card (Fin (q - 1)) = Fintype.card {v : V // v ≠ 0} := by
      rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq, hV]
    have hosurj := (Fintype.bijective_iff_injective_and_card o).mpr ⟨hoinj, hcard⟩
    intro v hv
    obtain ⟨j, hj⟩ := hosurj.2 ⟨v, hv⟩
    exact ⟨j, j.2, congrArg Subtype.val hj⟩
  set A := Submodule.span (ZMod 3) (Set.range fun j : ℕ => T ^ j) with hAdef
  have hTA : ∀ j : ℕ, T ^ j ∈ A := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hAcomm : ∀ s ∈ A, ∀ j : ℕ, s * T ^ j = T ^ j * s := by
    intro s hs j
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨i, rfl⟩ := hs
      rw [← pow_add, ← pow_add, add_comm]
    | zero => rw [zero_mul, mul_zero]
    | add s t _ _ hs ht => rw [add_mul, mul_add, hs, ht]
    | smul c s _ hs => rw [smul_mul_assoc, mul_smul_comm, hs]
  have hAkill : ∀ s ∈ A, s v₀ = 0 → s = 0 := by
    intro s hs hsv
    ext v
    by_cases hv : v = 0
    · rw [hv, map_zero, LinearMap.zero_apply]
    · obtain ⟨j, -, rfl⟩ := horbit v hv
      rw [LinearMap.zero_apply, ← Module.End.mul_apply, hAcomm s hs j, Module.End.mul_apply,
        hsv, map_zero]
  have hApow : ∀ s ∈ A, s ≠ 0 → ∃ j : ℕ, s = T ^ j := by
    intro s hs hs0
    have hsv : s v₀ ≠ 0 := fun h => hs0 (hAkill s hs h)
    obtain ⟨j, -, hj⟩ := horbit _ hsv
    refine ⟨j, ?_⟩
    have := hAkill (s - T ^ j) (A.sub_mem hs (hTA j)) (by
      rw [LinearMap.sub_apply, hj, sub_self])
    exact sub_eq_zero.mp this
  let ev : A →ₗ[ZMod 3] V := (LinearMap.applyₗ v₀).comp A.subtype
  have hev : Function.Bijective ev := by
    refine ⟨fun s t hst => ?_, fun v => ?_⟩
    · have := hAkill ((s : Module.End (ZMod 3) V) - t) (A.sub_mem s.2 t.2) (by
        change (s : Module.End (ZMod 3) V) v₀ - (t : Module.End (ZMod 3) V) v₀ = 0
        have h1 : (s : Module.End (ZMod 3) V) v₀ = (t : Module.End (ZMod 3) V) v₀ := hst
        rw [h1, sub_self])
      exact Subtype.ext (sub_eq_zero.mp this)
    · by_cases hv : v = 0
      · exact ⟨0, by rw [hv, map_zero]⟩
      · obtain ⟨j, -, hj⟩ := horbit v hv
        exact ⟨⟨T ^ j, hTA j⟩, hj⟩
  have : Finite (Module.End (ZMod 3) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 3) V => (f : V → V)) DFunLike.coe_injective
  let _ : Fintype A := Fintype.ofFinite A
  have hAcard : Fintype.card A = 3 ^ n := by
    rw [Fintype.card_of_bijective hev, hV]
  have hAfin : Module.finrank (ZMod 3) A = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 3) (V := A)
    rw [hAcard, ZMod.card] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  let Ψ : MultilinearMap (ZMod 3) (fun _ : Fin k => A) M :=
    Φ.compLinearMap (fun i => (LinearMap.applyₗ (x i)).comp A.subtype)
  have hΨ : ∀ s : A, Ψ (fun _ => s) = Φ (fun i => (s : Module.End (ZMod 3) V) (x i)) :=
    fun s => rfl
  have hsum := sum_diag_eq_zero Ψ (by rw [hAfin]; exact hk)
  have hpowinv : ∀ j : ℕ, Φ (fun i => (T ^ j) (x i)) = Φ x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← ih]
      have := hΦ (fun i => (T ^ j) (x i))
      rw [← this]
      congr 1
      ext i
      rw [pow_succ', Module.End.mul_apply]
  have hval : ∀ s ∈ (Finset.univ : Finset A).erase 0, Ψ (fun _ => s) = Φ x := by
    intro s hs
    have hs0 : s ≠ 0 := Finset.ne_of_mem_erase hs
    obtain ⟨j, hj⟩ := hApow s s.2 (fun h => hs0 (Subtype.ext h))
    rw [hΨ, hj, hpowinv]
  have h0 : Ψ (fun _ => 0) = 0 := by
    have := Ψ.map_coord_zero (m := fun _ => (0 : A)) (⟨0, by omega⟩ : Fin k) rfl
    exact this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : A)), h0, zero_add,
    Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hAcard] at hsum
  exact eq_zero_of_nsmul_eq_zero hn hsum

end ThreeMult

end CFSG.Walter.W67

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCoordDefs
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

private lemma ggCZ_two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

private lemma ggCZ_coord_sum {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (v : V) (k : Fin m) :
    φ k (∑ j, φ j v • e j) = φ k v := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hsum : (∑ j, φ j v * (if k = j then 1 else 0)) = φ k v := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk
      rw [if_neg (Ne.symm hjk), mul_zero]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  simpa only [hd k] using hsum

private lemma ggCZ_coord_c {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (v : V) :
    ∀ k, φ k (v - ∑ j, φ j v • e j) = 0 := by
  intro k
  rw [map_sub, ggCZ_coord_sum hd v k]
  exact sub_self _

private lemma ggCZ_eq_of_on_e_fix {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {f g : V →ₗ[ZMod p] V}
    (hE : ∀ k, f (e k) = g (e k))
    (hC : ∀ v, (∀ k, φ k v = 0) → f v = g v) : f = g := by
  refine LinearMap.ext fun v => ?_
  set c := v - ∑ k, φ k v • e k with hcdef
  have hc : ∀ k, φ k c = 0 := ggCZ_coord_c hd v
  have hv : v = (∑ k, φ k v • e k) + c := by rw [hcdef]; abel
  calc
    f v = f ((∑ k, φ k v • e k) + c) := congrArg f hv
    _ = ∑ k, φ k v • f (e k) + f c := by simp only [map_add, map_sum, map_smul]
    _ = ∑ k, φ k v • g (e k) + g c := by
      rw [hC c hc, Finset.sum_congr rfl fun k _ => by rw [hE k]]
    _ = g ((∑ k, φ k v • e k) + c) := by simp only [map_add, map_sum, map_smul]
    _ = g v := congrArg g hv.symm

private lemma ggCZ_linearEquiv_eq_of_on_e_fix {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ)
    {f g : V ≃ₗ[ZMod p] V} (hE : ∀ k, f (e k) = g (e k))
    (hC : ∀ v, (∀ k, φ k v = 0) → f v = g v) : f = g :=
  LinearEquiv.ext fun v => LinearMap.congr_fun (ggCZ_eq_of_on_e_fix hd hE hC) v

private noncomputable def ggCZdualE {φ : Fin m → Module.Dual (ZMod p) V}
    (i j : Fin m) (ε : ZMod p) : Module.Dual (ZMod p) V where
  toFun v := φ i v - ε * φ j v
  map_add' v w := by
    rw [map_add, map_add]
    ring
  map_smul' c v := by
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
    ring

private lemma ggCZdualE_apply {φ : Fin m → Module.Dual (ZMod p) V}
    (i j : Fin m) (ε : ZMod p) (v : V) :
    ggCZdualE (φ := φ) i j ε v = φ i v - ε * φ j v := rfl

private noncomputable def ggCZdualS {φ : Fin m → Module.Dual (ZMod p) V}
    (i : Fin m) : Module.Dual (ZMod p) V where
  toFun v := 2 * φ i v
  map_add' v w := by
    rw [map_add]
    ring
  map_smul' c v := by
    rw [map_smul, smul_eq_mul, RingHom.id_apply]
    ring

private lemma ggCZdualS_apply {φ : Fin m → Module.Dual (ZMod p) V}
    (i : Fin m) (v : V) : ggCZdualS (φ := φ) i v = 2 * φ i v := rfl

private lemma ggCZdualE_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} {ε : ZMod p} (hε : ε = 1 ∨ ε = -1)
    (hij : i ≠ j) : ggCZdualE (φ := φ) i j ε (e i - ε • e j) = 2 := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h : φ i (e i - ε • e j) - ε * φ j (e i - ε • e j) = 1 + ε * ε := by
    simp only [map_sub, map_smul, hd i i, hd i j, hd j i, hd j j, if_true, if_false, hij,
      Ne.symm hij, smul_eq_mul]
    ring
  rw [ggCZdualE_apply, h, hε2]
  norm_num

private lemma ggCZdualS_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin m) : ggCZdualS (φ := φ) i (e i) = 2 := by
  rw [ggCZdualS_apply, hd i i]
  norm_num

private noncomputable def ggCZreflDE {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (i j : Fin m) (ε : ZMod p)
    (h : ggCZdualE (φ := φ) i j ε (e i - ε • e j) = 2) : V ≃ₗ[ZMod p] V :=
  Module.reflection (x := e i - ε • e j) (f := ggCZdualE (φ := φ) i j ε) h

private lemma ggCZreflDE_apply {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i j : Fin m} {ε : ZMod p}
    (h : ggCZdualE (φ := φ) i j ε (e i - ε • e j) = 2) (v : V) :
    ggCZreflDE (φ := φ) i j ε h v =
      v - (φ i v - ε * φ j v) • (e i - ε • e j) := by
  rw [ggCZreflDE, Module.reflection_apply, ggCZdualE_apply]

private lemma ggCZreflDE_involutive {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i j : Fin m} {ε : ZMod p}
    (h : ggCZdualE (φ := φ) i j ε (e i - ε • e j) = 2) (v : V) :
    ggCZreflDE (φ := φ) i j ε h (ggCZreflDE (φ := φ) i j ε h v) = v := by
  rw [ggCZreflDE]
  exact Module.involutive_reflection _ v

private noncomputable def ggCZreflS {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (i : Fin m) (h : ggCZdualS (φ := φ) i (e i) = 2) : V ≃ₗ[ZMod p] V :=
  Module.reflection (x := e i) (f := ggCZdualS (φ := φ) i) h

private lemma ggCZreflS_apply {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i : Fin m} (h : ggCZdualS (φ := φ) i (e i) = 2) (v : V) :
    ggCZreflS (φ := φ) i h v = v - (2 * φ i v) • e i := by
  rw [ggCZreflS, Module.reflection_apply, ggCZdualS_apply]

private lemma ggCZreflS_involutive {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i : Fin m} (h : ggCZdualS (φ := φ) i (e i) = 2) (v : V) :
    ggCZreflS (φ := φ) i h (ggCZreflS (φ := φ) i h v) = v := by
  rw [ggCZreflS]
  exact Module.involutive_reflection _ v

private lemma ggCZconj_apply_of_formula {σ τ : V ≃ₗ[ZMod p] V} {y : V}
    {g : Module.Dual (ZMod p) V}
    (hτ : ∀ z, τ z = z - g z • y) (hσ2 : ∀ z, σ (σ z) = z) (v : V) :
    (σ * τ * σ⁻¹) v = v - g (σ v) • σ y := by
  have hσinv : σ⁻¹ = σ := by
    apply inv_eq_of_mul_eq_one_right
    ext z
    exact hσ2 z
  calc
    (σ * τ * σ⁻¹) v = σ (τ (σ v)) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hσinv]
    _ = σ (σ v - g (σ v) • y) := by rw [hτ]
    _ = σ (σ v) - g (σ v) • σ y := by rw [map_sub, map_smul]
    _ = v - g (σ v) • σ y := by rw [hσ2]

private lemma ggCZreflDE_conj_succ {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j l : Fin m} (hij : i < j) (hjl : j.val + 1 = l.val)
    (hσ : ggCZdualE (φ := φ) j l 1 (e j - (1 : ZMod p) • e l) = 2)
    (hτ : ggCZdualE (φ := φ) i j 1 (e i - (1 : ZMod p) • e j) = 2)
    (hτ' : ggCZdualE (φ := φ) i l 1 (e i - (1 : ZMod p) • e l) = 2) :
    ggCZreflDE (φ := φ) j l 1 hσ * ggCZreflDE (φ := φ) i j 1 hτ *
      (ggCZreflDE (φ := φ) j l 1 hσ)⁻¹ =
      ggCZreflDE (φ := φ) i l 1 hτ' := by
  have hjl' : j ≠ l := by omega
  have hil' : i ≠ l := by omega
  refine LinearEquiv.ext fun v => ?_
  rw [ggCZconj_apply_of_formula (σ := ggCZreflDE (φ := φ) j l 1 hσ)
    (τ := ggCZreflDE (φ := φ) i j 1 hτ)
    (g := ggCZdualE (φ := φ) i j 1)
    (y := e i - (1 : ZMod p) • e j)
    (fun z => ggCZreflDE_apply hτ z)
    (ggCZreflDE_involutive hσ) v]
  rw [ggCZreflDE_apply hτ']
  have h1 : (ggCZdualE (φ := φ) i j 1) (ggCZreflDE (φ := φ) j l 1 hσ v) =
      φ i v - 1 * φ l v := by
    rw [ggCZreflDE_apply, ggCZdualE_apply]
    simp only [map_sub, map_smul, hd i j, hd i l, hd j j, hd j l, if_true, if_false,
      ne_of_lt hij, hjl', hil', one_mul,
         ]
    ring
  have h2 : ggCZreflDE (φ := φ) j l 1 hσ (e i - (1 : ZMod p) • e j) = e i - (1 : ZMod p) • e l := by
    rw [ggCZreflDE_apply]
    have hc : φ j (e i - (1 : ZMod p) • e j) - 1 * φ l (e i - (1 : ZMod p) • e j) = -1 := by
      simp only [map_sub, map_smul, hd j i, hd j j, hd l i, hd l j, if_true,
        if_false, Ne.symm (ne_of_lt hij), Ne.symm hjl', Ne.symm hil',
        one_mul]
      ring
    rw [hc]
    simp only [one_smul, neg_one_smul]
    abel
  rw [h1, h2]

private lemma ggCZreflS_conj_succ {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i l : Fin m} (hil : i.val + 1 = l.val) :
    ggCZreflDE (φ := φ) i l 1
        (ggCZdualE_root hd (Or.inl rfl) (by omega)) *
      ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
      (ggCZreflDE (φ := φ) i l 1
        (ggCZdualE_root hd (Or.inl rfl) (by omega)))⁻¹ =
      ggCZreflS (φ := φ) i (ggCZdualS_root hd i) := by
  have hil' : i ≠ l := by omega
  have hσ : ggCZdualE (φ := φ) i l 1 (e i - (1 : ZMod p) • e l) = 2 :=
    ggCZdualE_root hd (Or.inl rfl) hil'
  have hτ : ggCZdualS (φ := φ) l (e l) = 2 := ggCZdualS_root hd l
  have hτ' : ggCZdualS (φ := φ) i (e i) = 2 := ggCZdualS_root hd i
  refine LinearEquiv.ext fun v => ?_
  rw [ggCZconj_apply_of_formula (σ := ggCZreflDE (φ := φ) i l 1 hσ)
    (τ := ggCZreflS (φ := φ) l hτ)
    (g := ggCZdualS (φ := φ) l)
    (y := e l)
    (fun z => ggCZreflS_apply hτ z)
    (ggCZreflDE_involutive hσ) v]
  rw [ggCZreflS_apply hτ']
  have h1 : (ggCZdualS (φ := φ) l) (ggCZreflDE (φ := φ) i l 1 hσ v) =
      2 * φ i v := by
    rw [ggCZreflDE_apply, ggCZdualS_apply]
    simp only [map_sub, map_smul, hd l i, hd l l, if_true, if_false,
      Ne.symm hil', one_mul]
    ring
  have h2 : ggCZreflDE (φ := φ) i l 1 hσ (e l) = e i := by
    rw [ggCZreflDE_apply]
    have hc : φ i (e l) - 1 * φ l (e l) = -1 := by
      simp only [hd i l, hd l l, if_true, if_false, hil', mul_one
        ]
      ring
    rw [hc]
    simp only [one_smul, neg_one_smul]
    abel
  rw [h1, h2]

private lemma ggCZreflS_conj_plus {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) :
    ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
      ggCZreflDE (φ := φ) i j 1 (ggCZdualE_root hd (Or.inl rfl) hij) *
      (ggCZreflS (φ := φ) j (ggCZdualS_root hd j))⁻¹ =
      ggCZreflDE (φ := φ) i j (-1) (ggCZdualE_root hd (Or.inr rfl) hij) := by
  have hσ : ggCZdualS (φ := φ) j (e j) = 2 := ggCZdualS_root hd j
  have hτ : ggCZdualE (φ := φ) i j 1 (e i - (1 : ZMod p) • e j) = 2 :=
    ggCZdualE_root hd (Or.inl rfl) hij
  have hτ' : ggCZdualE (φ := φ) i j (-1) (e i - (-1 : ZMod p) • e j) = 2 :=
    ggCZdualE_root hd (Or.inr rfl) hij
  refine LinearEquiv.ext fun v => ?_
  rw [ggCZconj_apply_of_formula (σ := ggCZreflS (φ := φ) j hσ)
    (τ := ggCZreflDE (φ := φ) i j 1 hτ)
    (g := ggCZdualE (φ := φ) i j 1)
    (y := e i - (1 : ZMod p) • e j)
    (fun z => ggCZreflDE_apply hτ z)
    (ggCZreflS_involutive hσ) v]
  rw [ggCZreflDE_apply hτ']
  have h1 : (ggCZdualE (φ := φ) i j 1) (ggCZreflS (φ := φ) j hσ v) =
      φ i v - (-1) * φ j v := by
    rw [ggCZreflS_apply, ggCZdualE_apply]
    simp only [map_sub, map_smul, hd i j, hd j j, if_true, if_false, hij,
      one_mul]
    ring
  have h2 : ggCZreflS (φ := φ) j hσ (e i - (1 : ZMod p) • e j) =
      e i - (-1 : ZMod p) • e j := by
    rw [ggCZreflS_apply]
    have hc : 2 * φ j (e i - (1 : ZMod p) • e j) = -2 := by
      simp only [map_sub, map_smul, hd j i, hd j j, if_true, if_false, Ne.symm hij
            ]
      ring
    rw [hc]
    module
  rw [h1, h2]

private lemma ggCZreflDE_mem_adj {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i l : Fin m} (hil : i.val + 1 = l.val)
    (h : ggCZdualE (φ := φ) i l 1 (e i - (1 : ZMod p) • e l) = 2) :
    ggCZreflDE (φ := φ) i l 1 h ∈ ggCZWB p e φ := by
  rw [ggCZWB]
  refine Subgroup.subset_closure (Or.inl ⟨i, l, hil, fun v => ?_⟩)
  rw [ggCZreflDE_apply]
  simp only [one_mul, one_smul]

private lemma ggCZreflS_mem_last {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i : Fin m} (hi : i.val + 1 = m)
    (h : ggCZdualS (φ := φ) i (e i) = 2) :
    ggCZreflS (φ := φ) i h ∈ ggCZWB p e φ := by
  rw [ggCZWB]
  refine Subgroup.subset_closure (Or.inr ⟨i, hi, fun v => ?_⟩)
  rw [ggCZreflS_apply]

private lemma ggCZreflDE_mem {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i < j) :
    ggCZreflDE (φ := φ) i j 1
      (ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hij)) ∈ ggCZWB p e φ := by
  suffices ∀ n : ℕ, ∀ j : Fin m, j.val = n → ∀ h : i < j,
      ggCZreflDE (φ := φ) i j 1
        (ggCZdualE_root hd (Or.inl rfl) (ne_of_lt h)) ∈ ggCZWB p e φ from
    this j.val j rfl hij
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro j hjval hij
      by_cases hadj : i.val + 1 = j.val
      · have hmem := ggCZreflDE_mem_adj (φ := φ) hadj
            (ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hij))
        convert hmem using 2
      · have hjgt : i.val + 1 < j.val := by omega
        let j' : Fin m := ⟨j.val - 1, by omega⟩
        have hj'val : j'.val = j.val - 1 := rfl
        have hlt : i < j' := by
          rw [Fin.lt_def, hj'val]
          omega
        have hmem1 : ggCZreflDE (φ := φ) i j' 1
            (ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hlt)) ∈ ggCZWB p e φ :=
          ih j'.val (by omega) j' rfl hlt
        have hj'l : j'.val + 1 = j.val := by
          rw [hj'val]
          omega
        have hτ : ggCZdualE (φ := φ) i j' 1 (e i - (1 : ZMod p) • e j') = 2 :=
          ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hlt)
        have hj'lj : j' < j := by
          rw [Fin.lt_def, hj'val]
          omega
        have hσ : ggCZdualE (φ := φ) j' j 1 (e j' - (1 : ZMod p) • e j) = 2 :=
          ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hj'lj)
        have hτ' : ggCZdualE (φ := φ) i j 1 (e i - (1 : ZMod p) • e j) = 2 :=
          ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hij)
        have hmemd : ggCZreflDE (φ := φ) j' j 1 hσ ∈ ggCZWB p e φ :=
          ggCZreflDE_mem_adj (φ := φ) hj'l hσ
        have hconj := ggCZreflDE_conj_succ hd (i := i) (j := j') (l := j) hlt hj'l hσ hτ hτ'
        rw [← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmemd hmem1) (Subgroup.inv_mem _ hmemd)

private lemma ggCZreflS_mem_aux {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) :
    ∀ n : ℕ, ∀ i : Fin m, m - 1 - i.val = n →
      ggCZreflS (φ := φ) i (ggCZdualS_root hd i) ∈ ggCZWB p e φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro i hn
      by_cases hi : i.val + 1 = m
      · exact ggCZreflS_mem_last (φ := φ) hi (ggCZdualS_root hd i)
      · have hi' : i.val + 1 < m := by omega
        let l : Fin m := ⟨i.val + 1, hi'⟩
        have hil : i.val + 1 = l.val := rfl
        have hmemS : ggCZreflS (φ := φ) l (ggCZdualS_root hd l) ∈ ggCZWB p e φ :=
          ih (m - 1 - l.val) (by omega) l rfl
        have hσ : ggCZdualE (φ := φ) i l 1 (e i - (1 : ZMod p) • e l) = 2 :=
          ggCZdualE_root hd (Or.inl rfl) (by omega)
        have hmemd : ggCZreflDE (φ := φ) i l 1 hσ ∈ ggCZWB p e φ :=
          ggCZreflDE_mem_adj (φ := φ) hil hσ
        have hconj := ggCZreflS_conj_succ (hd := hd) (i := i) (l := l) hil
        rw [← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmemd hmemS) (Subgroup.inv_mem _ hmemd)

private lemma ggCZreflS_mem {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i : Fin m) :
    ggCZreflS (φ := φ) i (ggCZdualS_root hd i) ∈ ggCZWB p e φ :=
  ggCZreflS_mem_aux hd (m - 1 - i.val) i rfl

private lemma ggCZreflDE_mem_one {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) :
    ggCZreflDE (φ := φ) i j 1 (ggCZdualE_root hd (Or.inl rfl) hij) ∈ ggCZWB p e φ := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ggCZreflDE_mem hd hlt
  · have hmem := ggCZreflDE_mem hd hgt
    have heq : ggCZreflDE (φ := φ) i j 1 (ggCZdualE_root hd (Or.inl rfl) hij) =
        ggCZreflDE (φ := φ) j i 1 (ggCZdualE_root hd (Or.inl rfl) (ne_of_lt hgt)) := by
      ext v
      rw [ggCZreflDE_apply, ggCZreflDE_apply]
      module
    rw [heq]
    exact hmem

theorem ggCZ_subset_ggCZWB {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) : ggCZRD e φ ∪ ggCZS e φ ⊆ ggCZWB p e φ := by
  intro r hr
  rcases hr with hr | hr
  · obtain ⟨i, j, hij, ε, hε, hi⟩ := hr
    rcases hε with rfl | rfl
    · have hD : ggCZreflDE (φ := φ) i j 1
          (ggCZdualE_root hd (Or.inl rfl) hij) ∈ ggCZWB p e φ :=
        ggCZreflDE_mem_one hd hij
      have hrD : r = ggCZreflDE (φ := φ) i j 1
          (ggCZdualE_root hd (Or.inl rfl) hij) := by
        ext v
        rw [ggCZreflDE_apply]
        exact hi v
      rwa [hrD]
    · have hD : ggCZreflDE (φ := φ) i j 1
          (ggCZdualE_root hd (Or.inl rfl) hij) ∈ ggCZWB p e φ :=
        ggCZreflDE_mem_one hd hij
      have hS := ggCZreflS_mem hd j
      have hplus : ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
          ggCZreflDE (φ := φ) i j 1 (ggCZdualE_root hd (Or.inl rfl) hij) *
          (ggCZreflS (φ := φ) j (ggCZdualS_root hd j))⁻¹ ∈ ggCZWB p e φ :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hS hD) (Subgroup.inv_mem _ hS)
      have hconj := ggCZreflS_conj_plus hd (i := i) (j := j) hij
      have hrplus : ggCZreflDE (φ := φ) i j (-1)
          (ggCZdualE_root hd (Or.inr rfl) hij) ∈ ggCZWB p e φ := by
        rw [← hconj]
        exact hplus
      have hrRD : r = ggCZreflDE (φ := φ) i j (-1)
          (ggCZdualE_root hd (Or.inr rfl) hij) := by
        ext v
        rw [ggCZreflDE_apply]
        exact hi v
      rwa [hrRD]
  · obtain ⟨i, hi⟩ := hr
    have hS := ggCZreflS_mem hd i
    have hrS : r = ggCZreflS (φ := φ) i (ggCZdualS_root hd i) := by
      ext v
      rw [ggCZreflS_apply]
      exact hi v
    rwa [hrS]

private def ggCZSP (e : Fin m → V) (g : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∃ s : Fin m → ZMod p,
    (∀ k, s k = 1 ∨ s k = -1) ∧ ∀ k, g (e k) = s k • e (σ k)

private lemma ggCZSP_one (e : Fin m → V) : ggCZSP e (1 : V ≃ₗ[ZMod p] V) := by
  refine ⟨1, fun _ => 1, fun k => Or.inl rfl, fun k => ?_⟩
  simp

private lemma ggCZSP_mul {e : Fin m → V}
    {g h : V ≃ₗ[ZMod p] V} (hg : ggCZSP e g) (hh : ggCZSP e h) :
    ggCZSP e (g * h) := by
  obtain ⟨σ, s, hs, hact⟩ := hg
  obtain ⟨τ, t, ht, hact'⟩ := hh
  refine ⟨σ * τ, fun k => t k * s (τ k), ?_, fun k => ?_⟩
  · intro k
    show t k * s (τ k) = 1 ∨ t k * s (τ k) = -1
    rcases ht k with h | h <;> rcases hs (τ k) with h' | h' <;> rw [h, h'] <;> norm_num
  · rw [LinearEquiv.mul_apply, hact', map_smul, hact, smul_smul]
    rfl

private lemma ggCZSP_inv {e : Fin m → V}
    {g : V ≃ₗ[ZMod p] V} (hg : ggCZSP e g) : ggCZSP e g⁻¹ := by
  obtain ⟨σ, s, hs, hact⟩ := hg
  have hs2 : ∀ k, s k * s k = 1 := by
    intro k
    rcases hs k with h | h <;> rw [h] <;> norm_num
  refine ⟨σ⁻¹, fun k => s (σ⁻¹ k), fun k => hs (σ⁻¹ k), fun k => ?_⟩
  apply g.injective
  change g ((g⁻¹) (e k)) = g (s (σ⁻¹ k) • e (σ⁻¹ k))
  rw [show g⁻¹ = g.symm from rfl, LinearEquiv.apply_symm_apply, map_smul, hact,
    show σ (σ⁻¹ k) = k from by simp, smul_smul, hs2, one_smul]

private lemma ggCZSP_gen {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r : V ≃ₗ[ZMod p] V} (hr : GGCZGensB e φ r) :
    ggCZSP e r := by
  rcases hr with ⟨i, j, hij, hr⟩ | ⟨i, hi, hr⟩
  · have hijne : i ≠ j := by omega
    refine ⟨Equiv.swap i j, fun _ => 1, fun k => Or.inl rfl, fun k => ?_⟩
    rw [hr (e k)]
    simp only [ one_smul]
    by_cases hki : k = i
    · rw [hki]
      rw [hd i i, hd j i, if_pos rfl, if_neg (Ne.symm hijne), sub_zero, one_smul]
      rw [Equiv.swap_apply_left]
      abel
    · by_cases hkj : k = j
      · rw [hkj]
        rw [hd i j, hd j j, if_neg hijne, if_pos rfl, zero_sub, neg_smul, one_smul]
        rw [Equiv.swap_apply_right]
        abel
      · have hswap : Equiv.swap i j k = k := by
          rw [Equiv.swap_apply_def]
          simp [hki, hkj]
        rw [hswap, hd i k, hd j k, if_neg (Ne.symm hki), if_neg (Ne.symm hkj), sub_self,
          zero_smul, sub_zero]
  · refine ⟨1, fun k => if k = i then -1 else 1, ?_, fun k => ?_⟩
    · intro k
      by_cases hki : k = i <;> simp [hki]
    · rw [hr (e k)]
      simp only [  Equiv.Perm.one_apply]
      by_cases hki : k = i
      · rw [hki]
        rw [hd i i, if_pos rfl, mul_one, two_smul, if_pos rfl, neg_one_smul]
        abel
      · rw [hd i k, if_neg (Ne.symm hki), mul_zero, zero_smul, sub_zero]
        simp [hki]

private theorem ggCZWB_SP {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggCZWB p e φ) :
    ggCZSP e g := by
  rw [ggCZWB] at hg
  induction hg using Subgroup.closure_induction with
  | mem r hr => exact ggCZSP_gen hd hr
  | one => exact ggCZSP_one e
  | mul g h _ _ hg hh => exact ggCZSP_mul hg hh
  | inv g _ hg => exact ggCZSP_inv hg

private lemma ggCZSP_sq {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin m)} {s : Fin m → ZMod p}
    (hd : GGCZDual e φ)
    (hact : ∀ k, g (e k) = s k • e (σ k)) (hg2 : g * g = 1) :
    σ * σ = 1 ∧ ∀ k, s k * s (σ k) = 1 := by
  have hgg : ∀ k, g (g (e k)) = e k := by
    intro k
    have h := congrArg (fun h : V ≃ₗ[ZMod p] V => h (e k)) hg2
    simpa using h
  have hkey : ∀ k, e k = (s k * s (σ k)) • e (σ (σ k)) := by
    intro k
    rw [← hgg k, hact k, map_smul, hact, ← smul_smul]
  have hfix : ∀ k, σ (σ k) = k := by
    intro k
    by_contra hne
    have h := congrArg (φ k) (hkey k)
    rw [map_smul, hd k k, hd k (σ (σ k)), if_neg (Ne.symm hne)] at h
    simp only [smul_eq_mul, mul_zero] at h
    exact one_ne_zero h
  refine ⟨Equiv.ext hfix, fun k => ?_⟩
  have h := congrArg (φ k) (hkey k)
  rw [map_smul, hd k k, hd k (σ (σ k)), if_pos (hfix k).symm] at h
  simpa only [if_true, smul_eq_mul, mul_one] using h.symm

private lemma ggCZSP_sign_eq {s : Fin m → ZMod p} {σ : Equiv.Perm (Fin m)}
    (hs : ∀ k, s k = 1 ∨ s k = -1) (hss : ∀ k, s k * s (σ k) = 1) (k : Fin m) :
    s (σ k) = s k := by
  have h2 : s k * s k = 1 := by
    rcases hs k with h | h <;> rw [h] <;> norm_num
  calc
    s (σ k) = (s k * s k) * s (σ k) := by rw [h2, one_mul]
    _ = s k * (s k * s (σ k)) := by ring
    _ = s k * 1 := by rw [hss k]
    _ = s k := by rw [mul_one]

private lemma ggCZSP_sign_ne_zero {s : Fin m → ZMod p}
    (hs : ∀ k, s k = 1 ∨ s k = -1) (k : Fin m) : s k ≠ 0 := by
  rcases hs k with h | h
  · rw [h]; exact one_ne_zero
  · rw [h]; exact neg_ne_zero.mpr one_ne_zero

private lemma ggCZ_move_apply (g : V ≃ₗ[ZMod p] V) (x : V) : g x - x ∈ ggLinMove g := by
  rw [ggLinMove]
  refine LinearMap.mem_range.mpr ⟨x, ?_⟩
  rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]

private lemma ggCZ_false_of_two_moves {φ : Fin m → Module.Dual (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} (hr : Module.finrank (ZMod p) (ggLinMove g) = 1)
    {v w : V} (hv : v ∈ ggLinMove g) (hw : w ∈ ggLinMove g) (hv0 : v ≠ 0)
    {i : Fin m} (hvi : φ i v ≠ 0) (hwi : φ i w = 0) (hw0 : w ≠ 0) : False := by
  have : Module.Finite (ZMod p) (ggLinMove g) :=
    Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (K := ZMod p)
    (V := ↥(ggLinMove g)) ⟨v, hv⟩ (by simpa using hv0)).mp hr ⟨w, hw⟩
  have hcw : c • v = w := by simpa using congrArg Subtype.val hc
  have h : c * φ i v = 0 := by
    have := congrArg (φ i) hcw
    simpa only [map_smul, smul_eq_mul, hwi] using this
  have hc0 : c = 0 := (mul_eq_zero.mp h).resolve_right hvi
  rw [hc0, zero_smul] at hcw
  exact hw0 hcw.symm

private lemma ggCZeq_reflS {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V} {s : Fin m → ZMod p}
    (hact : ∀ k, g (e k) = s k • e k) {i : Fin m}
    (hsi : s i = -1) (hne : ∀ k, k ≠ i → s k = 1)
    (hfix : ∀ v, (∀ k, φ k v = 0) → g v = v) :
    g = ggCZreflS (φ := φ) i (ggCZdualS_root hd i) := by
  refine ggCZ_linearEquiv_eq_of_on_e_fix hd (fun k => ?_) (fun v hv => ?_)
  · rw [hact k, ggCZreflS_apply]
    by_cases hki : k = i
    · rw [hki, hsi, hd i i, if_pos rfl, mul_one, neg_one_smul, two_smul]
      abel
    · rw [hne k hki, hd i k, if_neg (Ne.symm hki), mul_zero, zero_smul, sub_zero, one_smul]
  · rw [hfix v hv, ggCZreflS_apply, hv i, mul_zero, zero_smul, sub_zero]

private lemma ggCZeq_reflDE {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V} {σ : Equiv.Perm (Fin m)}
    {s : Fin m → ZMod p} (hact : ∀ k, g (e k) = s k • e (σ k))
    (hs : ∀ k, s k = 1 ∨ s k = -1) (hss : ∀ k, s k * s (σ k) = 1) {i j : Fin m}
    (hij : i ≠ j) (hσi : σ i = j) (hσj : σ j = i)
    (hfixσ : ∀ k, k ≠ i → k ≠ j → σ k = k)
    (hfixs : ∀ k, k ≠ i → k ≠ j → s k = 1)
    (hfix : ∀ v, (∀ k, φ k v = 0) → g v = v) :
    g = ggCZreflDE (φ := φ) i j (s i) (ggCZdualE_root hd (hs i) hij) := by
  have hsj : s j = s i := by
    have h := ggCZSP_sign_eq hs hss i
    rwa [hσi] at h
  have hs2 : s i * s i = 1 := by
    rcases hs i with h | h <;> rw [h] <;> norm_num
  refine ggCZ_linearEquiv_eq_of_on_e_fix hd (fun k => ?_) (fun v hv => ?_)
  · rw [hact k, ggCZreflDE_apply]
    by_cases hki : k = i
    · rw [hki, hσi, hd i i, hd j i, if_pos rfl, if_neg (Ne.symm hij)]
      simp only [mul_zero, sub_zero, one_smul]
      abel
    · by_cases hkj : k = j
      · rw [hkj, hσj, hsj, hd i j, hd j j, if_neg hij, if_pos rfl]
        rw [mul_one, zero_sub, neg_smul, sub_neg_eq_add, smul_sub, smul_smul, hs2, one_smul]
        abel
      · rw [hfixσ k hki hkj, hfixs k hki hkj, hd i k, hd j k, if_neg (Ne.symm hki),
          if_neg (Ne.symm hkj)]
        simp only [mul_zero, sub_self, zero_smul, sub_zero, one_smul]
  · rw [hfix v hv, ggCZreflDE_apply, hv i, hv j, mul_zero, sub_zero, zero_smul, sub_zero]

theorem ggCZWB_refl (hp2 : p ≠ 2) {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggCZWB p e φ) (hr : GGLinRefl g) :
    g ∈ ggCZRD e φ ∪ ggCZS e φ := by
  obtain ⟨σ, s, hs, hact⟩ := ggCZWB_SP hd hg
  obtain ⟨hσ2, hss⟩ := ggCZSP_sq hd hact hr.1
  have hσ2' : ∀ k, σ (σ k) = k := by
    intro k
    have h := congrFun (congrArg (fun τ : Equiv.Perm (Fin m) => (τ : Fin m → Fin m)) hσ2) k
    simpa [Equiv.Perm.mul_apply] using h
  have hfixC : ∀ v, (∀ k, φ k v = 0) → g v = v := fun v hv => ggCZWB_fix hg hv
  by_cases hσid : σ = 1
  · have hact' : ∀ k, g (e k) = s k • e k := by
      intro k
      rw [hact k, hσid]
      simp
    by_cases hneg : ∃ i, s i = -1
    · obtain ⟨i, hsi⟩ := hneg
      by_cases hmore : ∃ j, j ≠ i ∧ s j = -1
      · obtain ⟨j, hji, hsj⟩ := hmore
        let v := g (e i) - e i
        let w := g (e j) - e j
        have hv : v ∈ ggLinMove g := ggCZ_move_apply g (e i)
        have hw : w ∈ ggLinMove g := ggCZ_move_apply g (e j)
        have hv_eq : φ i v = -2 := by
          simp only [v, hact' i, hsi, map_sub, map_smul, hd i i, if_true, smul_eq_mul]
          ring
        have hvi : φ i v ≠ 0 := by
          rw [hv_eq]
          exact neg_ne_zero.mpr (ggCZ_two_ne_zero hp2)
        have hwi : φ i w = 0 := by
          simp only [w, hact' j, hsj, map_sub, map_smul, hd i j,
            if_neg (Ne.symm hji), smul_eq_mul]
          ring
        have hwj_eq : φ j w = -2 := by
          simp only [w, hact' j, hsj, map_sub, map_smul, hd j j, if_true, smul_eq_mul]
          ring
        have hwj : φ j w ≠ 0 := by
          rw [hwj_eq]
          exact neg_ne_zero.mpr (ggCZ_two_ne_zero hp2)
        have hw0 : w ≠ 0 := fun h => hwj (by rw [h, map_zero])
        exact (ggCZ_false_of_two_moves hr.2 hv hw (fun h => hvi (by rw [h, map_zero]))
          hvi hwi hw0).elim
      · have hne : ∀ k, k ≠ i → s k = 1 := by
          intro k hki
          rcases hs k with h | h
          · exact h
          · exact absurd ⟨k, hki, h⟩ hmore
        have hgS := ggCZeq_reflS hd hact' hsi hne hfixC
        rw [hgS]
        exact Or.inr ⟨i, fun v =>
          ggCZreflS_apply (e := e) (φ := φ) (i := i) (ggCZdualS_root hd i) v⟩
    · have hs1 : ∀ k, s k = 1 := by
        intro k
        rcases hs k with h | h
        · exact h
        · exact absurd ⟨k, h⟩ hneg
      have hg1 : g = 1 := by
        refine ggCZ_linearEquiv_eq_of_on_e_fix hd (fun k => ?_) (fun v hv => hfixC v hv)
        rw [hact' k, hs1 k]
        simp
      have hzero : Module.finrank (ZMod p) (ggLinMove g) = 0 := by
        rw [hg1, ggLinMove, LinearEquiv.coe_toLinearMap_one, sub_self, LinearMap.range_zero,
          finrank_bot]
      rw [hr.2] at hzero
      norm_num at hzero
  · have hne : ∃ i, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hσid (Equiv.ext h)
    obtain ⟨i, hi⟩ := hne
    let j : Fin m := σ i
    have hji : j ≠ i := hi
    have hij : i ≠ j := fun h => hji h.symm
    have hσi : σ i = j := rfl
    have hσj : σ j = i := by
      rw [show σ j = σ (σ i) from rfl, hσ2']
    by_cases hextra : ∃ k, k ≠ i ∧ k ≠ j ∧ σ k ≠ k
    · obtain ⟨k, hki, hkj, hσk⟩ := hextra
      let l : Fin m := σ k
      have hσk_eq : σ k = l := rfl
      have hlk : l ≠ k := hσk
      have hσl : σ l = k := by
        rw [show l = σ k from rfl, hσ2']
      have hli : l ≠ i := by
        intro h
        apply hkj
        rw [← hσi, ← hσl, h]
      have hlj : l ≠ j := by
        intro h
        apply hki
        rw [← hσj, ← hσl, h]
      let v := g (e i) - e i
      let w := g (e k) - e k
      have hv : v ∈ ggLinMove g := ggCZ_move_apply g (e i)
      have hw : w ∈ ggLinMove g := ggCZ_move_apply g (e k)
      have hv_eq : φ i v = -1 := by
        simp only [v, hact i, hσi, map_sub, map_smul, hd i j, hd i i, if_neg hij,
           if_true, smul_eq_mul]
        ring
      have hvi : φ i v ≠ 0 := by
        rw [hv_eq]
        exact neg_ne_zero.mpr one_ne_zero
      have hwi : φ i w = 0 := by
        change φ i (g (e k) - e k) = 0
        rw [hact k, hσk_eq]
        simp only [map_sub, map_smul, hd i l, hd i k, if_neg (Ne.symm hli),
          if_neg (Ne.symm hki), smul_eq_mul]
        ring
      have hwk_eq : φ k w = -1 := by
        change φ k (g (e k) - e k) = -1
        rw [hact k, hσk_eq]
        simp only [map_sub, map_smul, hd k l, hd k k, if_neg (Ne.symm hlk), if_true,
          smul_eq_mul]
        ring
      have hwk : φ k w ≠ 0 := by
        rw [hwk_eq]
        exact neg_ne_zero.mpr one_ne_zero
      have hw0 : w ≠ 0 := fun h => hwk (by rw [h, map_zero])
      exact (ggCZ_false_of_two_moves hr.2 hv hw (fun h => hvi (by rw [h, map_zero]))
        hvi hwi hw0).elim
    · push Not at hextra
      by_cases hneg : ∃ k, k ≠ i ∧ k ≠ j ∧ s k = -1
      · obtain ⟨k, hki, hkj, hsk⟩ := hneg
        let v := g (e i) - e i
        let w := g (e k) - e k
        have hv : v ∈ ggLinMove g := ggCZ_move_apply g (e i)
        have hw : w ∈ ggLinMove g := ggCZ_move_apply g (e k)
        have hv_eq : φ i v = -1 := by
          simp only [v, hact i, hσi, map_sub, map_smul, hd i j, hd i i, if_neg hij,
             if_true, smul_eq_mul]
          ring
        have hvi : φ i v ≠ 0 := by
          rw [hv_eq]
          exact neg_ne_zero.mpr one_ne_zero
        have hwi : φ i w = 0 := by
          simp only [w, hact k, hextra k hki hkj, hsk, map_sub, map_smul, hd i k,
            if_neg (Ne.symm hki), smul_eq_mul]
          ring
        have hwk_eq : φ k w = -2 := by
          simp only [w, hact k, hextra k hki hkj, hsk, map_sub, map_smul, hd k k,
             if_true, smul_eq_mul]
          ring
        have hwk : φ k w ≠ 0 := by
          rw [hwk_eq]
          exact neg_ne_zero.mpr (ggCZ_two_ne_zero hp2)
        have hw0 : w ≠ 0 := fun h => hwk (by rw [h, map_zero])
        exact (ggCZ_false_of_two_moves hr.2 hv hw (fun h => hvi (by rw [h, map_zero]))
          hvi hwi hw0).elim
      · push Not at hneg
        have hfixs : ∀ k, k ≠ i → k ≠ j → s k = 1 := by
          intro k hki hkj
          rcases hs k with h | h
          · exact h
          · exact absurd h (hneg k hki hkj)
        have hgRD := ggCZeq_reflDE hd hact hs hss hij hσi hσj hextra hfixs hfixC
        rw [hgRD]
        exact Or.inl ⟨i, j, hij, s i, hs i, fun v => ggCZreflDE_apply _ v⟩

private lemma ggCZreflDE_fix {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    {i j : Fin m} {ε : ZMod p}
    (h : ggCZdualE (φ := φ) i j ε (e i - ε • e j) = 2) {v : V}
    (hv : ∀ k, φ k v = 0) : ggCZreflDE (φ := φ) i j ε h v = v := by
  rw [ggCZreflDE_apply]
  simp only [hv i, hv j, mul_zero, sub_zero, zero_smul, sub_self]

private lemma ggCZreflDE_apply_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {a b c : Fin m} (hab : a ≠ b)
    (h : ggCZdualE (φ := φ) a b 1 (e a - (1 : ZMod p) • e b) = 2) :
    ggCZreflDE (φ := φ) a b 1 h (e c) = e (Equiv.swap a b c) := by
  rw [ggCZreflDE_apply]
  by_cases hca : c = a
  · rw [hca, hd a a, hd b a, if_pos rfl, if_neg (Ne.symm hab)]
    rw [Equiv.swap_apply_left]
    simp only [mul_zero, sub_zero, one_smul]
    abel
  · by_cases hcb : c = b
    · rw [hcb, hd a b, hd b b, if_neg hab, if_pos rfl]
      rw [Equiv.swap_apply_right]
      module
    · have hswap : Equiv.swap a b c = c := by
        rw [Equiv.swap_apply_def]
        simp [hca, hcb]
      rw [hswap, hd a c, hd b c, if_neg (Ne.symm hca), if_neg (Ne.symm hcb)]
      simp only [mul_zero, sub_self, zero_smul, sub_zero]

private lemma ggCZreflDE_conj_swap {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {a b i j : Fin m} (hab : a ≠ b) (hij : i ≠ j)
    (hσ : ggCZdualE (φ := φ) a b 1 (e a - (1 : ZMod p) • e b) = 2)
    (hτ : ggCZdualE (φ := φ) i j 1 (e i - (1 : ZMod p) • e j) = 2)
    (hτ' : ggCZdualE (φ := φ) (Equiv.swap a b i) (Equiv.swap a b j) 1
      (e (Equiv.swap a b i) - (1 : ZMod p) • e (Equiv.swap a b j)) = 2) :
    ggCZreflDE (φ := φ) a b 1 hσ * ggCZreflDE (φ := φ) i j 1 hτ *
      (ggCZreflDE (φ := φ) a b 1 hσ)⁻¹ =
      ggCZreflDE (φ := φ) (Equiv.swap a b i) (Equiv.swap a b j) 1 hτ' := by
  have hswapij : Equiv.swap a b i ≠ Equiv.swap a b j := by
    intro h
    apply hij
    simpa using congrArg (Equiv.swap a b) h
  have hinv : (ggCZreflDE (φ := φ) a b 1 hσ)⁻¹ = ggCZreflDE (φ := φ) a b 1 hσ := by
    apply inv_eq_of_mul_eq_one_right
    ext z
    exact ggCZreflDE_involutive hσ z
  refine ggCZ_linearEquiv_eq_of_on_e_fix hd (fun c => ?_) (fun v hv => ?_)
  · rw [hinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ggCZreflDE_apply_e hd hab hσ, ggCZreflDE_apply_e hd hij hτ,
      ggCZreflDE_apply_e hd hab hσ, ggCZreflDE_apply_e hd hswapij hτ']
    have hperm : Equiv.swap (Equiv.swap a b i) (Equiv.swap a b j) =
        ((Equiv.swap a b).symm.trans (Equiv.swap i j)).trans (Equiv.swap a b) :=
      (Equiv.symm_trans_swap_trans i j (Equiv.swap a b)).symm
    rw [hperm]
    simp [Equiv.trans_apply]
  · rw [hinv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ggCZreflDE_fix hσ hv, ggCZreflDE_fix hτ hv, ggCZreflDE_fix hσ hv,
      ggCZreflDE_fix hτ' hv]

private noncomputable def ggCZD {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (a b : Fin m) (hab : a ≠ b) : V ≃ₗ[ZMod p] V :=
  ggCZreflDE (φ := φ) a b 1 (ggCZdualE_root hd (Or.inl rfl) hab)

private lemma ggCZD_mem {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {a b : Fin m} (hab : a ≠ b) :
    ggCZD hd a b hab ∈ ggCZWB p e φ :=
  ggCZreflDE_mem_one hd hab

private lemma ggCZD_conj_swap {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {a b i j : Fin m} (hab : a ≠ b) (hij : i ≠ j) :
    ggCZD hd a b hab * ggCZD hd i j hij * (ggCZD hd a b hab)⁻¹ =
      ggCZD hd (Equiv.swap a b i) (Equiv.swap a b j)
        (by intro h; exact hij ((Equiv.swap a b).injective h)) := by
  exact ggCZreflDE_conj_swap hd hab hij _ _ _


private lemma ggCZD_symm {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) :
    ggCZD hd i j hij = ggCZD hd j i (Ne.symm hij) := by
  refine ggCZ_linearEquiv_eq_of_on_e_fix hd (fun c => ?_) (fun v hv => ?_)
  · rw [ggCZD, ggCZD,
      ggCZreflDE_apply_e hd hij (ggCZdualE_root hd (Or.inl rfl) hij),
      ggCZreflDE_apply_e hd (Ne.symm hij) (ggCZdualE_root hd (Or.inl rfl) (Ne.symm hij)),
      Equiv.swap_comm]
  · rw [ggCZD, ggCZD,
      ggCZreflDE_fix (h := ggCZdualE_root hd (Or.inl rfl) hij) hv,
      ggCZreflDE_fix (h := ggCZdualE_root hd (Or.inl rfl) (Ne.symm hij)) hv]

private lemma ggCZD_conj_mul {g₁ g₂ r s t : V ≃ₗ[ZMod p] V}
    (h₁ : g₁ * r * g₁⁻¹ = s) (h₂ : g₂ * s * g₂⁻¹ = t) :
    (g₂ * g₁) * r * (g₂ * g₁)⁻¹ = t := by
  rw [mul_inv_rev]
  calc
    g₂ * g₁ * r * (g₁⁻¹ * g₂⁻¹) = g₂ * (g₁ * r * g₁⁻¹) * g₂⁻¹ := by group
    _ = g₂ * s * g₂⁻¹ := by rw [h₁]
    _ = t := h₂

private lemma ggCZD_conj_exists {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ g ∈ ggCZWB p e φ, g * ggCZD hd i j hij * g⁻¹ = ggCZD hd k l hkl := by
  classical
  by_cases hik : i = k
  · by_cases hjl : j = l
    · exact ⟨1, Subgroup.one_mem _, by simp [hik, hjl]⟩
    · have hjl' : j ≠ l := hjl
      have hil : i ≠ l := by
        intro h
        exact hkl (by rw [← hik, h])
      refine ⟨ggCZD hd j l hjl', ggCZD_mem hd hjl', ?_⟩
      have hswap_i : Equiv.swap j l i = i :=
        Equiv.swap_apply_of_ne_of_ne hij hil
      have hswap_j : Equiv.swap j l j = l := Equiv.swap_apply_left j l
      simpa [hik.symm, hswap_i, hswap_j] using ggCZD_conj_swap hd hjl' hij
  · by_cases hjl : j = l
    · have hik' : i ≠ k := hik
      have hjk : j ≠ k := by
        intro h
        exact hkl (by rw [← hjl, h])
      refine ⟨ggCZD hd i k hik', ggCZD_mem hd hik', ?_⟩
      have hswap_i : Equiv.swap i k i = k := Equiv.swap_apply_left i k
      have hswap_j : Equiv.swap i k j = j :=
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk
      simpa [hjl.symm, hswap_i, hswap_j] using ggCZD_conj_swap hd hik' hij
    · by_cases hjk : j = k
      · by_cases hli : l = i
        · refine ⟨ggCZD hd i j hij, ggCZD_mem hd hij, ?_⟩
          have hmem := ggCZD_conj_swap hd hij hij
          simpa [hjk, hli, Equiv.swap_apply_left, Equiv.swap_apply_right] using hmem
        · have hil : i ≠ l := fun h => hli h.symm
          have hji : j ≠ i := Ne.symm hij
          have hjl' : j ≠ l := by rw [hjk]; exact hkl
          have h1 : ggCZD hd i j hij * ggCZD hd i j hij * (ggCZD hd i j hij)⁻¹ =
              ggCZD hd j i hji := by
            simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using
              ggCZD_conj_swap hd hij hij
          have hswap_j : Equiv.swap i l j = j :=
            Equiv.swap_apply_of_ne_of_ne hji hjl'
          have h2 : ggCZD hd i l hil * ggCZD hd j i hji * (ggCZD hd i l hil)⁻¹ =
              ggCZD hd j l hjl' := by
            simpa only [hswap_j, Equiv.swap_apply_left] using
              ggCZD_conj_swap hd hil hji
          refine ⟨ggCZD hd i l hil * ggCZD hd i j hij,
            Subgroup.mul_mem _ (ggCZD_mem hd hil) (ggCZD_mem hd hij), ?_⟩
          simpa [hjk] using ggCZD_conj_mul h1 h2
      · by_cases hli : l = i
        · have hkl' : k ≠ i := fun h => hkl (by rw [hli, h])
          have hji : j ≠ i := Ne.symm hij
          have hjk' : j ≠ k := hjk
          have h1 : ggCZD hd j i hji * ggCZD hd i j hij * (ggCZD hd j i hji)⁻¹ =
              ggCZD hd i j hij := by
            simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right,
              ggCZD_symm hd hji] using ggCZD_conj_swap hd hji hij
          have hswap_i : Equiv.swap j k i = i :=
            Equiv.swap_apply_of_ne_of_ne hij hik
          have h2 : ggCZD hd j k hjk' * ggCZD hd i j hij * (ggCZD hd j k hjk')⁻¹ =
              ggCZD hd i k hik := by
            simpa only [hswap_i, Equiv.swap_apply_left] using
              ggCZD_conj_swap hd hjk' hij
          refine ⟨ggCZD hd j k hjk' * ggCZD hd j i hji,
            Subgroup.mul_mem _ (ggCZD_mem hd hjk') (ggCZD_mem hd hji), ?_⟩
          calc
            ggCZD hd j k hjk' * ggCZD hd j i hji * ggCZD hd i j hij *
                (ggCZD hd j k hjk' * ggCZD hd j i hji)⁻¹
                = ggCZD hd i k hik := by
              simpa only [mul_assoc] using ggCZD_conj_mul h1 h2
            _ = ggCZD hd k l hkl := by simp [hli, ggCZD_symm hd hkl']
        · have hji : j ≠ i := Ne.symm hij
          have hkj : k ≠ j := Ne.symm hjk
          have hjl' : j ≠ l := hjl
          have hik' : i ≠ k := hik
          have hkl' : k ≠ l := hkl
          have h1 : ggCZD hd i k hik' * ggCZD hd i j hij * (ggCZD hd i k hik')⁻¹ =
              ggCZD hd k j hkj := by
            have hswap_j : Equiv.swap i k j = j :=
              Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) hjk
            simpa only [hswap_j, Equiv.swap_apply_left] using
              ggCZD_conj_swap hd hik' hij
          have h2 : ggCZD hd j l hjl' * ggCZD hd k j hkj * (ggCZD hd j l hjl')⁻¹ =
              ggCZD hd k l hkl' := by
            have hswap_k : Equiv.swap j l k = k :=
              Equiv.swap_apply_of_ne_of_ne hkj hkl'
            simpa only [hswap_k, Equiv.swap_apply_left] using
              ggCZD_conj_swap hd hjl' hkj
          refine ⟨ggCZD hd j l hjl' * ggCZD hd i k hik',
            Subgroup.mul_mem _ (ggCZD_mem hd hjl') (ggCZD_mem hd hik'), ?_⟩
          exact ggCZD_conj_mul h1 h2


private lemma ggCZreflS_apply_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (i c : Fin m) :
    ggCZreflS (φ := φ) i (ggCZdualS_root hd i) (e c) =
      if c = i then -e c else e c := by
  rw [ggCZreflS_apply]
  by_cases hci : c = i
  · rw [hci, hd i i, if_pos rfl, if_pos rfl, mul_one, two_smul]
    abel
  · rw [hd i c, if_neg (Ne.symm hci), if_neg hci, mul_zero, zero_smul, sub_zero]

private lemma ggCZreflS_fix {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i : Fin m} {v : V} (hv : ∀ k, φ k v = 0) :
    ggCZreflS (φ := φ) i (ggCZdualS_root hd i) v = v := by
  rw [ggCZreflS_apply, hv i, mul_zero, zero_smul, sub_zero]

private lemma ggCZreflS_conj_D {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i k : Fin m} (hik : i ≠ k) :
    ggCZD hd i k hik * ggCZreflS (φ := φ) i (ggCZdualS_root hd i) *
      (ggCZD hd i k hik)⁻¹ = ggCZreflS (φ := φ) k (ggCZdualS_root hd k) := by
  have hσ : ggCZdualE (φ := φ) i k 1 (e i - (1 : ZMod p) • e k) = 2 :=
    ggCZdualE_root hd (Or.inl rfl) hik
  have hτ : ggCZdualS (φ := φ) i (e i) = 2 := ggCZdualS_root hd i
  have hD2 : ggCZD hd i k hik * ggCZD hd i k hik = 1 := by
    ext z
    rw [ggCZD, LinearEquiv.mul_apply]
    exact ggCZreflDE_involutive _ z
  have hDinv : (ggCZD hd i k hik)⁻¹ = ggCZD hd i k hik :=
    inv_eq_of_mul_eq_one_right hD2
  refine LinearEquiv.ext fun v => ?_
  rw [ggCZD]
  rw [ggCZconj_apply_of_formula (σ := ggCZreflDE (φ := φ) i k 1 hσ)
      (τ := ggCZreflS (φ := φ) i (ggCZdualS_root hd i))
      (g := ggCZdualS (φ := φ) i)
      (y := e i)
      (fun z => ggCZreflS_apply (ggCZdualS_root hd i) z)
      (ggCZreflDE_involutive hσ) v]
  rw [ggCZreflS_apply (ggCZdualS_root hd k), ggCZreflDE_apply, ggCZreflDE_apply,
    ggCZdualS_apply, map_sub, map_smul, map_sub]
  simp only [hd i i, hd i k, hd k i, if_neg hik,
    if_neg (Ne.symm hik), if_true, one_mul, mul_one, mul_zero, sub_zero,
    smul_eq_mul, one_smul]
  module

theorem ggCZWB_conj_RD {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZRD e φ) (hr' : r' ∈ ggCZRD e φ) :
    ∃ g ∈ ggCZWB p e φ, g * r * g⁻¹ = r' := by
  obtain ⟨i, j, hij, ε, hε, hform⟩ := hr
  obtain ⟨k, l, hkl, δ, hδ, hform'⟩ := hr'
  have htoD : ∃ (a b : Fin m) (hab : a ≠ b) (g : V ≃ₗ[ZMod p] V),
      g ∈ ggCZWB p e φ ∧ g * r * g⁻¹ = ggCZD hd a b hab := by
    rcases hε with rfl | rfl
    · refine ⟨i, j, hij, 1, Subgroup.one_mem _, ?_⟩
      have hrD : r = ggCZD hd i j hij := by
        ext v
        rw [ggCZD, ggCZreflDE_apply, hform v]
      rw [hrD]
      simp
    · refine ⟨i, j, hij, ggCZreflS (φ := φ) j (ggCZdualS_root hd j), ggCZreflS_mem hd j, ?_⟩
      have hrPlus : r = ggCZreflDE (φ := φ) i j (-1)
          (ggCZdualE_root hd (Or.inr rfl) hij) := by
        ext v
        rw [ggCZreflDE_apply, hform v]
      have hconj := ggCZreflS_conj_plus hd (i := i) (j := j) hij
      have hS2 : ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
          ggCZreflS (φ := φ) j (ggCZdualS_root hd j) = 1 := by
        ext z
        exact ggCZreflS_involutive _ z
      have hSinv : (ggCZreflS (φ := φ) j (ggCZdualS_root hd j))⁻¹ =
          ggCZreflS (φ := φ) j (ggCZdualS_root hd j) :=
        inv_eq_of_mul_eq_one_right hS2
      have hconj' : ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
          ggCZD hd i j hij *
          ggCZreflS (φ := φ) j (ggCZdualS_root hd j) = ggCZreflDE (φ := φ) i j (-1)
            (ggCZdualE_root hd (Or.inr rfl) hij) := by
        simpa only [ggCZD, hSinv] using hconj
      rw [hrPlus, hSinv]
      calc
        ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
            ggCZreflDE (φ := φ) i j (-1) (ggCZdualE_root hd (Or.inr rfl) hij) *
            ggCZreflS (φ := φ) j (ggCZdualS_root hd j) =
            ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
              (ggCZreflS (φ := φ) j (ggCZdualS_root hd j) * ggCZD hd i j hij *
                ggCZreflS (φ := φ) j (ggCZdualS_root hd j)) *
              ggCZreflS (φ := φ) j (ggCZdualS_root hd j) := by rw [hconj']
        _ = ggCZD hd i j hij := by
          have hgoal : ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
              (ggCZreflS (φ := φ) j (ggCZdualS_root hd j) * ggCZD hd i j hij *
                ggCZreflS (φ := φ) j (ggCZdualS_root hd j)) *
              ggCZreflS (φ := φ) j (ggCZdualS_root hd j) =
              (ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
                ggCZreflS (φ := φ) j (ggCZdualS_root hd j)) * ggCZD hd i j hij *
                (ggCZreflS (φ := φ) j (ggCZdualS_root hd j) *
                  ggCZreflS (φ := φ) j (ggCZdualS_root hd j)) := by group
          rw [hgoal, hS2, mul_one, one_mul]
  obtain ⟨a, b, hab, g, hg, hgr⟩ := htoD
  have htoD' : ∃ (c d : Fin m) (hcd : c ≠ d) (g' : V ≃ₗ[ZMod p] V),
      g' ∈ ggCZWB p e φ ∧ g' * r' * g'⁻¹ = ggCZD hd c d hcd := by
    rcases hδ with rfl | rfl
    · refine ⟨k, l, hkl, 1, Subgroup.one_mem _, ?_⟩
      have hrD : r' = ggCZD hd k l hkl := by
        ext v
        rw [ggCZD, ggCZreflDE_apply, hform' v]
      rw [hrD]
      simp
    · refine ⟨k, l, hkl, ggCZreflS (φ := φ) l (ggCZdualS_root hd l), ggCZreflS_mem hd l, ?_⟩
      have hrPlus : r' = ggCZreflDE (φ := φ) k l (-1)
          (ggCZdualE_root hd (Or.inr rfl) hkl) := by
        ext v
        rw [ggCZreflDE_apply, hform' v]
      have hconj := ggCZreflS_conj_plus hd (i := k) (j := l) hkl
      have hS2 : ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
          ggCZreflS (φ := φ) l (ggCZdualS_root hd l) = 1 := by
        ext z
        exact ggCZreflS_involutive _ z
      have hSinv : (ggCZreflS (φ := φ) l (ggCZdualS_root hd l))⁻¹ =
          ggCZreflS (φ := φ) l (ggCZdualS_root hd l) :=
        inv_eq_of_mul_eq_one_right hS2
      have hconj' : ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
          ggCZD hd k l hkl *
          ggCZreflS (φ := φ) l (ggCZdualS_root hd l) = ggCZreflDE (φ := φ) k l (-1)
            (ggCZdualE_root hd (Or.inr rfl) hkl) := by
        simpa only [ggCZD, hSinv] using hconj
      rw [hrPlus, hSinv]
      calc
        ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
            ggCZreflDE (φ := φ) k l (-1) (ggCZdualE_root hd (Or.inr rfl) hkl) *
            ggCZreflS (φ := φ) l (ggCZdualS_root hd l) =
            ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
              (ggCZreflS (φ := φ) l (ggCZdualS_root hd l) * ggCZD hd k l hkl *
                ggCZreflS (φ := φ) l (ggCZdualS_root hd l)) *
              ggCZreflS (φ := φ) l (ggCZdualS_root hd l) := by rw [hconj']
        _ = ggCZD hd k l hkl := by
          have hgoal : ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
              (ggCZreflS (φ := φ) l (ggCZdualS_root hd l) * ggCZD hd k l hkl *
                ggCZreflS (φ := φ) l (ggCZdualS_root hd l)) *
              ggCZreflS (φ := φ) l (ggCZdualS_root hd l) =
              (ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
                ggCZreflS (φ := φ) l (ggCZdualS_root hd l)) * ggCZD hd k l hkl *
                (ggCZreflS (φ := φ) l (ggCZdualS_root hd l) *
                  ggCZreflS (φ := φ) l (ggCZdualS_root hd l)) := by group
          rw [hgoal, hS2, mul_one, one_mul]
  obtain ⟨c, d, hcd, g', hg', hgr'⟩ := htoD'
  obtain ⟨h, hh, hconj⟩ := ggCZD_conj_exists hd hab hcd
  have hg'inv : (g')⁻¹ * ggCZD hd c d hcd * g' = r' := by
    rw [← hgr']
    group
  refine ⟨(g')⁻¹ * h * g, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hh) hg
  · calc
      ((g')⁻¹ * h * g) * r * ((g')⁻¹ * h * g)⁻¹ =
          (g')⁻¹ * h * (g * r * g⁻¹) * h⁻¹ * g' := by group
      _ = (g')⁻¹ * h * ggCZD hd a b hab * h⁻¹ * g' := by rw [hgr]
      _ = (g')⁻¹ * (h * ggCZD hd a b hab * h⁻¹) * g' := by group
      _ = (g')⁻¹ * ggCZD hd c d hcd * g' := by rw [hconj]
      _ = r' := hg'inv

theorem ggCZWB_conj_S {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {r r' : V ≃ₗ[ZMod p] V} (hr : r ∈ ggCZS e φ) (hr' : r' ∈ ggCZS e φ) :
    ∃ g ∈ ggCZWB p e φ, g * r * g⁻¹ = r' := by
  obtain ⟨i, hi⟩ := hr
  obtain ⟨k, hk⟩ := hr'
  have hri : r = ggCZreflS (φ := φ) i (ggCZdualS_root hd i) := by
    ext v
    rw [ggCZreflS_apply]
    exact hi v
  have hrk : r' = ggCZreflS (φ := φ) k (ggCZdualS_root hd k) := by
    ext v
    rw [ggCZreflS_apply]
    exact hk v
  by_cases hik : i = k
  · exact ⟨1, Subgroup.one_mem _, by rw [hri, hrk]; simp [hik]⟩
  · have hmem := ggCZreflS_conj_D hd hik
    refine ⟨ggCZD hd i k hik, ggCZD_mem hd hik, ?_⟩
    rw [hri, hrk]
    exact hmem

private lemma ggCZ_phi_sum_e {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (w : Fin m → ZMod p) (i : Fin m) :
    φ i (∑ k, w k • e k) = w i := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hsum : (∑ k, w k * (if i = k then 1 else 0)) = w i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      rw [if_neg (Ne.symm hki), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simpa only [hd i] using hsum

private lemma ggCZ_sum_coord {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) (w : Fin m → ZMod p) (i : Fin m) :
    (∑ k, w k * φ k (e i)) = w i := by
  have hsum : (∑ k, w k * (if k = i then 1 else 0)) = w i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      rw [if_neg hki, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hsum' : (∑ k, w k * φ k (e i)) =
      ∑ k, w k * (if k = i then 1 else 0) :=
    Finset.sum_congr rfl fun k _ => by rw [hd k i]
  rw [hsum', hsum]

theorem ggCZWB_not_mem_H (hp2 : p ≠ 2) (hm : 2 ≤ m) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {g : V ≃ₗ[ZMod p] V}
    (hg : g ∈ ggCZWB p e φ) : g ∉ ggCZH e φ := by
  intro hH
  obtain ⟨w, hw, hformula⟩ := hH
  obtain ⟨σ, s, hs, hact⟩ := ggCZWB_SP hd hg
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hw0 : w i0 = 1 ∨ w i0 = -1 := hw i0
  have hw1 : w i1 = 1 ∨ w i1 = -1 := hw i1
  have hw0sq : w i0 * w i0 = 1 := by
    rcases hw0 with h | h <;> rw [h] <;> norm_num
  have h2 : (2 : ZMod p) ≠ 0 := ggCZ_two_ne_zero hp2
  have h2inv : (2 : ZMod p)⁻¹ ≠ 0 := inv_ne_zero h2
  have hzero : w i0 * w i1 ≠ 0 := by
    apply mul_ne_zero
    · rcases hw0 with h | h <;> rw [h] <;> simp
    · rcases hw1 with h | h <;> rw [h] <;> simp
  have hcoord0 : φ i0 (g (e i0)) = (2 : ZMod p)⁻¹ := by
    rw [hformula, map_sub, map_smul, ggCZ_sum_coord hd w i0, ggCZ_phi_sum_e hd w i0]
    simp only [hd i0 i0, if_true, smul_eq_mul]
    field_simp
    rw [pow_two, hw0sq]
    norm_num
  have hcoord1 : φ i1 (g (e i0)) = -((2 : ZMod p)⁻¹ * w i0 * w i1) := by
    rw [hformula, map_sub, map_smul, ggCZ_sum_coord hd w i0, ggCZ_phi_sum_e hd w i1]
    simp only [  hd i1 i0, if_neg (Ne.symm hi01), smul_eq_mul]
    ring
  have hif0 : i0 = σ i0 := by
    by_contra h
    have hz : φ i0 (g (e i0)) = 0 := by
      rw [hact i0, map_smul, hd i0 (σ i0), if_neg h, smul_eq_mul, mul_zero]
    rw [hcoord0] at hz
    exact h2inv hz
  have hif1 : i1 = σ i0 := by
    by_contra h
    have hz : φ i1 (g (e i0)) = 0 := by
      rw [hact i0, map_smul, hd i1 (σ i0), if_neg h, smul_eq_mul, mul_zero]
    rw [hcoord1] at hz
    have hprod : (2 : ZMod p)⁻¹ * w i0 * w i1 = 0 := by
      have := neg_eq_zero.mp hz
      simpa [mul_assoc] using this
    exact hzero (by
      rcases mul_eq_zero.mp hprod with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2inv
        · rw [h'', zero_mul]
      · rw [h', mul_zero])
  exact hi01 (hif0.trans hif1.symm)

end

end CFSG.StandardType

end

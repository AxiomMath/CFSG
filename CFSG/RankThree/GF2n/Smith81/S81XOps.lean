module

public import Mathlib.Tactic.Module
public import Mathlib.Data.Finsupp.SMul

public section

namespace CFSG.RankThree.GF2n.Smith81.XOps

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

@[expose] def Fil (lev : ι → ℤ) (k : ℤ) : Submodule K (ι →₀ K) where
  carrier := {v | ∀ b, lev b < k → v b = 0}
  add_mem' := fun {a b} ha hb x hx => by simp [ha x hx, hb x hx]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c v hv x hx => by simp [hv x hx]

theorem mem_Fil {lev : ι → ℤ} {k : ℤ} {v : ι →₀ K} : v ∈ Fil lev k ↔ ∀ b, lev b < k → v b = 0 :=
  Iff.rfl

theorem Fil_mono {lev : ι → ℤ} {k k' : ℤ} (h : k ≤ k') : Fil (K := K) lev k' ≤ Fil lev k :=
  fun _ hv b hb => hv b (lt_of_lt_of_le hb h)

@[expose] def Raises (lev : ι → ℤ) (d : ℤ) (E : Module.End K (ι →₀ K)) : Prop :=
  ∀ b b', E (Finsupp.single b 1) b' ≠ 0 → lev b' = lev b + d

theorem single_mem_Fil (lev : ι → ℤ) (b : ι) : Finsupp.single b (1 : K) ∈ Fil lev (lev b) := by
  rw [mem_Fil]
  intro b' hb'
  rw [Finsupp.single_apply, if_neg]
  intro h
  subst h
  exact lt_irrefl _ hb'

theorem Raises.map_Fil {lev : ι → ℤ} {d : ℤ} {E : Module.End K (ι →₀ K)} (h : Raises lev d E)
    {k : ℤ} {v : ι →₀ K} (hv : v ∈ Fil lev k) : E v ∈ Fil lev (k + d) := by
  rw [mem_Fil]
  intro b' hb'
  have hsum : v = ∑ b ∈ v.support, v b • Finsupp.single b (1 : K) := by
    conv_lhs => rw [← Finsupp.sum_single v]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finsupp.smul_single_one]
  rw [hsum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hE : E (Finsupp.single b 1) b' = 0
  · rw [hE, mul_zero]
  · have hlev := h b b' hE
    have hvb : v b ≠ 0 := Finsupp.mem_support_iff.mp hb
    have hkb : k ≤ lev b := by
      by_contra hcon
      exact hvb ((mem_Fil.mp hv) b (not_le.mp hcon))
    exfalso
    omega

theorem Raises.single_mem_Fil {lev : ι → ℤ} {d : ℤ} {E : Module.End K (ι →₀ K)}
    (h : Raises lev d E) (b : ι) : E (Finsupp.single b 1) ∈ Fil lev (lev b + d) :=
  h.map_Fil (XOps.single_mem_Fil lev b)

theorem xops_list_sum_mem {ρ : Type*} (lev : ι → ℤ) (k : ℤ) (g : ρ → ι →₀ K) (L : List ρ)
    (h : ∀ γ ∈ L, g γ ∈ Fil lev k) : (L.map g).sum ∈ Fil lev k := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ (h a (by simp)) (ih fun γ hγ => h γ (by simp [hγ]))

theorem xops_list_sum_apply {ρ : Type*} (L : List ρ) (g : ρ → ι →₀ K) (x : ι) :
    (L.map g).sum x = (L.map fun γ => g γ x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem xops_step {M : Type*} [AddCommGroup M] [Module K M] (A : Module.End K M) (c : K)
    (x v t : M) :
    x + c • A x - v - (c • A v + t) = (x - v - t) + c • A t + c • A (x - v - t) := by
  rw [map_sub, map_sub]
  module

theorem prod_expansion {ρ : Type*} (lev : ι → ℤ) {d : ℤ} (hd : 0 < d) (L : List ρ)
    (E : ρ → Module.End K (ι →₀ K)) (c : ρ → K) (hL : ∀ γ ∈ L, Raises lev d (E γ)) (b : ι) :
    ((L.map fun γ => (1 : Module.End K (ι →₀ K)) + c γ • E γ).prod) (Finsupp.single b 1) -
        Finsupp.single b 1 -
        (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum ∈ Fil lev (lev b + 2 * d) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hL' : ∀ γ ∈ L, Raises lev d (E γ) := fun γ hγ => hL γ (List.mem_cons_of_mem _ hγ)
    have ha : Raises lev d (E a) := hL a (by simp)
    have hr := ih hL'
    have ht : (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum ∈ Fil lev (lev b + d) :=
      xops_list_sum_mem lev _ _ L fun γ hγ => Submodule.smul_mem _ _ ((hL' γ hγ).single_mem_Fil b)
    have hEt : E a (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum ∈ Fil lev (lev b + 2 * d) :=
      Fil_mono (by omega) (ha.map_Fil ht)
    have hEr : E a (((L.map fun γ => (1 : Module.End K (ι →₀ K)) + c γ • E γ).prod)
        (Finsupp.single b 1) - Finsupp.single b 1 -
          (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum) ∈ Fil lev (lev b + 2 * d) :=
      Fil_mono (by omega) (ha.map_Fil hr)
    have hmem := Submodule.add_mem _ (Submodule.add_mem _ hr (Submodule.smul_mem _ (c a) hEt))
      (Submodule.smul_mem _ (c a) hEr)
    have key := xops_step (E a) (c a)
      (((L.map fun γ => (1 : Module.End K (ι →₀ K)) + c γ • E γ).prod) (Finsupp.single b 1))
      (Finsupp.single b 1) (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Module.End.mul_apply,
      LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply]
    rw [key]
    exact hmem

theorem prod_coord {ρ : Type*} (lev : ι → ℤ) {d : ℤ} (hd : 0 < d) (L : List ρ)
    (E : ρ → Module.End K (ι →₀ K)) (c : ρ → K) (hL : ∀ γ ∈ L, Raises lev d (E γ)) (b b' : ι)
    (hb' : lev b' = lev b + d) :
    ((L.map fun γ => (1 : Module.End K (ι →₀ K)) + c γ • E γ).prod) (Finsupp.single b 1) b' =
      (L.map fun γ => c γ * E γ (Finsupp.single b 1) b').sum := by
  have hexp := (mem_Fil.mp (prod_expansion lev hd L E c hL b)) b' (by omega)
  have hbb : Finsupp.single b (1 : K) b' = 0 := by
    rw [Finsupp.single_apply, if_neg]
    intro h
    subst h
    omega
  simp only [Finsupp.sub_apply, hbb, sub_zero, xops_list_sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at hexp
  exact sub_eq_zero.mp hexp

theorem prod_coord_low {ρ : Type*} (lev : ι → ℤ) {d : ℤ} (hd : 0 < d) (L : List ρ)
    (E : ρ → Module.End K (ι →₀ K)) (c : ρ → K) (hL : ∀ γ ∈ L, Raises lev d (E γ)) (b b' : ι)
    (hne : b' ≠ b) (hlt : lev b' < lev b + d) :
    ((L.map fun γ => (1 : Module.End K (ι →₀ K)) + c γ • E γ).prod) (Finsupp.single b 1) b' = 0 := by
  have hexp := (mem_Fil.mp (prod_expansion lev hd L E c hL b)) b' (by omega)
  have hbb : Finsupp.single b (1 : K) b' = 0 := by
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hne h.symm
  have ht : (L.map fun γ => c γ • E γ (Finsupp.single b 1)).sum ∈ Fil lev (lev b + d) :=
    xops_list_sum_mem lev _ _ L fun γ hγ => Submodule.smul_mem _ _ ((hL γ hγ).single_mem_Fil b)
  have htb := (mem_Fil.mp ht) b' hlt
  simp only [Finsupp.sub_apply, hbb, htb, sub_zero] at hexp
  exact hexp

end CFSG.RankThree.GF2n.Smith81.XOps

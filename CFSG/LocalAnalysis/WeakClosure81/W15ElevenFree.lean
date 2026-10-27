module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open Subgroup
open scoped commutatorElement
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private theorem b15_prod_eq_one {A : Subgroup G} [IsMulCommutative A]
    {p : ℕ} (hp : p.Prime) (F : ℕ → A) (hper : F p = F 0) {z : G}
    (hzN : z ∈ normalizer (A : Set G))
    (hshift : ∀ j, z * (F j : G) * z⁻¹ = (F (j + 1) : G))
    (hcz : A ⊓ centralizer ({z} : Set G) = ⊥) :
    (∏ j ∈ Finset.range p, F j) = 1 := by
  classical
  let φ : A →* A := ((MulAut.conj z).toMonoidHom.comp A.subtype).codRestrict A
    (fun x => (Subgroup.mem_normalizer_iff.mp hzN x).mp x.2)
  have hφ : ∀ x : A, ((φ x : A) : G) = z * (x : G) * z⁻¹ := fun _ => rfl
  have hφF : ∀ j, φ (F j) = F (j + 1) := by
    intro j
    apply Subtype.ext
    rw [hφ, hshift j]
  let N : A := ∏ j ∈ Finset.range p, F j
  have hNfix : φ N = N := by
    have h1 : φ N = ∏ j ∈ Finset.range p, F (j + 1) := by
      change φ (∏ j ∈ Finset.range p, F j) = ∏ j ∈ Finset.range p, F (j + 1)
      rw [map_prod φ F (Finset.range p)]
      exact Finset.prod_congr rfl (fun j _ => hφF j)
    have hpp : p = (p - 1) + 1 := by have := hp.pos; omega
    have hshift_prod : (∏ j ∈ Finset.range p, F (j + 1))
        = (∏ j ∈ Finset.range (p - 1), F (j + 1)) * F 0 := by
      conv_lhs => rw [hpp]
      rw [Finset.prod_range_succ, hpp.symm, hper]
    have hN : (∏ j ∈ Finset.range p, F j)
        = (∏ j ∈ Finset.range (p - 1), F (j + 1)) * F 0 := by
      conv_lhs => rw [hpp]
      rw [Finset.prod_range_succ']
    rw [h1, hshift_prod, ← hN]
  have hNmem : (N : G) ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hfix : z * (N : G) * z⁻¹ = (N : G) := by
      have h := congrArg (fun x : A => (x : G)) hNfix
      rwa [hφ] at h
    calc z * (N : G) = z * (N : G) * z⁻¹ * z := by group
      _ = (N : G) * z := by rw [hfix]
  have hNbot : N = 1 := by
    have hmem : (N : G) ∈ A ⊓ centralizer ({z} : Set G) := ⟨N.2, hNmem⟩
    rw [hcz, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  show N = 1
  exact hNbot

theorem inf_centralizer_le_commutator_of_inv {I : Subgroup G} (hI : IsElemAbelian 2 I)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x ι : G} (hx : x ^ p = 1)
    (hxN : x ∈ normalizer (I : Set G)) (hιN : ι ∈ normalizer (I : Set G)) (hι : ι * ι = 1)
    (hinv : ι * x * ι⁻¹ = x⁻¹) (hcx : I ⊓ centralizer ({x} : Set G) = ⊥) :
    I ⊓ centralizer ({ι} : Set G) ≤ ⁅I, zpowers ι⁆ := by
  classical
  haveI : IsMulCommutative I := hI.1
  intro i hi
  obtain ⟨hiI, hic⟩ := Subgroup.mem_inf.mp hi
  have hcomm_i : i * ι = ι * i := Subgroup.mem_centralizer_singleton_iff.mp hic
  have hmem : ∀ j : ℕ, x ^ j * i * (x ^ j)⁻¹ ∈ I := fun j =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem (normalizer (I : Set G)) hxN j) i).mp hiI
  let F : ℕ → I := fun j => ⟨x ^ j * i * (x ^ j)⁻¹, hmem j⟩
  have hF : ∀ j : ℕ, (F j : G) = x ^ j * i * (x ^ j)⁻¹ := fun _ => rfl
  have hF0 : (F 0 : G) = i := by simpa using hF 0
  have hper : F p = F 0 := by
    apply Subtype.ext
    simp [hF, hx]
  have hshift : ∀ j, x * (F j : G) * x⁻¹ = (F (j + 1) : G) := by
    intro j
    simp only [hF, pow_succ']
    group
  have hN1 : (∏ j ∈ Finset.range p, F j) = 1 :=
    b15_prod_eq_one hp F hper hxN hshift hcx
  have hp_pos : 0 < p := hp.pos
  have hpp : p = (p - 1) + 1 := by omega
  have hN_eq : (∏ j ∈ Finset.range p, F j)
      = F 0 * (∏ j ∈ Finset.range (p - 1), F (j + 1)) := by
    conv_lhs => rw [hpp]
    rw [Finset.prod_range_succ', mul_comm]
  have hF0sq : F 0 * F 0 = 1 := by
    have h := hI.2 (F 0) (F 0).2
    rw [pow_two] at h
    exact Subtype.ext h
  have hP_eq : (∏ j ∈ Finset.range (p - 1), F (j + 1)) = F 0 := by
    have h : F 0 * (∏ j ∈ Finset.range (p - 1), F (j + 1)) = 1 := by
      rw [← hN_eq, hN1]
    rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hF0sq]
  have hconj_shift : ∀ m : ℕ, m ≤ p → ι * (F m : G) * ι⁻¹ = (F (p - m) : G) := by
    intro m hm
    have hxpow : ι * x ^ m * ι⁻¹ = (x ^ m)⁻¹ := by
      rw [← conj_pow (a := ι) (b := x) (i := m), hinv, inv_pow]
    have hi : ι * i * ι⁻¹ = i := by
      rw [← hcomm_i]
      group
    have hinvpow : ι * (x ^ m)⁻¹ * ι⁻¹ = x ^ m := by
      rw [← conj_inv (a := x ^ m) (b := ι), hxpow, inv_inv]
    have hpow : (x ^ m)⁻¹ = x ^ (p - m) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, show m + (p - m) = p by omega, hx]
    have htarget : x ^ (p - m) * i * (x ^ (p - m))⁻¹ = (x ^ m)⁻¹ * i * x ^ m := by
      rw [show x ^ (p - m) = (x ^ m)⁻¹ from hpow.symm,
        show ((x ^ m)⁻¹)⁻¹ = x ^ m from inv_inv (x ^ m)]
    simp only [hF]
    calc ι * (x ^ m * i * (x ^ m)⁻¹) * ι⁻¹
        = (ι * x ^ m * ι⁻¹) * (ι * i * ι⁻¹) * (ι * (x ^ m)⁻¹ * ι⁻¹) := by group
      _ = (x ^ m)⁻¹ * i * x ^ m := by rw [hxpow, hi, hinvpow]
      _ = x ^ (p - m) * i * (x ^ (p - m))⁻¹ := htarget.symm
  have hcomm : ∀ m : ℕ, 1 ≤ m → m ≤ p - 1 →
      (F m : G) * (F (p - m) : G) = ⁅(F m : G), ι⁆ := by
    intro m _ hmp
    have hm : m ≤ p := by omega
    have hcs := hconj_shift m hm
    have hinv_m : ((F m : G))⁻¹ = (F m : G) := by
      apply inv_eq_of_mul_eq_one_right
      have h2 : (F m * F m : I) = 1 := by
        have h := hI.2 (F m) (F m).2
        rw [pow_two] at h
        exact Subtype.ext h
      simpa using congrArg (fun t : I => (t : G)) h2
    calc (F m : G) * (F (p - m) : G)
        = (F m : G) * (ι * (F m : G) * ι⁻¹) := by rw [← hcs]
      _ = (F m : G) * ι * (F m : G) * ι⁻¹ := by group
      _ = (F m : G) * ι * ((F m : G))⁻¹ * ι⁻¹ := by rw [hinv_m]
      _ = ⁅(F m : G), ι⁆ := by rw [commutatorElement_def]
  obtain ⟨n, hn⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hP_split : (∏ j ∈ Finset.range (p - 1), F (j + 1))
      = ∏ j ∈ Finset.range n, (F (j + 1) * F (p - (j + 1))) := by
    have hp_sub : p - 1 = n + n := by omega
    rw [hp_sub, Finset.prod_range_add (fun j => F (j + 1)) n n]
    have hreflect : (∏ j ∈ Finset.range n, F (n + j + 1))
        = ∏ j ∈ Finset.range n, F (p - (j + 1)) := by
      have h := Finset.prod_range_reflect (fun j => F (n + j + 1)) n
      rw [← h]
      apply Finset.prod_congr rfl
      intro j hj
      have hj' : j < n := Finset.mem_range.mp hj
      congr 1
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
  have hfactor : ∀ j ∈ Finset.range n,
      ((F (j + 1) * F (p - (j + 1)) : I) : G) ∈ ⁅I, zpowers ι⁆ := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    have h1 : 1 ≤ j + 1 := by omega
    have h2 : j + 1 ≤ p - 1 := by omega
    rw [Subgroup.coe_mul, hcomm (j + 1) h1 h2]
    exact Subgroup.commutator_mem_commutator (F (j + 1)).2 (Subgroup.mem_zpowers ι)
  have hDI : (∏ j ∈ Finset.range n, (F (j + 1) * F (p - (j + 1))) : I) ∈
      (⁅I, zpowers ι⁆ ⊓ I).subgroupOf I := by
    apply Subgroup.prod_mem
    intro j hj
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hfactor j hj, (F (j + 1) * F (p - (j + 1))).2⟩
  have hPmem : (((∏ j ∈ Finset.range n,
      (F (j + 1) * F (p - (j + 1))) : I)) : G) ∈ ⁅I, zpowers ι⁆ :=
    (Subgroup.mem_subgroupOf.mp hDI).1
  have hi_eq : i = (((∏ j ∈ Finset.range n,
      (F (j + 1) * F (p - (j + 1))) : I)) : G) := by
    calc i = (F 0 : G) := hF0.symm
      _ = ((∏ j ∈ Finset.range (p - 1), F (j + 1) : I) : G) := by rw [← hP_eq]
      _ = (((∏ j ∈ Finset.range n,
            (F (j + 1) * F (p - (j + 1))) : I)) : G) := by rw [hP_split]
  rw [hi_eq]
  exact hPmem

theorem le_commutator_of_inf_centralizer_eq_bot {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G} (hz : z ^ p = 1)
    (hzN : z ∈ normalizer (A : Set G)) (hcz : A ⊓ centralizer ({z} : Set G) = ⊥) :
    A ≤ ⁅A, zpowers z⁆ := by
  classical
  haveI : IsMulCommutative A := hA.1
  intro a ha
  let aA : A := ⟨a, ha⟩
  have hmem : ∀ j : ℕ, z ^ j * a * (z ^ j)⁻¹ ∈ A := fun j =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem (normalizer (A : Set G)) hzN j) a).mp ha
  let F : ℕ → A := fun j => ⟨z ^ j * a * (z ^ j)⁻¹, hmem j⟩
  have hF : ∀ j : ℕ, (F j : G) = z ^ j * a * (z ^ j)⁻¹ := fun _ => rfl
  have hper : F p = F 0 := by
    apply Subtype.ext
    simp [hF, hz]
  have hshift : ∀ j, z * (F j : G) * z⁻¹ = (F (j + 1) : G) := by
    intro j
    simp only [hF, pow_succ']
    group
  have hprod1 : (∏ j ∈ Finset.range p, F j) = 1 :=
    b15_prod_eq_one hp F hper hzN hshift hcz
  have hkey : (∏ j ∈ Finset.range p, aA * (F j)⁻¹) = aA := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, hprod1, inv_one, mul_one]
    rw [Finset.prod_const, Finset.card_range]
    obtain ⟨n, hn⟩ := hp.eq_two_or_odd'.resolve_left hp2
    have h2 : aA ^ 2 = 1 := by
      rw [pow_two]
      have h : (↑aA : G) * (↑aA : G) = 1 := by
        simpa [pow_two] using hA.2 aA aA.2
      exact Subtype.ext h
    calc aA ^ p = aA ^ (2 * n + 1) := by rw [hn]
      _ = aA ^ (2 * n) * aA := by rw [pow_succ]
      _ = (aA ^ 2) ^ n * aA := by rw [pow_mul]
      _ = 1 ^ n * aA := by rw [h2]
      _ = aA := by rw [one_pow, one_mul]
  have hcomm : ∀ j : ℕ, ((aA * (F j)⁻¹ : A) : G) = ⁅a, z ^ j⁆ := by
    intro j
    simp only [aA, F, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [commutatorElement_def]
    group
  have hmemD : (((∏ j ∈ Finset.range p, aA * (F j)⁻¹ : A)) : G) ∈ ⁅A, zpowers z⁆ := by
    have hDI : (∏ j ∈ Finset.range p, aA * (F j)⁻¹ : A) ∈
        (⁅A, zpowers z⁆ ⊓ A).subgroupOf A := by
      apply Subgroup.prod_mem
      intro j hj
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, (aA * (F j)⁻¹).2⟩
      rw [hcomm j]
      exact Subgroup.commutator_mem_commutator ha
        (Subgroup.pow_mem (zpowers z) (Subgroup.mem_zpowers z) j)
    exact (Subgroup.mem_subgroupOf.mp hDI).1
  rw [hkey] at hmemD
  exact hmemD

end CFSG.LocalAnalysis.WeakClosure81

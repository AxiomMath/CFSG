module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Module CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def hh (u v : Fin 4 → K) : K := hermLin K f 4 1 4 u v

@[expose] noncomputable def Aniso (u : Fin 4 → K) : Prop := hh f u u ≠ 0

@[expose] noncomputable def gram (u v : Fin 4 → K) : K :=
  hh f u u * hh f v v - hh f u v * hh f v u

theorem hh_apply (u v : Fin 4 → K) :
    hh f u v = sg K f (u 1) * v 1 + sg K f (u 2) * v 2 + sg K f (u 3) * v 3 := by
  rw [hh, hermLin, LinearMap.sum_apply, Fin.sum_univ_four]
  simp

theorem hh_add_left (u u' v : Fin 4 → K) : hh f (u + u') v = hh f u v + hh f u' v := by
  simp only [hh_apply, Pi.add_apply, map_add, add_mul]
  ring

theorem hh_add_right (u v v' : Fin 4 → K) : hh f u (v + v') = hh f u v + hh f u v' := by
  exact map_add (hermLin K f 4 1 4 u) v v'

theorem hh_smul_left (c : K) (u v : Fin 4 → K) : hh f (c • u) v = sg K f c * hh f u v := by
  simp only [hh_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem hh_smul_right (c : K) (u v : Fin 4 → K) : hh f u (c • v) = c * hh f u v := by
  exact map_smul (hermLin K f 4 1 4 u) c v

theorem hh_symm (hK : Nat.card K = (2 ^ f) ^ 2) (u v : Fin 4 → K) :
    hh f v u = sg K f (hh f u v) := by
  simp only [hh_apply, map_add, map_mul, sg_sg hK]
  ring

theorem hh_self_fixed (hK : Nat.card K = (2 ^ f) ^ 2) (v : Fin 4 → K) :
    sg K f (hh f v v) = hh f v v :=
  (hh_symm f hK v v).symm

theorem hh_of_mem_Vsub_left {u : Fin 4 → K} (hu : u ∈ Vsub (K := K) 4 1) (v : Fin 4 → K) :
    hh f u v = 0 := by
  have hu1 : u 1 = 0 := hu 1 (by decide)
  have hu2 : u 2 = 0 := hu 2 (by decide)
  have hu3 : u 3 = 0 := hu 3 (by decide)
  rw [hh_apply, hu1, hu2, hu3]
  simp

theorem hh_of_mem_Vsub_right {v : Fin 4 → K} (hv : v ∈ Vsub (K := K) 4 1) (u : Fin 4 → K) :
    hh f u v = 0 := by
  have hv1 : v 1 = 0 := hv 1 (by decide)
  have hv2 : v 2 = 0 := hv 2 (by decide)
  have hv3 : v 3 = 0 := hv 3 (by decide)
  rw [hh_apply, hv1, hv2, hv3]
  simp

theorem mem_perpB4_iff (U : Submodule K (Fin 4 → K)) (v : Fin 4 → K) :
    v ∈ perpB K f 4 1 4 U ↔ ∀ u ∈ U, hh f u v = 0 := by
  simp only [perpB, Submodule.mem_iInf, LinearMap.mem_ker, hh]

theorem Vsub_le_perpB (U : Submodule K (Fin 4 → K)) : Vsub (K := K) 4 1 ≤ perpB K f 4 1 4 U := by
  intro v hv
  rw [mem_perpB4_iff]
  intro u _
  exact hh_of_mem_Vsub_right f hv u

theorem sg_eq_pow (s : K) : sg K f s = s ^ 2 ^ f :=
  unitaryInvolution_apply K 2 f s

theorem gram_symm (u v : Fin 4 → K) : gram f u v = gram f v u := by
  simp only [gram]
  ring

theorem gram_self (u : Fin 4 → K) : gram f u u = 0 := by
  simp only [gram]
  ring

theorem gram_smul_right (c : K) (u v : Fin 4 → K) :
    gram f u (c • v) = sg K f c * c * gram f u v := by
  simp only [gram, hh_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem gram_smul_left (c : K) (u v : Fin 4 → K) :
    gram f (c • u) v = sg K f c * c * gram f u v := by
  simp only [gram, hh_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem gram_add_smul_right (u v : Fin 4 → K) (c : K) : gram f u (v + c • u) = gram f u v := by
  simp only [gram, hh_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem gram_eq_zero_of_smul {u v : Fin 4 → K} (c : K) (h : v = c • u) : gram f u v = 0 := by
  subst h
  rw [gram_smul_right, gram_self, mul_zero]

theorem hh_comb (a b : Fin 4 → K) (s : K) :
    hh f (s • a + b) (s • a + b) =
      hh f a a * s ^ (2 ^ f + 1) + hh f a b * s ^ 2 ^ f + hh f b a * s + hh f b b := by
  simp only [hh_add_left f, hh_add_right f, hh_smul_left f, hh_smul_right f, sg_eq_pow f]
  rw [pow_succ]
  ring

theorem gram_comb (c a b : Fin 4 → K) (s : K) :
    gram f c (s • a + b) =
      gram f c a * s ^ (2 ^ f + 1) +
        (hh f c c * hh f a b - hh f c b * hh f a c) * s ^ 2 ^ f +
        (hh f c c * hh f b a - hh f c a * hh f b c) * s + gram f c b := by
  simp only [gram, hh_add_left f, hh_add_right f, hh_smul_left f, hh_smul_right f, sg_eq_pow f]
  rw [pow_succ]
  ring

theorem gram_eq_zero_of_coeffs (hK : Nat.card K = (2 ^ f) ^ 2) {u a b : Fin 4 → K}
    (hu : Aniso f u) (h1 : gram f u a = 0) (h2 : gram f u b = 0)
    (h3 : hh f u u * hh f a b - hh f u b * hh f a u = 0) : gram f a b = 0 := by
  have he : hh f u u ≠ 0 := hu
  have hee : hh f u u * hh f u u ≠ 0 := mul_ne_zero he he
  have h1' : hh f u u * hh f a a = hh f u a * sg K f (hh f u a) := by
    have h := h1
    rw [gram, sub_eq_zero] at h
    rwa [hh_symm f hK u a] at h
  have h2' : hh f u u * hh f b b = hh f u b * sg K f (hh f u b) := by
    have h := h2
    rw [gram, sub_eq_zero] at h
    rwa [hh_symm f hK u b] at h
  have h3' : hh f u u * hh f a b = hh f u b * sg K f (hh f u a) := by
    have h := h3
    rwa [hh_symm f hK u a, sub_eq_zero] at h
  have h3sg : hh f u u * hh f b a = sg K f (hh f u b) * hh f u a := by
    have h := congrArg (sg K f) h3'
    simp only [map_mul, hh_self_fixed f hK u, sg_sg hK, ← hh_symm f hK a b] at h
    exact h
  have key : (hh f u u * hh f b b) * (hh f u u * hh f a a) -
      (hh f u u * hh f b a) * (hh f u u * hh f a b) = 0 := by
    rw [h1', h2', h3', h3sg]
    ring
  have hmain : hh f u u * hh f u u * gram f a b = 0 := by
    calc hh f u u * hh f u u * gram f a b
        = (hh f u u * hh f b b) * (hh f u u * hh f a a) -
            (hh f u u * hh f b a) * (hh f u u * hh f a b) := by
          rw [gram]; ring
      _ = 0 := key
  exact (mul_eq_zero.mp hmain).resolve_left hee

theorem aniso_single_one : Aniso f (Pi.single (1 : Fin 4) (1 : K)) := by
  unfold Aniso
  rw [hh_apply]
  simp [Pi.single_apply]

theorem aniso_single_two : Aniso f (Pi.single (2 : Fin 4) (1 : K)) := by
  unfold Aniso
  rw [hh_apply]
  simp [Pi.single_apply]

theorem gram_single_one_two :
    gram f (Pi.single (1 : Fin 4) (1 : K)) (Pi.single (2 : Fin 4) (1 : K)) ≠ 0 := by
  simp only [gram, hh_apply, Pi.single_apply]
  norm_num

@[expose] noncomputable def polar (x y : Fin 4 → K) : Fin 4 → K :=
  ![0, sg K f (x 2 * y 3 - x 3 * y 2), sg K f (x 3 * y 1 - x 1 * y 3),
    sg K f (x 1 * y 2 - x 2 * y 1)]

theorem polar_zero (x y : Fin 4 → K) : polar f x y 0 = 0 := by
  simp [polar]

theorem hh_polar_left (x y : Fin 4 → K) : hh f x (polar f x y) = 0 := by
  have hp1 : polar f x y 1 = sg K f (x 2 * y 3 - x 3 * y 2) := rfl
  have hp2 : polar f x y 2 = sg K f (x 3 * y 1 - x 1 * y 3) := rfl
  have hp3 : polar f x y 3 = sg K f (x 1 * y 2 - x 2 * y 1) := rfl
  rw [hh_apply, hp1, hp2, hp3, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add]
  have hzero : x 1 * (x 2 * y 3 - x 3 * y 2) + x 2 * (x 3 * y 1 - x 1 * y 3) +
      x 3 * (x 1 * y 2 - x 2 * y 1) = 0 := by ring
  rw [hzero, map_zero]

theorem hh_polar_right (x y : Fin 4 → K) : hh f y (polar f x y) = 0 := by
  have hp1 : polar f x y 1 = sg K f (x 2 * y 3 - x 3 * y 2) := rfl
  have hp2 : polar f x y 2 = sg K f (x 3 * y 1 - x 1 * y 3) := rfl
  have hp3 : polar f x y 3 = sg K f (x 1 * y 2 - x 2 * y 1) := rfl
  rw [hh_apply, hp1, hp2, hp3, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add]
  have hzero : y 1 * (x 2 * y 3 - x 3 * y 2) + y 2 * (x 3 * y 1 - x 1 * y 3) +
      y 3 * (x 1 * y 2 - x 2 * y 1) = 0 := by ring
  rw [hzero, map_zero]

theorem hh_polar_self (hK : Nat.card K = (2 ^ f) ^ 2) (x y : Fin 4 → K) :
    hh f (polar f x y) (polar f x y) = gram f x y := by
  have hp1 : polar f x y 1 = sg K f (x 2 * y 3 - x 3 * y 2) := rfl
  have hp2 : polar f x y 2 = sg K f (x 3 * y 1 - x 1 * y 3) := rfl
  have hp3 : polar f x y 3 = sg K f (x 1 * y 2 - x 2 * y 1) := rfl
  rw [hh_apply, hp1, hp2, hp3, gram, hh_apply, hh_apply, hh_apply, hh_apply]
  simp only [map_mul, map_sub, sg_sg hK]
  ring

@[expose] def pev (q : ℕ) (c : K × K × K × K) (s : K) : K :=
  c.1 * s ^ (q + 1) + c.2.1 * s ^ q + c.2.2.1 * s + c.2.2.2

theorem ncard_pev_roots_le (q : ℕ) (hq : 2 ≤ q) {c : K × K × K × K} (hc : c ≠ 0) :
    Set.ncard {s : K | pev q c s = 0} ≤ q + 1 := by
  classical
  haveI := Fintype.ofFinite K
  set P : Polynomial K :=
    Polynomial.monomial (q + 1) c.1 + Polynomial.monomial q c.2.1 +
      Polynomial.monomial 1 c.2.2.1 + Polynomial.monomial 0 c.2.2.2 with hP
  have hc1 : P.coeff (q + 1) = c.1 := by
    rw [hP, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial_of_ne (m := q + 1) (n := q) c.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := q + 1) (n := 1) c.2.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := q + 1) (n := 0) c.2.2.2 (by omega),
      Polynomial.coeff_monomial_same (q + 1) c.1]
    ring
  have hc2 : P.coeff q = c.2.1 := by
    rw [hP, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial_of_ne (m := q) (n := q + 1) c.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := q) (n := 1) c.2.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := q) (n := 0) c.2.2.2 (by omega),
      Polynomial.coeff_monomial_same q c.2.1]
    ring
  have hc3 : P.coeff 1 = c.2.2.1 := by
    rw [hP, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial_of_ne (m := 1) (n := q + 1) c.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := 1) (n := q) c.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := 1) (n := 0) c.2.2.2 (by omega),
      Polynomial.coeff_monomial_same 1 c.2.2.1]
    ring
  have hc4 : P.coeff 0 = c.2.2.2 := by
    rw [hP, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial_of_ne (m := 0) (n := q + 1) c.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := 0) (n := q) c.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := 0) (n := 1) c.2.2.1 (by omega),
      Polynomial.coeff_monomial_same 0 c.2.2.2]
    ring
  have hp : P ≠ 0 := by
    intro h0
    apply hc
    have h1 : c.1 = 0 := by rw [← hc1, h0, Polynomial.coeff_zero]
    have h2 : c.2.1 = 0 := by rw [← hc2, h0, Polynomial.coeff_zero]
    have h3 : c.2.2.1 = 0 := by rw [← hc3, h0, Polynomial.coeff_zero]
    have h4 : c.2.2.2 = 0 := by rw [← hc4, h0, Polynomial.coeff_zero]
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  have hP_eval : ∀ s : K, P.eval s = pev q c s := by
    intro s
    rw [hP]
    simp [pev, Polynomial.eval_monomial]
  have hsub : (Finset.univ.filter (fun s : K => pev q c s = 0)).val ⊆ P.roots := by
    intro s hs
    rw [Finset.mem_val, Finset.mem_filter] at hs
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def, hP_eval s]
    exact hs.2
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  have hdeg : P.natDegree ≤ q + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [hP, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_monomial_of_ne (m := m) (n := q + 1) c.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := m) (n := q) c.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := m) (n := 1) c.2.2.1 (by omega),
      Polynomial.coeff_monomial_of_ne (m := m) (n := 0) c.2.2.2 (by omega)]
    ring
  have hset : {s : K | pev q c s = 0} = ↑(Finset.univ.filter (fun s : K => pev q c s = 0)) := by
    ext s
    simp
  rw [hset, Set.ncard_coe_finset]
  exact le_trans hle hdeg

theorem exists_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {c₁ c₂ c₃ : K × K × K × K} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (h₃ : c₃ ≠ 0) :
    ∃ s : K, pev (2 ^ f) c₁ s ≠ 0 ∧ pev (2 ^ f) c₂ s ≠ 0 ∧ pev (2 ^ f) c₃ s ≠ 0 := by
  classical
  by_contra h
  rw [not_exists] at h
  set A₁ : Set K := {s : K | pev (2 ^ f) c₁ s = 0} with hA₁
  set A₂ : Set K := {s : K | pev (2 ^ f) c₂ s = 0} with hA₂
  set A₃ : Set K := {s : K | pev (2 ^ f) c₃ s = 0} with hA₃
  have hsub : (Set.univ : Set K) ⊆ A₁ ∪ A₂ ∪ A₃ := by
    intro s _
    by_contra hc
    rw [Set.mem_union, Set.mem_union, hA₁, hA₂, hA₃, Set.mem_setOf_eq, Set.mem_setOf_eq,
      Set.mem_setOf_eq] at hc
    simp only [not_or, not_not] at hc
    rcases hc with ⟨⟨h1, h2⟩, h3⟩
    exact h s ⟨h1, h2, h3⟩
  have hcard : Nat.card K ≤ A₁.ncard + A₂.ncard + A₃.ncard := by
    calc Nat.card K = (Set.univ : Set K).ncard := (Set.ncard_univ K).symm
      _ ≤ (A₁ ∪ A₂ ∪ A₃).ncard := Set.ncard_le_ncard hsub
      _ ≤ (A₁ ∪ A₂).ncard + A₃.ncard := Set.ncard_union_le (A₁ ∪ A₂) A₃
      _ ≤ (A₁.ncard + A₂.ncard) + A₃.ncard :=
          add_le_add (Set.ncard_union_le A₁ A₂) le_rfl
  have h1 : A₁.ncard ≤ 2 ^ f + 1 := ncard_pev_roots_le (K := K) (2 ^ f) (by omega) h₁
  have h2 : A₂.ncard ≤ 2 ^ f + 1 := ncard_pev_roots_le (K := K) (2 ^ f) (by omega) h₂
  have h3 : A₃.ncard ≤ 2 ^ f + 1 := ncard_pev_roots_le (K := K) (2 ^ f) (by omega) h₃
  have hbound : Nat.card K ≤ 3 * (2 ^ f + 1) := by
    calc Nat.card K ≤ A₁.ncard + A₂.ncard + A₃.ncard := hcard
      _ ≤ (2 ^ f + 1) + (2 ^ f + 1) + (2 ^ f + 1) := add_le_add (add_le_add h1 h2) h3
      _ = 3 * (2 ^ f + 1) := by ring
  rw [hK] at hbound
  nlinarith [hq]

end CFSG.ClassicalInvolution.Phan.PhanE

end

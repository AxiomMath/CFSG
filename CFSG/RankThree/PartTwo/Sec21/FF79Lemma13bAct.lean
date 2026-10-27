module

public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts13

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13b

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped IsMulCommutative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

structure Coord (B : Subgroup G) where
  e : G → (Fin 3 → ZMod 3)
  d : (Fin 3 → ZMod 3) → G
  d_mem : ∀ u, d u ∈ B
  e_d : ∀ u, e (d u) = u
  d_e : ∀ x ∈ B, d (e x) = x
  e_mul : ∀ x ∈ B, ∀ y ∈ B, e (x * y) = e x + e y

theorem exists_coord [Finite G] {B : Subgroup G} (hB : IsElemAb 3 3 B) : Nonempty (Coord B) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 ↥B := hB.1
  haveI : Finite (Additive ↥B) := inferInstanceAs (Finite ↥B)
  haveI : Module.Finite (ZMod 3) (Additive ↥B) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 3) (Additive ↥B) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive ↥B)
    have h1 : Nat.card (Additive ↥B) = 3 ^ 3 := hB.2
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  let e0 : Additive ↥B ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hrank]; simp)
  classical
  refine ⟨⟨fun x => if hx : x ∈ B then e0 (Additive.ofMul ⟨x, hx⟩) else 0,
    fun u => ((Additive.toMul (e0.symm u) : ↥B) : G), fun u => (Additive.toMul (e0.symm u)).2,
    fun u => ?_, fun x hx => ?_, fun x hx y hy => ?_⟩⟩
  · simp
  · simp [hx]
  · have hxy : x * y ∈ B := B.mul_mem hx hy
    simp only [hx, hy, hxy, dite_true]
    rw [← map_add]
    rfl

theorem conj_mem_of_nor {B : Subgroup G} {n x : G} (hn : n ∈ Nor B) (hx : x ∈ B) :
    n * x * n⁻¹ ∈ B :=
  ((Subgroup.mem_set_normalizer_iff.mp hn) x).mp hx

namespace Coord

variable {B : Subgroup G} (c : Coord B)

theorem e_one : c.e 1 = 0 := by
  have h := c.e_mul 1 B.one_mem 1 B.one_mem
  rw [mul_one] at h
  have : c.e 1 + c.e 1 = c.e 1 + 0 := by rw [add_zero, ← h]
  exact add_left_cancel this

theorem e_inv {x : G} (hx : x ∈ B) : c.e x⁻¹ = - c.e x := by
  have h := c.e_mul x⁻¹ (B.inv_mem hx) x hx
  rw [inv_mul_cancel, c.e_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem e_inj {x y : G} (hx : x ∈ B) (hy : y ∈ B) (h : c.e x = c.e y) : x = y := by
  rw [← c.d_e x hx, ← c.d_e y hy, h]

theorem e_pow {x : G} (hx : x ∈ B) (k : ℕ) : c.e (x ^ k) = k • c.e x := by
  induction k with
  | zero => simp [c.e_one]
  | succ k ih =>
    rw [pow_succ, c.e_mul _ (B.pow_mem hx k) x hx, ih, succ_nsmul]

theorem d_add (u v : Fin 3 → ZMod 3) : c.d (u + v) = c.d u * c.d v := by
  refine c.e_inj (c.d_mem _) (B.mul_mem (c.d_mem _) (c.d_mem _)) ?_
  rw [c.e_mul _ (c.d_mem _) _ (c.d_mem _), c.e_d, c.e_d, c.e_d]

theorem d_zero : c.d 0 = 1 := by
  refine c.e_inj (c.d_mem _) B.one_mem ?_
  rw [c.e_d, c.e_one]

@[expose] def fAdd (n : G) (u : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 := c.e (n * c.d u * n⁻¹)

theorem fAdd_apply {n : G} (u : Fin 3 → ZMod 3) : c.fAdd n u = c.e (n * c.d u * n⁻¹) := rfl

theorem fAdd_zero {n : G} (hn : n ∈ Nor B) : c.fAdd n 0 = 0 := by
  simp [fAdd_apply, c.d_zero, c.e_one]

theorem fAdd_add {n : G} (hn : n ∈ Nor B) (u v : Fin 3 → ZMod 3) :
    c.fAdd n (u + v) = c.fAdd n u + c.fAdd n v := by
  rw [fAdd_apply, fAdd_apply, fAdd_apply, c.d_add,
    ← c.e_mul _ (conj_mem_of_nor hn (c.d_mem u)) _ (conj_mem_of_nor hn (c.d_mem v))]
  congr 1
  group

theorem fAdd_nsmul {n : G} (hn : n ∈ Nor B) (k : ℕ) (u : Fin 3 → ZMod 3) :
    c.fAdd n (k • u) = k • c.fAdd n u := by
  induction k with
  | zero => simpa using c.fAdd_zero hn
  | succ k ih => rw [succ_nsmul, c.fAdd_add hn, ih, succ_nsmul]

theorem fAdd_smul {n : G} (hn : n ∈ Nor B) (a : ZMod 3) (u : Fin 3 → ZMod 3) :
    c.fAdd n (a • u) = a • c.fAdd n u := by
  have h : a • u = a.val • u := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have h' : a • c.fAdd n u = a.val • c.fAdd n u := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h, h', c.fAdd_nsmul hn]

theorem fAdd_sum {n : G} (hn : n ∈ Nor B) {ι : Type*} (s : Finset ι)
    (w : ι → Fin 3 → ZMod 3) : c.fAdd n (∑ i ∈ s, w i) = ∑ i ∈ s, c.fAdd n (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c.fAdd_zero hn
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, c.fAdd_add hn, ih]

@[expose] def mat (n : G) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  Matrix.of fun i => c.fAdd n (Pi.single i 1)

theorem vecMul_mat {n : G} (hn : n ∈ Nor B) (u : Fin 3 → ZMod 3) :
    Matrix.vecMul u (c.mat n) = c.fAdd n u := by
  classical
  rw [Matrix.vecMul_eq_sum]
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin 3 → ZMod 3) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hu, c.fAdd_sum hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [c.fAdd_smul hn]
  rfl

theorem fAdd_comp {n m : G} (hn : n ∈ Nor B) (u : Fin 3 → ZMod 3) :
    c.fAdd m (c.fAdd n u) = c.fAdd (m * n) u := by
  rw [fAdd_apply, fAdd_apply, fAdd_apply, c.d_e _ (conj_mem_of_nor hn (c.d_mem u))]
  congr 1
  group

theorem fAdd_one (u : Fin 3 → ZMod 3) : c.fAdd 1 u = u := by
  rw [fAdd_apply]
  simp [c.e_d]

theorem exists_gl {n : G} (hn : n ∈ Nor B) :
    ∃ g : GL (Fin 3) (ZMod 3), ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹) := by
  have hn' : n⁻¹ ∈ Nor B := inv_mem hn
  have h1 : c.mat n * c.mat n⁻¹ = 1 := by
    apply Matrix.vecMul_injective
    funext u
    simp only [← Matrix.vecMul_vecMul, c.vecMul_mat hn, c.vecMul_mat hn', Matrix.vecMul_one]
    rw [c.fAdd_comp hn, inv_mul_cancel, c.fAdd_one]
  have h2 : c.mat n⁻¹ * c.mat n = 1 := by
    apply Matrix.vecMul_injective
    funext u
    simp only [← Matrix.vecMul_vecMul, c.vecMul_mat hn, c.vecMul_mat hn', Matrix.vecMul_one]
    rw [c.fAdd_comp hn', mul_inv_cancel, c.fAdd_one]
  refine ⟨⟨c.mat n, c.mat n⁻¹, h1, h2⟩, fun x hx => ?_⟩
  show Matrix.vecMul (c.e x) (c.mat n) = _
  rw [c.vecMul_mat hn, fAdd_apply, c.d_e x hx]

theorem act33_mul (g h : GL (Fin 3) (ZMod 3)) (u : Fin 3 → ZMod 3) :
    act33 (g * h) u = act33 h (act33 g u) := by
  simp [act33, Matrix.vecMul_vecMul]

theorem act33_inv_act33 (g : GL (Fin 3) (ZMod 3)) (u : Fin 3 → ZMod 3) :
    act33 g⁻¹ (act33 g u) = u := by
  rw [← act33_mul, mul_inv_cancel]
  simp [act33]

theorem gl_ext {g h : GL (Fin 3) (ZMod 3)} (H : ∀ u, act33 g u = act33 h u) : g = h := by
  apply Units.ext
  apply Matrix.vecMul_injective
  funext u
  exact H u

@[expose] def X : Subgroup (GL (Fin 3) (ZMod 3)) where
  carrier := {g | ∃ n ∈ Nor B, ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹)}
  one_mem' := ⟨1, one_mem _, fun x hx => by simp [act33]⟩
  mul_mem' := by
    rintro g h ⟨n, hn, hgn⟩ ⟨m, hm, hhm⟩
    refine ⟨m * n, mul_mem hm hn, fun x hx => ?_⟩
    rw [act33_mul, hgn x hx, hhm _ (conj_mem_of_nor hn hx)]
    congr 1
    group
  inv_mem' := by
    rintro g ⟨n, hn, hgn⟩
    refine ⟨n⁻¹, inv_mem hn, fun x hx => ?_⟩
    have h1 : act33 g (c.e (n⁻¹ * x * n⁻¹⁻¹)) = c.e x := by
      rw [hgn _ (conj_mem_of_nor (inv_mem hn) hx)]
      congr 1
      group
    rw [← h1, act33_inv_act33]

theorem exists_mem_X {n : G} (hn : n ∈ Nor B) :
    ∃ g ∈ c.X, ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹) := by
  obtain ⟨g, hg⟩ := c.exists_gl hn
  exact ⟨g, ⟨n, hn, hg⟩, hg⟩

theorem act_eq {g : GL (Fin 3) (ZMod 3)} {n : G} (hg : ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹))
    (u : Fin 3 → ZMod 3) : act33 g u = c.e (n * c.d u * n⁻¹) := by
  have := hg (c.d u) (c.d_mem u)
  rwa [c.e_d] at this

theorem e_smul_pow {x : G} (hx : x ∈ B) (a : ZMod 3) : c.e (x ^ a.val) = a • c.e x := by
  rw [c.e_pow hx, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem d_smul (u : Fin 3 → ZMod 3) (a : ZMod 3) : c.d (a • u) = c.d u ^ a.val := by
  refine c.e_inj (c.d_mem _) (B.pow_mem (c.d_mem u) _) ?_
  rw [c.e_d, c.e_smul_pow (c.d_mem u), c.e_d]

@[expose] def sub (H : Subgroup G) : Submodule (ZMod 3) (Fin 3 → ZMod 3) where
  carrier := {u | c.d u ∈ H}
  add_mem' := fun {u v} hu hv => by
    simp only [Set.mem_setOf_eq, c.d_add] at hu hv ⊢
    exact H.mul_mem hu hv
  zero_mem' := by simp [c.d_zero]
  smul_mem' := fun a u hu => by
    simp only [Set.mem_setOf_eq, c.d_smul] at hu ⊢
    exact H.pow_mem hu _

theorem natCard_sub {H : Subgroup G} (hH : H ≤ B) : Nat.card (c.sub H) = Nat.card H := by
  refine Nat.card_congr
    ⟨fun u => ⟨c.d u, u.2⟩, fun x => ⟨c.e x, ?_⟩, fun u => ?_, fun x => ?_⟩
  · show c.d (c.e x) ∈ H
    rw [c.d_e x (hH x.2)]
    exact x.2
  · exact Subtype.ext (c.e_d u)
  · exact Subtype.ext (c.d_e x (hH x.2))

theorem finrank_sub {H : Subgroup G} (hH : H ≤ B) {k : ℕ} (hc : Nat.card H = 3 ^ k) :
    Module.finrank (ZMod 3) (c.sub H) = k := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := c.sub H)
  rw [c.natCard_sub hH, hc, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm

theorem exists_basis_sub {H : Subgroup G} (hH : H ≤ B) (hc : Nat.card H = 9) :
    ∃ c₁ ∈ H, ∃ c₂ ∈ H, LinearIndependent (ZMod 3) ![c.e c₁, c.e c₂] ∧
      ∀ u, u ∈ Submodule.span (ZMod 3) {c.e c₁, c.e c₂} ↔ c.d u ∈ H := by
  have hfr : Module.finrank (ZMod 3) (c.sub H) = 2 := c.finrank_sub hH (k := 2) (by simpa using hc)
  let bs := Module.finBasisOfFinrankEq (ZMod 3) (c.sub H) hfr
  let w : Fin 2 → (Fin 3 → ZMod 3) := fun i => (bs i : Fin 3 → ZMod 3)
  have hli : LinearIndependent (ZMod 3) w :=
    bs.linearIndependent.map' (c.sub H).subtype (Submodule.ker_subtype _)
  have hw : ∀ i, c.d (w i) ∈ H := fun i => (bs i).2
  have hvec : (![c.e (c.d (w 0)), c.e (c.d (w 1))] : Fin 2 → Fin 3 → ZMod 3) = w := by
    ext i : 1
    fin_cases i <;> simp [c.e_d]
  have hset : ({c.e (c.d (w 0)), c.e (c.d (w 1))} : Set (Fin 3 → ZMod 3)) = Set.range w := by
    rw [c.e_d, c.e_d]
    ext u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i
      exacts [Or.inl rfl, Or.inr rfl]
  refine ⟨c.d (w 0), hw 0, c.d (w 1), hw 1, by rw [hvec]; exact hli, fun u => ?_⟩
  rw [hset]
  have hle : Submodule.span (ZMod 3) (Set.range w) ≤ c.sub H := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (bs i).2
  have hspan : Submodule.span (ZMod 3) (Set.range w) = c.sub H := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [finrank_span_eq_card hli, hfr]
    simp
  rw [hspan]
  rfl

theorem closure_eq {x₀ x₁ x₂ : G} (h0 : x₀ ∈ B) (h1 : x₁ ∈ B) (h2 : x₂ ∈ B)
    (hli : LinearIndependent (ZMod 3) ![c.e x₀, c.e x₁, c.e x₂]) :
    B = Subgroup.closure {x₀, x₁, x₂} := by
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hle : Subgroup.closure ({x₀, x₁, x₂} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  refine le_antisymm (fun x hx => ?_) hle
  have hmem : c.e x ∈ Submodule.span (ZMod 3) (Set.range ![c.e x₀, c.e x₁, c.e x₂]) := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Fin.sum_univ_three] at ha
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at ha
  have hcl : x₀ ^ (a 0).val * x₁ ^ (a 1).val * x₂ ^ (a 2).val ∈ Subgroup.closure {x₀, x₁, x₂} := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure
      (by simp)) _) (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have heq : x = x₀ ^ (a 0).val * x₁ ^ (a 1).val * x₂ ^ (a 2).val := by
    refine c.e_inj hx (B.mul_mem (B.mul_mem (B.pow_mem h0 _) (B.pow_mem h1 _)) (B.pow_mem h2 _))
      ?_
    rw [c.e_mul _ (B.mul_mem (B.pow_mem h0 _) (B.pow_mem h1 _)) _ (B.pow_mem h2 _),
      c.e_mul _ (B.pow_mem h0 _) _ (B.pow_mem h1 _), c.e_smul_pow h0, c.e_smul_pow h1,
      c.e_smul_pow h2, ← ha]
  rw [heq]
  exact hcl

theorem act_iff {g : GL (Fin 3) (ZMod 3)} {n : G}
    (hg : ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹)) (hn : n ∈ Nor B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) : act33 g (c.e x) = c.e y ↔ n * x * n⁻¹ = y := by
  rw [hg x hx]
  exact ⟨fun h => c.e_inj (conj_mem_of_nor hn hx) hy h, fun h => by rw [h]⟩

theorem act_neg_iff {g : GL (Fin 3) (ZMod 3)} {n : G}
    (hg : ∀ x ∈ B, act33 g (c.e x) = c.e (n * x * n⁻¹)) (hn : n ∈ Nor B) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) : act33 g (c.e x) = -c.e y ↔ n * x * n⁻¹ = y⁻¹ := by
  rw [← c.e_inv hy]
  exact c.act_iff hg hn hx (B.inv_mem hy)

end Coord

end CFSG.RankThree.PartTwo.Sec21.FF79.L13b

module

public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped commutatorElement Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem left_mem_pair (i j : Fin τ.rank) : i ∈ ({i, j} : Set (Fin τ.rank)) :=
  Set.mem_insert i {j}

theorem right_mem_pair (i j : Fin τ.rank) : j ∈ ({i, j} : Set (Fin τ.rank)) :=
  Set.mem_insert_of_mem i (Set.mem_singleton j)

@[expose] def qx
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    subsystemGroup τ K J :=
  ⟨xUnit τ K k c, xUnit_mem_subsystemGroup hk c⟩

@[expose] def qy
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    subsystemGroup τ K J :=
  ⟨yUnit τ K k c, yUnit_mem_subsystemGroup hk c⟩

@[simp]
theorem coe_qx
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    (qx hk c : ModGL τ K) = xUnit τ K k c :=
  rfl

@[simp]
theorem coe_qy
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    (qy hk c : ModGL τ K) = yUnit τ K k c :=
  rfl

theorem closure_gen_eq_top
    (J : Set (Fin τ.rank)) :
    Subgroup.closure ((Subtype.val : subsystemGroup τ K J → ModGL τ K) ⁻¹'
      {g | ∃ i ∈ J, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c}) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem ext_subsystemGroup
    {G : Type*} [Group G] {J : Set (Fin τ.rank)}
    {f g : subsystemGroup τ K J →* G}
    (hx : ∀ k (hk : k ∈ J) (c : K), f (qx hk c) = g (qx hk c))
    (hy : ∀ k (hk : k ∈ J) (c : K), f (qy hk c) = g (qy hk c)) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense (closure_gen_eq_top J) fun x hxs => ?_
  obtain ⟨k, hk, c, hx' | hy'⟩ := hxs
  · have e : x = qx hk c := Subtype.ext hx'
    rw [e]
    exact hx k hk c
  · have e : x = qy hk c := Subtype.ext hy'
    rw [e]
    exact hy k hk c

abbrev t01 (c : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c

abbrev t10 (c : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c

abbrev t12 (c : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c

abbrev t21 (c : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c

variable (K) in
@[expose] def IsElemRep
    (i j : Fin τ.rank)
    (r : subsystemGroup τ K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K) : Prop :=
  ∀ c : K, r (qx (left_mem_pair i j) c) = t01 c ∧ r (qy (left_mem_pair i j) c) = t10 c ∧
    r (qx (right_mem_pair i j) c) = t12 c ∧ r (qy (right_mem_pair i j) c) = t21 c

namespace IsElemRep

variable {i j : Fin τ.rank}
  {r : subsystemGroup τ K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K}

theorem ext (hr : IsElemRep K i j r)
    {r' : subsystemGroup τ K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K}
    (hr' : IsElemRep K i j r') : r = r' := by
  refine ext_subsystemGroup (fun k hk c => ?_) (fun k hk c => ?_)
  · rcases hk with rfl | hk
    · rw [(hr c).1, (hr' c).1]
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      rw [(hr c).2.2.1, (hr' c).2.2.1]
  · rcases hk with rfl | hk
    · rw [(hr c).2.1, (hr' c).2.1]
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      rw [(hr c).2.2.2, (hr' c).2.2.2]

theorem surjective
    (hr : IsElemRep K i j r) : Function.Surjective r := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  have h01 : ∀ c, t01 c ∈ r.range := fun c => ⟨_, (hr c).1⟩
  have h10 : ∀ c, t10 c ∈ r.range := fun c => ⟨_, (hr c).2.1⟩
  have h12 : ∀ c, t12 c ∈ r.range := fun c => ⟨_, (hr c).2.2.1⟩
  have h21 : ∀ c, t21 c ∈ r.range := fun c => ⟨_, (hr c).2.2.2⟩
  have hcomm : ∀ {x y : Matrix.SpecialLinearGroup (Fin 3) K}, x ∈ r.range → y ∈ r.range →
      ⁅x, y⁆ ∈ r.range := fun hx hy => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have h02 : ∀ c : K, Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈
      r.range := fun c => by
    rw [← mul_one c, ← Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)]
    exact hcomm (h01 c) (h12 1)
  have h20 : ∀ c : K, Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈
      r.range := fun c => by
    rw [← mul_one c, ← Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)]
    exact hcomm (h21 c) (h10 1)
  rintro _ ⟨a, b, hab, c, rfl⟩
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hab
  · exact h12 c
  · exact h20 c
  · exact h21 c
  · exact absurd rfl hab

end IsElemRep

theorem torusElt_eq_prod
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (t : Kˣ) :
    (⟨torusElt τ K k t, subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus hk t)⟩ :
      subsystemGroup τ K J) =
      qx hk (t : K) * qy hk (-(t : K)⁻¹) * qx hk (t : K) * (qx hk (-1) * qy hk 1 * qx hk (-1)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, qx, qy]
  rw [torusElt, CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul,
    CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  simp [Units.val_inv_eq_inv_val]

theorem weylElement_mul_weylElement_eq_diagonal {a b : Fin 3} (hab : a ≠ b) {t : K} (ht : t ≠ 0) :
    (1 + single a b t : Matrix (Fin 3) (Fin 3) K) * (1 + single b a (-t⁻¹)) *
        (1 + single a b t) * ((1 + single a b (-1)) * (1 + single b a 1) * (1 + single a b (-1))) =
      diagonal fun k => if k = a then t else if k = b then t⁻¹ else 1 := by
  rw [(CFSG.LinearGroups.elementary_diagonal_factorization hab ht).2.2.2.1,
    CFSG.LinearGroups.weylElement, CFSG.LinearGroups.weylElement, inv_neg, inv_one, neg_neg]

variable {i j : Fin τ.rank}
  {r : subsystemGroup τ K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K}

theorem torusElt_pair_mem
    (i j : Fin τ.rank) (t u : Kˣ) :
    torusElt τ K i t * torusElt τ K j u ∈ subsystemGroup τ K {i, j} :=
  mul_mem (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (left_mem_pair i j) t))
    (subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (right_mem_pair i j) u))

theorem IsElemRep.torus
    (hr : IsElemRep K i j r) (t u : Kˣ) :
    ((r ⟨torusElt τ K i t * torusElt τ K j u, torusElt_pair_mem i j t u⟩ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(t : K), (t : K)⁻¹ * u, (u : K)⁻¹] := by
  have e : (⟨torusElt τ K i t * torusElt τ K j u, torusElt_pair_mem i j t u⟩ :
      subsystemGroup τ K {i, j}) =
      ⟨torusElt τ K i t, subsystemTorus_le_subsystemGroup
        (torusElt_mem_subsystemTorus (left_mem_pair i j) t)⟩ *
      ⟨torusElt τ K j u, subsystemTorus_le_subsystemGroup
        (torusElt_mem_subsystemTorus (right_mem_pair i j) u)⟩ := rfl
  rw [e, map_mul, torusElt_eq_prod (left_mem_pair i j), torusElt_eq_prod (right_mem_pair i j)]
  simp only [map_mul, (hr _).1, (hr _).2.1, (hr _).2.2.1, (hr _).2.2.2,
    Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  rw [weylElement_mul_weylElement_eq_diagonal (show (0 : Fin 3) ≠ 1 by decide) t.ne_zero,
    weylElement_mul_weylElement_eq_diagonal (show (1 : Fin 3) ≠ 2 by decide) u.ne_zero,
    diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp [mul_comm]

theorem qx_inv
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    (qx hk c)⁻¹ = qx hk (-c) :=
  Subtype.ext (Units.ext ((coe_xUnit_inv k c).trans (coe_xUnit k (-c)).symm))

theorem qy_inv
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) (c : K) :
    (qy hk c)⁻¹ = qy hk (-c) :=
  Subtype.ext (Units.ext ((coe_yUnit_inv k c).trans (coe_yUnit k (-c)).symm))

theorem weylElt_one_eq_prod
    {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J) :
    (⟨weylElt τ K k 1, weylElt_mem_subsystemGroup hk 1⟩ : subsystemGroup τ K J) =
      qx hk 1 * qy hk (-1) * qx hk 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, qx, qy]
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
  simp

theorem weylElement_conj_single (c : K) :
    (1 + single 0 1 1 : Matrix (Fin 3) (Fin 3) K) * (1 + single 1 0 (-1)) * (1 + single 0 1 1) *
        (1 + single 1 2 c) * ((1 + single 0 1 (-1)) * (1 + single 1 0 1) * (1 + single 0 1 (-1))) =
      1 + single 0 2 c := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.single_apply]

theorem IsElemRep.injective
    (hr : IsElemRep K i j r) {α : Fin 3 → Fin τ.rank → ℤ}
    (hα : Function.Injective α) (hrange : Set.range α = parabolicPosRoots τ {i, j})
    (h0 : α 0 = Pi.single i 1) (h1 : α 1 = Pi.single j 1)
    (h2 : α 2 = reflect τ i (Pi.single j 1))
    (hB : ∀ g : subsystemGroup τ K {i, j}, r g = 1 →
      (g : ModGL τ K) ∈ subsystemBorel τ K {i, j}) : Function.Injective r := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hb : (g : ModGL τ K) ∈ (subsystemTorus τ K {i, j} : Set (ModGL τ K)) *
      (parabolicLeviUnipotent τ K {i, j} : Set (ModGL τ K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := τ) (K := K) (A := {i, j})) _).mp (hB g hg)
  obtain ⟨t', ht', u', hu', htu⟩ := hb
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_pair.1 ht'
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) α hα hrange).surjOn hu'
  obtain ⟨ε, hε, hconj⟩ := weylElt_mul_pinnedX_mul_inv K i (isRoot_single τ j)
  have hli := left_mem_pair i j
  have hrj := right_mem_pair i j
  set N : subsystemGroup τ K {i, j} := ⟨weylElt τ K i 1, weylElt_mem_subsystemGroup hli 1⟩
    with hNdef
  have hNe : N = qx hli 1 * qy hli (-1) * qx hli 1 := weylElt_one_eq_prod hli
  have hNinv : N⁻¹ = qx hli (-1) * qy hli 1 * qx hli (-1) := by
    rw [hNe, _root_.mul_inv_rev, _root_.mul_inv_rev, qx_inv, qy_inv, neg_neg, mul_assoc]
  have hX2 : pinnedX τ K (α 2) (x 2) =
      weylElt τ K i 1 * xUnit τ K j (ε * x 2) * (weylElt τ K i 1)⁻¹ := by
    have e := hconj (ε * x 2)
    rw [pinnedX_single, ← mul_assoc, hε, one_mul] at e
    rw [h2, ← e]
  have hgprod : g = ⟨torusElt τ K i a * torusElt τ K j b, torusElt_pair_mem i j a b⟩ *
      (qx hli (x 0) * (qx hrj (x 1) * (N * qx hrj (ε * x 2) * N⁻¹))) := by
    apply Subtype.ext
    rw [← htu]
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_qx, hNdef]
    have e2 : (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = 2 := rfl
    have e1 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := rfl
    rw [e2, e1, hX2, h0, h1, pinnedX_single, pinnedX_single]
  have hM := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hg
  simp only [hgprod, map_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one] at hM
  rw [hr.torus, hNinv, hNe] at hM
  simp only [map_mul, (hr _).1, (hr _).2.1, (hr _).2.2.1, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.LinearGroups.coe_transvection] at hM
  have hM' : diagonal ![(a : K), (a : K)⁻¹ * b, (b : K)⁻¹] *
      ((1 + single 0 1 (x 0)) * ((1 + single 1 2 (x 1)) * (1 + single 0 2 (ε * x 2)))) = 1 := by
    rw [← weylElement_conj_single]
    exact hM
  have e := fun p q => congrFun (congrFun hM' p) q
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e01 := e 0 1
  have e12 := e 1 2
  have e02 := e 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.single_apply,
    Matrix.diagonal_apply] at e00 e11 e22 e01 e12 e02
  have hε0 : ε ≠ 0 := fun h => by
    rw [h, zero_mul] at hε
    exact zero_ne_one hε
  have hx2 : x 2 = 0 := by
    rw [e01, zero_mul, add_zero] at e02
    exact (mul_eq_zero.1 e02).resolve_left hε0
  have hx : x = 0 := by
    funext m
    fin_cases m
    exacts [e01, e12, hx2]
  subst e00 e22 hx
  apply Subtype.ext
  rw [← htu]
  simp [torusElt_one, pinnedX_zero]

section FieldMaps

variable {L : Type} [Field L]

@[expose] def baseChangeQ
    (σ : K →+* L) (J : Set (Fin τ.rank)) :
    subsystemGroup τ K J →* subsystemGroup τ L J :=
  ((baseChangeGL σ).comp (subsystemGroup τ K J).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_subsystemGroup σ g.2

theorem baseChangeQ_qx
    (σ : K →+* L) {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J)
    (c : K) : baseChangeQ σ J (qx hk c) = qx hk (σ c) :=
  Subtype.ext (baseChangeGL_xUnit σ k c)

theorem baseChangeQ_qy
    (σ : K →+* L) {J : Set (Fin τ.rank)} {k : Fin τ.rank} (hk : k ∈ J)
    (c : K) : baseChangeQ σ J (qy hk c) = qy hk (σ c) :=
  Subtype.ext (baseChangeGL_yUnit σ k c)

theorem IsElemRep.map
    (σ : K →+* L)
    {rK : subsystemGroup τ K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K}
    {rL : subsystemGroup τ L {i, j} →* Matrix.SpecialLinearGroup (Fin 3) L}
    (hK : IsElemRep K i j rK) (hL : IsElemRep L i j rL) (g : subsystemGroup τ K {i, j}) :
    rL (baseChangeQ σ {i, j} g) = Matrix.SpecialLinearGroup.map σ (rK g) := by
  have h : rL.comp (baseChangeQ σ {i, j}) = (Matrix.SpecialLinearGroup.map σ).comp rK := by
    refine ext_subsystemGroup (fun k hk c => ?_) (fun k hk c => ?_)
    · simp only [MonoidHom.comp_apply, baseChangeQ_qx]
      rcases hk with rfl | hk
      · rw [(hL _).1, (hK _).1, Matrix.SpecialLinearGroup.map_transvection]
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        rw [(hL _).2.2.1, (hK _).2.2.1, Matrix.SpecialLinearGroup.map_transvection]
    · simp only [MonoidHom.comp_apply, baseChangeQ_qy]
      rcases hk with rfl | hk
      · rw [(hL _).2.1, (hK _).2.1, Matrix.SpecialLinearGroup.map_transvection]
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        rw [(hL _).2.2.2, (hK _).2.2.2, Matrix.SpecialLinearGroup.map_transvection]
  exact DFunLike.congr_fun h g

end FieldMaps

theorem diagonal_mul_one_add_single {d : Fin 3 → K} (p q : Fin 3) (c : K) :
    diagonal d * (1 + single p q c) = diagonal d + single p q (d p * c) := by
  ext a b
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_mul,
    Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · rw [h.1]
  · rw [mul_zero]

theorem one_add_single_mul_diagonal {d : Fin 3 → K} (p q : Fin 3) (c : K) :
    (1 + single p q c) * diagonal d = diagonal d + single p q (c * d q) := by
  ext a b
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · rw [h.2]
  · rw [zero_mul]

theorem IsElemRep.conj (hr : IsElemRep K i j r) {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {a b : K}
    (ha : (h : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single i 1)) =
      a • rootVec τ K (Pi.single i 1))
    (hb : (h : Module.End K (RootModule τ K)) (rootVec τ K (Pi.single j 1)) =
      b • rootVec τ K (Pi.single j 1))
    (g : ModGL τ K) (hg : g ∈ subsystemGroup τ K {i, j}) :
    ∃ hm : h * g * h⁻¹ ∈ subsystemGroup τ K {i, j},
      diagonal ![a * b, b, 1] * ((r ⟨g, hg⟩ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      ((r ⟨h * g * h⁻¹, hm⟩ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![a * b, b, 1] := by
  obtain ⟨ha0, hxa, hya⟩ := conj_xUnit_of_apply_single hh ha
  obtain ⟨hb0, hxb, hyb⟩ := conj_xUnit_of_apply_single hh hb
  have hli := left_mem_pair i j
  have hrj := right_mem_pair i j
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · rcases hk with rfl | hk
      · have hm : h * xUnit τ K k c * h⁻¹ ∈ subsystemGroup τ K {k, j} := by
          rw [hxa]
          exact xUnit_mem_subsystemGroup hli _
        refine ⟨hm, ?_⟩
        have e0 : (⟨xUnit τ K k c, _⟩ : subsystemGroup τ K {k, j}) = qx hli c := rfl
        have e1 : (⟨h * xUnit τ K k c * h⁻¹, hm⟩ : subsystemGroup τ K {k, j}) =
            qx hli (a * c) := Subtype.ext (hxa c)
        rw [e0, e1, (hr _).1, (hr _).1, CFSG.LinearGroups.coe_transvection,
          CFSG.LinearGroups.coe_transvection, diagonal_mul_one_add_single,
          one_add_single_mul_diagonal]
        congr 2
        rw [show (![a * b, b, 1] : Fin 3 → K) 0 = a * b from rfl,
          show (![a * b, b, 1] : Fin 3 → K) 1 = b from rfl]
        ring
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        have hm : h * xUnit τ K k c * h⁻¹ ∈ subsystemGroup τ K {i, k} := by
          rw [hxb]
          exact xUnit_mem_subsystemGroup hrj _
        refine ⟨hm, ?_⟩
        have e0 : (⟨xUnit τ K k c, _⟩ : subsystemGroup τ K {i, k}) = qx hrj c := rfl
        have e1 : (⟨h * xUnit τ K k c * h⁻¹, hm⟩ : subsystemGroup τ K {i, k}) =
            qx hrj (b * c) := Subtype.ext (hxb c)
        rw [e0, e1, (hr _).2.2.1, (hr _).2.2.1, CFSG.LinearGroups.coe_transvection,
          CFSG.LinearGroups.coe_transvection, diagonal_mul_one_add_single,
          one_add_single_mul_diagonal]
        congr 2
        rw [show (![a * b, b, 1] : Fin 3 → K) 1 = b from rfl,
          show (![a * b, b, 1] : Fin 3 → K) 2 = 1 from rfl]
        ring
    · rcases hk with rfl | hk
      · have hm : h * yUnit τ K k c * h⁻¹ ∈ subsystemGroup τ K {k, j} := by
          rw [hya]
          exact yUnit_mem_subsystemGroup hli _
        refine ⟨hm, ?_⟩
        have e0 : (⟨yUnit τ K k c, _⟩ : subsystemGroup τ K {k, j}) = qy hli c := rfl
        have e1 : (⟨h * yUnit τ K k c * h⁻¹, hm⟩ : subsystemGroup τ K {k, j}) =
            qy hli (a⁻¹ * c) := Subtype.ext (hya c)
        rw [e0, e1, (hr _).2.1, (hr _).2.1, CFSG.LinearGroups.coe_transvection,
          CFSG.LinearGroups.coe_transvection, diagonal_mul_one_add_single,
          one_add_single_mul_diagonal]
        congr 2
        rw [show (![a * b, b, 1] : Fin 3 → K) 0 = a * b from rfl,
          show (![a * b, b, 1] : Fin 3 → K) 1 = b from rfl]
        field_simp
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        have hm : h * yUnit τ K k c * h⁻¹ ∈ subsystemGroup τ K {i, k} := by
          rw [hyb]
          exact yUnit_mem_subsystemGroup hrj _
        refine ⟨hm, ?_⟩
        have e0 : (⟨yUnit τ K k c, _⟩ : subsystemGroup τ K {i, k}) = qy hrj c := rfl
        have e1 : (⟨h * yUnit τ K k c * h⁻¹, hm⟩ : subsystemGroup τ K {i, k}) =
            qy hrj (b⁻¹ * c) := Subtype.ext (hyb c)
        rw [e0, e1, (hr _).2.2.2, (hr _).2.2.2, CFSG.LinearGroups.coe_transvection,
          CFSG.LinearGroups.coe_transvection, diagonal_mul_one_add_single,
          one_add_single_mul_diagonal]
        congr 2
        rw [show (![a * b, b, 1] : Fin 3 → K) 1 = b from rfl,
          show (![a * b, b, 1] : Fin 3 → K) 2 = 1 from rfl]
        field_simp
  | one =>
    have hm : h * 1 * h⁻¹ ∈ subsystemGroup τ K {i, j} := by
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    refine ⟨hm, ?_⟩
    have e0 : (⟨1, one_mem _⟩ : subsystemGroup τ K {i, j}) = 1 := rfl
    have e1 : (⟨h * 1 * h⁻¹, hm⟩ : subsystemGroup τ K {i, j}) = 1 := Subtype.ext (by
      show h * 1 * h⁻¹ = 1
      group)
    rw [e0, e1, map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul]
  | mul x y hx hy ihx ihy =>
    obtain ⟨hmx, ex⟩ := ihx
    obtain ⟨hmy, ey⟩ := ihy
    have hm : h * (x * y) * h⁻¹ ∈ subsystemGroup τ K {i, j} := by
      rw [show h * (x * y) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) by group]
      exact mul_mem hmx hmy
    refine ⟨hm, ?_⟩
    have e0 : (⟨x * y, mul_mem hx hy⟩ : subsystemGroup τ K {i, j}) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    have e1 : (⟨h * (x * y) * h⁻¹, hm⟩ : subsystemGroup τ K {i, j}) =
        ⟨h * x * h⁻¹, hmx⟩ * ⟨h * y * h⁻¹, hmy⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group)
    rw [e0, e1, map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ex, Matrix.mul_assoc, ey,
      Matrix.mul_assoc]
  | inv x hx ihx =>
    obtain ⟨hmx, ex⟩ := ihx
    have hm : h * x⁻¹ * h⁻¹ ∈ subsystemGroup τ K {i, j} := by
      rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
      exact inv_mem hmx
    refine ⟨hm, ?_⟩
    have e0 : (⟨x⁻¹, inv_mem hx⟩ : subsystemGroup τ K {i, j}) = (⟨x, hx⟩)⁻¹ := rfl
    have e1 : (⟨h * x⁻¹ * h⁻¹, hm⟩ : subsystemGroup τ K {i, j}) = (⟨h * x * h⁻¹, hmx⟩)⁻¹ :=
      Subtype.ext (by
        simp only [Subgroup.coe_inv]
        group)
    set M := r ⟨x, hx⟩
    set M' := r ⟨h * x * h⁻¹, hmx⟩
    have hMM : ((M : Matrix (Fin 3) (Fin 3) K)) * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hMM' : ((M'⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (M' : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [e0, e1, map_inv, map_inv]
    calc diagonal ![a * b, b, 1] * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
        ((M'⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M' *
          (diagonal ![a * b, b, 1] * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)) := by rw [hMM', Matrix.one_mul]
      _ = ((M'⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (diagonal ![a * b, b, 1] * M) * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) := by rw [ex]; simp only [Matrix.mul_assoc]
      _ = ((M'⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          diagonal ![a * b, b, 1] := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hMM, Matrix.mul_one]

end CFSG.RankThree.Chevalley.SteinbergBN

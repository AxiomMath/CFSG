module

public import CFSG.RankThree.E6.NativeA3SL4
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement Pointwise

theorem support13_subset : support13 ⊆ support134 := by
  intro i hi
  rcases (mem_support13 i).1 hi with rfl | rfl
  · exact (mem_support134 _).2 (Or.inl rfl)
  · exact (mem_support134 _).2 (Or.inr (Or.inl rfl))

theorem e6Index_0_mem_support13 : e6Index 0 ∈ support13 := (mem_support13 _).2 (Or.inl rfl)
theorem e6Index_2_mem_support13 : e6Index 2 ∈ support13 := (mem_support13 _).2 (Or.inr rfl)
theorem e6Index_4_mem_support56 : e6Index 4 ∈ support56 := (mem_support56 _).2 (Or.inl rfl)
theorem e6Index_5_mem_support56 : e6Index 5 ∈ support56 := (mem_support56 _).2 (Or.inr rfl)

variable {K : Type} [Field K]

theorem subsystemGroup13_le :
    subsystemGroup Tag.E6 K support13 ≤ subsystemGroup Tag.E6 K support134 :=
  Subgroup.closure_mono fun _ ⟨i, hi, c, hg⟩ => ⟨i, support13_subset hi, c, hg⟩

@[expose] def IsA2Block (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ k, M (Fin.last 3) k = (1 : Matrix (Fin 4) (Fin 4) K) (Fin.last 3) k ∧
    M k (Fin.last 3) = (1 : Matrix (Fin 4) (Fin 4) K) k (Fin.last 3)

theorem isA2Block_one : IsA2Block (1 : Matrix (Fin 4) (Fin 4) K) := fun _ => ⟨rfl, rfl⟩

theorem isA2Block_one_add_single {p q : Fin 4} (hp : p ≠ Fin.last 3) (hq : q ≠ Fin.last 3)
    (c : K) : IsA2Block (1 + single p q c) := by
  intro k
  simp only [Matrix.add_apply, Matrix.single_apply]
  exact ⟨by rw [ite_eq_right fun h => absurd h.1 hp, add_zero],
    by rw [ite_eq_right fun h => absurd h.2 hq, add_zero]⟩

theorem IsA2Block.mul {M N : Matrix (Fin 4) (Fin 4) K} (hM : IsA2Block M) (hN : IsA2Block N) :
    IsA2Block (M * N) := by
  intro k
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last 3)
      (fun l _ hl => by rw [(hM l).1, Matrix.one_apply_ne (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), (hM _).1, Matrix.one_apply_eq, one_mul, (hN k).1]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last 3)
      (fun l _ hl => by rw [(hN l).2, Matrix.one_apply_ne hl, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), (hN _).2, Matrix.one_apply_eq, mul_one, (hM k).2]

theorem IsA2Block.of_mul_eq_one {M N : Matrix (Fin 4) (Fin 4) K} (hM : IsA2Block M)
    (h₁ : M * N = 1) (h₂ : N * M = 1) : IsA2Block N := by
  intro k
  constructor
  · have h := congrFun (congrFun h₁ (Fin.last 3)) k
    rwa [Matrix.mul_apply, Finset.sum_eq_single (Fin.last 3)
      (fun l _ hl => by rw [(hM l).1, Matrix.one_apply_ne (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), (hM _).1, Matrix.one_apply_eq, one_mul] at h
  · have h := congrFun (congrFun h₂ k) (Fin.last 3)
    rwa [Matrix.mul_apply, Finset.sum_eq_single (Fin.last 3)
      (fun l _ hl => by rw [(hM l).2, Matrix.one_apply_ne hl, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), (hM _).2, Matrix.one_apply_eq, mul_one] at h

theorem isA2Block_a3Mat {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    IsA2Block (a3Mat g) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a3Mat_x1]; exact isA2Block_one_add_single (by decide) (by decide) c
      · rw [a3Mat_x3]; exact isA2Block_one_add_single (by decide) (by decide) c
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a3Mat_y1]; exact isA2Block_one_add_single (by decide) (by decide) c
      · rw [a3Mat_y3]; exact isA2Block_one_add_single (by decide) (by decide) c
  | one => rw [a3Mat_one]; exact isA2Block_one
  | mul x y hx hy ihx ihy =>
    rw [a3Mat_mul (subsystemGroup13_le hx) (subsystemGroup13_le hy)]
    exact ihx.mul ihy
  | inv x hx ih =>
    have h₁ := a3Mat_mul (subsystemGroup13_le hx) (inv_mem (subsystemGroup13_le hx))
    have h₂ := a3Mat_mul (inv_mem (subsystemGroup13_le hx)) (subsystemGroup13_le hx)
    rw [mul_inv_cancel, a3Mat_one] at h₁
    rw [inv_mul_cancel, a3Mat_one] at h₂
    exact ih.of_mul_eq_one h₁.symm h₂.symm

@[expose] def a2Mat₁ (g : ModGL Tag.E6 K) : Matrix (Fin 3) (Fin 3) K :=
  (a3Mat g).submatrix Fin.castSucc Fin.castSucc

theorem submatrix_mul_of_isA2Block {M N : Matrix (Fin 4) (Fin 4) K} (hM : IsA2Block M) :
    (M * N).submatrix Fin.castSucc Fin.castSucc =
      M.submatrix Fin.castSucc Fin.castSucc * N.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  have h0 : M (Fin.castSucc i) (Fin.last 3) = 0 := by
    rw [(hM _).2, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  change ∑ k : Fin 4, M (Fin.castSucc i) k * N k (Fin.castSucc j) =
    ∑ k : Fin 3, M (Fin.castSucc i) (Fin.castSucc k) * N (Fin.castSucc k) (Fin.castSucc j)
  rw [Fin.sum_univ_castSucc (n := 3), h0, zero_mul, add_zero]

theorem a2Mat₁_mul {g h : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13)
    (hh : h ∈ subsystemGroup Tag.E6 K support13) : a2Mat₁ (g * h) = a2Mat₁ g * a2Mat₁ h := by
  rw [a2Mat₁, a3Mat_mul (subsystemGroup13_le hg) (subsystemGroup13_le hh),
    submatrix_mul_of_isA2Block (isA2Block_a3Mat hg)]
  rfl

theorem a2Mat₁_one : a2Mat₁ (1 : ModGL Tag.E6 K) = 1 := by
  rw [a2Mat₁, a3Mat_one]
  exact Matrix.submatrix_one _ (Fin.castSucc_injective 3)

theorem submatrix_one_add_single (p q : Fin 3) (c : K) :
    ((1 : Matrix (Fin 4) (Fin 4) K) + single (Fin.castSucc p) (Fin.castSucc q) c).submatrix
      Fin.castSucc Fin.castSucc = 1 + single p q c := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    Fin.castSucc_inj]

theorem a2Mat₁_x1 (t : K) : a2Mat₁ (xUnit Tag.E6 K (e6Index 0) t) = 1 + single 0 1 t := by
  rw [a2Mat₁, a3Mat_x1]
  exact submatrix_one_add_single 0 1 t

theorem a2Mat₁_y1 (t : K) : a2Mat₁ (yUnit Tag.E6 K (e6Index 0) t) = 1 + single 1 0 t := by
  rw [a2Mat₁, a3Mat_y1]
  exact submatrix_one_add_single 1 0 t

theorem a2Mat₁_x3 (t : K) : a2Mat₁ (xUnit Tag.E6 K (e6Index 2) t) = 1 + single 1 2 t := by
  rw [a2Mat₁, a3Mat_x3]
  exact submatrix_one_add_single 1 2 t

theorem a2Mat₁_y3 (t : K) : a2Mat₁ (yUnit Tag.E6 K (e6Index 2) t) = 1 + single 2 1 t := by
  rw [a2Mat₁, a3Mat_y3]
  exact submatrix_one_add_single 2 1 t

theorem det_a2Mat₁ {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    (a2Mat₁ g).det = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a2Mat₁_x1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a2Mat₁_x3]; exact det_transvection_of_ne _ _ (by decide) _
    · rcases (mem_support13 i).1 hi with rfl | rfl
      · rw [a2Mat₁_y1]; exact det_transvection_of_ne _ _ (by decide) _
      · rw [a2Mat₁_y3]; exact det_transvection_of_ne _ _ (by decide) _
  | one => rw [a2Mat₁_one, det_one]
  | mul x y hx hy ihx ihy => rw [a2Mat₁_mul hx hy, det_mul, ihx, ihy, mul_one]
  | inv x hx ih =>
    have h := a2Mat₁_mul (inv_mem hx) hx
    rw [inv_mul_cancel, a2Mat₁_one] at h
    have h' := congrArg Matrix.det h
    rw [det_one, det_mul, ih, mul_one] at h'
    exact h'.symm

variable (K) in
@[expose] def a2Rep₁ : subsystemGroup Tag.E6 K support13 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨a2Mat₁ (g : ModGL Tag.E6 K), det_a2Mat₁ g.2⟩
  map_one' := Subtype.ext a2Mat₁_one
  map_mul' g h := Subtype.ext (a2Mat₁_mul g.2 h.2)

theorem coe_a2Rep₁ (g : subsystemGroup Tag.E6 K support13) :
    ((a2Rep₁ K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      a2Mat₁ (g : ModGL Tag.E6 K) :=
  rfl

theorem sl3_eq_top_of_adjacent (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (h01 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ H)
    (h12 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c ∈ H)
    (h10 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ H)
    (h21 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c ∈ H) :
    H = ⊤ := by
  have hcomm : ∀ {a b : SpecialLinearGroup (Fin 3) K}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H :=
    fun ha hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have h02 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c ∈ H := by
    intro c
    have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) c 1
    rw [mul_one] at e
    rw [← e]
    exact hcomm (h01 c) (h12 1)
  have h20 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c ∈ H := by
    intro c
    have e := Matrix.SpecialLinearGroup.commutatorElement_transvection
      (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) c 1
    rw [mul_one] at e
    rw [← e]
    exact hcomm (h21 c) (h10 1)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact h01 c
  | 0, 2, _ => exact h02 c
  | 1, 0, _ => exact h10 c
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact h12 c
  | 2, 0, _ => exact h20 c
  | 2, 1, _ => exact h21 c
  | 2, 2, h => exact absurd rfl h

theorem a2Rep₁_surjective : Function.Surjective (a2Rep₁ K) := by
  rw [← MonoidHom.range_eq_top]
  refine sl3_eq_top_of_adjacent _ (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_)
  · exact ⟨⟨_, xUnit_mem_subsystemGroup e6Index_0_mem_support13 c⟩, Subtype.ext (a2Mat₁_x1 c)⟩
  · exact ⟨⟨_, xUnit_mem_subsystemGroup e6Index_2_mem_support13 c⟩, Subtype.ext (a2Mat₁_x3 c)⟩
  · exact ⟨⟨_, yUnit_mem_subsystemGroup e6Index_0_mem_support13 c⟩, Subtype.ext (a2Mat₁_y1 c)⟩
  · exact ⟨⟨_, yUnit_mem_subsystemGroup e6Index_2_mem_support13 c⟩, Subtype.ext (a2Mat₁_y3 c)⟩

theorem eq_one_of_isA2Block {M : Matrix (Fin 4) (Fin 4) K} (hM : IsA2Block M)
    (h : M.submatrix Fin.castSucc Fin.castSucc = 1) : M = 1 := by
  ext i j
  induction i using Fin.lastCases with
  | last => exact (hM j).1
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact (hM _).2
    | cast j =>
      have e := congrFun (congrFun h i) j
      rw [Matrix.submatrix_apply] at e
      rw [e, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.castSucc_inj]

theorem a2Rep₁_injective : Function.Injective (a2Rep₁ K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h4 : a3Mat (g : ModGL Tag.E6 K) = 1 :=
    eq_one_of_isA2Block (isA2Block_a3Mat g.2) (congrArg Subtype.val hg)
  have h1 : a3Rep K ⟨g, subsystemGroup13_le g.2⟩ = 1 := Subtype.ext h4
  have h2 := a3Rep_injective (h1.trans (map_one _).symm)
  have h3 : (g : ModGL Tag.E6 K) = 1 := congrArg Subtype.val h2
  exact Subtype.ext h3

theorem a2Rep₁_bijective : Function.Bijective (a2Rep₁ K) :=
  ⟨a2Rep₁_injective, a2Rep₁_surjective⟩

@[expose] def e6TorusPair (i j : Fin Tag.E6.rank) (a b : Kˣ) : ModGL Tag.E6 K :=
  torusElt Tag.E6 K i a * torusElt Tag.E6 K j b

theorem e6TorusPair_mul (i j : Fin Tag.E6.rank) (a b a' b' : Kˣ) :
    e6TorusPair i j a b * e6TorusPair i j a' b' = e6TorusPair i j (a * a') (b * b') := by
  have h := torusElt_mul_comm (τ := Tag.E6) (R := K) j i b a'
  rw [e6TorusPair, e6TorusPair, e6TorusPair, torusElt_mul, torusElt_mul]
  calc torusElt Tag.E6 K i a * torusElt Tag.E6 K j b *
        (torusElt Tag.E6 K i a' * torusElt Tag.E6 K j b')
      = torusElt Tag.E6 K i a * (torusElt Tag.E6 K j b * torusElt Tag.E6 K i a') *
          torusElt Tag.E6 K j b' := by group
    _ = _ := by rw [h]; group

theorem e6TorusPair_one (i j : Fin Tag.E6.rank) : e6TorusPair i j (1 : Kˣ) 1 = 1 := by
  rw [e6TorusPair, torusElt_one, torusElt_one, mul_one]

theorem e6TorusPair_inv (i j : Fin Tag.E6.rank) (a b : Kˣ) :
    (e6TorusPair i j a b)⁻¹ = e6TorusPair i j a⁻¹ b⁻¹ :=
  inv_eq_of_mul_eq_one_right (by
    rw [e6TorusPair_mul, mul_inv_cancel, mul_inv_cancel, e6TorusPair_one])

theorem e6TorusPair_mem_torusGroup (i j : Fin Tag.E6.rank) (a b : Kˣ) :
    e6TorusPair i j a b ∈ torusGroup Tag.E6 K :=
  mul_mem (torusElt_mem_torusGroup i a) (torusElt_mem_torusGroup j b)

theorem mem_subsystemTorus_pair {i j : Fin Tag.E6.rank} {g : ModGL Tag.E6 K} :
    g ∈ subsystemTorus Tag.E6 K {i, j} ↔ ∃ a b : Kˣ, g = e6TorusPair i j a b := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, t, rfl⟩ := hx
      rcases Set.mem_insert_iff.1 hk with rfl | hk
      · exact ⟨t, 1, by rw [e6TorusPair, torusElt_one, mul_one]⟩
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        exact ⟨1, t, by rw [e6TorusPair, torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, (e6TorusPair_one i j).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨_, _, e6TorusPair_mul i j a b a' b'⟩
    | inv x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨_, _, e6TorusPair_inv i j a b⟩
  · rintro ⟨a, b, rfl⟩
    have hi : i ∈ ({i, j} : Set (Fin Tag.E6.rank)) := Set.mem_insert i {j}
    have hj : j ∈ ({i, j} : Set (Fin Tag.E6.rank)) :=
      Set.mem_insert_of_mem i (Set.mem_singleton j)
    exact mul_mem (torusElt_mem_subsystemTorus (K := K) hi a)
      (torusElt_mem_subsystemTorus (K := K) hj b)

theorem e6TorusPair_mem_subsystemGroup (i j : Fin Tag.E6.rank) (a b : Kˣ) :
    e6TorusPair i j a b ∈ subsystemGroup Tag.E6 K {i, j} :=
  subsystemTorus_le_subsystemGroup (mem_subsystemTorus_pair.2 ⟨a, b, rfl⟩)

theorem a2Mat₁_torus (a b : Kˣ) :
    a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) a b) =
      diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  have e : e6TorusPair (e6Index 0) (e6Index 2) a b = a3TorusElt a b 1 := by
    rw [e6TorusPair, a3TorusElt, torusElt_one, mul_one]
  rw [a2Mat₁, e, a3Mat_a3TorusElt, Matrix.submatrix_diagonal _ _ (Fin.castSucc_injective 3)]
  congr 1
  funext k
  fin_cases k <;> simp

theorem baseChangeGL_mem_subsystemGroupE6 {L : Type} [Field L] (σ : K →+* L)
    {J : Set (Fin Tag.E6.rank)} {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K J) :
    baseChangeGL σ g ∈ subsystemGroup Tag.E6 L J := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      exact xUnit_mem_subsystemGroup hi _
    · rw [baseChangeGL_yUnit]
      exact yUnit_mem_subsystemGroup hi _
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem a2Mat₁_baseChangeGL {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    a2Mat₁ (baseChangeGL σ g) = (a2Mat₁ g).map σ := by
  rw [a2Mat₁, a3Mat_baseChangeGL σ (subsystemGroup13_le hg)]
  rfl

variable (K) in
abbrev e6Diagram : ModGL Tag.E6 K →* ModGL Tag.E6 K := twistHom TwistTag.E6 K (RingHom.id K)

theorem e6Diagram_xUnit (i : Fin Tag.E6.rank) (c : K) :
    e6Diagram K (xUnit Tag.E6 K i c) = xUnit Tag.E6 K (e6Rho i) c :=
  twistHom_xUnit TwistTag.E6 K (RingHom.id K) i c

theorem e6Diagram_yUnit (i : Fin Tag.E6.rank) (c : K) :
    e6Diagram K (yUnit Tag.E6 K i c) = yUnit Tag.E6 K (e6Rho i) c :=
  twistHom_yUnit TwistTag.E6 K (RingHom.id K) i c

theorem e6Diagram_torusElt (i : Fin Tag.E6.rank) (u : Kˣ) :
    e6Diagram K (torusElt Tag.E6 K i u) = torusElt Tag.E6 K (e6Rho i) u := by
  have h := twistHom_torusElt TwistTag.E6 K (RingHom.id K) i u
  have hu : Units.map (RingHom.id K).toMonoidHom u = u := Units.ext rfl
  rw [hu] at h
  exact h

theorem e6Rho_values : e6Rho (e6Index 0) = e6Index 5 ∧ e6Rho (e6Index 2) = e6Index 4 ∧
    e6Rho (e6Index 4) = e6Index 2 ∧ e6Rho (e6Index 5) = e6Index 0 := by
  decide

theorem e6Diagram_mem_Q₁ {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support56) :
    e6Diagram K g ∈ subsystemGroup Tag.E6 K support13 := by
  obtain ⟨_, _, r4, r5⟩ := e6Rho_values
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [e6Diagram_xUnit]
      rcases (mem_support56 i).1 hi with rfl | rfl
      · rw [r4]; exact xUnit_mem_subsystemGroup e6Index_2_mem_support13 c
      · rw [r5]; exact xUnit_mem_subsystemGroup e6Index_0_mem_support13 c
    · rw [e6Diagram_yUnit]
      rcases (mem_support56 i).1 hi with rfl | rfl
      · rw [r4]; exact yUnit_mem_subsystemGroup e6Index_2_mem_support13 c
      · rw [r5]; exact yUnit_mem_subsystemGroup e6Index_0_mem_support13 c
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

variable (K) in
@[expose] def a2Flip : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem a2Flip_mul_self : a2Flip K * a2Flip K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a2Flip, Matrix.mul_apply, Fin.sum_univ_succ]

theorem a2Flip_mul_self_assoc (M : Matrix (Fin 3) (Fin 3) K) :
    a2Flip K * (a2Flip K * M) = M := by
  rw [← Matrix.mul_assoc, a2Flip_mul_self, Matrix.one_mul]

theorem det_a2Flip : (a2Flip K).det = 1 := by
  simp [a2Flip, Matrix.det_fin_three]

theorem map_a2Flip {L : Type} [Field L] (σ : K →+* L) : (a2Flip K).map σ = a2Flip L := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a2Flip]

@[expose] def a2Mat₂ (g : ModGL Tag.E6 K) : Matrix (Fin 3) (Fin 3) K :=
  a2Flip K * (adjugate (a2Mat₁ (e6Diagram K g)))ᵀ * a2Flip K

theorem a2Mat₂_mul {g h : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support56)
    (hh : h ∈ subsystemGroup Tag.E6 K support56) : a2Mat₂ (g * h) = a2Mat₂ g * a2Mat₂ h := by
  rw [a2Mat₂, a2Mat₂, a2Mat₂, map_mul, a2Mat₁_mul (e6Diagram_mem_Q₁ hg) (e6Diagram_mem_Q₁ hh),
    adjugate_mul_distrib, transpose_mul]
  simp only [Matrix.mul_assoc, a2Flip_mul_self_assoc]

theorem a2Mat₂_one : a2Mat₂ (1 : ModGL Tag.E6 K) = 1 := by
  rw [a2Mat₂, map_one, a2Mat₁_one, adjugate_one, transpose_one, Matrix.mul_one, a2Flip_mul_self]

theorem det_a2Mat₂ {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support56) :
    (a2Mat₂ g).det = 1 := by
  rw [a2Mat₂, det_mul, det_mul, det_transpose, det_adjugate, det_a2Mat₁ (e6Diagram_mem_Q₁ hg),
    one_pow, det_a2Flip, mul_one, mul_one]

variable (K) in
@[expose] def a2Rep₂ : subsystemGroup Tag.E6 K support56 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨a2Mat₂ (g : ModGL Tag.E6 K), det_a2Mat₂ g.2⟩
  map_one' := Subtype.ext a2Mat₂_one
  map_mul' g h := Subtype.ext (a2Mat₂_mul g.2 h.2)

theorem coe_a2Rep₂ (g : subsystemGroup Tag.E6 K support56) :
    ((a2Rep₂ K g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      a2Mat₂ (g : ModGL Tag.E6 K) :=
  rfl

theorem adjugate_eq_inv_of_det_eq_one {M : Matrix (Fin 3) (Fin 3) K} (h : M.det = 1) :
    adjugate M = M⁻¹ := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

theorem adjugate_one_add_single {p q : Fin 3} (hpq : p ≠ q) (c : K) :
    adjugate (1 + single p q c : Matrix (Fin 3) (Fin 3) K) = 1 + single p q (-c) := by
  rw [adjugate_eq_inv_of_det_eq_one (M := 1 + single p q c) (det_transvection_of_ne p q hpq c),
    (CFSG.LinearGroups.elementary_matrix_identities hpq).2.2.1]

theorem a2Flip_conj (M : Matrix (Fin 3) (Fin 3) K) : a2Flip K * M * a2Flip K =
    !![M 2 2, -M 2 1, M 2 0; -M 1 2, M 1 1, -M 1 0; M 0 2, -M 0 1, M 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a2Flip, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]

theorem a2Mat₂_x5 (t : K) : a2Mat₂ (xUnit Tag.E6 K (e6Index 4) t) = 1 + single 0 1 t := by
  rw [a2Mat₂, e6Diagram_xUnit, e6Rho_values.2.2.1, a2Mat₁_x3,
    adjugate_one_add_single (by decide)]
  rw [a2Flip_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2Mat₂_x6 (t : K) : a2Mat₂ (xUnit Tag.E6 K (e6Index 5) t) = 1 + single 1 2 t := by
  rw [a2Mat₂, e6Diagram_xUnit, e6Rho_values.2.2.2, a2Mat₁_x1,
    adjugate_one_add_single (by decide)]
  rw [a2Flip_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2Mat₂_y5 (t : K) : a2Mat₂ (yUnit Tag.E6 K (e6Index 4) t) = 1 + single 1 0 t := by
  rw [a2Mat₂, e6Diagram_yUnit, e6Rho_values.2.2.1, a2Mat₁_y3,
    adjugate_one_add_single (by decide)]
  rw [a2Flip_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2Mat₂_y6 (t : K) : a2Mat₂ (yUnit Tag.E6 K (e6Index 5) t) = 1 + single 2 1 t := by
  rw [a2Mat₂, e6Diagram_yUnit, e6Rho_values.2.2.2, a2Mat₁_y1,
    adjugate_one_add_single (by decide)]
  rw [a2Flip_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem a2Rep₂_surjective : Function.Surjective (a2Rep₂ K) := by
  rw [← MonoidHom.range_eq_top]
  refine sl3_eq_top_of_adjacent _ (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_)
  · exact ⟨⟨_, xUnit_mem_subsystemGroup e6Index_4_mem_support56 c⟩, Subtype.ext (a2Mat₂_x5 c)⟩
  · exact ⟨⟨_, xUnit_mem_subsystemGroup e6Index_5_mem_support56 c⟩, Subtype.ext (a2Mat₂_x6 c)⟩
  · exact ⟨⟨_, yUnit_mem_subsystemGroup e6Index_4_mem_support56 c⟩, Subtype.ext (a2Mat₂_y5 c)⟩
  · exact ⟨⟨_, yUnit_mem_subsystemGroup e6Index_5_mem_support56 c⟩, Subtype.ext (a2Mat₂_y6 c)⟩

theorem a2Rep₂_injective : Function.Injective (a2Rep₂ K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : a2Mat₂ (g : ModGL Tag.E6 K) = 1 := congrArg Subtype.val hg
  have hmem := e6Diagram_mem_Q₁ g.2
  set A := a2Mat₁ (e6Diagram K (g : ModGL Tag.E6 K)) with hA
  have h2 : (adjugate A)ᵀ = 1 := by
    have e : a2Flip K * (a2Flip K * (adjugate A)ᵀ * a2Flip K) * a2Flip K = (adjugate A)ᵀ := by
      simp only [Matrix.mul_assoc, a2Flip_mul_self_assoc, a2Flip_mul_self, Matrix.mul_one]
    rw [← e]
    change a2Flip K * a2Mat₂ (g : ModGL Tag.E6 K) * a2Flip K = 1
    rw [h1, Matrix.mul_one, a2Flip_mul_self]
  have h3 : A = 1 := by
    have hadj : adjugate A = 1 := by
      rw [← Matrix.transpose_transpose (adjugate A), h2, Matrix.transpose_one]
    rw [adjugate_eq_inv_of_det_eq_one (det_a2Mat₁ hmem)] at hadj
    have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M⁻¹) hadj
    rwa [Matrix.nonsing_inv_nonsing_inv _ (by rw [det_a2Mat₁ hmem]; exact isUnit_one),
      inv_one] at e
  have h4 : a2Rep₁ K ⟨_, hmem⟩ = 1 := Subtype.ext h3
  have h5 := a2Rep₁_injective (h4.trans (map_one _).symm)
  have h6 : e6Diagram K (g : ModGL Tag.E6 K) = 1 := congrArg Subtype.val h5
  have h7 : (g : ModGL Tag.E6 K) = 1 :=
    twistHom_injective TwistTag.E6 K (RingHom.id K) (h6.trans (map_one _).symm)
  exact Subtype.ext h7

theorem a2Rep₂_bijective : Function.Bijective (a2Rep₂ K) :=
  ⟨a2Rep₂_injective, a2Rep₂_surjective⟩

theorem a2Mat₂_torus (a b : Kˣ) :
    a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) a b) =
      diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  have e : e6Diagram K (e6TorusPair (e6Index 4) (e6Index 5) a b) =
      e6TorusPair (e6Index 0) (e6Index 2) b a := by
    rw [e6TorusPair, map_mul, e6Diagram_torusElt, e6Diagram_torusElt, e6Rho_values.2.2.1,
      e6Rho_values.2.2.2, e6TorusPair, torusElt_mul_comm]
  have hinv : (diagonal ![(b : K), ((b⁻¹ * a : Kˣ) : K), ((a⁻¹ : Kˣ) : K)])⁻¹ =
      diagonal ![((b⁻¹ : Kˣ) : K), ((a⁻¹ * b : Kˣ) : K), (a : K)] := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [← Units.val_mul, mul_assoc]
  have hdet : (diagonal ![(b : K), ((b⁻¹ * a : Kˣ) : K), ((a⁻¹ : Kˣ) : K)]).det = 1 := by
    rw [← a2Mat₁_torus]
    exact det_a2Mat₁ (e6TorusPair_mem_subsystemGroup _ _ b a)
  rw [a2Mat₂, e, a2Mat₁_torus, adjugate_eq_inv_of_det_eq_one hdet, hinv, diagonal_transpose,
    a2Flip_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem baseChangeGL_e6Diagram {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support56) :
    baseChangeGL σ (e6Diagram K g) = e6Diagram L (baseChangeGL σ g) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [e6Diagram_xUnit, baseChangeGL_xUnit, baseChangeGL_xUnit, e6Diagram_xUnit]
    · rw [e6Diagram_yUnit, baseChangeGL_yUnit, baseChangeGL_yUnit, e6Diagram_yUnit]
  | one => simp only [map_one]
  | mul x y _ _ hx hy => simp only [map_mul, hx, hy]
  | inv x _ hx => simp only [map_inv, hx]

theorem a2Mat₂_baseChangeGL {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K support56) :
    a2Mat₂ (baseChangeGL σ g) = (a2Mat₂ g).map σ := by
  rw [a2Mat₂, a2Mat₂, ← baseChangeGL_e6Diagram σ hg,
    a2Mat₁_baseChangeGL σ (e6Diagram_mem_Q₁ hg), Matrix.map_mul, Matrix.map_mul, map_a2Flip,
    Matrix.transpose_map, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate,
    RingHom.mapMatrix_apply]

theorem apply_a3Vec_castSucc {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13)
    (j : Fin 3) :
    (g : Module.End K (RootModule Tag.E6 K)) (a3Vec K (Fin.castSucc j)) =
      ∑ i : Fin 3, a2Mat₁ g i j • a3Vec K (Fin.castSucc i) := by
  rw [apply_a3Vec (subsystemGroup13_le hg), Fin.sum_univ_castSucc (n := 3)]
  have h0 : a3Mat g (Fin.last 3) (Fin.castSucc j) = 0 := by
    rw [((isA2Block_a3Mat hg) _).1, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  rw [h0, zero_smul, add_zero]
  rfl

theorem mem_Q₁_inf_torusGroup {g : ModGL Tag.E6 K} :
    g ∈ subsystemGroup Tag.E6 K support13 ⊓ torusGroup Tag.E6 K ↔
      ∃ a b : Kˣ, g = e6TorusPair (e6Index 0) (e6Index 2) a b := by
  rw [subsystemGroup_inf_torusGroup]
  exact mem_subsystemTorus_pair (i := e6Index 0) (j := e6Index 2)

theorem mem_Q₂_inf_torusGroup {g : ModGL Tag.E6 K} :
    g ∈ subsystemGroup Tag.E6 K support56 ⊓ torusGroup Tag.E6 K ↔
      ∃ a b : Kˣ, g = e6TorusPair (e6Index 4) (e6Index 5) a b := by
  rw [subsystemGroup_inf_torusGroup]
  exact mem_subsystemTorus_pair (i := e6Index 4) (j := e6Index 5)

theorem pairing_support13_support56 : ∀ i j : Fin 6, (i = 0 ∨ i = 2) → (j = 4 ∨ j = 5) →
    (Pi.single (e6Index i) 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
      (Tag.E6.symmetrizedCartan *ᵥ (Pi.single (e6Index j) 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
  rw [symmetrizedCartan_E6]
  decide +kernel

theorem commute_pinnedX_E6 {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h0 : α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0) (c d : K) :
    Commute (pinnedX Tag.E6 K α c) (pinnedX Tag.E6 K β d) :=
  (simply_laced_orthogonal_root_commutation Tag.E6 (Or.inr (Or.inl rfl))).2 K α β hα hβ h0 _
    (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commute_gen₁₂ {i j : Fin Tag.E6.rank} (hi : i ∈ support13) (hj : j ∈ support56)
    {x y : ModGL Tag.E6 K} (hx : ∃ c, x = xUnit Tag.E6 K i c ∨ x = yUnit Tag.E6 K i c)
    (hy : ∃ d, y = xUnit Tag.E6 K j d ∨ y = yUnit Tag.E6 K j d) : Commute x y := by
  have h0 : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
      (Tag.E6.symmetrizedCartan *ᵥ (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
    rcases (mem_support13 i).1 hi with rfl | rfl <;> rcases (mem_support56 j).1 hj with rfl | rfl
    · exact pairing_support13_support56 0 4 (Or.inl rfl) (Or.inl rfl)
    · exact pairing_support13_support56 0 5 (Or.inl rfl) (Or.inr rfl)
    · exact pairing_support13_support56 2 4 (Or.inr rfl) (Or.inl rfl)
    · exact pairing_support13_support56 2 5 (Or.inr rfl) (Or.inr rfl)
  obtain ⟨c, rfl | rfl⟩ := hx <;> obtain ⟨d, rfl | rfl⟩ := hy
  · rw [← pinnedX_single, ← pinnedX_single]
    exact commute_pinnedX_E6 (isRoot_single _ i) (isRoot_single _ j) h0 c d
  · rw [← pinnedX_single, ← pinnedX_neg_single]
    exact commute_pinnedX_E6 (isRoot_single _ i) (isRoot_neg_single _ j)
      (by rw [mulVec_neg, dotProduct_neg, h0, neg_zero]) c d
  · rw [← pinnedX_neg_single, ← pinnedX_single]
    exact commute_pinnedX_E6 (isRoot_neg_single _ i) (isRoot_single _ j)
      (by rw [neg_dotProduct, h0, neg_zero]) c d
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single]
    exact commute_pinnedX_E6 (isRoot_neg_single _ i) (isRoot_neg_single _ j)
      (by rw [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, h0]) c d

theorem commute_Q₁_Q₂ {g h : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13)
    (hh : h ∈ subsystemGroup Tag.E6 K support56) : Commute g h := by
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, d, hyd⟩ := hy
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, hxc⟩ := hx
      exact commute_gen₁₂ hi hj ⟨c, hxc⟩ ⟨d, hyd⟩
    | one => exact Commute.one_left _
    | mul x z _ _ hx hz => exact hx.mul_left hz
    | inv x _ hx => exact hx.inv_left
  | one => exact Commute.one_right _
  | mul y z _ _ hy hz => exact hy.mul_right hz
  | inv y _ hy => exact hy.inv_right

theorem Q₁_mul_Q₂_comm :
    (subsystemGroup Tag.E6 K support13 : Set (ModGL Tag.E6 K)) *
        subsystemGroup Tag.E6 K support56 =
      (subsystemGroup Tag.E6 K support56 : Set (ModGL Tag.E6 K)) *
        subsystemGroup Tag.E6 K support13 := by
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, (commute_Q₁_Q₂ ha hb).eq.symm⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, (commute_Q₁_Q₂ ha hb).eq⟩

theorem torusElt_apply_rootVec_single (i k : Fin Tag.E6.rank) (t : Kˣ) :
    (torusElt Tag.E6 K i t : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K (Pi.single k 1)) =
      ((t ^ Tag.E6.cartan i k : Kˣ) : K) • rootVec Tag.E6 K (Pi.single k 1) := by
  have e : ∑ j, Tag.E6.cartan i j * (Pi.single k 1 : Fin Tag.E6.rank → ℤ) j =
      Tag.E6.cartan i k := by
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
  rw [torusElt_rootVec i t (isRoot_single Tag.E6 k), e]

theorem e6TorusPair_apply_rootVec_single (i j k : Fin Tag.E6.rank) (a b : Kˣ) :
    (e6TorusPair i j a b : Module.End K (RootModule Tag.E6 K))
        (rootVec Tag.E6 K (Pi.single k 1)) =
      ((a ^ Tag.E6.cartan i k * b ^ Tag.E6.cartan j k : Kˣ) : K) •
        rootVec Tag.E6 K (Pi.single k 1) := by
  rw [e6TorusPair, Units.val_mul, Module.End.mul_apply, torusElt_apply_rootVec_single, map_smul,
    torusElt_apply_rootVec_single, smul_smul]
  congr 1
  rw [Units.val_mul, mul_comm]

theorem rootVec_single_ne_zero (k : Fin Tag.E6.rank) :
    rootVec Tag.E6 K (Pi.single k 1 : Fin Tag.E6.rank → ℤ) ≠ 0 := by
  rw [C2E6Std.rootVec_eq_single (isRoot_single Tag.E6 k)]
  exact Finsupp.single_ne_zero.2 one_ne_zero

theorem eq_one_of_mem_torusGroup_of_fix_single {g : ModGL Tag.E6 K}
    (hg : g ∈ torusGroup Tag.E6 K)
    (h : ∀ k, (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (Pi.single k 1)) =
      rootVec Tag.E6 K (Pi.single k 1)) : g = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
  have hl : l = 1 := funext fun k => by
    have h1 := h k
    change rootDiag l (rootVec Tag.E6 K (Pi.single k 1)) = _ at h1
    rw [rootDiag_rootVec l (isRoot_single Tag.E6 k)] at h1
    have h2 : ((rootChar l (Pi.single k 1) : Kˣ) : K) = 1 :=
      smul_left_injective K (rootVec_single_ne_zero k) (h1.trans (one_smul K _).symm)
    have e := rootChar_nsmul_single l k 1
    rw [one_smul, pow_one] at e
    rw [e] at h2
    exact Units.ext h2
  rw [hl, rootDiagUnit_one]

theorem smul_eq_one_of_apply_eq {g : ModGL Tag.E6 K} {u : Kˣ} {k : Fin Tag.E6.rank}
    (hu : (g : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (Pi.single k 1)) =
      (u : K) • rootVec Tag.E6 K (Pi.single k 1)) (hg : g = 1) : u = 1 := by
  subst hg
  rw [Units.val_one, Module.End.one_apply] at hu
  exact Units.ext (smul_left_injective K (rootVec_single_ne_zero k)
    ((one_smul K _).trans hu)).symm

theorem cube_root_aux {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) :
    u⁻¹ * u ^ 2 = u ∧ (u ^ 2)⁻¹ = u := by
  refine ⟨inv_mul_eq_iff_eq_mul.2 (sq u), inv_eq_of_mul_eq_one_left ?_⟩
  rw [← pow_succ', hu]

theorem a2Mat₁_center {u : Kˣ} (hu : u ^ 3 = 1) :
    a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) u (u ^ 2)) = scalar (Fin 3) (u : K) := by
  obtain ⟨h1, h2⟩ := cube_root_aux hu
  rw [a2Mat₁_torus, h1, h2, scalar_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem a2Mat₂_center {u : Kˣ} (hu : u ^ 3 = 1) :
    a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2)) = scalar (Fin 3) (u : K) := by
  obtain ⟨h1, h2⟩ := cube_root_aux hu
  rw [a2Mat₂_torus, h1, h2, scalar_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem cartan_center_sum : ∀ k : Fin Tag.E6.rank,
    Tag.E6.cartan (e6Index 0) k + 2 * Tag.E6.cartan (e6Index 2) k + Tag.E6.cartan (e6Index 4) k +
      2 * Tag.E6.cartan (e6Index 5) k = 3 * (![0, 0, 1, -1, 0, 1] : Fin 6 → ℤ) k := by
  decide

theorem cartan_col3 : Tag.E6.cartan (e6Index 0) (e6Index 3) = 0 ∧
    Tag.E6.cartan (e6Index 2) (e6Index 3) = -1 ∧ Tag.E6.cartan (e6Index 4) (e6Index 3) = -1 ∧
    Tag.E6.cartan (e6Index 5) (e6Index 3) = 0 := by
  decide

theorem zpow_center_aux {G : Type*} [CommGroup G] {u : G} (hu : u ^ 3 = 1) (a b c d m : ℤ)
    (h : a + 2 * b + c + 2 * d = 3 * m) :
    u ^ a * (u ^ 2) ^ b * (u ^ c * (u ^ 2) ^ d) = 1 := by
  have h3 : u ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hu
  have e : u ^ a * (u ^ 2) ^ b * (u ^ c * (u ^ 2) ^ d) = u ^ (a + 2 * b + c + 2 * d) := by
    rw [← zpow_natCast u 2, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add,
      ← _root_.zpow_add, ← _root_.zpow_add]
    congr 1
    push_cast
    ring
  rw [e, h, _root_.zpow_mul, h3, _root_.one_zpow]

theorem e6TorusPair_center_mul {u : Kˣ} (hu : u ^ 3 = 1) :
    e6TorusPair (e6Index 0) (e6Index 2) u (u ^ 2) * e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2) =
      1 := by
  refine eq_one_of_mem_torusGroup_of_fix_single (mul_mem (e6TorusPair_mem_torusGroup _ _ _ _)
    (e6TorusPair_mem_torusGroup _ _ _ _)) fun k => ?_
  rw [Units.val_mul, Module.End.mul_apply, e6TorusPair_apply_rootVec_single, map_smul,
    e6TorusPair_apply_rootVec_single, smul_smul, ← Units.val_mul, mul_comm,
    zpow_center_aux hu _ _ _ _ _ (cartan_center_sum k), Units.val_one, one_smul]

theorem eq_of_e6TorusPair_center_mul {a b : Kˣ} (ha : a ^ 3 = 1)
    (h : e6TorusPair (e6Index 0) (e6Index 2) a (a ^ 2) *
      e6TorusPair (e6Index 4) (e6Index 5) b (b ^ 2) = 1) : a = b := by
  obtain ⟨c0, c2, c4, c5⟩ := cartan_col3
  have hv : ((e6TorusPair (e6Index 0) (e6Index 2) a (a ^ 2) *
      e6TorusPair (e6Index 4) (e6Index 5) b (b ^ 2) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K (Pi.single (e6Index 3) 1)) =
      ((b⁻¹ * (a ^ 2)⁻¹ : Kˣ) : K) • rootVec Tag.E6 K (Pi.single (e6Index 3) 1) := by
    rw [Units.val_mul, Module.End.mul_apply, e6TorusPair_apply_rootVec_single, map_smul,
      e6TorusPair_apply_rootVec_single, smul_smul, ← Units.val_mul, c0, c2, c4, c5]
    simp
  have h1 := smul_eq_one_of_apply_eq hv h
  rw [← _root_.mul_inv_rev, inv_eq_one] at h1
  rw [eq_inv_of_mul_eq_one_right h1, (cube_root_aux ha).2]

variable (K) in
@[expose] def a2Equiv₁ : subsystemGroup Tag.E6 K support13 ≃* SpecialLinearGroup (Fin 3) K :=
  MulEquiv.ofBijective (a2Rep₁ K) a2Rep₁_bijective

variable (K) in
@[expose] def a2Equiv₂ : subsystemGroup Tag.E6 K support56 ≃* SpecialLinearGroup (Fin 3) K :=
  MulEquiv.ofBijective (a2Rep₂ K) a2Rep₂_bijective

variable (K) in
@[expose] def twoA2Mul :
    SpecialLinearGroup (Fin 3) K × SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K :=
  MonoidHom.noncommCoprod
    ((subsystemGroup Tag.E6 K support13).subtype.comp (a2Equiv₁ K).symm.toMonoidHom)
    ((subsystemGroup Tag.E6 K support56).subtype.comp (a2Equiv₂ K).symm.toMonoidHom)
    fun A B => commute_Q₁_Q₂ ((a2Equiv₁ K).symm A).2 ((a2Equiv₂ K).symm B).2

theorem twoA2Mul_apply (A B : SpecialLinearGroup (Fin 3) K) :
    twoA2Mul K (A, B) =
      ((a2Equiv₁ K).symm A : ModGL Tag.E6 K) * ((a2Equiv₂ K).symm B : ModGL Tag.E6 K) :=
  rfl

theorem range_twoA2Mul :
    Set.range (twoA2Mul K) = (subsystemGroup Tag.E6 K support13 : Set (ModGL Tag.E6 K)) *
      subsystemGroup Tag.E6 K support56 := by
  ext x
  simp only [Set.mem_range, Set.mem_mul, SetLike.mem_coe, Prod.exists]
  constructor
  · rintro ⟨A, B, rfl⟩
    exact ⟨_, ((a2Equiv₁ K).symm A).2, _, ((a2Equiv₂ K).symm B).2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a2Equiv₁ K ⟨a, ha⟩, a2Equiv₂ K ⟨b, hb⟩, ?_⟩
    rw [twoA2Mul_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem a2Equiv₁_apply (g : subsystemGroup Tag.E6 K support13) : a2Equiv₁ K g = a2Rep₁ K g :=
  rfl

theorem a2Equiv₂_apply (g : subsystemGroup Tag.E6 K support56) : a2Equiv₂ K g = a2Rep₂ K g :=
  rfl

theorem ne_zero_of_pow_three_eq_one {l : K} (hl : l ^ 3 = 1) : l ≠ 0 := by
  rintro rfl
  norm_num at hl

@[expose] def cubeUnit {l : K} (hl : l ^ 3 = 1) : Kˣ := Units.mk0 l (ne_zero_of_pow_three_eq_one hl)

theorem cubeUnit_pow {l : K} (hl : l ^ 3 = 1) : cubeUnit hl ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, cubeUnit, Units.val_mk0, hl, Units.val_one])

theorem a2Equiv₁_symm_scalar {l : K} (hl : l ^ 3 = 1) (A : SpecialLinearGroup (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l) :
    (((a2Equiv₁ K).symm A : subsystemGroup Tag.E6 K support13) : ModGL Tag.E6 K) =
      e6TorusPair (e6Index 0) (e6Index 2) (cubeUnit hl) (cubeUnit hl ^ 2) := by
  have hmem : e6TorusPair (e6Index 0) (e6Index 2) (cubeUnit hl) (cubeUnit hl ^ 2) ∈
      subsystemGroup Tag.E6 K support13 := e6TorusPair_mem_subsystemGroup _ _ _ _
  have e : (a2Equiv₁ K).symm A = ⟨_, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [hA, a2Equiv₁_apply, coe_a2Rep₁, a2Mat₁_center (cubeUnit_pow hl)]
    rfl
  rw [e]

theorem a2Equiv₂_symm_scalar {l : K} (hl : l ^ 3 = 1) (B : SpecialLinearGroup (Fin 3) K)
    (hB : (B : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l) :
    (((a2Equiv₂ K).symm B : subsystemGroup Tag.E6 K support56) : ModGL Tag.E6 K) =
      e6TorusPair (e6Index 4) (e6Index 5) (cubeUnit hl) (cubeUnit hl ^ 2) := by
  have hmem : e6TorusPair (e6Index 4) (e6Index 5) (cubeUnit hl) (cubeUnit hl ^ 2) ∈
      subsystemGroup Tag.E6 K support56 := e6TorusPair_mem_subsystemGroup _ _ _ _
  have e : (a2Equiv₂ K).symm B = ⟨_, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [hB, a2Equiv₂_apply, coe_a2Rep₂, a2Mat₂_center (cubeUnit_pow hl)]
    rfl
  rw [e]

theorem twoA2Mul_eq_one_iff (A B : SpecialLinearGroup (Fin 3) K) :
    twoA2Mul K (A, B) = 1 ↔ ∃ l : K, l ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l ∧
        (B : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l := by
  constructor
  · intro h
    obtain ⟨g₁, rfl⟩ := (a2Equiv₁ K).surjective A
    obtain ⟨g₂, rfl⟩ := (a2Equiv₂ K).surjective B
    rw [twoA2Mul_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h
    have hg₁Q₂ : (g₁ : ModGL Tag.E6 K) ∈ subsystemGroup Tag.E6 K support56 := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem g₂.2
    have hg₂Q₁ : (g₂ : ModGL Tag.E6 K) ∈ subsystemGroup Tag.E6 K support13 := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem g₁.2
    have hA : a2Equiv₁ K g₁ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      obtain ⟨x, rfl⟩ := (a2Equiv₁ K).surjective X
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (commute_Q₁_Q₂ x.2 hg₁Q₂).eq)
    have hB : a2Equiv₂ K g₂ ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      obtain ⟨x, rfl⟩ := (a2Equiv₂ K).surjective X
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (commute_Q₁_Q₂ hg₂Q₁ x.2).eq.symm)
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    obtain ⟨q, hq, hqB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hB
    rw [Fintype.card_fin] at hr hq
    have e₁ := a2Equiv₁_symm_scalar hr (a2Equiv₁ K g₁) hrA.symm
    have e₂ := a2Equiv₂_symm_scalar hq (a2Equiv₂ K g₂) hqB.symm
    rw [MulEquiv.symm_apply_apply] at e₁ e₂
    rw [e₁, e₂] at h
    have hrq : cubeUnit hr = cubeUnit hq := eq_of_e6TorusPair_center_mul (cubeUnit_pow hr) h
    have hrq' : r = q := congrArg Units.val hrq
    refine ⟨r, hr, hrA.symm, ?_⟩
    rw [hrq']
    exact hqB.symm
  · rintro ⟨l, hl, hA, hB⟩
    rw [twoA2Mul_apply, a2Equiv₁_symm_scalar hl A hA, a2Equiv₂_symm_scalar hl B hB]
    exact e6TorusPair_center_mul (cubeUnit_pow hl)

theorem exists_center_Q₁ {l : K} (hl : l ^ 3 = 1) :
    ∃ g ∈ Subgroup.center (subsystemGroup Tag.E6 K support13),
      (a2Rep₁ K g : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l := by
  have hdet : (scalar (Fin 3) l).det = 1 := by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl]
  set s : SpecialLinearGroup (Fin 3) K := ⟨scalar (Fin 3) l, hdet⟩
  obtain ⟨g, hg⟩ := a2Rep₁_bijective.2 s
  refine ⟨g, Subgroup.mem_center_iff.2 fun h => a2Rep₁_bijective.1 ?_, by rw [hg]⟩
  rw [map_mul, map_mul, hg]
  refine Subtype.ext ?_
  change (a2Rep₁ K h : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) l =
    scalar (Fin 3) l * (a2Rep₁ K h : Matrix (Fin 3) (Fin 3) K)
  exact (Matrix.scalar_commute l (fun r => Commute.all l r) _).eq.symm

theorem exists_center_Q₂ {l : K} (hl : l ^ 3 = 1) :
    ∃ g ∈ Subgroup.center (subsystemGroup Tag.E6 K support56),
      (a2Rep₂ K g : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l := by
  have hdet : (scalar (Fin 3) l).det = 1 := by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl]
  set s : SpecialLinearGroup (Fin 3) K := ⟨scalar (Fin 3) l, hdet⟩
  obtain ⟨g, hg⟩ := a2Rep₂_bijective.2 s
  refine ⟨g, Subgroup.mem_center_iff.2 fun h => a2Rep₂_bijective.1 ?_, by rw [hg]⟩
  rw [map_mul, map_mul, hg]
  refine Subtype.ext ?_
  change (a2Rep₂ K h : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) l =
    scalar (Fin 3) l * (a2Rep₂ K h : Matrix (Fin 3) (Fin 3) K)
  exact (Matrix.scalar_commute l (fun r => Commute.all l r) _).eq.symm

theorem diagonal_conj_one_add_single {d d' : Fin 3 → K} (hd : ∀ k, d k * d' k = 1)
    (p q : Fin 3) (c : K) :
    diagonal d * (1 + single p q c) * diagonal d' = 1 + single p q (d p * c * d' q) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h : p = a ∧ q = a
    · obtain ⟨hp, hq⟩ := h
      simp only [hp, hq, and_self, ite_true]
      linear_combination hd a
    · simp only [ite_true, h, ite_false, add_zero, mul_one]
      exact hd a
  · by_cases h : p = a ∧ q = b
    · obtain ⟨hp, hq⟩ := h
      simp only [hp, hq, hab, and_self, ite_true, ite_false, zero_add]
    · simp only [hab, h, ite_false, add_zero, mul_zero, zero_mul]

theorem conj_formula {Q : Subgroup (ModGL Tag.E6 K)} {S : Set (ModGL Tag.E6 K)}
    (hQ : Q = Subgroup.closure S) (M : ModGL Tag.E6 K → Matrix (Fin 3) (Fin 3) K)
    (hmul : ∀ g ∈ Q, ∀ g' ∈ Q, M (g * g') = M g * M g') (hone : M 1 = 1)
    {D D' : Matrix (Fin 3) (Fin 3) K} (hDD' : D * D' = 1) (hD'D : D' * D = 1)
    (h : ModGL Tag.E6 K) (hgen : ∀ x ∈ S, h * x * h⁻¹ ∈ Q ∧ M (h * x * h⁻¹) = D * M x * D')
    {g : ModGL Tag.E6 K} (hg : g ∈ Q) : h * g * h⁻¹ ∈ Q ∧ M (h * g * h⁻¹) = D * M g * D' := by
  subst hQ
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one =>
    rw [mul_one, mul_inv_cancel, hone, Matrix.mul_one, hDD']
    exact ⟨one_mem _, rfl⟩
  | mul x y hx hy ihx ihy =>
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    refine ⟨mul_mem ihx.1 ihy.1, ?_⟩
    rw [hmul _ ihx.1 _ ihy.1, ihx.2, ihy.2, hmul _ hx _ hy]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D' D, hD'D, Matrix.one_mul]
  | inv x hx ih =>
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    refine ⟨inv_mem ih.1, ?_⟩
    have h1 : M (h * x * h⁻¹)⁻¹ * M (h * x * h⁻¹) = 1 := by
      rw [← hmul _ (inv_mem ih.1) _ ih.1, inv_mul_cancel, hone]
    have h2 : D * M x⁻¹ * D' * M (h * x * h⁻¹) = 1 := by
      rw [ih.2]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D' D, hD'D, Matrix.one_mul, ← Matrix.mul_assoc (M x⁻¹),
        ← hmul _ (inv_mem hx) _ hx, inv_mul_cancel, hone, Matrix.one_mul, hDD']
    exact (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)

theorem xUnit_param_injective (i : Fin Tag.E6.rank) {c d : K}
    (h : xUnit Tag.E6 K i c = xUnit Tag.E6 K i d) : c = d :=
  xOp_injective (τ := Tag.E6) (R := K) i (congrArg Units.val h)

theorem exists_simple_root_characters {h : ModGL Tag.E6 K} (hh : h ∈ torusGroup Tag.E6 K) :
    ∃ χ : Fin Tag.E6.rank → Kˣ, (∀ i c, h * xUnit Tag.E6 K i c * h⁻¹ = xUnit Tag.E6 K i (χ i * c)) ∧
      ∀ i c, h * yUnit Tag.E6 K i c * h⁻¹ = yUnit Tag.E6 K i (((χ i)⁻¹ : Kˣ) * c) := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact ⟨l, (root_diagonal_conjugation Tag.E6 K l).1, (root_diagonal_conjugation Tag.E6 K l).2.1⟩

theorem units_conj_arith₁ (s t : Kˣ) (c : K) :
    ((s * t : Kˣ) : K) * c * ((t⁻¹ : Kˣ) : K) = (s : K) * c :=
  calc ((s * t : Kˣ) : K) * c * ((t⁻¹ : Kˣ) : K) = (s : K) * c * ((t : K) * ((t⁻¹ : Kˣ) : K)) := by
        rw [Units.val_mul]; ring
    _ = (s : K) * c := by rw [Units.mul_inv, mul_one]

theorem units_conj_arith₂ (s t : Kˣ) (c : K) :
    (t : K) * c * (((s * t)⁻¹ : Kˣ) : K) = ((s⁻¹ : Kˣ) : K) * c :=
  calc (t : K) * c * (((s * t)⁻¹ : Kˣ) : K) =
        ((s⁻¹ : Kˣ) : K) * c * ((t : K) * ((t⁻¹ : Kˣ) : K)) := by
        rw [mul_inv, Units.val_mul]; ring
    _ = ((s⁻¹ : Kˣ) : K) * c := by rw [Units.mul_inv, mul_one]

theorem conj_torus_formula {J : Set (Fin Tag.E6.rank)} {i₁ i₂ : Fin Tag.E6.rank}
    (hJ : ∀ i, i ∈ J ↔ (i = i₁ ∨ i = i₂)) (M : ModGL Tag.E6 K → Matrix (Fin 3) (Fin 3) K)
    (hmul : ∀ g ∈ subsystemGroup Tag.E6 K J, ∀ g' ∈ subsystemGroup Tag.E6 K J,
      M (g * g') = M g * M g') (hone : M 1 = 1)
    (hx₁ : ∀ c, M (xUnit Tag.E6 K i₁ c) = 1 + single 0 1 c)
    (hx₂ : ∀ c, M (xUnit Tag.E6 K i₂ c) = 1 + single 1 2 c)
    (hy₁ : ∀ c, M (yUnit Tag.E6 K i₁ c) = 1 + single 1 0 c)
    (hy₂ : ∀ c, M (yUnit Tag.E6 K i₂ c) = 1 + single 2 1 c)
    {h : ModGL Tag.E6 K} (hh : h ∈ torusGroup Tag.E6 K) {s t : Kˣ}
    (hs : ∀ c : K, h * xUnit Tag.E6 K i₁ c * h⁻¹ = xUnit Tag.E6 K i₁ (s * c))
    (ht : ∀ c : K, h * xUnit Tag.E6 K i₂ c * h⁻¹ = xUnit Tag.E6 K i₂ (t * c))
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K J) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.E6 K J ∧
      M (h * g * h⁻¹) = diagonal ![((s * t : Kˣ) : K), (t : K), 1] * M g *
        diagonal ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1] := by
  obtain ⟨χ, hχx, hχy⟩ := exists_simple_root_characters hh
  have hs' : χ i₁ = s := Units.ext (by
    have := xUnit_param_injective i₁ ((hχx i₁ 1).symm.trans (hs 1))
    rwa [mul_one, mul_one] at this)
  have ht' : χ i₂ = t := Units.ext (by
    have := xUnit_param_injective i₂ ((hχx i₂ 1).symm.trans (ht 1))
    rwa [mul_one, mul_one] at this)
  have hd : ∀ k, (![((s * t : Kˣ) : K), (t : K), 1] : Fin 3 → K) k *
      ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1] k = 1 := by
    intro k
    fin_cases k
    · exact Units.mul_inv (s * t)
    · exact Units.mul_inv t
    · exact mul_one 1
  have hd' : ∀ k, (![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1] : Fin 3 → K) k *
      ![((s * t : Kˣ) : K), (t : K), 1] k = 1 := fun k => by rw [mul_comm]; exact hd k
  have hDD : ∀ {d d' : Fin 3 → K}, (∀ k, d k * d' k = 1) → diagonal d * diagonal d' = 1 :=
    fun h => by rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg _ (funext h)
  have hJ₁ : i₁ ∈ J := (hJ i₁).2 (Or.inl rfl)
  have hJ₂ : i₂ ∈ J := (hJ i₂).2 (Or.inr rfl)
  refine conj_formula rfl M hmul hone (hDD hd) (hDD hd') h ?_ hg
  rintro x ⟨i, hi, c, rfl | rfl⟩
  · rcases (hJ i).1 hi with rfl | rfl
    · rw [hs, hx₁, hx₁, diagonal_conj_one_add_single hd]
      refine ⟨xUnit_mem_subsystemGroup hJ₁ _, ?_⟩
      congr 2
      exact (units_conj_arith₁ s t c).symm
    · rw [ht, hx₂, hx₂, diagonal_conj_one_add_single hd]
      refine ⟨xUnit_mem_subsystemGroup hJ₂ _, ?_⟩
      congr 2
      change (t : K) * c = (t : K) * c * 1
      rw [mul_one]
  · rcases (hJ i).1 hi with rfl | rfl
    · rw [hχy, hs', hy₁, hy₁, diagonal_conj_one_add_single hd]
      refine ⟨yUnit_mem_subsystemGroup hJ₁ _, ?_⟩
      congr 2
      exact (units_conj_arith₂ s t c).symm
    · rw [hχy, ht', hy₂, hy₂, diagonal_conj_one_add_single hd]
      refine ⟨yUnit_mem_subsystemGroup hJ₂ _, ?_⟩
      congr 2
      change ((t⁻¹ : Kˣ) : K) * c = 1 * c * ((t⁻¹ : Kˣ) : K)
      rw [one_mul, mul_comm]

theorem a2Mat₁_conj_torus {h : ModGL Tag.E6 K} (hh : h ∈ torusGroup Tag.E6 K) {s t : Kˣ}
    (hs : ∀ c : K, h * xUnit Tag.E6 K (e6Index 0) c * h⁻¹ = xUnit Tag.E6 K (e6Index 0) (s * c))
    (ht : ∀ c : K, h * xUnit Tag.E6 K (e6Index 2) c * h⁻¹ = xUnit Tag.E6 K (e6Index 2) (t * c))
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support13) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.E6 K support13 ∧
      a2Mat₁ (h * g * h⁻¹) = diagonal ![((s * t : Kˣ) : K), (t : K), 1] * a2Mat₁ g *
        diagonal ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1] :=
  conj_torus_formula mem_support13 a2Mat₁ (fun _ hg _ hg' => a2Mat₁_mul hg hg') a2Mat₁_one
    a2Mat₁_x1 a2Mat₁_x3 a2Mat₁_y1 a2Mat₁_y3 hh hs ht hg

theorem a2Mat₂_conj_torus {h : ModGL Tag.E6 K} (hh : h ∈ torusGroup Tag.E6 K) {s t : Kˣ}
    (hs : ∀ c : K, h * xUnit Tag.E6 K (e6Index 4) c * h⁻¹ = xUnit Tag.E6 K (e6Index 4) (s * c))
    (ht : ∀ c : K, h * xUnit Tag.E6 K (e6Index 5) c * h⁻¹ = xUnit Tag.E6 K (e6Index 5) (t * c))
    {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K support56) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.E6 K support56 ∧
      a2Mat₂ (h * g * h⁻¹) = diagonal ![((s * t : Kˣ) : K), (t : K), 1] * a2Mat₂ g *
        diagonal ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1] :=
  conj_torus_formula mem_support56 a2Mat₂ (fun _ hg _ hg' => a2Mat₂_mul hg hg') a2Mat₂_one
    a2Mat₂_x5 a2Mat₂_x6 a2Mat₂_y5 a2Mat₂_y6 hh hs ht hg

theorem mem_center_Q₁_iff (g : subsystemGroup Tag.E6 K support13) :
    g ∈ Subgroup.center (subsystemGroup Tag.E6 K support13) ↔
      ∃ u : Kˣ, u ^ 3 = 1 ∧
        (g : ModGL Tag.E6 K) = e6TorusPair (e6Index 0) (e6Index 2) u (u ^ 2) := by
  constructor
  · intro hg
    have hc : a2Rep₁ K g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      obtain ⟨x, rfl⟩ := a2Rep₁_surjective X
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg x]
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    rw [Fintype.card_fin] at hr
    refine ⟨cubeUnit hr, cubeUnit_pow hr, ?_⟩
    have e := a2Equiv₁_symm_scalar hr (a2Rep₁ K g) hrg.symm
    rw [← a2Equiv₁_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · rintro ⟨u, hu, hg⟩
    refine Subgroup.mem_center_iff.2 fun x => a2Rep₁_injective ?_
    rw [map_mul, map_mul]
    have hs : a2Rep₁ K g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨u, ?_, ?_⟩
      · rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
      · rw [coe_a2Rep₁, hg, a2Mat₁_center hu]
    exact (Subgroup.mem_center_iff.1 hs _)

theorem mem_center_Q₂_iff (g : subsystemGroup Tag.E6 K support56) :
    g ∈ Subgroup.center (subsystemGroup Tag.E6 K support56) ↔
      ∃ u : Kˣ, u ^ 3 = 1 ∧
        (g : ModGL Tag.E6 K) = e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2) := by
  constructor
  · intro hg
    have hc : a2Rep₂ K g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      refine Subgroup.mem_center_iff.2 fun X => ?_
      obtain ⟨x, rfl⟩ := a2Rep₂_surjective X
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg x]
    obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
    rw [Fintype.card_fin] at hr
    refine ⟨cubeUnit hr, cubeUnit_pow hr, ?_⟩
    have e := a2Equiv₂_symm_scalar hr (a2Rep₂ K g) hrg.symm
    rw [← a2Equiv₂_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · rintro ⟨u, hu, hg⟩
    refine Subgroup.mem_center_iff.2 fun x => a2Rep₂_injective ?_
    rw [map_mul, map_mul]
    have hs : a2Rep₂ K g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨u, ?_, ?_⟩
      · rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, hu, Units.val_one]
      · rw [coe_a2Rep₂, hg, a2Mat₂_center hu]
    exact (Subgroup.mem_center_iff.1 hs _)

theorem E6_native_two_A2_full_central_product_and_torus_action (K : Type) [Field K] :
    Function.Bijective (a2Rep₁ K) ∧ Function.Bijective (a2Rep₂ K) ∧
    (∀ t : K, a2Mat₁ (xUnit Tag.E6 K (e6Index 0) t) = 1 + single 0 1 t) ∧
    (∀ t : K, a2Mat₁ (xUnit Tag.E6 K (e6Index 2) t) = 1 + single 1 2 t) ∧
    (∀ t : K, a2Mat₁ (yUnit Tag.E6 K (e6Index 0) t) = 1 + single 1 0 t) ∧
    (∀ t : K, a2Mat₁ (yUnit Tag.E6 K (e6Index 2) t) = 1 + single 2 1 t) ∧
    (∀ t : K, a2Mat₂ (xUnit Tag.E6 K (e6Index 4) t) = 1 + single 0 1 t) ∧
    (∀ t : K, a2Mat₂ (xUnit Tag.E6 K (e6Index 5) t) = 1 + single 1 2 t) ∧
    (∀ t : K, a2Mat₂ (yUnit Tag.E6 K (e6Index 4) t) = 1 + single 1 0 t) ∧
    (∀ t : K, a2Mat₂ (yUnit Tag.E6 K (e6Index 5) t) = 1 + single 2 1 t) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : ModGL Tag.E6 K),
      g ∈ subsystemGroup Tag.E6 K support13 →
        baseChangeGL σ g ∈ subsystemGroup Tag.E6 L support13 ∧
          a2Mat₁ (baseChangeGL σ g) = (a2Mat₁ g).map σ) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : ModGL Tag.E6 K),
      g ∈ subsystemGroup Tag.E6 K support56 →
        baseChangeGL σ g ∈ subsystemGroup Tag.E6 L support56 ∧
          a2Mat₂ (baseChangeGL σ g) = (a2Mat₂ g).map σ) ∧
    subsystemGroup Tag.E6 K support13 = rootSpan Tag.E6 K (parabolicRoots Tag.E6 support13) ∧
    subsystemGroup Tag.E6 K support56 = rootSpan Tag.E6 K (parabolicRoots Tag.E6 support56) ∧
    (∀ g₁ ∈ subsystemGroup Tag.E6 K support13, ∀ g₂ ∈ subsystemGroup Tag.E6 K support56,
      g₁ * g₂ = g₂ * g₁) ∧
    (subsystemGroup Tag.E6 K support13 : Set (ModGL Tag.E6 K)) *
        subsystemGroup Tag.E6 K support56 =
      (subsystemGroup Tag.E6 K support56 : Set (ModGL Tag.E6 K)) *
        subsystemGroup Tag.E6 K support13 ∧
    (∀ A B : Matrix.SpecialLinearGroup (Fin 3) K, twoA2Mul K (A, B) =
      ((a2Equiv₁ K).symm A : ModGL Tag.E6 K) * ((a2Equiv₂ K).symm B : ModGL Tag.E6 K)) ∧
    Set.range (twoA2Mul K) = (subsystemGroup Tag.E6 K support13 : Set (ModGL Tag.E6 K)) *
      subsystemGroup Tag.E6 K support56 ∧
    (∀ A B : Matrix.SpecialLinearGroup (Fin 3) K, twoA2Mul K (A, B) = 1 ↔
      ∃ l : K, l ^ 3 = 1 ∧ (A : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l ∧
        (B : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) l) ∧
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) K, twoA2Mul K (A, 1) = 1 → A = 1) ∧
    (∀ B : Matrix.SpecialLinearGroup (Fin 3) K, twoA2Mul K (1, B) = 1 → B = 1) ∧
    (∀ g : subsystemGroup Tag.E6 K support13, g ∈ Subgroup.center _ ↔
      ∃ u : Kˣ, u ^ 3 = 1 ∧ (g : ModGL Tag.E6 K) = e6TorusPair (e6Index 0) (e6Index 2) u (u ^ 2)) ∧
    (∀ g : subsystemGroup Tag.E6 K support56, g ∈ Subgroup.center _ ↔
      ∃ u : Kˣ, u ^ 3 = 1 ∧ (g : ModGL Tag.E6 K) = e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2)) ∧
    (∀ u : Kˣ, u ^ 3 = 1 →
      a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) u (u ^ 2)) = scalar (Fin 3) (u : K) ∧
        a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) u (u ^ 2)) = scalar (Fin 3) (u : K)) ∧
    (∀ h ∈ torusGroup Tag.E6 K, ∃ χ : Fin Tag.E6.rank → Kˣ,
      (∀ i c, h * xUnit Tag.E6 K i c * h⁻¹ = xUnit Tag.E6 K i (χ i * c)) ∧
        ∀ i c, h * yUnit Tag.E6 K i c * h⁻¹ = yUnit Tag.E6 K i (((χ i)⁻¹ : Kˣ) * c)) ∧
    (∀ h ∈ torusGroup Tag.E6 K, ∀ s t : Kˣ,
      (∀ c : K, h * xUnit Tag.E6 K (e6Index 0) c * h⁻¹ = xUnit Tag.E6 K (e6Index 0) (s * c)) →
      (∀ c : K, h * xUnit Tag.E6 K (e6Index 2) c * h⁻¹ = xUnit Tag.E6 K (e6Index 2) (t * c)) →
      ∀ g ∈ subsystemGroup Tag.E6 K support13, h * g * h⁻¹ ∈ subsystemGroup Tag.E6 K support13 ∧
        a2Mat₁ (h * g * h⁻¹) = diagonal ![((s * t : Kˣ) : K), (t : K), 1] * a2Mat₁ g *
          diagonal ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1]) ∧
    (∀ h ∈ torusGroup Tag.E6 K, ∀ s t : Kˣ,
      (∀ c : K, h * xUnit Tag.E6 K (e6Index 4) c * h⁻¹ = xUnit Tag.E6 K (e6Index 4) (s * c)) →
      (∀ c : K, h * xUnit Tag.E6 K (e6Index 5) c * h⁻¹ = xUnit Tag.E6 K (e6Index 5) (t * c)) →
      ∀ g ∈ subsystemGroup Tag.E6 K support56, h * g * h⁻¹ ∈ subsystemGroup Tag.E6 K support56 ∧
        a2Mat₂ (h * g * h⁻¹) = diagonal ![((s * t : Kˣ) : K), (t : K), 1] * a2Mat₂ g *
          diagonal ![(((s * t)⁻¹ : Kˣ) : K), ((t⁻¹ : Kˣ) : K), 1]) ∧
    (∀ a b : Kˣ, a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) a b) =
      diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)]) ∧
    (∀ a b : Kˣ, a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) a b) =
      diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)]) ∧
    (∀ g : ModGL Tag.E6 K, g ∈ subsystemGroup Tag.E6 K support13 ⊓ torusGroup Tag.E6 K ↔
      ∃ a b : Kˣ, g = e6TorusPair (e6Index 0) (e6Index 2) a b) ∧
    (∀ g : ModGL Tag.E6 K, g ∈ subsystemGroup Tag.E6 K support56 ⊓ torusGroup Tag.E6 K ↔
      ∃ a b : Kˣ, g = e6TorusPair (e6Index 4) (e6Index 5) a b) := by
  have hker := twoA2Mul_eq_one_iff (K := K)
  refine ⟨a2Rep₁_bijective, a2Rep₂_bijective, a2Mat₁_x1, a2Mat₁_x3, a2Mat₁_y1, a2Mat₁_y3,
    a2Mat₂_x5, a2Mat₂_x6, a2Mat₂_y5, a2Mat₂_y6,
    fun L _ σ g hg => ⟨baseChangeGL_mem_subsystemGroupE6 σ hg, a2Mat₁_baseChangeGL σ hg⟩,
    fun L _ σ g hg => ⟨baseChangeGL_mem_subsystemGroupE6 σ hg, a2Mat₂_baseChangeGL σ hg⟩,
    subsystemGroup_eq_rootSpan support13, subsystemGroup_eq_rootSpan support56,
    fun g₁ h₁ g₂ h₂ => (commute_Q₁_Q₂ h₁ h₂).eq, Q₁_mul_Q₂_comm, twoA2Mul_apply,
    range_twoA2Mul, hker, fun A hA => ?_, fun B hB => ?_, mem_center_Q₁_iff, mem_center_Q₂_iff,
    fun u hu => ⟨a2Mat₁_center hu, a2Mat₂_center hu⟩,
    fun h hh => exists_simple_root_characters hh,
    fun h hh s t hs ht g hg => a2Mat₁_conj_torus hh hs ht hg,
    fun h hh s t hs ht g hg => a2Mat₂_conj_torus hh hs ht hg,
    a2Mat₁_torus, a2Mat₂_torus, fun g => mem_Q₁_inf_torusGroup,
    fun g => mem_Q₂_inf_torusGroup⟩
  · obtain ⟨l, -, hlA, hl1⟩ := (hker A 1).1 hA
    have hl : l = 1 := by
      have e := congrFun (congrFun hl1 0) 0
      simpa using e.symm
    refine Subtype.ext ?_
    rw [hlA, hl, map_one]
    rfl
  · obtain ⟨l, -, hl1, hlB⟩ := (hker 1 B).1 hB
    have hl : l = 1 := by
      have e := congrFun (congrFun hl1 0) 0
      simpa using e.symm
    refine Subtype.ext ?_
    rw [hlB, hl, map_one]
    rfl

end CFSG.RankThree.E6

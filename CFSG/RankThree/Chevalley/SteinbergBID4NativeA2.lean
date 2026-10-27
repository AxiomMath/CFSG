module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2Rep

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {K : Type} [Field K]

theorem borel_apply_d4A2Vec_eq_zero {c : ModGL Tag.D4 K} (hc : c ∈ borelGroup Tag.D4 K)
    {j j' : Fin 3} (h : j < j') :
    (c : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K j) (d4A2Label j') = 0 :=
  (triangular_borel_structure.{0, 0} Tag.D4 K).2.2.2.2.2.2.2.2.2.1 c hc (d4A2Label j')
    (d4A2Label j) ((d4A2Label_precedes_iff j j').2 h)

theorem d4A2_one_add_mul_one_add {A S : Matrix (Fin 3) (Fin 3) K} (h : A * S = 0) :
    (1 + A) * (1 + S) = 1 + (A + S) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h, add_zero]
  abel

theorem prod_d4A2Pos (x : Fin 3 → K) :
    (List.ofFn fun m => (1 + single (d4A2PosRow m) (d4A2PosCol m) (x m) :
      Matrix (Fin 3) (Fin 3) K)).prod =
      1 + (single 1 2 (x 0) + (single 0 1 (x 1) + single 0 2 (x 2))) := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  change (1 + single 1 2 (x 0)) * ((1 + single 0 1 (x 1)) * (1 + single 0 2 (x 2))) = _
  have z1 : (single 0 1 (x 1) : Matrix (Fin 3) (Fin 3) K) * single 0 2 (x 2) = 0 :=
    single_mul_single_of_ne _ _ _ _ (by decide) _
  have z2 : (single 1 2 (x 0) : Matrix (Fin 3) (Fin 3) K) * single 0 1 (x 1) = 0 :=
    single_mul_single_of_ne _ _ _ _ (by decide) _
  have z3 : (single 1 2 (x 0) : Matrix (Fin 3) (Fin 3) K) * single 0 2 (x 2) = 0 :=
    single_mul_single_of_ne _ _ _ _ (by decide) _
  rw [d4A2_one_add_mul_one_add z1,
    d4A2_one_add_mul_one_add (by rw [Matrix.mul_add, z2, z3, add_zero])]

theorem d4A2Mat_list_prod (l : List (ModGL Tag.D4 K))
    (hl : ∀ g ∈ l, g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    d4A2Mat l.prod = (l.map d4A2Mat).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, d4A2Mat_one]
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      d4A2Mat_mul (Subgroup.list_prod_mem _ fun h hh => hl h (List.mem_cons_of_mem g hh)),
      ih fun h hh => hl h (List.mem_cons_of_mem g hh)]

theorem eq_one_of_d4A2Mat_mul_eq_one {t u : ModGL Tag.D4 K}
    (ht : t ∈ subsystemTorus Tag.D4 K d4SuppA2)
    (hu : u ∈ parabolicLeviUnipotent Tag.D4 K d4SuppA2) (h : d4A2Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_d4A2.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) d4A2PosRoot
    d4A2PosRoot_injective range_d4A2PosRoot).surjOn hu
  choose ε hε hfam using d4A2RootFamily_all (K := K)
  have hrc : ∀ m, d4A2PosRow m ≠ d4A2PosCol m := fun m => (d4A2PosRow_lt_col m).ne
  set y : Fin 3 → K := fun m => (ε (d4A2PosRow m) (d4A2PosCol m) (hrc m) : K) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.D4 K (d4A2PosRoot m) (x m),
      g ∈ subsystemGroup Tag.D4 K d4SuppA2 := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_d4A2Group (d4A2PosRoot_mem m) _
  have hu' : d4A2Mat (List.ofFn fun m => pinnedX Tag.D4 K (d4A2PosRoot m) (x m)).prod =
      1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2))) := by
    rw [d4A2Mat_list_prod _ hlist, List.map_ofFn, ← prod_d4A2Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, d4A2PosRoot_eq, hfam]
  rw [d4A2Mat_mul (Subgroup.list_prod_mem _ hlist), d4A2Mat_d4A2TorusElt, hu'] at h
  have e : ∀ p q, (Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] *
      (1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2)))) :
        Matrix (Fin 3) (Fin 3) K) p q = (1 : Matrix (Fin 3) (Fin 3) K) p q := fun p q => by
    rw [h]
  have d0 := e 0 0
  have d1 := e 1 1
  simp [Matrix.diagonal_mul, Matrix.add_apply] at d0 d1
  have ha : a = 1 := Units.ext (by simpa using d0)
  subst ha
  have hb : b = 1 := Units.ext (by simpa using d1)
  subst hb
  have o0 := e 1 2
  have o1 := e 0 1
  have o2 := e 0 2
  simp [Matrix.diagonal_mul, Matrix.add_apply] at o0 o1 o2
  have hy0 : ∀ m, y m = 0 := by
    intro m
    fin_cases m
    exacts [o0, o1, o2]
  have hx0 : x = 0 := by
    funext m
    have h0 := hy0 m
    rw [hy] at h0
    rcases hε (d4A2PosRow m) (d4A2PosCol m) (hrc m) with h1 | h1 <;>
      (simp only [h1] at h0; simpa using h0)
  subst hx0
  refine ⟨d4A2TorusElt_one, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem d4A2Rep_injective : Function.Injective (d4A2Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : d4A2Mat (g : ModGL Tag.D4 K) = 1 := congrArg Subtype.val hg
  have hfixv : ∀ k, ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K k) =
      d4A2Vec K k := by
    intro k
    rw [apply_d4A2Vec g.2, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ d4A2Module K,
      ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) m = m := by
    intro m hm
    have e := eq_sum_of_mem_d4A2Module hm
    calc ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) m =
        ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))
          (∑ k, m (d4A2Label k) • d4A2Vec K k) := by rw [← e]
      _ = ∑ k, m (d4A2Label k) • d4A2Vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  have hgS : (g : ModGL Tag.D4 K) ∈
      (subsystemGroup Tag.D4 K d4SuppA2 : Set (ModGL Tag.D4 K)) := g.2
  rw [(subsystem_root_group_bruhat (τ := Tag.D4) (K := K) (A := d4SuppA2)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.D4 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.D4 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.D4 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.D4) (K := K) (A := d4SuppA2)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.D4) K w : Module.End K (RootModule Tag.D4 K))
      (d4A2Vec K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))
        (d4A2Vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.D4) K w = b⁻¹ * (g : ModGL Tag.D4 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_d4A2Module_of_mem (inv_mem hvS) (d4A2Vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', d4A2Weight j' = w • d4A2Weight j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec (K := K) w (isRoot_d4A2Weight j)
    have h0 := borel_apply_d4A2Vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← rootVec_d4A2Weight, hne, ← hj', rootVec_d4A2Weight, Finsupp.smul_apply,
      d4A2Vec_apply, ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_d4A2Weight hw (smul_d4A2Weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.D4 K (∅ : Set (Fin Tag.D4.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.D4 K d4SuppA2 : Set (ModGL Tag.D4 K)) *
      (parabolicLeviUnipotent Tag.D4 K d4SuppA2 : Set (ModGL Tag.D4 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.D4) (K := K) (A := d4SuppA2)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := eq_one_of_d4A2Mat_mul_eq_one ht hu (by rw [hgbv]; exact hmat)
  refine Subtype.ext ?_
  rw [Subgroup.coe_one, ← hgbv, h1.1, h1.2, mul_one]

theorem baseChangeGL_mem_d4A2Group {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.D4 K}
    (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    baseChangeGL σ g ∈ subsystemGroup Tag.D4 L d4SuppA2 := by
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

theorem d4A2_map_single_ringHom {L : Type} [Field L] (σ : K →+* L) (p q : Fin 3) (c : K) :
    (single p q c : Matrix (Fin 3) (Fin 3) K).map σ = single p q (σ c) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem d4A2Mat_baseChangeGL {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.D4 K}
    (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    d4A2Mat (baseChangeGL σ g) = (d4A2Mat g).map σ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · rw [d4A2Mat_x0, d4A2Mat_x0, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, d4A2_map_single_ringHom]
      · rw [d4A2Mat_x2, d4A2Mat_x2, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, d4A2_map_single_ringHom]
    · rw [baseChangeGL_yUnit]
      rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
      · rw [d4A2Mat_y0, d4A2Mat_y0, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, d4A2_map_single_ringHom]
      · rw [d4A2Mat_y2, d4A2Mat_y2, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, d4A2_map_single_ringHom]
  | one => rw [map_one, d4A2Mat_one, d4A2Mat_one, Matrix.map_one _ σ.map_zero σ.map_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, d4A2Mat_mul (baseChangeGL_mem_d4A2Group σ hy), ihx, ihy, d4A2Mat_mul hy,
      Matrix.map_mul]
  | inv x hx ih =>
    have hL := baseChangeGL_mem_d4A2Group σ hx
    rw [map_inv, d4A2Mat_inv hL, ih]
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, ← d4A2Mat_mul hx, inv_mul_cancel, d4A2Mat_one,
      Matrix.map_one _ σ.map_zero σ.map_one]

theorem d4A2Mat_conj_of_gen {D D' : Matrix (Fin 3) (Fin 3) K} (hDD' : D * D' = 1)
    (hD'D : D' * D = 1) (h : ModGL Tag.D4 K)
    (hgen : ∀ i ∈ d4SuppA2, ∀ c : K,
      (h * xUnit Tag.D4 K i c * h⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
        d4A2Mat (h * xUnit Tag.D4 K i c * h⁻¹) = D * d4A2Mat (xUnit Tag.D4 K i c) * D') ∧
      (h * yUnit Tag.D4 K i c * h⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
        d4A2Mat (h * yUnit Tag.D4 K i c * h⁻¹) = D * d4A2Mat (yUnit Tag.D4 K i c) * D'))
    {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
      d4A2Mat (h * g * h⁻¹) = D * d4A2Mat g * D' := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · exact (hgen i hi c).1
    · exact (hgen i hi c).2
  | one =>
    rw [mul_one, mul_inv_cancel, d4A2Mat_one, Matrix.mul_one, hDD']
    exact ⟨one_mem _, rfl⟩
  | mul x y _ hy ihx ihy =>
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    refine ⟨mul_mem ihx.1 ihy.1, ?_⟩
    rw [d4A2Mat_mul ihy.1, ihx.2, ihy.2, d4A2Mat_mul hy]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D' D, hD'D, Matrix.one_mul]
  | inv x hx ih =>
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    refine ⟨inv_mem ih.1, ?_⟩
    have h1 : d4A2Mat (h * x * h⁻¹)⁻¹ * d4A2Mat (h * x * h⁻¹) = 1 := by
      rw [← d4A2Mat_mul ih.1, inv_mul_cancel, d4A2Mat_one]
    have h2 : D * d4A2Mat x⁻¹ * D' * d4A2Mat (h * x * h⁻¹) = 1 := by
      rw [ih.2]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D' D, hD'D, Matrix.one_mul, ← Matrix.mul_assoc (d4A2Mat x⁻¹),
        ← d4A2Mat_mul hx, inv_mul_cancel, d4A2Mat_one, Matrix.one_mul, hDD']
    exact (Matrix.inv_eq_left_inv h1).symm.trans (Matrix.inv_eq_left_inv h2)

theorem d4A2_diagonal_conj_one_add_single {d d' : Fin 3 → K} (hd : ∀ k, d k * d' k = 1)
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

theorem eq_rootDiag_of_apply_single {l : Fin Tag.D4.rank → Kˣ}
    (hh : rootDiagUnit Tag.D4 l ∈ torusGroup Tag.D4 K) {i : Fin Tag.D4.rank} {a : K}
    (ha : ((rootDiagUnit Tag.D4 l : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))
      (rootVec Tag.D4 K (Pi.single i 1)) = a • rootVec Tag.D4 K (Pi.single i 1)) :
    a = l i := by
  rw [← torusRootChar_eq_of_apply (isRoot_single Tag.D4 i) ha]
  refine (eq_torusRootChar_of_conj hh (isRoot_single Tag.D4 i) fun c => ?_).symm
  rw [pinnedX_single, pinnedX_single]
  exact (root_diagonal_conjugation Tag.D4 K l).1 i c

theorem d4A2Mat_conj_torus {h : ModGL Tag.D4 K} (hh : h ∈ torusGroup Tag.D4 K) {a b : K}
    (ha : (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 0 1)) =
      a • rootVec Tag.D4 K (Pi.single 0 1))
    (hb : (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 2 1)) =
      b • rootVec Tag.D4 K (Pi.single 2 1))
    {g : ModGL Tag.D4 K} (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    h * g * h⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
      d4A2Mat (h * g * h⁻¹) =
        diagonal ![a * b, b, 1] * d4A2Mat g * diagonal ![(a * b)⁻¹, b⁻¹, 1] := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation Tag.D4 K l
  obtain rfl := eq_rootDiag_of_apply_single hh ha
  obtain rfl := eq_rootDiag_of_apply_single hh hb
  have h0 := (l 0).ne_zero
  have h2 := (l 2).ne_zero
  have hd : ∀ k, (![(l 0 : K) * l 2, (l 2 : K), 1] : Fin 3 → K) k *
      ![((l 0 : K) * l 2)⁻¹, (l 2 : K)⁻¹, 1] k = 1 := by
    intro k
    fin_cases k
    · exact mul_inv_cancel₀ (mul_ne_zero h0 h2)
    · exact mul_inv_cancel₀ h2
    · exact mul_one 1
  have hd' : ∀ k, (![((l 0 : K) * l 2)⁻¹, (l 2 : K)⁻¹, 1] : Fin 3 → K) k *
      ![(l 0 : K) * l 2, (l 2 : K), 1] k = 1 := fun k => by rw [mul_comm]; exact hd k
  have hDD : ∀ {d d' : Fin 3 → K}, (∀ k, d k * d' k = 1) → diagonal d * diagonal d' = 1 :=
    fun h => by rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg _ (funext h)
  refine d4A2Mat_conj_of_gen (hDD hd) (hDD hd') _ (fun i hi c => ?_) hg
  rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
  · rw [hx, hy, d4A2Mat_x0, d4A2Mat_x0, d4A2Mat_y0, d4A2Mat_y0,
      d4A2_diagonal_conj_one_add_single hd, d4A2_diagonal_conj_one_add_single hd]
    refine ⟨⟨xUnit_mem_subsystemGroup zero_mem_d4SuppA2 _, ?_⟩,
      ⟨yUnit_mem_subsystemGroup zero_mem_d4SuppA2 _, ?_⟩⟩
    · congr 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
    · congr 2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_inv_eq_inv_val]
      field_simp
  · rw [hx, hy, d4A2Mat_x2, d4A2Mat_x2, d4A2Mat_y2, d4A2Mat_y2,
      d4A2_diagonal_conj_one_add_single hd, d4A2_diagonal_conj_one_add_single hd]
    refine ⟨⟨xUnit_mem_subsystemGroup two_mem_d4SuppA2 _, ?_⟩,
      ⟨yUnit_mem_subsystemGroup two_mem_d4SuppA2 _, ?_⟩⟩
    · congr 2
      simp
    · congr 2
      simp [mul_comm]

theorem d4A2Mat_conj_torus_mul {h : ModGL Tag.D4 K} (hh : h ∈ torusGroup Tag.D4 K) {a b : K}
    (ha : (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 0 1)) =
      a • rootVec Tag.D4 K (Pi.single 0 1))
    (hb : (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 2 1)) =
      b • rootVec Tag.D4 K (Pi.single 2 1))
    {z g : ModGL Tag.D4 K} (hz : z ∈ subsystemGroup Tag.D4 K d4SuppA2)
    (hg : g ∈ subsystemGroup Tag.D4 K d4SuppA2) :
    h * z * g * (h * z)⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
      d4A2Mat (h * z * g * (h * z)⁻¹) = (diagonal ![a * b, b, 1] * d4A2Mat z) * d4A2Mat g *
        (diagonal ![a * b, b, 1] * d4A2Mat z)⁻¹ := by
  have e : h * z * g * (h * z)⁻¹ = h * (z * g * z⁻¹) * h⁻¹ := by group
  have hzg : z * g * z⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 :=
    mul_mem (mul_mem hz hg) (inv_mem hz)
  obtain ⟨hmem, hmat⟩ := d4A2Mat_conj_torus hh ha hb hzg
  refine ⟨e ▸ hmem, ?_⟩
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  obtain rfl := eq_rootDiag_of_apply_single hh ha
  obtain rfl := eq_rootDiag_of_apply_single hh hb
  have hDD' : diagonal ![(l 0 : K) * l 2, (l 2 : K), 1] *
      diagonal ![((l 0 : K) * l 2)⁻¹, (l 2 : K)⁻¹, 1] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    refine congrArg _ (funext fun k => ?_)
    fin_cases k
    · exact mul_inv_cancel₀ (mul_ne_zero (l 0).ne_zero (l 2).ne_zero)
    · exact mul_inv_cancel₀ (l 2).ne_zero
    · exact mul_one 1
  rw [e, hmat, d4A2Mat_mul (inv_mem hz), d4A2Mat_mul hg, d4A2Mat_inv hz, Matrix.mul_inv_rev,
    Matrix.inv_eq_right_inv hDD']
  simp only [Matrix.mul_assoc]

theorem D4_native_A2_root_subgroup_faithful_SL3 (K : Type) [Field K] :
    (∀ g ∈ subsystemGroup Tag.D4 K d4SuppA2, ∀ m ∈ d4A2Module K,
      (g : Module.End K (RootModule Tag.D4 K)) m ∈ d4A2Module K) ∧
    Function.Bijective (d4A2Rep K) ∧
    (∀ (g : subsystemGroup Tag.D4 K d4SuppA2) (j : Fin 3),
      ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) (d4A2Vec K j) =
        ∑ i, (d4A2Rep K g : Matrix (Fin 3) (Fin 3) K) i j • d4A2Vec K i) ∧
    (∀ c : K, d4A2Mat (xUnit Tag.D4 K 0 c) = 1 + single 0 1 c) ∧
    (∀ c : K, d4A2Mat (yUnit Tag.D4 K 0 c) = 1 + single 1 0 c) ∧
    (∀ c : K, d4A2Mat (xUnit Tag.D4 K 2 c) = 1 + single 1 2 c) ∧
    (∀ c : K, d4A2Mat (yUnit Tag.D4 K 2 c) = 1 + single 2 1 c) ∧
    (∀ t u : Kˣ, d4A2Mat (d4A2TorusElt t u) =
      diagonal ![(t : K), ((t⁻¹ * u : Kˣ) : K), ((u⁻¹ : Kˣ) : K)]) ∧
    subsystemGroup Tag.D4 K d4SuppA2 = rootSpan Tag.D4 K d4A2Sigma ∧
    (∀ g : ModGL Tag.D4 K, g ∈ subsystemGroup Tag.D4 K d4SuppA2 ⊓ torusGroup Tag.D4 K ↔
      ∃ t u : Kˣ, g = d4A2TorusElt t u) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : subsystemGroup Tag.D4 K d4SuppA2),
      ∃ hσ : baseChangeGL σ (g : ModGL Tag.D4 K) ∈ subsystemGroup Tag.D4 L d4SuppA2,
        (d4A2Rep L ⟨_, hσ⟩ : Matrix (Fin 3) (Fin 3) L) =
          (d4A2Rep K g : Matrix (Fin 3) (Fin 3) K).map σ) ∧
    ∀ h ∈ torusGroup Tag.D4 K, ∀ a b : K,
      (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 0 1)) =
        a • rootVec Tag.D4 K (Pi.single 0 1) →
      (h : Module.End K (RootModule Tag.D4 K)) (rootVec Tag.D4 K (Pi.single 2 1)) =
        b • rootVec Tag.D4 K (Pi.single 2 1) →
      (∀ g ∈ subsystemGroup Tag.D4 K d4SuppA2, h * g * h⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2) ∧
      ∀ z ∈ subsystemGroup Tag.D4 K d4SuppA2, ∀ g ∈ subsystemGroup Tag.D4 K d4SuppA2,
        h * z * g * (h * z)⁻¹ ∈ subsystemGroup Tag.D4 K d4SuppA2 ∧
          d4A2Mat (h * z * g * (h * z)⁻¹) = (diagonal ![a * b, b, 1] * d4A2Mat z) * d4A2Mat g *
            (diagonal ![a * b, b, 1] * d4A2Mat z)⁻¹ := by
  refine ⟨fun g hg m hm => mem_d4A2Module_of_mem hg hm, ⟨d4A2Rep_injective, d4A2Rep_surjective⟩,
    fun g j => apply_d4A2Vec g.2 j, d4A2Mat_x0, d4A2Mat_y0, d4A2Mat_x2, d4A2Mat_y2,
    d4A2Mat_d4A2TorusElt, ?_, fun g => ?_, fun L _ σ g =>
      ⟨baseChangeGL_mem_d4A2Group σ g.2, d4A2Mat_baseChangeGL σ g.2⟩,
    fun h hh a b ha hb => ⟨fun g hg => (d4A2Mat_conj_torus hh ha hb hg).1,
      fun z hz g hg => d4A2Mat_conj_torus_mul hh ha hb hz hg⟩⟩
  · rw [subsystemGroup_eq_rootSpan, parabolicRoots_d4SuppA2]
  · rw [subsystemGroup_inf_torusGroup, mem_subsystemTorus_d4A2]

end CFSG.RankThree.Chevalley

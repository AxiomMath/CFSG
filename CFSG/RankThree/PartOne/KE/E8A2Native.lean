module

public import CFSG.RankThree.PartOne.KE.E8A2NativeModule
public import CFSG.RankThree.PartOne.KE.E7A2Native

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped commutatorElement Pointwise

variable {K : Type} [Field K]

theorem e8a2TorusElt_mul (a b a' b' : Kˣ) :
    e8a2TorusElt a b * e8a2TorusElt a' b' = e8a2TorusElt (a * a') (b * b') := by
  simp only [e8a2TorusElt, torusElt_mul]
  have h := torusElt_mul_comm (τ := Tag.E8) (R := K) (e8Index 2) (e8Index 0) b a'
  calc torusElt Tag.E8 K (e8Index 0) a * torusElt Tag.E8 K (e8Index 2) b *
        (torusElt Tag.E8 K (e8Index 0) a' * torusElt Tag.E8 K (e8Index 2) b')
      = torusElt Tag.E8 K (e8Index 0) a * (torusElt Tag.E8 K (e8Index 2) b *
          torusElt Tag.E8 K (e8Index 0) a') * torusElt Tag.E8 K (e8Index 2) b' := by group
    _ = _ := by rw [h]; group

theorem e8a2TorusElt_one : e8a2TorusElt (1 : Kˣ) 1 = (1 : ModGL Tag.E8 K) := by
  simp only [e8a2TorusElt, torusElt_one, mul_one]

theorem e8a2TorusElt_inv (a b : Kˣ) :
    (e8a2TorusElt a b : ModGL Tag.E8 K)⁻¹ = e8a2TorusElt a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [e8a2TorusElt_mul, mul_inv_cancel, mul_inv_cancel, e8a2TorusElt_one]

theorem mem_subsystemTorus_e8a2 {g : ModGL Tag.E8 K} :
    g ∈ subsystemTorus Tag.E8 K e8support13 ↔ ∃ a b : Kˣ, g = e8a2TorusElt a b := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, t, rfl⟩ := hx
      rcases (mem_e8support13 i).1 hi with rfl | rfl
      · exact ⟨t, 1, by simp only [e8a2TorusElt, torusElt_one, mul_one]⟩
      · exact ⟨1, t, by simp only [e8a2TorusElt, torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, e8a2TorusElt_one.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨_, _, e8a2TorusElt_mul a b a' b'⟩
    | inv x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨_, _, e8a2TorusElt_inv a b⟩
  · rintro ⟨a, b, rfl⟩
    exact mul_mem (torusElt_mem_subsystemTorus mem_e8support13_0 a)
      (torusElt_mem_subsystemTorus mem_e8support13_2 b)

theorem e8a2Weight_height : ∀ i j : Fin 3,
    (height (e8a2Weight j) < height (e8a2Weight i) ↔ i < j) ∧
      (height (e8a2Weight i) = height (e8a2Weight j) ↔ i = j) := by
  decide +kernel

theorem e8a2Label_precedes_iff (i j : Fin 3) : (e8a2Label i).Precedes (e8a2Label j) ↔ i < j := by
  simp only [Label.Precedes, Label.weight]
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact ((e8a2Weight_height i j).1).1 h
    · obtain rfl := ((e8a2Weight_height i j).2).1 h
      exact absurd h' (lt_irrefl _)
  · intro h
    exact Or.inl (((e8a2Weight_height i j).1).2 h)

theorem e8Index_mem_e8support13_iff (i : Fin 8) : e8Index i ∈ e8support13 ↔ (i = 0 ∨ i = 2) :=
  mem_e8support13 (e8Index i)

theorem e8a2Weight_outside : ∀ k : Fin 3, ∀ i : Fin 8, ¬(i = 0 ∨ i = 2) →
    e8a2Weight k (e8Index i) = e8a2Weight 0 (e8Index i) := by
  decide +kernel

theorem exists_e8a2Weight_of_e8RootVec : ∀ m : Fin 240,
    (∀ i : Fin 8, ¬(i = 0 ∨ i = 2) → e8RootVec m (e8Index i) = e8a2Weight 0 (e8Index i)) →
      ∃ k, e8a2Weight k = e8RootVec m := by
  decide +kernel

theorem exists_e8a2Weight_smul {w : WeylGroup Tag.E8}
    (hw : w ∈ parabolicWeylGroup Tag.E8 e8support13) (k : Fin 3) :
    ∃ k', e8a2Weight k' = w • e8a2Weight k := by
  obtain ⟨m, hm⟩ := isRoot_iff_exists_e8RootVec.1 (IsRoot.smul (isRoot_e8a2Weight k) w)
  obtain ⟨k', hk'⟩ := exists_e8a2Weight_of_e8RootVec m (fun i hi => by
    have hi' : e8Index i ∉ e8support13 := fun h => hi ((e8Index_mem_e8support13_iff i).1 h)
    rw [hm, smul_apply_of_mem_parabolicWeylGroup hw _ hi', e8a2Weight_outside k i hi])
  exact ⟨k', hk'.trans hm⟩

theorem smul_e8a2Weight_eq_of_not_lt {w : WeylGroup Tag.E8}
    (hw : w ∈ parabolicWeylGroup Tag.E8 e8support13)
    (hprec : ∀ j j', e8a2Weight j' = w • e8a2Weight j → ¬j < j') (j : Fin 3) :
    w • e8a2Weight j = e8a2Weight j := by
  by_contra hj
  classical
  set M : Finset (Fin 3) := Finset.univ.filter fun k => w • e8a2Weight k ≠ e8a2Weight k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : w • e8a2Weight k ≠ e8a2Weight k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := exists_e8a2Weight_smul hw k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply e8a2Weight_injective
    apply smul_left_cancel w
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)

theorem single_eq_e8a2Weight_sub :
    (Pi.single (e8Index 0) 1 : Fin Tag.E8.rank → ℤ) = e8a2Weight 0 - e8a2Weight 1 ∧
    (Pi.single (e8Index 2) 1 : Fin Tag.E8.rank → ℤ) = e8a2Weight 1 - e8a2Weight 2 := by
  decide +kernel

theorem eq_one_of_smul_e8a2Weight {w : WeylGroup Tag.E8}
    (hw : w ∈ parabolicWeylGroup Tag.E8 e8support13) (h : ∀ k, w • e8a2Weight k = e8a2Weight k) :
    w = 1 := by
  obtain ⟨e0, e2⟩ := single_eq_e8a2Weight_sub
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ e8support13
  · have hfix : w • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) = Pi.single i 1 := by
      rcases (mem_e8support13 i).1 hi with rfl | rfl
      · rw [e0, smul_sub, h, h]
      · rw [e2, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single Tag.E8 i) w
    have hcoord : (w • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hw _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

theorem borel_apply_e8a2Vec_eq_zero {c : ModGL Tag.E8 K} (hc : c ∈ borelGroup Tag.E8 K)
    {j j' : Fin 3} (h : j < j') :
    (c : Module.End K (RootModule Tag.E8 K)) (e8a2Vec K j) (e8a2Label j') = 0 :=
  (triangular_borel_structure.{0, 0} Tag.E8 K).2.2.2.2.2.2.2.2.2.1 c hc (e8a2Label j')
    (e8a2Label j) ((e8a2Label_precedes_iff j j').2 h)

@[expose] def e8a2PosRoot : Fin 3 → Fin Tag.E8.rank → ℤ :=
  ![chainRoot e8chain13 1 2, chainRoot e8chain13 0 1, chainRoot e8chain13 0 2]

theorem e8a2PosRoot_injective : Function.Injective e8a2PosRoot := by
  intro k k' h
  revert k k'
  decide +kernel

theorem e8chainRoot13_height_pos : ∀ k l : Fin 3, k ≠ l →
    (0 < height (chainRoot e8chain13 k l) ↔ k < l) := by
  decide +kernel

theorem exists_e8a2PosRoot :
    ∀ k l : Fin 3, k < l → ∃ m, e8a2PosRoot m = chainRoot e8chain13 k l := by
  decide +kernel

theorem range_e8a2PosRoot : Set.range e8a2PosRoot = parabolicPosRoots Tag.E8 e8support13 := by
  ext β
  constructor
  · rintro ⟨m, rfl⟩
    have h : ∀ m : Fin 3, ∃ k l : Fin 3, k < l ∧ e8a2PosRoot m = chainRoot e8chain13 k l := by
      decide +kernel
    obtain ⟨k, l, hkl, hm⟩ := h m
    rw [hm]
    have hmem := e8chainRoot13_mem_parabolicRoots hkl.ne
    exact ⟨hmem, hmem.1, (e8chainRoot13_height_pos k l hkl.ne).2 hkl⟩
  · rintro ⟨hβ, -, hpos⟩
    obtain ⟨k, l, hkl, rfl⟩ := exists_e8chainRoot13_of_mem hβ
    exact exists_e8a2PosRoot k l ((e8chainRoot13_height_pos k l hkl).1 hpos)

theorem e8a2PosRoot_eq (m : Fin 3) :
    e8a2PosRoot m = chainRoot e8chain13 (a2PosRow m) (a2PosCol m) := by
  fin_cases m <;> rfl

theorem e8a2Mat_list_prod (l : List (ModGL Tag.E8 K))
    (hl : ∀ g ∈ l, g ∈ subsystemGroup Tag.E8 K e8support13) :
    e8a2Mat l.prod = (l.map e8a2Mat).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, e8a2Mat_one]
  | cons g l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      e8a2Mat_mul (hl g List.mem_cons_self) (Subgroup.list_prod_mem _ fun h hh => hl h
        (List.mem_cons_of_mem g hh)), ih fun h hh => hl h (List.mem_cons_of_mem g hh)]

theorem e8a2PosRoot_mem (m : Fin 3) : e8a2PosRoot m ∈ parabolicRoots Tag.E8 e8support13 :=
  (show e8a2PosRoot m ∈ parabolicPosRoots Tag.E8 e8support13 from
    range_e8a2PosRoot ▸ ⟨m, rfl⟩).1

theorem eq_one_of_e8a2Mat_mul_eq_one {t u : ModGL Tag.E8 K}
    (ht : t ∈ subsystemTorus Tag.E8 K e8support13)
    (hu : u ∈ parabolicLeviUnipotent Tag.E8 K e8support13) (h : e8a2Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_e8a2.1 ht
  obtain ⟨x, -, rfl⟩ := (bijOn_prod_pinnedX_parabolicPosRoots (K := K) e8a2PosRoot
    e8a2PosRoot_injective range_e8a2PosRoot).surjOn hu
  choose ε hε hfam using e8a2RootFamily_all (K := K)
  have hrc : ∀ m, a2PosRow m ≠ a2PosCol m := fun m => (a2PosRow_lt_col m).ne
  set y : Fin 3 → K := fun m => (ε (a2PosRow m) (a2PosCol m) (hrc m) : K) * x m with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.E8 K (e8a2PosRoot m) (x m),
      g ∈ subsystemGroup Tag.E8 K e8support13 := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact pinnedX_mem_e8a2Group (e8a2PosRoot_mem m) _
  have hu' : e8a2Mat (List.ofFn fun m => pinnedX Tag.E8 K (e8a2PosRoot m) (x m)).prod =
      1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2))) := by
    rw [e8a2Mat_list_prod _ hlist, List.map_ofFn, ← prod_a2Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, e8a2PosRoot_eq, hfam]
  rw [e8a2Mat_mul (e8a2TorusElt_mem a b) (Subgroup.list_prod_mem _ hlist), e8a2Mat_e8a2TorusElt,
    hu'] at h
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
    rcases hε (a2PosRow m) (a2PosCol m) (hrc m) with h1 | h1 <;>
      (simp only [h1] at h0; simpa using h0)
  subst hx0
  refine ⟨e8a2TorusElt_one, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

theorem e8a2Rep_injective : Function.Injective (e8a2Rep K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmat : e8a2Mat (g : ModGL Tag.E8 K) = 1 := congrArg Subtype.val hg
  have hfixv : ∀ k, ((g : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) (e8a2Vec K k) =
      e8a2Vec K k := by
    intro k
    rw [apply_e8a2Vec g.2, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ e8a2Module K,
      ((g : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) m = m := by
    intro m hm
    have e := eq_sum_of_mem_e8a2Module hm
    calc ((g : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) m =
        ((g : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K))
          (∑ k, m (e8a2Label k) • e8a2Vec K k) := by rw [← e]
      _ = ∑ k, m (e8a2Label k) • e8a2Vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  have hgS : (g : ModGL Tag.E8 K) ∈
      (subsystemGroup Tag.E8 K e8support13 : Set (ModGL Tag.E8 K)) := g.2
  rw [(subsystem_root_group_bruhat (τ := Tag.E8) (K := K) (A := e8support13)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w, hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup Tag.E8 K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent Tag.E8 K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup Tag.E8 K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup Tag.E8 K e8support13 :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E8) (K := K) (A := e8support13)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem Tag.E8) K w : Module.End K (RootModule Tag.E8 K))
      (e8a2Vec K j) = ((b⁻¹ * v⁻¹ : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K))
        (e8a2Vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem Tag.E8) K w = b⁻¹ * (g : ModGL Tag.E8 K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (mem_e8a2Module_of_mem (inv_mem hvS) (e8a2Vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j', e8a2Weight j' = w • e8a2Weight j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := canonicalRep_rootVec_of_isRoot (K := K) w (isRoot_e8a2Weight j)
    have h0 := borel_apply_e8a2Vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← rootVec_e8a2Weight, hne, ← hj', rootVec_e8a2Weight, Finsupp.smul_apply,
      e8a2Vec_apply, ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w = 1 := eq_one_of_smul_e8a2Weight hw (smul_e8a2Weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan Tag.E8 K (∅ : Set (Fin Tag.E8.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus Tag.E8 K e8support13 : Set (ModGL Tag.E8 K)) *
      (parabolicLeviUnipotent Tag.E8 K e8support13 : Set (ModGL Tag.E8 K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := Tag.E8) (K := K) (A := e8support13)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := eq_one_of_e8a2Mat_mul_eq_one ht hu (by rw [hgbv]; exact hmat)
  refine Subtype.ext ?_
  rw [Subgroup.coe_one, ← hgbv, h1.1, h1.2, mul_one]

theorem baseChangeGL_mem_e8a2Group {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E8 K}
    (hg : g ∈ subsystemGroup Tag.E8 K e8support13) :
    baseChangeGL σ g ∈ subsystemGroup Tag.E8 L e8support13 := by
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

theorem e8a2Mat_baseChangeGL {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E8 K}
    (hg : g ∈ subsystemGroup Tag.E8 K e8support13) :
    e8a2Mat (baseChangeGL σ g) = (e8a2Mat g).map σ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, c, rfl | rfl⟩ := hx
    · rw [baseChangeGL_xUnit]
      rcases (mem_e8support13 i).1 hi with rfl | rfl
      · rw [e8a2Mat_x1, e8a2Mat_x1, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, a2_map_single]
      · rw [e8a2Mat_x3, e8a2Mat_x3, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, a2_map_single]
    · rw [baseChangeGL_yUnit]
      rcases (mem_e8support13 i).1 hi with rfl | rfl
      · rw [e8a2Mat_y1, e8a2Mat_y1, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, a2_map_single]
      · rw [e8a2Mat_y3, e8a2Mat_y3, Matrix.map_add _ (map_add σ),
          Matrix.map_one _ σ.map_zero σ.map_one, a2_map_single]
  | one => rw [map_one, e8a2Mat_one, e8a2Mat_one, Matrix.map_one _ σ.map_zero σ.map_one]
  | mul x y hx hy ihx ihy =>
    rw [map_mul, e8a2Mat_mul (baseChangeGL_mem_e8a2Group σ hx) (baseChangeGL_mem_e8a2Group σ hy),
      ihx, ihy, e8a2Mat_mul hx hy, Matrix.map_mul]
  | inv x hx ih =>
    have hL := baseChangeGL_mem_e8a2Group σ hx
    rw [map_inv, e8a2Mat_inv hL, ih]
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, ← e8a2Mat_mul (inv_mem hx) hx, inv_mul_cancel, e8a2Mat_one,
      Matrix.map_one _ σ.map_zero σ.map_one]

theorem E8_native_A2_faithful_SL3_all_characteristics (K : Type) [Field K] :
    Function.Bijective (e8a2Rep K) ∧
    (∀ (g : subsystemGroup Tag.E8 K e8support13) (j : Fin 3),
      ((g : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) (e8a2Vec K j) =
        ∑ i, (e8a2Rep K g : Matrix (Fin 3) (Fin 3) K) i j • e8a2Vec K i) ∧
    (∀ t : K, e8a2Mat (xUnit Tag.E8 K (e8Index 0) t) = 1 + single 0 1 t) ∧
    (∀ t : K, e8a2Mat (yUnit Tag.E8 K (e8Index 0) t) = 1 + single 1 0 t) ∧
    (∀ t : K, e8a2Mat (xUnit Tag.E8 K (e8Index 2) t) = 1 + single 1 2 t) ∧
    (∀ t : K, e8a2Mat (yUnit Tag.E8 K (e8Index 2) t) = 1 + single 2 1 t) ∧
    (∀ a b : Kˣ, e8a2Mat (e8a2TorusElt a b) =
      Matrix.diagonal ![(a : K), ((a⁻¹ * b : Kˣ) : K), ((b⁻¹ : Kˣ) : K)]) ∧
    subsystemGroup Tag.E8 K e8support13 = rootSpan Tag.E8 K (parabolicRoots Tag.E8 e8support13) ∧
    (∀ g : ModGL Tag.E8 K, g ∈ subsystemGroup Tag.E8 K e8support13 ⊓ torusGroup Tag.E8 K ↔
      ∃ a b : Kˣ, g = e8a2TorusElt a b) ∧
    (∀ i j : Fin 3, i ≠ j → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ t : K,
      e8a2Mat (pinnedX Tag.E8 K (chainRoot e8chain13 i j) t) = 1 + single i j ((ε : K) * t)) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : ModGL Tag.E8 K),
      g ∈ subsystemGroup Tag.E8 K e8support13 →
        baseChangeGL σ g ∈ subsystemGroup Tag.E8 L e8support13 ∧
          e8a2Mat (baseChangeGL σ g) = (e8a2Mat g).map σ) ∧
    (∀ l : K, l ^ 3 = 1 → ∃ g ∈ Subgroup.center (subsystemGroup Tag.E8 K e8support13),
      (e8a2Rep K g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) l) := by
  have hbij : Function.Bijective (e8a2Rep K) := ⟨e8a2Rep_injective, e8a2Rep_surjective⟩
  refine ⟨hbij, fun g j => apply_e8a2Vec g.2 j, e8a2Mat_x1, e8a2Mat_y1, e8a2Mat_x3, e8a2Mat_y3,
    e8a2Mat_e8a2TorusElt, subsystemGroup_eq_rootSpan e8support13, fun g => ?_,
    e8a2RootFamily_all,
    fun L _ σ g hg => ⟨baseChangeGL_mem_e8a2Group σ hg, e8a2Mat_baseChangeGL σ hg⟩,
    fun l hl => ?_⟩
  · rw [subsystemGroup_inf_torusGroup, mem_subsystemTorus_e8a2]
  ·
    have hdet : (Matrix.scalar (Fin 3) l).det = 1 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hl]
    set s : SpecialLinearGroup (Fin 3) K := ⟨Matrix.scalar (Fin 3) l, hdet⟩
    obtain ⟨g, hg⟩ := hbij.2 s
    refine ⟨g, Subgroup.mem_center_iff.2 fun h => hbij.1 ?_, by rw [hg]⟩
    rw [map_mul, map_mul, hg]
    refine Subtype.ext ?_
    change (e8a2Rep K h : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) l =
      Matrix.scalar (Fin 3) l * (e8a2Rep K h : Matrix (Fin 3) (Fin 3) K)
    exact (Matrix.scalar_commute l (fun r => Commute.all l r) _).eq.symm

end CFSG.RankThree.PartOne.KE

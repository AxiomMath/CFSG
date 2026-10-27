module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Monster.B.Fischer.Fi22Order
public import TauCeti.RingTheory.LocalRing.Basic
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.A2ActualPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.A2Actual
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
open CFSG.StandardType.F4ExplicitPos.PositiveNo117
open scoped Pointwise
variable {K : Type} [Field K]

theorem f4_subsystemGroup_subset_subsystemCells
    (A : Set (Fin Tag.F4.rank)) :
    (subsystemGroup Tag.F4 K A : Set (ModGL Tag.F4 K)) ⊆ subsystemCells Tag.F4 K A := by
  let M : Subgroup (ModGL Tag.F4 K) :=
    { carrier := {g | (∀ x ∈ subsystemCells Tag.F4 K A, g * x ∈ subsystemCells Tag.F4 K A) ∧
        ∀ x ∈ subsystemCells Tag.F4 K A, g⁻¹ * x ∈ subsystemCells Tag.F4 K A}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBM : ∀ b ∈ subsystemBorel Tag.F4 K A, b ∈ M := fun b hb =>
    ⟨fun x hx => borel_mul_mem_subsystemCells hb hx,
      fun x hx => borel_mul_mem_subsystemCells (inv_mem hb) hx⟩
  have hnM : ∀ i ∈ A, weylElt Tag.F4 K i 1 ∈ M := fun i hi => by
    refine ⟨fun x hx => f4_weylElt_mul_mem_subsystemCells hi hx, fun x hx => ?_⟩
    have hsq := weylElt_one_sq (τ := Tag.F4) (R := K) i
    have e : (weylElt Tag.F4 K i 1)⁻¹ = weylElt Tag.F4 K i 1 * (torusElt Tag.F4 K i (-1))⁻¹ := by
      rw [← hsq, sq, mul_inv_rev, mul_inv_cancel_left]
    rw [e, mul_assoc]
    exact f4_weylElt_mul_mem_subsystemCells hi
      (borel_mul_mem_subsystemCells (inv_mem (torusElt_mem_subsystemBorel hi _)) hx)
  have hle : subsystemGroup Tag.F4 K A ≤ M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact hBM _ (xUnit_mem_subsystemBorel hi c)
    · rw [yUnit_eq_conj]
      exact mul_mem (mul_mem (hnM i hi) (hBM _ (xUnit_mem_subsystemBorel hi _)))
        (inv_mem (hnM i hi))
  intro g hg
  have h1 : (1 : ModGL Tag.F4 K) ∈ subsystemCells Tag.F4 K A :=
    mem_subsystemCells.2 ⟨1, one_mem _, one_mem_subsystemCell_one⟩
  simpa using (hle hg).1 1 h1

theorem f4_subsystemCell_eq_mul
    {A : Set (Fin Tag.F4.rank)} {w : WeylGroup Tag.F4}
    (hw : w ∈ parabolicWeylGroup Tag.F4 A) :
    subsystemCell Tag.F4 K A w = (subsystemBorel Tag.F4 K A : Set (ModGL Tag.F4 K)) *
      {canonicalRep (coxeterSystem Tag.F4) K w} *
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
    rw [← SetLike.mem_coe, coe_subsystemBorel] at hb'
    obtain ⟨t, ht, v, hv, rfl⟩ := hb'
    set S₁ := parabolicPosRoots Tag.F4 A \ inversionSet w
    have hsplit : parabolicPosRoots Tag.F4 A = S₁ ∪ inversionSet w :=
      (Set.sdiff_union_of_subset (inversionSet_subset_parabolicPosRoots hw)).symm
    have hv' : v ∈ rootSpan Tag.F4 K (S₁ ∪ inversionSet w) := by
      rw [← hsplit]
      exact hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := f4_exists_mul_rootSpan_eq K (S₁ := S₁)
      (S₂ := inversionSet w) (fun α hα => hα.1.2) (fun α hα => ⟨hα.1, hα.2.1⟩)
      Set.disjoint_sdiff_left
      (fun α hα β hβ a b ha hb hr => by
        rw [← hsplit] at hα hβ ⊢
        exact add_mem_parabolicPosRoots hα hβ ha hb hr) hv'
    have hnt := canonicalRep_conj_mem_subsystemTorus (K := K) hw ht
    have hnu : canonicalRep (coxeterSystem Tag.F4) K w * u₁ *
        (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ ∈
        parabolicLeviUnipotent Tag.F4 K A := by
      refine rootSpan_mono ?_ (canonicalRep_conj_mem_rootSpan (fun α hα => hα.1.1.1) hu₁)
      rintro _ ⟨α, ⟨hα, hαI⟩, rfl⟩
      refine mem_parabolicPosRoots_of (smul_mem_parabolicRoots hw hα.1) ?_
      rcases IsRoot.height_pos_or_neg (IsRoot.smul hα.1.1 w) with h | h
      · exact h
      · exact absurd ⟨hα.1.1, hα.2.2, IsRoot.smul hα.1.1 w, h⟩ hαI
    refine ⟨_, ⟨b * (canonicalRep (coxeterSystem Tag.F4) K w * t *
      (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹) * (canonicalRep (coxeterSystem Tag.F4) K w * u₁ *
      (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹), mul_mem (mul_mem hb (Subgroup.mem_sup_left hnt))
      (Subgroup.mem_sup_right hnu), _, rfl, rfl⟩, u₂, hu₂, ?_⟩
    simp only
    group
  · rintro _ ⟨_, ⟨b, hb, _, rfl, rfl⟩, u, hu, rfl⟩
    exact mem_subsystemCell.2 ⟨b, hb, u, rootSpan_inversionSet_le_subsystemBorel hw hu, rfl⟩

theorem f4_subsystem_bruhat_no117_actual
    (J : Set (Fin Tag.F4.rank)) :
    ∀ {g : ModGL Tag.F4 K}, g ∈ subsystemGroup Tag.F4 K J →
      ∃ w ∈ parabolicWeylGroup Tag.F4 J, ∃ b ∈ subsystemBorel Tag.F4 K J,
        ∃ v ∈ rootSpan Tag.F4 K (inversionSet w) ⊓ subsystemGroup Tag.F4 K J,
          b * canonicalRep (coxeterSystem Tag.F4) K w * v = g := by
  intro g hg
  have hgcell : g ∈ subsystemCells Tag.F4 K J := f4_subsystemGroup_subset_subsystemCells J hg
  obtain ⟨w, hw, hcell⟩ := mem_subsystemCells.1 hgcell
  rw [f4_subsystemCell_eq_mul hw] at hcell
  obtain ⟨y, hy, u, hu, heq⟩ := hcell
  obtain ⟨b, hb, m, hm, rfl⟩ := hy
  rw [Set.mem_singleton_iff] at hm
  subst hm
  refine ⟨w, hw, b, hb, u, ⟨hu, ?_⟩, heq⟩
  have hbS : b ∈ subsystemGroup Tag.F4 K J := subsystemBorel_le_subsystemGroup hb
  have hnS : canonicalRep (coxeterSystem Tag.F4) K w ∈ subsystemGroup Tag.F4 K J :=
    canonicalRep_mem_subsystemGroup hw
  have h1 : u = (b * canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ * g := by
    rw [← heq]
    group
  rw [h1]
  exact (subsystemGroup Tag.F4 K J).mul_mem
    ((subsystemGroup Tag.F4 K J).inv_mem ((subsystemGroup Tag.F4 K J).mul_mem hbS hnS)) hg

open scoped MatrixGroups

open Matrix

theorem f4_bijOn_prod_pinnedX_parabolicPosRoots
    {J : Set (Fin Tag.F4.rank)} {m : ℕ}
    (α : Fin m → Fin Tag.F4.rank → ℤ) (hα : Function.Injective α)
    (hrange : Set.range α = parabolicPosRoots Tag.F4 J) :
    Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX Tag.F4 K (α k) (c k)).prod)
      Set.univ (parabolicLeviUnipotent Tag.F4 K J) :=
  f4_bijOn_prod_pinnedX K (fun _ h => h.2)
    (fun _ hβ _ hγ _ _ ha hb hr => add_mem_parabolicPosRoots hβ hγ ha hb hr) α hα hrange

theorem f4_pinnedX_mem_f4Long
    {α : Fin Tag.F4.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.F4 f4LongSupport) (t : K) :
    pinnedX Tag.F4 K α t ∈ subsystemGroup Tag.F4 K f4LongSupport :=
  rootSubgroup_le_subsystemGroup hα (mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem f4LongRootFamily_02_actual :
    F4LongRootFamily K 0 2 := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 0)
    (isRoot_single Tag.F4 (f4Index 1))
  have hr : reflect Tag.F4 (f4Index 0) (Pi.single (f4Index 1) 1) = chainRoot f4chainLong 0 2 := by
    decide +kernel
  rw [hr] at h
  have hn : weylElt Tag.F4 K (f4Index 0) 1 ∈ subsystemGroup Tag.F4 K f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  have hα : Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
    have := f4chainLong_mem_parabolicRoots (k := 1) (l := 2) (by decide)
    rwa [f4chainLong_values.2.1] at this
  refine ⟨Units.mkOfMulEqOne ε ε hεε, fun t => ?_⟩
  have e : pinnedX Tag.F4 K (chainRoot f4chainLong 0 2) t =
      weylElt Tag.F4 K (f4Index 0) 1 * pinnedX Tag.F4 K (Pi.single (f4Index 1) 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 0) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := f4_pinnedX_mem_f4Long hα (ε * t)
  rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
    f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_single, f4Long_Mat_x2]
  exact f4LongN_conj_12 _

theorem f4LongRootFamily_20_actual :
    F4LongRootFamily K 2 0 := by
  obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv K (f4Index 0)
    (isRoot_neg_single Tag.F4 (f4Index 1))
  have hr : reflect Tag.F4 (f4Index 0) (-Pi.single (f4Index 1) 1) = chainRoot f4chainLong 2 0 := by
    decide +kernel
  rw [hr] at h
  have hn : weylElt Tag.F4 K (f4Index 0) 1 ∈ subsystemGroup Tag.F4 K f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  have hα : -Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
    have := f4chainLong_mem_parabolicRoots (k := 2) (l := 1) (by decide)
    rwa [f4chainLong_values.2.2.2] at this
  refine ⟨Units.mkOfMulEqOne ε ε hεε, fun t => ?_⟩
  have e : pinnedX Tag.F4 K (chainRoot f4chainLong 2 0) t =
      weylElt Tag.F4 K (f4Index 0) 1 * pinnedX Tag.F4 K (-Pi.single (f4Index 1) 1) (ε * t) *
        (weylElt Tag.F4 K (f4Index 0) 1)⁻¹ := by
    rw [h, ← mul_assoc, hεε, one_mul]
  have hX := f4_pinnedX_mem_f4Long hα (ε * t)
  rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
    f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_neg_single, f4Long_Mat_y2]
  exact f4LongN_conj_21 _

theorem f4LongRootFamily_all_actual :
    ∀ i j : Fin 3, i ≠ j → F4LongRootFamily K i j := by
  obtain ⟨c01, c12, c10, c21⟩ := f4chainLong_values
  have f01 : F4LongRootFamily K 0 1 := f4LongRootFamily_of_eq
    (fun t => by rw [c01, pinnedX_single]) f4Long_Mat_x1
  have f12 : F4LongRootFamily K 1 2 := f4LongRootFamily_of_eq
    (fun t => by rw [c12, pinnedX_single]) f4Long_Mat_x2
  have f10 : F4LongRootFamily K 1 0 := f4LongRootFamily_of_eq
    (fun t => by rw [c10, pinnedX_neg_single]) f4Long_Mat_y1
  have f21 : F4LongRootFamily K 2 1 := f4LongRootFamily_of_eq
    (fun t => by rw [c21, pinnedX_neg_single]) f4Long_Mat_y2
  intro i j hij
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => exact f01
  | 0, 2, _ => exact f4LongRootFamily_02_actual
  | 1, 0, _ => exact f10
  | 1, 1, h => exact absurd rfl h
  | 1, 2, _ => exact f12
  | 2, 0, _ => exact f4LongRootFamily_20_actual
  | 2, 1, _ => exact f21
  | 2, 2, h => exact absurd rfl h

theorem f4Long_eq_one_of_Mat_mul_eq_one_actual
    {t u : ModGL Tag.F4 K}
    (ht : t ∈ subsystemTorus Tag.F4 K f4LongSupport)
    (hu : u ∈ parabolicLeviUnipotent Tag.F4 K f4LongSupport) (h : f4Long_data.Mat (t * u) = 1) :
    t = 1 ∧ u = 1 := by
  obtain ⟨a, b, rfl⟩ := mem_subsystemTorus_f4Long.1 ht
  obtain ⟨x, -, rfl⟩ := (f4_bijOn_prod_pinnedX_parabolicPosRoots f4LongPosRoot
    f4LongPosRoot_injective range_f4LongPosRoot).surjOn hu
  choose ε hε using f4LongRootFamily_all_actual (K := K)
  have hrc : ∀ m, a2PosRow m ≠ a2PosCol m := fun m => (a2PosRow_lt_col m).ne
  set y : Fin 3 → K := fun m => ((ε (a2PosRow m) (a2PosCol m) (hrc m) : Kˣ) : K) * x m
    with hy
  have hlist : ∀ g ∈ List.ofFn fun m => pinnedX Tag.F4 K (f4LongPosRoot m) (x m),
      g ∈ subsystemGroup Tag.F4 K f4LongSupport := by
    intro g hg
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hg
    exact f4_pinnedX_mem_f4Long (f4LongPosRoot_mem m) _
  have hu' : f4Long_data.Mat (List.ofFn fun m => pinnedX Tag.F4 K (f4LongPosRoot m) (x m)).prod =
      1 + (single 1 2 (y 0) + (single 0 1 (y 1) + single 0 2 (y 2))) := by
    rw [f4Long_data.Mat_list_prod _ hlist, List.map_ofFn, ← prod_a2Pos y]
    refine congrArg List.prod (congrArg List.ofFn (funext fun m => ?_))
    rw [Function.comp_apply, f4LongPosRoot_eq, hε]
  rw [f4Long_data.Mat_mul (torus2Elt_mem_f4Long a b) (Subgroup.list_prod_mem _ hlist),
    f4Long_Mat_torus, hu'] at h
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
    exact (mul_eq_zero.1 h0).resolve_left (Units.ne_zero _)
  subst hx0
  refine ⟨torus2Elt_one _ _, ?_⟩
  simp only [Pi.zero_apply, pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow]

end CFSG.StandardType.F4ExplicitPos.A2Actual
end

end

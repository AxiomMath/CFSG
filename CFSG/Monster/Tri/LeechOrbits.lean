module

public import CFSG.Monster.Tri.LeechSpec
public import CFSG.Monster.B.Co2.KstabMaximal
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GroupActions

theorem iUnion_orbit_eq_of_partition {G Ω : Type*} [Group G] [MulAction G Ω] (a : Ω)
    (S : Subgroup G) {ι : Type*} [Fintype ι] (b : ι → Ω) (n : ι → ℕ)
    (hbmem : ∀ i, b i ∈ MulAction.orbit G a)
    (hn : ∀ i, (MulAction.orbit S (b i)).ncard = n i)
    (hne : ∀ i j, i ≠ j → MulAction.orbit S (b i) ≠ MulAction.orbit S (b j))
    (hfin : (MulAction.orbit G a).Finite) (hsumN : ∑ i, n i = (MulAction.orbit G a).ncard) :
    (⋃ i, MulAction.orbit S (b i)) = MulAction.orbit G a := by
  have hTO : ∀ i, MulAction.orbit S (b i) ⊆ MulAction.orbit G a := fun i => by
    refine (MulAction.orbit_subgroup_subset S (b i)).trans ?_
    rw [MulAction.orbit_eq_iff.2 (hbmem i)]
  have hTfin : ∀ i, (MulAction.orbit S (b i)).Finite := fun i => hfin.subset (hTO i)
  have hdisj : Pairwise (Function.onFun Disjoint fun i => MulAction.orbit S (b i)) :=
    fun i j hij => by
      rw [Function.onFun, Set.disjoint_left]
      intro z hzi hzj
      apply hne i j hij
      rw [← MulAction.orbit_eq_iff.2 hzi, ← MulAction.orbit_eq_iff.2 hzj]
  apply Set.eq_of_subset_of_ncard_le (Set.iUnion_subset hTO) _ hfin
  rw [Set.ncard_iUnion_of_finite hTfin hdisj, finsum_eq_sum_of_fintype]
  simp only [hn]
  exact hsumN.ge

end CFSG.GroupActions

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.KstabMaximal

attribute [local instance] olqLeft

@[expose] def seed : Fin 4 → L2 := ![v0, dec 1, dec 64, dec 4096]

@[expose] def seedSize : Fin 4 → ℕ := ![1, 47104, 46575, 4600]

theorem seed_mem (i : Fin 4) : seed i ∈ shortSet := by
  fin_cases i
  · exact classOf_vMinus_mem_shortSet
  · exact dec_one_mem_shortSet
  · exact dec_sixtyFour_mem_shortSet
  · exact dec_fourThousand_mem_shortSet

theorem ncard_orbit_seed
    (i : Fin 4) : (MulAction.orbit Sgrp (seed i)).ncard = seedSize i := by
  fin_cases i
  · exact ncard_orbit_Sgrp_v0
  · exact ncard_orbit_Sgrp_one
  · exact ncard_orbit_Sgrp_sixtyFour
  · exact ncard_orbit_Sgrp_fourThousand

theorem seedSize_injective : Function.Injective seedSize := sizes_injective

theorem iUnion_orbit_seed :
    (⋃ i, MulAction.orbit Sgrp (seed i)) = shortSet := by
  have h := GroupActions.iUnion_orbit_eq_of_partition v0 Sgrp seed seedSize
    (fun i => by rw [orbit_olq_v0]; exact seed_mem i) ncard_orbit_seed
    (fun i j hij h => hij (seedSize_injective (by
      rw [← ncard_orbit_seed i, ← ncard_orbit_seed j, h])))
    (Set.toFinite _) (by rw [ncard_orbit_olq_v0]; decide)
  rwa [orbit_olq_v0] at h

theorem smul_mem_shortSet_iff (k : OLq) {x : L2} : k • x ∈ shortSet ↔ x ∈ shortSet :=
  kOp_mem_shortSet_iff k⁻¹

theorem qL_smul (k : OLq) (x : L2) : qL (k • x) = qL x := qL_kOp k⁻¹ x

theorem smul_mem_frameDelta_iff (k : OLq) {x : L2} : k • x ∈ frameDelta ↔ x ∈ frameDelta :=
  kOp_mem_frameDelta_iff k⁻¹

theorem adj_smul_iff (k : OLq) {a b : L2} :
    shortGraph.Adj (k • a) (k • b) ↔ shortGraph.Adj a b := shortGraph_adj_kOp k⁻¹

theorem smul_add_olq (k : OLq) (x y : L2) : k • (x + y) = k • x + k • y := map_add (kOp k⁻¹) x y

theorem smul_v0_of_mem_Sgrp
    {s : OLq} (hs : s ∈ Sgrp) : s • v0 = v0 := by
  have h : s ∈ MulAction.stabilizer OLq v0 := by
    rw [stabilizer_olq]
    exact Sgrp_le_Kstab hs
  exact h

theorem orbit_invariants
    {b y : L2} (hy : y ∈ MulAction.orbit Sgrp b) :
    (shortGraph.Adj v0 y ↔ shortGraph.Adj v0 b) ∧ qL (v0 + y) = qL (v0 + b) ∧
      (v0 + y ∈ frameDelta ↔ v0 + b ∈ frameDelta) := by
  obtain ⟨s, rfl⟩ := hy
  have hs : (s : OLq) • v0 = v0 := smul_v0_of_mem_Sgrp s.2
  have hsum : v0 + (s : OLq) • b = (s : OLq) • (v0 + b) := by rw [smul_add_olq, hs]
  show (shortGraph.Adj v0 ((s : OLq) • b) ↔ shortGraph.Adj v0 b) ∧
    qL (v0 + (s : OLq) • b) = qL (v0 + b) ∧
    (v0 + (s : OLq) • b ∈ frameDelta ↔ v0 + b ∈ frameDelta)
  rw [hsum]
  refine ⟨?_, qL_smul _ _, smul_mem_frameDelta_iff _⟩
  have h1 : shortGraph.Adj v0 ((s : OLq) • b) ↔
      shortGraph.Adj ((s : OLq) • v0) ((s : OLq) • b) := by rw [hs]
  exact h1.trans (adj_smul_iff _)

theorem dec_one_eq : dec 1 = ellCls 0 := dec_one_shiftLeft 0

theorem dec_sixtyFour_eq : dec 64 = ellCls 6 := dec_one_shiftLeft 6

theorem bL_v0_ellCls (k : Fin 24) :
    bL v0 (ellCls k) = (popc 24 (12288 &&& gramRow k) : ZMod 2) := by
  rw [← dec_12288]
  exact bL_dec 12288 k

theorem qL_add_v0_dec_one :
    qL (v0 + dec 1) = 1 := by
  rw [qL_add_of_mem_shortSet classOf_vMinus_mem_shortSet dec_one_mem_shortSet, dec_one_eq,
    bL_v0_ellCls]
  decide +kernel

theorem qL_add_v0_dec_sixtyFour :
    qL (v0 + dec 64) = 0 := by
  rw [qL_add_of_mem_shortSet classOf_vMinus_mem_shortSet dec_sixtyFour_mem_shortSet,
    dec_sixtyFour_eq, bL_v0_ellCls]
  decide +kernel

theorem add_v0_dec_fourThousand_mem :
    v0 + dec 4096 ∈ shortSet := by
  have h : v0 + dec 4096 = ellCls 13 := by
    rw [← dec_12288, ← dec_xor, show (12288 ^^^ 4096 : ℕ) = 1 <<< ((13 : Fin 24) : ℕ) by decide,
      dec_one_shiftLeft]
  rw [h]
  exact ellCls_mem_shortSet 13

theorem v0_add_dec_sixtyFour_ne_zero :
    v0 + dec 64 ≠ 0 := by
  intro h
  rw [← dec_12288, ← dec_xor, ← dec_zero] at h
  have h1 := dec_inj _ _ (by decide) (by decide) h
  revert h1
  decide

theorem seed_adj
    (i : Fin 4) : shortGraph.Adj v0 (seed i) ↔ i = 3 := by
  fin_cases i
  · exact iff_of_false (shortGraph.irrefl) (by decide)
  · refine iff_of_false (fun h => ?_) (by decide)
    have h' : qL (v0 + dec 1) = 0 := qL_eq_zero_of_mem_shortSet h.2.2
    rw [qL_add_v0_dec_one] at h'
    exact one_ne_zero h'
  · exact iff_of_false (fun h => not_mem_shortSet_v0_add_ell6 h.2.2) (by decide)
  · exact iff_of_true ⟨classOf_vMinus_mem_shortSet, dec_fourThousand_mem_shortSet,
      add_v0_dec_fourThousand_mem⟩ rfl

theorem seed_qL
    (i : Fin 4) : qL (v0 + seed i) = 1 ↔ i = 1 := by
  fin_cases i
  · refine iff_of_false ?_ (by decide)
    change qL (v0 + v0) ≠ 1
    rw [add_self_L2, QuadraticMap.map_zero]
    decide
  · exact iff_of_true qL_add_v0_dec_one rfl
  · refine iff_of_false ?_ (by decide)
    change qL (v0 + dec 64) ≠ 1
    rw [qL_add_v0_dec_sixtyFour]
    decide
  · refine iff_of_false ?_ (by decide)
    change qL (v0 + dec 4096) ≠ 1
    rw [qL_eq_zero_of_mem_shortSet add_v0_dec_fourThousand_mem]
    decide

theorem seed_delta
    (i : Fin 4) : v0 + seed i ∈ frameDelta ↔ i = 2 := by
  fin_cases i
  · refine iff_of_false ?_ (by decide)
    change v0 + v0 ∉ frameDelta
    rw [add_self_L2]
    exact fun h => h.1 rfl
  · refine iff_of_false (fun h => ?_) (by decide)
    have h' : qL (v0 + dec 1) = 0 := h.2.1
    rw [qL_add_v0_dec_one] at h'
    exact one_ne_zero h'
  · exact iff_of_true ⟨v0_add_dec_sixtyFour_ne_zero, qL_add_v0_dec_sixtyFour,
      not_mem_shortSet_v0_add_ell6⟩ rfl
  · refine iff_of_false (fun h => h.2.2 ?_) (by decide)
    exact add_v0_dec_fourThousand_mem

theorem exists_orbit_seed
    {y : L2} (hy : y ∈ shortSet) :
    ∃ i, y ∈ MulAction.orbit Sgrp (seed i) := by
  rw [← iUnion_orbit_seed] at hy
  exact Set.mem_iUnion.1 hy

theorem mem_orbit_seed_three
    {y : L2} (hy : shortGraph.Adj v0 y) :
    y ∈ MulAction.orbit Sgrp (seed 3) := by
  obtain ⟨i, hi⟩ := exists_orbit_seed (mem_shortSet_of_adj_right hy)
  have := (seed_adj i).1 ((orbit_invariants hi).1.1 hy)
  rwa [this] at hi

theorem exists_smul_eq_seed
    {x y : L2} (hx : x ∈ shortSet) (hy : y ∈ shortSet) :
    ∃ (k : OLq) (i : Fin 4), k • x = v0 ∧ k • y = seed i := by
  rw [← orbit_olq_v0] at hx
  obtain ⟨g, rfl⟩ := hx
  have hy' : g⁻¹ • y ∈ shortSet := (smul_mem_shortSet_iff g⁻¹).2 hy
  obtain ⟨i, s, hs⟩ := exists_orbit_seed hy'
  have hs' : (s : OLq) • seed i = g⁻¹ • y := hs
  refine ⟨(s : OLq)⁻¹ * g⁻¹, i, ?_, ?_⟩
  · rw [mul_smul, inv_smul_smul]
    exact smul_v0_of_mem_Sgrp (inv_mem s.2)
  · rw [mul_smul, ← hs', inv_smul_smul]

end CFSG.Monster.Tri.Leech

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphStarClasses
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The conjugation action on the seven edge-star classes

Conjugation acts on oriented darts and transports their intrinsic edge stars.
The local transitivity of the root stabilizer on the four neighbours upgrades
vertex transitivity to dart transitivity, hence to transitivity on the seven
edge-star classes.  Simplicity makes this nontrivial action faithful.  A class
stabilizer therefore supplies the index-seven subgroup needed for the A₇
recognition tail.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

@[expose] public def commutingGraphDartSmul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (d : (commutingGraph c).Dart) :
    (commutingGraph c).Dart :=
  ⟨(g • d.fst, g • d.snd),
    (commutingGraph.adj_smul_iff c g d.fst d.snd).mpr d.adj⟩

public instance commutingGraphDartSMul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : SMul G (commutingGraph c).Dart where
  smul := commutingGraphDartSmul c

public instance commutingGraphDartMulAction
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : MulAction G (commutingGraph c).Dart where
  one_smul d := by
    apply SimpleGraph.Dart.ext
    change (1 • d.fst, 1 • d.snd) = (d.fst, d.snd)
    simp
  mul_smul g h d := by
    apply SimpleGraph.Dart.ext
    change ((g * h) • d.fst, (g * h) • d.snd) =
      (g • h • d.fst, g • h • d.snd)
    simp [mul_smul]

@[simp] public theorem commutingGraphDart_smul_fst
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (d : (commutingGraph c).Dart) :
    (g • d).fst = g • d.fst := rfl

@[simp] public theorem commutingGraphDart_smul_snd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (d : (commutingGraph c).Dart) :
    (g • d).snd = g • d.snd := rfl

public theorem commutingGraphDartStar_smul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (d : (commutingGraph c).Dart) :
    commutingGraphDartStar c (g • d) = g • commutingGraphDartStar c d := by
  ext X
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have h := commutingGraphEdgeStar_smul_iff
    c g d.fst d.snd (g⁻¹ • X)
  simpa only [commutingGraphDartStar, commutingGraphDart_smul_fst, commutingGraphDart_smul_snd,
    ← mul_smul, mul_inv_cancel, one_smul] using h

@[expose] public def commutingGraphEdgeStarClassSmul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (S : CommutingGraphEdgeStarClass c) :
    CommutingGraphEdgeStarClass c :=
  ⟨g • S.1, by
    obtain ⟨d, hd⟩ := S.2
    refine ⟨g • d, ?_⟩
    rw [commutingGraphDartStar_smul, hd]⟩

public instance commutingGraphEdgeStarClassSMul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : SMul G (CommutingGraphEdgeStarClass c) where
  smul := commutingGraphEdgeStarClassSmul c

public instance commutingGraphEdgeStarClassMulAction
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : MulAction G (CommutingGraphEdgeStarClass c) where
  one_smul S := by
    apply Subtype.ext
    exact one_smul G S.1
  mul_smul g h S := by
    apply Subtype.ext
    exact mul_smul g h S.1

@[simp] public theorem commutingGraphDartStarClass_smul
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (g : G) (d : (commutingGraph c).Dart) :
    commutingGraphDartStarClass c (g • d) =
      g • commutingGraphDartStarClass c d := by
  apply Subtype.ext
  exact commutingGraphDartStar_smul c g d

public theorem firstCase_commutingGraphDart_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (D E : (commutingGraph c).Dart) :
    ∃ g : G, g • D = E := by
  obtain ⟨a, ha⟩ := UConjugates.exists_smul_base c D.fst
  obtain ⟨b, hb⟩ := UConjugates.exists_smul_base c E.fst
  have ha0 : a⁻¹ • D.fst = UConjugates.base c := by
    calc
      a⁻¹ • D.fst = a⁻¹ • (a • UConjugates.base c) := by rw [ha]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  have hb0 : b⁻¹ • E.fst = UConjugates.base c := by
    calc
      b⁻¹ • E.fst = b⁻¹ • (b • UConjugates.base c) := by rw [hb]
      _ = UConjugates.base c := by rw [← mul_smul]; simp
  let D0 : UConjugates c := a⁻¹ • D.snd
  let E0 : UConjugates c := b⁻¹ • E.snd
  have hbaseD : (commutingGraph c).Adj (UConjugates.base c) D0 := by
    have h := (commutingGraph.adj_smul_iff c a⁻¹ D.fst D.snd).mpr D.adj
    simpa only [D0, ha0] using h
  have hbaseE : (commutingGraph c).Adj (UConjugates.base c) E0 := by
    have h := (commutingGraph.adj_smul_iff c b⁻¹ E.fst E.snd).mpr E.adj
    simpa only [E0, hb0] using h
  let DN : lineNeighborSet c := ⟨D0, by
    have h := (commutingGraph_adj_iff c _ _).mp hbaseD
    exact ⟨h.1.symm, h.2⟩⟩
  let EN : lineNeighborSet c := ⟨E0, by
    have h := (commutingGraph_adj_iff c _ _).mp hbaseE
    exact ⟨h.1.symm, h.2⟩⟩
  obtain ⟨h, hh⟩ := neighbor_orbit_transitive hmin c hfirst d DN EN
  have hhfix : (h : G) • UConjugates.base c = UConjugates.base c := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [commutingGraph.stabilizer_base_eq_hhat hmin c hfirst]
    exact h.2
  have hD0 : (h : G) • D0 = E0 := by
    simpa only [DN, EN] using hh
  refine ⟨b * (h : G) * a⁻¹, ?_⟩
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change (b * (h : G) * a⁻¹) • D.fst = E.fst
    simp only [mul_smul]
    rw [ha0, hhfix, hb]
  · change (b * (h : G) * a⁻¹) • D.snd = E.snd
    simp only [mul_smul]
    change b • (h : G) • D0 = E.snd
    rw [hD0]
    dsimp only [E0]
    rw [← mul_smul]
    simp

public theorem firstCase_edgeStarClass_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (S T : CommutingGraphEdgeStarClass c) :
    ∃ g : G, g • S = T := by
  obtain ⟨D, hD⟩ := commutingGraphDartStarClass_surjective c S
  obtain ⟨E, hE⟩ := commutingGraphDartStarClass_surjective c T
  obtain ⟨g, hg⟩ := firstCase_commutingGraphDart_transitive hmin c hfirst d D E
  refine ⟨g, ?_⟩
  calc
    g • S = g • commutingGraphDartStarClass c D := by rw [hD]
    _ = commutingGraphDartStarClass c (g • D) :=
      (commutingGraphDartStarClass_smul c g D).symm
    _ = commutingGraphDartStarClass c E := by rw [hg]
    _ = T := hE

public theorem firstCase_edgeStarClass_faithful
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    FaithfulSMul G (CommutingGraphEdgeStarClass c) := by
  classical
  let := Fintype.ofFinite (CommutingGraphEdgeStarClass c)
  rw [faithfulSMul_iff]
  intro g hg
  let φ : G →* Equiv.Perm (CommutingGraphEdgeStarClass c) :=
    MulAction.toPermHom G (CommutingGraphEdgeStarClass c)
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hker : φ.ker = ⊥ ∨ φ.ker = ⊤ :=
    @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple φ.ker inferInstance
  have hker_bot : φ.ker = ⊥ := by
    rcases hker with hbot | htop
    · exact hbot
    · exfalso
      have hcardF : Fintype.card (CommutingGraphEdgeStarClass c) = 7 := by
        rw [← Nat.card_eq_fintype_card]
        exact firstCase_edgeStarClass_card_seven hmin c hfirst d
      obtain ⟨S, T, hST⟩ := Fintype.exists_pair_of_one_lt_card (α :=
        CommutingGraphEdgeStarClass c) (by omega)
      obtain ⟨k, hk⟩ := firstCase_edgeStarClass_transitive hmin c hfirst d S T
      have hkker : k ∈ φ.ker := by rw [htop]; simp
      have hkphi : φ k = 1 := MonoidHom.mem_ker.mp hkker
      have hkfix : k • S = S := by
        change (φ k) S = S
        rw [hkphi]
        rfl
      exact hST (hkfix.symm.trans hk)
  have hgker : g ∈ φ.ker := by
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro S
    change g • S = S
    exact hg S
  rw [hker_bot] at hgker
  simpa using hgker

public theorem firstCase_exists_indexSeven_subgroup_oddGraph
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    ∃ H : Subgroup G, H.index = 7 := by
  classical
  let C := CommutingGraphEdgeStarClass c
  have hCcard : Nat.card C = 7 :=
    firstCase_edgeStarClass_card_seven hmin c hfirst d
  have hCpos : 0 < Nat.card C := by rw [hCcard]; norm_num
  have hCnonempty : Nonempty C := (Nat.card_pos_iff.mp hCpos).1
  let S : C := Classical.choice hCnonempty
  let : MulAction.IsPretransitive G C :=
    ⟨fun X Y => firstCase_edgeStarClass_transitive hmin c hfirst d X Y⟩
  refine ⟨MulAction.stabilizer G S, ?_⟩
  rw [MulAction.index_stabilizer_of_transitive]
  exact hCcard

end

end CFSG.GorensteinWalter

module

public import CFSG.LocalAnalysis.StandardType.GGK0LQDictKinds
public import CFSG.LocalAnalysis.StandardType.GGK0LQKindA
public import CFSG.LocalAnalysis.StandardType.GGK0LQKindD
public import CFSG.LocalAnalysis.StandardType.GGK0LQKindE
public import CFSG.LocalAnalysis.StandardType.GGK0LQShape
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecA
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecD
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecE
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecC
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecC2
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecTwoD
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecTriD4
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecTwE6
public import CFSG.LocalAnalysis.StandardType.GGK0LQ2Adapt
public import CFSG.LocalAnalysis.StandardType.GGK0LQFamTable
import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
import CFSG.LocalAnalysis.StandardType.GGK0NormalTypes
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private theorem lk0xlqrows_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

theorem lq_p_ne_zero (hpair : GGKacExcPair lab p) : (p : Omega) ≠ 0 := by
  intro h
  have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff Omega 2 p).1 h
  exact hpair.2.1 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpair.1).1 h2).symm

theorem lq_zero_length_lt (A : K0LangMark Omega lab p R I phi) :
    ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).length < (k0DiagOf A.row.T).marks.length := by
  have hsum := ggKacShVecs_sum (k0DiagOf A.row.T).marks p A.row.s A.row.s_mem
  have hp : 0 < p := by
    obtain ⟨N⟩ := k0Normal_nonempty A
    exact N.zero_lt
  have hlt : ∃ i ∈ List.range (k0DiagOf A.row.T).marks.length,
      ¬ decide (A.row.s.getD i 0 = 0) = true := by
    by_contra h
    push Not at h
    have hzero : (∑ i : Fin (k0DiagOf A.row.T).marks.length,
        (k0DiagOf A.row.T).marks.getD i.val 0 * A.row.s.getD i.val 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hs : A.row.s.getD i.val 0 = 0 := by
        have := h i.val (List.mem_range.2 i.isLt)
        simpa using this
      rw [hs, mul_zero]
    rw [hzero] at hsum
    omega
  have := (List.length_filter_lt_length_iff_exists).2 hlt
  simpa using this

theorem lq_shape_K0 (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      lqShapeCount (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)) := by
  change _ = lqShapeCount (k0CompType (k0DiagOf A.row.T) ((P.orbitNodes j).headD []))
  have hbs := lq_nodes_basic A P j
  have hmem := lq_nodes_mem_comps A P j
  have hz : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).Sublist
        (List.range (k0DiagOf A.row.T).marks.length) :=
    List.filter_sublist
  have h := lq_shape_table A.tau A.row.T A.tau_eq hz (lq_zero_length_lt A) hmem
  have hset : {w : Fin A.tau.rank → ℤ | ∃ i : Fin A.row.diagram.marks.length,
      i.val ∈ (P.orbitNodes j).headD [] ∧ w = A.nodeMap (Pi.single i 1)} =
      {w | ∃ x ∈ (P.orbitNodes j).headD [], w = lqExtRoot A.tau A.row.T x} := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.val, hi, lq_nodeMap_eq A i⟩
    · rintro ⟨x, hx, rfl⟩
      have hx_lt : x < A.row.diagram.marks.length := by
        have := (hbs.2.2 x hx).1
        rw [KacRow.diagram, lk0xlqrows_marks_length A.row.T, A.tau_eq]
        exact this
      exact ⟨⟨x, hx_lt⟩, hx, (lq_nodeMap_eq A ⟨x, hx_lt⟩).symm⟩
  rw [P.repr_roots j, hset]
  exact h

theorem lq_k0AutOrder_pos (c rk : List ℕ) : 1 ≤ k0AutOrder c rk := by
  unfold k0AutOrder
  have key : ∀ (fuel o : ℕ) (cur : List ℕ), o ≤ k0AutOrder.go c rk o cur fuel := by
    intro fuel
    induction fuel with
    | zero => intro o cur; simp [k0AutOrder.go]
    | succ f ih =>
        intro o cur
        simp only [k0AutOrder.go]
        split
        · exact le_refl _
        · exact le_trans (Nat.le_succ o) (ih _ _)
  exact key _ 1 rk

theorem lq_tw_pos (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) : 1 ≤ lqTw A P j := by
  unfold lqTw
  have h := lq_k0AutOrder_pos ((P.orbitNodes j).headD [])
    (k0pPow A.row.rho (P.orbitNodes j).length)
  dsimp only
  split_ifs <;> omega

theorem lq_fam_facts (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E6 →
        (lqNodes A P j).length = 6 ∧ A.row.T ≠ .F4) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E7 →
        (lqNodes A P j).length = 7 ∧ A.row.T ≠ .F4) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E8 →
        (lqNodes A P j).length = 8 ∧ A.row.T = .E8) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .F4 →
        (lqNodes A P j).length = 4 ∧ A.row.T = .F4) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .C → A.row.T = .F4) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .D → A.row.T ≠ .F4) ∧
      (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 ≠ .G2 ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .C →
        2 ≤ (lqNodes A P j).length ∧ (lqNodes A P j).length ≤ 4 ∧
          ((lqNodes A P j).length = 4 → lqNodes A P j = [0, 1, 2, 3])) ∧
      ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .D → 4 ≤ (lqNodes A P j).length) :=
  let h1 := lq_fam_table A.row.T _ (List.mem_sublists.2 List.filter_sublist) (lq_zero_length_lt A) _
    (lq_nodes_mem_comps A P j)
  let h2 := lq_fam_rank_table A.row.T _ (List.mem_sublists.2 List.filter_sublist)
    (lq_zero_length_lt A) _ (lq_nodes_mem_comps A P j)
  ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, h2.1, h2.2⟩

theorem lq_ncard_lt_rootCount (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    (componentRoots (rootCharHom A.a) (P.repr j)).ncard < A.tau.rootCount := by
  by_contra h
  push Not at h
  exact A.a_ne (rootDiagUnit_eq_one_of_ncard (P.repr j) h)

theorem lq_kind_inner_of_shape (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) {r c : ℕ}
    (hr : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = r)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = c)
    (h6 : ¬ (r = 6 ∧ c = 72)) (h4 : ¬ (r = 4 ∧ c = 24))
    (htwoD : ¬ (4 ≤ r ∧ c = 2 * r * (r - 1))) (hsuN : ¬ (2 ≤ r ∧ c = r * (r + 1))) :
    twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner := by
  unfold twistKind
  rw [hr, hn]
  by_cases hin : twistInner (componentRoots (rootCharHom A.a) (P.repr j))
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[componentOrbitLength A.setup.ρ
        (componentRoots (rootCharHom A.a) (P.repr j))])
  · exact if_pos hin
  · rw [if_neg hin]
    have e1 : ¬ ((r = 6 ∧ c = 72) ∨ (r = 4 ∧ c = 24 ∧ ¬ twistInner
        (componentRoots (rootCharHom A.a) (P.repr j))
        ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[2 * componentOrbitLength A.setup.ρ
          (componentRoots (rootCharHom A.a) (P.repr j))]))) := by
      rintro (h | ⟨h4', h24, -⟩)
      · exact h6 h
      · exact h4 ⟨h4', h24⟩
    rw [if_neg e1, if_neg htwoD, if_neg hsuN]

theorem lq_twistInner_of_shape
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) {r c : ℕ}
    (hr : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = r)
    (hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = c)
    (h6 : ¬ (r = 6 ∧ c = 72)) (h4 : ¬ (r = 4 ∧ c = 24))
    (htwoD : ¬ (4 ≤ r ∧ c = 2 * r * (r - 1))) (hsuN : ¬ (2 ≤ r ∧ c = r * (r + 1))) :
    twistInner (componentRoots (rootCharHom A.a) (P.repr j))
      ((A.setup.ρ : (Fin A.tau.rank → ℤ) → _)^[componentOrbitLength A.setup.ρ
        (componentRoots (rootCharHom A.a) (P.repr j))]) :=
  twistInner_of_twistKind_eq_innerT A.setup
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds A.a_torus (P.repr j)
    (lq_kind_inner_of_shape A P j hr hn h6 h4 htwoD hsuN)

theorem lq_row_A
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = true) {r : ℕ}
    (hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.A, r)) (hr : 2 ≤ r) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hlen : (lqNodes A P j).length = r := by
    have h1 := lq_compType_A_rank (k0DiagOf A.row.T) (lqNodes A P j) (by rw [hct])
    rw [hct] at h1
    exact h1.symm
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = r := by
    rw [lq_compRank A P j, hlen]
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      (lqNodes A P j).length * ((lqNodes A P j).length + 1) := by
    rw [lq_shape_K0 A P j, hct, hlen]
    rfl
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hdesc := lq_descriptor_eq A P j
  rw [hct] at hdesc
  by_cases htw : lqTw A P j = 1
  · have hk : twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner := by
      by_cases h2 : r = 2
      · exact (lq_kind_of_A2 A P j (by rw [hlen, h2]) (by rw [hct])).1 htw
      · exact (lq_kind_A A P j (by rw [hlen]; omega) (by rw [hct]) hn).1 htw
    have hlabel : A.row.D.orbits[j].lab = ⟨.A, r, A.row.D.orbits[j].lab.n⟩ := by
      have h := congrArg (fun o => o.lab) hdesc
      simp only [k0LabelOf, htw, if_true] at h
      rw [h]
    have hΛ : LargeEvenInLambda2 (⟨.A, r, A.row.D.orbits[j].lab.n⟩ : LargeEvenLabel) :=
      ⟨hn1, (by omega : 1 ≤ r), fun h => by
        exfalso
        have h1 : r = 1 := h
        omega⟩
    refine ⟨by rw [hlabel]; exact hΛ, ?_⟩
    have h := lq_rec_A A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp (P.repr j) hk
      (by rw [hrank]; exact hr) (by rw [hrank]; rw [hlen] at hn; rw [hn]) (lq_qpow A P j)
    rw [hrank] at h
    rw [hlabel]
    exact h
  · have hk : twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN := by
      by_cases h2 : r = 2
      · exact (lq_kind_of_A2 A P j (by rw [hlen, h2]) (by rw [hct])).2 htw
      · exact (lq_kind_A A P j (by rw [hlen]; omega) (by rw [hct]) hn).2 htw
    have hnot : ¬ (compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 2 ∧
        A.row.D.orbits[j].lab.n = 1) := by
      rintro ⟨h2, hN1⟩
      have hr2 : r = 2 := by rw [← hrank]; exact h2
      have := (lq_qs_false_iff A P j).2 ⟨by rw [hct], Or.inr ⟨htw, by rw [hct, hr2]⟩, hN1⟩
      rw [hj] at this
      exact absurd this (by decide)
    have hlabel : A.row.D.orbits[j].lab = ⟨.twA, r, A.row.D.orbits[j].lab.n⟩ := by
      have h := congrArg (fun o => o.lab) hdesc
      simp only [k0LabelOf, if_neg htw] at h
      rw [h]
    have hΛ : LargeEvenInLambda2 (⟨.twA, r, A.row.D.orbits[j].lab.n⟩ : LargeEvenLabel) :=
      ⟨hn1, hr, fun h2 => by
        have h2' : r = 2 := h2
        by_contra hlt
        have hlt' : ¬ 2 ≤ A.row.D.orbits[j].lab.n := hlt
        exact hnot ⟨by rw [hrank]; exact h2', by omega⟩⟩
    refine ⟨by rw [hlabel]; exact hΛ, ?_⟩
    · have h := lq_rec_SU A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp (P.repr j) hk
        (lq_qpow A P j) hnot
      rw [hrank] at h
      rw [hlabel]
      exact h

private theorem lk0xlqrows_rootCount :
    Tag.E6.rootCount = 72 ∧ Tag.E7.rootCount = 126 ∧ Tag.E8.rootCount = 240 ∧
      Tag.F4.rootCount = 48 := by
  decide +kernel

private theorem lk0xlqrows_tau (A : K0LangMark Omega lab p R I phi) :
    (A.row.T = .F4 ∧ A.tau = .F4) ∨ (A.row.T = .E6 ∧ A.tau = .E6) ∨
      (A.row.T = .E7 ∧ A.tau = .E7) ∨ (A.row.T = .E8 ∧ A.tau = .E8) := by
  have h := A.tau_eq
  cases hT : A.row.T <;> simp_all [absTag]

theorem lq_row_D
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) {r : ℕ}
    (hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.D, r)) (hr : 4 ≤ r) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hlen : (lqNodes A P j).length = r := by
    have h1 := lq_compType_rank_ACD (k0DiagOf A.row.T) (lqNodes A P j)
      (Or.inr (Or.inr (by rw [hct])))
    rw [hct] at h1
    exact h1.symm
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = r := by
    rw [lq_compRank A P j, hlen]
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard =
      2 * (lqNodes A P j).length * ((lqNodes A P j).length - 1) := by
    rw [lq_shape_K0 A P j, hct, hlen]
    exact (Nat.mul_assoc 2 r (r - 1)).symm
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hT : A.row.T ≠ .F4 := (lq_fam_facts A P j).2.2.2.2.2.1 (by rw [hct])
  have hτ : A.tau = .E6 ∨ A.tau = .E7 ∨ A.tau = .E8 := by
    rcases lk0xlqrows_tau A with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hT
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hdesc := lq_descriptor_eq A P j
  rw [hct] at hdesc
  have hrk : 4 ≤ (lqNodes A P j).length := by rw [hlen]; exact hr
  have hD : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .D := by rw [hct]
  by_cases htw1 : lqTw A P j = 1
  · have hinner := ((lq_kind_D A P j hrk hD hn).1 htw1)
    have hlabel : A.row.D.orbits[j].lab = ⟨.D, r, A.row.D.orbits[j].lab.n⟩ := by
      have h := congrArg (fun o => o.lab) hdesc
      simp only [k0LabelOf, htw1, if_true] at h
      rw [h]
    refine ⟨by rw [hlabel]; exact ⟨hn1, (by omega : 3 ≤ r)⟩, ?_⟩
    have h := lq_rec_D hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp (P.repr j)
      (by rw [hrank]; exact hr) (by rw [hrank]; rw [hlen] at hn; exact hn) hinner (lq_qpow A P j)
    rw [hrank] at h
    rw [hlabel]
    exact h
  · by_cases htw2 : lqTw A P j = 2
    · have hk := (lq_kind_D A P j hrk hD hn).2.1 htw2
      have hlabel : A.row.D.orbits[j].lab = ⟨.twD, r, A.row.D.orbits[j].lab.n⟩ := by
        have h := congrArg (fun o => o.lab) hdesc
        simp only [k0LabelOf] at h
        rw [if_neg htw1, if_pos htw2] at h
        rw [h]
      refine ⟨by rw [hlabel]; exact ⟨hn1, (by omega : 2 ≤ r)⟩, ?_⟩
      have h := lq_rec_twoD A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp A.a_ne (P.repr j)
        hk (lq_qpow A P j)
      rw [hrank] at h
      rw [hlabel]
      exact h
    · have h3 : 3 ≤ lqTw A P j := by have := lq_tw_pos A P j; omega
      obtain ⟨hl4, hk⟩ := (lq_kind_D A P j hrk hD hn).2.2 h3
      have hlabel : A.row.D.orbits[j].lab = ⟨.triD4, 0, A.row.D.orbits[j].lab.n⟩ := by
        have h := congrArg (fun o => o.lab) hdesc
        simp only [k0LabelOf] at h
        rw [if_neg htw1, if_neg htw2] at h
        rw [h]
      refine ⟨by rw [hlabel]; exact ⟨hn1, rfl⟩, ?_⟩
      have h := lq_rec_triD4 A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp A.a_ne (P.repr j)
        hk (by rw [hrank]; rw [hlen] at hl4; exact hl4) (lq_qpow A P j)
      rw [hlabel]
      exact h


theorem lq_row_A1
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = true)
    (hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.A, 1)) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hlen : (lqNodes A P j).length = 1 := by
    have h1 := lq_compType_A_rank (k0DiagOf A.row.T) (lqNodes A P j) (by rw [hct])
    rw [hct] at h1
    exact h1.symm
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 1 := by
    rw [lq_compRank A P j, hlen]
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 2 := by
    rw [lq_shape_K0 A P j, hct]
    rfl
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have htw : lqTw A P j = 1 := lq_tw_single A P j hlen
  have hdesc := lq_descriptor_eq A P j
  rw [hct] at hdesc
  have hlabel : A.row.D.orbits[j].lab = ⟨.A, 1, A.row.D.orbits[j].lab.n⟩ := by
    have h := congrArg (fun o => o.lab) hdesc
    simp only [k0LabelOf, htw, if_true] at h
    rw [h]
  have hN2 : 2 ≤ A.row.D.orbits[j].lab.n := by
    by_contra hlt
    have hN1 : A.row.D.orbits[j].lab.n = 1 := by omega
    have := (lq_qs_false_iff A P j).2 ⟨by rw [hct], Or.inl ⟨htw, by rw [hct]⟩, hN1⟩
    rw [hj] at this
    exact absurd this (by decide)
  refine ⟨by rw [hlabel]; exact ⟨hn1, le_refl 1, fun _ => hN2⟩, ?_⟩
  have h := lq_rec_A1 A.setup A.a_torus (P.repr j) hrank hn (lq_qpow A P j) hN2
  rw [hlabel]
  exact h

private theorem lk0xlqrows_rec_E7_gen
    {τ : Tag} (hτ : τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h7 : compRank (componentRoots (rootCharHom a) i) = 7)
    (hn : (componentRoots (rootCharHom a) i).ncard = 126)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.E7, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  subst hτ
  exact lq_rec_E7 S hp hpL hT hTp i h7 hn hinner hN

theorem lq_row_E7
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (hE : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E7) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  obtain ⟨hlen, hTne⟩ := (lq_fam_facts A P j).2.1 hE
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 126 := by
    rw [lq_shape_K0 A P j]
    generalize k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = x at hE
    obtain ⟨f, r⟩ := x
    simp only at hE
    subst hE
    rfl
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 7 := by
    rw [lq_compRank A P j, hlen]
  have hlt := lq_ncard_lt_rootCount A P j
  rw [hn] at hlt
  have hτ : A.tau = .E8 := by
    obtain ⟨hr6, hr7, hr8, hr4⟩ := lk0xlqrows_rootCount
    rcases lk0xlqrows_tau A with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hTne
    · rw [h] at hlt
      omega
    · rw [h] at hlt
      omega
    · exact h
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hdesc := lq_descriptor_eq A P j
  have hlabel : A.row.D.orbits[j].lab = ⟨.E7, 0, A.row.D.orbits[j].lab.n⟩ := by
    have h := congrArg (fun o => o.lab) hdesc
    rw [hE] at h
    simp only [k0LabelOf] at h
    rw [h]
  refine ⟨by rw [hlabel]; exact ⟨hn1, rfl⟩, ?_⟩
  have hinner := lq_twistInner_of_shape A P j hrank hn (by omega) (by omega) (by omega) (by omega)
  have h := lk0xlqrows_rec_E7_gen hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp (P.repr j)
    hrank hn hinner (lq_qpow A P j)
  rw [hlabel]
  exact h

theorem lq_row_E6
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (hE : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .E6) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  obtain ⟨hlen, hTne⟩ := (lq_fam_facts A P j).1 hE
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 72 := by
    rw [lq_shape_K0 A P j]
    generalize k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = x at hE
    obtain ⟨f, r⟩ := x
    simp only at hE
    subst hE
    rfl
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 6 := by
    rw [lq_compRank A P j, hlen]
  have hlt := lq_ncard_lt_rootCount A P j
  rw [hn] at hlt
  have hτ : A.tau = .E7 ∨ A.tau = .E8 := by
    obtain ⟨hr6, hr7, hr8, hr4⟩ := lk0xlqrows_rootCount
    rcases lk0xlqrows_tau A with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hTne
    · rw [h] at hlt
      omega
    · exact Or.inl h
    · exact Or.inr h
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hdesc := lq_descriptor_eq A P j
  obtain ⟨hk1, hk2⟩ := lq_kind_E6 A P j hlen hE (by rw [hn])
  by_cases htw : lqTw A P j = 1
  · have hlabel : A.row.D.orbits[j].lab = ⟨.E6, 0, A.row.D.orbits[j].lab.n⟩ := by
      have h := congrArg (fun o => o.lab) hdesc
      rw [hE] at h
      simp only [k0LabelOf, htw, if_true] at h
      rw [h]
    refine ⟨by rw [hlabel]; exact ⟨hn1, rfl⟩, ?_⟩
    have h := lq_rec_E6 hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp (P.repr j) hrank hn
      (hk1 htw) (lq_qpow A P j)
    rw [hlabel]
    exact h
  · have hlabel : A.row.D.orbits[j].lab = ⟨.twE6, 0, A.row.D.orbits[j].lab.n⟩ := by
      have h := congrArg (fun o => o.lab) hdesc
      rw [hE] at h
      simp only [k0LabelOf] at h
      rw [if_neg htw] at h
      rw [h]
    refine ⟨by rw [hlabel]; exact ⟨hn1, rfl⟩, ?_⟩
    have h := lq_rec_twE6 A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp A.a_ne (P.repr j)
      (hk2 htw) hrank (lq_qpow A P j)
    rw [hlabel]
    exact h

private theorem lk0xlqrows_rec_C_gen
    {τ : Tag} (hτ : τ = .F4) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : compRank (componentRoots (rootCharHom a) i) = 3)
    (hn : (componentRoots (rootCharHom a) i).ncard = 18)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.C, 3, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have h := lq_rec_C hτ S hp hpL hT hTp h1 i h3 hn hinner hN
  rw [h3] at h
  exact h

private theorem lk0xlqrows_rec_C2_gen
    {τ : Tag} (hτ : τ = .F4) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : compRank (componentRoots (rootCharHom a) i) = 2)
    (hn : (componentRoots (rootCharHom a) i).ncard = 8)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N)
    (hN2 : 2 ≤ N) :
    GGHasLabel ⟨.C, 2, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  have h := lq_rec_C2 hτ S hp hpL hT hTp h1 i h2 hn hinner hN hN2
  rw [h2] at h
  exact h

private theorem lk0xlqrows_rec_B2der_gen
    {τ : Tag} (hτ : τ = .F4) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : compRank (componentRoots (rootCharHom a) i) = 2)
    (hn : (componentRoots (rootCharHom a) i).ncard = 8)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N)
    (hN1 : N = 1) :
    GGHasLabel ⟨.B2der, 0, 1⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
  lq_rec_B2der hτ S hp hpL hT hTp h1 i h2 hn hinner hN hN1

private theorem lk0xlqrows_label_C2_one (tw : ℕ) {nEff : ℕ} (h : nEff = 1) :
    (k0LabelOf .C 2 tw nEff).lab = ⟨.B2der, 0, 1⟩ := by
  subst h
  rfl

private theorem lk0xlqrows_label_C2_ne (tw : ℕ) {nEff : ℕ} (h : nEff ≠ 1) :
    (k0LabelOf .C 2 tw nEff).lab = ⟨.C, 2, nEff⟩ := by
  unfold k0LabelOf
  dsimp only
  rw [if_neg (fun h' => h h'.2)]

private theorem lk0xlqrows_tau_F4 (A : K0LangMark Omega lab p R I phi) (hT : A.row.T = .F4) :
    A.tau = .F4 := by
  rcases lk0xlqrows_tau A with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd hT (by rw [h]; decide)
  · exact absurd hT (by rw [h]; decide)
  · exact absurd hT (by rw [h]; decide)

theorem lq_row_C
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) {r : ℕ}
    (hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.C, r)) (hr : 3 ≤ r) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hlen : (lqNodes A P j).length = r := by
    have h1 := lq_compType_rank_ACD (k0DiagOf A.row.T) (lqNodes A P j)
      (Or.inr (Or.inl (by rw [hct])))
    rw [hct] at h1
    exact h1.symm
  have hfc := (lq_fam_facts A P j).2.2.2.2.2.2.2.1 (by rw [hct])
  have hT : A.row.T = .F4 := (lq_fam_facts A P j).2.2.2.2.1 (by rw [hct])
  have hr4 : r ≠ 4 := by
    intro h4
    have hc : lqNodes A P j = [0, 1, 2, 3] := hfc.2.2 (by rw [hlen]; exact h4)
    obtain ⟨-, -, hz⟩ := lq_nodes_basic A P j
    have hs : ∀ x ∈ ([0, 1, 2, 3] : List ℕ), A.row.s.getD x 0 = 0 := fun x hx =>
      (hz x (by rw [hc]; exact hx)).2
    have hsum := ggKacShVecs_sum (k0DiagOf A.row.T).marks p A.row.s A.row.s_mem
    have hm : (k0DiagOf A.row.T).marks = [1, 2, 3, 4, 2] := by rw [hT]; rfl
    rw [Fin.sum_univ_eq_sum_range (fun i => (k0DiagOf A.row.T).marks.getD i 0 * A.row.s.getD i 0)
      _, hm] at hsum
    simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.range_zero,
      Finset.sum_empty] at hsum
    have h0 := hs 0 (by simp)
    have h1 := hs 1 (by simp)
    have h2 := hs 2 (by simp)
    have h3 := hs 3 (by simp)
    simp only [List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, h3] at hsum
    have hodd : p % 2 = 1 := hpair.1.eq_two_or_odd.resolve_left hpair.2.1
    omega
  have hr3 : r = 3 := by
    have h4 := hfc.2.1
    rw [hlen] at h4
    omega
  subst hr3
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 3 := by
    rw [lq_compRank A P j, hlen]
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 18 := by
    rw [lq_shape_K0 A P j, hct]
    rfl
  have hτ : A.tau = .F4 := lk0xlqrows_tau_F4 A hT
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hdesc := lq_descriptor_eq A P j
  rw [hct] at hdesc
  have hlabel : A.row.D.orbits[j].lab = ⟨.C, 3, A.row.D.orbits[j].lab.n⟩ := by
    have h := congrArg (fun o => o.lab) hdesc
    simp only [k0LabelOf] at h
    rw [if_neg (fun h2 => by omega)] at h
    rw [h]
  refine ⟨by rw [hlabel]; exact ⟨hn1, by norm_num, fun h => by
    exfalso
    have h1 : 3 = 2 := h
    omega⟩, ?_⟩
  have hin := lq_twistInner_of_shape A P j hrank hn (by omega) (by omega) (by omega) (by omega)
  have h := lk0xlqrows_rec_C_gen hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp A.a_ne
    (P.repr j) hrank hn hin (lq_qpow A P j)
  rw [hlabel]
  exact h

theorem lq_row_C2
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length)
    (hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.C, 2)) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hlen : (lqNodes A P j).length = 2 := by
    have h1 := lq_compType_rank_ACD (k0DiagOf A.row.T) (lqNodes A P j)
      (Or.inr (Or.inl (by rw [hct])))
    rw [hct] at h1
    exact h1.symm
  have hrank : compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 2 := by
    rw [lq_compRank A P j, hlen]
  have hn : (componentRoots (rootCharHom A.a) (P.repr j)).ncard = 8 := by
    rw [lq_shape_K0 A P j, hct]
    rfl
  have hτ : A.tau = .F4 :=
    lk0xlqrows_tau_F4 A ((lq_fam_facts A P j).2.2.2.2.1 (by rw [hct]))
  have hn1 : 1 ≤ A.row.D.orbits[j].lab.n := lq_orbit_n_pos A P j hlab.1
  have hTp : rootDiagUnit A.tau A.a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall A.a_pow
  have hin := lq_twistInner_of_shape A P j hrank hn (by omega) (by omega) (by omega) (by omega)
  have hdesc := lq_descriptor_eq A P j
  have hnE : A.row.D.orbits[j].lab.n = (P.orbitNodes j).length * lab.n := by
    rw [hdesc, k0LabelOf_lab_n]
  rw [hct] at hdesc
  by_cases hN1 : A.row.D.orbits[j].lab.n = 1
  · have hlabel : A.row.D.orbits[j].lab = ⟨.B2der, 0, 1⟩ := by
      rw [hdesc]
      exact lk0xlqrows_label_C2_one _ (by rw [← hnE]; exact hN1)
    refine ⟨by rw [hlabel]; exact ⟨le_refl 1, rfl, rfl⟩, ?_⟩
    have h := lk0xlqrows_rec_B2der_gen hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp
      A.a_ne (P.repr j) hrank hn hin (lq_qpow A P j) hN1
    rw [hlabel]
    exact h
  · have hlabel : A.row.D.orbits[j].lab = ⟨.C, 2, A.row.D.orbits[j].lab.n⟩ := by
      rw [hnE, hdesc]
      exact lk0xlqrows_label_C2_ne _ (by rw [← hnE]; exact hN1)
    have hN2 : 2 ≤ A.row.D.orbits[j].lab.n := by omega
    refine ⟨by rw [hlabel]; exact ⟨hn1, le_refl 2, fun _ => hN2⟩, ?_⟩
    have h := lk0xlqrows_rec_C2_gen hτ A.setup hpair.1 (lq_p_ne_zero hpair) A.a_torus hTp
      A.a_ne (P.repr j) hrank hn hin (lq_qpow A P j) hN2
    rw [hlabel]
    exact h

theorem lq_row_all
    (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = true) :
    LargeEvenInLambda2 A.row.D.orbits[j].lab ∧
      GGHasLabel A.row.D.orbits[j].lab
        (↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j)) ⧸
          Subgroup.center
            ↥(rationalComponent A.setup.ρ A.setup.Γ (rootCharHom A.a) (P.repr j))) := by
  have hfam := lq_fam_facts A P j
  have hlenpos : 1 ≤ (lqNodes A P j).length := List.length_pos_iff.mpr (lq_nodes_basic A P j).1
  have hlt := lq_ncard_lt_rootCount A P j
  rw [lq_shape_K0 A P j] at hlt
  rcases lq_fam_cases (k0DiagOf A.row.T) (lqNodes A P j) with hA | hC | hD | h6 | h7 | h8 | hF | hG
  · have hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.A, (lqNodes A P j).length) :=
      Prod.ext hA (lq_compType_A_rank _ _ hA)
    by_cases h1 : (lqNodes A P j).length = 1
    · rw [h1] at hct
      exact lq_row_A1 hlab hpair A P j hj hct
    · exact lq_row_A hlab hpair A P j hj hct (by omega)
  · have hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.C, (lqNodes A P j).length) :=
      Prod.ext hC (lq_compType_rank_ACD _ _ (Or.inr (Or.inl hC)))
    have hr2 := (hfam.2.2.2.2.2.2.2.1 hC).1
    by_cases h2 : (lqNodes A P j).length = 2
    · rw [h2] at hct
      exact lq_row_C2 hlab hpair A P j hct
    · exact lq_row_C hlab hpair A P j hct (by omega)
  · have hct : k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.D, (lqNodes A P j).length) :=
      Prod.ext hD (lq_compType_rank_ACD _ _ (Or.inr (Or.inr hD)))
    exact lq_row_D hlab hpair A P j hct (hfam.2.2.2.2.2.2.2.2 hD)
  · exact lq_row_E6 hlab hpair A P j h6
  · exact lq_row_E7 hlab hpair A P j h7
  · exfalso
    obtain ⟨-, hT8⟩ := hfam.2.2.1 h8
    have hc : lqShapeCount (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)) = 240 := by
      generalize k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = x at h8
      obtain ⟨f, r⟩ := x
      simp only at h8
      subst h8
      rfl
    rw [hc] at hlt
    obtain ⟨hr6, hr7, hr8, hr4⟩ := lk0xlqrows_rootCount
    rcases lk0xlqrows_tau A with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hlt <;> omega
  · exfalso
    obtain ⟨-, hTF⟩ := hfam.2.2.2.1 hF
    have hc : lqShapeCount (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)) = 48 := by
      generalize k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = x at hF
      obtain ⟨f, r⟩ := x
      simp only at hF
      subst hF
      rfl
    rw [hc] at hlt
    obtain ⟨hr6, hr7, hr8, hr4⟩ := lk0xlqrows_rootCount
    rcases lk0xlqrows_tau A with ⟨-, h⟩ | ⟨hT, h⟩ | ⟨hT, h⟩ | ⟨hT, h⟩
    · rw [h] at hlt
      omega
    · rw [hT] at hTF
      exact absurd hTF (by decide)
    · rw [hT] at hTF
      exact absurd hTF (by decide)
    · rw [hT] at hTF
      exact absurd hTF (by decide)
  · exact absurd hG hfam.2.2.2.2.2.2.1

end CFSG.StandardType.GGK0LQ

end

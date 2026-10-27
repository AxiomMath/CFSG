module

public import CFSG.Monster.B.Classical.UnitarySixCounts
public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import CFSG.Monster.B.Classical.UnitarySixPoints
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open scoped LinearAlgebra.Projectivization

theorem rep_pt {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    ∃ a : F4ˣ, a • v = (pt v hv0 hv).1.rep :=
  Projectivization.exists_smul_eq_mk_rep F4 v hv0

theorem card_units_F4 : Fintype.card F4ˣ = 3 := by
  rw [Fintype.card_units, F4.card]

theorem card_vec_eq_three_mul (P : V → Prop) [DecidablePred P]
    (hP : ∀ (c : F4) (v : V), c ≠ 0 → (P (c • v) ↔ P v)) [Fintype {p : IsoPt // P p.1.rep}] :
    Fintype.card {v : V // v ≠ 0 ∧ herm v v = 0 ∧ P v} =
      3 * Fintype.card {p : IsoPt // P p.1.rep} := by
  classical
  let G : {p : IsoPt // P p.1.rep} × F4ˣ → {v : V // v ≠ 0 ∧ herm v v = 0 ∧ P v} :=
    fun x => ⟨(x.2 : F4) • x.1.1.1.rep, smul_ne_zero x.2.ne_zero x.1.1.1.rep_nonzero, by
      rw [herm_smul_left, herm_smul_right, isIsoPt_of x.1.1, mul_zero, mul_zero],
      (hP _ _ x.2.ne_zero).2 x.1.2⟩
  have hG : Function.Bijective G := by
    constructor
    · rintro ⟨⟨p, hp⟩, a⟩ ⟨⟨q, hq⟩, b⟩ h
      have h' : (a : F4) • p.1.rep = (b : F4) • q.1.rep := congrArg Subtype.val h
      have hpq : p = q := by
        rw [← pt_rep p, ← pt_rep q, pt_eq_pt_iff]
        refine ⟨(a : F4)⁻¹ * b, ?_⟩
        rw [mul_smul, ← h', smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
      subst hpq
      have hab : (a : F4) = b := by
        have h2 : ((a : F4) - b) • p.1.rep = 0 := by rw [sub_smul, h', sub_self]
        rcases smul_eq_zero.1 h2 with h3 | h3
        · exact sub_eq_zero.1 h3
        · exact absurd h3 p.1.rep_nonzero
      rw [Units.val_inj] at hab
      subst hab
      rfl
    · rintro ⟨v, hv0, hv, hPv⟩
      obtain ⟨a, ha⟩ := rep_pt hv0 hv
      refine ⟨⟨⟨pt v hv0 hv, ?_⟩, a⁻¹⟩, ?_⟩
      · rw [← ha]
        exact (hP _ _ a.ne_zero).2 hPv
      · apply Subtype.ext
        change ((a⁻¹ : F4ˣ) : F4) • (pt v hv0 hv).1.rep = v
        rw [← ha, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul]
  rw [← Fintype.card_of_bijective hG, Fintype.card_prod, card_units_F4, mul_comm]

noncomputable instance : Fintype IsoPt := Fintype.ofFinite _

noncomputable instance : DecidableRel isoGraph.Adj := Classical.decRel _

theorem rep_ne_zero (q : IsoPt) : q.1.rep ≠ 0 := q.1.rep_nonzero

theorem stdPt_eq_iff (j : Fin 6) (q : IsoPt) :
    stdPt j = q ↔ ∀ i, i ≠ j → q.1.rep i = 0 := by
  conv_lhs => rw [← pt_rep q]
  rw [stdPt, pt_eq_pt_iff]
  constructor
  · rintro ⟨c, hc⟩ i hij
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have := congrFun hc j
      simp at this
    have := congrFun hc i
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hij] at this
    exact (mul_eq_zero.1 this).resolve_left hc0
  · intro h
    have hj : q.1.rep j ≠ 0 := by
      intro hj
      apply rep_ne_zero q
      funext i
      by_cases hij : i = j
      · subst hij; exact hj
      · exact h i hij
    refine ⟨(q.1.rep j)⁻¹, ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij
      rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hj, Pi.single_eq_same]
    · rw [Pi.smul_apply, smul_eq_mul, h i hij, mul_zero, Pi.single_eq_of_ne hij]

theorem orth_stdPt_iff (j : Fin 6) (q : IsoPt) :
    Orth (stdPt j).1 q.1 ↔ herm (Pi.single j 1) q.1.rep = 0 := by
  have h := orth_mk (v := Pi.single j 1) (w := q.1.rep) (by simp) q.1.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h

theorem adj_stdPt_iff (j : Fin 6) (q : IsoPt) :
    isoGraph.Adj (stdPt j) q ↔
      herm (Pi.single j 1) q.1.rep = 0 ∧ ∃ i : Fin 6, i ≠ j ∧ q.1.rep i ≠ 0 := by
  rw [isoGraph_adj, orth_stdPt_iff, and_comm, Ne, stdPt_eq_iff]
  push Not
  rfl

theorem scale_invariant_herm_single (j : Fin 6) :
    ∀ (c : F4) (v : V), c ≠ 0 → (herm (Pi.single j 1) (c • v) = 0 ↔
      herm (Pi.single j 1) v = 0) := by
  intro c v hc
  rw [herm_smul_right, mul_eq_zero, or_iff_right (fun h => hc (bar_eq_zero_iff.1 h))]

theorem scale_invariant_support (j : Fin 6) :
    ∀ (c : F4) (v : V), c ≠ 0 → ((∃ i : Fin 6, i ≠ j ∧ (c • v) i ≠ 0) ↔
      ∃ i : Fin 6, i ≠ j ∧ v i ≠ 0) := by
  intro c v hc
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]

theorem card_isoPt : Fintype.card IsoPt = 693 := by
  have h := card_vec_eq_three_mul (fun _ => True) (fun _ _ _ => Iff.rfl)
  rw [card_isotropic_vec] at h
  have h2 : Fintype.card {p : IsoPt // True} = Fintype.card IsoPt :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
  omega

theorem card_neighborSet_stdPt : Fintype.card (isoGraph.neighborSet (stdPt 0)) = 180 := by
  have h := card_vec_eq_three_mul
    (fun v => herm (Pi.single 0 1) v = 0 ∧ ∃ i : Fin 6, i ≠ 0 ∧ v i ≠ 0)
    (fun c v hc => and_congr (scale_invariant_herm_single 0 c v hc)
      (scale_invariant_support 0 c v hc))
  rw [card_neighbor_vec] at h
  have h2 : Fintype.card (isoGraph.neighborSet (stdPt 0)) =
      Fintype.card {q : IsoPt // herm (Pi.single 0 1) q.1.rep = 0 ∧
        ∃ i : Fin 6, i ≠ 0 ∧ q.1.rep i ≠ 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun q => adj_stdPt_iff 0 q)
  omega

theorem card_commonNeighbors_adj :
    Fintype.card (isoGraph.commonNeighbors (stdPt 0) (stdPt 1)) = 51 := by
  have h := card_vec_eq_three_mul
    (fun v => herm (Pi.single 0 1) v = 0 ∧ herm (Pi.single 1 1) v = 0 ∧
      (∃ i : Fin 6, i ≠ 0 ∧ v i ≠ 0) ∧ ∃ i : Fin 6, i ≠ 1 ∧ v i ≠ 0)
    (fun c v hc => and_congr (scale_invariant_herm_single 0 c v hc)
      (and_congr (scale_invariant_herm_single 1 c v hc)
        (and_congr (scale_invariant_support 0 c v hc) (scale_invariant_support 1 c v hc))))
  rw [card_common_adj_vec] at h
  have h2 : Fintype.card (isoGraph.commonNeighbors (stdPt 0) (stdPt 1)) =
      Fintype.card {q : IsoPt // herm (Pi.single 0 1) q.1.rep = 0 ∧
        herm (Pi.single 1 1) q.1.rep = 0 ∧ (∃ i : Fin 6, i ≠ 0 ∧ q.1.rep i ≠ 0) ∧
          ∃ i : Fin 6, i ≠ 1 ∧ q.1.rep i ≠ 0} := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [SimpleGraph.mem_commonNeighbors, adj_stdPt_iff, adj_stdPt_iff]
    tauto
  omega

theorem card_commonNeighbors_nonadj :
    Fintype.card (isoGraph.commonNeighbors (stdPt 0) (stdPt 5)) = 45 := by
  have h := card_vec_eq_three_mul
    (fun v => herm (Pi.single 0 1) v = 0 ∧ herm (Pi.single 5 1) v = 0)
    (fun c v hc => and_congr (scale_invariant_herm_single 0 c v hc)
      (scale_invariant_herm_single 5 c v hc))
  rw [card_common_nonadj_vec] at h
  have key : ∀ v : V, herm (Pi.single 0 1) v = 0 → herm (Pi.single 5 1) v = 0 →
      (∃ i : Fin 6, i ≠ 0 ∧ v i ≠ 0) ∨ v = 0 := by
    intro v h0 h5
    by_cases hv : v = 0
    · exact Or.inr hv
    · left
      by_contra hne
      push Not at hne
      apply hv
      funext i
      by_cases hi : i = 0
      · subst hi
        rw [herm_single_left] at h5
        exact bar_eq_zero_iff.1 h5
      · exact hne i hi
  have key5 : ∀ v : V, herm (Pi.single 0 1) v = 0 → herm (Pi.single 5 1) v = 0 →
      (∃ i : Fin 6, i ≠ 5 ∧ v i ≠ 0) ∨ v = 0 := by
    intro v h0 h5
    by_cases hv : v = 0
    · exact Or.inr hv
    · left
      by_contra hne
      push Not at hne
      apply hv
      funext i
      by_cases hi : i = 5
      · subst hi
        rw [herm_single_left] at h0
        exact bar_eq_zero_iff.1 h0
      · exact hne i hi
  have h2 : Fintype.card (isoGraph.commonNeighbors (stdPt 0) (stdPt 5)) =
      Fintype.card {q : IsoPt // herm (Pi.single 0 1) q.1.rep = 0 ∧
        herm (Pi.single 5 1) q.1.rep = 0} := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [SimpleGraph.mem_commonNeighbors, adj_stdPt_iff, adj_stdPt_iff]
    constructor
    · rintro ⟨⟨h0, -⟩, h5, -⟩
      exact ⟨h0, h5⟩
    · rintro ⟨h0, h5⟩
      exact ⟨⟨h0, (key _ h0 h5).resolve_right (rep_ne_zero q)⟩,
        h5, (key5 _ h0 h5).resolve_right (rep_ne_zero q)⟩
  omega

theorem card_neighborSet_smul (g : SU frobeniusF4 6) (p : IsoPt) :
    Fintype.card (isoGraph.neighborSet (g • p)) = Fintype.card (isoGraph.neighborSet p) := by
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun q => ?_)
  change isoGraph.Adj (g • p) q ↔ isoGraph.Adj p (g⁻¹ • q)
  rw [← isoGraph_adj_smul g p (g⁻¹ • q), smul_inv_smul]

theorem card_commonNeighbors_smul (g : SU frobeniusF4 6) (p q : IsoPt) :
    Fintype.card (isoGraph.commonNeighbors (g • p) (g • q)) =
      Fintype.card (isoGraph.commonNeighbors p q) := by
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun r => ?_)
  change r ∈ isoGraph.commonNeighbors (g • p) (g • q) ↔
    g⁻¹ • r ∈ isoGraph.commonNeighbors p q
  rw [SimpleGraph.mem_commonNeighbors, SimpleGraph.mem_commonNeighbors,
    ← isoGraph_adj_smul g p (g⁻¹ • r), ← isoGraph_adj_smul g q (g⁻¹ • r), smul_inv_smul]

theorem isSRGWith : isoGraph.IsSRGWith 693 180 51 45 where
  card := card_isoPt
  regular p := by
    obtain ⟨g, rfl⟩ := exists_SU_smul_stdPt p
    rw [← SimpleGraph.card_neighborSet_eq_degree, card_neighborSet_smul, card_neighborSet_stdPt]
  of_adj p q hpq := by
    obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_adj p q hpq
    rw [card_commonNeighbors_smul, card_commonNeighbors_adj]
  of_not_adj p q hpq hna := by
    obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_nonadj p q hpq hna
    rw [card_commonNeighbors_smul, card_commonNeighbors_nonadj]

theorem scalar_smul_eq (z : SU frobeniusF4 6) (hz : z ∈ scalars) (p : IsoPt) : z • p = p := by
  obtain ⟨a, rfl⟩ := hz
  induction p using IsoPt.ind with
  | h v hv0 hv =>
    rw [smul_pt]
    refine (pt_eq_pt_iff _ _ _ _).mpr ⟨a, ?_⟩
    rw [smul_def, coe_scalarHom, scalar_mulVec]

theorem scalars_le_ker : scalars ≤ (MulAction.toPermHom (SU frobeniusF4 6) IsoPt).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  exact Equiv.ext fun p => scalar_smul_eq z hz p

@[expose] noncomputable def projAct : ProjSU →* Equiv.Perm IsoPt :=
  QuotientGroup.lift scalars (MulAction.toPermHom (SU frobeniusF4 6) IsoPt) scalars_le_ker

theorem projAct_mk (g : SU frobeniusF4 6) (p : IsoPt) : projAct (g : ProjSU) p = g • p := rfl

theorem projAct_transitive (p q : IsoPt) : ∃ x : ProjSU, projAct x p = q := by
  obtain ⟨g, rfl⟩ := exists_SU_smul_stdPt p
  obtain ⟨h, rfl⟩ := exists_SU_smul_stdPt q
  exact ⟨((h * g⁻¹ : SU frobeniusF4 6) : ProjSU), by rw [projAct_mk, mul_smul, inv_smul_smul]⟩

theorem projAct_transitive_adj (p q p' q' : IsoPt) (h : isoGraph.Adj p q)
    (h' : isoGraph.Adj p' q') : ∃ x : ProjSU, projAct x p = p' ∧ projAct x q = q' := by
  obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_adj p q h
  obtain ⟨g', rfl, rfl⟩ := exists_SU_smul_adj p' q' h'
  exact ⟨((g' * g⁻¹ : SU frobeniusF4 6) : ProjSU), by rw [projAct_mk, mul_smul, inv_smul_smul],
    by rw [projAct_mk, mul_smul, inv_smul_smul]⟩

theorem projAct_transitive_nonadj (p q p' q' : IsoPt) (hpq : p ≠ q) (h : ¬isoGraph.Adj p q)
    (hpq' : p' ≠ q') (h' : ¬isoGraph.Adj p' q') :
    ∃ x : ProjSU, projAct x p = p' ∧ projAct x q = q' := by
  obtain ⟨g, rfl, rfl⟩ := exists_SU_smul_nonadj p q hpq h
  obtain ⟨g', rfl, rfl⟩ := exists_SU_smul_nonadj p' q' hpq' h'
  exact ⟨((g' * g⁻¹ : SU frobeniusF4 6) : ProjSU), by rw [projAct_mk, mul_smul, inv_smul_smul],
    by rw [projAct_mk, mul_smul, inv_smul_smul]⟩

theorem eq_scalar_of_fix_matrix (M : Matrix (Fin 6) (Fin 6) F4)
    (hcol : ∀ j, ∃ c : F4, M *ᵥ Pi.single j 1 = c • Pi.single j 1)
    (hpair : ∀ i j : Fin 6, (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] →
      ∃ c : F4, M *ᵥ (Pi.single i 1 + Pi.single j 1) = c • (Pi.single i 1 + Pi.single j 1)) :
    M = Matrix.scalar (Fin 6) (M 0 0) := by
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    obtain ⟨c, hc⟩ := hcol j
    have := congrFun hc i
    rwa [Matrix.mulVec_single_one, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero] at this
  have hdiag : ∀ i j : Fin 6, (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] →
      M i i = M j j := by
    intro i j hij
    have hne : i ≠ j := by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    obtain ⟨c, hc⟩ := hpair i j hij
    have hi := congrFun hc i
    have hj := congrFun hc j
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hi hj
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm, Matrix.col_apply, hoff i j hne,
      hoff j i hne.symm, add_zero, zero_add, mul_one] at hi hj
    rw [hi, hj]
  have h1 := hdiag 0 1 (by simp)
  have h2 := hdiag 0 2 (by simp)
  have h3 := hdiag 0 3 (by simp)
  have h4 := hdiag 0 4 (by simp)
  have h5 := hdiag 1 5 (by simp)
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    fin_cases i
    · rfl
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact (h1.trans h5).symm
  · rw [ite_eq_right hij, hoff i j hij]

theorem exists_mulVec_eq_smul_of_fix (g : SU frobeniusF4 6) {v : V} (hv0 : v ≠ 0)
    (hv : herm v v = 0) (h : g • pt v hv0 hv = pt v hv0 hv) :
    ∃ c : F4, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = c • v := by
  rw [smul_pt, pt_eq_pt_iff] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [← smul_def, ← hc]⟩

theorem mem_scalars_of_fix (g : SU frobeniusF4 6)
    (hcol : ∀ j, g • stdPt j = stdPt j)
    (hpair : ∀ i j : Fin 6, ∀ hij : (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)],
      g • pt _ (pair_isotropic i j hij).2 (pair_isotropic i j hij).1 =
        pt _ (pair_isotropic i j hij).2 (pair_isotropic i j hij).1) :
    g ∈ scalars := by
  rw [mem_scalars]
  exact ⟨_, eq_scalar_of_fix_matrix _
    (fun j => exists_mulVec_eq_smul_of_fix g _ _ (hcol j))
    (fun i j hij => exists_mulVec_eq_smul_of_fix g _ _ (hpair i j hij))⟩

theorem fix_all_iff_mem_scalars (g : SU frobeniusF4 6) :
    (∀ p : IsoPt, g • p = p) ↔ g ∈ scalars :=
  ⟨fun h => mem_scalars_of_fix g (fun _ => h _) (fun _ _ _ => h _),
    fun hg p => scalar_smul_eq g hg p⟩

theorem projAct_injective : Function.Injective projAct := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [QuotientGroup.eq_one_iff]
    refine (fix_all_iff_mem_scalars g).1 fun p => ?_
    rw [← projAct_mk, hx]
    rfl

end CFSG.Monster.B.Classical.UnitarySix

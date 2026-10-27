module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Mat
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainRecOut

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

theorem isConjLineIn_iff_exists_mulVec (B : Basis3 G k) (u : Coords k) {e : Coords k}
    (he : e ≠ 0) :
    IsConjLineIn B.span (B.vec u) (B.line e) ↔
      (∃ A ∈ (ggAutomizer ⊤ B.span).map B.glHom,
        (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ u = e) ∨
      (∃ A ∈ (ggAutomizer ⊤ B.span).map B.glHom,
        (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ u = -e) := by
  constructor
  · rintro ⟨g, hgN, hg⟩
    obtain ⟨x, hx, hxv⟩ := B.exists_xg_of_mem_normalizer hgN
    rw [hxv] at hg
    have hmem : B.vec e ∈
        Subgroup.zpowers (B.vec ((x : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ u)) := by
      rw [hg]
      exact Subgroup.mem_zpowers _
    rcases B.eq_or_eq_neg_of_vec_mem_zpowers he hmem with h | h
    · exact Or.inl ⟨x, hx, h.symm⟩
    · exact Or.inr ⟨x, hx, by rw [h, neg_neg]⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      rw [hgv, h]
      rfl
    · obtain ⟨g, hgN, hgv⟩ := B.exists_conj_of_mem_xg hx
      refine ⟨g, hgN, ?_⟩
      rw [hgv, h, B.vec_neg_eq_inv, Subgroup.zpowers_inv]
      rfl

private theorem diagonal_mul_self_of_isSign {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) :
    Matrix.diagonal s * Matrix.diagonal s = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i => s i * s i) = fun _ => 1 from
    funext fun i => mul_self_of_isSign hs i, Matrix.diagonal_one]

private theorem diagonal_conj_conj {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s)
    (A : Matrix (Fin k) (Fin k) (ZMod 3)) :
    Matrix.diagonal s * (Matrix.diagonal s * A * Matrix.diagonal s) *
      Matrix.diagonal s = A := by
  rw [show Matrix.diagonal s * (Matrix.diagonal s * A * Matrix.diagonal s) *
      Matrix.diagonal s =
      (Matrix.diagonal s * Matrix.diagonal s) *
        (A * (Matrix.diagonal s * Matrix.diagonal s)) by
    simp only [Matrix.mul_assoc]]
  rw [diagonal_mul_self_of_isSign hs, Matrix.one_mul, Matrix.mul_one]

private theorem diagonal_mul_spMat_mul_diagonal {k : ℕ} (s t : Fin k → ZMod 3)
    (σ : Equiv.Perm (Fin k)) :
    Matrix.diagonal s * spMat σ t * Matrix.diagonal s =
      spMat σ (fun j => s (σ j) * t j * s j) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = σ j
  · rw [hij]
    simp [spMat_apply]
  · simp [spMat_apply, hij]

theorem acts_signed_iff (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s) {g : G}
    {A : Matrix (Fin k) (Fin k) (ZMod 3)} :
    (B.signed s hs).Acts g A ↔
      B.Acts g (Matrix.diagonal s * A * Matrix.diagonal s) := by
  have hD : ∀ (e : Coords k) (i : Fin k), (Matrix.diagonal s *ᵥ e) i = s i * e i := by
    intro e i
    rw [Matrix.mulVec_diagonal]
  have hmul : ∀ e : Coords k,
      (Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ e =
        Matrix.diagonal s *ᵥ (A *ᵥ (Matrix.diagonal s *ᵥ e)) := by
    intro e
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hDD : ∀ e : Coords k, Matrix.diagonal s *ᵥ (Matrix.diagonal s *ᵥ e) = e := by
    intro e
    funext i
    rw [hD, hD]
    show s i * (s i * e i) = e i
    rw [← mul_assoc, mul_self_of_isSign hs i, one_mul]
  constructor
  · intro hA j
    have h := (B.signed s hs).acts_vec hA (Matrix.diagonal s *ᵥ Pi.single j 1)
    have hL : (B.signed s hs).vec (Matrix.diagonal s *ᵥ Pi.single j 1) = B.b j := by
      rw [B.vec_signed, ← B.vec_single j]
      apply congrArg B.vec
      funext i
      rw [hD]
      rw [← mul_assoc, mul_self_of_isSign hs i, one_mul]
    have hR : (B.signed s hs).vec (A *ᵥ (Matrix.diagonal s *ᵥ Pi.single j 1)) =
        B.vec ((Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ Pi.single j 1) := by
      rw [B.vec_signed, hmul]
      apply congrArg B.vec
      funext i
      rw [hD]
    rw [hL, hR] at h
    have hcol : (Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ Pi.single j 1 =
        fun i => (Matrix.diagonal s * A * Matrix.diagonal s) i j := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hcol] at h
    exact h
  · intro hA j
    have h := B.acts_vec hA (Matrix.diagonal s *ᵥ Pi.single j 1)
    have hL : B.vec (Matrix.diagonal s *ᵥ Pi.single j 1) =
        (B.signed s hs).vec (Pi.single j 1) := by
      rw [B.vec_signed]
      apply congrArg B.vec
      funext i
      rw [hD]
    have hR : B.vec ((Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ
        (Matrix.diagonal s *ᵥ Pi.single j 1)) =
        (B.signed s hs).vec (A *ᵥ Pi.single j 1) := by
      rw [hmul, hDD, B.vec_signed]
      apply congrArg B.vec
      funext i
      rw [hD]
    rw [hL, hR] at h
    have hcol : A *ᵥ Pi.single j 1 = fun i => A i j := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hcol] at h
    rw [← (B.signed s hs).vec_single j]
    exact h

theorem realized_signed (B : Basis3 G k) {s : Fin k → ZMod 3} (hs : IsSign s)
    (H : Subgroup G) :
    (B.signed s hs).realized H =
      {A | ∃ M ∈ B.realized H, A = Matrix.diagonal s * M * Matrix.diagonal s} := by
  ext A
  constructor
  · rintro ⟨g, hg, hA⟩
    refine ⟨Matrix.diagonal s * A * Matrix.diagonal s,
      ⟨g, hg, (B.acts_signed_iff hs).mp hA⟩, (diagonal_conj_conj hs A).symm⟩
  · rintro ⟨M, ⟨g, hg, hM⟩, rfl⟩
    exact ⟨g, hg, (B.acts_signed_iff hs).mpr (by rwa [diagonal_conj_conj hs M])⟩

end Basis3

private theorem prod_mul_self_of_isSign {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) :
    (∏ i, s i) * (∏ i, s i) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => mul_self_of_isSign hs i

private theorem diagonal_conj_mem_evenAll0 {n : ℕ} {s : Fin (n + 1) → ZMod 3}
    (hs : IsSign s) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hM : M ∈ evenAll0 n) :
    Matrix.diagonal s * M * Matrix.diagonal s ∈ evenAll0 n := by
  obtain ⟨σ, t, ht, ⟨hσ0, hp⟩, rfl⟩ := hM
  refine ⟨σ, fun j => s (σ j) * t j * s j, ?_, ⟨hσ0, ?_⟩,
    Basis3.diagonal_mul_spMat_mul_diagonal s t σ⟩
  · intro j
    change s (σ j) * t j * s j = 1 ∨ s (σ j) * t j * s j = -1
    rcases hs (σ j) with h1 | h1 <;> rcases ht j with h2 | h2 <;>
      rcases hs j with h3 | h3 <;> rw [h1, h2, h3] <;> decide
  · have hpsq : (∏ j, s j) * (∏ j, s j) = 1 := prod_mul_self_of_isSign hs
    calc ∏ j, s (σ j) * t j * s j
        = (∏ j, s (σ j)) * (∏ j, t j) * (∏ j, s j) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      _ = 1 := by rw [Equiv.prod_comp σ s, hp, mul_one]; exact hpsq

private theorem row_quad_signed {n : ℕ} {s : Fin (n + 1) → ZMod 3} (hs : IsSign s)
    (hs0 : s 0 = 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hrow : ∀ j, j ≠ 0 → A 0 j = 0)
    (hquad : ∀ v : Coords (n + 1), v 0 = 0 →
      ∑ i, (A *ᵥ v) i ^ 2 = ∑ i, v i ^ 2) :
    (∀ j, j ≠ 0 → (Matrix.diagonal s * A * Matrix.diagonal s) 0 j = 0) ∧
      ∀ v : Coords (n + 1), v 0 = 0 →
        ∑ i, ((Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ v) i ^ 2 =
          ∑ i, v i ^ 2 := by
  have hD : ∀ (e : Coords (n + 1)) (i : Fin (n + 1)),
      (Matrix.diagonal s *ᵥ e) i = s i * e i := by
    intro e i
    rw [Matrix.mulVec_diagonal]
  have hmul : ∀ e : Coords (n + 1),
      (Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ e =
        Matrix.diagonal s *ᵥ (A *ᵥ (Matrix.diagonal s *ᵥ e)) := by
    intro e
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hsum : ∀ z : Coords (n + 1),
      ∑ i, (Matrix.diagonal s *ᵥ z) i ^ 2 = ∑ i, z i ^ 2 := by
    intro z
    apply Finset.sum_congr rfl
    intro i _
    rw [hD]
    rcases hs i with h | h
    · rw [h]
      ring
    · rw [h]
      calc (-1 * z i) ^ 2 = (-(z i)) ^ 2 := by ring
        _ = z i ^ 2 := neg_sq _
  constructor
  · intro j hj
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hs0, hrow j hj]
    simp
  · intro v hv
    have hv0 : (Matrix.diagonal s *ᵥ v) 0 = 0 := by
      rw [hD]
      simp [hs0, hv]
    calc ∑ i, ((Matrix.diagonal s * A * Matrix.diagonal s) *ᵥ v) i ^ 2
        = ∑ i, (A *ᵥ (Matrix.diagonal s *ᵥ v)) i ^ 2 := by rw [hmul, hsum]
      _ = ∑ i, (Matrix.diagonal s *ᵥ v) i ^ 2 := hquad (Matrix.diagonal s *ᵥ v) hv0
      _ = ∑ i, v i ^ 2 := hsum v

private theorem card_perm_fix_zero6 : Nat.card {σ : Equiv.Perm (Fin 6) // σ 0 = 0} = 120 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem card_signs6 :
    Nat.card {s : Fin 6 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 5, s i.succ = 1} = 16 := by
  have e : {s : Fin 6 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 5, s i.succ = 1} =
      {s : Fin 6 → ZMod 3 // (∀ i, s i = 1 ∨ s i = -1) ∧ s 0 = 1 ∧
        ∏ i : Fin 5, s i.succ = 1} := rfl
  rw [e, Nat.card_eq_fintype_card]
  decide +kernel

private theorem sign_eq_of_spMat_eq6 {σ τ : Equiv.Perm (Fin 6)} {s t : Fin 6 → ZMod 3}
    (hs : IsSign s) (h : spMat σ s = spMat τ t) : s = t := by
  have hστ := perm_eq_of_spMat_eq hs h
  subst hστ
  funext j
  have e := congrFun (congrFun h (σ j)) j
  rwa [spMat_apply, spMat_apply, if_pos rfl, if_pos rfl] at e

theorem card_stab_evenAll0 {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    (hS : StabMatHyp 5 (evenAll0 5) Xg) :
    Nat.card ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 6 → ZMod 3)) = 1920 := by
  classical
  let Q := {σ : Equiv.Perm (Fin 6) // σ 0 = 0} ×
    {s : Fin 6 → ZMod 3 // IsSign s ∧ s 0 = 1 ∧ ∏ i : Fin 5, s i.succ = 1}
  have hsm : ∀ (A : ↥Xg) (v : Fin 6 → ZMod 3),
      A • v = ((A : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v :=
    fun A v => by rw [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec]
  have hex : ∀ q : Q, ∃ A ∈ Xg,
      (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) = spMat q.1.1 q.2.1 := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, hs, hs0, hp⟩⟩
    refine hS.sub _ ⟨σ, s, hs, ⟨hσ, ?_⟩, rfl⟩
    rw [Fin.prod_univ_succ, hs0, one_mul]
    exact hp
  have hfix : ∀ q : Q, spMat q.1.1 q.2.1 *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rintro ⟨⟨σ, hσ⟩, ⟨s, -, hs0, -⟩⟩
    have hσ' : σ.symm 0 = 0 := by rw [Equiv.symm_apply_eq, hσ]
    rw [spMat_mulVec]
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [hσ', hs0]
    · have hne : σ.symm i ≠ 0 := fun h' =>
        hi (by rw [← Equiv.apply_symm_apply σ i, h', hσ])
      simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hi]
  let Φ : Q → ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 6 → ZMod 3)) := fun q =>
    ⟨⟨(hex q).choose, (hex q).choose_spec.1⟩, by
      rw [MulAction.mem_stabilizer_iff, hsm]
      show ((hex q).choose : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ _ = _
      rw [(hex q).choose_spec.2]
      exact hfix q⟩
  have hΦ : ∀ q, (((Φ q : ↥Xg) : GL (Fin 6) (ZMod 3)) :
      Matrix (Fin 6) (Fin 6) (ZMod 3)) = spMat q.1.1 q.2.1 :=
    fun q => (hex q).choose_spec.2
  have hbij : Function.Bijective Φ := by
    constructor
    · intro q q' hq
      have e := congrArg (fun A :
          ↥(MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 6 → ZMod 3)) =>
        (((A : ↥Xg) : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3))) hq
      simp only [hΦ] at e
      obtain ⟨⟨σ, hσ⟩, ⟨s, hs, hs'⟩⟩ := q
      obtain ⟨⟨σ', hσ''⟩, ⟨s', hs'', hs'''⟩⟩ := q'
      have h1 := perm_eq_of_spMat_eq hs e
      have h2 := sign_eq_of_spMat_eq6 hs e
      subst h1
      subst h2
      rfl
    · rintro ⟨⟨A, hA⟩, hAs⟩
      rw [MulAction.mem_stabilizer_iff, hsm] at hAs
      have hcol : ∀ i, i ≠ 0 →
          (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) i 0 = 0 := by
        intro i hi
        have e := congrFun hAs i
        rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_eq_of_ne hi] at e
      obtain ⟨σ, s, hs, ⟨hσ0, hprod⟩, hAe⟩ := hS.norm A hA hcol
      have hs0 : s 0 = 1 := by
        have h := congrFun hAs 0
        rw [hAe, spMat_mulVec_single, hσ0] at h
        simpa using h
      have hp5 : ∏ i : Fin 5, s i.succ = 1 := by
        rw [Fin.prod_univ_succ, hs0, one_mul] at hprod
        exact hprod
      refine ⟨(⟨σ, hσ0⟩, ⟨s, hs, hs0, hp5⟩), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      rw [hΦ]
      exact hAe.symm
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod, card_perm_fix_zero6,
    card_signs6]

private theorem ncard_of_card6 {p : (Fin 6 → ZMod 3) → Prop} [DecidablePred p] {n : ℕ}
    (h : (Finset.univ.filter p).card = n) : {v : Fin 6 → ZMod 3 | p v}.ncard = n := by
  rw [← h, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

private theorem card_orbit_shape6 (ε : ZMod 3) (hε : ε = 1 ∨ ε = -1) :
    {e : Fin 6 → ZMod 3 | e ≠ 0 ∧
      ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))}.ncard = 54 := by
  have h : ∀ e : Fin 6 → ZMod 3, (e ≠ 0 ∧
      ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))) ↔
      ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε)) := by
    intro e
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with h | h
      · exact absurd h.2 (by decide)
      · unfold wt at h
        simp at h
  rw [show {e : Fin 6 → ZMod 3 | e ≠ 0 ∧
      ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))} =
      {e : Fin 6 → ZMod 3 |
        ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))} from Set.ext h]
  rcases hε with rfl | rfl
  · exact ncard_of_card6 (by decide +kernel)
  · exact ncard_of_card6 (by decide +kernel)

private theorem card_of_stabMatHyp {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    (hS : StabMatHyp 5 (evenAll0 5) Xg) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1)
    (horb : ∀ e : Fin 6 → ZMod 3, e ≠ 0 →
      ((IsOrbitE0 5 Xg e ∨ IsOrbitE0 5 Xg (-e)) ↔
        ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε)))) :
    Nat.card Xg = 103680 := by
  have hstab := card_stab_evenAll0 hS
  have hnegmat : (-1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ evenAll0 5 := by
    refine ⟨1, fun _ => -1, fun _ => Or.inr rfl, ⟨rfl, ?_⟩, ?_⟩
    · decide
    · ext i j
      by_cases h : i = j
      · subst h
        simp [spMat_apply]
      · simp [spMat_apply, h]
  have hneg : (-1 : GL (Fin 6) (ZMod 3)) ∈ Xg := by
    obtain ⟨A, hA, hAe⟩ := hS.sub _ hnegmat
    have hA' : A = (-1 : GL (Fin 6) (ZMod 3)) := Units.ext hAe
    rwa [hA'] at hA
  have hnegiff : ∀ e : Fin 6 → ZMod 3, IsOrbitE0 5 Xg (-e) ↔ IsOrbitE0 5 Xg e := by
    intro e
    constructor
    · rintro ⟨A, hA, hAe⟩
      refine ⟨(-1 : GL (Fin 6) (ZMod 3)) * A, Xg.mul_mem hneg hA, ?_⟩
      rw [gl_mul_mulVec, hAe,
        show ((-1 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = -1 by
          rw [Units.val_neg, Units.val_one]]
      rw [Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    · rintro ⟨A, hA, hAe⟩
      refine ⟨(-1 : GL (Fin 6) (ZMod 3)) * A, Xg.mul_mem hneg hA, ?_⟩
      rw [gl_mul_mulVec, hAe,
        show ((-1 : GL (Fin 6) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = -1 by
          rw [Units.val_neg, Units.val_one]]
      rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  have hshape : ∀ e : Fin 6 → ZMod 3, e ≠ 0 →
      (IsOrbitE0 5 Xg e ↔
        ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = ε))) := by
    intro e he
    have h := horb e he
    rw [hnegiff e, or_self] at h
    exact h
  have hzero : ¬ IsOrbitE0 5 Xg (0 : Fin 6 → ZMod 3) := by
    rintro ⟨A, -, hA⟩
    exact gl_mulVec_ne_zero A (pi_single_zero_ne_zero 5) hA
  have hset : {v : Fin 6 → ZMod 3 | IsOrbitE0 5 Xg v} =
      {v : Fin 6 → ZMod 3 | v ≠ 0 ∧
        ((wt v ≤ 2 ∧ v 0 ≠ 0) ∨ (wt v = 6 ∧ ∏ i, v i = ε))} := by
    ext v
    by_cases hv : v = 0
    · subst hv
      exact ⟨fun h => absurd h hzero, fun h => absurd rfl h.1⟩
    · exact ⟨fun h => ⟨hv, (hshape v hv).mp h⟩, fun h => (hshape v hv).mpr h.2⟩
  have horbitcard : {v : Fin 6 → ZMod 3 | IsOrbitE0 5 Xg v}.ncard = 54 := by
    rw [hset]
    exact card_orbit_shape6 ε hε
  have h1 := Subgroup.card_mul_index
    (MulAction.stabilizer ↥Xg (Pi.single 0 1 : Fin 6 → ZMod 3))
  rw [MulAction.index_stabilizer, hstab] at h1
  have h2 : MulAction.orbit ↥Xg (Pi.single 0 1 : Fin 6 → ZMod 3) =
      {v | IsOrbitE0 5 Xg v} := by
    ext v
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, IsOrbitE0, Subgroup.smul_def,
      Units.smul_def, Matrix.smul_eq_mulVec]
    constructor
    · rintro ⟨⟨A, hA⟩, rfl⟩
      exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨⟨A, hA⟩, rfl⟩
  rw [h2, horbitcard] at h1
  rw [← h1]

@[expose] def sgn5 : Fin 6 → ZMod 3 := fun i => if i = 5 then -1 else 1

theorem isSign_sgn5 : IsSign sgn5 := by
  unfold IsSign sgn5
  decide

private theorem shape_sgn5 (e : Fin 6 → ZMod 3) :
    ((wt (fun i => sgn5 i * e i) ≤ 2 ∧ (fun i => sgn5 i * e i) 0 ≠ 0) ∨
      (wt (fun i => sgn5 i * e i) = 6 ∧ ∏ i, sgn5 i * e i = -1)) ↔
    ((wt e ≤ 2 ∧ e 0 ≠ 0) ∨ (wt e = 6 ∧ ∏ i, e i = 1)) := by
  have h0 : sgn5 0 = 1 := by decide
  have hp : ∏ i, sgn5 i * e i = -∏ i, e i := by
    rw [Finset.prod_mul_distrib, show ∏ i, sgn5 i = -1 by decide, neg_one_mul]
  rw [wt_sign_mul isSign_sgn5, hp]
  simp only [h0, one_mul]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨h.1, ?_⟩
      have := congrArg Neg.neg h.2
      simpa using this
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h.1, by rw [h.2]⟩

theorem t5Main_of_mat (hM : T5MatMain) (hR : OE6RecOut) : T5Main := by
  intro G _ _ b₀ K E hstd B hB hII hfus hodd hN
  obtain ⟨hspan, hb0, hBK⟩ := hB
  subst hspan
  let Xg := (ggAutomizer ⊤ B.span).map B.glHom
  have hS : StabMatHyp 5 (evenAll0 5) Xg := B.stabMatHyp_xg hb0 hN hodd hfus
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcard_aut⟩ := hstd.2.1
  have hcardX : 2 ^ 6 * Nat.factorial 6 < Nat.card Xg := by
    show 2 ^ 6 * Nat.factorial 6 <
      Nat.card ((ggAutomizer ⊤ B.span).map B.glHom)
    rwa [Subgroup.card_map_of_injective B.glHom_injective]
  obtain ⟨ε, hε, hX⟩ := hM Xg hS hcardX
  obtain ⟨hrow, hquad, horb⟩ := hR ε hε
  rw [← hX] at hrow hquad horb
  have hcard_order : Nat.card ↥(ggAutomizer ⊤ B.span) = 103680 := by
    rw [← Subgroup.card_map_of_injective B.glHom_injective]
    exact card_of_stabMatHyp (Xg := Xg) hS hε horb
  rcases hε with hε1 | hεm
  · subst hε1
    refine ⟨B, ⟨rfl, hb0, hBK⟩, hcard_order, hN, ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, hxA⟩ := B.exists_xg_of_realized ⊤ hA
      exact ⟨fun j hj => by rw [← hxA]; exact hrow x hx j hj,
        fun v hv => by rw [← hxA]; exact hquad x hx v hv⟩
    · intro e he
      rw [B.isConjLine_iff_isConjLineIn hfus, ← hb0, ← B.vec_single 0,
        B.isConjLineIn_iff_exists_mulVec (Pi.single 0 1) he]
      simpa only [IsOrbitE0] using horb e he
  · subst hεm
    refine ⟨B.signed sgn5 isSign_sgn5,
      ⟨B.span_signed isSign_sgn5, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · show B.b 0 ^ (sgn5 0).val = b₀
      rw [show (sgn5 0).val = 1 by decide, pow_one, hb0]
    · intro i hi
      exact K.pow_mem (hBK i hi) _
    · rw [B.span_signed isSign_sgn5]
      exact hcard_order
    · rw [B.realized_signed isSign_sgn5, hN]
      ext A
      constructor
      · rintro ⟨M, hM, rfl⟩
        exact diagonal_conj_mem_evenAll0 isSign_sgn5 hM
      · intro hA
        exact ⟨Matrix.diagonal sgn5 * A * Matrix.diagonal sgn5,
          diagonal_conj_mem_evenAll0 isSign_sgn5 hA,
          (Basis3.diagonal_conj_conj isSign_sgn5 A).symm⟩
    · intro A hA
      rw [B.realized_signed isSign_sgn5 ⊤] at hA
      obtain ⟨M, hM, rfl⟩ := hA
      obtain ⟨x, hx, hxM⟩ := B.exists_xg_of_realized ⊤ hM
      refine row_quad_signed isSign_sgn5 (by decide) ?_ ?_
      · intro j hj
        rw [← hxM]
        exact hrow x hx j hj
      · intro v hv
        rw [← hxM]
        exact hquad x hx v hv
    · intro e he
      have hne : (fun i => sgn5 i * e i) ≠ 0 := sign_mul_ne_zero_vec isSign_sgn5 he
      rw [B.line_signed isSign_sgn5, B.isConjLine_iff_isConjLineIn hfus, ← hb0,
        ← B.vec_single 0, B.isConjLineIn_iff_exists_mulVec (Pi.single 0 1) hne]
      have h := horb (fun i => sgn5 i * e i) hne
      rw [shape_sgn5 e] at h
      simpa only [IsOrbitE0] using h

end CFSG.StandardType.FrameRoute.FS81

end

module

public import CFSG.Monster.Spin.Extraspecial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem eq_one_of_ne_zero' : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

theorem eq_of_add_eq_zero_C {a b : C} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [add_self_C', add_zero]
    _ = (a + b) + b := (add_assoc _ _ _).symm
    _ = b := by rw [h, zero_add]

theorem eq_of_add_eq_zero_cocode {δ ε : Cocode} (h : δ + ε = 0) : δ = ε := by
  calc δ = δ + (ε + ε) := by rw [add_self_cocode, add_zero]
    _ = (δ + ε) + ε := (add_assoc _ _ _).symm
    _ = ε := by rw [h, zero_add]

section Field

variable {k : Type*} [Field k]

theorem sum_sgnR_pair_eq_zero (h2 : (2 : k) ≠ 0) {δ : Cocode} {x₀ : C₀}
    (hx₀ : pair x₀ δ ≠ 0) : ∑ x : C₀, sgnR k (pair x δ) = 0 := by
  have h1 : pair x₀ δ = 1 := eq_one_of_ne_zero' _ hx₀
  have hS : ∑ x : C₀, sgnR k (pair x δ) = -∑ x : C₀, sgnR k (pair x δ) := by
    calc ∑ x : C₀, sgnR k (pair x δ)
        = ∑ x : C₀, sgnR k (pair ((x + x₀ : C₀) : C) δ) :=
          (Fintype.sum_equiv (Equiv.addRight x₀) _ (fun y : C₀ => sgnR k (pair y δ))
            (fun _ => rfl)).symm
      _ = ∑ x : C₀, -sgnR k (pair x δ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Submodule.coe_add, pair_add_left, h1, sgnR_add_one]
      _ = -∑ x : C₀, sgnR k (pair x δ) := Finset.sum_neg_distrib _
  have h2S : (2 : k) * ∑ x : C₀, sgnR k (pair x δ) = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    exact add_neg_cancel _
  exact (mul_eq_zero.1 h2S).resolve_left h2

theorem sum_sgnR_pair (h2 : (2 : k) ≠ 0) (δ : Cocode) :
    ∑ x : C₀, sgnR k (pair x δ) = if ∀ x : C₀, pair x δ = 0 then 2048 else 0 := by
  split_ifs with h
  · simp only [h, sgnR_zero, Finset.sum_const, Finset.card_univ, card_C₀, nsmul_eq_mul,
      mul_one]
    norm_num
  · obtain ⟨x₀, hx₀⟩ := not_forall.1 h
    exact sum_sgnR_pair_eq_zero h2 hx₀

theorem trace_qmatR (h2 : (2 : k) ≠ 0) (s : ZMod 2) (a : C) (δ : Cocode) :
    trace (qmatR k s a δ) = if a = 0 ∧ δ = 0 then sgnR k s * 4096 else 0 := by
  rw [qmatR, trace_spm]
  by_cases hfix : pair ΩC δ = 0 ∧ π₀ a = 0
  · obtain ⟨hΩ, hπ⟩ := hfix
    have hsh : ∀ x : C₀, shift a x = x := fun x => (shift_eq_self_iff a x).2 hπ
    have hperm : ∀ i, qPerm a δ i = i := fun i => by
      rw [qPerm, hΩ, add_zero, hsh]
    simp only [hperm, ite_true]
    rw [Fintype.sum_prod_type]
    simp only [qSign, hsh]
    rcases zmod2_cases (μ₀ a) with hμ | hμ
    · have ha : a = 0 := eq_of_π₀_μ₀ (by rw [hπ, map_zero]) (by rw [hμ, map_zero])
      simp only [hμ, mul_zero, add_zero, sgnR_add, ← Finset.mul_sum, sum_sgnR_pair h2,
        Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      by_cases hall : ∀ x : C₀, pair x δ = 0
      · have hδ : δ = 0 := eq_zero_of_forall_pair fun u => by
          rw [← π₀_add_μ₀ u, pair_add_left, pair_smul_left, hall, hΩ, mul_zero, add_zero]
        simp only [ite_true, ha, hδ, and_self]
        norm_num
      · have hδ : δ ≠ 0 := fun h => hall fun x => by rw [h, pair_zero_right]
        simp only [hall, ite_false, mul_zero, hδ, and_false]
    · have ha : a ≠ 0 := fun h => by
        rw [h, map_zero] at hμ
        exact zero_ne_one hμ
      rw [Finset.sum_comm]
      have hη : ∀ x : C₀, ∑ η : ZMod 2, sgnR k (s + η * μ₀ a + pair x δ) = 0 := fun x => by
        rw [← sum_sgnR_add (R := k) (s + pair x δ)]
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [hμ, mul_one]
        congr 1
        ring
      simp only [hη, Finset.sum_const_zero, ha, false_and, ite_false]
  · have hperm : ∀ i, ¬qPerm a δ i = i := by
      intro i h
      apply hfix
      have h1 := congrArg Prod.fst h
      have h2' := congrArg Prod.snd h
      simp only [qPerm, add_eq_left] at h1 h2'
      exact ⟨h1, (shift_eq_self_iff a i.2).1 h2'⟩
    have hne : ¬(a = 0 ∧ δ = 0) := fun ⟨ha, hδ⟩ =>
      hfix ⟨by rw [hδ, pair_zero_right], by rw [ha, map_zero]⟩
    simp only [hperm, ite_false, Finset.sum_const_zero, hne]

end Field

@[expose] def TDR (R : Type*) [CommRing R] (p : C × Cocode) : Matrix SpinIdx SpinIdx R :=
  TmatR R p.1 * DmatR R p.2

theorem TDR_eq_qmatR {R : Type*} [CommRing R] (p : C × Cocode) : TDR R p = qmatR R 0 p.1 p.2 := by
  rw [TDR, TmatR_eq_qmatR, DmatR_eq_qmatR, qmatR_mul, pair_zero_right]
  simp only [add_zero, zero_add]

theorem TDR_eq_map {R : Type*} [CommRing R] (p : C × Cocode) :
    TDR R p = (TDR ℤ p).map (Int.cast : ℤ → R) := by
  rw [TDR_eq_qmatR, TDR_eq_qmatR, ← map_qmatR (Int.castRingHom R)]
  rfl

section Field

variable {k : Type*} [Field k]

theorem trace_transpose_TDR_mul (h2 : (2 : k) ≠ 0) (p q : C × Cocode) :
    trace ((TDR k p)ᵀ * TDR k q) = if p = q then 4096 else 0 := by
  rw [TDR_eq_qmatR, TDR_eq_qmatR, qmatR_transpose, qmatR_mul, trace_qmatR h2]
  by_cases hpq : p = q
  · subst hpq
    rw [add_self_C', add_self_cocode, ite_eq_left ⟨rfl, rfl⟩, ite_eq_left rfl, zero_add,
      add_zero, zmod2_add_self, sgnR_zero, one_mul]
  · have h : ¬(p.1 + q.1 = 0 ∧ p.2 + q.2 = 0) := fun h =>
      hpq (Prod.ext (eq_of_add_eq_zero_C h.1) (eq_of_add_eq_zero_cocode h.2))
    rw [ite_eq_right h, ite_eq_right hpq]

theorem four_thousand_ninety_six_ne_zero (h2 : (2 : k) ≠ 0) : (4096 : k) ≠ 0 := by
  have := pow_ne_zero 12 h2
  norm_num at this
  exact this

theorem linearIndependent_TDR (h2 : (2 : k) ≠ 0) : LinearIndependent k (TDR k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun M => trace ((TDR k q)ᵀ * M)) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul,
    trace_transpose_TDR_mul h2, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, trace_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (four_thousand_ninety_six_ne_zero h2)

theorem card_eq_finrank_matrix :
    Fintype.card (C × Cocode) = Module.finrank k (Matrix SpinIdx SpinIdx k) := by
  rw [Fintype.card_prod, card_C, card_cocode, Module.finrank_matrix, Module.finrank_self,
    card_spinIdx]

@[expose] def TDbasis (h2 : (2 : k) ≠ 0) : Module.Basis (C × Cocode) k (Matrix SpinIdx SpinIdx k) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_TDR h2) card_eq_finrank_matrix

@[simp] theorem coe_TDbasis (h2 : (2 : k) ≠ 0) : ⇑(TDbasis h2) = TDR k :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem span_TDR (h2 : (2 : k) ≠ 0) : Submodule.span k (Set.range (TDR k)) = ⊤ := by
  rw [← coe_TDbasis h2]
  exact (TDbasis h2).span_eq

theorem commute_of_forall_commute_TDR (h2 : (2 : k) ≠ 0) {M : Matrix SpinIdx SpinIdx k}
    (hM : ∀ p, TDR k p * M = M * TDR k p) (N : Matrix SpinIdx SpinIdx k) : N * M = M * N := by
  have hN : N ∈ Submodule.span k (Set.range (TDR k)) := by
    rw [span_TDR h2]
    exact Submodule.mem_top
  induction hN using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact hM p
  | zero => rw [Matrix.zero_mul, Matrix.mul_zero]
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]

theorem mem_range_scalar_of_forall_commute_TDR (h2 : (2 : k) ≠ 0) {M : Matrix SpinIdx SpinIdx k}
    (hM : ∀ p, TDR k p * M = M * TDR k p) : M ∈ Set.range (Matrix.scalar SpinIdx) :=
  mem_range_scalar_of_commute_single fun i j _ =>
    commute_of_forall_commute_TDR h2 hM (single i j 1)

theorem eq_bot_or_eq_top_of_invariant (h2 : (2 : k) ≠ 0) (W : Submodule k (SpinIdx → k))
    (hX : ∀ e : Parker, ∀ v ∈ W, v ᵥ* XmatR k e ∈ W)
    (hD : ∀ δ : Cocode, ∀ v ∈ W, v ᵥ* DmatR k δ ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let A : Submodule k (Matrix SpinIdx SpinIdx k) :=
    { carrier := {N | ∀ v ∈ W, v ᵥ* N ∈ W}
      add_mem' := fun {N N'} hN hN' v hv => by
        rw [vecMul_add]
        exact W.add_mem (hN v hv) (hN' v hv)
      zero_mem' := fun v _ => by
        rw [vecMul_zero]
        exact W.zero_mem
      smul_mem' := fun c N hN v hv => by
        rw [vecMul_smul]
        exact W.smul_mem c (hN v hv) }
  have hmul : ∀ N N', N ∈ A → N' ∈ A → N * N' ∈ A := fun N N' hN hN' v hv => by
    rw [← vecMul_vecMul]
    exact hN' _ (hN v hv)
  have hTD : ∀ p, TDR k p ∈ A := fun p =>
    hmul _ _ (hmul _ _ (hX _) (hD _)) (hD _)
  have htop : A = ⊤ := by
    rw [eq_top_iff, ← span_TDR h2, Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact hTD p
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      exact hv0 (funext fun i => by
        by_contra hvi
        exact h ⟨i, hvi⟩)
    rw [eq_top_iff]
    intro w _
    have hN : (v i)⁻¹ • vecMulVec (Pi.single i 1) w ∈ A := by
      rw [htop]
      exact Submodule.mem_top
    have := hN v hv
    rwa [vecMul_smul, vecMul_vecMulVec, dotProduct_single, mul_one, smul_smul,
      inv_mul_cancel₀ hi, one_smul] at this

end Field

@[expose] def toGLR (R : Type*) [CommRing R] : SpinCoord →* GL SpinIdx R where
  toFun x := ⟨qmatR R x.s x.a x.δ, (qmatR R x.s x.a x.δ)ᵀ, qmatR_mul_transpose_self _ _ _,
    qmatR_transpose_mul_self _ _ _⟩
  map_one' := Units.ext qmatR_zero
  map_mul' _ _ := Units.ext (qmatR_mul _ _ _ _ _ _).symm

@[expose] def reduceQ (R : Type*) [CommRing R] : Q →* GL SpinIdx R :=
  (toGLR R).comp spinEquiv.symm.toMonoidHom

theorem coe_reduceQ_spinEquiv (R : Type*) [CommRing R] (x : SpinCoord) :
    ((reduceQ R (spinEquiv x) : GL SpinIdx R) : Matrix SpinIdx SpinIdx R) = qmatR R x.s x.a x.δ := by
  simp only [reduceQ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem reduceQ_eq_map (R : Type*) [CommRing R] (g : Q) :
    ∃ M : Matrix SpinIdx SpinIdx ℤ, ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      M.map (Int.cast : ℤ → ℚ) ∧
      ((reduceQ R g : GL SpinIdx R) : Matrix SpinIdx SpinIdx R) = M.map (Int.cast : ℤ → R) := by
  obtain ⟨x, rfl⟩ := spinEquiv.surjective g
  refine ⟨qmatR ℤ x.s x.a x.δ, ?_, ?_⟩
  · rw [coe_spinEquiv, coe_toGL, ← map_qmatR (Int.castRingHom ℚ)]
    rfl
  · rw [coe_reduceQ_spinEquiv, ← map_qmatR (Int.castRingHom R)]
    rfl

theorem XU_eq_spinEquiv (e : Parker) :
    (⟨XU e, XU_mem_Q e⟩ : Q) = spinEquiv ⟨e.sign, e.code, thetaD e.code⟩ :=
  Subtype.ext (XU_eq_toGL e)

theorem DU_eq_spinEquiv (δ : Cocode) : (⟨DU δ, DU_mem_Q δ⟩ : Q) = spinEquiv ⟨0, 0, δ⟩ :=
  Subtype.ext (DU_eq_toGL δ)

theorem coe_reduceQ_XU (R : Type*) [CommRing R] (e : Parker) :
    ((reduceQ R ⟨XU e, XU_mem_Q e⟩ : GL SpinIdx R) : Matrix SpinIdx SpinIdx R) = XmatR R e := by
  rw [XU_eq_spinEquiv, coe_reduceQ_spinEquiv, XmatR_eq_qmatR]

theorem coe_reduceQ_DU (R : Type*) [CommRing R] (δ : Cocode) :
    ((reduceQ R ⟨DU δ, DU_mem_Q δ⟩ : GL SpinIdx R) : Matrix SpinIdx SpinIdx R) = DmatR R δ := by
  rw [DU_eq_spinEquiv, coe_reduceQ_spinEquiv, DmatR_eq_qmatR]

theorem reduceQ_irreducible {k : Type*} [Field k] (hk : ringChar k ≠ 2)
    (W : Submodule k (SpinIdx → k))
    (hW : ∀ g : Q, ∀ v ∈ W, v ᵥ* ((reduceQ k g : GL SpinIdx k) : Matrix SpinIdx SpinIdx k) ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_invariant (Ring.two_ne_zero hk) W
    (fun e v hv => coe_reduceQ_XU k e ▸ hW _ v hv)
    (fun δ v hv => coe_reduceQ_DU k δ ▸ hW _ v hv)

theorem TDR_rat (p : C × Cocode) : TDR ℚ p = Tmat p.1 * Dmat p.2 := rfl

private theorem two_ne_zero_rat : (2 : ℚ) ≠ 0 := two_ne_zero

theorem exists_scalar_of_commute_Q {M : Matrix SpinIdx SpinIdx ℚ}
    (hM : ∀ g ∈ Q, (g : Matrix SpinIdx SpinIdx ℚ) * M = M * g) :
    ∃ c : ℚ, M = Matrix.scalar SpinIdx c := by
  obtain ⟨c, hc⟩ := mem_range_scalar_of_forall_commute_TDR two_ne_zero_rat (M := M) fun p => by
    have := hM (TU p.1 * DU p.2) (Q.mul_mem (TU_mem_Q _) (DU_mem_Q _))
    rwa [Units.val_mul, coe_TU, coe_DU] at this
  exact ⟨c, hc.symm⟩

theorem Q_irreducible (W : Submodule ℚ (SpinIdx → ℚ))
    (hW : ∀ g ∈ Q, ∀ v ∈ W, v ᵥ* (g : Matrix SpinIdx SpinIdx ℚ) ∈ W) : W = ⊥ ∨ W = ⊤ :=
  eq_bot_or_eq_top_of_invariant two_ne_zero_rat W (fun e v hv => hW _ (XU_mem_Q e) v hv)
    (fun δ v hv => hW _ (DU_mem_Q δ) v hv)

theorem spin_full_operator_basis :
    Fintype.card (C × Cocode) = 2 ^ 24 ∧
    LinearIndependent ℚ (fun p : C × Cocode => Tmat p.1 * Dmat p.2) ∧
    Submodule.span ℚ (Set.range fun p : C × Cocode => Tmat p.1 * Dmat p.2) = ⊤ ∧
    (∀ p q : C × Cocode, trace ((Tmat p.1 * Dmat p.2)ᵀ * (Tmat q.1 * Dmat q.2)) =
      if p = q then 4096 else 0) ∧
    (∀ M : Matrix SpinIdx SpinIdx ℚ, (∀ g ∈ Q, (g : Matrix SpinIdx SpinIdx ℚ) * M = M * g) →
      ∃ c : ℚ, M = Matrix.scalar SpinIdx c) ∧
    (∀ W : Submodule ℚ (SpinIdx → ℚ), (∀ g ∈ Q, ∀ v ∈ W, v ᵥ* (g : Matrix SpinIdx SpinIdx ℚ) ∈ W) →
      W = ⊥ ∨ W = ⊤) ∧
    ∀ (k : Type*) [Field k], ringChar k ≠ 2 →
      (∀ p : C × Cocode, TmatR k p.1 * DmatR k p.2 =
        (TmatR ℤ p.1 * DmatR ℤ p.2).map (Int.cast : ℤ → k)) ∧
      LinearIndependent k (fun p : C × Cocode => TmatR k p.1 * DmatR k p.2) ∧
      Submodule.span k (Set.range fun p : C × Cocode => TmatR k p.1 * DmatR k p.2) = ⊤ ∧
      (∀ p q : C × Cocode, trace ((TmatR k p.1 * DmatR k p.2)ᵀ * (TmatR k q.1 * DmatR k q.2)) =
        if p = q then 4096 else 0) ∧
      (∀ g : Q, ∃ M : Matrix SpinIdx SpinIdx ℤ,
        ((g : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = M.map (Int.cast : ℤ → ℚ) ∧
        ((reduceQ k g : GL SpinIdx k) : Matrix SpinIdx SpinIdx k) = M.map (Int.cast : ℤ → k)) ∧
      (∀ W : Submodule k (SpinIdx → k),
        (∀ g : Q, ∀ v ∈ W, v ᵥ* ((reduceQ k g : GL SpinIdx k) : Matrix SpinIdx SpinIdx k) ∈ W) →
        W = ⊥ ∨ W = ⊤) := by
  refine ⟨by rw [Fintype.card_prod, card_C, card_cocode]; norm_num,
    linearIndependent_TDR two_ne_zero_rat,
    span_TDR two_ne_zero_rat, trace_transpose_TDR_mul two_ne_zero_rat,
    fun M hM => exists_scalar_of_commute_Q hM, Q_irreducible, fun k _ hk => ?_⟩
  have h2 := Ring.two_ne_zero hk
  exact ⟨TDR_eq_map, linearIndependent_TDR h2, span_TDR h2, trace_transpose_TDR_mul h2,
    reduceQ_eq_map k, reduceQ_irreducible hk⟩

end CFSG.Monster.Spin

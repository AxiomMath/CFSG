module

public import CFSG.Quasithin.Background.SimsF5Ai
public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Background.SimsF5Main

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix CFSG.Open CFSG.Quasithin.SimsF5Lat
open scoped Pointwise

local notation:max "mat(" g ")" => ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))

theorem m7_smul_spn (g : GL6) (v : V6) : g • spn {v} = spn {mat(g) *ᵥ v} := by
  change (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) • Submodule.span (ZMod 3) {v} =
    Submodule.span (ZMod 3) {mat(g) *ᵥ v}
  rw [Submodule.smul_span, Set.smul_set_singleton]
  rfl

theorem m7_smul_eq {g : ↥MDot} {P Q : PtX} {v w : V6} (hP : (P : Sub6) = spn {v})
    (hQ : (Q : Sub6) = spn {w}) (h : mat(g) *ᵥ v = w ∨ mat(g) *ᵥ v = -w) : g • P = Q := by
  refine Subtype.ext ?_
  change (g : GL6) • (P : Sub6) = (Q : Sub6)
  rw [hP, hQ, m7_smul_spn]
  rcases h with h | h
  · rw [h]
  · rw [h, ai_spn_neg]

theorem m7_qV_x1_add_x2 : qV (x1 + x2) = -1 := by decide

theorem m7_qV_x3_sub_x4 : qV (x3 - x4) = -1 := by decide

@[expose] def m7zPt : PtX := ⟨spn {x1 + x2}, x1 + x2, m7_qV_x1_add_x2, rfl⟩

@[expose] def m7wPt : PtX := ⟨spn {x3 - x4}, x3 - x4, m7_qV_x3_sub_x4, rfl⟩

theorem m7_xDot_ne_yDot : xDot ≠ yDot := by
  intro h
  have h1 : x1 - x2 ∈ spn {x6} := by
    have := congrArg Subtype.val h
    change spn {x6} = spn {x1 - x2} at this
    rw [this]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  exact (by decide : ∀ a : ZMod 3, a • x6 ≠ x1 - x2) a ha

theorem stabilizer_xDot : MulAction.stabilizer ↥MDot xDot = M0Dot.subgroupOf MDot := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, M0Dot, Subgroup.mem_inf,
    MulAction.mem_stabilizer_iff]
  exact ⟨fun h => ⟨g.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩

theorem m7_mem_Sx {g : GL6} (hM : g ∈ MDot) :
    (⟨g, hM⟩ : ↥MDot) ∈ MulAction.stabilizer ↥MDot xDot ↔ g ∈ M0Dot := by
  rw [stabilizer_xDot]
  exact Iff.rfl

theorem m7_eigen_of_fix {g : ↥MDot} (hg : ∀ P : PtX, g • P = P) {v : V6} (hv : qV v = -1) :
    ∃ c : ZMod 3, mat(g) *ᵥ v = c • v := by
  have h := congrArg Subtype.val (hg ⟨spn {v}, v, hv, rfl⟩)
  change (g : GL6) • spn {v} = spn {v} at h
  rw [m7_smul_spn] at h
  have : mat(g) *ᵥ v ∈ spn {v} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  exact ⟨c, hc.symm⟩

theorem m7_q_add : ∀ j k : Fin 6, j.val < 5 → k.val < 5 → j ≠ k →
    qV (xvec j + xvec k) = -1 := by decide

theorem m7_q_sub : ∀ j k : Fin 6, j.val < 5 → k.val < 5 → j ≠ k →
    qV (xvec j - xvec k) = -1 := by decide

theorem m7_exists_k : ∀ i j : Fin 6, i ≠ j → j.val < 5 →
    ∃ k : Fin 6, k.val < 5 ∧ k ≠ i ∧ k ≠ j := by decide

theorem m7_offdiag {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ v : V6, qV v = -1 → ∃ c : ZMod 3, M *ᵥ v = c • v)
    {i j k : Fin 6} (hj : j.val < 5) (hk : k.val < 5) (hjk : j ≠ k) (hij : i ≠ j) (hik : i ≠ k) :
    M i j = 0 := by
  obtain ⟨c₁, h₁⟩ := h _ (m7_q_add j k hj hk hjk)
  obtain ⟨c₂, h₂⟩ := h _ (m7_q_sub j k hj hk hjk)
  have e₁ := congrFun h₁ i
  have e₂ := congrFun h₂ i
  rw [Matrix.mulVec_add, Pi.add_apply, mulVec_xvec, mulVec_xvec, Pi.smul_apply, Pi.add_apply,
    mono_xvec_apply, mono_xvec_apply, if_neg hij, if_neg hik] at e₁
  rw [Matrix.mulVec_sub, Pi.sub_apply, mulVec_xvec, mulVec_xvec, Pi.smul_apply, Pi.sub_apply,
    mono_xvec_apply, mono_xvec_apply, if_neg hij, if_neg hik] at e₂
  have key : ∀ a b c d : ZMod 3, a + b = c • (0 + 0) → a - b = d • (0 - 0) → a = 0 := by decide
  exact key _ _ c₁ c₂ e₁ e₂

theorem m7_diag_eq {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ v : V6, qV v = -1 → ∃ c : ZMod 3, M *ᵥ v = c • v)
    (off : ∀ i j : Fin 6, i ≠ j → M i j = 0) {j k : Fin 6} (hj : j.val < 5) (hk : k.val < 5)
    (hjk : j ≠ k) : M j j = M k k := by
  obtain ⟨c, hc⟩ := h _ (m7_q_add j k hj hk hjk)
  have e₁ := congrFun hc j
  have e₂ := congrFun hc k
  rw [Matrix.mulVec_add, Pi.add_apply, mulVec_xvec, mulVec_xvec, Pi.smul_apply, Pi.add_apply,
    mono_xvec_apply, mono_xvec_apply, if_pos rfl, if_neg hjk, off j k hjk] at e₁
  rw [Matrix.mulVec_add, Pi.add_apply, mulVec_xvec, mulVec_xvec, Pi.smul_apply, Pi.add_apply,
    mono_xvec_apply, mono_xvec_apply, if_pos rfl, if_neg hjk.symm, off k j hjk.symm] at e₂
  have key : ∀ a b c : ZMod 3, a + 0 = c • (1 + 0) → 0 + b = c • (0 + 1) → a = b := by decide
  exact key _ _ c e₁ e₂

theorem m7_diag_eq_x6 {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ v : V6, qV v = -1 → ∃ c : ZMod 3, M *ᵥ v = c • v)
    (off : ∀ i j : Fin 6, i ≠ j → M i j = 0) : M 5 5 = M 0 0 := by
  have hq : qV (x1 + x2 + x3 + x6) = -1 := by decide
  obtain ⟨c, hc⟩ := h _ hq
  have e₁ := congrFun hc 0
  have e₂ := congrFun hc 5
  clear hc hq h
  simp only [x1, x2, x3, x6, Matrix.mulVec_add, Pi.add_apply, mulVec_xvec, Pi.smul_apply,
    mono_xvec_apply, off 0 1 (by decide), off 0 2 (by decide), off 0 5 (by decide),
    off 5 0 (by decide), off 5 1 (by decide), off 5 2 (by decide)] at e₁ e₂
  revert e₁ e₂
  generalize M 0 0 = a
  generalize M 5 5 = b
  revert a b c
  decide

theorem m7_scalar {M : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ v : V6, qV v = -1 → ∃ c : ZMod 3, M *ᵥ v = c • v) :
    ∃ c : ZMod 3, ∀ j : Fin 6, M *ᵥ xvec j = c • xvec j := by
  have off : ∀ i j : Fin 6, i ≠ j → M i j = 0 := by
    intro i j hij
    by_cases hj5 : j = 5
    · subst hj5
      obtain ⟨c, hc⟩ := h x6 qV_x6
      have := congrFun hc i
      have h5 : x6 = xvec 5 := rfl
      rw [h5, mulVec_xvec, Pi.smul_apply, mono_xvec_apply, if_neg hij] at this
      simpa using this
    · have hjv : j.val < 5 := by
        have : j.val ≠ 5 := fun h => hj5 (Fin.ext h)
        omega
      obtain ⟨k, hk, hki, hkj⟩ := m7_exists_k i j hij hjv
      exact m7_offdiag h hjv hk hkj.symm hij hki.symm
  have hdiag : ∀ j : Fin 6, M j j = M 0 0 := by
    intro j
    by_cases hj0 : j = 0
    · rw [hj0]
    by_cases hj5 : j = 5
    · rw [hj5]
      exact m7_diag_eq_x6 h off
    · have hjv : j.val < 5 := by
        have : j.val ≠ 5 := fun h => hj5 (Fin.ext h)
        omega
      exact m7_diag_eq h off hjv (by decide) hj0
  refine ⟨M 0 0, fun j => ?_⟩
  funext i
  rw [mulVec_xvec, Pi.smul_apply, mono_xvec_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, hdiag i, smul_eq_mul, mul_one]
  · rw [if_neg hij, off i j hij, smul_zero]

theorem m7_eq_one_of_fix {g : ↥MDot} (hg : ∀ P : PtX, g • P = P) : g = 1 := by
  obtain ⟨c, hc⟩ := m7_scalar (fun v hv => m7_eigen_of_fix hg hv)
  have hc0 : c ≠ 0 :=
    ai_scalar_ne_zero (h := (g : GL6)) (v := xvec 5) (hc 5) (mono_xvec_ne_zero 5)
  rcases (by decide : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1) c hc0 with rfl | rfl
  · refine Subtype.ext (mono_gl_ext fun i => ?_)
    rw [hc i, one_smul]
    simp
  · exfalso
    apply neg_one_not_mem_MDot
    have : (g : GL6) = -1 := by
      refine mono_gl_ext fun i => ?_
      rw [hc i, neg_one_smul, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [← this]
    exact g.2

theorem faithfulSMul_PtX : FaithfulSMul ↥MDot PtX where
  eq_of_smul_eq_smul {g h} H := by
    have : g⁻¹ * h = 1 := m7_eq_one_of_fix fun P => by rw [mul_smul, ← H P, inv_smul_smul]
    exact inv_mul_eq_one.1 this

theorem m7_f_eigen : ∀ v : V6, qV v = -1 → fMat *ᵥ v = -v →
    v = x6 ∨ v = -x6 ∨ v = x1 - x2 ∨ v = -(x1 - x2) := by decide +kernel

theorem m7_fMat_x6 : fMat *ᵥ x6 = -x6 := by
  rw [fMat_mulVec_x6, neg_one_smul]

theorem m7_fMat_u : fMat *ᵥ (x1 - x2) = -(x1 - x2) := by decide

theorem m7_cen_vec {g : ↥MDot} (hg : (g : GL6) * fDot = fDot * (g : GL6)) {w : V6}
    (hw : fMat *ᵥ w = -w) (hq : qV w = -1) :
    mat(g) *ᵥ w = x6 ∨ mat(g) *ᵥ w = -x6 ∨ mat(g) *ᵥ w = x1 - x2 ∨
      mat(g) *ᵥ w = -(x1 - x2) := by
  apply m7_f_eigen
  · rw [qV_mulVec_of_mem_OVq (MDot_le_OVq g.2), hq]
  · have h1 : fMat * mat(g) = mat(g) * fMat := by
      have := congrArg Units.val hg.symm
      rw [Units.val_mul, Units.val_mul] at this
      exact this
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_neg]

theorem m7_cen_pt {g : ↥MDot} (hg : (g : GL6) * fDot = fDot * (g : GL6)) {P : PtX} {w : V6}
    (hP : (P : Sub6) = spn {w}) (hw : fMat *ᵥ w = -w) (hq : qV w = -1) :
    g • P = xDot ∨ g • P = yDot := by
  rcases m7_cen_vec hg hw hq with h | h | h | h
  · exact Or.inl (m7_smul_eq (v := w) hP rfl (Or.inl h))
  · exact Or.inl (m7_smul_eq (v := w) hP rfl (Or.inr h))
  · exact Or.inr (m7_smul_eq (v := w) hP rfl (Or.inl h))
  · exact Or.inr (m7_smul_eq (v := w) hP rfl (Or.inr h))

theorem smul_xDot_of_cen {g : ↥MDot} (hg : (g : GL6) * fDot = fDot * (g : GL6))
    (hg0 : (g : GL6) ∉ M0Dot) : g • xDot = yDot := by
  rcases m7_cen_pt hg (P := xDot) (w := x6) rfl m7_fMat_x6 qV_x6 with h | h
  · exfalso
    apply hg0
    have h' : g ∈ MulAction.stabilizer ↥MDot xDot := h
    rw [stabilizer_xDot] at h'
    exact h'
  · exact h

theorem m7_cen_fix_yDot {g : ↥MDot} (hg : (g : GL6) * fDot = fDot * (g : GL6))
    (hx : g • xDot = xDot) : g • yDot = yDot := by
  rcases m7_cen_pt hg (P := yDot) (w := x1 - x2) rfl m7_fMat_u qV_x1_sub_x2 with h | h
  · exfalso
    apply m7_xDot_ne_yDot
    apply smul_left_cancel g
    rw [hx]
    exact h.symm
  · exact h

@[expose] def m7R (c x : V6) : V6 := x - (qV c * bil x c) • c

theorem m7_inv_self : ∀ c : ZMod 3, c ≠ 0 → c⁻¹ = c := fun c hc =>
  inv_eq_of_mul_eq_one_right (by revert c; decide)

theorem m7_refl_apply (c x : V6) (hc : qV c ≠ 0) : mat(refl6 c hc) *ᵥ x = m7R c x := by
  rw [refl6_mulVec, m7_inv_self _ hc]
  rfl

theorem m7_refl_prod_apply (c d x : V6) (hc : qV c ≠ 0) (hd : qV d ≠ 0) :
    mat(refl6 c hc * refl6 d hd) *ᵥ x = m7R c (m7R d x) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, m7_refl_apply _ _ hd, m7_refl_apply _ _ hc]

theorem m7_pair {c d w : V6} {P : PtX} (hP : (P : Sub6) = spn {w}) (hc : qV c ≠ 0)
    (hd : qV d ≠ 0) (hcd : qV c = qV d) (h6 : m7R c (m7R d x6) = x6 ∨ m7R c (m7R d x6) = -x6)
    (hu : m7R c (m7R d (x1 - x2)) = w ∨ m7R c (m7R d (x1 - x2)) = -w) :
    ∃ g : ↥MDot, (g : GL6) ∈ M0Dot ∧ g • yDot = P := by
  obtain ⟨ε, hε, h6'⟩ : ∃ ε : ZMod 3, ε ≠ 0 ∧ m7R c (m7R d x6) = ε • x6 := by
    rcases h6 with h | h
    · exact ⟨1, one_ne_zero, by rw [h, one_smul]⟩
    · exact ⟨-1, by decide, by rw [h, neg_one_smul]⟩
  have hM := refl6_mul_refl6_mem_MDot c d hc hd hcd
  refine ⟨⟨refl6 c hc * refl6 d hd, hM⟩, ⟨hM, mem_stabilizer_spn_x6_iff.2 ⟨ε, hε, ?_⟩⟩,
    m7_smul_eq (v := x1 - x2) rfl hP ?_⟩
  · change mat(refl6 c hc * refl6 d hd) *ᵥ x6 = ε • x6
    rw [m7_refl_prod_apply, h6']
  · change mat(refl6 c hc * refl6 d hd) *ᵥ (x1 - x2) = w ∨ _ = -w
    rwa [m7_refl_prod_apply]

theorem m7_orth_cases : ∀ w : V6, w 5 = 0 → qV w = -1 →
    (qV (x1 - x2 - w) = qV x6 ∧ qV (x1 - x2 - w) ≠ 0 ∧ m7R (x1 - x2 - w) (m7R x6 x6) = -x6 ∧
      m7R (x1 - x2 - w) (m7R x6 (x1 - x2)) = w) ∨
    (qV (x1 - x2 + w) = qV x6 ∧ qV (x1 - x2 + w) ≠ 0 ∧ m7R (x1 - x2 + w) (m7R x6 x6) = -x6 ∧
      m7R (x1 - x2 + w) (m7R x6 (x1 - x2)) = -w) ∨
    (qV (x1 - x2 - w) = qV x3 ∧ qV (x1 - x2 - w) ≠ 0 ∧ m7R (x1 - x2 - w) (m7R x3 x6) = x6 ∧
      m7R (x1 - x2 - w) (m7R x3 (x1 - x2)) = w) := by
  decide +kernel

theorem exists_M0Dot_smul_yDot {P : PtX} (hP : DeltaDot.Adj xDot P) :
    ∃ g : ↥MDot, (g : GL6) ∈ M0Dot ∧ g • yDot = P := by
  obtain ⟨S, w, hw, rfl⟩ := P
  have h5 : w 5 = 0 := by
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hP
    · have := h x6 (Submodule.mem_span_singleton_self _) w (Submodule.mem_span_singleton_self _)
      rwa [bil_comm, bil_x6] at this
    · have := h w (Submodule.mem_span_singleton_self _) x6 (Submodule.mem_span_singleton_self _)
      rwa [bil_x6] at this
  rcases m7_orth_cases w h5 hw with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact m7_pair rfl h2 qV_x6_ne_zero h1 (Or.inr h3) (Or.inl h4)
  · exact m7_pair rfl h2 qV_x6_ne_zero h1 (Or.inr h3) (Or.inr h4)
  · exact m7_pair rfl h2 (qV_xvec_ne_zero 2) h1 (Or.inl h3) (Or.inl h4)

theorem m7_adj_iff {S S' : PtX} :
    DeltaDot.Adj S S' ↔ S ≠ S' ∧ ∀ v ∈ (S : Sub6), ∀ w ∈ (S' : Sub6), bil v w = 0 := by
  rw [DeltaDot, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | h)
  · exact h
  · intro v hv w hw
    rw [bil_comm]
    exact h w hw v hv

theorem m7_orth_smul (g : ↥MDot) (S S' : PtX) :
    (∀ v ∈ ((g • S : PtX) : Sub6), ∀ w ∈ ((g • S' : PtX) : Sub6), bil v w = 0) ↔
      ∀ v ∈ (S : Sub6), ∀ w ∈ (S' : Sub6), bil v w = 0 := by
  have hO : (g : GL6) ∈ OVq := MDot_le_OVq g.2
  constructor
  · intro h v hv w hw
    have := h ((g : GL6) • v) ((quat_mem_smul_iff _ _ _).2 ⟨v, hv, rfl⟩) ((g : GL6) • w)
      ((quat_mem_smul_iff _ _ _).2 ⟨w, hw, rfl⟩)
    rwa [quat_smul_def, quat_smul_def, bil_mulVec_of_mem_OVq hO] at this
  · intro h v hv w hw
    obtain ⟨v', hv', rfl⟩ := (quat_mem_smul_iff _ _ _).1 hv
    obtain ⟨w', hw', rfl⟩ := (quat_mem_smul_iff _ _ _).1 hw
    rw [quat_smul_def, quat_smul_def, bil_mulVec_of_mem_OVq hO]
    exact h v' hv' w' hw'

theorem m7_graphAction : CFSG.Quasithin.GraphAction ↥MDot DeltaDot where
  adj_smul g a b := by
    rw [m7_adj_iff, m7_adj_iff, m7_orth_smul, (MulAction.injective g).ne_iff]

theorem m7_trans (P : PtX) : ∃ g : ↥MDot, g • xDot = P := by
  obtain ⟨S, w, hw, rfl⟩ := P
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [qV_zero] at hw
    exact absurd hw (by decide)
  obtain ⟨g, hg, hgx⟩ := exists_mem_MDot_mulVec_eq x6_ne_zero hw0 (qV_x6.trans hw.symm)
  exact ⟨⟨g, hg⟩, m7_smul_eq (v := x6) rfl rfl (Or.inl hgx)⟩

theorem m7_adj_xy : DeltaDot.Adj xDot yDot := by
  rw [m7_adj_iff]
  refine ⟨m7_xDot_ne_yDot, ?_⟩
  intro v hv w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [bil_smul_left, bil_smul_right]
  have : bil x6 (x1 - x2) = 0 := by decide
  rw [this, mul_zero, mul_zero]

theorem m7_edgeSet_eq :
    DeltaDot.edgeSet = Set.range fun g : ↥MDot => s(g • xDot, g • yDot) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hab
      obtain ⟨g, rfl⟩ := m7_trans a
      have h1 : DeltaDot.Adj xDot (g⁻¹ • b) := by
        have := (m7_graphAction.adj_smul g⁻¹ (g • xDot) b).2 hab
        rwa [inv_smul_smul] at this
      obtain ⟨h, hh0, hh⟩ := exists_M0Dot_smul_yDot h1
      have hx : h • xDot = xDot := by
        have : h ∈ MulAction.stabilizer ↥MDot xDot := by rw [stabilizer_xDot]; exact hh0
        exact this
      refine ⟨g * h, ?_⟩
      show s((g * h) • xDot, (g * h) • yDot) = s(g • xDot, b)
      rw [mul_smul, mul_smul, hx, hh, smul_inv_smul]
    · rintro ⟨g, hg⟩
      rcases Sym2.eq_iff.1 hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (m7_graphAction.adj_smul g xDot yDot).2 m7_adj_xy
      · exact (m7_graphAction.adj_smul g yDot xDot).2 m7_adj_xy.symm

theorem m7_mem_HDot {g : GL6} (hM : g ∈ MDot) (hs : g ∈ MulAction.stabilizer GL6 V3plus) :
    (⟨g, hM⟩ : ↥MDot) ∈ HDot :=
  Subgroup.mem_subgroupOf.2 ⟨hM, hs⟩

theorem m7_mem_stab_V3 {g : GL6}
    (h : ∀ v : V6, ((mat(g) *ᵥ v) 2 = 0 ∧ (mat(g) *ᵥ v) 3 = 0 ∧ (mat(g) *ᵥ v) 4 = 0) ↔
      (v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0)) :
    g ∈ MulAction.stabilizer GL6 V3plus :=
  (quat_mem_stabilizer_iff g V3plus).2 fun v => by
    rw [ai_mem_V3plus_iff, quat_smul_def, ai_mem_V3plus_iff]
    exact (h v).symm

theorem m7_HDot_smul_mem {h : ↥MDot} (hh : h ∈ HDot) {P : PtX} (hP : P ∈ DeltaDotH) :
    h • P ∈ DeltaDotH := by
  have hs : (h : GL6) ∈ MulAction.stabilizer GL6 V3plus := (Subgroup.mem_subgroupOf.1 hh).2
  intro v hv
  obtain ⟨b, hb, rfl⟩ := (quat_mem_smul_iff _ _ _).1 hv
  exact ((quat_mem_stabilizer_iff _ _).1 hs b).1 (hP hb)

theorem m7_mem_DeltaDotH_iff {P : PtX} : P ∈ DeltaDotH ↔ P = xDot ∨ P = yDot ∨ P = m7zPt := by
  rw [DeltaDotH_eq]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem m7_xDot_mem : xDot ∈ DeltaDotH := m7_mem_DeltaDotH_iff.2 (Or.inl rfl)

theorem m7_yDot_mem : yDot ∈ DeltaDotH := m7_mem_DeltaDotH_iff.2 (Or.inr (Or.inl rfl))

@[expose] def m7c : V6 := x6 - (x1 - x2)

theorem m7_qV_c : qV m7c = qV x3 := by decide

theorem m7_qV_c_ne : qV m7c ≠ 0 := by
  rw [m7_qV_c]
  exact qV_xvec_ne_zero 2

@[expose] def m7T : GL6 := refl6 m7c m7_qV_c_ne * refl6 x3 (qV_xvec_ne_zero 2)

theorem m7T_mem : m7T ∈ MDot := refl6_mul_refl6_mem_MDot _ _ _ _ m7_qV_c

theorem m7T_apply (x : V6) : mat(m7T) *ᵥ x = m7R m7c (m7R x3 x) :=
  m7_refl_prod_apply _ _ _ _ _

theorem m7R_apply (c x : V6) (k : Fin 6) : m7R c x k = x k - qV c * bil x c * c k := by
  rw [m7R, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem m7T_coord (v : V6) :
    (mat(m7T) *ᵥ v) 2 = -v 2 ∧ (mat(m7T) *ᵥ v) 3 = v 3 ∧ (mat(m7T) *ᵥ v) 4 = v 4 := by
  have hc : m7c 2 = 0 ∧ m7c 3 = 0 ∧ m7c 4 = 0 := by decide
  have hq : qV x3 = 1 := by decide
  have hb : bil v x3 = 2 * v 2 := by
    rw [bil_coord]
    simp only [x3, mono_xvec_apply]
    simp
  rw [m7T_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [m7R_apply, hc.1, mul_zero, sub_zero, m7R_apply, hb, hq]
    simp only [x3, mono_xvec_apply]
    simp
    ring
  · rw [m7R_apply, hc.2.1, mul_zero, sub_zero, m7R_apply]
    simp [x3, mono_xvec_apply]
  · rw [m7R_apply, hc.2.2, mul_zero, sub_zero, m7R_apply]
    simp [x3, mono_xvec_apply]

theorem m7T_stab : m7T ∈ MulAction.stabilizer GL6 V3plus := by
  refine m7_mem_stab_V3 fun v => ?_
  obtain ⟨h2, h3, h4⟩ := m7T_coord v
  rw [h2, h3, h4, neg_eq_zero]

theorem m7T_x6 : mat(m7T) *ᵥ x6 = x1 - x2 := by
  rw [m7T_apply]; decide

theorem m7T_u : mat(m7T) *ᵥ (x1 - x2) = x6 := by
  rw [m7T_apply]; decide

theorem m7T_z : mat(m7T) *ᵥ (x1 + x2) = x1 + x2 := by
  rw [m7T_apply]; decide

@[expose] def m7t : ↥MDot := ⟨m7T, m7T_mem⟩

theorem m7t_mem : m7t ∈ HDot := m7_mem_HDot m7T_mem m7T_stab

theorem m7t_x : m7t • xDot = yDot := m7_smul_eq (v := x6) rfl rfl (Or.inl m7T_x6)

theorem m7t_y : m7t • yDot = xDot := m7_smul_eq (v := x1 - x2) rfl rfl (Or.inl m7T_u)

theorem m7t_z : m7t • m7zPt = m7zPt := m7_smul_eq (v := x1 + x2) rfl rfl (Or.inl m7T_z)

theorem m7_E_mem : eJ {1, 2} ∈ MDot := eJ_mem_MDot {1, 2} (by decide) (by decide)

theorem m7_eJ_stab_V3 (J : Finset (Fin 6)) : eJ J ∈ MulAction.stabilizer GL6 V3plus := by
  refine m7_mem_stab_V3 fun v => ?_
  rw [mono_eJ_mulVec]
  simp only [mul_eq_zero, mono_eJd_ne_zero J, false_or]

@[expose] def m7e : ↥MDot := ⟨eJ {1, 2}, m7_E_mem⟩

theorem m7e_mem : m7e ∈ HDot := m7_mem_HDot m7_E_mem (m7_eJ_stab_V3 _)

theorem m7e_x : m7e • xDot = xDot :=
  m7_smul_eq (v := x6) rfl rfl (Or.inl (by decide))

theorem m7e_y : m7e • yDot = m7zPt :=
  m7_smul_eq (v := x1 - x2) rfl rfl (Or.inl (by decide))

theorem m7e_z : m7e • m7zPt = yDot :=
  m7_smul_eq (v := x1 + x2) rfl rfl (Or.inl (by decide))

theorem m7_swap : ∃ t ∈ HDot, t • xDot = yDot ∧ t • yDot = xDot := ⟨m7t, m7t_mem, m7t_x, m7t_y⟩

theorem m7_verts_eq :
    DeltaDotSub.verts = (fun i : ↥MDot => i • xDot) '' (HDot : Set ↥MDot) := by
  have hv : DeltaDotSub.verts = DeltaDotH := SimpleGraph.Subgraph.induce_verts _ _
  rw [hv]
  ext P
  constructor
  · intro hP
    rcases m7_mem_DeltaDotH_iff.1 hP with rfl | rfl | rfl
    · exact ⟨1, one_mem _, one_smul _ _⟩
    · exact ⟨m7t, m7t_mem, m7t_x⟩
    · exact ⟨m7e * m7t, Subgroup.mul_mem _ m7e_mem m7t_mem, by
        show (m7e * m7t) • xDot = m7zPt
        rw [mul_smul, m7t_x, m7e_y]⟩
  · rintro ⟨h, hh, rfl⟩
    exact m7_HDot_smul_mem hh m7_xDot_mem

theorem m7_edgeSet_I_eq :
    DeltaDotSub.edgeSet = (fun i : ↥MDot => s(i • xDot, i • yDot)) '' (HDot : Set ↥MDot) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.Subgraph.mem_edgeSet]
    change (a ∈ DeltaDotH ∧ b ∈ DeltaDotH ∧ (⊤ : DeltaDot.Subgraph).Adj a b) ↔ _
    rw [SimpleGraph.Subgraph.top_adj]
    constructor
    · rintro ⟨ha, hb, hab⟩
      rw [m7_mem_DeltaDotH_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab.ne
      · exact ⟨1, one_mem _, by
          show s((1 : ↥MDot) • xDot, (1 : ↥MDot) • yDot) = _
          rw [one_smul, one_smul]⟩
      · refine ⟨m7e, m7e_mem, ?_⟩
        show s(m7e • xDot, m7e • yDot) = _
        rw [m7e_x, m7e_y]
      · refine ⟨m7t, m7t_mem, ?_⟩
        show s(m7t • xDot, m7t • yDot) = _
        rw [m7t_x, m7t_y]
      · exact absurd rfl hab.ne
      · refine ⟨m7t * m7e, Subgroup.mul_mem _ m7t_mem m7e_mem, ?_⟩
        show s((m7t * m7e) • xDot, (m7t * m7e) • yDot) = _
        rw [mul_smul, mul_smul, m7e_x, m7e_y, m7t_x, m7t_z]
      · refine ⟨m7e * m7t, Subgroup.mul_mem _ m7e_mem m7t_mem, ?_⟩
        show s((m7e * m7t) • xDot, (m7e * m7t) • yDot) = _
        rw [mul_smul, mul_smul, m7t_x, m7t_y, m7e_x, m7e_y]
      · refine ⟨m7e * m7t * m7e,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ m7e_mem m7t_mem) m7e_mem, ?_⟩
        show s((m7e * m7t * m7e) • xDot, (m7e * m7t * m7e) • yDot) = _
        rw [mul_smul, mul_smul, mul_smul, mul_smul, m7e_x, m7e_y, m7t_x, m7t_z, m7e_y, m7e_z]
      · exact absurd rfl hab.ne
    · rintro ⟨h, hh, hg⟩
      have hx := m7_HDot_smul_mem hh m7_xDot_mem
      have hy := m7_HDot_smul_mem hh m7_yDot_mem
      rcases Sym2.eq_iff.1 hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hx, hy, (m7_graphAction.adj_smul h xDot yDot).2 m7_adj_xy⟩
      · exact ⟨hy, hx, (m7_graphAction.adj_smul h yDot xDot).2 m7_adj_xy.symm⟩

theorem m7t_mem_stab_pair : m7t ∈ MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX) := by
  rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, m7t_x, m7t_y]
  exact Set.pair_comm _ _

theorem m7_I_eq :
    HDot = HDot ⊓ MulAction.stabilizer ↥MDot xDot ⊔
      HDot ⊓ MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro h hh
  have hBm : ∀ k : ↥MDot, k ∈ HDot → k • xDot = xDot →
      k ∈ HDot ⊓ MulAction.stabilizer ↥MDot xDot ⊔
        HDot ⊓ MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX) :=
    fun k hk hkx => Subgroup.mem_sup_left ⟨hk, hkx⟩
  have hCt : m7t ∈ HDot ⊓ MulAction.stabilizer ↥MDot xDot ⊔
      HDot ⊓ MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX) :=
    Subgroup.mem_sup_right ⟨m7t_mem, m7t_mem_stab_pair⟩
  have hBe := hBm m7e m7e_mem m7e_x
  rcases m7_mem_DeltaDotH_iff.1 (m7_HDot_smul_mem hh m7_xDot_mem) with h1 | h1 | h1
  · exact hBm h hh h1
  · have h2 := hBm (m7t⁻¹ * h) (Subgroup.mul_mem _ (Subgroup.inv_mem _ m7t_mem) hh)
      (by rw [mul_smul, h1, inv_smul_eq_iff]; exact m7t_x.symm)
    have := Subgroup.mul_mem _ hCt h2
    rwa [mul_inv_cancel_left] at this
  · have hk : (m7e * m7t) • xDot = m7zPt := by rw [mul_smul, m7t_x, m7e_y]
    have h2 := hBm ((m7e * m7t)⁻¹ * h)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ m7e_mem m7t_mem)) hh)
      (by rw [mul_smul, h1, inv_smul_eq_iff]; exact hk.symm)
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hBe hCt) h2
    rwa [mul_inv_cancel_left] at this

@[expose] def m7A : Subgroup ↥MDot :=
  MulAction.stabilizer ↥MDot xDot ⊓ MulAction.stabilizer ↥MDot yDot

@[expose] def m7B : Subgroup ↥MDot := HDot ⊓ MulAction.stabilizer ↥MDot xDot

@[expose] def m7Q : Subgroup ↥MDot := m7A ⊔ m7B

theorem m7_Q_le_Sx : m7Q ≤ MulAction.stabilizer ↥MDot xDot :=
  sup_le inf_le_left inf_le_right

theorem m7_mem_A {g : GL6} (hM : g ∈ MDot) (h0 : g ∈ M0Dot) (hc : g * fDot = fDot * g) :
    (⟨g, hM⟩ : ↥MDot) ∈ m7A := by
  have hx : (⟨g, hM⟩ : ↥MDot) • xDot = xDot := (m7_mem_Sx hM).2 h0
  exact ⟨hx, m7_cen_fix_yDot hc hx⟩

theorem m7_mem_B_eJ (J : Finset (Fin 6)) (hJ : J ⊆ Iset) (he : Even J.card) :
    (⟨eJ J, eJ_mem_MDot J hJ he⟩ : ↥MDot) ∈ m7B :=
  ⟨m7_mem_HDot _ (m7_eJ_stab_V3 J), (m7_mem_Sx _).2 (GDot_le_M0Dot (eJ_mem_GDot J hJ he))⟩

theorem m7e_mem_B : m7e ∈ m7B := ⟨m7e_mem, m7e_x⟩

theorem m7_frattini {g q : ↥MDot} (hg : g ∈ MulAction.stabilizer ↥MDot xDot) (hq : q ∈ m7Q)
    (h : q • yDot = g • yDot) : g ∈ m7Q := by
  have hqx : q • xDot = xDot := m7_Q_le_Sx hq
  have hgx : g • xDot = xDot := hg
  have hA : q⁻¹ * g ∈ m7A := by
    refine ⟨?_, ?_⟩
    · show (q⁻¹ * g) • xDot = xDot
      rw [mul_smul, hgx, inv_smul_eq_iff]
      exact hqx.symm
    · show (q⁻¹ * g) • yDot = yDot
      rw [mul_smul, ← h, inv_smul_smul]
  have := Subgroup.mul_mem _ hq (Subgroup.mem_sup_left hA : q⁻¹ * g ∈ m7Q)
  rwa [mul_inv_cancel_left] at this

@[expose] def m7c2 : V6 := x1 + x2 - x3 + x4

theorem m7_qV_c2 : qV m7c2 = qV x5 := by decide

theorem m7_qV_c2_ne : qV m7c2 ≠ 0 := by
  rw [m7_qV_c2]
  exact qV_xvec_ne_zero 4

@[expose] def m7P : GL6 := refl6 m7c2 m7_qV_c2_ne * refl6 x5 (qV_xvec_ne_zero 4)

theorem m7P_mem : m7P ∈ MDot := refl6_mul_refl6_mem_MDot _ _ _ _ m7_qV_c2

theorem m7P_apply (x : V6) : mat(m7P) *ᵥ x = m7R m7c2 (m7R x5 x) :=
  m7_refl_prod_apply _ _ _ _ _

theorem m7P_x6 : mat(m7P) *ᵥ x6 = x6 := by
  rw [m7P_apply]; decide

theorem m7P_u : mat(m7P) *ᵥ (x1 - x2) = x1 - x2 := by
  rw [m7P_apply]; decide

theorem m7P_z : mat(m7P) *ᵥ (x1 + x2) = x3 - x4 := by
  rw [m7P_apply]; decide

theorem m7P_mem_A : (⟨m7P, m7P_mem⟩ : ↥MDot) ∈ m7A :=
  ⟨m7_smul_eq (v := x6) rfl rfl (Or.inl m7P_x6), m7_smul_eq (v := x1 - x2) rfl rfl (Or.inl m7P_u)⟩

theorem m7P_z_pt : (⟨m7P, m7P_mem⟩ : ↥MDot) • m7zPt = m7wPt :=
  m7_smul_eq (v := x1 + x2) rfl rfl (Or.inl m7P_z)

theorem m7_f5P2_u : mat(f5P2) *ᵥ (x1 - x2) = x3 - x4 := by decide

theorem m7_latT_le_Q6 : latT ≤ m7Q.map MDot.subtype := by
  rw [latT_le_iff]
  intro g hg
  have hg' : g ∈ f5LatCert.tGens := hg
  have hgT : g ∈ TDot := latT_le_TDot (Subgroup.subset_closure hg)
  have hg0 : g ∈ M0Dot := M2Dot_le_M0Dot (TDot_le_M12 hgT).2
  have hgM : g ∈ MDot := hg0.1
  rw [tGens_eq] at hg'
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
  suffices h : (⟨g, hgM⟩ : ↥MDot) ∈ m7Q from ⟨_, h, rfl⟩
  rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.mem_sup_right (m7_mem_B_eJ _ (by decide) (by decide))
  · exact Subgroup.mem_sup_right (m7_mem_B_eJ _ (by decide) (by decide))
  · exact Subgroup.mem_sup_right (m7_mem_B_eJ _ (by decide) (by decide))
  · exact Subgroup.mem_sup_right (m7_mem_B_eJ _ (by decide) (by decide))
  · exact Subgroup.mem_sup_left (m7_mem_A hgM hg0 (by decide +kernel))
  · have hq : (⟨m7P, m7P_mem⟩ : ↥MDot) * m7e ∈ m7Q :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left m7P_mem_A) (Subgroup.mem_sup_right m7e_mem_B)
    refine m7_frattini ((m7_mem_Sx hgM).2 hg0) hq ?_
    have h1 : (⟨m7P, m7P_mem⟩ * m7e : ↥MDot) • yDot = m7wPt := by
      rw [mul_smul, m7e_y, m7P_z_pt]
    have h2 : (⟨f5P2, hgM⟩ : ↥MDot) • yDot = m7wPt :=
      m7_smul_eq (v := x1 - x2) rfl rfl (Or.inl m7_f5P2_u)
    rw [h1, h2]
  · exact Subgroup.mem_sup_left (m7_mem_A hgM hg0 rfl)

theorem m7_DDot_le_Q6 : DDot ≤ m7Q.map MDot.subtype := by
  intro g hg
  have hgG : g ∈ GDot := hg.1
  have hM : g ∈ MDot := hgG.1
  have hc : g * fDot = fDot * g := Subgroup.mem_centralizer_singleton_iff.1 hg.2
  exact ⟨⟨g, hM⟩, Subgroup.mem_sup_left (m7_mem_A hM (GDot_le_M0Dot hgG) hc), rfl⟩

theorem m7_Q6_eq : m7Q.map MDot.subtype = M0Dot := by
  have hle : m7Q.map MDot.subtype ≤ M0Dot := by
    rintro _ ⟨q, hq, rfl⟩
    have : q ∈ MulAction.stabilizer ↥MDot xDot := m7_Q_le_Sx hq
    rw [stabilizer_xDot] at this
    exact this
  have hD : 720 ∣ Nat.card ↥(m7Q.map MDot.subtype) :=
    card_DDot ▸ Subgroup.card_dvd_of_le m7_DDot_le_Q6
  rw [← latM0_eq_M0Dot] at hle ⊢
  rcases lat_overgroups _ m7_latT_le_Q6 hle with h | h | h | h | h | h
  · rw [h, card_latT] at hD; norm_num at hD
  · rw [h, card_latA] at hD; norm_num at hD
  · rw [h, card_latB] at hD; norm_num at hD
  · rw [h, card_latM1] at hD; norm_num at hD
  · rw [h, card_latM2] at hD; norm_num at hD
  · exact h

theorem m7_stab_eq :
    MulAction.stabilizer ↥MDot xDot =
      MulAction.stabilizer ↥MDot xDot ⊓ MulAction.stabilizer ↥MDot yDot ⊔
        HDot ⊓ MulAction.stabilizer ↥MDot xDot := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_right)
  intro g hg
  have hg0 : (g : GL6) ∈ m7Q.map MDot.subtype := by
    rw [m7_Q6_eq]
    have := hg
    rw [stabilizer_xDot] at this
    exact this
  obtain ⟨q, hq, hqg⟩ := hg0
  have : q = g := Subtype.ext hqg
  rwa [← this]

theorem isUniquenessSystem_model
    (hsup : MulAction.stabilizer ↥MDot xDot ⊔ HDot = ⊤) :
    CFSG.Quasithin.Asc94.IsUniquenessSystem DeltaDot HDot DeltaDotSub xDot yDot where
  graphAction := m7_graphAction
  trans := m7_trans
  edgeSet_eq := m7_edgeSet_eq
  swap := m7_swap
  verts_eq := m7_verts_eq
  edgeSet_I_eq := m7_edgeSet_I_eq
  sup_eq_top := hsup
  stab_eq := m7_stab_eq
  I_eq := m7_I_eq

end

module

public import CFSG.Quasithin.Background.SmithB49Coc
public import CFSG.Quasithin.Background.SmithB49D4
public import CFSG.Quasithin.Background.SmithB51LnSec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.B49

open Matrix Module CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln

section QW

variable {n : ℕ}

@[expose] def qW (W : Submodule (ZMod 2) (Fin n → ZMod 2)) : Subgroup ↥(StatedSL n (ZMod 2)) where
  carrier := {g | (∀ x, mat g *ᵥ x - x ∈ W) ∧ ∀ w ∈ W, mat g *ᵥ w = w}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · rw [mat_mul, ← mulVec_mulVec]
      have : mat g *ᵥ (mat h *ᵥ x) - x = (mat g *ᵥ (mat h *ᵥ x) - mat h *ᵥ x) +
          (mat h *ᵥ x - x) := by abel
      rw [this]
      exact W.add_mem (hg1 _) (hh1 x)
    · rw [mat_mul, ← mulVec_mulVec, hh2 w hw, hg2 w hw]
  one_mem' := ⟨fun x => by rw [mat_one, one_mulVec, sub_self]; exact W.zero_mem,
    fun w _ => by rw [mat_one, one_mulVec]⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun x => ?_, fun w hw => ?_⟩
    · have h1 := hg1 (mat g⁻¹ *ᵥ x)
      rw [mulVec_mulVec_inv] at h1
      have : mat g⁻¹ *ᵥ x - x = -(x - mat g⁻¹ *ᵥ x) := by abel
      rw [this]
      exact W.neg_mem h1
    · conv_lhs => rw [← hg2 w hw]
      rw [mulVec_inv_mulVec]

theorem le_fixN_qW (W : Submodule (ZMod 2) (Fin n → ZMod 2)) : W ≤ fixN (qW W) :=
  fun _ hw _ hg => hg.2 _ hw

theorem commN_qW_le (W : Submodule (ZMod 2) (Fin n → ZMod 2)) : commN (qW W) ≤ W := by
  rw [commN, Submodule.span_le]
  rintro _ ⟨g, hg, x, rfl⟩
  exact hg.1 x

theorem card_qW_le {W : Submodule (ZMod 2) (Fin n → ZMod 2)} :
    Nat.card (qW W) ≤ 2 ^ ((n - finrank (ZMod 2) W) * finrank (ZMod 2) W) := by
  refine (card_le_two_pow_mul (qW W)).trans (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 := Submodule.finrank_mono (le_fixN_qW W)
  have h2 := Submodule.finrank_mono (commN_qW_le W)
  exact Nat.mul_le_mul (by omega) h2

end QW

theorem exists_conj_W {W : Submodule (ZMod 2) (Fin 4 → ZMod 2)} (hW : finrank (ZMod 2) W = 2) :
    ∃ γ : ↥(StatedSL 4 (ZMod 2)), ∀ y, y ∈ W ↔
      ∃ y₀ : Fin 4 → ZMod 2, y₀ 2 = 0 ∧ y₀ 3 = 0 ∧ y = mat γ *ᵥ y₀ := by
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hW' : finrank (ZMod 2) W' = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hWW'
    rw [Module.finrank_fin_fun, hW] at this
    omega
  set b := Module.finBasisOfFinrankEq (ZMod 2) W hW
  set b' := Module.finBasisOfFinrankEq (ZMod 2) W' hW'
  set u : Fin 4 → Fin 4 → ZMod 2 := ![(b 0 : Fin 4 → ZMod 2), (b 1 : Fin 4 → ZMod 2),
    (b' 0 : Fin 4 → ZMod 2), (b' 1 : Fin 4 → ZMod 2)]
  set P : Matrix (Fin 4) (Fin 4) (ZMod 2) := Matrix.of fun i k => u k i
  have hP : ∀ y : Fin 4 → ZMod 2, P *ᵥ y =
      y 0 • (b 0 : Fin 4 → ZMod 2) + y 1 • (b 1 : Fin 4 → ZMod 2) +
        y 2 • (b' 0 : Fin 4 → ZMod 2) + y 3 • (b' 1 : Fin 4 → ZMod 2) := by
    intro y
    funext i
    simp [P, u, Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]
  have hsurj : Function.Surjective P.mulVec := by
    intro z
    have hz : z ∈ W ⊔ W' := by rw [hWW'.sup_eq_top]; trivial
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.1 hz
    refine ⟨![b.repr ⟨w, hw⟩ 0, b.repr ⟨w, hw⟩ 1, b'.repr ⟨w', hw'⟩ 0, b'.repr ⟨w', hw'⟩ 1], ?_⟩
    rw [hP]
    have e1 := b.sum_repr ⟨w, hw⟩
    have e2 := b'.sum_repr ⟨w', hw'⟩
    rw [Fin.sum_univ_two] at e1 e2
    have e1' := congrArg Subtype.val e1
    have e2' := congrArg Subtype.val e2
    simp only [Submodule.coe_add, Submodule.coe_smul] at e1' e2'
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    conv_rhs => rw [← e1', ← e2']
    abel
  have hu : IsUnit P := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨ofGL hu.unit, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · refine ⟨![b.repr ⟨y, hy⟩ 0, b.repr ⟨y, hy⟩ 1, 0, 0], rfl, rfl, ?_⟩
    rw [mat_ofGL, IsUnit.unit_spec, hP]
    have e1 := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [Fin.sum_univ_two] at e1
    simp only [Submodule.coe_add, Submodule.coe_smul] at e1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zero_smul, add_zero]
    exact e1.symm
  · rintro ⟨y₀, h2, h3, rfl⟩
    rw [mat_ofGL, IsUnit.unit_spec, hP, h2, h3, zero_smul, zero_smul, add_zero, add_zero]
    exact W.add_mem (W.smul_mem _ (b 0).2) (W.smul_mem _ (b 1).2)

@[expose] noncomputable def tq (a b : Fin 2) : ↥(StatedSL 4 (ZMod 2)) :=
  wordEval sgen4 (tw4 (qi a) (qj b))

theorem qi_ne_qj (a b : Fin 2) : qi a ≠ qj b := by
  revert a b
  decide

theorem mat_tq (a b : Fin 2) : mat (tq a b) = transvection (qi a) (qj b) 1 := by
  rw [tq, mat_wordEval_sgen4]
  exact tw4_bits _ _ (qi_ne_qj a b)

theorem transvection_sq : ∀ a b : Fin 2,
    transvection (qi a) (qj b) (1 : ZMod 2) * transvection (qi a) (qj b) 1 = 1 := by
  decide +kernel

theorem dmat_tq (a b : Fin 2) : dmat (tq a b) = (transvection (qi a) (qj b) 1)ᵀ := by
  have h : mat (tq a b) * transvection (qi a) (qj b) 1 = 1 := by
    rw [mat_tq]
    exact transvection_sq a b
  rw [dmat, mat_inv_eq h]

theorem fixed_dual : ∀ m : Fin 4 → ZMod 2,
    (∀ a b : Fin 2, (transvection (qi a) (qj b) (1 : ZMod 2))ᵀ *ᵥ m = m) →
      m 0 = 0 ∧ m 1 = 0 := by
  decide +kernel

theorem eq_vec_of (m : Fin 4 → ZMod 2) (h0 : m 0 = 0) (h1 : m 1 = 0) :
    m = ![0, 0, m 2, m 3] := by
  funext i
  fin_cases i <;> simp [h0, h1]

theorem transvection_sub : ∀ (a b : Fin 2) (y : Fin 4 → ZMod 2),
    (transvection (qi a) (qj b) (1 : ZMod 2) *ᵥ y - y) 2 = 0 ∧
      (transvection (qi a) (qj b) (1 : ZMod 2) *ᵥ y - y) 3 = 0 := by
  decide +kernel

theorem transvection_fix : ∀ (a b : Fin 2) (y : Fin 4 → ZMod 2), y 2 = 0 → y 3 = 0 →
    transvection (qi a) (qj b) (1 : ZMod 2) *ᵥ y = y := by
  decide +kernel

theorem conj_tq_mem {W : Submodule (ZMod 2) (Fin 4 → ZMod 2)} {γ : ↥(StatedSL 4 (ZMod 2))}
    (hγ : ∀ y, y ∈ W ↔ ∃ y₀ : Fin 4 → ZMod 2, y₀ 2 = 0 ∧ y₀ 3 = 0 ∧ y = mat γ *ᵥ y₀)
    (a b : Fin 2) : γ * tq a b * γ⁻¹ ∈ qW W := by
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · rw [hγ]
    refine ⟨transvection (qi a) (qj b) 1 *ᵥ (mat γ⁻¹ *ᵥ x) - mat γ⁻¹ *ᵥ x,
      (transvection_sub a b _).1, (transvection_sub a b _).2, ?_⟩
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, mat_tq, mulVec_sub,
      mulVec_mulVec_inv]
  · obtain ⟨w₀, h2, h3, rfl⟩ := (hγ w).1 hw
    rw [mat_mul, mat_mul, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_inv_mulVec, mat_tq,
      transvection_fix a b w₀ h2 h3]

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)} {U : Subgroup V}
  {π : ↥(StatedSL 4 (ZMod 2)) →* ↥L}

omit [Finite V] in
theorem fixed_tq_mem (D : ExtData L U π (dmatHom 4)) {x₀ : Fin 4 × Fin 4 → ZMod 2}
    (hx₀ : ∀ j, (D.coc - coboundaryA (muK (dmatHom 4)) x₀) (sgen4 j) = fvD4 j) {v : V}
    (hv : ∀ a b : Fin 2, ((π (tq a b) : ↥L) : MulAut V) v = v) : v ∈ U := by
  set μ := muK (dmatHom 4)
  have hc' : D.coc - coboundaryA μ x₀ ∈ Z1A μ := sub_mem D.coc_mem (B1A_le_Z1A _ ⟨x₀, rfl⟩)
  set X₀ := ExtData.unvec x₀
  have hcmat : ∀ a b : Fin 2, D.cmat (tq a b) = FmD4 a b +
      (mat (tq a b) * X₀ * dmat (tq a b)⁻¹ - X₀) := by
    intro a b
    have h1 := cocycle_word muK_sgen4_dmat hc' (tw4 (qi a) (qj b))
    simp only [hx₀] at h1
    rw [← tq] at h1
    simp only [← decM_foxDB] at h1
    rw [cocD4_tw a b] at h1
    have h2 : (D.coc - coboundaryA μ x₀) (tq a b) = (D.cmat (tq a b)).vec -
        ((mat (tq a b) * X₀ * dmat (tq a b)⁻¹).vec - X₀.vec) := by
      show D.coc (tq a b) - (μ (tq a b) x₀ - x₀) = _
      rw [← ExtData.vec_unvec x₀, muK_vec]
      rfl
    rw [h2] at h1
    rw [← vec_inj, vec_add, vec_sub, ← h1]
    abel
  set m := Multiplicative.toAdd (D.q v) with hm
  have hqfix : ∀ a b : Fin 2, dmat (tq a b) *ᵥ m = m := by
    intro a b
    have := D.q_eq (tq a b) v
    rw [hv a b] at this
    exact this.symm
  have hm01 := fixed_dual m (fun a b => by rw [← dmat_tq]; exact hqfix a b)
  obtain ⟨y, hy⟩ : ∃ y, y = Multiplicative.toAdd (D.b ⟨_, D.sub_mem_U v⟩) := ⟨_, rfl⟩
  have hfix : ∀ a b : Fin 2, FmD4 a b *ᵥ m =
      (transvection (qi a) (qj b) 1 - 1) *ᵥ (y + X₀ *ᵥ m) := by
    intro a b
    have h1 := D.fixed (hqfix a b) (hv a b)
    have hinv : dmat (tq a b)⁻¹ *ᵥ m = m := by
      conv_lhs => rw [← hqfix a b]
      rw [mulVec_mulVec, dmat_inv_mul, one_mulVec]
    rw [← hm, ← hy, hcmat, add_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hinv,
      mat_tq] at h1
    have h2 : FmD4 a b *ᵥ m = y - transvection (qi a) (qj b) 1 *ᵥ y -
        (transvection (qi a) (qj b) 1 *ᵥ (X₀ *ᵥ m) - X₀ *ᵥ m) := by
      rw [← h1]
      abel
    rw [h2, sub_mulVec, one_mulVec, mulVec_add]
    funext p
    simp only [Pi.add_apply, Pi.sub_apply]
    generalize y p = e₁
    generalize (transvection (qi a) (qj b) (1 : ZMod 2) *ᵥ y) p = e₂
    generalize (transvection (qi a) (qj b) (1 : ZMod 2) *ᵥ (X₀ *ᵥ m)) p = e₃
    generalize (X₀ *ᵥ m) p = e₄
    revert e₁ e₂ e₃ e₄
    decide
  have hm23 := offD4_check (m 2) (m 3) (y + X₀ *ᵥ m) (fun a b => by
    rw [← eq_vec_of m hm01.1 hm01.2]
    exact hfix a b)
  have hm0 : m = 0 := by
    rw [eq_vec_of m hm01.1 hm01.2, hm23.1, hm23.2]
    funext i
    fin_cases i <;> rfl
  rw [← D.q_ker]
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact hm0

omit [Finite V] in
theorem rk_U_V (D : ExtData L U π (dmatHom 4)) : rk ↥U = 4 ∧ rk V = 8 := by
  have hU : Nat.card ↥U = 2 ^ 4 := by
    rw [Nat.card_congr D.b.toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 2 ^ 4
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hker : D.q.ker = U := by
    ext v
    exact D.q_ker v
  have hsurj : Function.Surjective D.q := fun m => ⟨D.s m, D.qs m⟩
  let e : V ⧸ U ≃* Multiplicative (Fin 4 → ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective D.q hsurj)
  have hQ : Nat.card (V ⧸ U) = 2 ^ 4 := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 2 ^ 4
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hV : Nat.card V = 2 ^ 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup U, hQ, hU]
    norm_num
  constructor
  · unfold rk
    rw [hU, padicValNat.prime_pow]
  · unfold rk
    rw [hV, padicValNat.prime_pow]

theorem no_offender_D4 (hV : ∀ v : V, v ^ 2 = 1) (hU : RealM L U ⊥ π mat)
    (hQ : RealM L ⊤ U π dmat) (D : ExtData L U π (dmatHom 4)) {x₀ : Fin 4 × Fin 4 → ZMod 2}
    (hx₀ : ∀ j, (D.coc - coboundaryA (muK (dmatHom 4)) x₀) (sgen4 j) = fvD4 j)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender L A) (hq : IsQuadratic A) : False := by
  have hπ : Function.Bijective π := ⟨hU.injective (Or.inl rfl), hU.1⟩
  have hAL : A ≤ L := hA.1
  have hA2 : IsPGroup 2 ↥A := hA.2.2.1.isPGroup
  have hAtop : A ≤ stabSub (⊤ : Subgroup V) := fun g _ u => by simp
  have hAU : A ≤ stabSub U := hAL.trans hU.hLW
  have e1 := rkIdx_fixV_le_rk hV hA
  have e2 := rkSub_ge_sec (A := A) hV (le_top : U ≤ ⊤) hAtop
  have e3 := hQ.rkIdx_fixV_autSec hAL
  rw [fixM_dmat] at e3
  have e4 := rkIdx_fixV_autSec_bot hAU
  have e5 := hU.rkIdx_fixV_autSec hAL
  rw [fixM_mat] at e5
  have e6 := rk_le_mul_pre hπ hAL hA2
  have e7 := finrank_fixD_add (pre π A)
  have hcf := hU.commN_le_fixN hq
  have e8 := finrank_commN_le_of_le hcf
  have e9 := finrank_fixM_lt hπ (Or.inl rfl) hAL hA.2.1
  rw [fixM_mat] at e9
  have e10 := rkSub_top A
  have hab : finrank (ZMod 2) (fixN (pre π A)) = 2 ∧ finrank (ZMod 2) (commN (pre π A)) = 2 ∧
      rk ↥A = 4 := by
    set a := finrank (ZMod 2) (fixN (pre π A))
    set b := finrank (ZMod 2) (commN (pre π A))
    have ha3 : a ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> omega
  obtain ⟨ha, hb, hrA⟩ := hab
  set W := fixN (pre π A)
  have hWc : commN (pre π A) = W :=
    Submodule.eq_of_le_of_finrank_eq hcf (by rw [hb, ha])
  have hBQ : pre π A = qW W := by
    refine Subgroup.eq_of_le_of_card_ge (fun g hg => ⟨fun x => ?_, fun w hw => hw g hg⟩) ?_
    · rw [← hWc]
      exact sub_mem_commN hg x
    · rw [card_pre hπ hAL, card_eq_two_pow_of_isPGroup hA2, hrA]
      refine card_qW_le.trans ?_
      rw [ha]
  obtain ⟨γ, hγ⟩ := exists_conj_W ha
  have hmemA : ∀ a b : Fin 2, ((π (γ * tq a b * γ⁻¹) : ↥L) : MulAut V) ∈ A := by
    intro a b
    have : γ * tq a b * γ⁻¹ ∈ pre π A := by rw [hBQ]; exact conj_tq_mem hγ a b
    exact this
  have key : ∀ (g : ↥(StatedSL 4 (ZMod 2))) (x : V),
      ((π g : ↥L) : MulAut V) (((π g⁻¹ : ↥L) : MulAut V) x) = x := by
    intro g x
    rw [← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hfixU : fixV A ≤ U := by
    intro v hv
    obtain ⟨v', hv'd⟩ : ∃ v', v' = ((π γ⁻¹ : ↥L) : MulAut V) v := ⟨_, rfl⟩
    have hv' : ∀ a b : Fin 2, ((π (tq a b) : ↥L) : MulAut V) v' = v' := by
      intro a b
      have e : tq a b = γ⁻¹ * (γ * tq a b * γ⁻¹) * γ := by group
      rw [e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply,
        MulAut.mul_apply, hv'd, key γ v, hv _ (hmemA a b)]
    have hv'U := fixed_tq_mem D hx₀ hv'
    have hvv : v = ((π γ : ↥L) : MulAut V) v' := by
      rw [hv'd, key γ v]
    rw [hvv]
    exact D.hLU _ _ hv'U
  obtain ⟨hrU, hrV⟩ := rk_U_V D
  have hinf : U ⊓ fixV A = fixV A := inf_eq_right.2 hfixU
  have e11 := rk_add_rkIdx (fixV A)
  have e12 : rk ↥(U ⊓ fixV A) ≤ rk ↥U := rk_mono inf_le_left
  unfold rkSub at e4
  rw [hinf] at e4 e12
  omega

end CFSG.Quasithin.B5.B49

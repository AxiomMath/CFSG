module

public import CFSG.Timmesfeld.ARS.CaseMSU
public import CFSG.Timmesfeld.ARS.CaseOADegSpAlign

public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Timmesfeld.LieEmbed
open scoped commutatorElement

abbrev c4 (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

abbrev c4' (i : Fin 2) : Fin 4 := ⟨3 - i.val, by omega⟩

theorem rev_ne_self_four (k : Fin 4) : Fin.rev k ≠ k := by
  revert k
  decide

theorem c4_ne_rev : ∀ i : Fin 2, c4 i ≠ Fin.rev (c4 i) := by decide

theorem c4'_ne_rev : ∀ i : Fin 2, c4' i ≠ Fin.rev (c4' i) := by decide

theorem rev_c4 : ∀ k : Fin 2, Fin.rev (c4 k) = c4' k := by decide

theorem rev_c4' : ∀ k : Fin 2, Fin.rev (c4' k) = c4 k := by decide

set_option maxRecDepth 100000 in
theorem weight_four_check : ∀ a b i : Fin 4, b ≠ Fin.rev a →
    weight 4 a - weight 4 b ≠ 2 • weight 4 i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem two_weight_four_check : ∀ a i : Fin 4, 2 • weight 4 a = 2 • weight 4 i → a = i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem toStd_four_longC2 : ∀ i : Fin 2, Unitary.toStd 4 (longC2 i) = 2 • weight 4 (c4 i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem toStd_four_neg_longC2 :
    ∀ i : Fin 2, Unitary.toStd 4 (-longC2 i) = 2 • weight 4 (c4' i) := by
  decide +kernel

theorem isUTransGroup_rootGroup_long₄ {F : Type*} [Field F] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) (i : Fin 4) {γ : Fin (4 / 2) → ℤ}
    (hγ : toStd 4 γ = 2 • weight 4 i) :
    IsUTransGroup σ (Pi.single i 1) (Unitary.rootGroup σ hσ 4 γ) := by
  have hi : i ≠ Fin.rev i := (rev_ne_self_four i).symm
  have heq : Unitary.rootGroup σ hσ 4 γ = (longRootHom σ hi).range := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun _ => iSup_le fun hba => iSup_le fun hw =>
            absurd (hw.trans hγ) (weight_four_check a b i hba)
      · exact iSup_le fun a => iSup_le fun ha => iSup_le fun hw => by
          obtain rfl := two_weight_four_check a i (hw.trans hγ)
          exact le_rfl
      · exact iSup_le fun _ => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun hk => absurd hk (rev_ne_self_four k)
    · exact le_sup_of_le_left (le_sup_of_le_right (le_iSup_of_le i (le_iSup_of_le hi
        (le_iSup_of_le hγ.symm le_rfl))))
  rw [heq]
  refine ⟨fun x => ⟨?_, ?_⟩, fun c hc => ⟨longRootHom σ hi (Multiplicative.ofAdd ⟨c, hc⟩), ?_⟩⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, c.toAdd.2, by rw [suMat_apply, coe_longRootHom, uTrans_single]⟩
  · rintro ⟨c, hc, hx⟩
    refine ⟨Multiplicative.ofAdd ⟨c, hc⟩, suMat_injective σ ?_⟩
    rw [hx, suMat_apply, coe_longRootHom, uTrans_single]
    rfl
  · rw [suMat_apply, coe_longRootHom, uTrans_single]
    rfl

section Witt

variable {F : Type} [Field F]

@[expose] def hypCol₄ (P Q : Fin 2 → Fin 4 → F) (c : Fin 4) : Fin 4 → F :=
  if h : c.val < 2 then P ⟨c.val, h⟩ else Q ⟨3 - c.val, by omega⟩

@[expose] def hypMat₄ (P Q : Fin 2 → Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun a c => hypCol₄ P Q c a

theorem hypMat₄_mulVec_single (P Q : Fin 2 → Fin 4 → F) (c : Fin 4) :
    hypMat₄ P Q *ᵥ Pi.single c 1 = hypCol₄ P Q c := by
  funext a
  simp [hypMat₄, mulVec, dotProduct, Pi.single_apply]

variable [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem exists_su4_mulVec (hF : Nat.card F = (p ^ f) ^ 2) {P Q : Fin 2 → Fin 4 → F}
    (hpp : ∀ i j, uForm (unitaryInvolution F p f) (P i) (P j) = 0)
    (hqq : ∀ i j, uForm (unitaryInvolution F p f) (Q i) (Q j) = 0)
    (hpq : ∀ i j, uForm (unitaryInvolution F p f) (P i) (Q j) = if i = j then 1 else 0) :
    ∃ (g : SU (unitaryInvolution F p f) 4) (l : F), l ≠ 0 ∧ ∀ i : Fin 2,
      suMat _ 4 g *ᵥ Pi.single (c4 i) 1 = (if i = 0 then l else 1) • P i ∧
      suMat _ 4 g *ᵥ Pi.single (c4' i) 1 =
        (if i = 0 then (unitaryInvolution F p f l)⁻¹ else 1) • Q i := by
  set σ := unitaryInvolution F p f with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have hqp : ∀ i j, uForm σ (Q i) (P j) = if i = j then 1 else 0 := fun i j => by
    rw [← uForm_conj σ hσ, hpq]
    split_ifs with h1 h2 h2
    · exact map_one σ
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero σ
  set C := hypMat₄ P Q with hC
  have hgram : conjTr σ C * antidiag 4 * C = antidiag 4 := by
    ext a b
    rw [conjTr_mul_antidiag_mul_apply]
    fin_cases a <;> fin_cases b <;>
      simp [hC, hypMat₄, hypCol₄, hpp, hqq, hpq, hqp, antidiag]
  have hdetJ : (antidiag 4 : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
    have := congrArg Matrix.det (antidiag_mul_antidiag (F := F) (n := 4))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hnorm : σ C.det * C.det = 1 := by
    have h := congrArg Matrix.det hgram
    have e : (C.map σ).det = σ C.det := (RingEquiv.map_det σ C).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, e] at h
    have h' : σ C.det * C.det * (antidiag 4 : Matrix (Fin 4) (Fin 4) F).det =
        1 * (antidiag 4 : Matrix (Fin 4) (Fin 4) F).det := by
      linear_combination h
    exact mul_right_cancel₀ hdetJ h'
  have hC0 : C.det ≠ 0 := right_ne_zero_of_mul_eq_one hnorm
  have hd : σ C.det⁻¹ * C.det⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hnorm, inv_one]
  obtain ⟨l, hl0, hl⟩ := exists_mul_inv_sigma_eq hF hd
  rw [← hσdef] at hl
  have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl0
  set d : Fin 4 → F := fun c => if c = 0 then l else if c = 3 then (σ l)⁻¹ else 1 with hddef
  set C' := C * Matrix.diagonal d with hC'
  have hgram' : conjTr σ C' * antidiag 4 * C' = antidiag 4 := by
    have hD : conjTr σ (Matrix.diagonal d) * antidiag 4 * Matrix.diagonal d = antidiag 4 := by
      ext a b
      rw [conjTr_mul_antidiag_mul_apply]
      fin_cases a <;> fin_cases b <;>
        simp [hddef, uForm_eq, Fin.sum_univ_four, Matrix.diagonal_apply, antidiag, hσ, hl0, hσl]
    rw [hC', conjTr_mul, show conjTr σ (Matrix.diagonal d) * conjTr σ C * antidiag 4 *
        (C * Matrix.diagonal d) = conjTr σ (Matrix.diagonal d) *
          (conjTr σ C * antidiag 4 * C) * Matrix.diagonal d by
        simp only [Matrix.mul_assoc], hgram, hD]
  have hdet' : C'.det = 1 := by
    rw [hC', Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [hddef]
    norm_num
    rw [hl, mul_inv_cancel₀ hC0]
  let g0 : GL (Fin 4) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero C' (by rw [hdet']; exact one_ne_zero)
  have hg0 : g0 ∈ SU σ 4 := mem_SU.2 ⟨hdet', hgram'⟩
  have hd4 : ∀ i : Fin 2, d (c4 i) = if i = 0 then l else 1 := by
    intro i; fin_cases i <;> rfl
  have hd4' : ∀ i : Fin 2, d (c4' i) = if i = 0 then (σ l)⁻¹ else 1 := by
    intro i; fin_cases i <;> rfl
  have hcol : ∀ i : Fin 2, hypCol₄ P Q (c4 i) = P i := fun i => by
    rw [hypCol₄, dite_eq_left i.isLt]
  have hcol' : ∀ i : Fin 2, hypCol₄ P Q (c4' i) = Q i := fun i => by
    rw [hypCol₄, dite_eq_right (show ¬ 3 - i.val < 2 by omega)]
    congr 1
    ext
    show 3 - (3 - i.val) = i.val
    omega
  refine ⟨⟨g0, hg0⟩, l, hl0, fun i => ⟨?_, ?_⟩⟩
  · change C' *ᵥ Pi.single (c4 i) 1 = _
    rw [hC', ← mulVec_mulVec, LieEmbed.diagonal_mulVec_single, mulVec_smul, hC,
      hypMat₄_mulVec_single, hd4, hcol]
  · change C' *ᵥ Pi.single (c4' i) 1 = _
    rw [hC', ← mulVec_mulVec, LieEmbed.diagonal_mulVec_single, mulVec_smul, hC,
      hypMat₄_mulVec_single, hd4', hcol']

end Witt

section Align

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem isUTransGroup_pos₄ (i : Fin 2) :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c4 i) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4
        (longC2 i)) :=
  isUTransGroup_rootGroup_long₄ _ (c4 i) (toStd_four_longC2 i)

theorem isUTransGroup_neg₄ (i : Fin 2) :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c4' i) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4
        (-longC2 i)) :=
  isUTransGroup_rootGroup_long₄ _ (c4' i) (toStd_four_neg_longC2 i)

theorem isUTransGroup_alpha₄ :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c4 1) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4
        (Pi.single (1 : Fin 2) 1)) := by
  rw [← longC2_one]
  exact isUTransGroup_pos₄ hF 1

theorem exists_isUTransGroup_of_mem₄ (g : SU (unitaryInvolution F p f) 4) :
    ∃ v : Fin 4 → F, v ≠ 0 ∧ uForm (unitaryInvolution F p f) v v = 0 ∧
      IsUTransGroup (unitaryInvolution F p f) v (conjSub (Unitary.rootGroup
        (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1))
          g) :=
  ⟨_, suMat_mulVec_ne_zero _ g (single_one_ne_zero (c4 1)),
    (uForm_mulVec _ g _ _).trans (uForm_single_self (c4_ne_rev 1)),
    (isUTransGroup_alpha₄ hF).conjSub g⟩

theorem exists_aligned_su₂ {G : Type*} [Group G] (Φ : SU (unitaryInvolution F p f) 4 →* G)
    (hker : Φ.ker ≤ Subgroup.center _) {P Q : Fin 2 → Subgroup G}
    (hP : ∀ i, ∃ g, P i = (conjSub (Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1)) g).map Φ)
    (hQ : ∀ i, ∃ g, Q i = (conjSub (Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1)) g).map Φ)
    (hopp : ∀ i, ¬ Commuting (P i) (Q i))
    (hcomm : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)) :
    ∃ g : SU (unitaryInvolution F p f) 4, ∀ i,
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4
        (longC2 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = P i ∧
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 4
        (-longC2 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = Q i := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : F) + unitaryInvolution F p f ζ = 0 := ζ.2
  choose h hh using hP
  choose k hk using hQ
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 4 (Pi.single (1 : Fin 2) 1) := ⟨_, rfl⟩
  rw [← hX₀def] at hh hk
  have hX₀ : IsUTransGroup (unitaryInvolution F p f) (Pi.single (c4 1) 1) X₀ :=
    hX₀def ▸ isUTransGroup_alpha₄ hF
  obtain ⟨u, hudef⟩ : ∃ u : Fin 2 → Fin 4 → F,
      u = fun i => suMat _ 4 (h i) *ᵥ Pi.single (c4 1) 1 := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Fin 2 → Fin 4 → F,
      w = fun i => suMat _ 4 (k i) *ᵥ Pi.single (c4 1) 1 := ⟨_, rfl⟩
  have huT : ∀ i, IsUTransGroup (unitaryInvolution F p f) (u i) (conjSub X₀ (h i)) := fun i => by
    rw [hudef]; exact hX₀.conjSub (h i)
  have hwT : ∀ i, IsUTransGroup (unitaryInvolution F p f) (w i) (conjSub X₀ (k i)) := fun i => by
    rw [hwdef]; exact hX₀.conjSub (k i)
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    rw [hudef]; exact suMat_mulVec_ne_zero _ (h i) (single_one_ne_zero _)
  have hw0 : ∀ i, w i ≠ 0 := fun i => by
    rw [hwdef]; exact suMat_mulVec_ne_zero _ (k i) (single_one_ne_zero _)
  have huu : ∀ i, uForm (unitaryInvolution F p f) (u i) (u i) = 0 := fun i => by
    rw [hudef]; exact (uForm_mulVec _ _ _ _).trans (uForm_single_self (c4_ne_rev 1))
  have hww : ∀ i, uForm (unitaryInvolution F p f) (w i) (w i) = 0 := fun i => by
    rw [hwdef]; exact (uForm_mulVec _ _ _ _).trans (uForm_single_self (c4_ne_rev 1))
  have hc : ∀ {X Y : Subgroup G}, Commuting X Y →
      ∀ {A B : Subgroup (SU (unitaryInvolution F p f) 4)}, X = A.map Φ → Y = B.map Φ →
        ∀ x ∈ A, ∀ y ∈ B, ⁅x, y⁆ ∈ Subgroup.center _ := fun hXY A B hA hB =>
    CaseMSU.commutator_mem_center hker (hA ▸ hB ▸ hXY)
  have hprop : ∀ {v v' : Fin 4 → F} {X Y : Subgroup (SU (unitaryInvolution F p f) 4)},
      IsUTransGroup (unitaryInvolution F p f) v X → IsUTransGroup (unitaryInvolution F p f) v' Y →
        v' ≠ 0 → (∃ l : F, v' = l • v) → Y = X := by
    rintro v v' X Y hX hY hv' ⟨l, rfl⟩
    have hl : l ≠ 0 := fun hl => hv' (by rw [hl, zero_smul])
    exact (hY.of_smul hσ hl).eq hX
  have hBuw : ∀ i, uForm (unitaryInvolution F p f) (u i) (w i) ≠ 0 := fun i hB =>
    hopp i (by rw [hh i, hk i]; exact CaseMSU.commuting_map Φ ((huT i).commuting hσ (hwT i) hB))
  have hBuu : ∀ i j, uForm (unitaryInvolution F p f) (u i) (u j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact huu j
    rcases (huT i).uForm_eq_zero_of_center hσ hζ hζ' (huT j) (hu0 i) (huu i) (huu j)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_left) (hh i) (hh j)) with h0 | hl
    · exact h0
    · exfalso
      have hPji : P j = P i := by rw [hh i, hh j, hprop (huT i) (huT j) (hu0 j) hl]
      exact hopp i (by rw [← hPji]; exact ((hcomm i j hij).mono le_sup_right le_sup_left).symm)
  have hBww : ∀ i j, uForm (unitaryInvolution F p f) (w i) (w j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact hww j
    rcases (hwT i).uForm_eq_zero_of_center hσ hζ hζ' (hwT j) (hw0 i) (hww i) (hww j)
        (hc ((hcomm i j hij).mono le_sup_right le_sup_right) (hk i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQji : Q j = Q i := by rw [hk i, hk j, hprop (hwT i) (hwT j) (hw0 j) hl]
      exact hopp i (by rw [← hQji]; exact ((hcomm i j hij).mono le_sup_left le_sup_right))
  have hBuw' : ∀ i j, i ≠ j → uForm (unitaryInvolution F p f) (u i) (w j) = 0 := by
    intro i j hij
    rcases (huT i).uForm_eq_zero_of_center hσ hζ hζ' (hwT j) (hu0 i) (huu i) (hww j)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_right) (hh i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQP : Q j = P i := by rw [hh i, hk j, hprop (huT i) (hwT j) (hw0 j) hl]
      exact hopp j (by rw [hQP]; exact ((hcomm i j hij).mono le_sup_left le_sup_left).symm)
  have hw'T : ∀ i, IsUTransGroup (unitaryInvolution F p f)
      ((uForm (unitaryInvolution F p f) (u i) (w i))⁻¹ • w i) (conjSub X₀ (k i)) := fun i =>
    (hwT i).smul hσ (inv_ne_zero (hBuw i))
  obtain ⟨g, l, hl0, hg⟩ := exists_su4_mulVec hF (P := u)
    (Q := fun i => (uForm (unitaryInvolution F p f) (u i) (w i))⁻¹ • w i) hBuu
    (fun i j => by rw [uForm_smul_left, uForm_smul_right, hBww, mul_zero, mul_zero])
    (fun i j => by
      rw [uForm_smul_right]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, inv_mul_cancel₀ (hBuw i)]
      · rw [ite_eq_right hij, hBuw' i j hij, mul_zero])
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.map_map, hh i]
    congr 1
    have := (isUTransGroup_pos₄ hF i).conjSub g
    rw [(hg i).1] at this
    have hl' : (if i = 0 then l else 1) ≠ 0 := by
      split_ifs
      exacts [hl0, one_ne_zero]
    exact (this.of_smul hσ hl').eq (huT i)
  · rw [← Subgroup.map_map, hk i]
    congr 1
    have := (isUTransGroup_neg₄ hF i).conjSub g
    rw [(hg i).2] at this
    have hl' : (if i = 0 then (unitaryInvolution F p f l)⁻¹ else 1) ≠ 0 := by
      split_ifs
      exacts [inv_ne_zero ((map_ne_zero _).2 hl0), one_ne_zero]
    exact (this.of_smul hσ hl').eq (hw'T i)

end Align

end CFSG.Timmesfeld.ARS.CaseOADeg

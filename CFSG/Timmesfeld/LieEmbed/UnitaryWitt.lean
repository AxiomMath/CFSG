module

public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.Timmesfeld.LieEmbed

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Hilbert90

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem exists_mul_inv_sigma_eq (hF : Nat.card F = (p ^ f) ^ 2) {d : F}
    (hd : unitaryInvolution F p f d * d = 1) :
    ∃ l : F, l ≠ 0 ∧ l * (unitaryInvolution F p f l)⁻¹ = d := by
  classical
  have hd0 : d ≠ 0 := fun h => by rw [h, map_zero, zero_mul] at hd; exact zero_ne_one hd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Fˣ = (p ^ f) ^ 2 - 1 := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 d hd0))
  set q := p ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.out.pos
  have hσ : ∀ x : F, unitaryInvolution F p f x = x ^ q := fun x => unitaryInvolution_apply F p f x
  have hdq : (Units.mk0 d hd0) ^ (q + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, pow_succ, ← hσ, hd]
  rw [← hk, ← _root_.zpow_natCast, ← _root_.zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hord,
    hcard] at hdq
  have hdvd : ((q - 1 : ℕ) : ℤ) ∣ k := by
    have h2 : ((q ^ 2 - 1 : ℕ) : ℤ) = ((q - 1 : ℕ) : ℤ) * ((q + 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q hq1), Nat.cast_sub hq1]
      ring
    rw [h2] at hdq
    exact Int.dvd_of_mul_dvd_mul_right (by positivity : ((q + 1 : ℕ) : ℤ) ≠ 0) hdq
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨((g ^ (-m) : Fˣ) : F), Units.ne_zero _, ?_⟩
  have hgq : unitaryInvolution F p f ((g ^ (-m) : Fˣ) : F) = ((g ^ (-m * q) : Fˣ) : F) := by
    rw [hσ, ← Units.val_pow_eq_pow_val, ← _root_.zpow_natCast, ← _root_.zpow_mul]
  rw [hgq, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← _root_.zpow_neg, ← _root_.zpow_add,
    show -m + -(-m * (q : ℤ)) = k by
      rw [hm, Nat.cast_sub hq1]
      push_cast
      ring,
    hk, Units.val_mk0]

end Hilbert90

section Roots

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem uNil_single (i : Fin n) :
    uNil σ (Pi.single i 1 : Fin n → F) = Matrix.single i (Fin.rev i) 1 := by
  ext a b
  simp only [uNil, vecMulVec_apply, uRow_apply, Matrix.single_apply, Pi.single_apply]
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = Fin.rev a
    · subst hb; simp
    · have h1 : Fin.rev b ≠ a := fun h => hb (by rw [← h, Fin.rev_rev])
      have h2 : Fin.rev a ≠ b := fun h => hb h.symm
      simp [h1, h2]
  · have h1 : i ≠ a := fun h => ha h.symm
    simp [ha, h1]

theorem uTrans_single (i : Fin n) (c : F) :
    uTrans σ (Pi.single i 1 : Fin n → F) c = longRootMatrix i c := by
  rw [uTrans, uNil_single, longRootMatrix, Matrix.smul_single, smul_eq_mul, mul_one]

abbrev c6 (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

abbrev c6' (i : Fin 3) : Fin 6 := ⟨5 - i.val, by omega⟩

theorem rev_ne_self_six' (k : Fin 6) : Fin.rev k ≠ k := by
  revert k
  decide

set_option maxRecDepth 100000 in
theorem weight_six_check : ∀ a b i : Fin 6, b ≠ Fin.rev a →
    weight 6 a - weight 6 b ≠ 2 • weight 6 i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem two_weight_six_check : ∀ a i : Fin 6, 2 • weight 6 a = 2 • weight 6 i → a = i := by
  decide +kernel

theorem isUTransGroup_rootGroup_long (hσ : ∀ c, σ (σ c) = c) (i : Fin 6) {γ : Fin (6 / 2) → ℤ}
    (hγ : toStd 6 γ = 2 • weight 6 i) :
    IsUTransGroup σ (Pi.single i 1) (Unitary.rootGroup σ hσ 6 γ) := by
  have hi : i ≠ Fin.rev i := (rev_ne_self_six' i).symm
  have heq : Unitary.rootGroup σ hσ 6 γ = (longRootHom σ hi).range := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun _ => iSup_le fun hba => iSup_le fun hw =>
            absurd (hw.trans hγ) (weight_six_check a b i hba)
      · exact iSup_le fun a => iSup_le fun ha => iSup_le fun hw => by
          obtain rfl := two_weight_six_check a i (hw.trans hγ)
          exact le_rfl
      · exact iSup_le fun _ => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
          iSup_le fun hk => absurd hk (rev_ne_self_six' k)
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

end Roots

section Witt

variable {F : Type} [Field F] {n : ℕ}

theorem antidiag_mul_apply (C : Matrix (Fin n) (Fin n) F) (x b : Fin n) :
    ((antidiag n : Matrix (Fin n) (Fin n) F) * C) x b = C (Fin.rev x) b := by
  simp only [antidiag, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem conjTr_mul_antidiag_mul_apply (σ : F ≃+* F) (C : Matrix (Fin n) (Fin n) F) (a b : Fin n) :
    (conjTr σ C * (antidiag n : Matrix (Fin n) (Fin n) F) * C) a b =
      uForm σ (fun x => C x a) (fun x => C x b) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, uForm_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [antidiag_mul_apply]
  rfl

theorem antidiag_mul_antidiag : (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n = 1 := by
  ext a b
  rw [antidiag_mul_apply]
  simp only [antidiag, Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · have : b ≠ Fin.rev (Fin.rev a) := by rw [Fin.rev_rev]; exact Ne.symm h
    simp [h, Ne.symm h]

@[expose] def hypCol (P Q : Fin 3 → Fin 6 → F) (c : Fin 6) : Fin 6 → F :=
  if h : c.val < 3 then P ⟨c.val, h⟩ else Q ⟨5 - c.val, by omega⟩

@[expose] def hypMat (P Q : Fin 3 → Fin 6 → F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun a c => hypCol P Q c a

theorem hypMat_mulVec_single (P Q : Fin 3 → Fin 6 → F) (c : Fin 6) :
    hypMat P Q *ᵥ Pi.single c 1 = hypCol P Q c := by
  funext a
  simp [hypMat, mulVec, dotProduct, Pi.single_apply]

theorem diagonal_mulVec_single (d : Fin n → F) (c : Fin n) :
    Matrix.diagonal d *ᵥ Pi.single c 1 = d c • Pi.single c 1 := by
  funext a
  by_cases h : a = c
  · subst h; simp [Matrix.mulVec_single]
  · simp [Matrix.mulVec_single, h]

variable [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem exists_su6_mulVec (hF : Nat.card F = (p ^ f) ^ 2) {P Q : Fin 3 → Fin 6 → F}
    (hpp : ∀ i j, uForm (unitaryInvolution F p f) (P i) (P j) = 0)
    (hqq : ∀ i j, uForm (unitaryInvolution F p f) (Q i) (Q j) = 0)
    (hpq : ∀ i j, uForm (unitaryInvolution F p f) (P i) (Q j) = if i = j then 1 else 0) :
    ∃ (g : SU (unitaryInvolution F p f) 6) (l : F), l ≠ 0 ∧ ∀ i : Fin 3,
      suMat _ 6 g *ᵥ Pi.single (c6 i) 1 = (if i = 0 then l else 1) • P i ∧
      suMat _ 6 g *ᵥ Pi.single (c6' i) 1 =
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
  set C := hypMat P Q with hC
  have hgram : conjTr σ C * antidiag 6 * C = antidiag 6 := by
    ext a b
    rw [conjTr_mul_antidiag_mul_apply]
    fin_cases a <;> fin_cases b <;>
      simp [hC, hypMat, hypCol, hpp, hqq, hpq, hqp, antidiag]
  have hdetJ : (antidiag 6 : Matrix (Fin 6) (Fin 6) F).det ≠ 0 := by
    have := congrArg Matrix.det (antidiag_mul_antidiag (F := F) (n := 6))
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  have hnorm : σ C.det * C.det = 1 := by
    have h := congrArg Matrix.det hgram
    have e : (C.map σ).det = σ C.det := (RingEquiv.map_det σ C).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, e] at h
    have h' : σ C.det * C.det * (antidiag 6 : Matrix (Fin 6) (Fin 6) F).det =
        1 * (antidiag 6 : Matrix (Fin 6) (Fin 6) F).det := by
      linear_combination h
    exact mul_right_cancel₀ hdetJ h'
  have hC0 : C.det ≠ 0 := right_ne_zero_of_mul_eq_one hnorm
  have hd : σ C.det⁻¹ * C.det⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hnorm, inv_one]
  obtain ⟨l, hl0, hl⟩ := exists_mul_inv_sigma_eq hF hd
  rw [← hσdef] at hl
  have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl0
  set d : Fin 6 → F := fun c => if c = 0 then l else if c = 5 then (σ l)⁻¹ else 1 with hddef
  set C' := C * Matrix.diagonal d with hC'
  have hgram' : conjTr σ C' * antidiag 6 * C' = antidiag 6 := by
    have hD : conjTr σ (Matrix.diagonal d) * antidiag 6 * Matrix.diagonal d = antidiag 6 := by
      ext a b
      rw [conjTr_mul_antidiag_mul_apply]
      fin_cases a <;> fin_cases b <;>
        simp [hddef, uForm_eq, Fin.sum_univ_six, Matrix.diagonal_apply, antidiag, hσ, hl0, hσl]
    rw [hC', conjTr_mul, show conjTr σ (Matrix.diagonal d) * conjTr σ C * antidiag 6 *
        (C * Matrix.diagonal d) = conjTr σ (Matrix.diagonal d) *
          (conjTr σ C * antidiag 6 * C) * Matrix.diagonal d by
        simp only [Matrix.mul_assoc], hgram, hD]
  have hdet' : C'.det = 1 := by
    rw [hC', Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_six]
    simp only [hddef]
    norm_num
    rw [hl, mul_inv_cancel₀ hC0]
  let g0 : GL (Fin 6) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero C' (by rw [hdet']; exact one_ne_zero)
  have hg0 : g0 ∈ SU σ 6 := mem_SU.2 ⟨hdet', hgram'⟩
  have hd6 : ∀ i : Fin 3, d (c6 i) = if i = 0 then l else 1 := by
    intro i; fin_cases i <;> rfl
  have hd6' : ∀ i : Fin 3, d (c6' i) = if i = 0 then (σ l)⁻¹ else 1 := by
    intro i; fin_cases i <;> rfl
  have hcol : ∀ i : Fin 3, hypCol P Q (c6 i) = P i := fun i => by
    rw [hypCol, dite_eq_left i.isLt]
  have hcol' : ∀ i : Fin 3, hypCol P Q (c6' i) = Q i := fun i => by
    rw [hypCol, dite_eq_right (show ¬ 5 - i.val < 3 by omega)]
    congr 1
    ext
    show 5 - (5 - i.val) = i.val
    omega
  refine ⟨⟨g0, hg0⟩, l, hl0, fun i => ⟨?_, ?_⟩⟩
  · change C' *ᵥ Pi.single (c6 i) 1 = _
    rw [hC', ← mulVec_mulVec, diagonal_mulVec_single, mulVec_smul, hC, hypMat_mulVec_single,
      hd6, hcol]
  · change C' *ᵥ Pi.single (c6' i) 1 = _
    rw [hC', ← mulVec_mulVec, diagonal_mulVec_single, mulVec_smul, hC, hypMat_mulVec_single,
      hd6', hcol']

end Witt

section Coordinates

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem uForm_single_left (i : Fin n) (v : Fin n → F) :
    uForm σ (Pi.single i 1) v = v (Fin.rev i) := by
  rw [uForm_eq, Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem uForm_single_right (v : Fin n → F) (i : Fin n) :
    uForm σ v (Pi.single i 1) = σ (v (Fin.rev i)) := by
  rw [uForm_eq, Finset.sum_eq_single (Fin.rev i)]
  · simp
  · intro x _ hx
    have : Fin.rev x ≠ i := fun h => hx (by rw [← h, Fin.rev_rev])
    simp [this]
  · simp

theorem uForm_single_self {i : Fin n} (hi : i ≠ Fin.rev i) :
    uForm σ (Pi.single i 1 : Fin n → F) (Pi.single i 1) = 0 := by
  simp [uForm_single_left, Ne.symm hi]

theorem single_one_ne_zero (i : Fin n) : (Pi.single i 1 : Fin n → F) ≠ 0 := fun h => by
  simpa using congrFun h i

theorem IsUTransGroup.smul (hσ : ∀ c, σ (σ c) = c) {v : Fin n → F} {l : F} (hl : l ≠ 0)
    {X : Subgroup (SU σ n)} (h : IsUTransGroup σ v X) : IsUTransGroup σ (l • v) X :=
  IsUTransGroup.of_smul hσ (inv_ne_zero hl) (by rwa [smul_smul, inv_mul_cancel₀ hl, one_smul])

theorem IsUTransGroup.commute_of_mulVec_eq {v : Fin n → F} {X : Subgroup (SU σ n)}
    (h : IsUTransGroup σ v X) {s : SU σ n} (hs : suMat σ n s *ᵥ v = v) :
    ∀ x ∈ X, Commute s x := by
  intro x hx
  obtain ⟨c, -, hc⟩ := (h.1 x).1 hx
  have h1 := suMat_conj_of_eq σ hc s
  rw [hs, ← hc] at h1
  rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
  exact suMat_injective σ h1

theorem rootMatrix_mulVec_apply (i j : Fin n) (c : F) (v : Fin n → F) (x : Fin n) :
    (rootMatrix σ i j c *ᵥ v) x = v x + (if x = i then c * v j else 0) -
      (if x = Fin.rev j then σ c * v (Fin.rev i) else 0) := by
  simp only [rootMatrix, add_mulVec, sub_mulVec, one_mulVec, Pi.add_apply, Pi.sub_apply,
    single_mulVec, Function.update_apply, Pi.zero_apply]

theorem rootMatrix_mulVec_single {i j y : Fin n} (hjy : j ≠ y) (hiy : Fin.rev i ≠ y) (c : F) :
    rootMatrix σ i j c *ᵥ Pi.single y 1 = Pi.single y 1 := by
  funext x
  rw [rootMatrix_mulVec_apply]
  simp [hjy, hiy]

end Coordinates

end CFSG.Timmesfeld.LieEmbed

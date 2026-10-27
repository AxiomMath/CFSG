module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspConjN
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Matrix CFSG.LocalAnalysis.UniquenessCase.UCK.Insp CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem l3_exists_orderOf_eq {H : Type*} [Group H] [Finite H] [IsCyclic H] {N : ℕ}
    (hN : N ∣ Nat.card H) : ∃ g : H, orderOf g = N := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  exact ⟨g ^ (orderOf g / N), orderOf_pow_orderOf_div (by rw [hg]; exact Nat.card_pos.ne')
    (by rw [hg]; exact hN)⟩

theorem l3_coprime_singer {q : ℕ} (hq : q % 3 = 2) : Nat.Coprime (q - 1) (q ^ 2 + q + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have e : (k + 1) ^ 2 + (k + 1) + 1 = 3 + (k + 3) * k := by ring
  rw [Nat.add_sub_cancel, e, Nat.coprime_add_mul_right_right]
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).symm

section SingerL

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

variable (p) in
include p in
theorem l3_exists_model_L (hq : Nat.card F % 3 = 2) :
    ∃ b z : SL(3, F), b ^ 3 = 1 ∧ (∀ c : F, (b : Matrix (Fin 3) (Fin 3) F) ≠ c • 1) ∧
      orderOf z = Nat.card F ^ 2 + Nat.card F + 1 ∧ b * z * b⁻¹ = z ^ Nat.card F := by
  have hcube := cube_roots_trivial hq
  haveI : Fintype F := Fintype.ofFinite F
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hcardL : Nat.card (L3 F p) = Nat.card F ^ 3 := FiniteField.natCard_extension F p 3
  have hdvd : Nat.card F ^ 2 + Nat.card F + 1 ∣ Nat.card (L3 F p)ˣ := by
    rw [Nat.card_units, hcardL]
    refine ⟨Nat.card F - 1, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F = k + 1 := ⟨Nat.card F - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  obtain ⟨w, hw⟩ := l3_exists_orderOf_eq hdvd
  have hwpow : (w : L3 F p) ^ (Nat.card F ^ 2 + Nat.card F + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hw, pow_orderOf_eq_one, Units.val_one]
  set Φ : Matrix (Fin 3) (Fin 3) F := TL F p (frobL F p) with hΦ
  have hΦ3 : Φ * Φ * Φ = 1 := by
    rw [hΦ, ← map_mul, ← map_mul, frobL_cube, map_one]
  have hΦdet : Φ.det = 1 := by
    have h1 : Φ.det ^ 3 = 1 := by
      rw [← Matrix.det_pow, pow_succ, pow_two, hΦ3, Matrix.det_one]
    exact hcube _ h1
  have hΦns : ∀ c : F, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro c hc
    apply frobL_ne_scalar c
    apply (TL F p).injective
    rw [← hΦ, hc, map_smul, map_one]
  set Z : Matrix (Fin 3) (Fin 3) F := TL F p (mulL F p (w : L3 F p)) with hZ
  have hZpow : ∀ n : ℕ, Z ^ n = TL F p (mulL F p ((w : L3 F p) ^ n)) := by
    intro n
    rw [hZ, ← map_pow, ← mulL_pow]
  have hZN : Z ^ (Nat.card F ^ 2 + Nat.card F + 1) = 1 := by
    rw [hZpow, hwpow, mulL_one, map_one]
  have hZdet : Z.det = 1 := by
    have h1 : Z.det ^ (Nat.card F ^ 2 + Nat.card F + 1) = 1 := by
      rw [← Matrix.det_pow, hZN, Matrix.det_one]
    have hne : Z.det ≠ 0 := fun h0 => by
      rw [h0, zero_pow (by positivity)] at h1
      exact zero_ne_one h1
    have h2 : Z.det ^ (Nat.card F - 1) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one _ hne
    exact (pow_eq_one_iff_of_coprime (l3_coprime_singer hq).symm).1 ⟨h1, h2⟩
  have hrel : Φ * Z = Z ^ Nat.card F * Φ := by
    rw [hΦ, hZ, ← map_pow, ← mulL_pow, ← map_mul, ← map_mul, frobL_mulL]
  obtain ⟨b, hb⟩ : ∃ b : SL(3, F), (b : Matrix (Fin 3) (Fin 3) F) = Φ := ⟨⟨Φ, hΦdet⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : SL(3, F), (z : Matrix (Fin 3) (Fin 3) F) = Z := ⟨⟨Z, hZdet⟩, rfl⟩
  refine ⟨b, z, ?_, by rw [hb]; exact hΦns, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hb, Matrix.SpecialLinearGroup.coe_one, pow_succ,
      pow_two, hΦ3]
  · rw [← hw]
    refine orderOf_eq_orderOf_iff.2 fun n => ?_
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
    constructor
    · intro h
      have h' : (z : Matrix (Fin 3) (Fin 3) F) ^ n = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
      rw [hz, hZpow] at h'
      rw [← mulL_eq_one_iff (K := F) (p := p)]
      apply (TL F p).injective
      rw [h', map_one]
    · intro h
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hz, hZpow, h, mulL_one, map_one,
        Matrix.SpecialLinearGroup.coe_one]
  · rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, hb, hz]
    exact hrel

theorem l3_exists_singer_L {f : ℕ} (hf : 1 ≤ f) (hpf : Nat.card F = p ^ f)
    (hq : Nat.card F % 3 = 2) {d : SL(3, F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ z : SL(3, F), orderOf z = Nat.card F ^ 2 + Nat.card F + 1 ∧ d * z * d⁻¹ = z ^ Nat.card F := by
  have hcube := cube_roots_trivial hq
  have h3 := three_ne_zero_of_card_mod hf hpf hq
  have hω := no_root_of_cube_trivial h3 hcube
  obtain ⟨b, z₀, hb3, hbns, hz₀, hbz⟩ := l3_exists_model_L p hq
  have hmul3 : ∀ x : SL(3, F), x ^ 3 = 1 →
      (x : Matrix (Fin 3) (Fin 3) F) * x * x = 1 := by
    intro x hx
    have := congrArg (fun y : SL(3, F) => (y : Matrix (Fin 3) (Fin 3) F)) hx
    simpa [pow_succ] using this
  have hdns : ∀ c : F, (d : Matrix (Fin 3) (Fin 3) F) ≠ c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro c hc
    have h1 := hmul3 d hd3
    rw [hc] at h1
    have hc3 : c ^ 3 = 1 := by
      have h2 := congrFun (congrFun h1 0) 0
      have h2' : c * (c * c) = 1 := by
        simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
      linear_combination h2'
    have hc1 : c = 1 := hcube c hc3
    apply hd1
    apply Subtype.ext
    rw [hc, hc1, one_smul]
    rfl
  obtain ⟨Q, hQ⟩ := exists_conj3 h3 hω (b : Matrix (Fin 3) (Fin 3) F) (d : Matrix (Fin 3) (Fin 3) F)
    (hmul3 b hb3) b.2 hbns (hmul3 d hd3) d.2 hdns
  have hcb : conjSLnEquiv Q b = d := conjSLnEquiv_eq_of_mul_eq Q hQ
  refine ⟨conjSLnEquiv Q z₀, by rw [MulEquiv.orderOf_eq, hz₀], ?_⟩
  rw [← hcb, ← map_inv, ← map_mul, ← map_mul, hbz, map_pow]

end SingerL

section SingerU

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem l3_exists_model_U (σ : F ≃+* F) (hσ : ∀ c : F, σ c = c ^ p ^ f)
    (hK : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) :
    ∃ (S Φ : Matrix (Fin 3) (Fin 3) F) (Z : GL (Fin 3) F), conjTr σ S = S ∧ S.det ≠ 0 ∧
      conjTr σ Φ * S * Φ = S ∧ Φ * Φ * Φ = 1 ∧ Φ.det = 1 ∧
      (∀ c : F, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) ∧
      conjTr σ (Z : Matrix (Fin 3) (Fin 3) F) * S * Z = S ∧
      orderOf Z = (p ^ f) ^ 2 - p ^ f + 1 ∧ (Z : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      Φ * Z = (Z : Matrix (Fin 3) (Fin 3) F) ^ Nat.card F * Φ := by
  set Q := p ^ f with hQdef
  have hQ2 : 2 ≤ Q := two_le_of_card_eq_sq hK
  set N := Q ^ 2 - Q + 1 with hN
  have hβK := betaL_algebraMap σ hσ hK
  have hββ := betaL_betaL hK
  set β : L3 F p ≃+* L3 F p := betaL F p f with hβdef
  have hcardL : Nat.card (L3 F p) = (Q ^ 2) ^ 3 := by
    rw [FiniteField.natCard_extension, hK]
  have hN3 : Q ^ 3 + 1 = (Q + 1) * N := by
    obtain ⟨k, hk⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
    have e : Q ^ 2 - Q + 1 = k ^ 2 + k + 1 := by
      have : Q ^ 2 = k ^ 2 + k + Q := by rw [hk]; ring
      omega
    rw [hN, e, hk]
    ring
  have hdvd : N ∣ Nat.card (L3 F p)ˣ := by
    rw [Nat.card_units, hcardL]
    have e : (Q ^ 2) ^ 3 - 1 = (Q ^ 3 - 1) * (Q ^ 3 + 1) := by
      have h1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (Q ^ 2) ^ 3 := Nat.one_le_pow _ _ (by positivity)
      zify [h1, h2]
      ring
    rw [e, hN3]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  obtain ⟨w, hw⟩ := l3_exists_orderOf_eq hdvd
  have hwpow : (w : L3 F p) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hw, pow_orderOf_eq_one, Units.val_one]
  have hβw : β (w : L3 F p) * (w : L3 F p) = 1 := by
    rw [hβdef, betaL_apply, ← pow_succ, hN3, pow_mul', hwpow, one_pow]
  have hΦiso : ∀ x y : L3 F p, hermForm σ β hβK (frobL F p x) (frobL F p y) =
      hermForm σ β hβK x y := by
    intro x y
    rw [hermForm_apply, hermForm_apply, frobL_apply, frobL_apply, map_pow, ← mul_pow]
    have := Algebra.trace_eq_of_algEquiv (FiniteField.Extension.frob F p 3) (β x * y)
    rw [FiniteField.Extension.frob_apply] at this
    exact this
  have hZiso : ∀ x y : L3 F p, hermForm σ β hβK (mulL F p (w : L3 F p) x)
      (mulL F p (w : L3 F p) y) = hermForm σ β hβK x y := by
    intro x y
    have hx : ∀ z : L3 F p, mulL F p (w : L3 F p) z = (w : L3 F p) * z := fun z => rfl
    rw [hx, hx, hermForm_apply, hermForm_apply, map_mul β]
    calc Algebra.trace F (L3 F p) (β (w : L3 F p) * β x * ((w : L3 F p) * y))
        = Algebra.trace F (L3 F p) ((β (w : L3 F p) * (w : L3 F p)) * (β x * y)) := by
          congr 1
          ring
      _ = Algebra.trace F (L3 F p) (β x * y) := by rw [hβw, one_mul]
  set S : Matrix (Fin 3) (Fin 3) F := gram σ hβK (bL F p) with hS
  have hSherm : conjTr σ S = S := conjTr_gram σ hβK (bL F p) hββ
  have hSdet : S.det ≠ 0 := det_gram_ne_zero σ hβK (bL F p) hββ
  set Φ : Matrix (Fin 3) (Fin 3) F := TL F p (frobL F p) with hΦ
  set Z : Matrix (Fin 3) (Fin 3) F := TL F p (mulL F p (w : L3 F p)) with hZ
  have hΦS : conjTr σ Φ * S * Φ = S := conjTr_mul_gram_mul σ hβK (bL F p) (frobL F p) hΦiso
  have hZS : conjTr σ Z * S * Z = S :=
    conjTr_mul_gram_mul σ hβK (bL F p) (mulL F p (w : L3 F p)) hZiso
  have hΦ3 : Φ * Φ * Φ = 1 := by
    rw [hΦ, ← map_mul, ← map_mul, frobL_cube, map_one]
  have hΦns : ∀ c : F, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro c hc
    apply frobL_ne_scalar c
    apply (TL F p).injective
    rw [← hΦ, hc, map_smul, map_one]
  have hΦdet : Φ.det = 1 := by
    have h1 : Φ.det ^ 3 = 1 := by
      rw [← Matrix.det_pow, pow_succ, pow_two, hΦ3, Matrix.det_one]
    have hcop : Nat.Coprime 3 (Q + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    exact det_eq_one_of_isometry σ hSdet hΦS hσ h1 hcop
  have hZpow : ∀ n : ℕ, Z ^ n = TL F p (mulL F p ((w : L3 F p) ^ n)) := by
    intro n
    rw [hZ, ← map_pow, ← mulL_pow]
  have hZN : Z ^ N = 1 := by
    rw [hZpow, hwpow, mulL_one, map_one]
  have hZdet : Z.det = 1 := by
    have h1 : Z.det ^ N = 1 := by rw [← Matrix.det_pow, hZN, Matrix.det_one]
    have hcop : Nat.Coprime N (Q + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, Q = k + 2 := ⟨Q - 2, by omega⟩
      have e : N = 3 + k * (Q + 1) := by
        have : Q ^ 2 = k * (Q + 1) + Q + 2 := by rw [hk]; ring
        omega
      rw [e, Nat.coprime_comm, Nat.coprime_add_mul_right_right]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)).symm
    exact det_eq_one_of_isometry σ hSdet hZS hσ h1 hcop
  have hrel : Φ * Z = Z ^ Nat.card F * Φ := by
    rw [hΦ, hZ, ← map_pow, ← mulL_pow, ← map_mul, ← map_mul, frobL_mulL]
  let Zg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Z (by rw [hZdet]; exact one_ne_zero)
  have hZg : (Zg : Matrix (Fin 3) (Fin 3) F) = Z := rfl
  have hord : orderOf Zg = N := by
    rw [← hw]
    refine orderOf_eq_orderOf_iff.2 fun n => ?_
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, hZg, Units.val_one, hZpow, Units.ext_iff,
      Units.val_pow_eq_pow_val, Units.val_one]
    constructor
    · intro h
      rw [← mulL_eq_one_iff (K := F) (p := p)]
      apply (TL F p).injective
      rw [h, map_one]
    · intro h
      rw [h, mulL_one, map_one]
  exact ⟨S, Φ, Zg, hSherm, hSdet, hΦS, hΦ3, hΦdet, hΦns, hZS, hord, hZdet, hrel⟩

theorem l3_exists_singer_U (σ : F ≃+* F) (hσ : ∀ c : F, σ c = c ^ p ^ f)
    (hσσ : ∀ c : F, σ (σ c) = c) (hf : 1 ≤ f) (hK : Nat.card F = (p ^ f) ^ 2)
    (hq : p ^ f % 3 = 1) {d : SU σ 3} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ z : SU σ 3, orderOf z = (p ^ f) ^ 2 - p ^ f + 1 ∧ d * z * d⁻¹ = z ^ Nat.card F := by
  obtain ⟨ω, hω, hωQ⟩ := exists_cube_root (F := F) hK hq
  have hσω : σ ω = ω := by rw [hσ]; exact hωQ
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_pow_mod_one hf hq
  have hnorm : ∀ c : F, σ c = c → c ≠ 0 → ∃ β : F, σ β * β = c := by
    intro c hc hc0
    obtain ⟨β, hβ⟩ := exists_norm_eq hK (by rw [← hσ]; exact hc) hc0
    exact ⟨β, by rw [hσ]; exact hβ⟩
  obtain ⟨S₀, Φ, Z₀g, hS₀h, hS₀d, hΦS, hΦ3, hΦdet, hΦns, hZS, hZord, hZdet, hrel⟩ :=
    l3_exists_model_U σ hσ hK hq
  obtain ⟨hMcube, hMdet, hMiso, hMns⟩ := su_cube_facts σ hσ hq hd3 hd1
  obtain ⟨B₂, hB₂det, hB₂J, hMB₂⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm (antidiag 3)
    (conjTr_antidiag σ 3) det_antidiag_three _ hMiso hMcube hMdet hMns
  obtain ⟨B₁, hB₁det, hB₁S, hΦB₁⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm S₀ hS₀h hS₀d Φ hΦS
    hΦ3 hΦdet hΦns
  obtain ⟨G₁, hG₁⟩ : ∃ G : GL (Fin 3) F, (G : Matrix (Fin 3) (Fin 3) F) = B₁ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B₁ hB₁det, rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G : GL (Fin 3) F, (G : Matrix (Fin 3) (Fin 3) F) = B₂ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B₂ hB₂det, rfl⟩
  obtain ⟨Φg, hΦg⟩ : ∃ G : GL (Fin 3) F, (G : Matrix (Fin 3) (Fin 3) F) = Φ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Φ (by rw [hΦdet]; exact one_ne_zero), rfl⟩
  obtain ⟨B₁i, hB₁i⟩ : ∃ X : Matrix (Fin 3) (Fin 3) F,
      X = ((G₁⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨_, rfl⟩
  have hB₁B₁i : B₁ * B₁i = 1 := by rw [hB₁i, ← hG₁]; exact Units.mul_inv G₁
  have hB₁iB₁ : B₁i * B₁ = 1 := by rw [hB₁i, ← hG₁]; exact Units.inv_mul G₁
  obtain ⟨Pg, hPg⟩ : ∃ P : GL (Fin 3) F, P = G₂ * G₁⁻¹ := ⟨_, rfl⟩
  have hPm : (Pg : Matrix (Fin 3) (Fin 3) F) = B₂ * B₁i := by
    rw [hPg, Units.val_mul, hG₂, hB₁i]
  have hmat : ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (B₂ * B₁i) =
      (B₂ * B₁i) * Φ := by
    calc ((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (B₂ * B₁i)
        = (((d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * B₂) * B₁i :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (B₂ * diagonal ![ω, 1, ω ^ 2]) * B₁i := by rw [hMB₂]
      _ = B₂ * (B₁i * (B₁ * diagonal ![ω, 1, ω ^ 2])) * B₁i := by
          rw [← Matrix.mul_assoc B₁i, hB₁iB₁, Matrix.one_mul]
      _ = B₂ * (B₁i * (Φ * B₁)) * B₁i := by rw [hΦB₁]
      _ = (B₂ * B₁i) * Φ * (B₁ * B₁i) := by simp only [Matrix.mul_assoc]
      _ = (B₂ * B₁i) * Φ := by rw [hB₁B₁i, Matrix.mul_one]
  have hdP : (d : GL (Fin 3) F) * Pg = Pg * Φg := by
    apply Units.ext
    rw [Units.val_mul (d : GL (Fin 3) F) Pg, Units.val_mul Pg Φg, hPm, hΦg]
    exact hmat
  have hcj : (d : GL (Fin 3) F) = Pg * Φg * Pg⁻¹ := eq_mul_inv_of_mul_eq hdP
  have hΦZ : Φg * Z₀g = Z₀g ^ Nat.card F * Φg := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hΦg]
    exact hrel
  have hΦZ' : Φg * Z₀g * Φg⁻¹ = Z₀g ^ Nat.card F := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hΦZ
  obtain ⟨Zg, hZg⟩ : ∃ Z : GL (Fin 3) F, Z = Pg * Z₀g * Pg⁻¹ := ⟨_, rfl⟩
  have hdZ : (d : GL (Fin 3) F) * Zg * (d : GL (Fin 3) F)⁻¹ = Zg ^ Nat.card F := by
    have h1 : (d : GL (Fin 3) F) * Zg * (d : GL (Fin 3) F)⁻¹ =
        Pg * (Φg * Z₀g * Φg⁻¹) * Pg⁻¹ := by
      rw [hcj, hZg]
      group
    rw [h1, hΦZ', hZg, conj_pow]
  have hZgmat : (Zg : Matrix (Fin 3) (Fin 3) F) =
      (B₂ * B₁i) * (Z₀g : Matrix (Fin 3) (Fin 3) F) *
        ((Pg⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hZg, Units.val_mul, Units.val_mul Pg, hPm]
  have hPPi : (B₂ * B₁i) * ((Pg⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← hPm]
    exact Units.mul_inv Pg
  have hKey : conjTr σ (B₂ * B₁i) * antidiag 3 * (B₂ * B₁i) = S₀ :=
    key_isometry σ hB₁B₁i hB₁S hB₂J
  have hZgmem : Zg ∈ SU σ 3 := by
    rw [mem_SU]
    refine ⟨?_, ?_⟩
    · rw [hZgmat, ← hPm, Matrix.det_mul, Matrix.det_mul, hZdet, mul_one, ← Matrix.det_mul,
        Units.mul_inv, Matrix.det_one]
    · rw [hZgmat]
      exact conj_isometry σ hPPi hKey hZS
  obtain ⟨z, hz⟩ : ∃ z : SU σ 3, (z : GL (Fin 3) F) = Zg := ⟨⟨Zg, hZgmem⟩, rfl⟩
  refine ⟨z, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe, hz, hZg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hZord]
  · apply Subtype.ext
    show (d : GL (Fin 3) F) * (z : GL (Fin 3) F) * (d : GL (Fin 3) F)⁻¹ =
      (z : GL (Fin 3) F) ^ Nat.card F
    rw [hz]
    exact hdZ

end SingerU

end CFSG.LocalAnalysis.UniquenessCase.UCK

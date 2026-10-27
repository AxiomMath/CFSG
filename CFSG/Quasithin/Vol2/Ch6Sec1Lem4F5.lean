module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem ringEquiv_apply_eq_pow614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    (x : F) : τ x = x ^ p := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let τ' : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := τ) (fun a => by
      have h : (τ.toRingHom.comp (algebraMap (ZMod p) F)) = algebraMap (ZMod p) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h a)
  have hfin : Module.finrank (ZMod p) F = 2 := by
    have := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [hFc, ZMod.card] at this
    exact (Nat.pow_right_injective hp.out.two_le this).symm
  obtain ⟨⟨k, hk⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 τ'
  simp only at hn
  rw [hfin] at hk
  interval_cases k
  · exfalso
    apply hτ
    ext y
    have := congrArg (fun φ : F ≃ₐ[ZMod p] F => φ y) hn
    simp only [pow_zero, AlgEquiv.one_apply] at this
    exact this.symm
  · have := congrArg (fun φ : F ≃ₐ[ZMod p] F => φ x) hn
    simp only [pow_one, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] at this
    exact this.symm

@[expose] noncomputable def fixedField614 (τ : F ≃+* F) : Subfield F :=
  FixedPoints.subfield (Subgroup.zpowers τ) F

omit [Finite F] hp in
theorem mem_fixedField614 {τ : F ≃+* F} {x : F} : x ∈ fixedField614 τ ↔ τ x = x := by
  constructor
  · intro h
    exact h ⟨τ, Subgroup.mem_zpowers τ⟩
  · intro h
    rintro ⟨m, hm⟩
    have hst : τ ∈ MulAction.stabilizer (F ≃+* F) x := h
    have : m ∈ MulAction.stabilizer (F ≃+* F) x :=
      (Subgroup.zpowers_le.mpr hst) hm
    exact this

theorem ringEquiv_sq_eq_one614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1) :
    τ ^ 2 = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  ext x
  show τ (τ x) = x
  rw [ringEquiv_apply_eq_pow614 hF hτ, ringEquiv_apply_eq_pow614 hF hτ, ← pow_mul, ← pow_two,
    ← hFc, FiniteField.pow_card]

theorem card_fixedField614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1) :
    Nat.card (fixedField614 τ) = p := by
  have h := CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F τ
  have hord : orderOf τ = 2 := orderOf_eq_prime (ringEquiv_sq_eq_one614 hF hτ) hτ
  rw [hord, hF] at h
  exact (Nat.pow_left_injective two_ne_zero h).symm

omit hp in
theorem exists_generator614 (hF : Nat.card F = p ^ 2) :
    ∃ g : Fˣ, (∀ x : Fˣ, x ∈ Subgroup.zpowers g) ∧ orderOf g = p ^ 2 - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, hg, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]

theorem exists_mul_apply_eq614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    {l : F} (hl0 : l ≠ 0) (hl : τ l = l) : ∃ μ : F, μ ≠ 0 ∧ μ * τ μ = l := by
  classical
  obtain ⟨g, hg, hog⟩ := exists_generator614 hF
  have hp1 : 2 ≤ p := hp.out.two_le
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 l hl0))
  have hlp : (Units.mk0 l hl0) ^ (p - 1) = 1 := by
    apply Units.ext
    have h1 : l ^ p = l := by rw [← ringEquiv_apply_eq_pow614 hF hτ, hl]
    have h2 : l ^ (p - 1) * l = l := by rw [← pow_succ, Nat.sub_add_cancel (by omega), h1]
    simpa using mul_right_cancel₀ hl0 (h2.trans (one_mul l).symm)
  rw [← hm, ← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, hog] at hlp
  have hdvd : ((p ^ 2 - 1 : ℕ) : ℤ) ∣ m * ((p - 1 : ℕ) : ℤ) := by
    simpa using (Int.modEq_zero_iff_dvd.mp hlp)
  have hsplit : ((p ^ 2 - 1 : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ) * ((p + 1 : ℕ) : ℤ) := by
    have : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [this]
    push_cast
    ring
  rw [hsplit, mul_comm m] at hdvd
  have hne : ((p - 1 : ℕ) : ℤ) ≠ 0 := by
    have : 1 ≤ p - 1 := by omega
    exact_mod_cast (by omega : p - 1 ≠ 0)
  obtain ⟨j, hj⟩ := (Int.dvd_of_mul_dvd_mul_left hne hdvd)
  refine ⟨((g ^ j : Fˣ) : F), Units.ne_zero _, ?_⟩
  rw [ringEquiv_apply_eq_pow614 hF hτ, ← pow_succ', ← Units.val_pow_eq_pow_val]
  have e : (g ^ j) ^ (p + 1) = Units.mk0 l hl0 := by
    rw [← hm, hj, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [e]
  rfl

theorem exists_mul_apply_eq_self614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    {l : F} (hl0 : l ≠ 0) (hl : l * τ l = 1) : ∃ μ : F, μ ≠ 0 ∧ l * τ μ = μ := by
  classical
  obtain ⟨g, hg, hog⟩ := exists_generator614 hF
  have hp1 : 2 ≤ p := hp.out.two_le
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 l hl0))
  have hlp : (Units.mk0 l hl0) ^ (p + 1) = 1 := by
    apply Units.ext
    rw [ringEquiv_apply_eq_pow614 hF hτ] at hl
    simpa [pow_succ'] using hl
  rw [← hm, ← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, hog] at hlp
  have hdvd : ((p ^ 2 - 1 : ℕ) : ℤ) ∣ m * ((p + 1 : ℕ) : ℤ) := by
    simpa using (Int.modEq_zero_iff_dvd.mp hlp)
  have hsplit : ((p ^ 2 - 1 : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) := by
    have : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
    rw [this]
    push_cast
    ring
  rw [hsplit, mul_comm m] at hdvd
  have hne : ((p + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  obtain ⟨j, hj⟩ := (Int.dvd_of_mul_dvd_mul_left hne hdvd)
  refine ⟨((g ^ (-j) : Fˣ) : F), Units.ne_zero _, ?_⟩
  rw [ringEquiv_apply_eq_pow614 hF hτ, ← Units.val_pow_eq_pow_val]
  have e : Units.mk0 l hl0 * (g ^ (-j)) ^ p = g ^ (-j) := by
    rw [← hm, hj, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 1
    have h1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      have : 1 ≤ p := by omega
      push_cast [this]
      ring
    rw [h1]
    ring
  have := congrArg Units.val e
  simpa using this

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem isSquare_of_eq614 (hF : Nat.card F = p ^ 2) (hp2 : p ≠ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    {δ c Δ : F} (hδ : δ ≠ 0) (hΔ : Δ ^ ((p - 1) / 2) = -1) (hc : c * τ c * Δ = -1)
    (hrel : δ = c ^ 2 * Δ * τ δ) : IsSquare δ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨s, hs⟩ := hodd
  have hs' : (p - 1) / 2 = s := by omega
  rw [hs'] at hΔ
  rw [ringEquiv_apply_eq_pow614 hF hτ] at hc hrel
  have h1 : c ^ 2 * Δ * δ ^ (2 * s) = 1 := by
    have e : δ * (c ^ 2 * Δ * δ ^ (2 * s)) = δ * 1 := by
      rw [mul_one]
      conv_rhs => rw [hrel]
      rw [hs, pow_succ]
      ring
    exact mul_left_cancel₀ hδ e
  have h2 : c ^ (2 * s + 2) * Δ = -1 := by
    rw [← hc, hs]
    ring
  have h3 : (c ^ 2 * Δ) ^ (s + 1) = 1 := by
    calc (c ^ 2 * Δ) ^ (s + 1) = (c ^ (2 * s + 2) * Δ) * Δ ^ s := by ring
      _ = 1 := by rw [h2, hΔ]; ring
  have h4 : (δ ^ (2 * s)) ^ (s + 1) = 1 := by
    have := congrArg (· ^ (s + 1)) h1
    simp only [one_pow] at this
    rwa [mul_pow, h3, one_mul] at this
  have hringChar : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  rw [FiniteField.isSquare_iff hringChar hδ, hFc, hs]
  have e : (2 * s + 1) ^ 2 / 2 = 2 * s * (s + 1) := by
    have : (2 * s + 1) ^ 2 = 2 * (2 * s * (s + 1)) + 1 := by ring
    omega
  rw [e, pow_mul]
  exact h4

theorem exists_det_ne_zero614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    (N : Matrix (Fin 2) (Fin 2) F) (hN : N.det ≠ 0) :
    ∃ θ : F, θ ≠ 0 ∧ (θ • (1 : Matrix (Fin 2) (Fin 2) F) + τ θ • N).det ≠ 0 := by
  classical
  obtain ⟨g, -, hog⟩ := exists_generator614 hF
  have hp1 : 2 ≤ p := hp.out.two_le
  set t := N 0 0 + N 1 1
  set d := N.det
  have hdet : ∀ θ : F, θ ≠ 0 → (θ • (1 : Matrix (Fin 2) (Fin 2) F) + τ θ • N).det =
      θ ^ 2 * (1 + θ ^ (p - 1) * t + (θ ^ (p - 1)) ^ 2 * d) := by
    intro θ hθ
    have hτθ : τ θ = θ * θ ^ (p - 1) := by
      rw [ringEquiv_apply_eq_pow614 hF hτ, ← pow_succ', Nat.sub_add_cancel (by omega)]
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    rw [hτθ, show d = N 0 0 * N 1 1 - N 0 1 * N 1 0 from Matrix.det_fin_two N]
    ring
  set v : F := (g : F) ^ (p - 1)
  have hv0 : v ≠ 0 := pow_ne_zero _ (Units.ne_zero g)
  have hv1 : v ^ 2 ≠ 1 ∧ v ≠ 1 := by
    have key : ∀ k : ℕ, k = 1 ∨ k = 2 → v ^ k ≠ 1 := by
      intro k hk h
      have h1 : g ^ ((p - 1) * k) = 1 := by
        apply Units.ext
        rw [pow_mul]
        simpa [v] using h
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hog] at h2
      have hsplit : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        rw [mul_comm, ← Nat.sq_sub_sq, one_pow]
      rw [hsplit] at h2
      have h3 : p + 1 ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
      have := Nat.le_of_dvd (by omega) h3
      omega
    exact ⟨key 2 (Or.inr rfl), by simpa using key 1 (Or.inl rfl)⟩
  by_contra hall
  push Not at hall
  have hQ : ∀ θ : F, θ ≠ 0 → 1 + θ ^ (p - 1) * t + (θ ^ (p - 1)) ^ 2 * d = 0 := by
    intro θ hθ
    have := hall θ hθ
    rw [hdet θ hθ] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hθ)
  have e0 := hQ 1 one_ne_zero
  have e1 := hQ (g : F) (Units.ne_zero g)
  have e2 := hQ ((g : F) ^ 2) (pow_ne_zero _ (Units.ne_zero g))
  simp only [one_pow, one_mul] at e0
  have e2' : 1 + v ^ 2 * t + (v ^ 2) ^ 2 * d = 0 := by
    rw [← e2]
    simp only [v]
    ring
  have e1' : 1 + v * t + v ^ 2 * d = 0 := e1
  have f1 : (v - 1) * (t + d * (v + 1)) = 0 := by linear_combination e1' - e0
  have f2 : (v ^ 2 - 1) * (t + d * (v ^ 2 + 1)) = 0 := by linear_combination e2' - e0
  have g1 : t + d * (v + 1) = 0 :=
    (mul_eq_zero.mp f1).resolve_left (sub_ne_zero.mpr hv1.2)
  have g2 : t + d * (v ^ 2 + 1) = 0 :=
    (mul_eq_zero.mp f2).resolve_left (sub_ne_zero.mpr hv1.1)
  have g3 : d * (v * (v - 1)) = 0 := by linear_combination g2 - g1
  rcases mul_eq_zero.mp g3 with h | h
  · exact hN h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hv0 h'
    · exact hv1.2 (sub_eq_zero.mp h')

omit [Finite F] hp in
theorem pgl2FieldAut_mk614 (τ : F ≃+* F) (A : GL (Fin 2) F) :
    pgl2FieldAut F τ (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map τ.toRingHom A) := by
  rw [pgl2FieldAut_apply]
  exact pgl2RingEquiv_mk τ A

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

omit [Finite F] in
theorem coe_glMap614 (f : F →+* F) (A : GL (Fin 2) F) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (A : Matrix (Fin 2) (Fin 2) F).map f := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply f i j A

omit [Finite F] in
theorem mk_eq_mk_of_smul614 {A B : GL (Fin 2) F} {c : F} (hc : c ≠ 0)
    (h : (B : Matrix (Fin 2) (Fin 2) F) = c • (A : Matrix (Fin 2) (Fin 2) F)) :
    Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B := by
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, h]
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

omit [Finite F] in
theorem inl_mul_inr_mul_inl_inv614 (k : PGL2 F) (τ : F ≃+* F) :
    (SemidirectProduct.inl k : PGammaL2 F) * SemidirectProduct.inr τ *
        (SemidirectProduct.inl k)⁻¹ =
      SemidirectProduct.inl (k * pgl2FieldAut F τ k⁻¹) * SemidirectProduct.inr τ := by
  rw [map_mul, SemidirectProduct.inl_aut]
  simp only [map_inv]
  group

omit [Finite F] in
theorem inl_mul_mul_inl_inv614 (b a : PGL2 F) (τ : F ≃+* F) :
    (SemidirectProduct.inl b : PGammaL2 F) * (SemidirectProduct.inl a * SemidirectProduct.inr τ) *
        (SemidirectProduct.inl b)⁻¹ =
      SemidirectProduct.inl (b * a * pgl2FieldAut F τ b⁻¹) * SemidirectProduct.inr τ := by
  rw [map_mul, map_mul, SemidirectProduct.inl_aut]
  simp only [map_inv]
  group

theorem exists_twisted_coboundary614 (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    (N : Matrix (Fin 2) (Fin 2) F) (hN : N * N.map τ = 1) :
    ∃ B : Matrix (Fin 2) (Fin 2) F, B.det ≠ 0 ∧ N * B.map τ = B := by
  have hNdet : N.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hN
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨θ, -, hθ⟩ := exists_det_ne_zero614 hF hτ N hNdet
  refine ⟨θ • 1 + τ θ • N, hθ, ?_⟩
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun σ : F ≃+* F => σ x) (ringEquiv_sq_eq_one614 hF hτ)
    simpa [pow_two] using this
  have hmap : (θ • (1 : Matrix (Fin 2) (Fin 2) F) + τ θ • N).map τ =
      τ θ • (1 : Matrix (Fin 2) (Fin 2) F) + θ • N.map τ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hττ]
  rw [hmap, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hN, Matrix.mul_one, add_comm]

theorem exists_conj_eq_inr614 (hF : Nat.card F = p ^ 2) (f : PGammaL2 F) (hf2 : f ^ 2 = 1)
    (hfP : f ∉ pGammaL2PGLRange F) :
    ∃ b : PGL2 F, (SemidirectProduct.inl b : PGammaL2 F) * f * (SemidirectProduct.inl b)⁻¹ =
      SemidirectProduct.inr f.right := by
  classical
  set τ := f.right with hτdef
  set a := f.left with hadef
  have hf : f = SemidirectProduct.inl a * SemidirectProduct.inr τ :=
    (SemidirectProduct.inl_left_mul_inr_right f).symm
  have hτ : τ ≠ 1 := by
    intro h
    apply hfP
    refine ⟨a, ?_⟩
    rw [hf, h, map_one, mul_one]
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun σ : F ≃+* F => σ x) (ringEquiv_sq_eq_one614 hF hτ)
    simpa [pow_two] using this
  have ha : a * pgl2FieldAut F τ a = 1 := by
    have := congrArg SemidirectProduct.left hf2
    rw [pow_two, SemidirectProduct.mul_left] at this
    exact this
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective a
  rw [← hA] at ha hf
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hM
  rw [pgl2FieldAut_mk614, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at ha
  obtain ⟨l, hl⟩ := ha
  have hsmul : ∀ (c : F) (X : Matrix (Fin 2) (Fin 2) F), (c • X).map τ = τ c • X.map τ := by
    intro c X
    ext i j
    simp
  have hMl : M * M.map τ = (l : F) • 1 := by
    have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hl
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, coe_glMap614] at h
    have h' : M * M.map τ = Matrix.scalar (Fin 2) (l : F) := by rw [hM]; exact h.symm
    rw [h']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hMdet : M.det ≠ 0 := by
    rw [hM, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hlτ : τ (l : F) = l := by
    have h1 : M.map τ * M = (τ (l : F)) • 1 := by
      have := congrArg (fun X => X.map τ) hMl
      simp only [Matrix.map_mul] at this
      have e : (M.map τ).map τ = M := by ext i j; simp [hττ]
      rw [e] at this
      rw [this]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h2 : M.map τ * M = (l : F) • 1 := by
      have hinv : M.map τ = (l : F) • M⁻¹ := by
        have := congrArg (fun X => M⁻¹ * X) hMl
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hMdet),
          Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
        exact this
      rw [hinv, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hMdet)]
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 0) (h1.symm.trans h2)
    simpa using this
  obtain ⟨μ, hμ0, hμ⟩ := exists_mul_apply_eq614 hF hτ (l := (l : F)⁻¹)
    (inv_ne_zero (Units.ne_zero l)) (by rw [map_inv₀, hlτ])
  set N := μ • M with hN
  have hNN : N * N.map τ = 1 := by
    rw [hN, hsmul, Matrix.smul_mul, Matrix.mul_smul, hMl, smul_smul, smul_smul, hμ,
      inv_mul_cancel₀ (Units.ne_zero l), one_smul]
  obtain ⟨B, hBdet, hNB⟩ := exists_twisted_coboundary614 hF hτ N hNN
  set Bg := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  have hNdet : N.det ≠ 0 := by
    rw [hN, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hμ0) hMdet
  set Ng := Matrix.GeneralLinearGroup.mkOfDetNeZero N hNdet
  have hANg : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk Ng :=
    mk_eq_mk_of_smul614 hμ0 rfl
  have hNgB : Ng * Matrix.GeneralLinearGroup.map τ.toRingHom Bg = Bg := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul, coe_glMap614]
    exact congrFun (congrFun hNB i) j
  refine ⟨(Matrix.ProjGenLinGroup.mk Bg)⁻¹, ?_⟩
  rw [hf, inl_mul_mul_inl_inv614, inv_inv, pgl2FieldAut_mk614, hANg, mul_assoc, ← map_mul, hNgB,
    inv_mul_cancel, map_one, one_mul]

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

noncomputable abbrev iotaR614 (R : Subfield F) : PGL2 R →* PGL2 F :=
  Matrix.ProjGenLinGroup.map R.subtype

omit [Finite F] in
theorem iotaR614_injective (R : Subfield F) : Function.Injective (iotaR614 R) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  rw [MonoidHom.mem_ker, iotaR614, Matrix.ProjGenLinGroup.map_mk,
    Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
  obtain ⟨u, hu⟩ := hx
  have hent : ∀ i j, (R.subtype (A i j) : F) = (Matrix.scalar (Fin 2) (u : F)) i j := by
    intro i j
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.map_apply] at this
    exact this.symm
  have h01 : A 0 1 = 0 := by
    have := hent 0 1
    simp [Matrix.scalar_apply] at this
    exact_mod_cast this
  have h10 : A 1 0 = 0 := by
    have := hent 1 0
    simp [Matrix.scalar_apply] at this
    exact_mod_cast this
  have h00 : (A 0 0 : F) = u := by simpa [Matrix.scalar_apply] using hent 0 0
  have h11 : (A 1 1 : F) = u := by simpa [Matrix.scalar_apply] using hent 1 1
  have hA : A 1 1 = A 0 0 := Subtype.ext (h11.trans h00.symm)
  have hdet : (A : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have ha0 : A 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_fin_two, h, h01]
    ring
  rw [Subgroup.mem_bot, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 (A 0 0) ha0, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.coe_scalar]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, hA]

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

omit [Finite F] hp in
theorem coe_glMapGen614 {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : GL (Fin 2) K) :
    ((Matrix.GeneralLinearGroup.map f A : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      (A : Matrix (Fin 2) (Fin 2) K).map f := by
  ext i j
  exact Matrix.GeneralLinearGroup.map_apply f i j A

theorem isSquare_of_mem_fixedField614 (hF : Nat.card F = p ^ 2) (hp2 : p ≠ 2)
    {τ : F ≃+* F} (hτ : τ ≠ 1) {r : F} (hr : r ∈ fixedField614 τ) : IsSquare r := by
  classical
  by_cases hr0 : r = 0
  · exact ⟨0, by rw [hr0, mul_zero]⟩
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  have hringChar : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  rw [FiniteField.isSquare_iff hringChar hr0, hFc]
  have hrp : r ^ p = r := by
    rw [← ringEquiv_apply_eq_pow614 hF hτ]
    exact mem_fixedField614.mp hr
  have hr1 : r ^ (p - 1) = 1 := by
    have h2 : r ^ (p - 1) * r = 1 * r := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, hrp, one_mul]
    exact mul_right_cancel₀ hr0 h2
  obtain ⟨s, hs⟩ := hp.out.odd_of_ne_two hp2
  have e : p ^ 2 / 2 = (p - 1) * (s + 1) := by
    rw [hs]
    have : (2 * s + 1) ^ 2 = 2 * (2 * s * (s + 1)) + 1 := by ring
    rw [this, show 2 * s + 1 - 1 = 2 * s by omega]
    omega
  rw [e, pow_mul, hr1, one_pow]

theorem iotaR614_mem_range614 (hF : Nat.card F = p ^ 2) (hp2 : p ≠ 2) {τ : F ≃+* F}
    (hτ : τ ≠ 1) (x : PGL2 (fixedField614 τ)) :
    iotaR614 (fixedField614 τ) x ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  rw [iotaR614, Matrix.ProjGenLinGroup.map_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare,
    Matrix.GeneralLinearGroup.val_det_apply, coe_glMapGen614]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact isSquare_of_mem_fixedField614 hF hp2 hτ (Subtype.mem _)

omit [Finite F] hp in
theorem pgl2FieldAut_iotaR614 {τ : F ≃+* F} (x : PGL2 (fixedField614 τ)) :
    pgl2FieldAut F τ (iotaR614 (fixedField614 τ) x) = iotaR614 (fixedField614 τ) x := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  rw [iotaR614, Matrix.ProjGenLinGroup.map_mk, pgl2FieldAut_mk614]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact mem_fixedField614.mp (A i j).2

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

omit [Finite F] hp in
theorem glMap_mul_scalar_apply614 (A : GL (Fin 2) F) (f : F →+* F) (u : Fˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map f A * Matrix.GeneralLinearGroup.scalar (Fin 2) u :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j =
        f ((A : Matrix (Fin 2) (Fin 2) F) i j) * u := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, Matrix.GeneralLinearGroup.map_apply]

omit [Finite F] hp in
theorem exists_entry_ne_zero614 {K : Type*} [Field K] (A : GL (Fin 2) K) :
    ∃ i j, (A : Matrix (Fin 2) (Fin 2) K) i j ≠ 0 := by
  by_contra h
  push Not at h
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  apply hdet
  rw [Matrix.det_fin_two, h 0 0, h 0 1]
  ring

theorem exists_iotaR614_eq_of_fixed (hF : Nat.card F = p ^ 2) {τ : F ≃+* F} (hτ : τ ≠ 1)
    {h : PGL2 F} (hh : pgl2FieldAut F τ h = h) :
    ∃ x : PGL2 (fixedField614 τ), iotaR614 (fixedField614 τ) x = h := by
  classical
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun σ : F ≃+* F => σ x) (ringEquiv_sq_eq_one614 hF hτ)
    simpa [pow_two] using this
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  rw [pgl2FieldAut_mk614, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hh
  obtain ⟨u, hu⟩ := hh
  have hent : ∀ i j, τ ((A : Matrix (Fin 2) (Fin 2) F) i j) * u =
      (A : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) i j) hu
    rw [glMap_mul_scalar_apply614] at this
    exact this
  set κ : F := ((u : F))⁻¹ with hκ
  have hκent : ∀ i j, τ ((A : Matrix (Fin 2) (Fin 2) F) i j) =
      κ * (A : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have hu0 : (u : F) ≠ 0 := Units.ne_zero u
    calc τ ((A : Matrix (Fin 2) (Fin 2) F) i j) =
          τ ((A : Matrix (Fin 2) (Fin 2) F) i j) * u * (u : F)⁻¹ := by field_simp
      _ = (A : Matrix (Fin 2) (Fin 2) F) i j * (u : F)⁻¹ := by rw [hent]
      _ = κ * (A : Matrix (Fin 2) (Fin 2) F) i j := mul_comm _ _
  obtain ⟨i₀, j₀, hij⟩ := exists_entry_ne_zero614 A
  have hκκ : κ * τ κ = 1 := by
    have h1 := hκent i₀ j₀
    have h2 : (A : Matrix (Fin 2) (Fin 2) F) i₀ j₀ =
        τ κ * κ * (A : Matrix (Fin 2) (Fin 2) F) i₀ j₀ := by
      calc (A : Matrix (Fin 2) (Fin 2) F) i₀ j₀ = τ (τ ((A : Matrix (Fin 2) (Fin 2) F) i₀ j₀)) :=
            (hττ _).symm
        _ = τ κ * κ * (A : Matrix (Fin 2) (Fin 2) F) i₀ j₀ := by
            rw [h1, map_mul, hκent i₀ j₀]; ring
    have := mul_right_cancel₀ hij (h2.symm.trans (one_mul _).symm)
    rw [mul_comm]
    exact this
  have hκ0 : κ ≠ 0 := inv_ne_zero (Units.ne_zero u)
  obtain ⟨μ, hμ0, hμ⟩ := exists_mul_apply_eq_self614 hF hτ hκ0 hκκ
  have hfix : ∀ i j, μ * (A : Matrix (Fin 2) (Fin 2) F) i j ∈ fixedField614 τ := by
    intro i j
    rw [mem_fixedField614, map_mul, hκent, ← mul_assoc, mul_comm (τ μ), hμ]
  set MR : Matrix (Fin 2) (Fin 2) (fixedField614 τ) :=
    Matrix.of fun i j => ⟨μ * (A : Matrix (Fin 2) (Fin 2) F) i j, hfix i j⟩ with hMR
  have hMRmap : MR.map (fixedField614 τ).subtype = μ • (A : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    simp [hMR]
  have hMRdet : MR.det ≠ 0 := by
    intro h0
    have h1 := RingHom.map_det (fixedField614 τ).subtype MR
    rw [h0, map_zero, RingHom.mapMatrix_apply, hMRmap, Matrix.det_smul] at h1
    have hAdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    exact mul_ne_zero (pow_ne_zero _ hμ0) hAdet h1.symm
  refine ⟨Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero MR hMRdet), ?_⟩
  rw [iotaR614, Matrix.ProjGenLinGroup.map_mk]
  refine (mk_eq_mk_of_smul614 hμ0 ?_).symm
  rw [coe_glMapGen614]
  exact hMRmap

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

omit [Finite F] hp in
theorem trace_zero_of_involution614 {K : Type*} [Field K] (A : GL (Fin 2) K)
    (h2 : Matrix.ProjGenLinGroup.mk A ^ 2 = 1) (h1 : Matrix.ProjGenLinGroup.mk A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) K) 1 1 = -(A : Matrix (Fin 2) (Fin 2) K) 0 0 ∧
      (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
        (-(A : Matrix (Fin 2) (Fin 2) K).det) • 1 := by
  classical
  rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
  obtain ⟨c, hc⟩ := h2
  set M := (A : Matrix (Fin 2) (Fin 2) K) with hM
  have hMM : M * M = Matrix.scalar (Fin 2) (c : K) := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, pow_two, Units.val_mul] at this
    rw [hM, this]
  have e : ∀ i j, (M * M) i j = (Matrix.scalar (Fin 2) (c : K)) i j := fun i j => by rw [hMM]
  have e01 := e 0 1
  have e10 := e 1 0
  have e00 := e 0 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply,
    Matrix.diagonal_apply] at e01 e10 e00 e11
  norm_num at e01 e10 e00 e11
  have htr : M 0 0 + M 1 1 = 0 := by
    by_contra hne
    apply h1
    have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hcc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hne
    have had : M 0 0 = M 1 1 := by
      have : (M 0 0 - M 1 1) * (M 0 0 + M 1 1) = 0 := by linear_combination e00 - e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
    have ha0 : M 0 0 ≠ 0 := by
      intro h
      have hdet : M.det ≠ 0 := by
        rw [hM, ← Matrix.GeneralLinearGroup.val_det_apply]
        exact Units.ne_zero _
      apply hdet
      rw [Matrix.det_fin_two, h, hb]
      ring
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 (M 0 0) ha0, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hcc, had, ← hM]
  have hd : M 1 1 = -M 0 0 := by linear_combination htr
  refine ⟨hd, ?_⟩
  ext i j
  rw [Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hd] <;> ring

end

section

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]

theorem exists_conj_inr_eq614 (hF : Nat.card F = p ^ 2) (hp2 : p ≠ 2) {τ : F ≃+* F}
    (hτ : τ ≠ 1) (dR : PGL2 (fixedField614 τ)) (hd2 : dR ^ 2 = 1) (hd1 : dR ≠ 1)
    (hdout : dR ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := fixedField614 τ)).range) :
    ∃ k ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range,
      (SemidirectProduct.inl k : PGammaL2 F) * SemidirectProduct.inr τ *
          (SemidirectProduct.inl k)⁻¹ =
        SemidirectProduct.inl (iotaR614 (fixedField614 τ) dR) * SemidirectProduct.inr τ := by
  classical
  obtain ⟨Ar, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective dR
  have hRcard : Nat.card (fixedField614 τ) = p := card_fixedField614 hF hτ
  let : Fintype (fixedField614 τ) := Fintype.ofFinite (fixedField614 τ)
  have hRc : Fintype.card (fixedField614 τ) = p := by rw [← Nat.card_eq_fintype_card, hRcard]
  let : CharP (fixedField614 τ) p := charP_of_card_eq_prime_pow (f := 1) (by rw [hRc, pow_one])
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun σ : F ≃+* F => σ x) (ringEquiv_sq_eq_one614 hF hτ)
    simpa [pow_two] using this
  obtain ⟨-, hMr⟩ := trace_zero_of_involution614 Ar hd2 hd1
  set Mr := (Ar : Matrix (Fin 2) (Fin 2) (fixedField614 τ)) with hMrdef
  set Δr := Mr.det with hΔr
  have hΔr0 : Δr ≠ 0 := by
    rw [hΔr, hMrdef, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hΔrns : ¬ IsSquare Δr := by
    intro h
    apply hdout
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply]
    exact h
  have hΔrpow : Δr ^ ((p - 1) / 2) = -1 := by
    have hringChar : ringChar (fixedField614 τ) ≠ 2 := by
      rw [ringChar.eq (fixedField614 τ) p]; exact hp2
    have h1 := FiniteField.pow_dichotomy hringChar hΔr0
    have h2 := (FiniteField.isSquare_iff hringChar hΔr0).not.mp hΔrns
    rw [hRc] at h1 h2
    have e : p / 2 = (p - 1) / 2 := by
      obtain ⟨s, hs⟩ := hp.out.odd_of_ne_two hp2
      omega
    rw [e] at h1 h2
    exact h1.resolve_left h2
  set Δ : F := (Δr : F) with hΔ
  have hΔ0 : Δ ≠ 0 := by rw [hΔ]; exact_mod_cast hΔr0
  have hΔpow : Δ ^ ((p - 1) / 2) = -1 := by
    rw [hΔ]
    exact_mod_cast hΔrpow
  have hτΔ : τ Δ = Δ := mem_fixedField614.mp Δr.2
  set M : Matrix (Fin 2) (Fin 2) F := Mr.map (fixedField614 τ).subtype with hMdef
  have hMτ : M.map τ = M := by
    ext i j
    simp only [hMdef, Matrix.map_apply]
    exact mem_fixedField614.mp (Mr i j).2
  have hMM : M * M = (-Δ) • 1 := by
    have := congrArg (fun X => X.map (fixedField614 τ).subtype) hMr
    simp only [Matrix.map_mul] at this
    rw [hMdef, this]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hΔ, hΔr]
  have hMdet : M.det = Δ := by
    rw [hMdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  obtain ⟨c, hc0, hc⟩ := exists_mul_apply_eq614 hF hτ (l := (-Δ)⁻¹)
    (inv_ne_zero (neg_ne_zero.mpr hΔ0)) (by rw [map_inv₀, map_neg, hτΔ])
  have hsmul : ∀ (a : F) (X : Matrix (Fin 2) (Fin 2) F), (a • X).map τ = τ a • X.map τ := by
    intro a X
    ext i j
    simp
  set N := c • M with hN
  have hNN : N * N.map τ = 1 := by
    rw [hN, hsmul, hMτ, Matrix.smul_mul, Matrix.mul_smul, hMM, smul_smul, smul_smul, hc,
      inv_mul_cancel₀ (neg_ne_zero.mpr hΔ0), one_smul]
  obtain ⟨B, hBdet, hNB⟩ := exists_twisted_coboundary614 hF hτ N hNN
  set Bg := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  have hNdet : N.det ≠ 0 := by
    rw [hN, Matrix.det_smul, hMdet]
    exact mul_ne_zero (pow_ne_zero _ hc0) hΔ0
  set Ng := Matrix.GeneralLinearGroup.mkOfDetNeZero N hNdet
  have hNgB : Ng * Matrix.GeneralLinearGroup.map τ.toRingHom Bg = Bg := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Units.val_mul, coe_glMap614]
    exact congrFun (congrFun hNB i) j
  refine ⟨Matrix.ProjGenLinGroup.mk Bg, ?_, ?_⟩
  ·
    rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply]
    have hdetτ : (B.map τ).det = τ B.det := by
      rw [show B.map τ = τ.toRingHom.mapMatrix B from rfl, ← RingHom.map_det]
      rfl
    have hrel : B.det = c ^ 2 * Δ * τ B.det := by
      have := congrArg Matrix.det hNB
      rw [Matrix.det_mul, hdetτ, hN, Matrix.det_smul, hMdet, Fintype.card_fin] at this
      exact this.symm
    have hcΔ : c * τ c * Δ = -1 := by
      rw [hc]
      field_simp
    exact isSquare_of_eq614 hF hp2 hτ hBdet hΔpow hcΔ hrel
  · have h1 : Matrix.ProjGenLinGroup.mk Bg *
        pgl2FieldAut F τ (Matrix.ProjGenLinGroup.mk Bg)⁻¹ = Matrix.ProjGenLinGroup.mk Ng := by
      rw [map_inv, pgl2FieldAut_mk614, ← map_inv, ← map_mul]
      congr 1
      calc Bg * (Matrix.GeneralLinearGroup.map τ.toRingHom Bg)⁻¹ =
            Ng * Matrix.GeneralLinearGroup.map τ.toRingHom Bg *
              (Matrix.GeneralLinearGroup.map τ.toRingHom Bg)⁻¹ := by rw [hNgB]
        _ = Ng := mul_inv_cancel_right _ _
    have h2 : Matrix.ProjGenLinGroup.mk Ng =
        iotaR614 (fixedField614 τ) (Matrix.ProjGenLinGroup.mk Ar) := by
      rw [iotaR614, Matrix.ProjGenLinGroup.map_mk]
      refine (mk_eq_mk_of_smul614 hc0 ?_).symm
      rw [coe_glMapGen614]
      rfl
    rw [inl_mul_inr_mul_inl_inv614, h1, h2]

end

end CFSG.Quasithin.H13

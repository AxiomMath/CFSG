module

public import CFSG.LocalAnalysis.StandardType.GGZSMonShape
import CFSG.LocalAnalysis.StandardType.GGRCMonomialFrame

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma monomial_perm {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (a : U ≃ₗ[ZMod p] U)
    (h : ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j) :
    ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) := by
  classical
  choose j c hc hval using h
  have hinj : Function.Injective j := by
    intro i i' hjj
    by_contra hne
    have h1 : c i' • a (f i) = c i • a (f i') := by
      rw [hval i, hval i', hjj, smul_smul, smul_smul, mul_comm]
    have h2 : c i' • f i = c i • f i' := by
      apply a.injective
      simpa [map_smul] using h1
    exact hne (f.linearIndependent.eq_of_smul_apply_eq_smul_apply
      (c i') (c i) i i' (hc i') h2)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj)
  exact ⟨σ, c, hc, fun i => hval i⟩

private lemma smul_diagonal_unitsSMul {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (d : Fin n → (ZMod p)ˣ) {a : U ≃ₗ[ZMod p] U} {c : ZMod p} {i : Fin n}
    (h : a (f i) = c • f i) :
    a ((f.unitsSMul d) i) = c • (f.unitsSMul d) i := by
  simp only [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul, h, smul_smul]
  rw [mul_comm]

private lemma ne_zero_of_eq_smul_self [Fact p.Prime] {n : ℕ}
    {f : Module.Basis (Fin n) (ZMod p) U}
    {a : U ≃ₗ[ZMod p] U} {c : ZMod p} {i : Fin n} (h : a (f i) = c • f i) :
    c ≠ 0 := by
  intro hc
  have hzero : f i = 0 := by
    apply a.injective
    rw [h, hc, zero_smul, map_zero]
  exact f.ne_zero i hzero

private lemma not_exists_pm1_of_diagonal {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    {a : U ≃ₗ[ZMod p] U} {i₀ : Fin n} {c₀ : ZMod p}
    (hdiag : a (b i₀) = c₀ • b i₀) (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1) (hc₂ : c₀ ≠ -1) :
    ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i) := by
  rintro ⟨σ, c, hc, hval⟩
  have heq : c₀ • b i₀ = c i₀ • b (σ i₀) := by rw [← hdiag, hval i₀]
  have hσ : σ i₀ = i₀ :=
    (b.linearIndependent.eq_of_smul_apply_eq_smul_apply c₀ (c i₀) i₀ (σ i₀) hc₀ heq).symm
  have hc_eq : c₀ = c i₀ :=
    b.linearIndependent.smul_left_injective i₀ (by simpa [hσ] using heq)
  rcases hc i₀ with h1 | h1
  · exact hc₁ (hc_eq.trans h1)
  · exact hc₂ (hc_eq.trans h1)

private def IsMonomialPM1 {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    (a : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)

private lemma isMonomialPM1_one {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) U) :
    IsMonomialPM1 b 1 := by
  refine ⟨1, fun _ => 1, fun i => Or.inl rfl, ?_⟩
  intro i
  simp

private lemma isMonomialPM1_mul {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    {a a' : U ≃ₗ[ZMod p] U} (ha : IsMonomialPM1 b a) (ha' : IsMonomialPM1 b a') :
    IsMonomialPM1 b (a * a') := by
  obtain ⟨σ, c, hc, hval⟩ := ha
  obtain ⟨σ', c', hc', hval'⟩ := ha'
  refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_⟩
  · intro i
    rcases hc' i with h1 | h1 <;> rcases hc (σ' i) with h2 | h2 <;> simp [h1, h2]
  · intro i
    rw [LinearEquiv.mul_apply, hval' i, map_smul, hval (σ' i), smul_smul]
    rfl

private lemma isMonomialPM1_inv [Fact p.Prime] {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    {a : U ≃ₗ[ZMod p] U} (ha : IsMonomialPM1 b a) : IsMonomialPM1 b a⁻¹ := by
  obtain ⟨σ, c, hc, hval⟩ := ha
  have hcne : ∀ i, c i ≠ 0 := by
    intro i
    rcases hc i with h | h <;> simp [h]
  refine ⟨σ.symm, fun i => (c (σ.symm i))⁻¹, ?_, ?_⟩
  · intro i
    rcases hc (σ.symm i) with h1 | h1 <;> simp [h1]
  · intro i
    apply a.injective
    show a (a.symm (b i)) = a ((c (σ.symm i))⁻¹ • b (σ.symm i))
    rw [LinearEquiv.apply_symm_apply, map_smul, hval, Equiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ (hcne (σ.symm i)), one_smul]

private lemma unit_sq_eq_one_imp [Fact p.Prime] {c : (ZMod p)ˣ} (hc : c ^ 2 = 1) :
    c = 1 ∨ c = -1 := by
  have hv : (c : ZMod p) * (c : ZMod p) = 1 := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hc
    simpa [Units.val_pow_eq_pow_val, pow_two] using this
  rcases mul_self_eq_one_iff.mp hv with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext h1

private lemma isMonomialPM1_of_isDiagonal {n : ℕ} {b : Module.Basis (Fin n) (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} {i : Fin n}
    (hdiag : IsDiagonal b t (fun k => if k = i then -1 else 1)) :
    IsMonomialPM1 b t := by
  refine ⟨1, fun k => ((if k = i then -1 else 1 : (ZMod p)ˣ) : ZMod p), ?_, ?_⟩
  · intro k
    by_cases h : k = i <;> simp [h]
  · intro k
    simpa using hdiag k

private lemma isMonomialPM1_of_isTwistedSwap [Fact p.Prime] {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod p) U} {t : U ≃ₗ[ZMod p] U} {x y : Fin n}
    {c : (ZMod p)ˣ} (htw : IsTwistedSwap b t x y c) (hc2 : c ^ 2 = 1) :
    IsMonomialPM1 b t := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
  have hcpm : c = 1 ∨ c = -1 := unit_sq_eq_one_imp hc2
  refine ⟨Equiv.swap x y,
    fun k => if k = x then (c : ZMod p) else if k = y then (c : ZMod p) else 1, ?_, ?_⟩
  · intro k
    by_cases hx : k = x
    · rw [hx]; rcases hcpm with h | h <;> simp [h]
    · by_cases hy : k = y
      · rw [hy]; rcases hcpm with h | h <;> simp [h, htw.1.symm]
      · simp [hx, hy]
  · intro k
    by_cases hx : k = x
    · rw [hx]
      rw [htw.2.1]
      simp [Equiv.swap_apply_left]
    · by_cases hy : k = y
      · rw [hy]
        rw [htw.2.2.1, hcinv]
        simp [Equiv.swap_apply_right, htw.1.symm]
      · rw [htw.2.2.2 k hx hy]
        simp [hx, hy, Equiv.swap_apply_of_ne_of_ne hx hy]

private lemma isMonomialPM1_of_isRefl [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod p) U} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hno : ∀ s ∈ A, IsRefl p s → ∀ (i j : Fin n) (c : (ZMod p)ˣ),
      IsTwistedSwap b s i j c → c ^ 2 = 1)
    {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (ht : IsRefl p t) : IsMonomialPM1 b t := by
  obtain ⟨σ, c, hc, hval⟩ := hmon t htA
  rcases isDiagonal_or_isTwistedSwap_of_isRefl hp2 ht ⟨σ, c, hc, hval⟩ with h | ⟨x, y, u, htw⟩
  · obtain ⟨i, hdiag⟩ := h
    exact isMonomialPM1_of_isDiagonal hdiag
  · exact isMonomialPM1_of_isTwistedSwap htw (hno t htA ht x y u htw)

private lemma isMonomialPM1_of_mem_of_no_twistedSwap [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod p) U} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i))
    (hno : ∀ s ∈ A, IsRefl p s → ∀ (i j : Fin n) (c : (ZMod p)ˣ),
      IsTwistedSwap b s i j c → c ^ 2 = 1)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r}) {a : U ≃ₗ[ZMod p] U}
    (ha : a ∈ A) : IsMonomialPM1 b a := by
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {a | IsMonomialPM1 b a}
      one_mem' := isMonomialPM1_one b
      mul_mem' := fun ha hb => isMonomialPM1_mul ha hb
      inv_mem' := fun ha => isMonomialPM1_inv ha }
  have hle : Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} ≤ H := by
    rw [Subgroup.closure_le]
    rintro r ⟨hrA, hrRefl⟩
    exact isMonomialPM1_of_isRefl hp2 hmon hno hrA hrRefl
  rw [hgen] at ha
  exact hle ha

theorem exists_frame_of_witMON [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hRG : ReflGen p A) (hAI : AbsIrred p A) (hM : WitMON p A) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (ZMod p) U), 3 ≤ n ∧
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (b i) = c i • b (σ i)) ∧
      (∀ σ : Equiv.Perm (Fin n), permMap p b σ ∈ A) ∧
      ∃ δ ∈ A, ∃ (i j : Fin n) (ζ : (ZMod p)ˣ), i ≠ j ∧ ζ ^ 2 ≠ 1 ∧
        IsDiagonal b δ (pairUnit p i j ζ) := by
  classical
  obtain ⟨n, f, hn, hmono, a₀, ha₀, hdiag₀, i₀, c₀, hc₀, hc₁, hc₂⟩ := hM
  have hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i) :=
    fun a ha => monomial_perm f a (hmono a ha)
  have hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := hRG
  obtain ⟨b, hbmon, hbperm, d, hbd⟩ := ggRC_monomial_frame hp2 f A hAI hgen hmon
  have hbdiag : a₀ (b i₀) = c₀ • b i₀ := by
    rw [hbd]
    exact smul_diagonal_unitsSMul f d hc₀
  have hc₀ne : c₀ ≠ 0 := ne_zero_of_eq_smul_self hc₀
  have hnotpm : ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a₀ (b i) = c i • b (σ i) :=
    not_exists_pm1_of_diagonal hbdiag hc₀ne hc₁ hc₂
  have hex : ∃ s ∈ A, IsRefl p s ∧ ∃ (i j : Fin n) (c : (ZMod p)ˣ),
      IsTwistedSwap b s i j c ∧ c ^ 2 ≠ 1 := by
    by_contra hnoEx
    have hno : ∀ s ∈ A, IsRefl p s → ∀ (i j : Fin n) (c : (ZMod p)ˣ),
        IsTwistedSwap b s i j c → c ^ 2 = 1 := by
      intro s hs hrefl i j c htw
      by_contra hc
      exact hnoEx ⟨s, hs, hrefl, i, j, c, htw, hc⟩
    exact hnotpm (isMonomialPM1_of_mem_of_no_twistedSwap hp2 hbmon hno hgen ha₀)
  obtain ⟨s, hsA, hrefl, i, j, c, htw, hc2⟩ := hex
  refine ⟨n, b, hn, hbmon, hbperm, s * permMap p b (Equiv.swap i j), ?_, i, j, c⁻¹,
    htw.1, ?_, ?_⟩
  · exact A.mul_mem hsA (hbperm _)
  · intro h
    apply hc2
    have h' : ((c ^ 2)⁻¹ : (ZMod p)ˣ) = 1 := by
      simpa [inv_pow] using congrArg (fun u : (ZMod p)ˣ => u⁻¹) h
    exact inv_eq_one.mp h'
  · simpa using IsTwistedSwap.mul_isDiagonal htw (isTwistedSwap_permMap_swap htw.1)

end CFSG.StandardType.ZS

end

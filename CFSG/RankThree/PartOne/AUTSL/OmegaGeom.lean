module

public import CFSG.RankThree.PartOne.AUTSL.FieldExt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical
open Matrix

section TotSing

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem totSing_span {ι : Type*} (Q : QuadraticForm K V) (v : ι → V) (h0 : ∀ i, Q (v i) = 0)
    (hp : ∀ i k, QuadraticMap.polar Q (v i) (v k) = 0) :
    ∀ x ∈ Submodule.span K (Set.range v), Q x = 0 := by
  have h1 : ∀ i, ∀ y ∈ Submodule.span K (Set.range v), QuadraticMap.polar Q (v i) y = 0 := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hp i k
    | zero => exact QuadraticMap.polar_zero_right _ _
    | add y z _ _ hy hz => rw [QuadraticMap.polar_add_right, hy, hz, add_zero]
    | smul a y _ hy => rw [QuadraticMap.polar_smul_right, hy, smul_zero]
  have h2 : ∀ x ∈ Submodule.span K (Set.range v), ∀ y ∈ Submodule.span K (Set.range v),
      QuadraticMap.polar Q x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h1 i y hy
    | zero => exact QuadraticMap.polar_zero_left _ _
    | add x z _ _ hx hz => rw [QuadraticMap.polar_add_left, hx, hz, add_zero]
    | smul a x _ hx => rw [QuadraticMap.polar_smul_left, hx, smul_zero]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h0 i
  | zero => exact QuadraticMap.map_zero _
  | add x z hx' hz' hx hz =>
    rw [QuadraticMap.map_add (⇑Q), hx, hz, h2 x hx' z hz', add_zero, add_zero]
  | smul a x _ hx => rw [QuadraticMap.map_smul, hx, smul_zero]

theorem exists_totSing_four {E : Type*} (Q : QuadraticForm K V) (ρ : E → V →ₗ[K] V)
    (hρ : ∀ g v, Q (ρ g v) = Q v) (v : Fin 4 → V) (hli : LinearIndependent K v)
    (χ : Fin 4 → E → K) (hv : ∀ k g, ρ g (v k) = χ k g • v k)
    (hsq : ∀ k, ∃ g, χ k g ^ 2 ≠ 1) (hpair : ∀ k l, k ≠ l → ∃ g, χ k g * χ l g ≠ 1) :
    ∃ T : Submodule K V, Module.finrank K T = 4 ∧ ∀ x ∈ T, Q x = 0 := by
  have h0 : ∀ k, Q (v k) = 0 := by
    intro k
    obtain ⟨g, hg⟩ := hsq k
    have h1 : Q (v k) = χ k g ^ 2 * Q (v k) := by
      calc Q (v k) = Q (ρ g (v k)) := (hρ g _).symm
        _ = χ k g ^ 2 * Q (v k) := by rw [hv, QuadraticMap.map_smul, smul_eq_mul, sq]
    have h2 : (χ k g ^ 2 - 1) * Q (v k) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hg
    · exact h
  have hinv : ∀ g x y, QuadraticMap.polar Q (ρ g x) (ρ g y) = QuadraticMap.polar Q x y := by
    intro g x y
    simp only [QuadraticMap.polar]
    rw [← map_add, hρ, hρ, hρ]
  have hp : ∀ k l, QuadraticMap.polar Q (v k) (v l) = 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      rw [QuadraticMap.polar_self, h0, smul_zero]
    · obtain ⟨g, hg⟩ := hpair k l hkl
      have h1 : QuadraticMap.polar Q (v k) (v l) =
          (χ k g * χ l g) * QuadraticMap.polar Q (v k) (v l) := by
        calc QuadraticMap.polar Q (v k) (v l)
            = QuadraticMap.polar Q (ρ g (v k)) (ρ g (v l)) := (hinv g _ _).symm
          _ = _ := by
            rw [hv, hv, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, smul_eq_mul,
              smul_eq_mul, mul_assoc]
      have h2 : (χ k g * χ l g - 1) * QuadraticMap.polar Q (v k) (v l) = 0 := by
        linear_combination -h1
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (sub_eq_zero.1 h) hg
      · exact h
  refine ⟨Submodule.span K (Set.range v), ?_, totSing_span Q v h0 hp⟩
  rw [finrank_span_eq_card hli, Fintype.card_fin]

end TotSing

section Chars

variable {E : Type*} [CommGroup E] {X : Type*} [CommGroup X]

theorem exists_char_mul_self_ne_one (hE5 : ∀ x : E, x ^ 5 = 1) {F : E →* X} (hF : F ≠ 1) :
    ∃ x, F x * F x ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hF
  refine MonoidHom.ext fun x => ?_
  have h5 : F x ^ 5 = 1 := by rw [← map_pow, hE5, map_one]
  have h2 : F x * F x = 1 := hall x
  have h3 : F x * (F x * F x) * (F x * F x) = F x ^ 5 := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [MonoidHom.one_apply]
  calc F x = F x * (F x * F x) * (F x * F x) := by rw [h2]; simp
    _ = F x ^ 5 := h3
    _ = 1 := h5

end Chars

section CaseR

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K']
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zero_class_false_R (hsurj : Function.Surjective (algebraMap K K'))
    {E : Type*} [CommGroup E] (hE5 : ∀ x : E, x ^ 5 = 1) {B : Type*} [Group B] (ιB : B →* E)
    (ρ : E →* Matrix ι ι K) (Q : QuadraticForm K (ι → K))
    (hρQ : ∀ g v, Q (ρ g *ᵥ v) = Q v)
    (hWitt : ∀ T : Submodule K (ι → K), (∀ x ∈ T, Q x = 0) → Module.finrank K T ≤ 3)
    (P : GL ι K') (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K'))
    {ia ib ic i0 : ι} {a b c : B →* K'ˣ} (hia : (f ia).comp ιB = a) (hib : (f ib).comp ιB = b)
    (hic : (f ic).comp ιB = c) (hi0 : (f i0).comp ιB = 1) (hf0 : f i0 ≠ 1)
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : ∃ x : B, a x * b x ≠ 1) (hac' : ∃ x : B, a x * c x ≠ 1)
    (hbc' : ∃ x : B, b x * c x ≠ 1) : False := by
  let φ : K ≃+* K' := RingEquiv.ofBijective (algebraMap K K') ⟨(algebraMap K K').injective, hsurj⟩
  have hφapp : ∀ x, φ x = algebraMap K K' x := fun x => rfl
  set Pinv : Matrix ι ι K' := ((P⁻¹ : GL ι K') : Matrix ι ι K') with hPi
  have hPiP : Pinv * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  have hρPi : ∀ g : E, (ρ g).map (algebraMap K K') * Pinv =
      Pinv * Matrix.diagonal fun i => ((f i g : K'ˣ) : K') := by
    intro g
    have h1 := hD g
    calc (ρ g).map (algebraMap K K') * Pinv
        = (Pinv * (P : Matrix ι ι K')) * (ρ g).map (algebraMap K K') * Pinv := by
          rw [hPiP, one_mul]
      _ = Pinv * ((P : Matrix ι ι K') * (ρ g).map (algebraMap K K') * Pinv) := by noncomm_ring
      _ = _ := by rw [h1]
  let vK : ι → (ι → K) := fun i j => φ.symm (Pinv j i)
  have hvK : ∀ (g : E) (i : ι),
      ρ g *ᵥ vK i = φ.symm ((f i g : K'ˣ) : K') • vK i := by
    intro g i
    funext j
    apply φ.injective
    have h1 := congrFun (congrFun (hρPi g) j) i
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
    have hL : φ ((ρ g *ᵥ vK i) j) = ∑ l, algebraMap K K' (ρ g j l) * Pinv l i := by
      show φ (∑ l, ρ g j l * φ.symm (Pinv l i)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, φ.apply_symm_apply]
      rfl
    have hR : φ ((φ.symm ((f i g : K'ˣ) : K') • vK i) j) = Pinv j i * ((f i g : K'ˣ) : K') := by
      show φ (φ.symm ((f i g : K'ˣ) : K') * φ.symm (Pinv j i)) = _
      rw [map_mul, φ.apply_symm_apply, φ.apply_symm_apply, mul_comm]
    rw [hL, hR]
    simpa only [Matrix.map_apply] using h1
  let idx : Fin 4 → ι := ![ia, ib, ic, i0]
  let F : Fin 4 → (E →* K'ˣ) := fun k => f (idx k)
  let ch : Fin 4 → (B →* K'ˣ) := ![a, b, c, 1]
  have hrestr : ∀ k, (F k).comp ιB = ch k := by
    intro k
    fin_cases k
    · exact hia
    · exact hib
    · exact hic
    · exact hi0
  have hrestrx : ∀ (k : Fin 4) (x : B), F k (ιB x) = ch k x := fun k x => by
    rw [← hrestr k]
    rfl
  have hchne : ∀ k l : Fin 4, k ≠ l → ch k ≠ ch l := by
    have hac1 := ha.symm
    have hbc1 := hb.symm
    have hcc1 := hc.symm
    have hba := hab.symm
    have hca := hac.symm
    have hcb := hbc.symm
    intro k l hkl
    fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | assumption
  have hidx : Function.Injective idx := by
    intro k l hkl
    by_contra hne
    apply hchne k l hne
    rw [← hrestr k, ← hrestr l]
    have : F k = F l := by simp only [F, hkl]
    rw [this]
  have hex1 : ∀ d : B →* K'ˣ, d ≠ 1 → ∃ x : B, d x ≠ 1 := by
    intro d hd
    by_contra hall
    push Not at hall
    exact hd (MonoidHom.ext fun x => hall x)
  have hFne1 : ∀ k, F k ≠ 1 := by
    intro k hk
    have h1 : ch k = 1 := by rw [← hrestr k, hk]; rfl
    fin_cases k
    · exact ha h1
    · exact hb h1
    · exact hc h1
    · exact hf0 hk
  have hFsq : ∀ k, ∃ g : E, F k g * F k g ≠ 1 := fun k =>
    exists_char_mul_self_ne_one hE5 (hFne1 k)
  have hpairB : ∀ k l : Fin 4, k ≠ l → ∃ x : B, ch k x * ch l x ≠ 1 := by
    obtain ⟨xa, hxa⟩ := hex1 a ha
    obtain ⟨xb, hxb⟩ := hex1 b hb
    obtain ⟨xc, hxc⟩ := hex1 c hc
    obtain ⟨x1, hx1⟩ := hab'
    obtain ⟨x2, hx2⟩ := hac'
    obtain ⟨x3, hx3⟩ := hbc'
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · exact ⟨x1, hx1⟩
    · exact ⟨x2, hx2⟩
    · exact ⟨xa, by simpa [ch] using hxa⟩
    · exact ⟨x1, by rw [mul_comm]; exact hx1⟩
    · exact absurd rfl hkl
    · exact ⟨x3, hx3⟩
    · exact ⟨xb, by simpa [ch] using hxb⟩
    · exact ⟨x2, by rw [mul_comm]; exact hx2⟩
    · exact ⟨x3, by rw [mul_comm]; exact hx3⟩
    · exact absurd rfl hkl
    · exact ⟨xc, by simpa [ch] using hxc⟩
    · exact ⟨xa, by simpa [ch] using hxa⟩
    · exact ⟨xb, by simpa [ch] using hxb⟩
    · exact ⟨xc, by simpa [ch] using hxc⟩
    · exact absurd rfl hkl
  have hli : LinearIndependent K (fun k : Fin 4 => vK (idx k)) := by
    let Pinv₀ : Matrix ι ι K := Pinv.map φ.symm
    have hPi₀ : IsUnit Pinv₀ := by
      have hu : IsUnit Pinv := (P⁻¹).isUnit
      exact hu.map (RingHom.mapMatrix (φ.symm : K' →+* K)).toMonoidHom
    have hcol : ∀ i, vK i = Pinv₀ *ᵥ Pi.single i (1 : K) := by
      intro i
      rw [Matrix.mulVec_single_one]
      rfl
    have hinj : Function.Injective (Matrix.mulVecLin Pinv₀) :=
      Matrix.mulVec_injective_iff_isUnit.2 hPi₀
    have hbasis := (Pi.basisFun K ι).linearIndependent.map' (Matrix.mulVecLin Pinv₀)
      (LinearMap.ker_eq_bot.2 hinj)
    have hli0 : LinearIndependent K (fun i : ι => vK i) := by
      convert hbasis using 1
      funext i
      rw [hcol]
      simp [Pi.basisFun_apply]
    exact hli0.comp idx hidx
  let χ : Fin 4 → E → K := fun k g => φ.symm ((F k g : K'ˣ) : K')
  have hχmul : ∀ k l g, χ k g * χ l g = φ.symm (((F k g : K'ˣ) : K') * ((F l g : K'ˣ) : K')) := by
    intro k l g
    simp [χ]
  have hsq : ∀ k, ∃ g, χ k g ^ 2 ≠ 1 := by
    intro k
    obtain ⟨g, hg⟩ := hFsq k
    refine ⟨g, fun h => hg ?_⟩
    have h2 : φ.symm (((F k g : K'ˣ) : K') * ((F k g : K'ˣ) : K')) = 1 := by
      rw [← hχmul, ← sq]
      exact h
    have h3 : ((F k g : K'ˣ) : K') * ((F k g : K'ˣ) : K') = 1 := by
      have := congrArg φ h2
      simpa using this
    apply Units.ext
    simpa using h3
  have hpair : ∀ k l, k ≠ l → ∃ g, χ k g * χ l g ≠ 1 := by
    intro k l hkl
    obtain ⟨x, hx⟩ := hpairB k l hkl
    refine ⟨ιB x, fun h => hx ?_⟩
    rw [hχmul] at h
    have h3 : ((F k (ιB x) : K'ˣ) : K') * ((F l (ιB x) : K'ˣ) : K') = 1 := by
      have := congrArg φ h
      simpa using this
    have h4 : F k (ιB x) * F l (ιB x) = 1 := by
      apply Units.ext
      simpa using h3
    rw [hrestrx, hrestrx] at h4
    exact h4
  obtain ⟨T, hT4, hTs⟩ := exists_totSing_four Q (fun g => Matrix.mulVecLin (ρ g))
    (fun g v => hρQ g v) (fun k => vK (idx k)) hli χ (fun k g => hvK g (idx k)) hsq hpair
  have := hWitt T hTs
  omega

end CaseR

section Orth

variable {B : Type*} [Group B] [Fintype B] {K' : Type*} [Field K']

theorem sum_inv_mul_eq_zero {χ ψ : B →* K'ˣ} (h : χ ≠ ψ) :
    ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') * ((ψ b : K'ˣ) : K') = 0 := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, χ b₀ ≠ ψ b₀ := by
    by_contra hall
    push Not at hall
    exact h (MonoidHom.ext hall)
  set S := ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') * ((ψ b : K'ˣ) : K') with hS
  set c₀ : K' := (((χ b₀)⁻¹ : K'ˣ) : K') * ((ψ b₀ : K'ˣ) : K') with hc₀
  have h1 : c₀ * S = S := by
    rw [hS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft b₀) _ _ fun b => ?_
    simp only [Equiv.coe_mulLeft, map_mul, mul_inv, Units.val_mul, hc₀]
    ring
  have hc1 : c₀ ≠ 1 := by
    intro h2
    apply hb₀
    have h3 : ((χ b₀)⁻¹ : K'ˣ) * ψ b₀ = 1 := by
      apply Units.ext
      simpa [hc₀] using h2
    have : ψ b₀ = χ b₀ := by
      calc ψ b₀ = χ b₀ * ((χ b₀)⁻¹ * ψ b₀) := by group
        _ = χ b₀ := by rw [h3, mul_one]
    exact this.symm
  have h4 : (c₀ - 1) * S = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd (sub_eq_zero.1 h5) hc1
  · exact h5

end Orth

section CaseN

variable {K K' : Type*} [Field K] [CharP K 2] [Field K'] [Algebra K K'] [CharP K' 2]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP K 2] [CharP K' 2] in
theorem weight_coord_mulVec {E : Type*} [CommGroup E] (ρ : E →* Matrix ι ι K) (P : GL ι K')
    (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K'))
    (g : E) (v : ι → K) :
    (P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ (ρ g *ᵥ v)) =
      Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ
        ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ v)) := by
  have hPiP : ((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K') = 1 := Units.inv_mul P
  have hρ' : (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') =
      Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) * (P : Matrix ι ι K') := by
    calc (P : Matrix ι ι K') * (ρ g).map (algebraMap K K')
        = (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
            (((P⁻¹ : GL ι K') : Matrix ι ι K') * (P : Matrix ι ι K')) := by
          rw [hPiP, mul_one]
      _ = ((P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
            ((P⁻¹ : GL ι K') : Matrix ι ι K')) * (P : Matrix ι ι K') := by noncomm_ring
      _ = _ := by rw [hD g]
  have h1 : algebraMap K K' ∘ (ρ g *ᵥ v) =
      (ρ g).map (algebraMap K K') *ᵥ (algebraMap K K' ∘ v) := by
    funext i
    exact RingHom.map_mulVec (algebraMap K K') (ρ g) v i
  rw [h1, Matrix.mulVec_mulVec, hρ', ← Matrix.mulVec_mulVec]

omit [CharP K 2] [CharP K' 2] [Algebra K K'] [Fintype ι] [DecidableEq ι] in
theorem gram_entries {E : Type*} [CommGroup E] [Fintype ι] [DecidableEq ι] (f : ι → (E →* K'ˣ))
    (Qm : Matrix ι ι K')
    (hQE : ∀ g : E, Qm * Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) =
      Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) * Qm)
    {i j : ι} (hij : Qm i j ≠ 0) (g : E) :
    ((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') = 1 := by
  have h1 := congrFun (congrFun (hQE g) i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have hfi : ((f i g : K'ˣ) : K') ≠ 0 := (f i g).ne_zero
  have h2 : Qm i j * (((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') - 1) = 0 := by
    have h3 : ((f i g : K'ˣ) : K') * (Qm i j * ((f j g : K'ˣ) : K')) = Qm i j := by
      rw [h1, ← mul_assoc, mul_inv_cancel₀ hfi, one_mul]
    linear_combination h3
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hij
  · exact sub_eq_zero.1 h

omit [CharP K 2] [CharP K' 2] [Algebra K K'] in
theorem exists_gram_ne_zero {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (Qm : Matrix ι' ι' K')
    (hQu : IsUnit Qm) (j : ι') : ∃ i, Qm i j ≠ 0 := by
  by_contra hall
  push Not at hall
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hQu
  have h0 : Qm *ᵥ Pi.single j (1 : K') = Qm *ᵥ 0 := by
    funext i
    simp [hall i]
  have h1 := congrFun (hinj h0) j
  simp at h1

omit [CharP K 2] in
theorem support_N {E : Type*} [CommGroup E] (hE5 : ∀ x : E, x ^ 5 = 1) {B : Type*} [Group B]
    [Fintype B] (hB25 : Fintype.card B = 25) (ιB : B →* E)
    (ρ : E →* Matrix ι ι K) (Q : QuadraticForm K (ι → K))
    (σ : K' →+* K') (hσK : ∀ x : K, σ (algebraMap K K' x) = algebraMap K K' x)
    (hσ5 : ∀ y : K', y ^ 5 = 1 → σ y = y⁻¹)
    (P : GL ι K') (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K'))
    (Qm : Matrix ι ι K') (hQu : IsUnit Qm)
    (hQE : ∀ g : E, Qm * Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) =
      Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) * Qm)
    (hpolQ : ∀ v w : ι → K, algebraMap K K' (QuadraticMap.polar Q v w) =
      ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ v)) ⬝ᵥ
        Qm *ᵥ ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ w)))
    (hinj0 : ∀ i k, (f i).comp ιB = (f k).comp ιB → (f i).comp ιB ≠ 1 → i = k)
    (W : Submodule K (ι → K)) (hWs : ∀ x ∈ W, Q x = 0)
    (hWB : ∀ b : B, ∀ w ∈ W, ρ (ιB b) *ᵥ w ∈ W) (w : ι → K) (hw : w ∈ W) (k : ι)
    (hk : (f k).comp ιB ≠ 1) :
    ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ w)) k = 0 := by
  classical
  set Pm : Matrix ι ι K' := (P : Matrix ι ι K') with hPm
  set Pinv : Matrix ι ι K' := ((P⁻¹ : GL ι K') : Matrix ι ι K') with hPinv
  have hPPi : Pm * Pinv = 1 := Units.mul_inv P
  have hPiP : Pinv * Pm = 1 := Units.inv_mul P
  let D : E → Matrix ι ι K' := fun g => Matrix.diagonal fun i => ((f i g : K'ˣ) : K')
  have hρ' : ∀ g : E, Pm * (ρ g).map (algebraMap K K') = D g * Pm := by
    intro g
    have h1 := hD g
    calc Pm * (ρ g).map (algebraMap K K')
        = Pm * (ρ g).map (algebraMap K K') * (Pinv * Pm) := by rw [hPiP, mul_one]
      _ = (Pm * (ρ g).map (algebraMap K K') * Pinv) * Pm := by noncomm_ring
      _ = D g * Pm := by rw [h1]
  have hF1 : ∀ (g : E) (v : ι → K),
      Pm *ᵥ (algebraMap K K' ∘ (ρ g *ᵥ v)) = D g *ᵥ (Pm *ᵥ (algebraMap K K' ∘ v)) :=
    fun g v => weight_coord_mulVec ρ P f hD g v
  have hQrel : ∀ i j, Qm i j ≠ 0 → ∀ g : E,
      ((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') = 1 := fun i j hij g =>
    gram_entries f Qm hQE hij g
  have hcolnz : ∀ j, ∃ i, Qm i j ≠ 0 := exists_gram_ne_zero Qm hQu
  obtain ⟨u, hu⟩ : ∃ u : ι → K', u = Pm *ᵥ (algebraMap K K' ∘ w) := ⟨_, rfl⟩
  rw [← hu]
  have hexp : ∀ (g : E) (v : ι → K'), v ⬝ᵥ Qm *ᵥ (D g *ᵥ v) =
      ∑ j, ((∑ i, v i * Qm i j) * v j) * ((f j g : K'ˣ) : K') := by
    intro g v
    have hDv : ∀ j, (D g *ᵥ v) j = ((f j g : K'ˣ) : K') * v j := fun j =>
      Matrix.mulVec_diagonal _ _ _
    show ∑ i, v i * ∑ j, Qm i j * (D g *ᵥ v) j = _
    simp only [hDv, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hTsum : ∀ b : B, ∑ j, ((∑ i, u i * Qm i j) * u j) * ((f j (ιB b) : K'ˣ) : K') = 0 := by
    intro b
    have hwb : ρ (ιB b) *ᵥ w ∈ W := hWB b w hw
    have hpol : QuadraticMap.polar Q w (ρ (ιB b) *ᵥ w) = 0 := by
      have h1 := hWs _ (W.add_mem hw hwb)
      have h2 := hWs _ hw
      have h3 := hWs _ hwb
      simp only [QuadraticMap.polar, h1, h2, h3, sub_zero]
    have h4 := hpolQ w (ρ (ιB b) *ᵥ w)
    rw [hpol, map_zero, hF1, ← hu, hexp] at h4
    exact h4.symm
  have hTk : (∑ i, u i * Qm i k) * u k = 0 := by
    set χ : B →* K'ˣ := (f k).comp ιB with hχ
    have hcard : (Fintype.card B : K') = 1 := by
      have h24 : ((24 : ℕ) : K') = 0 := (CharP.cast_eq_zero_iff K' 2 24).2 (by norm_num)
      rw [hB25, show (25 : ℕ) = 24 + 1 from rfl, Nat.cast_add, h24, zero_add, Nat.cast_one]
    have h1 : ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') *
        ∑ j, ((∑ i, u i * Qm i j) * u j) * ((f j (ιB b) : K'ˣ) : K') = 0 :=
      Finset.sum_eq_zero fun b _ => by rw [hTsum b, mul_zero]
    have h2 : ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') *
        ∑ j, ((∑ i, u i * Qm i j) * u j) * ((f j (ιB b) : K'ˣ) : K') =
        ∑ j, ((∑ i, u i * Qm i j) * u j) *
          ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') * (((f j).comp ιB b : K'ˣ) : K') := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.comp_apply]
      ring
    have h3 : ∀ j, ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') * (((f j).comp ιB b : K'ˣ) : K') =
        if (f j).comp ιB = χ then 1 else 0 := by
      intro j
      by_cases hj : (f j).comp ιB = χ
      · simp only [hj, ↓reduceIte]
        have : ∀ b : B, (((χ b)⁻¹ : K'ˣ) : K') * ((χ b : K'ˣ) : K') = 1 := by
          intro b
          simp
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact hcard
      · simp only [hj, ↓reduceIte]
        exact sum_inv_mul_eq_zero (Ne.symm hj)
    rw [h2] at h1
    have h4 : ∑ j, ((∑ i, u i * Qm i j) * u j) *
        ∑ b : B, (((χ b)⁻¹ : K'ˣ) : K') * (((f j).comp ιB b : K'ˣ) : K') =
        ∑ j, ((∑ i, u i * Qm i j) * u j) * (if (f j).comp ιB = χ then 1 else 0) :=
      Finset.sum_congr rfl fun j _ => by rw [h3 j]
    rw [h4, Finset.sum_eq_single k] at h1
    · have hkχ : (f k).comp ιB = χ := rfl
      simp only [hkχ, ↓reduceIte, mul_one] at h1
      exact h1
    · intro j _ hjk
      have hj : ¬ (f j).comp ιB = χ := fun hj => hjk (hinj0 j k hj (hj ▸ hk))
      simp only [hj, ↓reduceIte, mul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have hmapone : (1 : Matrix ι ι K').map σ = 1 := Matrix.map_one σ (map_zero σ) (map_one σ)
  let Pσ : Matrix ι ι K' := Pm.map σ
  let Piσ : Matrix ι ι K' := Pinv.map σ
  have hPσPiσ : Pσ * Piσ = 1 := by
    have := congrArg (fun M : Matrix ι ι K' => M.map σ) hPPi
    simpa only [Matrix.map_mul, hmapone] using this
  have hPiσPσ : Piσ * Pσ = 1 := by
    have := congrArg (fun M : Matrix ι ι K' => M.map σ) hPiP
    simpa only [Matrix.map_mul, hmapone] using this
  let Aσ : Matrix ι ι K' := Pm * Piσ
  have hρσ : ∀ g : E, ((ρ g).map (algebraMap K K')).map σ = (ρ g).map (algebraMap K K') := by
    intro g
    ext i j
    simp [Matrix.map_apply, hσK]
  have hG2 : ∀ g : E, Pσ * (ρ g).map (algebraMap K K') * Piσ =
      Matrix.diagonal fun i => (((f i g : K'ˣ) : K'))⁻¹ := by
    intro g
    have h1 := congrArg (fun M : Matrix ι ι K' => M.map σ) (hD g)
    simp only [Matrix.map_mul, hρσ] at h1
    rw [Matrix.diagonal_map (map_zero σ)] at h1
    have h3 : (fun i => σ ((f i g : K'ˣ) : K')) = fun i => (((f i g : K'ˣ) : K'))⁻¹ := by
      funext i
      apply hσ5
      have h5 := congrArg (fun x : K'ˣ => (x : K'))
        (show f i g ^ 5 = 1 by rw [← map_pow, hE5, map_one])
      simpa using h5
    rw [h3] at h1
    exact h1
  have hG3 : ∀ g : E, Aσ * Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) = D g * Aσ := by
    intro g
    calc Aσ * Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹)
        = Pm * Piσ * (Pσ * (ρ g).map (algebraMap K K') * Piσ) := by rw [hG2]
      _ = Pm * (Piσ * Pσ) * (ρ g).map (algebraMap K K') * Piσ := by noncomm_ring
      _ = Pm * (ρ g).map (algebraMap K K') * Piσ := by rw [hPiσPσ, mul_one]
      _ = D g * Pm * Piσ := by rw [hρ']
      _ = D g * Aσ := by noncomm_ring
  have hAσrel : ∀ i j, Aσ i j ≠ 0 → ∀ g : E,
      ((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') = 1 := by
    intro i j hij g
    have h1 := congrFun (congrFun (hG3 g) i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, D] at h1
    have hfj : ((f j g : K'ˣ) : K') ≠ 0 := (f j g).ne_zero
    have h2 : Aσ i j * (((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') - 1) = 0 := by
      have h3 : ((f j g : K'ˣ) : K') * (Aσ i j * (((f j g : K'ˣ) : K'))⁻¹) = Aσ i j := by
        field_simp
      rw [h1] at h3
      linear_combination h3
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hij
    · exact sub_eq_zero.1 h
  have hσu : σ ∘ u = Pσ *ᵥ (algebraMap K K' ∘ w) := by
    funext k'
    have h1 := RingHom.map_mulVec σ Pm (algebraMap K K' ∘ w) k'
    rw [hu]
    refine h1.trans ?_
    have h2 : (σ ∘ (algebraMap K K' ∘ w)) = algebraMap K K' ∘ w := by
      funext j
      exact hσK (w j)
    rw [h2]
  have hG4 : u = Aσ *ᵥ (σ ∘ u) := by
    rw [hσu, Matrix.mulVec_mulVec]
    have h1 : Aσ * Pσ = Pm := by
      show Pm * Piσ * Pσ = Pm
      rw [mul_assoc, hPiσPσ, mul_one]
    rw [h1, hu]
  have hpart : ∀ i₁ i₂, (∀ g : E, ((f i₁ g : K'ˣ) : K') * ((f k g : K'ˣ) : K') = 1) →
      (∀ g : E, ((f i₂ g : K'ˣ) : K') * ((f k g : K'ˣ) : K') = 1) → i₁ = i₂ := by
    intro i₁ i₂ h₁ h₂
    have hu1 : ∀ g, f i₁ g = (f k g)⁻¹ := fun g => by
      have : f i₁ g * f k g = 1 := Units.ext (by simpa using h₁ g)
      exact eq_inv_of_mul_eq_one_left this
    have hu2 : ∀ g, f i₂ g = (f k g)⁻¹ := fun g => by
      have : f i₂ g * f k g = 1 := Units.ext (by simpa using h₂ g)
      exact eq_inv_of_mul_eq_one_left this
    refine hinj0 i₁ i₂ (MonoidHom.ext fun b => ?_) ?_
    · simp only [MonoidHom.comp_apply, hu1, hu2]
    · intro h
      apply hk
      refine MonoidHom.ext fun b => ?_
      have h1 : f i₁ (ιB b) = 1 := by
        have := DFunLike.congr_fun h b
        simpa using this
      have h2 := hu1 (ιB b)
      rw [h1] at h2
      have h3 : (f k (ιB b))⁻¹ = 1 := h2.symm
      simpa using h3
  by_contra hne
  have hsum := congrFun hG4 k
  obtain ⟨i, hi⟩ : ∃ i, Aσ k i * σ (u i) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [hsum]
    exact Finset.sum_eq_zero fun i _ => hall i
  have hAki : Aσ k i ≠ 0 := left_ne_zero_of_mul hi
  have hui : u i ≠ 0 := fun h => hi (by rw [h, map_zero, mul_zero])
  obtain ⟨i', hi'⟩ := hcolnz k
  have hii' : i = i' := hpart i i' (fun g => by rw [mul_comm]; exact hAσrel k i hAki g)
    (hQrel i' k hi')
  subst hii'
  have hcoef : ∑ i₂, u i₂ * Qm i₂ k = u i * Qm i k := by
    rw [Finset.sum_eq_single i]
    · intro i₂ _ hi₂
      have : Qm i₂ k = 0 := by
        by_contra hQ
        exact hi₂ (hpart i₂ i (hQrel i₂ k hQ) (hQrel i k hi'))
      rw [this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hcoef] at hTk
  exact (mul_ne_zero (mul_ne_zero hui hi') hne) hTk


omit [CharP K 2] [CharP K' 2] [DecidableEq ι] in
theorem eigen_rational (hK5 : ∀ x : K, x ^ 5 = 1 → x = 1) {w : ι → K} (hw0 : w ≠ 0)
    (M : Matrix ι ι K) (μ : K') (hμ5 : μ ^ 5 = 1)
    (h : algebraMap K K' ∘ (M *ᵥ w) = μ • (algebraMap K K' ∘ w)) : μ = 1 := by
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw0 (funext hall)
  have h1 := congrFun h j
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
  have hinj : Function.Injective (algebraMap K K') := (algebraMap K K').injective
  have hwj : algebraMap K K' (w j) ≠ 0 := by simpa using hj
  have hμ : μ = algebraMap K K' ((M *ᵥ w) j / w j) := by
    rw [map_div₀, h1]
    field_simp
  have hy5 : ((M *ᵥ w) j / w j) ^ 5 = 1 := by
    apply hinj
    rw [map_pow, ← hμ, hμ5, map_one]
  rw [hμ, hK5 _ hy5, map_one]


theorem zero_class_false_N {E : Type*} [CommGroup E] (hE5 : ∀ x : E, x ^ 5 = 1) {B : Type*}
    [Group B] [Fintype B] (hB25 : Fintype.card B = 25) (ιB : B →* E)
    (ρ : E →* Matrix ι ι K) (Q : QuadraticForm K (ι → K))
    (hρQ : ∀ g v, Q (ρ g *ᵥ v) = Q v) (hK5 : ∀ x : K, x ^ 5 = 1 → x = 1)
    (σ : K' →+* K') (hσK : ∀ x : K, σ (algebraMap K K' x) = algebraMap K K' x)
    (hσ5 : ∀ y : K', y ^ 5 = 1 → σ y = y⁻¹)
    (P : GL ι K') (f : ι → (E →* K'ˣ))
    (hD : ∀ g : E, (P : Matrix ι ι K') * (ρ g).map (algebraMap K K') *
      ((P⁻¹ : GL ι K') : Matrix ι ι K') = Matrix.diagonal fun i => ((f i g : K'ˣ) : K'))
    (Qm : Matrix ι ι K') (hQs : Qmᵀ = Qm) (hQu : IsUnit Qm)
    (hQE : ∀ g : E, Qm * Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) =
      Matrix.diagonal (fun i => (((f i g : K'ˣ) : K'))⁻¹) * Qm)
    (hpolQ : ∀ v w : ι → K, algebraMap K K' (QuadraticMap.polar Q v w) =
      ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ v)) ⬝ᵥ
        Qm *ᵥ ((P : Matrix ι ι K') *ᵥ (algebraMap K K' ∘ w)))
    (hinj0 : ∀ i k, (f i).comp ιB = (f k).comp ιB → (f i).comp ιB ≠ 1 → i = k)
    {i₀ k₀ : ι} (hik : i₀ ≠ k₀) (hi₀ : (f i₀).comp ιB = 1)
    (hzero : ∀ i, (f i).comp ιB = 1 → i = i₀ ∨ i = k₀)
    (W : Submodule K (ι → K)) (hW0 : W ≠ ⊥) (hWs : ∀ x ∈ W, Q x = 0)
    (hWB : ∀ b : B, ∀ w ∈ W, ρ (ιB b) *ᵥ w ∈ W) (hne : f i₀ ≠ 1) : False := by
  classical
  set Pm : Matrix ι ι K' := (P : Matrix ι ι K') with hPm
  have hf5 : ∀ (i : ι) (g : E), ((f i g : K'ˣ) : K') ^ 5 = 1 := by
    intro i g
    have h5 := congrArg (fun x : K'ˣ => (x : K'))
      (show f i g ^ 5 = 1 by rw [← map_pow, hE5, map_one])
    simpa using h5
  have hsq : ∀ i, (∀ g : E, ((f i g : K'ˣ) : K') * ((f i g : K'ˣ) : K') = 1) → f i = 1 := by
    intro i h
    refine MonoidHom.ext fun g => ?_
    apply Units.ext
    have h1 := h g
    have h5 := hf5 i g
    set z : K' := ((f i g : K'ˣ) : K') with hz
    have : z = z ^ 5 := by
      calc z = z * (z * z) * (z * z) := by rw [h1]; ring
        _ = z ^ 5 := by ring
    rw [this, h5]
    simp
  have hQrel : ∀ i j, Qm i j ≠ 0 → ∀ g : E,
      ((f i g : K'ˣ) : K') * ((f j g : K'ˣ) : K') = 1 := fun i j hij g =>
    gram_entries f Qm hQE hij g
  have hQii : Qm i₀ i₀ = 0 := by
    by_contra h
    exact hne (hsq i₀ (hQrel i₀ i₀ h))
  obtain ⟨j₁, hj₁⟩ := exists_gram_ne_zero Qm hQu i₀
  have hrel1 := hQrel j₁ i₀ hj₁
  have hj₁zero : (f j₁).comp ιB = 1 := by
    refine MonoidHom.ext fun b => ?_
    have h1 := hrel1 (ιB b)
    have h2 : ((f i₀ (ιB b) : K'ˣ) : K') = 1 := by
      have := DFunLike.congr_fun hi₀ b
      simpa using congrArg (fun x : K'ˣ => (x : K')) this
    rw [h2, mul_one] at h1
    apply Units.ext
    simpa using h1
  have hj₁k₀ : j₁ = k₀ := by
    rcases hzero j₁ hj₁zero with h | h
    · exfalso
      rw [h] at hj₁
      exact hj₁ hQii
    · exact h
  subst hj₁k₀
  have hQki : Qm j₁ i₀ ≠ 0 := hj₁
  have hQik : Qm i₀ j₁ ≠ 0 := by
    have : Qm i₀ j₁ = Qm j₁ i₀ := by
      have := congrFun (congrFun hQs i₀) j₁
      simpa [Matrix.transpose_apply] using this.symm
    rw [this]
    exact hQki
  have hQkk : Qm j₁ j₁ = 0 := by
    by_contra h
    have hf1 : f j₁ = 1 := hsq j₁ (hQrel j₁ j₁ h)
    apply hne
    refine MonoidHom.ext fun g => ?_
    have h1 := hrel1 g
    have h2 : ((f j₁ g : K'ˣ) : K') = 1 := by rw [hf1]; rfl
    rw [h2, one_mul] at h1
    apply Units.ext
    simpa using h1
  have hrel0 : ∀ g : E, ((f j₁ g : K'ˣ) : K') * ((f i₀ g : K'ˣ) : K') = 1 := hrel1
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨u, hu⟩ : ∃ u : ι → K', u = Pm *ᵥ (algebraMap K K' ∘ w) := ⟨_, rfl⟩
  have hsupp : ∀ m, u m ≠ 0 → m = i₀ ∨ m = j₁ := by
    intro m hm
    by_contra hmm
    push Not at hmm
    have hk : (f m).comp ιB ≠ 1 := fun h => by
      rcases hzero m h with h' | h'
      · exact hmm.1 h'
      · exact hmm.2 h'
    have := support_N hE5 hB25 ιB ρ Q σ hσK hσ5 P f hD Qm hQu hQE hpolQ hinj0 W hWs hWB w hwW m hk
    rw [← hu] at this
    exact hm this
  obtain ⟨g, hg⟩ : ∃ g : E, f i₀ g ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (MonoidHom.ext hall)
  obtain ⟨lam, hlam⟩ : ∃ lam : K', lam = ((f i₀ g : K'ˣ) : K') := ⟨_, rfl⟩
  have hlam1 : lam ≠ 1 := fun h => hg (Units.ext (by rw [← hlam]; exact h))
  have hlam0 : lam ≠ 0 := by rw [hlam]; exact (f i₀ g).ne_zero
  have hlam5 : lam ^ 5 = 1 := by rw [hlam]; exact hf5 i₀ g
  have hflam : ((f j₁ g : K'ˣ) : K') = lam⁻¹ := by
    rw [hlam]
    exact eq_inv_of_mul_eq_one_left (hrel0 g)
  have h2 : (2 : K') = 0 := by exact_mod_cast CharP.cast_eq_zero K' 2
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨a, ha⟩ : ∃ a : K', a = u i₀ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : K', b = u j₁ := ⟨_, rfl⟩
  have hu_form : u = a • (Pi.single i₀ (1 : K')) + b • (Pi.single j₁ (1 : K')) := by
    funext m
    by_cases h1 : m = i₀
    · rw [h1]
      simp [ha, hik]
    · by_cases h2' : m = j₁
      · rw [h2']
        simp [hb, Ne.symm hik]
      · have : u m = 0 := by
          by_contra h
          rcases hsupp m h with h' | h'
          · exact h1 h'
          · exact h2' h'
        simp [this, h1, h2']
  have hDu : ∀ m, (Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u) m =
      ((f m g : K'ˣ) : K') * u m := fun m => Matrix.mulVec_diagonal _ _ _
  have hPinj : Function.Injective (fun v : ι → K' => Pm *ᵥ v) :=
    Matrix.mulVec_injective_iff_isUnit.2 P.isUnit
  have heig : ∀ μ : K', μ ^ 5 = 1 →
      Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u = μ • u → μ = 1 := by
    intro μ hμ5 hμ
    refine eigen_rational hK5 hw0 (ρ g) μ hμ5 ?_
    apply hPinj
    show Pm *ᵥ (algebraMap K K' ∘ (ρ g *ᵥ w)) = Pm *ᵥ (μ • (algebraMap K K' ∘ w))
    rw [weight_coord_mulVec ρ P f hD g w, ← hu, hμ, Matrix.mulVec_smul, ← hu]
  by_cases hb0 : b = 0
  · apply hlam1
    apply heig lam hlam5
    funext m
    rw [hDu]
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hm : m = i₀
    · rw [hm, ← hlam]
    · have : u m = 0 := by
        by_contra h
        rcases hsupp m h with h' | h'
        · exact hm h'
        · rw [h'] at h
          exact h (by rw [← hb]; exact hb0)
      rw [this, mul_zero, mul_zero]
  by_cases ha0 : a = 0
  · have hinv : lam⁻¹ = 1 := by
      apply heig lam⁻¹ (by rw [inv_pow, hlam5, inv_one])
      funext m
      rw [hDu]
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases hm : m = j₁
      · rw [hm, hflam]
      · have : u m = 0 := by
          by_contra h
          rcases hsupp m h with h' | h'
          · rw [h'] at h
            exact h (by rw [← ha]; exact ha0)
          · exact hm h'
        rw [this, mul_zero, mul_zero]
    exact hlam1 (inv_eq_one.1 hinv)
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ι → K, w₁ = ρ g *ᵥ w := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : ι → K, w₂ = ρ g *ᵥ w₁ := ⟨_, rfl⟩
  have hP1 : Pm *ᵥ (algebraMap K K' ∘ w₁) =
      Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u := by
    rw [hu, hw₁]
    exact weight_coord_mulVec ρ P f hD g w
  have hP2 : Pm *ᵥ (algebraMap K K' ∘ w₂) = Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ
      (Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u) := by
    rw [hw₂, weight_coord_mulVec ρ P f hD g w₁, hP1]
  obtain ⟨τ, hτ⟩ : ∃ τ : K', τ = lam + lam⁻¹ := ⟨_, rfl⟩
  have hCH : Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ
      (Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u) +
      τ • (Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u) + u = 0 := by
    funext m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.mulVec_diagonal]
    by_cases hm : u m = 0
    · rw [hm]
      ring
    · rcases hsupp m hm with h | h
      · rw [h, ← hlam, ← ha, hτ]
        linear_combination (lam ^ 2 * a + a) * h2 + a * (inv_mul_cancel₀ hlam0)
      · rw [h, hflam, ← hb, hτ]
        linear_combination (lam⁻¹ ^ 2 * b + b) * h2 + b * (mul_inv_cancel₀ hlam0)
  have hlin : algebraMap K K' ∘ w₂ + τ • (algebraMap K K' ∘ w₁) + algebraMap K K' ∘ w = 0 := by
    apply hPinj
    show Pm *ᵥ _ = Pm *ᵥ 0
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, hP2, hP1, ← hu,
      Matrix.mulVec_zero]
    exact hCH
  have hw1ne : w₁ ≠ 0 := by
    intro h
    apply hw0
    have h1 : ρ g⁻¹ *ᵥ (ρ g *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [← h1, ← hw₁, h, Matrix.mulVec_zero]
  obtain ⟨j, hj⟩ : ∃ j, w₁ j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw1ne (funext hall)
  have hlinj : ∀ m, algebraMap K K' (w₂ m) + τ * algebraMap K K' (w₁ m) +
      algebraMap K K' (w m) = 0 := fun m => by
    have := congrFun hlin m
    simpa using this
  have hτ0 : τ ≠ 0 := by
    intro h0
    have h1 : (lam + 1) ^ 2 = 0 := by
      rw [hτ] at h0
      linear_combination lam * h0 - mul_inv_cancel₀ hlam0 + lam * h2
    have h3 : lam + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    apply hlam1
    linear_combination h3 - h2
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : K, algebraMap K K' τ₀ = τ := by
    refine ⟨(w₂ j + w j) / w₁ j, ?_⟩
    have hj' : algebraMap K K' (w₁ j) ≠ 0 := by simpa using hj
    rw [map_div₀, map_add]
    have h1 := hlinj j
    field_simp
    linear_combination -h1 + (algebraMap K K' (w₂ j) + algebraMap K K' (w j)) * h2
  have hτ₀0 : τ₀ ≠ 0 := by
    intro h
    apply hτ0
    rw [← hτ₀, h, map_zero]
  have hw₂form : w₂ = τ₀ • w₁ + w := by
    funext m
    apply (algebraMap K K').injective
    have h1 := hlinj m
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hτ₀]
    linear_combination h1 - (τ * algebraMap K K' (w₁ m) + algebraMap K K' (w m)) * h2
  have hQw : Q w = 0 := hWs w hwW
  have hQw₁ : Q w₁ = 0 := by rw [hw₁, hρQ]; exact hQw
  have hQw₂ : Q w₂ = 0 := by rw [hw₂, hρQ]; exact hQw₁
  have hpol : QuadraticMap.polar Q w₁ w = 0 := by
    have h1 : Q w₂ = (τ₀ * τ₀) • Q w₁ + Q w + τ₀ • QuadraticMap.polar Q w₁ w := by
      rw [hw₂form, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul,
        QuadraticMap.polar_smul_left]
    rw [hQw₂, hQw₁, hQw, smul_zero, zero_add, zero_add, smul_eq_mul] at h1
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd h hτ₀0
    · exact h
  have hcoord := hpolQ w₁ w
  rw [hpol, map_zero, hP1, ← hu] at hcoord
  have hDu' : Matrix.diagonal (fun i => ((f i g : K'ˣ) : K')) *ᵥ u =
      (lam * a) • (Pi.single i₀ (1 : K')) + (lam⁻¹ * b) • (Pi.single j₁ (1 : K')) := by
    funext m
    rw [Matrix.mulVec_diagonal]
    by_cases h1 : m = i₀
    · rw [h1, ← hlam, ← ha]
      simp [hik]
    · by_cases h2' : m = j₁
      · rw [h2', hflam, ← hb]
        simp [Ne.symm hik]
      · have : u m = 0 := by
          by_contra h
          rcases hsupp m h with h' | h'
          · exact h1 h'
          · exact h2' h'
        simp [this, h1, h2']
  rw [hDu', hu_form] at hcoord
  have hsymm : Qm j₁ i₀ = Qm i₀ j₁ := by
    have := congrFun (congrFun hQs i₀) j₁
    simpa [Matrix.transpose_apply] using this
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one, add_dotProduct,
    smul_dotProduct, single_dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.col_apply, hQii, hQkk, hsymm] at hcoord
  have hfin : Qm i₀ j₁ * a * b * τ = 0 := by
    rw [hτ]
    linear_combination -hcoord
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hQik ha0) hb0) hτ0) hfin

end CaseN




end CFSG.RankThree.PartOne.AUTSL

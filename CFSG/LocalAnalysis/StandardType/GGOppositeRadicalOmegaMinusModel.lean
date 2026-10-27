module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusStd
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank GGOppRad GGOppRadSpU

variable {n : ℕ} {K : Type} [Field K] {b c : K}

variable (n K b c) in
@[expose] noncomputable def minusRep :
    spinGroup (quadMinus n K b c) →* Module.End K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (spinAction (quadMinus n K b c))

theorem minusRep_apply (x : spinGroup (quadMinus n K b c)) (v : Vm n K) :
    minusRep n K b c x v = spinAction (quadMinus n K b c) x v :=
  rfl

variable [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

variable (n) in
@[expose] noncomputable def minusForm : QuadForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  toQuadForm (quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)

theorem minusForm_Q (v : Vm n K) : (minusForm n hirr).Q v = quadMinus n K b c v :=
  rfl

theorem minusForm_β (u v : Vm n K) :
    (minusForm n hirr).polar.β u v = polar (quadMinus n K b c) u v :=
  rfl

theorem minusRep_Q (x : spinGroup (quadMinus n K b c)) (v : Vm n K) :
    (minusForm n hirr).Q (minusRep n K b c x v) = (minusForm n hirr).Q v :=
  map_spinAction _ x v

theorem isIsometric_minusRep : IsIsometric (minusForm n hirr).polar (minusRep n K b c) :=
  (minusForm n hirr).isIsometric_of_Q (minusRep_Q hirr)

include hirr in
theorem minusRep_injective [CharP K 2] : Function.Injective (minusRep n K b c) := by
  intro x y hxy
  refine RootCentOmega.spinAction_quadMinus_injective hirr (LinearEquiv.ext fun v => ?_)
  exact congrArg (fun f : Module.End K (Vm n K) => f v) hxy

include hirr in
theorem finite_spinGroup_quadMinus [CharP K 2] : Finite (spinGroup (quadMinus n K b c)) := by
  have : Finite (Vm n K ≃ₗ[K] Vm n K) :=
    Finite.of_injective (fun e : Vm n K ≃ₗ[K] Vm n K => (e : Vm n K → Vm n K))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  exact Finite.of_injective _ (RootCentOmega.spinAction_quadMinus_injective hirr)

theorem exists_minusRep_eq_eichler (hn : 4 ≤ n) (x y : Vm n K)
    (hx : (minusForm n hirr).Q x = 0) (hxy : (minusForm n hirr).polar.β x y = 0) :
    ∃ h : spinGroup (quadMinus n K b c), ∀ v,
      minusRep n K b c h v = (minusForm n hirr).eichler x y v := by
  have hmem : eichler (quadMinus n K b c) x y ∈ (spinAction (quadMinus n K b c)).range := by
    rw [range_spinAction_quadMinus hn hirr]
    exact eichler_mem_elementaryGroup _ x y
  obtain ⟨h, hh⟩ := hmem
  refine ⟨h, fun v => ?_⟩
  rw [minusRep_apply, hh, eichler_apply hx hxy, QuadForm.eichler_apply, minusForm_β, minusForm_β,
    minusForm_Q, polar_comm (quadMinus n K b c) v x, polar_comm (quadMinus n K b c) v y]
  module

omit [Finite K] in
theorem quadMinusPolar_eq (u v : Vm n K) :
    quadMinusPolar n K b c u v = polar (quadMinus n K b c) u v := by
  rw [polar_quadMinus, quadMinusPolar]
  ring

theorem noQuotientReflection_minusRep (hn : 4 ≤ n) :
    NoQuotientReflection (minusForm n hirr) (minusRep n K b c) := by
  intro h Z hZ a ha hQa hrefl
  have hmem : spinMatrix (quadMinus n K b c) h ∈ StatedOmega (StatedQuadMinus n K b c) := by
    rw [← range_spinMatrix_quadMinus hn hirr]
    exact ⟨h, rfl⟩
  refine not_reflection_on_quotient_of_mem_statedOmega_quadMinus n hirr hmem (Z := Z) (a := a)
    (fun z hz => ?_) (fun z hz => ?_) ?_ fun v hv => ?_
  · rw [← coe_quadMinus]
    exact hZ z hz
  · rw [quadMinusPolar_eq]
    exact ha z hz
  · rw [← coe_quadMinus]
    exact hQa
  · rw [spinMatrix_mulVec, ← coe_quadMinus, quadMinusPolar_eq]
    exact hrefl v fun z hz => by rw [minusForm_β, ← quadMinusPolar_eq]; exact hv z hz

omit [Finite K] in
theorem exists_finrank_three_quadMinus (hn : 4 ≤ n) :
    ∃ T : Submodule K (Vm n K), finrank K T = 3 ∧ ∀ x ∈ T, quadMinus n K b c x = 0 := by
  classical
  let f : Fin 3 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := fun j => Sum.inl ⟨j, by omega⟩
  have hf : Function.Injective f := fun j j' h => by
    simp only [f, Sum.inl.injEq, Fin.mk.injEq] at h
    exact Fin.ext h
  have hli : LinearIndependent K (fun j => (Pi.single (f j) (1 : K) : Vm n K)) := by
    have := (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).linearIndependent.comp f hf
    convert this using 1
    funext j
    simp
  refine ⟨Submodule.span K (Set.range fun j => (Pi.single (f j) (1 : K) : Vm n K)),
    by rw [finrank_span_eq_card hli, Fintype.card_fin], fun x hx => ?_⟩
  have hx' : ∀ a, (∀ j, a ≠ f j) → x a = 0 := by
    intro a ha
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Pi.single_eq_of_ne (ha j) _
    | zero => rfl
    | add y z _ _ hy hz => rw [Pi.add_apply, hy, hz, add_zero]
    | smul r y _ hy => rw [Pi.smul_apply, hy, smul_zero]
  rw [quadMinus_apply, hx' (.inr (.inr 0)) (fun j => by simp [f]),
    hx' (.inr (.inr 1)) (fun j => by simp [f])]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hx' (.inr (.inl i)) (fun j => by simp [f]), mul_zero]

theorem exists_spinAction_eq_of_mem_omegaGroup_minus [CharP K 2] (hn : 4 ≤ n)
    {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ omegaGroup (quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)) :
    ∃ h : spinGroup (quadMinus n K b c), spinAction (quadMinus n K b c) h = g := by
  have h1 := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) (exists_finrank_three_quadMinus hn) hg
  rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn hirr,
    ← range_spinAction_quadMinus hn hirr] at h1
  exact h1

@[expose] def mpr : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr t) => .inr (.inr t.rev)

omit [Finite K] in
theorem mpr_mpr (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) : mpr (mpr a) = a := by
  rcases a with i | i | t <;> simp [mpr]

omit [Finite K] in
theorem mpr_ne (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) : mpr a ≠ a := by
  rcases a with i | i | t
  · simp [mpr]
  · simp [mpr]
  · simp only [mpr, ne_eq, Sum.inr.injEq]
    intro h
    fin_cases t <;> simp at h

variable (b) in
@[expose] def mg : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K
  | .inr (.inr _) => b
  | _ => 1

include hirr in
theorem b_ne_zero [CharP K 2] : b ≠ 0 := by
  intro hb
  have h := CFSG.LieType.BorelTits.four_mul_sub_sq_ne_zero hirr
  rw [hb, show (4 : K) = 2 * 2 by norm_num, CharTwo.two_eq_zero] at h
  simp at h

include hirr in
theorem mg_ne_zero [CharP K 2] (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) : mg (n := n) b a ≠ 0 := by
  rcases a with i | i | t
  · exact one_ne_zero
  · exact one_ne_zero
  · exact b_ne_zero hirr

omit [Finite K] in
theorem polar_single_minus [CharP K 2] (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (v : Vm n K) :
    polar (quadMinus n K b c) (Pi.single a 1) v = mg b a * v (mpr a) := by
  classical
  rw [polar_quadMinus]
  rcases a with i | i | t
  · simp [mg, mpr, Pi.single_apply]
  · simp [mg, mpr, Pi.single_apply]
  · fin_cases t
    · simp [mg, mpr, CharTwo.two_eq_zero]
    · simp [mg, mpr, CharTwo.two_eq_zero]

omit [Finite K] in
theorem polar_sum_single_minus [CharP K 2] (w v : Vm n K) :
    polar (quadMinus n K b c) w v = ∑ a, w a * (mg b a * v (mpr a)) := by
  conv_lhs => rw [← sum_single_eq' w]
  rw [CFSG.LocalAnalysis.ComponentInitial.polar_sum_smul_left]
  simp only [polar_single_minus]
where
  sum_single_eq' (w : Vm n K) : ∑ a, w a • (Pi.single a (1 : K) : Vm n K) = w := by
    ext c
    simp [Finset.sum_apply, Pi.single_apply]

@[expose] def IsMinusLevel (M : ℕ) (ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ) : Prop :=
  (∀ a, ℓ a + ℓ (mpr a) = M) ∧ ℓ (.inr (.inr 0)) = ℓ (.inr (.inr 1))

omit [Finite K] in
theorem IsMinusLevel.plane {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (h : IsMinusLevel M ℓ) (t : Fin 2) : 2 * ℓ (.inr (.inr t)) = M := by
  have h0 := h.1 (.inr (.inr 0))
  simp only [mpr] at h0
  fin_cases t
  · simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    have : (0 : Fin 2).rev = 1 := rfl
    rw [this, ← h.2] at h0
    omega
  · simp only [Fin.mk_one, Fin.isValue]
    have : (0 : Fin 2).rev = 1 := rfl
    rw [this] at h0
    rw [← h.2]
    have h1 := h.2
    omega

omit [Finite K] in
theorem IsMinusLevel.le {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (h : IsMinusLevel M ℓ) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) : ℓ a ≤ M := by
  have := h.1 a
  omega

theorem perp_stdFlag_minus [CharP K 2] {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) {k : ℕ} (hk : k ≤ M + 1) :
    (minusForm n hirr).polar.perp (stdFlag ℓ k) = stdFlag ℓ (M + 1 - k) := by
  classical
  ext v
  constructor
  · intro hv c hc
    have hmem : (Pi.single (mpr c) (1 : K) : Vm n K) ∈ stdFlag ℓ k :=
      single_mem_stdFlag.mpr (by have := hℓ.1 c; omega)
    have h1 := hv _ hmem
    rw [minusForm_β, polar_single_minus, mpr_mpr] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mg_ne_zero hirr _)
  · intro hv w hw
    rw [minusForm_β, polar_sum_single_minus]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : k ≤ ℓ a
    · rw [hw a ha, zero_mul]
    · rw [hv (mpr a) (by have := hℓ.1 a; omega), mul_zero, mul_zero]

theorem isSelfDual_stdFlag_minus [CharP K 2] {M : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ) :
    IsSelfDual (minusForm n hirr).polar (stdFlag ℓ) (M + 1) :=
  ⟨stdFlag_mono ℓ, stdFlag_zero ℓ, fun k hk => stdFlag_eq_top fun a => by
    have := hℓ.le a
    omega, fun k hk => perp_stdFlag_minus hirr hℓ hk⟩

omit [Finite K] in
theorem quadMinus_eq_zero_of_mem_stdFlag {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) {k : ℕ} (hk : 2 * k ≤ M + 1) {v : Vm n K} (hv : v ∈ stdFlag ℓ k) :
    quadMinus n K b c v = 0 := by
  rw [quadMinus_apply, hv (.inr (.inr 0)) (by have := hℓ.plane 0; omega),
    hv (.inr (.inr 1)) (by have := hℓ.plane 1; omega)]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := hℓ.1 (.inl i)
  simp only [mpr] at this
  by_cases h1 : k ≤ ℓ (.inl i)
  · rw [hv _ h1, zero_mul]
  · rw [hv (.inr (.inl i)) (by omega), mul_zero]

theorem isTotallySingular_stdFlag_minus {M : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ) {k : ℕ}
    (hk : 2 * k ≤ M + 1) : (minusForm n hirr).IsTotallySingular (stdFlag ℓ k) :=
  fun _ hv => quadMinus_eq_zero_of_mem_stdFlag hℓ hk hv

end GGOppRadOmega

end CFSG.StandardType

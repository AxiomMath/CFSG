module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerMixing

public section

namespace CFSG.RankThree.PartOne.CTP

open Module

section Reflection

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {bar : E →+* E}

noncomputable def hermReflMap (Hf : W →ₛₗ[bar] W →ₗ[E] E) (e : W) (μ : E) : W →ₗ[E] W :=
  LinearMap.id + LinearMap.smulRight (μ • Hf e) e

theorem hermReflMap_apply (Hf : W →ₛₗ[bar] W →ₗ[E] E) (e : W) (μ : E) (y : W) :
    hermReflMap Hf e μ y = y + (μ * Hf e y) • e := by
  simp [hermReflMap]

theorem hermReflMap_isometry (Hf : W →ₛₗ[bar] W →ₗ[E] E)
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a) {e : W} {μ : E}
    (hμ : μ + bar μ + Hf e e * (μ * bar μ) = 0) (y z : W) :
    Hf (hermReflMap Hf e μ y) (hermReflMap Hf e μ z) = Hf y z := by
  rw [hermReflMap_apply, hermReflMap_apply]
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, map_mul, ← hsymm e y, RingHom.id_apply]
  linear_combination (bar (Hf e y) * Hf e z) * hμ

theorem hermReflMap_comp (Hf : W →ₛₗ[bar] W →ₗ[E] E) {e : W} {μ μ' : E}
    (hμ : μ + μ' + Hf e e * (μ * μ') = 0) (y : W) :
    hermReflMap Hf e μ' (hermReflMap Hf e μ y) = y := by
  rw [hermReflMap_apply, hermReflMap_apply, map_add, map_smul, smul_eq_mul]
  have h0 : μ * Hf e y + μ' * (Hf e y + μ * Hf e y * Hf e e) = 0 := by
    linear_combination (Hf e y) * hμ
  rw [add_assoc, ← add_smul, h0, zero_smul, add_zero]

noncomputable def hermRefl (Hf : W →ₛₗ[bar] W →ₗ[E] E) {e : W} {μ : E}
    (hμ : μ + bar μ + Hf e e * (μ * bar μ) = 0) : W ≃ₗ[E] W :=
  LinearEquiv.ofLinearMap (hermReflMap Hf e μ) (hermReflMap Hf e (bar μ))
    (LinearMap.ext fun y => hermReflMap_comp Hf (by linear_combination hμ) y)
    (LinearMap.ext fun y => hermReflMap_comp Hf hμ y)

theorem hermRefl_apply (Hf : W →ₛₗ[bar] W →ₗ[E] E) {e : W} {μ : E}
    (hμ : μ + bar μ + Hf e e * (μ * bar μ) = 0) (y : W) :
    hermRefl Hf hμ y = y + (μ * Hf e y) • e :=
  hermReflMap_apply Hf e μ y

end Reflection

section Mixing

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {bar : E →+* E}

theorem exists_hermitian_mixing (Hf : W →ₛₗ[bar] W →ₗ[E] E)
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a)
    {ρ : E} (hρ : bar ρ = ρ⁻¹) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 ≠ 1) (hρ3 : ρ ^ 3 ≠ 1)
    {u w : W} (huw : Hf u w = 0) (hw : Hf w w ≠ 0) :
    ∃ γ : W ≃ₗ[E] W, (∀ y z, Hf (γ y) (γ z) = Hf y z) ∧
      ∃ κ₁ κ₂ : E, κ₁ ≠ 0 ∧ κ₂ ≠ 0 ∧ γ w = κ₁ • w + κ₂ • u := by
  have hwu : Hf w u = 0 := by rw [← hsymm u w, huw, map_zero]
  have hbar1 : bar 1 = 1 := map_one bar
  have hc₀ : (1 + ρ) ≠ 0 := by
    intro h0
    apply hρ2
    have : ρ = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this]; norm_num
  have hN : (1 + ρ) * bar (1 + ρ) ≠ 1 := by
    intro h1
    rw [map_add, hbar1, hρ] at h1
    field_simp at h1
    have h2 : ρ ^ 2 + ρ + 1 = 0 := by linear_combination h1
    apply hρ3
    linear_combination (ρ - 1) * h2
  obtain ⟨c, hc0, hcn⟩ : ∃ c : E, c ≠ 0 ∧ c * bar c * Hf u u + Hf w w ≠ 0 := by
    by_cases h1 : 1 * bar 1 * Hf u u + Hf w w = 0
    · refine ⟨1 + ρ, hc₀, fun h2 => ?_⟩
      rw [hbar1] at h1
      have h3 : ((1 + ρ) * bar (1 + ρ) - 1) * Hf u u = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact hN (sub_eq_zero.mp h)
      · apply hw
        rw [h] at h1
        linear_combination h1
    · exact ⟨1, one_ne_zero, h1⟩
  obtain ⟨e, he⟩ : ∃ e : W, e = c • u + w := ⟨_, rfl⟩
  have hee : Hf e e = c * bar c * Hf u u + Hf w w := by
    rw [he]
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, RingHom.id_apply, huw, hwu]
    ring
  have hew : Hf e w = Hf w w := by
    rw [he]
    simp [huw]
  have hn0 : Hf e e ≠ 0 := by rw [hee]; exact hcn
  have hnbar : bar (Hf e e) = Hf e e := hsymm e e
  obtain ⟨lam, hlam1, hlam0, hlambar, hlamn⟩ : ∃ lam : E, lam ≠ 1 ∧ lam ≠ 0 ∧ bar lam = lam⁻¹ ∧
      c * bar c * Hf u u + lam * Hf w w ≠ 0 := by
    by_cases h1 : c * bar c * Hf u u + ρ * Hf w w = 0
    · refine ⟨ρ ^ 2, hρ2, pow_ne_zero 2 hρ0, by rw [map_pow, hρ, inv_pow], fun h2 => ?_⟩
      have h3 : (ρ ^ 2 - ρ) * Hf w w = 0 := by linear_combination h2 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · apply hρ1
        have h4 : ρ * (ρ - 1) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h4 with h' | h'
        · exact absurd h' hρ0
        · exact sub_eq_zero.mp h'
      · exact hw h
    · exact ⟨ρ, hρ1, hρ0, hρ, h1⟩
  have hμ : (lam - 1) / Hf e e + bar ((lam - 1) / Hf e e) +
      Hf e e * ((lam - 1) / Hf e e * bar ((lam - 1) / Hf e e)) = 0 := by
    rw [map_div₀, map_sub, map_one, hlambar, hnbar]
    field_simp
    ring
  have hk1 : 1 + (lam - 1) / Hf e e * Hf w w =
      (c * bar c * Hf u u + lam * Hf w w) / Hf e e := by
    field_simp
    rw [hee]
    ring
  refine ⟨hermRefl Hf hμ, hermReflMap_isometry Hf hsymm hμ, 1 + (lam - 1) / Hf e e * Hf w w,
    (lam - 1) / Hf e e * Hf w w * c, ?_, ?_, ?_⟩
  · rw [hk1]
    exact div_ne_zero hlamn hn0
  · exact mul_ne_zero (mul_ne_zero (div_ne_zero (sub_ne_zero.2 hlam1) hn0) hw) hc0
  · rw [hermRefl_apply, hew, he]
    module

end Mixing

section Anisotropic

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {bar : E →+* E}

theorem exists_anisotropic_of_pairing (Hf : W →ₛₗ[bar] W →ₗ[E] E)
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a) (hbar : ∃ s, bar s ≠ s) (R : Submodule E W)
    {w₀ w₁ : W} (h₀ : w₀ ∈ R) (h₁ : w₁ ∈ R) (hz : Hf w₀ w₁ ≠ 0) :
    ∃ w ∈ R, Hf w w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ t : E, t + bar t = 0 := by
    intro t
    set z := Hf w₀ w₁ with hzdef
    have h00 := hcon w₀ h₀
    have h11 := hcon w₁ h₁
    have h10 : Hf w₁ w₀ = bar z := (hsymm w₀ w₁).symm
    have hc := hcon (w₀ + (t * z⁻¹) • w₁) (R.add_mem h₀ (R.smul_mem _ h₁))
    have hexp : Hf (w₀ + (t * z⁻¹) • w₁) (w₀ + (t * z⁻¹) • w₁) =
        t * z⁻¹ * z + bar (t * z⁻¹) * bar z := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, h00, h11, h10]
      ring
    rw [hexp, ← map_mul, inv_mul_cancel_right₀ hz] at hc
    exact hc
  obtain ⟨s, hs⟩ := hbar
  have h2 : (1 : E) + 1 = 0 := by simpa using key 1
  apply hs
  linear_combination (key s) - s * h2

end Anisotropic

section Paired

open Polynomial CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

theorem exists_mixing_element_of_paired (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) {h : primaryFactors (spEnd x)}
    (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    {u w : Fin r ⊕ Fin r → K} (hu : u ∈ primaryComponent (spEnd x) (h : K[X]))
    (hw : w ∈ primaryComponent (spEnd x) (h : K[X]))
    (hind : LinearIndependent (AdjoinRoot (h : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (spEnd x) (h : K[X])), ⟨w, hw⟩]) :
    ∃ g : StatedSp r K, g * x = x * g ∧ spEnd g w = w + u := by
  obtain ⟨φ, hφ1, -⟩ := ((S.blocks hxA hx1).paired h hne).factor
  set W := primaryComponent (spEnd x) (h : K[X]) with hWdef
  set E := AdjoinRoot (h : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp h1.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set ψ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hψ
  have hψw : ψ w₀ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hψu : ψ u₀ = 0 := by
    have h1 : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hψ, LinearMap.smul_apply, h1, smul_zero]
  let γ₀ : blockGL (spEnd x) (h : K[X]) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hψu)
  refine ⟨(φ.symm γ₀ : StatedSp r K), (mem_spSupported.mp (φ.symm γ₀).2).1, ?_⟩
  have hg := hφ1 (φ.symm γ₀) w hw
  rw [MulEquiv.apply_symm_apply] at hg
  rw [← hg]
  have hγ : blockApply γ₀ w hw = w + ((ψ w₀ • u₀ : W) : Fin r ⊕ Fin r → K) := rfl
  rw [hγ, hψw, one_smul]

end Paired


section SelfDual

open Polynomial CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

theorem coe_smul_mem_of_stable {V : Type*} [AddCommGroup V] [Module K V] {T : Module.End K V}
    {a : K[X]} {Sub : Submodule K V} (hstab : ∀ s ∈ Sub, T s ∈ Sub) (c : AdjoinRoot a)
    (v : primaryComponent T a) (hv : (v : V) ∈ Sub) :
    ((c • v : primaryComponent T a) : V) ∈ Sub := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
  rw [coe_mk_smul_primaryComponent]
  exact CFSG.RankThree.PartOne.KCUnitaryMixing.aeval_apply_mem hstab g hv

theorem exists_pairing_in_component {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
    {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hself : reciprocalPolynomial a = a)
    {Sub : Submodule K V} (hstab : ∀ s ∈ Sub, (x : Module.End K V) s ∈ Sub)
    (hnd : (B.restrict Sub).Nondegenerate) {w₀ : V} (hw₀ : w₀ ∈ Sub)
    (hw₀a : w₀ ∈ primaryComponent (x : Module.End K V) a) (hw0 : w₀ ≠ 0) :
    ∃ w₁ ∈ Sub, w₁ ∈ primaryComponent (x : Module.End K V) a ∧ B w₀ w₁ ≠ 0 := by
  obtain ⟨s, hs, hBs⟩ : ∃ s ∈ Sub, B w₀ s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw0 (congrArg Subtype.val (hnd.1 ⟨w₀, hw₀⟩ fun z => hcon z z.2))
  have hsq := H.squarefree
  refine ⟨primaryProjection (x : Module.End K V) a s,
    CFSG.RankThree.PartOne.KCUnitaryMixing.aeval_apply_mem hstab _ hs,
    primaryProjection_mem hsq ha s, ?_⟩
  have h1 : B (primaryProjection (x : Module.End K V) a s) w₀ = B s w₀ := by
    rw [H.adj_spec, H.adj_primaryProjection ha, hself, primaryProjection_of_mem hsq ha hw₀a]
  rw [H.skew (primaryProjection (x : Module.End K V) a s) w₀, h1, ← H.skew s w₀]
  exact hBs

theorem eq_zero_of_trace_mul_eq_zero [Finite K] (h : K[X]) [Fact (Irreducible h)]
    (z : AdjoinRoot h) (hz : ∀ c : AdjoinRoot h, Algebra.trace K (AdjoinRoot h) (c * z) = 0) :
    z = 0 := by
  have : FiniteDimensional K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  have hnd := traceForm_nondegenerate K (AdjoinRoot h)
  refine hnd.2 z fun c => ?_
  rw [Algebra.traceForm_apply]
  exact hz c

theorem exists_mixing_element_of_selfDual (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {x : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1)
    {h : primaryFactors (spEnd x)} (hh1 : (h : K[X]) ≠ X - 1)
    (hself : reciprocalPolynomial (h : K[X]) = h) {u w : Fin r ⊕ Fin r → K}
    (hu : u ∈ spLineSpace L) (huh : u ∈ primaryComponent (spEnd x) (h : K[X])) (hu0 : u ≠ 0)
    (hw : w ∈ spLineSpace N) (hwh : w ∈ primaryComponent (spEnd x) (h : K[X])) (hw0 : w ≠ 0) :
    ∃ g : StatedSp r K, g * x = x * g ∧ ∃ w₀ ∈ spLineSpace N, w₀ ≠ 0 ∧
      ∃ u' ∈ spLineSpace L, ∃ w' ∈ spLineSpace N, u' ≠ 0 ∧ w' ≠ 0 ∧
        spEnd g w₀ = u' + w' := by
  classical
  have := S.finite
  have blocks := S.blocks hxA hx1
  obtain ⟨d, hd2, hpd, σ, hσpow, hσne, hσσ, hσroot, hσadj, hE, hbar, Hf, hsymmF, hsep,
    ⟨η, hη0, hηbar, htrace⟩, -, φ, hφ⟩ := (blocks.selfDual h hh1 hself).exists_half
  have hsymm : ∀ a b : primaryComponent (spEnd x) (h : K[X]), hE.bar (Hf a b) = Hf b a :=
    fun a b => hsymmF.eq a b
  have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
  have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
    fun a ha b hb => D.orth _ _ hne a ha b hb
  have hHf : ∀ a b : primaryComponent (spEnd x) (h : K[X]),
      (a : Fin r ⊕ Fin r → K) ∈ spLineSpace L → (b : Fin r ⊕ Fin r → K) ∈ spLineSpace N →
        Hf a b = 0 := by
    intro a b ha hb
    refine eq_zero_of_trace_mul_eq_zero (h : K[X]) (Hf a b) fun c => ?_
    rw [htrace a b c]
    exact horth _ ha _ (coe_smul_mem_of_stable hstabN (c * η) b hb)
  let R : Submodule (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X])) :=
    { carrier := {v | (v : Fin r ⊕ Fin r → K) ∈ spLineSpace N}
      add_mem' := fun {a b} ha hb => (spLineSpace N).add_mem ha hb
      zero_mem' := (spLineSpace N).zero_mem
      smul_mem' := fun c v hv => coe_smul_mem_of_stable hstabN c v hv }
  set w₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨w, hwh⟩ with hw₁
  have hw₁R : w₁ ∈ R := hw
  obtain ⟨y, hyN, hyh, hBy⟩ := exists_pairing_in_component
    (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA)) h.2 hself hstabN
    (D.nondeg (some ⟨N, hN⟩)) hw hwh hw0
  set y₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨y, hyh⟩ with hy₁
  have hy₁R : y₁ ∈ R := hyN
  have hz : Hf w₁ y₁ ≠ 0 := by
    intro h0
    apply hBy
    have h1 := htrace w₁ (η⁻¹ • y₁) 1
    have e1 : Hf w₁ (η⁻¹ • y₁) = 0 := by rw [map_smul, smul_eq_mul, h0, mul_zero]
    have e2 : ((1 * η) • (η⁻¹ • y₁) : primaryComponent (spEnd x) (h : K[X])) = y₁ := by
      rw [smul_smul, one_mul, mul_inv_cancel₀ hη0, one_smul]
    rw [e1, e2, mul_zero, map_zero] at h1
    exact h1.symm
  have hbarne : ∃ s, hE.bar s ≠ s := by
    by_contra hcon
    push Not at hcon
    refine hσne (AlgEquiv.ext fun z => ?_)
    rw [AlgEquiv.one_apply, ← hbar z]
    exact hcon z
  obtain ⟨wa, hwaR, hwa⟩ := exists_anisotropic_of_pairing Hf hsymm hbarne R hw₁R hy₁R hz
  have hρord := blocks.nontrivial (h : K[X]) h.2 hh1
  have hp3 := S.three_lt_p
  set ρ : AdjoinRoot (h : K[X]) := AdjoinRoot.root (h : K[X]) with hρdef
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one ρ
    rw [hρord] at h1
    rw [h0, zero_pow (by omega : p ≠ 0)] at h1
    exact zero_ne_one h1
  have hρ1 : ρ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hρord
    omega
  have hρ2 : ρ ^ 2 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hρord] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hρ3 : ρ ^ 3 ≠ 1 := by
    intro h2
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hρord] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hρbar : hE.bar ρ = ρ⁻¹ := (hbar ρ).trans hσroot
  set u₀ : primaryComponent (spEnd x) (h : K[X]) := ⟨u, huh⟩ with hu₀
  have huw : Hf u₀ wa = 0 := hHf u₀ wa hu hwaR
  obtain ⟨γ, hγiso, κ₁, κ₂, hκ₁, hκ₂, hγw⟩ :=
    exists_hermitian_mixing Hf hsymm hρbar hρ0 hρ1 hρ2 hρ3 huw hwa
  have hγmem : LinearMap.GeneralLinearGroup.ofLinearEquiv γ ∈ sesqUnitaryGroup Hf := by
    rw [mem_sesqUnitaryGroup]
    exact fun a b => hγiso a b
  have hg := hφ (φ.symm ⟨_, hγmem⟩) (wa : Fin r ⊕ Fin r → K) wa.2
  rw [MulEquiv.apply_symm_apply] at hg
  have hu₀ne : u₀ ≠ 0 := fun h0 => hu0 (congrArg Subtype.val h0)
  have hwane : wa ≠ 0 := fun h0 => hwa (by simp [h0])
  have hblock : blockApply (⟨LinearMap.GeneralLinearGroup.ofLinearEquiv γ, hγmem⟩ :
      sesqUnitaryGroup Hf) (wa : Fin r ⊕ Fin r → K) wa.2 =
      ((γ wa : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) := rfl
  refine ⟨(φ.symm ⟨_, hγmem⟩ : StatedSp r K), (mem_spSupported.mp (φ.symm ⟨_, hγmem⟩).2).1,
    (wa : Fin r ⊕ Fin r → K), hwaR, fun h0 => hwane (Subtype.ext h0),
    ((κ₂ • u₀ : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K),
    coe_smul_mem_of_stable hstabL κ₂ u₀ hu,
    ((κ₁ • wa : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K),
    coe_smul_mem_of_stable hstabN κ₁ wa hwaR,
    fun h0 => smul_ne_zero hκ₂ hu₀ne (Subtype.ext h0),
    fun h0 => smul_ne_zero hκ₁ hwane (Subtype.ext h0), ?_⟩
  rw [← hg, hblock, hγw, Submodule.coe_add, add_comm]

end SelfDual

end CFSG.RankThree.PartOne.CTP

module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofRigid
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofHessList

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLPow

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 psuConj psuField mem_unitaryIsom3
  psuField_mul_psuConj_mul_inv exists_psuConj_mul_psuField)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

theorem commutator_mem_of_factor {X : Type*} [Group X] (D : Subgroup X) (F : Set X)
    (hF : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁) (hFD : ∀ f ∈ F, ∀ d ∈ D, f * d * f⁻¹ ∈ D)
    {x y : X} (hx : ∃ d ∈ D, ∃ f ∈ F, x = d * f) (hy : ∃ d ∈ D, ∃ f ∈ F, y = d * f) :
    ⁅x, y⁆ ∈ D := by
  obtain ⟨d₁, hd₁, f₁, hf₁, rfl⟩ := hx
  obtain ⟨d₂, hd₂, f₂, hf₂, rfl⟩ := hy
  have e : ⁅d₁ * f₁, d₂ * f₂⁆ = d₁ * (f₁ * d₂ * f₁⁻¹) * (f₁ * f₂ * (f₂ * f₁)⁻¹) *
      (f₂ * d₁ * f₂⁻¹)⁻¹ * d₂⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e, show f₁ * f₂ * (f₂ * f₁)⁻¹ = 1 by rw [hF f₁ hf₁ f₂ hf₂, mul_inv_cancel], mul_one]
  exact mul_mem (mul_mem (mul_mem hd₁ (hFD f₁ hf₁ d₂ hd₂)) (inv_mem (hFD f₂ hf₂ d₁ hd₁)))
    (inv_mem hd₂)

theorem commute_commutator {X : Type*} [Group X] {a b z : X} (ha : Commute a z)
    (hb : Commute b z) : Commute ⁅a, b⁆ z := by
  rw [commutatorElement_def]
  exact ((ha.mul_left hb).mul_left ha.inv_left).mul_left hb.inv_left

variable {K : Type} [Field K]

theorem commutator_mem_range_conjAut [Finite K] (τ₁ τ₂ : MulAut (projectiveSL 3 K)) :
    ⁅τ₁, τ₂⁆ ∈ (conjAut 3 K).range := by
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := 3) (K := K)
  set D := (conjAut 3 K).range with hD
  set F : Set (MulAut (projectiveSL 3 K)) :=
    {x | ∃ (σ : K ≃+* K) (ε : ℕ), x = fieldAut 3 K σ * dualAut 3 K ^ ε} with hF
  have hδf : ∀ σ : K ≃+* K, Commute (dualAut 3 K) (fieldAut 3 K σ) := fun σ =>
    dualAut_mul_fieldAut σ
  have hδD : ∀ d ∈ D, dualAut 3 K * d * (dualAut 3 K)⁻¹ ∈ D := by
    rintro _ ⟨A, rfl⟩
    refine ⟨GeneralLinearGroup.inverseTranspose A, ?_⟩
    rw [dualAut_mul_conjAut, mul_inv_cancel_right]
  have hδnD : ∀ (n : ℕ), ∀ d ∈ D, dualAut 3 K ^ n * d * (dualAut 3 K ^ n)⁻¹ ∈ D := by
    intro n
    induction n with
    | zero =>
      intro d hd
      simpa using hd
    | succ n ih =>
      intro d hd
      have h1 := hδD _ (ih d hd)
      have e : dualAut 3 K ^ (n + 1) * d * (dualAut 3 K ^ (n + 1))⁻¹ =
          dualAut 3 K * (dualAut 3 K ^ n * d * (dualAut 3 K ^ n)⁻¹) * (dualAut 3 K)⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact h1
  have hfD : ∀ (σ : K ≃+* K), ∀ d ∈ D, fieldAut 3 K σ * d * (fieldAut 3 K σ)⁻¹ ∈ D := by
    rintro σ _ ⟨A, rfl⟩
    exact ⟨_, (hfc σ A).symm⟩
  have hmem : ∀ τ : MulAut (projectiveSL 3 K), ∃ d ∈ D, ∃ x ∈ F, τ = d * x := by
    intro τ
    obtain ⟨A, σ, ε, -, hA⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 τ
    exact ⟨conjAut 3 K A, ⟨A, rfl⟩, fieldAut 3 K σ * dualAut 3 K ^ ε, ⟨σ, ε, rfl⟩,
      by rw [hA, mul_assoc]⟩
  refine commutator_mem_of_factor D F ?_ ?_ (hmem τ₁) (hmem τ₂)
  · rintro _ ⟨σ, ε, rfl⟩ _ ⟨τ, η, rfl⟩
    have h1 : Commute (dualAut 3 K ^ ε) (fieldAut 3 K τ) := (hδf τ).pow_left ε
    have h2 : Commute (dualAut 3 K ^ η) (fieldAut 3 K σ) := (hδf σ).pow_left η
    have h3 : fieldAut 3 K σ * fieldAut 3 K τ = fieldAut 3 K τ * fieldAut 3 K σ := by
      rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
    calc fieldAut 3 K σ * dualAut 3 K ^ ε * (fieldAut 3 K τ * dualAut 3 K ^ η)
        = fieldAut 3 K σ * (dualAut 3 K ^ ε * fieldAut 3 K τ) * dualAut 3 K ^ η := by group
      _ = fieldAut 3 K σ * fieldAut 3 K τ * (dualAut 3 K ^ ε * dualAut 3 K ^ η) := by
          rw [h1.eq]
          group
      _ = fieldAut 3 K τ * fieldAut 3 K σ * (dualAut 3 K ^ η * dualAut 3 K ^ ε) := by
          rw [h3, ← pow_add, ← pow_add, add_comm]
      _ = fieldAut 3 K τ * (dualAut 3 K ^ η * fieldAut 3 K σ) * dualAut 3 K ^ ε := by
          rw [h2.eq]
          group
      _ = fieldAut 3 K τ * dualAut 3 K ^ η * (fieldAut 3 K σ * dualAut 3 K ^ ε) := by group
  · rintro _ ⟨σ, ε, rfl⟩ d hd
    have e : fieldAut 3 K σ * dualAut 3 K ^ ε * d * (fieldAut 3 K σ * dualAut 3 K ^ ε)⁻¹ =
        fieldAut 3 K σ * (dualAut 3 K ^ ε * d * (dualAut 3 K ^ ε)⁻¹) * (fieldAut 3 K σ)⁻¹ := by
      group
    rw [e]
    exact hfD σ _ (hδnD ε d hd)

variable {p f : ℕ} {π : Bool}

theorem exists_conjM'_eq_commutator (hπ : π = false → UnitaryFieldData p f K)
    (hK : PiField π p f K) (hq2 : 2 < p ^ f) (τ₁ τ₂ : MulAut (projImage (slPi π 3 (p ^ f) K))) :
    ∃ (g : GL (Fin 3) K) (hg : g ∈ glPi π 3 (p ^ f) K), ⁅τ₁, τ₂⁆ = Res8Hess.conjM' hπ hg := by
  have := hK.finite
  cases π
  ·
    have h := hK.unitary
    set Φ := psuEquivUnitary h with hΦ
    have hmem : ∀ τ : MulAut (unitaryPSU h 3),
        ∃ d ∈ (psuConj h).range, ∃ x ∈ Set.range (psuField h), τ = d * x := by
      intro τ
      obtain ⟨A, σ, hA⟩ := exists_psuConj_mul_psuField hq2 τ
      exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hA⟩
    have hc : ⁅MulAut.congr Φ τ₁, MulAut.congr Φ τ₂⁆ ∈ (psuConj h).range := by
      refine commutator_mem_of_factor (psuConj h).range (Set.range (psuField h)) ?_ ?_
        (hmem _) (hmem _)
      · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
        rw [← map_mul, ← map_mul, ringAut_mul_comm K σ τ]
      · rintro _ ⟨σ, rfl⟩ _ ⟨A, rfl⟩
        exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
    obtain ⟨A, hA⟩ := hc
    have hAg : (A : GL (Fin 3) K) ∈ glPi false 3 (p ^ f) K := by
      rw [mem_glPi_false h]
      exact mem_unitaryIsom3.mp A.2
    refine ⟨A, hAg, (MulAut.congr Φ).injective ?_⟩
    rw [map_commutatorElement, ← hA, L3PGL.congr_conjM'_false h hπ hAg]
  ·
    set Φ := pslEquivProjective (p ^ f) K with hΦ
    obtain ⟨A, hA⟩ := commutator_mem_range_conjAut (MulAut.congr Φ τ₁) (MulAut.congr Φ τ₂)
    refine ⟨A, mem_glPi_true _ _, (MulAut.congr Φ).injective ?_⟩
    rw [map_commutatorElement, ← hA, L3PGL.congr_conjM'_true hπ (mem_glPi_true _ _)]

theorem comm_of_commute_plane (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {y s : GL (Fin 3) K}
    (hy : y ∈ glPi π 3 (p ^ f) K) (hy3 : Type123 π (p ^ f) K y 3)
    (hsSL : s ∈ slPi π 3 (p ^ f) K) (hsH : s ∈ glPi π 3 (p ^ f) K)
    (hsZ : s ∉ StatedScalars (Fin 3) K) (hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K)
    (hys : y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K)
    {τ₁ τ₂ : MulAut (projImage (slPi π 3 (p ^ f) K))}
    (h1s : Commute τ₁ (Res8Hess.conjM' hπ hsH)) (h1y : Commute τ₁ (Res8Hess.conjM' hπ hy))
    (h2s : Commute τ₂ (Res8Hess.conjM' hπ hsH)) (h2y : Commute τ₂ (Res8Hess.conjM' hπ hy))
    {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : ⁅τ₁, τ₂⁆ ^ n = 1) : τ₁ * τ₂ = τ₂ * τ₁ := by
  obtain ⟨g, hg, hζ⟩ := exists_conjM'_eq_commutator hπ hK hq2 τ₁ τ₂
  have hgs := commute_commutator h1s h2s
  have hgy := commute_commutator h1y h2y
  rw [hζ] at hgs hgy hτn
  have h1 := L3PGL.conjM'_eq_one hπ hK hq hq2 hy hy3 hsSL hsH hsZ hs3 hys hg hgs.eq hgy.eq hn hτn
  rw [← hζ] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem conjM'_eq_one_hess (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hc : (cycThree : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi π 3 (p ^ f) K)
    {a : GL (Fin 3) K} (ha : a ∈ glPi π 3 (p ^ f) K)
    (had : Res8Hess.conjM' hπ ha * Res8Hess.conjM' hπ hd =
      Res8Hess.conjM' hπ hd * Res8Hess.conjM' hπ ha)
    (hac : Res8Hess.conjM' hπ ha * Res8Hess.conjM' hπ hc =
      Res8Hess.conjM' hπ hc * Res8Hess.conjM' hπ ha)
    {n : ℕ} (hn : ¬ 3 ∣ n) (han : Res8Hess.conjM' hπ ha ^ n = 1) :
    Res8Hess.conjM' hπ ha = 1 := by
  have hcd := L3PGL.mk_comm_of_conjM'_comm hπ hK hq hq2 ha hd had
  have hcc := L3PGL.mk_comm_of_conjM'_comm hπ hK hq hq2 ha hc hac
  have hpow : ProjGenLinGroup.mk a ^ n = 1 := by
    refine Sec13.eq_one_of_conj_eq_self hK hq hq2 fun x hx => ?_
    have h1 := L3PGL.coe_conjM'_pow hπ ha n ⟨x, hx⟩
    rw [han, MulAut.one_apply] at h1
    exact h1.symm
  have hord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk a)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn)
  have h1 := L3PGL.eq_one_of_comm_d_c hτ hτ1 L3PGL.coe_cycThree_eq_heisC hcd hcc hord
  ext m
  rw [Res8Hess.coe_conjM', h1, MulAut.one_apply]
  group

theorem comm_of_commute_hess (hπ : π = false → UnitaryFieldData p f K) (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hc : (cycThree : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi π 3 (p ^ f) K)
    {τ₁ τ₂ : MulAut (projImage (slPi π 3 (p ^ f) K))}
    (h1d : Commute τ₁ (Res8Hess.conjM' hπ hd)) (h1c : Commute τ₁ (Res8Hess.conjM' hπ hc))
    (h2d : Commute τ₂ (Res8Hess.conjM' hπ hd)) (h2c : Commute τ₂ (Res8Hess.conjM' hπ hc))
    {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : ⁅τ₁, τ₂⁆ ^ n = 1) : τ₁ * τ₂ = τ₂ * τ₁ := by
  obtain ⟨g, hg, hζ⟩ := exists_conjM'_eq_commutator hπ hK hq2 τ₁ τ₂
  have hgd := commute_commutator h1d h2d
  have hgc := commute_commutator h1c h2c
  rw [hζ] at hgd hgc hτn
  have h1 := conjM'_eq_one_hess hπ hK hq hq2 hτ hτ1 hc hd hg hgd.eq hgc.eq hn hτn
  rw [← hζ] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end CFSG.RankThree.PartTwo.Sec14.L3PGLPow

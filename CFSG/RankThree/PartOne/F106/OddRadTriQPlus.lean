module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusCentralizers
public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.RankThree.PartOne.F106.OddRadSL2
public import CFSG.RankThree.PartOne.F106.OddRadTools

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold
open scoped commutatorElement

set_option linter.unusedSectionVars false

theorem oddRad_D4_qplus {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq : 5 ∣ 2 ^ f + 1) (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hx : orderOf x = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(Subgroup.centralizer {x})))) := by
  classical
  have hp5 : (5 : ℕ).Prime := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (5 : ℕ).Prime := ⟨hp5⟩
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hq
    omega
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := f * 3) (by omega)
      (by rw [hK, pow_mul])
  have : Fintype K := Fintype.ofFinite K
  let K₂ := FiniteField.Extension K 2 2
  let ι₀ : K →+* K₂ := algebraMap K K₂
  have : CharP K₂ 2 := charP_of_injective_algebraMap ι₀.injective 2
  have hK₂ : Nat.card K₂ = (2 ^ f) ^ 6 := by
    rw [FiniteField.natCard_extension, hK]
    ring
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by rw [hK₂]; positivity)
  let σ₂ : K₂ ≃+* K₂ := RingEquiv.ofBijective (iterateFrobenius K₂ 2 (4 * f))
    ⟨(iterateFrobenius K₂ 2 (4 * f)).injective,
      Finite.surjective_of_injective (iterateFrobenius K₂ 2 (4 * f)).injective⟩
  have hσ₂ : ∀ c, σ₂ c = c ^ ((2 ^ f) ^ 4) := fun c => by
    show iterateFrobenius K₂ 2 (4 * f) c = _
    rw [iterateFrobenius_def, ← pow_mul]
    congr 1
    ring
  let τ : K₂ ≃+* K₂ := RingEquiv.ofBijective (iterateFrobenius K₂ 2 (3 * f))
    ⟨(iterateFrobenius K₂ 2 (3 * f)).injective,
      Finite.surjective_of_injective (iterateFrobenius K₂ 2 (3 * f)).injective⟩
  have hτ : ∀ c, τ c = c ^ ((2 ^ f) ^ 3) := fun c => by
    show iterateFrobenius K₂ 2 (3 * f) c = _
    rw [iterateFrobenius_def, ← pow_mul]
    congr 1
    ring
  obtain ⟨-, -, ⟨g, hg, hzg⟩, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow 2 f
    Nat.prime_two hf K K₂ hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, hΓ, -, -, -, hsyl⟩ := hall g hg hzg
  obtain ⟨⟨S, hS⟩, -⟩ := hsyl 5 hp5 (by norm_num) hq
  have : Finite (ModGL TwistTag.D4.tag K₂) := finite_modGL
  have hord5 := factorization_eq_of_sylow_le (p := 5)
    (inf_le_right : graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
      trialityConjImage K σ.toRingHom g ≤ trialityConjImage K σ.toRingHom g) S hS
  set Γ := trialityConjImage K σ.toRingHom g with hΓdef
  have hTΓ : graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ Γ ≤ Γ := inf_le_right
  let ψ : ModGL TwistTag.D4.tag K →* ModGL TwistTag.D4.tag K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂))
  have hψ : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := TwistTag.D4.tag) _)
  let ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ModGL TwistTag.D4.tag K₂ :=
    ψ.comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
  have hι : Function.Injective ι := hψ.comp Subtype.val_injective
  have hrange : ι.range = Γ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hιx : ι x ∈ Γ := hrange ▸ ⟨x, rfl⟩
  have hιxM : (ι x) ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    rw [← map_pow, this, map_one]
  obtain ⟨γ, hγΓ, hγ⟩ := K133H.exists_conj_le_of_sylow (p := 5) (Y := Γ)
    (H := graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ Γ) (A := Subgroup.zpowers (ι x)) hTΓ
    (Subgroup.zpowers_le.2 hιx)
    (fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hιxM, one_zpow])
    hord5
  have hx'T : γ * ι x * γ⁻¹ ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ Γ :=
    hγ (Subgroup.mem_map.2 ⟨_, Subgroup.mem_zpowers _, rfl⟩)
  have hord : orderOf (γ * ι x * γ⁻¹) = 5 := by
    rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
      orderOf_injective _ (MulAut.conj γ).injective, orderOf_injective _ hι, hx]
  have h1 := card_radical_residual_of_embedding ι hι x
  rw [hrange] at h1
  have h2 := card_radical_residual_conj Γ hγΓ (ι x)
  rw [h1, ← h2]
  refine odd_card_radical_residual_of_dichotomy (Γ ⊓ Subgroup.centralizer {γ * ι x * γ⁻¹}) ?_
  obtain ⟨-, -, -, -, -, -, a, -, hcases⟩ := triality_qplus_fixed_root_centralizers 2 f
    Nat.prime_two hf K K₂ hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ hτ g hg hzg 5 hp5 (by norm_num) hq
    (γ * ι x * γ⁻¹) hx'T hord
  rcases hcases with ⟨-, hXeq⟩ | ⟨α, hαr, -, -, D, Q, R, hD, hQ, hR, hRq, hDD, -, -, -, -, hw⟩
  · left
    rw [hXeq]
    intro u hu v hv
    exact SteinbergBT.TrialityPlane.mul_comm_of_mem_torusGroup'
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hu).1).1.1
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hv).1).1.1
  · right
    obtain ⟨v₀, hv₀, b, hO⟩ := TwistTag.D4.exists_diagramOrbit_eq hαr
    have hOset : (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
        fixedOrbitImage TwistTag.D4 v₀ b := by
      rw [hO, Finset.coe_image]
      rfl
    obtain ⟨hinj, hrange, P, hP, -⟩ := hw v₀ hv₀ b hOset.symm
    have hRQ : R ≤ Q := by
      rw [hR]
      exact inf_le_left
    obtain ⟨e⟩ := nonempty_mulEquiv_of_comap_eq_conjSL hinj (hrange.symm ▸ hRQ) hP
    have h4F : 4 ≤ Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) := by
      rcases foldedD4_cases b with rfl | rfl
      · rw [natCard_orbitFieldFixed_zero Nat.prime_two hK hK₂ hσ₂ hτ]
        exact hq4.trans (Nat.le_self_pow (by norm_num) _)
      · rw [natCard_orbitFieldFixed_one Nat.prime_two hf hK hσ₂ hτ σ.toRingHom hσ]
        exact hq4
    have : Finite (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) := Subtype.finite
    obtain ⟨hs, hp⟩ := simple_perfect_of_mulEquiv_SL2 h4F e
    refine ⟨R, ?_, hs, hp⟩
    rw [← hD]
    exact hDD

end CFSG.RankThree.PartOne.F106

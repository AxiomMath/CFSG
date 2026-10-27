module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentRank
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups


theorem uc22d4_centShape_qplus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrq : r ∣ ℓ ^ f + 1)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hx : orderOf x = r) :
    UC22D4CentShape ℓ (ℓ ^ f)
      (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hPx : IsPGroup r (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨K₂, _, _, σ₂, τ, g, hK₂, hσ₂, hτ, hg, hzg⟩ := exists_qplus_setting hℓ hf hK σ hσ
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, -, -, -, ⟨eT⟩, -⟩ := hall g hg hzg
  obtain ⟨u, -, hrange, hPT⟩ := exists_realization_le_torus hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg hr hr3
    hrq hPx
  set F := trialityRealization (σ := σ) (u * g) with hFdef
  have hF : Function.Injective F := trialityRealization_injective _
  have hFx := hPT x (Subgroup.mem_zpowers x)
  have hFxp : orderOf (F x) = r := by rw [orderOf_injective F hF x, hx]
  obtain ⟨-, -, hL0, hL1, hfix0, hfix1, a, -, hcase⟩ :=
    triality_qplus_fixed_root_centralizers ℓ f hℓ hf K K₂ hK hK₂ σ.toRingHom hσ σ₂ hσ₂ τ hτ
      g hg hzg r hr hr3 hrq (F x) hFx hFxp
  have hmap := map_centralizer_singleton_of_injective hF hrange x
  set C := centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) with hCdef
  rcases hcase with ⟨-, hDT⟩ | ⟨α, hα, -, -, D, Q, R, hDdef, -, hRdef, hRq, hcomm, hZD, hZH,
    -, -, hall'⟩
  ·
    have hmapC : C.map F = trialityConjImage K σ.toRingHom g ⊓ centralizer {F x} := hmap
    have hcommT : ∀ y z : (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
        trialityConjImage K σ.toRingHom g : Subgroup (ModGL TwistTag.D4.tag K₂)),
        y * z = z * y := fun y z => eT.injective (by rw [map_mul, map_mul, mul_comm])
    left
    intro y hy z hz
    have hyT : F y ∈ (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
        trialityConjImage K σ.toRingHom g : Subgroup (ModGL TwistTag.D4.tag K₂)) := by
      rw [← hDT, ← hmapC]
      exact ⟨y, hy, rfl⟩
    have hzT : F z ∈ (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
        trialityConjImage K σ.toRingHom g : Subgroup (ModGL TwistTag.D4.tag K₂)) := by
      rw [← hDT, ← hmapC]
      exact ⟨z, hz, rfl⟩
    apply hF
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hcommT ⟨F y, hyT⟩ ⟨F z, hzT⟩)
  ·
    have hmapC : C.map F = trialityConjImage K σ.toRingHom g ⊓ centralizer {F x} := hmap
    obtain ⟨w, hw, b, hb⟩ := TwistTag.D4.exists_diagramOrbit_eq hα
    have hfo : fixedOrbitImage TwistTag.D4 w b = ↑(TwistTag.D4.diagramOrbit α) := by
      rw [hb, Finset.coe_image]
      rfl
    obtain ⟨hιinj, hιrange, P, hcomap, -, -⟩ := hall' w hw b hfo
    have hRQ : R ≤ (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b).range := by
      rw [hRdef, ← hιrange]
      exact inf_le_left
    have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
        (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
          (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) := by
      intro A B h
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      have h1 := congrArg (fun X : SL2 (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) =>
        (X : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b)) i j) h
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] at h1
      exact (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
        (orbitField TwistTag.D4 K₂ σ₂.toRingHom b)).injective h1
    have hPinj : Function.Injective (CFSG.RankThree.Classical.conjSL P) := fun A B h => by
      have h1 := congrArg (CFSG.RankThree.Classical.conjSL P⁻¹) h
      rwa [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul,
        inv_mul_cancel, CFSG.RankThree.Classical.conjSL_one,
        CFSG.RankThree.Classical.conjSL_one] at h1
    have hRmap : (R.comap (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b)).map
        (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) = R := by
      rw [Subgroup.map_comap_eq]
      exact inf_of_le_right hRQ
    let eR : SL2 (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) ≃* R :=
      ((((MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)).trans
        (MulEquiv.subgroupCongr hcomap.symm)).trans
          (Subgroup.equivMapOfInjective _ _ hιinj)).trans (MulEquiv.subgroupCongr hRmap)
    have hmapcomm : (⁅C, C⁆ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map F =
        R := by
      rw [Subgroup.map_commutator, hmapC, ← hDdef, hcomm]
    let eD : (⁅C, C⁆ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃* R :=
      (Subgroup.equivMapOfInjective _ F hF).trans (MulEquiv.subgroupCongr hmapcomm)
    rcases foldedD4_cases b with rfl | rfl
    ·
      have hcard : Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, by decide⟩) =
          ℓ ^ (3 * f) := by
        rw [natCard_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ, ← pow_mul, mul_comm]
      have hle : ⁅C, C⁆ ≤ C := commutator_le_self' C
      refine Or.inr (Or.inr (Or.inr ?_))
      have h3 := uc22d4_le_pRank_of_sl2 (m := 3 * f) hℓ hcard hle (eD.trans eR.symm)
      omega
    ·
      refine Or.inr (Or.inr (Or.inl ?_))
      exact ⟨orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨1, by decide⟩, inferInstance,
        inferInstance, hfix1, ⟨eD.trans eR.symm⟩⟩


end CFSG.LocalAnalysis.UniquenessCase.UC22

module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_15

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_6
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.6) -/


private theorem theorem_13_6_theorem_13_5_hypothesis_of_core
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H P C : Subgroup G)
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (hH : H = P ⊔ C)
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hζ0 : ζ0 ∈ S1)
    (hlam : lam ∈ S1)
    (hζ0_ne_lam : ζ0 ≠ lam)
    (hvirt : Theory.Character.IsVirtualCharacter lamτ)
    (ha : (1 : ℂ) = Section1.scalarProduct G (τS (lam - ζ0)) lamτ)
    (horth : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      ζ ≠ ζ0 → ζ ≠ lam →
        Section1.scalarProduct G (τS (ζ - ζ0)) lamτ = 0) :
    theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ) := by
  exact ⟨hH, hS1, hζ0, hlam, hζ0_ne_lam, hvirt, ha, horth⟩

public theorem theorem_13_6_exists_nonkernelInducedFamily
    {G : Type u}
    [Group G]
    [Finite G]
    (M H K : Subgroup G)
    (hHM : H ≤ M)
    (hKH : K ≤ H) :
    ∃ S : Finset (Section1.ClassFunction M),
      nonkernelInducedFamily M H K S := by
  exact exists_nonkernelInducedFamily M H K hHM hKH

private theorem theorem_13_6_nonkernelInducedFamily_pairwise_orthogonal
    {G : Type u}
    [Group G]
    [Finite G]
    (M H K : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (hS : nonkernelInducedFamily M H K S)
    (hHnormal : (H.subgroupOf M).Normal) :
    ∀ ζ : Section1.ClassFunction M, ζ ∈ S →
      ∀ η : Section1.ClassFunction M, η ∈ S → ζ ≠ η →
        Section1.scalarProduct M ζ η = 0 := by
  classical
  letI : (H.subgroupOf M).Normal := hHnormal
  intro ζ hζ η hη hneq
  rcases (hS.2.2 ζ).mp hζ with ⟨θζ, hθζ, _hθζnotker, hζeq⟩
  rcases (hS.2.2 η).mp hη with ⟨θη, hθη, _hθηnotker, hηeq⟩
  rcases hθζ with ⟨nζ, ρζ, hρζ, hθζeq⟩
  rcases hθη with ⟨nη, ρη, hρη, hθηeq⟩
  rw [hζeq, hηeq, hθζeq, hθηeq]
  refine Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
    (H.subgroupOf M) ρζ.character ρζ ρη rfl hρζ hρη ?_
  intro i hconj
  apply hneq
  rw [hζeq, hηeq, hθζeq, hθηeq]
  exact Section1.proposition_1_5_c_conjugate_orbit_canonical
    (H.subgroupOf M) ρη ρζ.character i hconj

private theorem theorem_13_6_conjugateCharacter_inducedCF
    {G : Type u}
    [Group G]
    [Finite G]
    (H : Subgroup G)
    [Finite H]
    (theta : Section1.ClassFunction H) :
    Section1.conjugateCharacter (Section1.inducedCF H theta) =
      Section1.inducedCF H (Section1.conjugateCharacter theta) := by
  classical
  funext g
  unfold Section1.conjugateCharacter Section1.inducedCF Section1.inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0))
        =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by
          simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
          rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then
          (Section1.conjugateCharacter theta) ⟨x * g * x⁻¹, hx⟩ else 0) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hmem : x * g * x⁻¹ ∈ H
          · simp [hmem]
            rfl
          · simp [hmem]

public theorem theorem_13_6_nonkernelInducedFamily_conjugate_mem
    {G : Type u}
    [Group G]
    [Finite G]
    (M H K : Subgroup G)
    (S : Finset (Section1.ClassFunction M))
    (hS : nonkernelInducedFamily M H K S)
    {χ : Section1.ClassFunction M}
    (hχ : χ ∈ S) :
    Section1.conjugateCharacter χ ∈ S := by
  rcases hS with ⟨_hHM, _hKH, hS⟩
  rcases (hS χ).mp hχ with ⟨θ, hθirr, hθnotker, hχeq⟩
  refine (hS (Section1.conjugateCharacter χ)).mpr ?_
  refine ⟨Section1.conjugateCharacter θ,
    Section1.isIrreducibleCharacterOnGroup_conjugateCharacter hθirr, ?_, ?_⟩
  · intro hkerbar
    apply hθnotker
    intro a
    have h := hkerbar a
    have hstar := congrArg star h
    simpa [Section1.conjugateCharacter, Section1.degree] using hstar
  · rw [hχeq, theorem_13_6_conjugateCharacter_inducedCF (H.subgroupOf M) θ]

private theorem theorem_13_6_subgroupInKernel_inducedCF_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (H A : Subgroup G)
    [Finite H]
    [hA : A.Normal]
    (hAH : A ≤ H)
    (θ : Section1.ClassFunction H)
    (hθker : Section1.subgroupInKernel' θ (A.subgroupOf H)) :
    Section1.subgroupInKernel' (Section1.inducedCF H θ) A := by
  classical
  intro a
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hindex : (Subgroup.index H : ℂ) * Nat.card H = Nat.card G := by
    exact_mod_cast H.index_mul_card
  have hxA : ∀ x : G, x * (a : G) * x⁻¹ ∈ A := by
    intro x
    simpa using hA.conj_mem (a : G) a.2 x
  have hxH : ∀ x : G, x * (a : G) * x⁻¹ ∈ H :=
    fun x => hAH (hxA x)
  have hsum :
      (∑ x : G,
          if hx : x * (a : G) * x⁻¹ ∈ H then
            θ ⟨x * (a : G) * x⁻¹, hx⟩
          else
            0) = ∑ _x : G, Section1.degree θ := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    rw [dif_pos (hxH x)]
    exact hθker ⟨⟨x * (a : G) * x⁻¹, hxH x⟩,
      Subgroup.mem_subgroupOf.mpr (hxA x)⟩
  calc
    Section1.inducedCF H θ a
        = (Nat.card H : ℂ)⁻¹ * ((Nat.card G : ℂ) * Section1.degree θ) := by
          unfold Section1.inducedCF Section1.inducedClassFunction
          rw [hsum]
          simp [Finset.card_univ]
    _ = ((Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ)) * Section1.degree θ := by
          ring
    _ = (Subgroup.index H : ℂ) * Section1.degree θ := by
          apply congrArg (fun z => z * Section1.degree θ)
          rw [← hindex]
          field_simp [hcardH]
    _ = Section1.degree (Section1.inducedCF H θ) := by
          rw [Section1.degree_inducedClassFunction H θ]

public theorem theorem_13_6_lambda_inducedFromNonkernel_H_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (_lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hlamS : lam ∈ Sfam)
    (hH : H = P ⊔ C)
    (hlinear : inducedFromLinearCharacterForSection13 Smax H lam) :
    ∃ θ : Section1.ClassFunction (H.subgroupOf Smax),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ¬ Section1.subgroupInKernel' θ
          ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)) ∧
        lam = Section1.inducedCF (H.subgroupOf Smax) θ := by
  rcases hlinear with ⟨_hHS, θ, hθirr, _hθdeg, hlam_ind⟩
  refine ⟨θ, hθirr, ?_, hlam_ind⟩
  intro hθker
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨_hPSmax, hPNormal, _hPnil, _hPHall⟩, _hmax⟩
  letI : (P.subgroupOf Smax).Normal := hPNormal
  have hPHsub : P.subgroupOf Smax ≤ H.subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ H
    rw [hH]
    exact (show P ≤ P ⊔ C from le_sup_left)
      (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hlamPker : Section1.subgroupInKernel' lam (P.subgroupOf Smax) := by
    rw [hlam_ind]
    exact theorem_13_6_subgroupInKernel_inducedCF_of_source
      (H.subgroupOf Smax) (P.subgroupOf Smax) hPHsub θ hθker
  rcases (hSfam.2.2 lam).1 hlamS with
    ⟨θPU, hθPUirr, hθPUnotker, hlamPU⟩
  have hPPUsub : P.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact (show P ≤ P ⊔ U from le_sup_left)
      (by simpa [Subgroup.mem_subgroupOf] using hx)
  have hPUnormal : ((P ⊔ U).subgroupOf Smax).Normal := by
    rcases hDercomp with ⟨_hPDer, _hUDer, hDer_eq, _hdisj⟩
    have hDnormal : ((ambientDerivedSubgroup Smax).subgroupOf Smax).Normal := by
      simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
    simpa [← hDer_eq] using hDnormal
  letI : ((P ⊔ U).subgroupOf Smax).Normal := hPUnormal
  have hIndPUker : Section1.subgroupInKernel'
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU)
      (P.subgroupOf Smax) := by
    rw [← hlamPU]
    exact hlamPker
  rcases hθPUirr with ⟨nPU, ρPU, _hρPUirr, hθPUeq⟩
  have hθPUker : Section1.subgroupInKernel' θPU
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) := by
    rw [hθPUeq]
    exact (Section1.proposition_1_6_a
      ((P ⊔ U).subgroupOf Smax) (P.subgroupOf Smax) hPPUsub ρPU).mpr
        (by simpa [hθPUeq] using hIndPUker)
  exact hθPUnotker hθPUker

public theorem theorem_13_6_mem_nonkernelInducedFamily_of_hypothesis_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    lam ∈ S1 := by
  rcases h6hyp with ⟨hH, _hlamIrr, _hlamDegree, hlinear, _hlamImage⟩
  rcases theorem_13_6_lambda_inducedFromNonkernel_H_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      lam lamτ p q u v c d hsource hlamS hH hlinear with
    ⟨θH, hθHirr, hθHnotker, hLamInd⟩
  exact (hS1.2.2 lam).2 ⟨θH, hθHirr, hθHnotker, hLamInd⟩

public theorem theorem_13_6_lambda_mem_S1_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ S1 : Finset (Section1.ClassFunction Smax),
      nonkernelInducedFamily Smax H P S1 ∧
        lam ∈ S1 := by
  rcases h6hyp with ⟨hH, hlam_irred, hlam_deg, hlinear, hlamτ_eq⟩
  rcases hlinear with ⟨hHS, θ, hθirr, hθdeg, hlam_ind⟩
  have hPH : P ≤ H := by
    intro x hxP
    rw [hH]
    exact (show P ≤ P ⊔ C from le_sup_left) hxP
  rcases theorem_13_6_exists_nonkernelInducedFamily Smax H P hHS hPH with
    ⟨S1, hS1⟩
  have h6hyp' : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u :=
    ⟨hH, hlam_irred, hlam_deg, ⟨hHS, θ, hθirr, hθdeg, hlam_ind⟩, hlamτ_eq⟩
  have hlamS1 : lam ∈ S1 :=
    theorem_13_6_mem_nonkernelInducedFamily_of_hypothesis_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS h6hyp' S1 hS1
  exact ⟨S1, hS1, hlamS1⟩

private theorem theorem_13_6_lamTau_virtual_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    Theory.Character.IsVirtualCharacter lamτ := by
  rcases h6hyp with ⟨_hH, _hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hspan : Section5.integerSpan Sfam lam :=
    Section5.integerSpan_of_mem Sfam hlamS
  have hvirt : Theory.Character.IsVirtualCharacter (τ1 lam) :=
    hcoh.2.1 lam hspan
  simpa [hlamτ_eq] using hvirt

private theorem theorem_13_6_tauS_lambda_scalarProduct_self_one_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    Section1.scalarProduct G (τ1 lam) lamτ = 1 := by
  rcases h6hyp with ⟨_hH, hlam_irred, _hlam_deg, _hlam_linear, hlamτ_eq⟩
  have hselfS : Section1.scalarProduct Smax lam lam = 1 :=
    section13_scalarProduct_self_of_irreducibleCharacter hlam_irred
  have hselfTau : Section1.scalarProduct G (τ1 lam) (τ1 lam) = 1 := by
    calc
      Section1.scalarProduct G (τ1 lam) (τ1 lam) =
          Section1.scalarProduct Smax lam lam :=
        Section5.isCFLinearIsometryOnSpan_apply_of_mem hcoh.1 hlamS hlamS
      _ = 1 := hselfS
  simpa [hlamτ_eq] using hselfTau

private theorem theorem_13_6_theorem_13_5_hypothesis_core_of_orthogonal_to_lambda
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ζ0 : Section1.ClassFunction Smax)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hspan : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section5.integerSpan Sfam ζ)
    (hdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.degree ζ = Section1.degree ζ0)
    (hself : Section1.scalarProduct G (τ1 lam) lamτ = 1)
    (hζ0 : ζ0 ∈ S1)
    (hlam : lam ∈ S1)
    (hζ0_ne_lam : ζ0 ≠ lam)
    (horth : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ lam →
      Section1.scalarProduct G (τ1 ζ) lamτ = 0) :
    ∃ ζ0 : Section1.ClassFunction Smax,
      ζ0 ∈ S1 ∧
        ζ0 ≠ lam ∧
        (1 : ℂ) = Section1.scalarProduct G (τS (lam - ζ0)) lamτ ∧
        ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
          ζ ≠ ζ0 → ζ ≠ lam →
            Section1.scalarProduct G (τS (ζ - ζ0)) lamτ = 0 := by
  have hagree : ∀ ζ : Section1.ClassFunction Smax, ∀ hζ : ζ ∈ S1,
      τ1 (ζ - ζ0) = τS (ζ - ζ0) := by
    intro ζ hζ
    apply hcoh.2.2
    refine ⟨Section5.integerSpan_sub (hspan ζ hζ) (hspan ζ0 hζ0), ?_⟩
    apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
    change Section1.degree ζ - Section1.degree ζ0 = 0
    rw [hdegree ζ hζ]
    simp
  refine ⟨ζ0, hζ0, hζ0_ne_lam, ?_, ?_⟩
  · have hζ0orth : Section1.scalarProduct G (τ1 ζ0) lamτ = 0 :=
      horth ζ0 hζ0 hζ0_ne_lam
    calc
      (1 : ℂ) = Section1.scalarProduct G (τ1 (lam - ζ0)) lamτ := by
        rw [map_sub, Section5.scalarProduct_sub_left, hself, hζ0orth]
        simp
      _ = Section1.scalarProduct G (τS (lam - ζ0)) lamτ := by
        rw [hagree lam hlam]
  · intro ζ hζ _hζ_ne0 hζ_ne_lam
    have hζ0orth : Section1.scalarProduct G (τ1 ζ0) lamτ = 0 :=
      horth ζ0 hζ0 hζ0_ne_lam
    calc
      Section1.scalarProduct G (τS (ζ - ζ0)) lamτ =
          Section1.scalarProduct G (τ1 (ζ - ζ0)) lamτ := by
        rw [hagree ζ hζ]
      _ = 0 := by
        rw [map_sub, Section5.scalarProduct_sub_left,
          horth ζ hζ hζ_ne_lam, hζ0orth]
        simp

public theorem theorem_13_6_calS1_split1_conjugate_ne_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (_hS1 : nonkernelInducedFamily Smax H P S1)
    (_hlamS1 : lam ∈ S1) :
    Section1.conjugateCharacter lam ≠ lam := by
  classical
  rcases h6hyp with ⟨_hH, hlam_irred, hdeg, _hind, _hlamτ⟩
  rcases hlam_irred with ⟨n, ρ, hρirr, hρchar⟩
  have hoddSmax : Odd (Nat.card Smax) := by
    rcases hsource with
      ⟨_hcase, _hSTypeP, _hTTypeP, _hp_card, _hq_card, _hCeq, _hD, _hc_card,
        _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
        _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
        _hChoice, hMin, _hFourSixS, _hFourSixT⟩
    letI : IsMinCE G := hMin
    exact section13_odd_card_subgroup_of_odd_group Smax IsMinCE.odd_order
  have hq_gt_one : 1 < q :=
    (section13_theorem_13_10_rawSourcePositivity_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource).2.1
  have hu_pos : 0 < u :=
    (section13_uv_pos_of_sourceData
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource).1
  have huq_gt_one : 1 < u * q := by
    have hu_ge_one : 1 ≤ u := Nat.succ_le_iff.mpr hu_pos
    exact lt_of_lt_of_le hq_gt_one (by simpa using Nat.mul_le_mul_right q hu_ge_one)
  have hne_principal : ρ.character ≠ Section1.principalCharacter Smax := by
    intro hprincipal
    have hdeg_principal : Section1.degree lam = (1 : ℂ) := by
      rw [hρchar, hprincipal, Section1.degree_apply]
      simp [Section1.principalCharacter]
    have hdeg_one : ((u * q : ℕ) : ℂ) = 1 := by
      simpa [Nat.cast_mul] using hdeg.symm.trans hdeg_principal
    have huq_ne_one : (u * q : ℕ) ≠ 1 := Nat.ne_of_gt huq_gt_one
    exact huq_ne_one (by exact_mod_cast hdeg_one)
  have hρ_ne_conj :
      ρ.character ≠ Section1.conjugateCharacter ρ.character :=
    Section1.proposition_1_1 hoddSmax ρ hρirr hne_principal
  intro hconj
  apply hρ_ne_conj
  calc
    ρ.character = lam := hρchar.symm
    _ = Section1.conjugateCharacter lam := hconj.symm
    _ = Section1.conjugateCharacter ρ.character := by rw [hρchar]

private theorem theorem_13_6_calS1_split1_conjugate_choice_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hlamS : lam ∈ Sfam)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hlamS1 : lam ∈ S1) :
    ∃ ζ0 : Section1.ClassFunction Smax,
      ζ0 ∈ S1 ∧ ζ0 ≠ lam := by
  refine ⟨Section1.conjugateCharacter lam,
    theorem_13_6_nonkernelInducedFamily_conjugate_mem Smax H P S1 hS1 hlamS1, ?_⟩
  exact theorem_13_6_calS1_split1_conjugate_ne_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
    lam lamτ p q u v c d _hsource _hlamS _h6hyp S1 hS1 hlamS1

private theorem theorem_13_6_H_subgroupOf_Smax_normal_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    (H.subgroupOf Smax).Normal := by
  rcases h6hyp with ⟨hH, _hlam_irred, _hdeg, _hind, _hlamτ_eq⟩
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hptypeS
  have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
    simpa [hfit] using section8FittingSubgroup_normal_in Smax
  simpa [hH] using hPCnormal

private noncomputable def theorem_13_6_irreducibleSubfamily
    {G : Type u} [Group G] [Finite G]
    (Smax : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax)) :
    Finset (Section1.ClassFunction Smax) :=
  section13_irreducibleSubfamily Smax Sfam

private theorem theorem_13_6_irreducibleSubfamily_subset
    {G : Type u} [Group G] [Finite G]
    (Smax : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax)) :
    theorem_13_6_irreducibleSubfamily Smax Sfam ⊆ Sfam := by
  exact section13_irreducibleSubfamily_subset Smax Sfam


private theorem theorem_13_6_muSum_mem_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hj0 : 0 < j)
    (hjp : j < p) :
    Section5.integerSpan Sfam (μsum j) := by
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ1, _hExt, houtput⟩
  exact Section5.integerSpan_of_mem Sfam ((houtput.1 j hj0 hjp).2.2.2)


public theorem section13_muSum_mem_nonkernelInducedFamily_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hj0 : 0 < j)
    (hjp : j < p) :
    μsum j ∈ S1 := by
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ1, _hExt, houtput⟩
  rcases houtput.1 j hj0 hjp with
    ⟨_hμchar, _hμdeg, hμlinearPC, hμSfam⟩
  have hμlinearH : inducedFromLinearCharacterForSection13 Smax H (μsum j) := by
    simpa [hH] using hμlinearPC
  rcases theorem_13_6_lambda_inducedFromNonkernel_H_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      (μsum j) (τS (μsum j)) p q u v c d hsource hμSfam hH hμlinearH with
    ⟨θH, hθHirr, hθHnotker, hMuInd⟩
  exact (hS1.2.2 (μsum j)).2 ⟨θH, hθHirr, hθHnotker, hMuInd⟩

private theorem section13_H_subgroupOf_Smax_normal_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    (H.subgroupOf Smax).Normal := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  have hfit : section8FittingSubgroup Smax = P ⊔ C := by
    simpa [hC] using Section8.theorem_8_5_a Smax P U W1 W2 hptypeS
  have hPCnormal : ((P ⊔ C).subgroupOf Smax).Normal := by
    simpa [hfit] using section8FittingSubgroup_normal_in Smax
  simpa [hH] using hPCnormal

private theorem section13_H_le_P_sup_U_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    H ≤ P ⊔ U := by
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rw [hH, hC]
  exact sup_le le_sup_left (inf_le_left.trans le_sup_right)

private theorem section13_calS1_eq_muSum_of_nonzero_scalarProduct
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (ζ : Section1.ClassFunction Smax)
    (hζ : ζ ∈ S1)
    (hj0 : 0 < j)
    (hjp : j < p)
    (hpair : Section1.scalarProduct Smax ζ (μsum j) ≠ 0) :
    ζ = μsum j := by
  have hμS1 : μsum j ∈ S1 :=
    section13_muSum_mem_nonkernelInducedFamily_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d j
      hsource hnotation hH S1 hS1 hj0 hjp
  have hHnormal : (H.subgroupOf Smax).Normal :=
    section13_H_subgroupOf_Smax_normal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH
  by_contra hne
  have horth :=
    theorem_13_6_nonkernelInducedFamily_pairwise_orthogonal
      Smax H P S1 hS1 hHnormal ζ hζ (μsum j) hμS1 hne
  exact hpair horth

private theorem section13_calS1_inducedCF_from_P_sup_U_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (ζ : Section1.ClassFunction Smax)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (hζeq : ζ = Section1.inducedCF (H.subgroupOf Smax) θ) :
    ∃ θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      θPU =
        Section1.inducedCF
          ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
          (Section1.subgroupOfClassFunction θ) ∧
      ζ = Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU := by
  have hHlePU := section13_H_le_P_sup_U_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
    hsource hH
  have hHT : H.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact hHlePU hx
  let θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax) :=
    Section1.inducedCF
      ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
      (Section1.subgroupOfClassFunction θ)
  refine ⟨θPU, rfl, ?_⟩
  rw [hζeq]
  exact (Section1.inducedCF_trans
    (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax) hHT θ).symm

private theorem section13_integerSpan_weightedFamilySum_nat
    {L ι : Type u} [Group L] [Finite ι]
    (S : Finset (Section1.ClassFunction L))
    (e : ι → ℕ)
    (χ : ι → Section1.ClassFunction L)
    (hχ : ∀ i, Section5.integerSpan S (χ i)) :
    Section5.integerSpan S (Section1.weightedFamilySum (fun i => (e i : ℂ)) χ) := by
  classical
  choose v hv using hχ
  refine ⟨fun X => ∑ i : ι, (e i : ℤ) * v i X, ?_⟩
  ext g
  calc
    Section1.weightedFamilySum (fun i => (e i : ℂ)) χ g
        = ∑ i : ι, (e i : ℂ) * χ i g := by
          rfl
    _ = ∑ i : ι, (e i : ℂ) *
          (∑ X : S, ((v i X : ℤ) : ℂ) * (X : Section1.ClassFunction L) g) := by
          simp [hv, Section1.evalCoeff]
    _ = ∑ i : ι, ∑ X : S,
          (e i : ℂ) * (((v i X : ℤ) : ℂ) * (X : Section1.ClassFunction L) g) := by
          simp [Finset.mul_sum]
    _ = ∑ X : S, ∑ i : ι,
          (e i : ℂ) * (((v i X : ℤ) : ℂ) * (X : Section1.ClassFunction L) g) := by
          rw [Finset.sum_comm]
    _ = ∑ X : S, (((∑ i : ι, (e i : ℤ) * v i X : ℤ) : ℂ) *
          (X : Section1.ClassFunction L) g) := by
          refine Finset.sum_congr rfl ?_
          intro X _
          simp [Finset.sum_mul, mul_assoc]
    _ = Section1.evalCoeff (fun X : S => (X : Section1.ClassFunction L))
          (fun X => ∑ i : ι, (e i : ℤ) * v i X) g := by
          simp [Section1.evalCoeff]


public theorem section13_calS1_P_sup_U_constituent_decomposition_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (_hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ)) :
    ∃ ι : Type u, ∃ _ : Finite ι,
      ∃ (e : ι → ℕ) (ψ : ι → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax)),
        θPU = Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ ∧
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i)) ∧
        ∀ i, Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
          (ψ i) θ := by
  classical
  have hHlePU := section13_H_le_P_sup_U_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
    hsource hH
  have hHT : H.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact hHlePU hx
  have hθchar : Section1.IsCharacter θ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr
  have hθsubchar : Section1.IsCharacter
      (Section1.subgroupOfClassFunction
        (T := (P ⊔ U).subgroupOf Smax) θ) :=
    Section1.isCharacter_subgroupOfClassFunction_of_le hHT θ hθchar
  have hθPUchar : Section1.IsCharacter θPU := by
    rw [hθPUeq]
    exact Section1.isCharacter_inducedCF_of_isCharacter
      ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
      (Section1.subgroupOfClassFunction
        (T := (P ⊔ U).subgroupOf Smax) θ)
      hθsubchar
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr
  have hθdeg_ne : Section1.degree θ ≠ 0 :=
    Section1.degree_ne_zero_of_isBookIrreducibleCharacter θ hθbook
  have hindex_ne :
      ((Subgroup.index
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite
      (H := (H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)))
  have hθPUdeg_ne : Section1.degree θPU ≠ 0 := by
    rw [hθPUeq, Section1.degree_inducedToSubgroup]
    exact mul_ne_zero hindex_ne hθdeg_ne
  have hθPU_ne : θPU ≠ 0 := by
    intro hzero
    apply hθPUdeg_ne
    simp [hzero, Section1.degree]
  rcases Section1.exists_positive_irreducible_decomposition_of_character
      θPU hθPUchar hθPU_ne with
    ⟨ι, hι, hιdec, e, ψ, _i0, hepos, hψbook, hψpair, hdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  have hψclass : ∀ i : ι, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.isBookIrreducibleCharacter_isClassFunction (ψ i) (hψbook i)
  have horthT : ∀ i j : ι,
      Section1.scalarProduct ((P ⊔ U).subgroupOf Smax) (ψ i) (ψ j) =
        if i = j then 1 else 0 :=
    Section1.scalarProduct_isBookIrreducible_family ψ hψbook hψpair
  have hdecompT :
      Section1.inducedCF
          ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
          (Section1.subgroupOfClassFunction
            (T := (P ⊔ U).subgroupOf Smax) θ) =
        Section1.weightedFamilySum (fun i => (e i : ℂ)) ψ := by
    rw [← hθPUeq]
    exact hdecomp
  let ιu : Type u := ULift.{u} ι
  let eu : ιu → ℕ := fun i => e i.down
  let ψu : ιu → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax) := fun i => ψ i.down
  have hsumULift :
      Section1.weightedFamilySum (fun i : ιu => (eu i : ℂ)) ψu =
        Section1.weightedFamilySum (fun i : ι => (e i : ℂ)) ψ := by
    ext g
    haveI : Finite ι := Finite.of_fintype ι
    letI : Fintype ι := Fintype.ofFinite ι
    letI : Fintype ιu := Fintype.ofFinite ιu
    let equivULift : ι ≃ ιu := Equiv.ulift.{u, 0}.symm
    simpa [Section1.weightedFamilySum, ιu, eu, ψu] using
      (Fintype.sum_equiv equivULift
        (fun i : ι => (e i : ℂ) * ψ i g)
        (fun i : ιu => (e i.down : ℂ) * ψ i.down g)
        (by intro i; rfl)).symm
  refine ⟨ιu, Finite.of_fintype ιu, eu, ψu, ?_, ?_, ?_⟩
  · exact hdecomp.trans hsumULift.symm
  · intro i
    exact Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ψ i.down) (hψbook i.down)
  · intro i
    exact Section1.proposition_1_7_liesAbove_of_positive_multiplicity
      (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax) e ψ θ
      hψclass horthT hdecompT i.down (hepos i.down)

private theorem section13_subgroupInKernel'_of_irreducible_constituent_of_kernel_character
    {K : Type u} [Group K] [Finite K]
    (B : Subgroup K)
    (φ χ : Section1.ClassFunction K)
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hχchar : Section1.IsCharacter χ)
    (hχker : Section1.subgroupInKernel' χ B)
    (hsp : Section1.scalarProduct K φ χ ≠ 0) :
    Section1.subgroupInKernel' φ B := by
  classical
  rcases hφirr with ⟨_nφ, φρ, hφρirr, hφeq⟩
  rcases hχchar with ⟨_Vχ, _haddχ, _hmodχ, _hfdχ, χρ, hχeq⟩
  have hsp_swap : Section1.scalarProduct K χ φ ≠ 0 :=
    (Section1.scalarProduct_ne_zero_swap (G := K) φ χ).mp hsp
  have hhom_ne : Module.finrank ℂ (Representation.IntertwiningMap φρ χρ) ≠ 0 := by
    intro hzero
    apply hsp_swap
    rw [hχeq, hφeq, Section1.scalarProduct_representation_char_eq_finrank φρ χρ]
    exact_mod_cast hzero
  have hexists : ∃ f : Representation.IntertwiningMap φρ χρ, f ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hsub : Subsingleton (Representation.IntertwiningMap φρ χρ) := by
      refine ⟨fun f g => ?_⟩
      rw [hnone f, hnone g]
    exact hhom_ne (Module.finrank_zero_of_subsingleton)
  rcases hexists with ⟨f, hfne⟩
  letI : Representation.IsIrreducible φρ := hφρirr
  have hfinj : Function.Injective f := by
    rcases Representation.IsIrreducible.injective_or_eq_zero f with hfinj | hfzero
    · exact hfinj
    · exact (hfne hfzero).elim
  have hχρker : Section1.subgroupInRepresentationKernel χρ B :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel χρ B).mp
      (by simpa [hχeq] using hχker)
  have hφρker : Section1.subgroupInRepresentationKernel φρ B := by
    intro b
    apply LinearMap.ext
    intro v
    apply hfinj
    calc
      f (φρ (b : K) v) = χρ (b : K) (f v) := by
        simpa using
          (Representation.IntertwiningMap.isIntertwining
            (ρ := φρ) (σ := χρ) f (b : K) v)
      _ = f v := by
        rw [hχρker b]
        rfl
  rw [hφeq]
  exact (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel φρ B).mpr
    hφρker


public theorem section13_calS1_P_sup_U_constituent_not_subgroupInKernel_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ) :
    ¬ Section1.subgroupInKernel' ψ
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) := by
  classical
  intro hψker
  have hHlePU := section13_H_le_P_sup_U_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
    hsource hH
  have hHT : H.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact hHlePU hx
  have hPH : P ≤ H := by
    rw [hH]
    exact le_sup_left
  have hPH_T :
      (P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax) ≤
        (H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax) := by
    intro x hx
    change ((x : (P ⊔ U).subgroupOf Smax) : Smax) ∈ H.subgroupOf Smax
    change (((x : (P ⊔ U).subgroupOf Smax) : Smax) : G) ∈ H
    exact hPH hx
  have hψchar : Section1.IsCharacter ψ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr
  have hψreschar : Section1.IsCharacter
      (Section1.subgroupRestriction
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ψ) := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ψ hψchar with
      ⟨Vψ, _haddψ, _hmodψ, _hfdψ, ψρ, hres⟩
    exact ⟨Vψ, inferInstance, inferInstance, inferInstance, ψρ, hres⟩
  have hθsubirr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.subgroupOfClassFunction
        (T := (P ⊔ U).subgroupOf Smax) θ) :=
    Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter _
      (Section1.isBookIrreducibleCharacter_subgroupOfClassFunction_of_le hHT θ
        (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθirr))
  have hψresker : Section1.subgroupInKernel'
      (Section1.subgroupRestriction
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ψ)
      (((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)).subgroupOf
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))) := by
    intro b
    simpa [Section1.subgroupRestriction, Section1.degree] using
      hψker ⟨((b : (H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) :
        (P ⊔ U).subgroupOf Smax), b.2⟩
  have hsp : Section1.scalarProduct
      ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
      (Section1.subgroupOfClassFunction (T := (P ⊔ U).subgroupOf Smax) θ)
      (Section1.subgroupRestriction
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ψ) ≠ 0 := by
    simpa [Section1.LiesAbove] using hψlies
  have hθsubker : Section1.subgroupInKernel'
      (Section1.subgroupOfClassFunction (T := (P ⊔ U).subgroupOf Smax) θ)
      (((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)).subgroupOf
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))) :=
    section13_subgroupInKernel'_of_irreducible_constituent_of_kernel_character
      (((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)).subgroupOf
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)))
      (Section1.subgroupOfClassFunction (T := (P ⊔ U).subgroupOf Smax) θ)
      (Section1.subgroupRestriction
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ψ)
      hθsubirr hψreschar hψresker hsp
  apply hθnotker
  intro a
  let aT : (H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax) :=
    ⟨⟨((a : H.subgroupOf Smax) : Smax), by
        change (((a : H.subgroupOf Smax) : Smax) : G) ∈ P ⊔ U
        exact (le_sup_left : P ≤ P ⊔ U) a.2⟩, (a : H.subgroupOf Smax).2⟩
  have haB : aT ∈
      (((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)).subgroupOf
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))) := by
    change (((aT : (H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) :
      (P ⊔ U).subgroupOf Smax) : Smax) ∈ P.subgroupOf Smax
    exact a.2
  have h := hθsubker ⟨aT, haB⟩
  simpa [aT, Section1.subgroupOfClassFunction, Section1.degree_subgroupOfClassFunction]
    using h

private theorem section13_typeP_prTIres_p_pos_of_notation
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 : Subgroup G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    0 < p := by
  rcases hnotation with ⟨homega, _hrest⟩
  rcases homega with ⟨_h31, _hq, hp, _ωFin, _hωFin⟩
  exact hp

private theorem section13_typeP_prTIres_xChar_base_subgroupInKernel
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax P U : Subgroup G}
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (xChar : J → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (h45a : Section4Scratch.theorem_4_5_a_statement
      ((P ⊔ U).subgroupOf Smax) piChar xChar)
    (hbase : piChar i0 j0 = Section1.principalCharacter Smax) :
    Section1.subgroupInKernel' (xChar j0)
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) := by
  intro a
  rw [← h45a.1 i0 j0, hbase]
  simp [Section1.subgroupRestriction, Section1.degree]

/- Checked finite-cardinality choice of the bounded Section 13 natural row
index `{j // j < p}` as the Section `(4.6)` column index. -/

/- Checked finite-cardinality choice of the bounded Section 13 natural column
index as the Section `(4.6)` column index, normalized so that natural zero is
the PF base column. -/


/- The supported source-selected Section `(4.6)` package attached to the
S-side Type-P data, with its actual source carrier hidden from the natural
table-indexing interface. -/
@[expose] public def section13_typeP_prTIres_pf4_sourceSelectedPackageData
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Smax P _ W1 W2 : Subgroup G)
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  ∃ A : Set Smax,
    Section10.section10FourSixNotationSupportedData Smax W1 W2 Wsec
        A A0 i0 j0 piChar δSign ωsec σsec τS ∧
      typePFourSixSigmaAgreesOnCyclicTI Smax W1 W2 Wsec σsec ∧
        ∃ H_cyclicA0 : G → Subgroup G,
          ∃ hCyclicA0 :
            Section2.hypothesis_2_2_statement
              (Section4Scratch.subgroupImageSet Smax
                (Section4Scratch.primeDadeA0Set
                  (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec A))
              Smax H_cyclicA0,
            (∀ α : Section1.ClassFunction Smax,
              Section2.CFOn Smax
                  (Section4Scratch.subgroupImageSet Smax
                    (Section4Scratch.primeDadeA0Set
                      (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec A)) α →
                τS α =
                  Section2.dadeTransform H_cyclicA0 hCyclicA0.subset_L α) ∧
        ∃ Ms : Subgroup G, ∃ Abook A0book A1book : Set G,
          ∃ H_A0 : G → Subgroup G,
            ∃ hA0M : Section2.Hypothesis2 A0book Smax H_A0,
              Section8.notation_8_10_source_data Smax P Ms Abook A0book A1book ∧
                Abook = Section8.section8CentralizerUnion
                  (ambientDerivedSubgroup Smax) Ms ∧
                A0book =
                  Abook ∪ section16ConjugatesOfSetBySet
                    (section16HatW W1 W2) (Smax : Set G) ∧
                P ≤ Ms ∧
                (∀ l : Smax,
                  (l : G) ∈
                    section16NonidentityElements ((Ms : Subgroup G) : Set G) →
                      (l : G) ∈ A0book) ∧
                ∀ α : Section1.ClassFunction Smax,
                  τS α = Section2.dadeTransform H_A0 hA0M.subset_L α

/- Checked extraction of PF `(4.3.b)` table distinctness from the source-selected
Section `(4.6)` package. -/
public theorem section13_typeP_prTIres_pf4_selected_table_pairwise_distinct
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Smax P U W1 W2 : Subgroup G)
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
    ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2 := by
  rcases hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨_σM, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨_hσmap, _hsign, _hirr, hselectedDistinct, _hind, _hSigma⟩
  exact hselectedDistinct

/- Checked extraction of PF `(4.3.b)` cross-column orthogonality from the
source-selected Section `(4.6)` package. -/


public theorem section13_typeP_prTIres_pf4_selected_table_four_three_b_data
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Smax P U W1 W2 : Subgroup G)
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
    (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
      (∀ i j,
        Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
          ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
        ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
          ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j := by
  rcases hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨σM, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨_hσmap, _hsign, hirr, _hselectedDistinct, hind, hSigma⟩
  exact ⟨hirr, hind, σM, hSigma⟩

/- Checked extraction of PF `(4.4)` base principal entry from the
source-selected Section `(4.6)` package. -/
public theorem section13_typeP_prTIres_pf4_selected_table_base_principal
    {G : Type u}
    [Group G]
    [Finite G]
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Smax P U W1 W2 : Subgroup G)
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
    piChar i0 j0 = Section1.principalCharacter Smax := by
  rcases hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨σM, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  exact
    (Section4.proposition_4_4_base
      (W1 := W1.subgroupOf Smax)
      (W2 := W2.subgroupOf Smax)
      (W := Wsec)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
        (ω := ωsec)
        (σ := σM)
        (piChar := piChar)
        (deltaSign := fun j => (δSign j : ℂ))
        hωsec h43b).2

private theorem section13_signed_irreducible_sign_eq_of_smul_eq
    {G : Type u}
    [Group G]
    [Finite G]
    {ε δ : ℂ}
    {χ ψ : Section1.ClassFunction G}
    (hε : ε = 1 ∨ ε = -1)
    (hδ : δ = 1 ∨ δ = -1)
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (h : ε • χ = δ • ψ) :
    ε = δ := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
  · rfl
  · exfalso
    rcases Section12.positive_degree_nat_of_isIrreducibleCharacterOnGroup hχ with
      ⟨n, hnpos, hn⟩
    rcases Section12.positive_degree_nat_of_isIrreducibleCharacterOnGroup hψ with
      ⟨m, _hmpos, hm⟩
    have hdeg := congrArg Section1.degree h
    have hχdeg : χ 1 = (n : ℂ) := by
      simpa [Section1.degree] using hn
    have hψdeg : ψ 1 = (m : ℂ) := by
      simpa [Section1.degree] using hm
    have hnm : (n : ℂ) = -(m : ℂ) := by
      simpa [Section1.degree, hχdeg, hψdeg] using hdeg
    have hzero : ((n + m : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add, hnm]
      ring
    have hpos : 0 < n + m := Nat.add_pos_left hnpos m
    have hne : ((n + m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hpos
    exact hne hzero
  · exfalso
    rcases Section12.positive_degree_nat_of_isIrreducibleCharacterOnGroup hχ with
      ⟨n, hnpos, hn⟩
    rcases Section12.positive_degree_nat_of_isIrreducibleCharacterOnGroup hψ with
      ⟨m, _hmpos, hm⟩
    have hdeg := congrArg Section1.degree h
    have hχdeg : χ 1 = (n : ℂ) := by
      simpa [Section1.degree] using hn
    have hψdeg : ψ 1 = (m : ℂ) := by
      simpa [Section1.degree] using hm
    have hnm : -(n : ℂ) = (m : ℂ) := by
      simpa [Section1.degree, hχdeg, hψdeg] using hdeg
    have hzero : ((n + m : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add, ← hnm]
      ring
    have hpos : 0 < n + m := Nat.add_pos_left hnpos m
    have hne : ((n + m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hpos
    exact hne hzero
  · rfl


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_signed_cyclicTI_base_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) := by
  rcases _hnotation with
    ⟨_hωData, _hσ, _hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum, hbase, _hbaseT⟩
  exact hbase

/- Checked extraction of `prTIsign0`: PF `(13.3)` sign normalization gives
the base sign after the lower-level cyclic-TI source supplies the signed base
value.  The wrappers below turn this package into `prTIirr00` and then into
the selected Section `(4.6)` base comparison. -/
public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_cyclicTI_base_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) ∧
      δ 0 = 1 := by
  have hsigned :
      (((δ 0 : ℤ) : ℂ) • μ 0 0 = Section1.principalCharacter Smax) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_signed_cyclicTI_base_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation
  have hp0 : 0 < p :=
    section13_typeP_prTIres_p_pos_of_notation
      Smax Tmax W W1 W2 ω η μ ν μsum νsum δ δ' σ p q hnotation
  have hsign :
      theorem_13_3_signNormalizationFor p q δ δ' :=
    ((theorem_13_3 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource).1
      ω η μ ν μsum νsum δ δ' σ hnotation).1
  exact ⟨hsigned, hsign.1 0 hp0⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_base_principal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    μ 0 0 = Section1.principalCharacter Smax := by
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_cyclicTI_base_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation with
    ⟨hsignedBase, hδ0⟩
  simpa [hδ0] using hsignedBase


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_ne_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ j : {j : ℕ // j < p},
      ∀ i1 i2 : {i : ℕ // i < q},
        i1 ≠ i2 → μ i1.1 j.1 ≠ μ i2.1 j.1 := by
  classical
  rcases _hnotation with
    ⟨hωNat, _hσNat, _hηNat, hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNat with ⟨h31, hq0, hp0, ωFin, hωFin, hωEq⟩
  have h31copy := h31
  rcases _hsource with
    ⟨_hcaseB, hTypeP, _hTypeT, _hp_card, _hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, hMin, _hTauS, _hTauT⟩
  have hTypePAll := hTypeP
  have hW_eq_sup : W = W1 ⊔ W2 := by
    change Section3.isCyclicTIHypothesis W1 W2 W at h31copy
    rcases h31copy with
      ⟨_hW1W, _hW2W, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro x hxW
      rcases hIP.mul_surjective x hxW with ⟨a, ha, b, hb, hx⟩
      rw [hx]
      exact (W1 ⊔ W2).mul_mem
        ((show W1 ≤ W1 ⊔ W2 from le_sup_left) ha)
        ((show W2 ≤ W1 ⊔ W2 from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  rcases hTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rcases hMF.1 with ⟨hPleSmax, _hPnorm, _hPnil, _hPHall⟩
  rcases hW1Hall with ⟨hW1leSmax, _hW1HallSub⟩
  have hW2leSmax : W2 ≤ Smax := fun x hx => hPleSmax ((hW2le hx).1)
  have hWsup_le : W1 ⊔ W2 ≤ Smax := sup_le hW1leSmax hW2leSmax
  have hWleSmax : W ≤ Smax := by
    rw [hW_eq_sup]
    exact hWsup_le
  have h42sup :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        ((W1 ⊔ W2).subgroupOf Smax) :=
    Section8.theorem_8_15_hypothesis_4_2_of_typeP
      (G := G) (M := Smax) (MF := P) (U := U)
      (W1 := W1) (W2 := W2) hMin hTypePAll
  have h42 :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        (W.subgroupOf Smax) := by
    simpa [hW_eq_sup] using h42sup
  let e : W ≃* W.subgroupOf Smax :=
    (Subgroup.subgroupOfEquivOfLe (H := W) (K := Smax) hWleSmax).symm
  let ωS : Fin q → Fin p → Section1.ClassFunction (W.subgroupOf Smax) :=
    fun i j => Section6.theorem_6_8_transportClassFunction e (ωFin i j)
  have hcardW1 :
      Nat.card (W1.subgroupOf Smax) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1leSmax).toEquiv
  have hcardW2 :
      Nat.card (W2.subgroupOf Smax) = Nat.card W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2leSmax).toEquiv
  have hV1 :
      ∀ x : W,
        ((x : G) ∈ W1) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W1.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hV2 :
      ∀ x : W,
        ((x : G) ∈ W2) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W2.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hωS :
      Section3.notation_3_3_statement
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) (W.subgroupOf Smax)
        (Fin q) (Fin p) ⟨0, hq0⟩ ⟨0, hp0⟩ ωS := by
    simpa [ωS] using
      Section6.theorem_6_8_notation_3_3_transport
        (L := G) (M := Smax)
        (W1 := W1) (W2 := W2) (W := W)
        (V1 := W1.subgroupOf Smax)
        (V2 := W2.subgroupOf Smax)
        (V := W.subgroupOf Smax)
        (e := e) hcardW1 hcardW2 hV1 hV2 hωFin
  have hsign :
      ∀ j : Fin p, Section1.IsSign (((δ j.1 : ℤ) : ℂ)) := by
    intro j
    rcases hδ j.1 j.2 with hδj | hδj
    · left
      simp [hδj]
    · right
      simp [hδj]
  have hind :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.inducedCF (W.subgroupOf Smax)
            (ωS i j - ωS ⟨0, hq0⟩ j) =
          (((δ j.1 : ℤ) : ℂ) • (μ i.1 j.1 - μ 0 j.1)) := by
    intro i j
    have hrow :
        (ωS i j - ωS ⟨0, hq0⟩ j) =
          Section1.subgroupOfClassFunction (T := Smax)
            (ω i.1 j.1 - ω 0 j.1) := by
      ext x
      have hx :
          (Subgroup.subgroupOfEquivOfLe hWleSmax x : W) =
            (⟨((x : W.subgroupOf Smax) : G), x.2⟩ : W) := by
        ext
        rfl
      simp [ωS, e, Section6.theorem_6_8_transportClassFunction,
        Section1.subgroupOfClassFunction, hωEq i.1 j.1 i.2 j.2,
        hωEq 0 j.1 hq0 j.2, hx]
    rw [hrow]
    simpa using hμind i.1 j.1 i.2 j.2
  intro j i1 i2 hi
  let jF : Fin p := ⟨j.1, j.2⟩
  let i1F : Fin q := ⟨i1.1, i1.2⟩
  let i2F : Fin q := ⟨i2.1, i2.2⟩
  have hiF : i1F ≠ i2F := by
    intro h
    exact hi (Subtype.ext (congrArg Fin.val h))
  simpa [i1F, i2F, jF] using
    Section4.theorem_4_3_b_same_column_ne_of_induced_row_differences
      (derivedSubgroup Smax)
      (W1.subgroupOf Smax)
      (W2.subgroupOf Smax)
      (W.subgroupOf Smax)
      (Fin q)
      (Fin p)
      ⟨0, hq0⟩
      ⟨0, hp0⟩
      ωS
        (fun i j => μ i.1 j.1)
        (fun j : Fin p => (((δ j.1 : ℤ) : ℂ)))
        h42
        hωS
        hsign
        hind
        (j := jF)
        hiF


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ j : {j : ℕ // j < p},
      ∀ i1 i2 : {i : ℕ // i < q},
        i1 ≠ i2 →
          Section1.scalarProduct Smax (μ i1.1 j.1) (μ i2.1 j.1) = 0 := by
  classical
  rcases _hnotation with
    ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  intro j i1 i2 hidx
  exact
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hμirr i1.1 j.1 i1.2 j.2)
      (hμirr i2.1 j.1 i2.2 j.2)
      (section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_ne_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource
        ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
          _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
          _hμsum, _hνsum⟩
        j i1 i2 hidx)


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_injective_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ j : {j : ℕ // j < p},
      Function.Injective (fun i : {i : ℕ // i < q} => μ i.1 j.1) := by
  classical
  rcases _hnotation with
    ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  intro j i1 i2 hEq
  by_cases hidx : i1 = i2
  · exact hidx
  · have horth :=
      section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_orthogonal_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource
        ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
          _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
          _hμsum, _hνsum⟩
        j i1 i2 hidx
    have hzero :
        Section1.scalarProduct Smax (μ i1.1 j.1) (μ i1.1 j.1) = 0 := by
      simpa [← hEq] using horth
    have hone :
        Section1.scalarProduct Smax (μ i1.1 j.1) (μ i1.1 j.1) = 1 :=
      section13_scalarProduct_self_of_irreducibleCharacter
        (hμirr i1.1 j.1 i1.2 j.2)
    have hcontr : (1 : ℂ) = 0 := by
      exact hone.symm.trans hzero
    norm_num at hcontr


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_distinct_columns_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i1 i2 : {i : ℕ // i < q},
      ∀ j1 j2 : {j : ℕ // j < p},
        j1 ≠ j2 →
          Section1.scalarProduct Smax (μ i1.1 j1.1) (μ i2.1 j2.1) = 0 := by
  classical
  rcases _hnotation with
    ⟨hωNat, _hσNat, _hηNat, hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNat with ⟨h31, hq0, hp0, ωFin, hωFin, hωEq⟩
  have h31copy := h31
  rcases _hsource with
    ⟨_hcaseB, hTypeP, _hTypeT, _hp_card, _hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, hMin, _hTauS, _hTauT⟩
  have hTypePAll := hTypeP
  have hW_eq_sup : W = W1 ⊔ W2 := by
    change Section3.isCyclicTIHypothesis W1 W2 W at h31copy
    rcases h31copy with
      ⟨_hW1W, _hW2W, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro x hxW
      rcases hIP.mul_surjective x hxW with ⟨a, ha, b, hb, hx⟩
      rw [hx]
      exact (W1 ⊔ W2).mul_mem
        ((show W1 ≤ W1 ⊔ W2 from le_sup_left) ha)
        ((show W2 ≤ W1 ⊔ W2 from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  rcases hTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rcases hMF.1 with ⟨hPleSmax, _hPnorm, _hPnil, _hPHall⟩
  rcases hW1Hall with ⟨hW1leSmax, _hW1HallSub⟩
  have hW2leSmax : W2 ≤ Smax := fun x hx => hPleSmax ((hW2le hx).1)
  have hWsup_le : W1 ⊔ W2 ≤ Smax := sup_le hW1leSmax hW2leSmax
  have hWleSmax : W ≤ Smax := by
    rw [hW_eq_sup]
    exact hWsup_le
  have h42sup :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        ((W1 ⊔ W2).subgroupOf Smax) :=
    Section8.theorem_8_15_hypothesis_4_2_of_typeP
      (G := G) (M := Smax) (MF := P) (U := U)
      (W1 := W1) (W2 := W2) hMin hTypePAll
  have h42 :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        (W.subgroupOf Smax) := by
    simpa [hW_eq_sup] using h42sup
  let e : W ≃* W.subgroupOf Smax :=
    (Subgroup.subgroupOfEquivOfLe (H := W) (K := Smax) hWleSmax).symm
  let ωS : Fin q → Fin p → Section1.ClassFunction (W.subgroupOf Smax) :=
    fun i j => Section6.theorem_6_8_transportClassFunction e (ωFin i j)
  have hcardW1 :
      Nat.card (W1.subgroupOf Smax) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1leSmax).toEquiv
  have hcardW2 :
      Nat.card (W2.subgroupOf Smax) = Nat.card W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2leSmax).toEquiv
  have hV1 :
      ∀ x : W,
        ((x : G) ∈ W1) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W1.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hV2 :
      ∀ x : W,
        ((x : G) ∈ W2) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W2.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hωS :
      Section3.notation_3_3_statement
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) (W.subgroupOf Smax)
        (Fin q) (Fin p) ⟨0, hq0⟩ ⟨0, hp0⟩ ωS := by
    simpa [ωS] using
      Section6.theorem_6_8_notation_3_3_transport
        (L := G) (M := Smax)
        (W1 := W1) (W2 := W2) (W := W)
        (V1 := W1.subgroupOf Smax)
        (V2 := W2.subgroupOf Smax)
        (V := W.subgroupOf Smax)
        (e := e) hcardW1 hcardW2 hV1 hV2 hωFin
  have hsign :
      ∀ j : Fin p, Section1.IsSign (((δ j.1 : ℤ) : ℂ)) := by
    intro j
    rcases hδ j.1 j.2 with hδj | hδj
    · left
      simp [hδj]
    · right
      simp [hδj]
  have hirr :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.IsIrreducibleCharacterOnGroup (μ i.1 j.1) := by
    intro i j
    exact hμirr i.1 j.1 i.2 j.2
  have hind :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.inducedCF (W.subgroupOf Smax)
            (ωS i j - ωS ⟨0, hq0⟩ j) =
          (((δ j.1 : ℤ) : ℂ) • (μ i.1 j.1 - μ 0 j.1)) := by
    intro i j
    have hrow :
        (ωS i j - ωS ⟨0, hq0⟩ j) =
          Section1.subgroupOfClassFunction (T := Smax)
            (ω i.1 j.1 - ω 0 j.1) := by
      ext x
      have hx :
          (Subgroup.subgroupOfEquivOfLe hWleSmax x : W) =
            (⟨((x : W.subgroupOf Smax) : G), x.2⟩ : W) := by
        ext
        rfl
      simp [ωS, e, Section6.theorem_6_8_transportClassFunction,
        Section1.subgroupOfClassFunction, hωEq i.1 j.1 i.2 j.2,
        hωEq 0 j.1 hq0 j.2, hx]
    rw [hrow]
    simpa using hμind i.1 j.1 i.2 j.2
  have hdistinct :
      ∀ j : Fin p, ∀ i i' : Fin q,
        i ≠ i' → μ i.1 j.1 ≠ μ i'.1 j.1 := by
    intro j i i' hi
    simpa using
      Section4.theorem_4_3_b_same_column_ne_of_induced_row_differences
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        (W.subgroupOf Smax)
        (Fin q)
        (Fin p)
        ⟨0, hq0⟩
        ⟨0, hp0⟩
        ωS
        (fun i j => μ i.1 j.1)
        (fun j : Fin p => (((δ j.1 : ℤ) : ℂ)))
        h42
        hωS
        hsign
        hind
        (j := j)
        hi
  intro i1 i2 j1 j2 hj
  let i1F : Fin q := ⟨i1.1, i1.2⟩
  let i2F : Fin q := ⟨i2.1, i2.2⟩
  let j1F : Fin p := ⟨j1.1, j1.2⟩
  let j2F : Fin p := ⟨j2.1, j2.2⟩
  have hjF : j1F ≠ j2F := by
    intro h
    exact hj (Subtype.ext (congrArg Fin.val h))
  simpa [i1F, i2F, j1F, j2F] using
    Section4.theorem_4_3_b_cross_column_scalarProduct_zero_of_induced_row_differences
      (derivedSubgroup Smax)
      (W1.subgroupOf Smax)
      (W2.subgroupOf Smax)
      (W.subgroupOf Smax)
      (Fin q)
      (Fin p)
      ⟨0, hq0⟩
      ⟨0, hp0⟩
      ωS
      (fun i j => μ i.1 j.1)
      (fun j : Fin p => (((δ j.1 : ℤ) : ℂ)))
      h42
      hωS
      hsign
      hirr
      hdistinct
      hind
      (i := i1F)
      (i' := i2F)
      (j := j1F)
      (j' := j2F)
      hjF


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_distinct_columns_ne_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i1 i2 : {i : ℕ // i < q},
      ∀ j1 j2 : {j : ℕ // j < p},
        j1 ≠ j2 → μ i1.1 j1.1 ≠ μ i2.1 j2.1 := by
  classical
  rcases _hnotation with
    ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  intro i1 i2 j1 j2 hj hEq
  have horth :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_distinct_columns_orthogonal_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource
      ⟨_hωNat, _hσNat, _hηNat, _hδ, _hδ', hμirr, _hνirr,
        _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
        _hμsum, _hνsum⟩
      i1 i2 j1 j2 hj
  have hzero :
      Section1.scalarProduct Smax (μ i1.1 j1.1) (μ i1.1 j1.1) = 0 := by
    simpa [hEq] using horth
  have hone :
      Section1.scalarProduct Smax (μ i1.1 j1.1) (μ i1.1 j1.1) = 1 :=
    section13_scalarProduct_self_of_irreducibleCharacter
      (hμirr i1.1 j1.1 i1.2 j1.2)
  have hcontr : (1 : ℂ) = 0 := by
    exact hone.symm.trans hzero
  norm_num at hcontr


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pair_injective_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    Function.Injective
      (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} => μ x.1.1 x.2.1) := by
  intro x y hxy
  have hsame :
      ∀ j : {j : ℕ // j < p},
        Function.Injective (fun i : {i : ℕ // i < q} => μ i.1 j.1) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_same_column_injective_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
  have hdiff :
      ∀ i1 i2 : {i : ℕ // i < q},
        ∀ j1 j2 : {j : ℕ // j < p},
          j1 ≠ j2 → μ i1.1 j1.1 ≠ μ i2.1 j2.1 :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_distinct_columns_ne_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
  rcases x with ⟨i1, j1⟩
  rcases y with ⟨i2, j2⟩
  by_cases hj : j1 = j2
  · subst j2
    have hi : i1 = i2 := hsame j1 hxy
    subst i2
    rfl
  · exfalso
    exact hdiff i1 i2 j1 j2 hj hxy


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pairwise_distinct_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i1 i2 : {i : ℕ // i < q},
      ∀ j1 j2 : {j : ℕ // j < p},
        μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2 := by
  intro i1 i2 j1 j2 hμ
  have hinj :
      Function.Injective
        (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} => μ x.1.1 x.2.1) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pair_injective_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
  have hpair : (i1, j1) = (i2, j2) := hinj hμ
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

private theorem section13_notation_3_3_split_table_eq
    {L : Type u}
    [Group L]
    [Finite L]
    (W1 W2 W : Subgroup L)
    {I J I' J' : Type*}
    [Fintype I]
    [Fintype J]
    [DecidableEq I]
    [DecidableEq J]
    [Fintype I']
    [Fintype J']
    [DecidableEq I']
    [DecidableEq J']
    (i0 : I)
    (j0 : J)
    (i0' : I')
    (j0' : J')
    (ω : I → J → Section1.ClassFunction W)
    (ω' : I' → J' → Section1.ClassFunction W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (hω' : Section3.notation_3_3_statement W1 W2 W I' J' i0' j0' ω') :
    ∃ fI : I → I', ∃ fJ : J → J', ∀ i j, ω i j = ω' (fI i) (fJ j) := by
  classical
  have hleft : ∀ i : I, ∃ i' : I', ω i j0 = ω' i' j0' := by
    intro i
    exact
      (hω'.left_kernel_exact (ω i j0) (hω.irreducible i j0)).1
        (hω.left_kernel i)
  choose fI hfI using hleft
  have hright : ∀ j : J, ∃ j' : J', ω i0 j = ω' i0' j' := by
    intro j
    exact
      (hω'.right_kernel_exact (ω i0 j) (hω.irreducible i0 j)).1
        (hω.right_kernel j)
  choose fJ hfJ using hright
  refine ⟨fI, fJ, ?_⟩
  intro i j
  ext x
  calc
    ω i j x = ω i j0 x * ω i0 j x := hω.product i j x
    _ = ω' (fI i) j0' x * ω' i0' (fJ j) x := by
      rw [hfI i, hfJ j]
    _ = ω' (fI i) (fJ j) x := (hω'.product (fI i) (fJ j) x).symm


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_restrict_compl_ortho_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
              ∃ fI : {i : ℕ // i < q} → I,
                ∃ fJ : {j : ℕ // j < p} → J,
                  ∃ dLocal : {j : ℕ // j < p} → ℤ,
                    (∀ j : {j : ℕ // j < p}, dLocal j = δ j.1) ∧
                      (∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1) ∧
                        ∀ i : {i : ℕ // i < q},
                          ∀ j : {j : ℕ // j < p},
                            ∀ x : Smax,
                              ∀ hx : x ∈ Section3.cyclicTISet
                                (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec,
                                (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) x =
                                  ωsec (fI i) (fJ j)
                                    ⟨x, Section3.cyclicTISet_subset
                                      (W1.subgroupOf Smax) (W2.subgroupOf Smax)
                                      Wsec hx⟩ := by
  classical
  have hsourceForPairwise := _hsource
  have hsourceForSetup := _hsource
  have hnotationAll := _hnotation
  rcases _hnotation with
    ⟨hωNat, _hσNat, _hηNat, hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωNat with ⟨h31, hq0, hp0, ωFin, hωFin, hωEq⟩
  have h31copy := h31
  rcases hsourceForSetup with
    ⟨_hcaseB, hTypeP, _hTypeT, _hp_card, _hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, _hMin, _hTauS, _hTauT⟩
  have hW_eq_sup : W = W1 ⊔ W2 := by
    change Section3.isCyclicTIHypothesis W1 W2 W at h31copy
    rcases h31copy with
      ⟨_hW1W, _hW2W, hIP, _hcyc, _hodd, _hcard1, _hcard2, _hTI⟩
    apply le_antisymm
    · intro x hxW
      rcases hIP.mul_surjective x hxW with ⟨a, ha, b, hb, hx⟩
      rw [hx]
      exact (W1 ⊔ W2).mul_mem
        ((show W1 ≤ W1 ⊔ W2 from le_sup_left) ha)
        ((show W2 ≤ W1 ⊔ W2 from le_sup_right) hb)
    · exact sup_le hIP.left_le hIP.right_le
  rcases hTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDerComp, _hPnoncyc, _hSecond, _hFit, _hFitLe,
      hW2le, _hW2cyc, _hW2ne, _hCentralizer, _hNormalizer⟩
  rcases hMF.1 with ⟨hPleSmax, _hPnorm, _hPnil, _hPHall⟩
  rcases hW1Hall with ⟨hW1leSmax, _hW1HallSub⟩
  have hW2leSmax : W2 ≤ Smax := fun x hx => hPleSmax ((hW2le hx).1)
  have hWsup_le : W1 ⊔ W2 ≤ Smax := sup_le hW1leSmax hW2leSmax
  have hWleSmax : W ≤ Smax := by
    rw [hW_eq_sup]
    exact hWsup_le
  rcases _hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases hnotation10 with
    ⟨_MF, _Ms, _Abook, _A0book, _A1book, _hSource10,
      hWsec_eq, _hA0eq, h46, hωsecData, _hIso, _hVirt, _hPrin,
      _h45, _h48, _hTauA0, _hFull⟩
  have hWsub_eq : W.subgroupOf Smax = Wsec := by
    calc
      W.subgroupOf Smax = (W1 ⊔ W2).subgroupOf Smax := by
        ext x
        simp [Subgroup.mem_subgroupOf, hW_eq_sup]
      _ = Wsec := hWsec_eq.symm
  have h42 :
      Section4.hypothesis_4_2_statement
        (derivedSubgroup Smax)
        (W1.subgroupOf Smax)
        (W2.subgroupOf Smax)
        (W.subgroupOf Smax) := by
    simpa [hWsub_eq] using h46.1
  let e : W ≃* W.subgroupOf Smax :=
    (Subgroup.subgroupOfEquivOfLe (H := W) (K := Smax) hWleSmax).symm
  let ωS : Fin q → Fin p → Section1.ClassFunction (W.subgroupOf Smax) :=
    fun i j => Section6.theorem_6_8_transportClassFunction e (ωFin i j)
  have hcardW1 :
      Nat.card (W1.subgroupOf Smax) = Nat.card W1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1leSmax).toEquiv
  have hcardW2 :
      Nat.card (W2.subgroupOf Smax) = Nat.card W2 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2leSmax).toEquiv
  have hV1 :
      ∀ x : W,
        ((x : G) ∈ W1) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W1.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hV2 :
      ∀ x : W,
        ((x : G) ∈ W2) ↔ (((e x : W.subgroupOf Smax) : Smax) ∈ W2.subgroupOf Smax) := by
    intro x
    simp [e, Subgroup.mem_subgroupOf]
  have hωS :
      Section3.notation_3_3_statement
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) (W.subgroupOf Smax)
        (Fin q) (Fin p) ⟨0, hq0⟩ ⟨0, hp0⟩ ωS := by
    simpa [ωS] using
      Section6.theorem_6_8_notation_3_3_transport
        (L := G) (M := Smax)
        (W1 := W1) (W2 := W2) (W := W)
        (V1 := W1.subgroupOf Smax)
        (V2 := W2.subgroupOf Smax)
        (V := W.subgroupOf Smax)
        (e := e) hcardW1 hcardW2 hV1 hV2 hωFin
  have hsign :
      ∀ j : Fin p, Section1.IsSign (((δ j.1 : ℤ) : ℂ)) := by
    intro j
    rcases hδ j.1 j.2 with hδj | hδj
    · left
      simp [hδj]
    · right
      simp [hδj]
  have hirr :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.IsIrreducibleCharacterOnGroup (μ i.1 j.1) := by
    intro i j
    exact hμirr i.1 j.1 i.2 j.2
  have hind :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.inducedCF (W.subgroupOf Smax)
            (ωS i j - ωS ⟨0, hq0⟩ j) =
          (((δ j.1 : ℤ) : ℂ) • (μ i.1 j.1 - μ 0 j.1)) := by
    intro i j
    have hrow :
        (ωS i j - ωS ⟨0, hq0⟩ j) =
          Section1.subgroupOfClassFunction (T := Smax)
            (ω i.1 j.1 - ω 0 j.1) := by
      ext x
      have hx :
          (Subgroup.subgroupOfEquivOfLe hWleSmax x : W) =
            (⟨((x : W.subgroupOf Smax) : G), x.2⟩ : W) := by
        ext
        rfl
      simp [ωS, e, Section6.theorem_6_8_transportClassFunction,
        Section1.subgroupOfClassFunction, hωEq i.1 j.1 i.2 j.2,
        hωEq 0 j.1 hq0 j.2, hx]
    rw [hrow]
    simpa using hμind i.1 j.1 i.2 j.2
  have hdistinct :
      ∀ a b : Fin q × Fin p, a ≠ b →
        μ a.1.1 a.2.1 ≠ μ b.1.1 b.2.1 := by
    intro a b hab hEq
    let i1 : {i : ℕ // i < q} := ⟨a.1.1, a.1.2⟩
    let j1 : {j : ℕ // j < p} := ⟨a.2.1, a.2.2⟩
    let i2 : {i : ℕ // i < q} := ⟨b.1.1, b.1.2⟩
    let j2 : {j : ℕ // j < p} := ⟨b.2.1, b.2.2⟩
    have hpair :=
      section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pairwise_distinct_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsourceForPairwise hnotationAll
        i1 i2 j1 j2 (by simpa [i1, i2, j1, j2] using hEq)
    have hi : a.1 = b.1 := Fin.ext (congrArg Subtype.val hpair.1)
    have hj : a.2 = b.2 := Fin.ext (congrArg Subtype.val hpair.2)
    exact hab (Prod.ext hi hj)
  have h43cNat :
      Section4.theorem_4_3_c_statement
        (W2.subgroupOf Smax) (W.subgroupOf Smax)
        (Fin q) (Fin p)
        (fun i j => μ i.1 j.1)
        (fun j : Fin p => (((δ j.1 : ℤ) : ℂ))) ωS :=
    Section4.theorem_4_3_c
      (derivedSubgroup Smax)
      (W1.subgroupOf Smax)
      (W2.subgroupOf Smax)
      (W.subgroupOf Smax)
      (Fin q)
      (Fin p)
      ⟨0, hq0⟩
      ⟨0, hp0⟩
      ωS
      (fun j : Fin p => (((δ j.1 : ℤ) : ℂ)))
      (fun i j => μ i.1 j.1)
      h42
      hωS
      hsign
      hirr
      hdistinct
      hind
  let eWS : W.subgroupOf Smax ≃* Wsec := MulEquiv.subgroupCongr hWsub_eq
  let ωT : Fin q → Fin p → Section1.ClassFunction Wsec :=
    fun i j => Section6.theorem_6_8_transportClassFunction eWS (ωS i j)
  have hV1WS :
      ∀ x : W.subgroupOf Smax,
        ((x : Smax) ∈ W1.subgroupOf Smax) ↔
          (((eWS x : Wsec) : Smax) ∈ W1.subgroupOf Smax) := by
    intro x
    simp [eWS]
  have hV2WS :
      ∀ x : W.subgroupOf Smax,
        ((x : Smax) ∈ W2.subgroupOf Smax) ↔
          (((eWS x : Wsec) : Smax) ∈ W2.subgroupOf Smax) := by
    intro x
    simp [eWS]
  have hωT :
      Section3.notation_3_3_statement
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec
        (Fin q) (Fin p) ⟨0, hq0⟩ ⟨0, hp0⟩ ωT := by
    simpa [ωT] using
      Section6.theorem_6_8_notation_3_3_transport
        (L := Smax) (M := Smax)
        (W1 := W1.subgroupOf Smax)
        (W2 := W2.subgroupOf Smax)
        (W := W.subgroupOf Smax)
        (V1 := W1.subgroupOf Smax)
        (V2 := W2.subgroupOf Smax)
        (V := Wsec)
        (e := eWS) rfl rfl hV1WS hV2WS hωS
  rcases
      section13_notation_3_3_split_table_eq
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec
        (⟨0, hq0⟩ : Fin q) (⟨0, hp0⟩ : Fin p) i0 j0
        ωT ωsec hωT hωsecData with
    ⟨gI, gJ, hωTable⟩
  let fI : {i : ℕ // i < q} → I := fun i => gI ⟨i.1, i.2⟩
  let fJ : {j : ℕ // j < p} → J := fun j => gJ ⟨j.1, j.2⟩
  let dLocal : {j : ℕ // j < p} → ℤ := fun j => δ j.1
  refine ⟨fI, fJ, dLocal, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    simpa [dLocal] using hδ j.1 j.2
  · intro i j x hx
    let iF : Fin q := ⟨i.1, i.2⟩
    let jF : Fin p := ⟨j.1, j.2⟩
    have hxWsec : x ∈ (Wsec : Set Smax) :=
      Section3.cyclicTISet_subset
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec hx
    have hxWsub : x ∈ (W.subgroupOf Smax : Set Smax) := by
      simpa [hWsub_eq] using hxWsec
    have hxNotW2 : x ∉ (W2.subgroupOf Smax : Set Smax) :=
      Section3.cyclicTISet_not_mem_right
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec hx
    have hxDiff :
        x ∈ ((W.subgroupOf Smax : Set Smax) \ (W2.subgroupOf Smax : Set Smax)) :=
      ⟨hxWsub, hxNotW2⟩
    have hnat :=
      h43cNat.1 iF jF x hxDiff
    have hnat' :
        μ i.1 j.1 x =
          ((δ j.1 : ℤ) : ℂ) * ωS iF jF ⟨x, hxWsub⟩ := by
      simpa [iF, jF] using hnat
    have hδsq : ((δ j.1 : ℤ) : ℂ) * ((δ j.1 : ℤ) : ℂ) = 1 := by
      rcases hδ j.1 j.2 with hδj | hδj <;> simp [hδj]
    have harg :
        eWS.symm ⟨x, hxWsec⟩ = ⟨x, hxWsub⟩ := by
      ext
      simp [eWS]
    have htransportVal :
        ωT iF jF ⟨x, hxWsec⟩ = ωS iF jF ⟨x, hxWsub⟩ := by
      simp [ωT, Section6.theorem_6_8_transportClassFunction, harg]
    have htableVal :
        ωT iF jF ⟨x, hxWsec⟩ =
          ωsec (gI iF) (gJ jF) ⟨x, hxWsec⟩ :=
      congrFun (hωTable iF jF) ⟨x, hxWsec⟩
    calc
      (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) x =
          ((δ j.1 : ℤ) : ℂ) * μ i.1 j.1 x := by
            simp [dLocal]
      _ = ((δ j.1 : ℤ) : ℂ) *
            (((δ j.1 : ℤ) : ℂ) * ωS iF jF ⟨x, hxWsub⟩) := by
            rw [hnat']
      _ = ωS iF jF ⟨x, hxWsub⟩ := by
            rw [← mul_assoc, hδsq, one_mul]
      _ = ωT iF jF ⟨x, hxWsec⟩ := htransportVal.symm
      _ = ωsec (fI i) (fJ j)
            ⟨x, Section3.cyclicTISet_subset
              (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec hx⟩ := by
            simpa [fI, fJ, iF, jF, hxWsec] using htableVal


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_signed_output_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
              ∃ fI : {i : ℕ // i < q} → I,
                ∃ fJ : {j : ℕ // j < p} → J,
                ∃ dLocal : {j : ℕ // j < p} → {z : ℤ // z = 1 ∨ z = -1},
                  (∀ j : {j : ℕ // j < p}, (dLocal j : ℤ) = δ j.1) ∧
                    ∀ i : {i : ℕ // i < q},
                      ∀ j : {j : ℕ // j < p},
                        ∀ x : Smax,
                          ∀ hx : x ∈ Section3.cyclicTISet
                            (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec,
                            (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) x =
                              ωsec (fI i) (fJ j)
                                ⟨x, Section3.cyclicTISet_subset
                                  (W1.subgroupOf Smax) (W2.subgroupOf Smax)
                                  Wsec hx⟩ := by
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_restrict_compl_ortho_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage with
    ⟨fI, fJ, dLocal, hdLocalEq, hdLocal, hvalue⟩
  refine ⟨fI, fJ, (fun j => ⟨dLocal j, hdLocal j⟩), ?_, ?_⟩
  · intro j
    exact hdLocalEq j
  · intro i j x hx
    exact hvalue i j x hx

/- Checked projection from the typed-sign `muV2` source output to the previous
plain-integer downstream interface. -/
public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_cyclicTI_value_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
              ∃ fI : {i : ℕ // i < q} → I,
                ∃ fJ : {j : ℕ // j < p} → J,
                  ∃ dLocal : {j : ℕ // j < p} → ℤ,
                    (∀ j : {j : ℕ // j < p}, dLocal j = δ j.1) ∧
                      (∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1) ∧
                        ∀ i : {i : ℕ // i < q},
                          ∀ j : {j : ℕ // j < p},
                            ∀ x : Smax,
                              ∀ hx : x ∈ Section3.cyclicTISet
                                (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec,
                                (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) x =
                                  ωsec (fI i) (fJ j)
                                    ⟨x, Section3.cyclicTISet_subset
                                      (W1.subgroupOf Smax) (W2.subgroupOf Smax)
                                      Wsec hx⟩ := by
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_signed_output_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage with
    ⟨fI, fJ, dLocal, hdLocalEq, hvalue⟩
  refine ⟨fI, fJ, (fun j => (dLocal j : ℤ)), ?_, ?_, ?_⟩
  · intro j
    exact hdLocalEq j
  · intro j
    exact (dLocal j).property
  · intro i j x hx
    exact hvalue i j x hx


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_Dsigma_entry_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
              ∃ fI : {i : ℕ // i < q} → I,
                ∃ fJ : {j : ℕ // j < p} → J,
                  ∃ dLocal : {j : ℕ // j < p} → ℤ,
                    (∀ j : {j : ℕ // j < p}, dLocal j = δ j.1) ∧
                      (∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1) ∧
                        ∀ i : {i : ℕ // i < q},
                          ∀ j : {j : ℕ // j < p},
                            σM (ωsec (fI i) (fJ j)) =
                              ((dLocal j : ℤ) : ℂ) • μ i.1 j.1 := by
  classical
  rcases _hnotation with
    ⟨_hωNat, _hσNat, _hηNat, hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases _hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨σM0, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨h46, _hW2K, _h31sec, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hωsecData, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨hσM0map, _hδSign, _hpiIrr, _hselectedDistinct, _hind, hSigma0⟩
  rcases
      Section3.pf35_data_of_theorem_3_2_map_statement
        hωsecData σM0 hσM0map with
    ⟨χ, horth, hsigned, h00, hInd, hσM0eq⟩
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_muV2_cyclicTI_value_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource
        ⟨_hωNat, _hσNat, _hηNat, hδ, _hδ', hμirr, _hνirr,
          _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
          _hμsum, _hνsum⟩
        Wsec A0 i0 j0 piChar δSign ωsec σsec
        ⟨A, hnotation10, _hSigmaAgree,
          ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩ with
    ⟨fI, fJ, dLocal, hdLocalEq, hdLocal, hmuV2⟩
  have h31local :
      Section3.hypothesis_3_1_statement
        (W1.subgroupOf Smax) (W2.subgroupOf Smax) Wsec :=
    (Section4.theorem_4_3_a
      (derivedSubgroup Smax)
      (W1.subgroupOf Smax)
      (W2.subgroupOf Smax)
      Wsec
      h46.1).2
  refine ⟨fI, fJ, dLocal, hdLocalEq, hdLocal, ?_⟩
  intro i j
  have hdLocalC : Section1.IsSign (((dLocal j : ℤ) : ℂ)) := by
    rcases hdLocal j with hdj | hdj
    · left
      simp [hdj]
    · right
      simp [hdj]
  have hXsigned :
      Section3.IsSignedIrreducibleCharacter
        (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) := by
    exact ⟨((dLocal j : ℤ) : ℂ), hdLocalC, μ i.1 j.1,
      hμirr i.1 j.1 i.2 j.2, rfl⟩
  have huniq :
      (((dLocal j : ℤ) : ℂ) • μ i.1 j.1) =
        Section3.sigmaOfPF35 ωsec χ (ωsec (fI i) (fJ j)) := by
    exact
      Section3.proposition_3_9_a_uniqueness_of_pf35
        (W1 := W1.subgroupOf Smax)
        (W2 := W2.subgroupOf Smax)
        (W := Wsec)
        (I := I)
        (J := J)
        (i0 := i0)
        (j0 := j0)
        (ω := ωsec)
        (χ := χ)
        h31local hωsecData horth hsigned h00 hInd
        (hωsecData.irreducible (fI i) (fJ j))
        hXsigned
        (by
          intro x hx
          exact hmuV2 i j x hx)
  have hσM0model :
      σM0 (ωsec (fI i) (fJ j)) =
        Section3.sigmaOfPF35 ωsec χ (ωsec (fI i) (fJ j)) := by
    calc
      σM0 (ωsec (fI i) (fJ j)) = χ (fI i) (fJ j) := hσM0eq (fI i) (fJ j)
      _ = Section3.sigmaOfPF35 ωsec χ (ωsec (fI i) (fJ j)) := by
        rw [Section3.sigmaOfPF35_apply_omega
          ωsec χ hωsecData.orthonormal (fI i) (fJ j)]
  calc
    σM (ωsec (fI i) (fJ j)) =
        (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) := _hSigma (fI i) (fJ j)
    _ = σM0 (ωsec (fI i) (fJ j)) := (hSigma0 (fI i) (fJ j)).symm
    _ = Section3.sigmaOfPF35 ωsec χ (ωsec (fI i) (fJ j)) := hσM0model
    _ = ((dLocal j : ℤ) : ℂ) • μ i.1 j.1 := huniq.symm


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_Dd_local_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
    (fI : {i : ℕ // i < q} → I)
    (fJ : {j : ℕ // j < p} → J)
    (dLocal : {j : ℕ // j < p} → ℤ)
    (_hdLocalEq : ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1)
    (_hdLocal : ∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1)
    (_hDsigmaLocal : ∀ i : {i : ℕ // i < q},
      ∀ j : {j : ℕ // j < p},
        σM (ωsec (fI i) (fJ j)) =
          ((dLocal j : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1 := by
  exact _hdLocalEq


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_dLocal_integer_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
    (fI : {i : ℕ // i < q} → I)
    (fJ : {j : ℕ // j < p} → J)
    (dLocal : {j : ℕ // j < p} → ℤ)
    (_hdLocalEq : ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1)
    (_hdLocal : ∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1)
    (_hDsigmaLocal : ∀ i : {i : ℕ // i < q},
      ∀ j : {j : ℕ // j < p},
        σM (ωsec (fI i) (fJ j)) =
          ((dLocal j : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p},
        dLocal j = δ j.1 := by
  intro j
  exact
    section13_typeP_prTIres_pf4_primeTIirr_spec_Dd_local_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM _hSigma
      fI fJ dLocal _hdLocalEq _hdLocal _hDsigmaLocal j


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_selected_sign_integer_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
    (fI : {i : ℕ // i < q} → I)
    (fJ : {j : ℕ // j < p} → J)
    (dLocal : {j : ℕ // j < p} → ℤ)
    (_hdLocalEq : ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1)
    (_hdLocal : ∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1)
    (_hDsigmaLocal : ∀ i : {i : ℕ // i < q},
      ∀ j : {j : ℕ // j < p},
        σM (ωsec (fI i) (fJ j)) =
          ((dLocal j : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p},
        δSign (fJ j) = δ j.1 := by
  classical
  have hnotationForSource := _hnotation
  have hpackageForSource := _hpackage
  rcases _hnotation with
    ⟨hω, _hσ, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hω with ⟨_h31, hq0, _hp0, _ωFin, _hωFin, _hωeq⟩
  rcases _hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨_σM0, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31sec, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hωsecData, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨_hσmap, hδSign, hpiIrr, _hselectedDistinct, _hind, _hSigma0⟩
  have hdLocalNatural :
      ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1 :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_dLocal_integer_identification_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource hnotationForSource
      Wsec A0 i0 j0 piChar δSign ωsec σsec hpackageForSource σM _hSigma
      fI fJ dLocal _hdLocalEq _hdLocal _hDsigmaLocal
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  intro j
  have hdLocalC :
      ((dLocal j : ℤ) : ℂ) = 1 ∨ ((dLocal j : ℤ) : ℂ) = -1 := by
    rcases _hdLocal j with hdj | hdj
    · left
      simp [hdj]
    · right
      simp [hdj]
  have hselectedLocalC :
      (δSign (fJ j) : ℂ) = ((dLocal j : ℤ) : ℂ) := by
    have hsignEq :
        (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
          ((dLocal j : ℤ) : ℂ) • μ izero.1 j.1 := by
      calc
        (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
            σM (ωsec (fI izero) (fJ j)) := (_hSigma (fI izero) (fJ j)).symm
        _ = ((dLocal j : ℤ) : ℂ) • μ izero.1 j.1 := _hDsigmaLocal izero j
    exact
      section13_signed_irreducible_sign_eq_of_smul_eq
        (by simpa [Section1.IsSign] using hδSign (fJ j))
        hdLocalC
        (hpiIrr (fI izero) (fJ j))
        (hμirr izero.1 j.1 izero.2 j.2)
        hsignEq
  have hselectedLocal : δSign (fJ j) = dLocal j := by
    exact_mod_cast hselectedLocalC
  exact hselectedLocal.trans (hdLocalNatural j)


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_selected_sign_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
    (fI : {i : ℕ // i < q} → I)
    (fJ : {j : ℕ // j < p} → J)
    (dLocal : {j : ℕ // j < p} → ℤ)
    (_hdLocalEq : ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1)
    (_hdLocal : ∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1)
    (_hDsigmaLocal : ∀ i : {i : ℕ // i < q},
      ∀ j : {j : ℕ // j < p},
        σM (ωsec (fI i) (fJ j)) =
          ((dLocal j : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p},
        (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ) := by
  have hsign :
      ∀ j : {j : ℕ // j < p}, δSign (fJ j) = δ j.1 :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_selected_sign_integer_identification_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM _hSigma
      fI fJ dLocal _hdLocalEq _hdLocal _hDsigmaLocal
  intro j
  exact congrArg (fun z : ℤ => ((z : ℤ) : ℂ)) (hsign j)


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_local_sign_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
    (fI : {i : ℕ // i < q} → I)
    (fJ : {j : ℕ // j < p} → J)
    (dLocal : {j : ℕ // j < p} → ℤ)
    (_hdLocalEq : ∀ j : {j : ℕ // j < p}, dLocal j = δ j.1)
    (_hdLocal : ∀ j : {j : ℕ // j < p}, dLocal j = 1 ∨ dLocal j = -1)
    (_hDsigmaLocal : ∀ i : {i : ℕ // i < q},
      ∀ j : {j : ℕ // j < p},
        σM (ωsec (fI i) (fJ j)) =
          ((dLocal j : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p},
        ((dLocal j : ℤ) : ℂ) = ((δ j.1 : ℤ) : ℂ) := by
  classical
  have hnotationForSource := _hnotation
  have hpackageForSource := _hpackage
  rcases _hnotation with
    ⟨hω, _hσ, _hη, _hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hω with ⟨_h31, hq0, _hp0, _ωFin, _hωFin, _hωeq⟩
  rcases _hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨_σM0, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31sec, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hωsecData, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨_hσmap, hδSign, hpiIrr, _hselectedDistinct, _hind, _hSigma0⟩
  have hselectedNatural :
      ∀ j : {j : ℕ // j < p},
        (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_selected_sign_identification_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource hnotationForSource
      Wsec A0 i0 j0 piChar δSign ωsec σsec hpackageForSource σM _hSigma
      fI fJ dLocal _hdLocalEq _hdLocal _hDsigmaLocal
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  intro j
  have hdLocalC :
      ((dLocal j : ℤ) : ℂ) = 1 ∨ ((dLocal j : ℤ) : ℂ) = -1 := by
    rcases _hdLocal j with hdj | hdj
    · left
      simp [hdj]
    · right
      simp [hdj]
  have hselectedLocal :
      (δSign (fJ j) : ℂ) = ((dLocal j : ℤ) : ℂ) := by
    have hsignEq :
        (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
          ((dLocal j : ℤ) : ℂ) • μ izero.1 j.1 := by
      calc
        (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
            σM (ωsec (fI izero) (fJ j)) := (_hSigma (fI izero) (fJ j)).symm
        _ = ((dLocal j : ℤ) : ℂ) • μ izero.1 j.1 := _hDsigmaLocal izero j
    exact
      section13_signed_irreducible_sign_eq_of_smul_eq
        (by simpa [Section1.IsSign] using hδSign (fJ j))
        hdLocalC
        (hpiIrr (fI izero) (fJ j))
        (hμirr izero.1 j.1 izero.2 j.2)
        hsignEq
  exact hselectedLocal.symm.trans (hselectedNatural j)


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_Dsigma_entry_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
    (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                ∀ i : {i : ℕ // i < q},
                  ∀ j : {j : ℕ // j < p},
                    σM (ωsec (fI i) (fJ j)) =
                      ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_Dsigma_entry_core_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM _hSigma with
    ⟨fI, fJ, dLocal, hdLocalEq, hdLocal, hDsigmaLocal⟩
  have hsign :
      ∀ j : {j : ℕ // j < p},
        ((dLocal j : ℤ) : ℂ) = ((δ j.1 : ℤ) : ℂ) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_local_sign_identification_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM _hSigma
      fI fJ dLocal hdLocalEq hdLocal hDsigmaLocal
  refine ⟨fI, fJ, ?_⟩
  intro i j
  calc
    σM (ωsec (fI i) (fJ j)) =
        ((dLocal j : ℤ) : ℂ) • μ i.1 j.1 := hDsigmaLocal i j
    _ = ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
      rw [hsign j]


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_signed_entry_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (_hselectedData :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                  ∀ i : {i : ℕ // i < q},
                    ∀ j : {j : ℕ // j < p},
                      (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) =
                        ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
  rcases _hselectedData with ⟨_hirr, _hind, σM, hSigma⟩
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_Dsigma_entry_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM hSigma with
    ⟨fI, fJ, hDsigma⟩
  refine ⟨fI, fJ, ?_⟩
  intro i j
  calc
    (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) =
        σM (ωsec (fI i) (fJ j)) := (hSigma (fI i) (fJ j)).symm
    _ = ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := hDsigma i j

private theorem section13_typeP_prTIres_pf4_primeTIirr_spec_Dd_core
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax)
      (_hSigma : ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j)
      (fI : {i : ℕ // i < q} → I)
      (fJ : {j : ℕ // j < p} → J)
      (_hDsigma : ∀ i : {i : ℕ // i < q},
        ∀ j : {j : ℕ // j < p},
          σM (ωsec (fI i) (fJ j)) =
            ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1) :
      ∀ j : {j : ℕ // j < p},
        (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ) := by
  classical
  rcases _hnotation with
    ⟨hω, _hσ, _hη, hδ, _hδ', hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hω with ⟨_h31, hq0, _hp0, _ωFin, _hωFin, _hωeq⟩
  rcases _hpackage with
    ⟨A, hnotation10, _hSigmaAgree,
      ⟨_H_cyclicA0, _hCyclicA0, _hTauCyclicA0, _hBook⟩⟩
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨_σM', _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31', _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨_hωsec, h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  rcases h43b with
    ⟨_hσmap, hδSign, hpiIrr, _hselectedDistinct, _hind, _hSigma'⟩
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  intro j
  have hδC :
      ((δ j.1 : ℤ) : ℂ) = 1 ∨ ((δ j.1 : ℤ) : ℂ) = -1 := by
    rcases hδ j.1 j.2 with hδj | hδj
    · left
      simp [hδj]
    · right
      simp [hδj]
  have hsignEq :
      (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
        ((δ j.1 : ℤ) : ℂ) • μ izero.1 j.1 := by
    calc
      (δSign (fJ j) : ℂ) • piChar (fI izero) (fJ j) =
          σM (ωsec (fI izero) (fJ j)) := (_hSigma (fI izero) (fJ j)).symm
      _ = ((δ j.1 : ℤ) : ℂ) • μ izero.1 j.1 := _hDsigma izero j
  exact
    section13_signed_irreducible_sign_eq_of_smul_eq
      (by simpa [Section1.IsSign] using hδSign (fJ j))
      hδC
      (hpiIrr (fI izero) (fJ j))
      (hμirr izero.1 j.1 izero.2 j.2)
      hsignEq


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_signed_table_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (_hselectedData :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                (∀ j : {j : ℕ // j < p},
                  (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ)) ∧
                  ∀ i : {i : ℕ // i < q},
                    ∀ j : {j : ℕ // j < p},
                      (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) =
                        ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
  classical
  rcases _hselectedData with ⟨hirr, hind, σM, hSigma⟩
  have hselectedDataForSource :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j :=
    ⟨hirr, hind, σM, hSigma⟩
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_signed_entry_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage hselectedDataForSource with
    ⟨fI, fJ, hsignedEntry⟩
  have hDsigma :
      ∀ i : {i : ℕ // i < q},
        ∀ j : {j : ℕ // j < p},
          σM (ωsec (fI i) (fJ j)) =
            ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
    intro i j
    calc
      σM (ωsec (fI i) (fJ j)) =
          (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) := hSigma (fI i) (fJ j)
      _ = ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := hsignedEntry i j
  have hsign :
      ∀ j : {j : ℕ // j < p},
        (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_Dd_core
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage σM hSigma fI fJ hDsigma
  exact ⟨fI, fJ, hsign, hsignedEntry⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_signed_Dmu_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (_hselectedData :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                (∀ j : {j : ℕ // j < p},
                  (δSign (fJ j) : ℂ) = ((δ j.1 : ℤ) : ℂ)) ∧
                  ∀ i : {i : ℕ // i < q},
                    ∀ j : {j : ℕ // j < p},
                      (δSign (fJ j) : ℂ) • piChar (fI i) (fJ j) =
                        ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
  exact
    section13_typeP_prTIres_pf4_primeTIirr_spec_signed_table_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage _hselectedData


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_Dmu_identification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (_hselectedData :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j) :
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                ∀ i : {i : ℕ // i < q},
                  ∀ j : {j : ℕ // j < p},
                    piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  rcases hnotation with
    ⟨_hω, _hσ, _hη, hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_signed_Dmu_identification_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource
        ⟨_hω, _hσ, _hη, hδ, _hδ', _hμirr, _hνirr,
          _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
          _hμsum, _hνsum⟩
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage _hselectedData with
    ⟨fI, fJ, hsign, hsignedEntry⟩
  refine ⟨fI, fJ, ?_⟩
  intro i j
  have hδne : ((δ j.1 : ℤ) : ℂ) ≠ 0 := by
    rcases hδ j.1 j.2 with hδsign | hδsign <;> simp [hδsign]
  have hscaled :
      ((δ j.1 : ℤ) : ℂ) • piChar (fI i) (fJ j) =
        ((δ j.1 : ℤ) : ℂ) • μ i.1 j.1 := by
    simpa [hsign j] using hsignedEntry i j
  have hcancel :=
    congrArg
      (fun z : Section1.ClassFunction Smax => (((δ j.1 : ℤ) : ℂ)⁻¹) • z)
      hscaled
  simpa [smul_smul, hδne] using hcancel


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_product_entry_matching_bounded_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ {I J : Type u}
      [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
      ∀ (Wsec : Subgroup Smax)
        (A0 : Set Smax)
        (i0 : I)
        (j0 : J)
        (piChar : I → J → Section1.ClassFunction Smax)
        (δSign : J → ℤ)
        (ωsec : I → J → Section1.ClassFunction Wsec)
        (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
        section13_typeP_prTIres_pf4_sourceSelectedPackageData
            Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
          ∃ fI : {i : ℕ // i < q} → I,
            ∃ fJ : {j : ℕ // j < p} → J,
          ∀ i : {i : ℕ // i < q},
            ∀ j : {j : ℕ // j < p},
              piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  intro I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
    ωsec σsec hpackage
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hselectedData :
      (∀ i j, Section1.IsIrreducibleCharacterOnGroup (piChar i j)) ∧
        (∀ i j,
          Section1.inducedCF Wsec (ωsec i j - ωsec i0 j) =
            ((δSign j : ℂ) • (piChar i j - piChar i0 j))) ∧
          ∃ σM : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction Smax,
            ∀ i j, σM (ωsec i j) = (δSign j : ℂ) • piChar i j :=
    section13_typeP_prTIres_pf4_selected_table_four_three_b_data
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  exact
    section13_typeP_prTIres_pf4_primeTIirr_spec_Dmu_identification_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage hselectedData


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_product_entry_matching_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ (_hq0 : 0 < q) (_hp0 : 0 < p),
      ∀ {I J : Type u}
        [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
        ∀ (Wsec : Subgroup Smax)
          (A0 : Set Smax)
          (i0 : I)
          (j0 : J)
          (piChar : I → J → Section1.ClassFunction Smax)
          (δSign : J → ℤ)
          (ωsec : I → J → Section1.ClassFunction Wsec)
          (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
          section13_typeP_prTIres_pf4_sourceSelectedPackageData
              Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                ∀ i : {i : ℕ // i < q},
                  ∀ j : {j : ℕ // j < p},
                    piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  intro _hq0 _hp0 I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
    ωsec σsec hpackage
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  exact
    section13_typeP_prTIres_pf4_primeTIirr_spec_product_entry_matching_bounded_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
      Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_raw_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ (_hq0 : 0 < q) (_hp0 : 0 < p),
      ∀ {I J : Type u}
        [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
        ∀ (Wsec : Subgroup Smax)
          (A0 : Set Smax)
          (i0 : I)
          (j0 : J)
          (piChar : I → J → Section1.ClassFunction Smax)
          (δSign : J → ℤ)
          (ωsec : I → J → Section1.ClassFunction Wsec)
          (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
          section13_typeP_prTIres_pf4_sourceSelectedPackageData
              Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                Function.Injective
                    (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} =>
                      (fI x.1, fJ x.2)) ∧
                    ∀ i : {i : ℕ // i < q},
                      ∀ j : {j : ℕ // j < p},
                        piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  intro hq0 hp0 I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
    ωsec σsec hpackage
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_product_entry_matching_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        hq0 hp0 Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
    ⟨fI, fJ, hentry⟩
  have hnaturalInj :
      Function.Injective
        (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} => μ x.1.1 x.2.1) :=
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pair_injective_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
  have hprod :
      Function.Injective
        (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} =>
          (fI x.1, fJ x.2)) := by
    intro x y hxy
    have hI : fI x.1 = fI y.1 := congrArg Prod.fst hxy
    have hJ : fJ x.2 = fJ y.2 := congrArg Prod.snd hxy
    have hμ : μ x.1.1 x.2.1 = μ y.1.1 y.2.1 := by
      calc
        μ x.1.1 x.2.1 = piChar (fI x.1) (fJ x.2) := (hentry x.1 x.2).symm
        _ = piChar (fI y.1) (fJ y.2) := by rw [hI, hJ]
        _ = μ y.1.1 y.2.1 := hentry y.1 y.2
    exact hnaturalInj hμ
  exact ⟨fI, fJ, hprod, hentry⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_base_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    μ 0 0 = Section1.principalCharacter Smax ∧
      ∀ (_hq0 : 0 < q) (_hp0 : 0 < p),
        ∀ {I J : Type u}
          [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
          ∀ (Wsec : Subgroup Smax)
            (A0 : Set Smax)
            (i0 : I)
            (j0 : J)
            (piChar : I → J → Section1.ClassFunction Smax)
            (δSign : J → ℤ)
            (ωsec : I → J → Section1.ClassFunction Wsec)
            (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
            section13_typeP_prTIres_pf4_sourceSelectedPackageData
                Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
              ∃ fI : {i : ℕ // i < q} → I,
                ∃ fJ : {j : ℕ // j < p} → J,
                  Function.Injective
                      (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} =>
                        (fI x.1, fJ x.2)) ∧
                    ∀ i : {i : ℕ // i < q},
                      ∀ j : {j : ℕ // j < p},
                        piChar (fI i) (fJ j) = μ i.1 j.1 := by
  exact
    ⟨section13_typeP_prTIres_pf4_primeTIirr_spec_base_principal_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation,
      section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_raw_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ (hq0 : 0 < q) (hp0 : 0 < p),
      ∀ {I J : Type u}
        [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
        ∀ (Wsec : Subgroup Smax)
          (A0 : Set Smax)
          (i0 : I)
          (j0 : J)
          (piChar : I → J → Section1.ClassFunction Smax)
          (δSign : J → ℤ)
          (ωsec : I → J → Section1.ClassFunction Wsec)
          (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
          section13_typeP_prTIres_pf4_sourceSelectedPackageData
              Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                Function.Injective
                    (fun x : {i : ℕ // i < q} × {j : ℕ // j < p} =>
                      (fI x.1, fJ x.2)) ∧
                  fI ⟨0, hq0⟩ = i0 ∧
                    fJ ⟨0, hp0⟩ = j0 ∧
                      ∀ i : {i : ℕ // i < q},
                        ∀ j : {j : ℕ // j < p},
                          piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  intro hq0 hp0 I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
    ωsec σsec hpackage
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_base_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation with
    ⟨hbase, hmatching⟩
  rcases
      hmatching hq0 hp0 Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
    ⟨fI, fJ, hprod, hentry⟩
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  let jzero : {j : ℕ // j < p} := ⟨0, hp0⟩
  have hselectedBase :
      piChar i0 j0 = Section1.principalCharacter Smax :=
    section13_typeP_prTIres_pf4_selected_table_base_principal
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  have hselectedDistinct :
      ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2 :=
    section13_typeP_prTIres_pf4_selected_table_pairwise_distinct
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  have hzeroEntry :
      piChar (fI izero) (fJ jzero) = piChar i0 j0 := by
    calc
      piChar (fI izero) (fJ jzero) = μ 0 0 := by
        simpa [izero, jzero] using hentry izero jzero
      _ = Section1.principalCharacter Smax := hbase
      _ = piChar i0 j0 := hselectedBase.symm
  have hzeroPair : (fI izero, fJ jzero) = (i0, j0) := by
    by_contra hne
    exact hselectedDistinct (fI izero, fJ jzero) (i0, j0) hne hzeroEntry
  have hfI0 : fI izero = i0 := congrArg Prod.fst hzeroPair
  have hfJ0 : fJ jzero = j0 := congrArg Prod.snd hzeroPair
  exact ⟨fI, fJ, hprod, hfI0, hfJ0, hentry⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_table_matching_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ (hq0 : 0 < q) (hp0 : 0 < p),
      ∀ {I J : Type u}
        [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
        ∀ (Wsec : Subgroup Smax)
          (A0 : Set Smax)
          (i0 : I)
          (j0 : J)
          (piChar : I → J → Section1.ClassFunction Smax)
          (δSign : J → ℤ)
          (ωsec : I → J → Section1.ClassFunction Wsec)
          (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
          section13_typeP_prTIres_pf4_sourceSelectedPackageData
              Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                Function.Injective fI ∧
                  Function.Injective fJ ∧
                    fI ⟨0, hq0⟩ = i0 ∧
                      fJ ⟨0, hp0⟩ = j0 ∧
                        ∀ i : {i : ℕ // i < q},
                          ∀ j : {j : ℕ // j < p},
                            piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  intro hq0 hp0 I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
    ωsec σsec hpackage
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_product_matching_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
        hq0 hp0 Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
    ⟨fI, fJ, hprod, hfI0, hfJ0, hentry⟩
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  let jzero : {j : ℕ // j < p} := ⟨0, hp0⟩
  have hfI : Function.Injective fI := by
    intro i1 i2 hfi
    have hpair :
        (i1, jzero) = (i2, jzero) :=
      hprod (by simpa using congrArg (fun i => (i, fJ jzero)) hfi)
    exact congrArg Prod.fst hpair
  have hfJ : Function.Injective fJ := by
    intro j1 j2 hfj
    have hpair :
        (izero, j1) = (izero, j2) :=
      hprod (by simpa using congrArg (fun j => (fI izero, j)) hfj)
    exact congrArg Prod.snd hpair
  exact ⟨fI, fJ, hfI, hfJ, hfI0, hfJ0, hentry⟩


public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    (∀ (hq0 : 0 < q) (hp0 : 0 < p),
      ∀ {I J : Type u}
        [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
        ∀ (Wsec : Subgroup Smax)
          (A0 : Set Smax)
          (i0 : I)
          (j0 : J)
          (piChar : I → J → Section1.ClassFunction Smax)
          (δSign : J → ℤ)
          (ωsec : I → J → Section1.ClassFunction Wsec)
          (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
          section13_typeP_prTIres_pf4_sourceSelectedPackageData
              Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
            ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                fI ⟨0, hq0⟩ = i0 ∧
                  fJ ⟨0, hp0⟩ = j0 ∧
                    ∀ i : {i : ℕ // i < q},
                      ∀ j : {j : ℕ // j < p},
                        piChar (fI i) (fJ j) = μ i.1 j.1) ∧
      ∀ i1 i2 : {i : ℕ // i < q},
        ∀ j1 j2 : {j : ℕ // j < p},
          μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2 := by
  classical
  constructor
  · intro hq0 hp0 I J instI decI instJ decJ Wsec A0 i0 j0 piChar δSign
      ωsec σsec hpackage
    letI : Fintype I := instI
    letI : DecidableEq I := decI
    letI : Fintype J := instJ
    letI : DecidableEq J := decJ
    rcases
        section13_typeP_prTIres_pf4_primeTIirr_spec_table_matching_source
          Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
          ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation
          hq0 hp0 Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
      ⟨fI, fJ, _hfI, _hfJ, hfI0, hfJ0, hentry⟩
    exact ⟨fI, fJ, hfI0, hfJ0, hentry⟩
  · exact
      section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pairwise_distinct_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation

/- Checked projection for the natural Section 13 `primeTIirr` table convention
once the natural bounds are known nonzero from notation.  It chooses normalized
row/column functions from the natural bounded index types to the source-selected
Section `(4.6)` table and records entry equality. -/
public theorem section13_typeP_prTIres_pf4_natural_table_normalized_functions_choice_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hq0 : 0 < q)
    (hp0 : 0 < p) :
    ∀ {I J : Type u}
      [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
      ∀ (Wsec : Subgroup Smax)
        (A0 : Set Smax)
        (i0 : I)
        (j0 : J)
        (piChar : I → J → Section1.ClassFunction Smax)
        (δSign : J → ℤ)
        (ωsec : I → J → Section1.ClassFunction Wsec)
        (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
        section13_typeP_prTIres_pf4_sourceSelectedPackageData
            Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
          ∃ fI : {i : ℕ // i < q} → I,
            ∃ fJ : {j : ℕ // j < p} → J,
              fI ⟨0, hq0⟩ = i0 ∧
                fJ ⟨0, hp0⟩ = j0 ∧
                  ∀ i : {i : ℕ // i < q},
                    ∀ j : {j : ℕ // j < p},
                      piChar (fI i) (fJ j) = μ i.1 j.1 := by
  exact
    (section13_typeP_prTIres_pf4_primeTIirr_spec_core_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation).1
      hq0 hp0


public theorem section13_typeP_prTIres_natural_mu_pairwise_distinct_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i1 i2 : {i : ℕ // i < q},
      ∀ j1 j2 : {j : ℕ // j < p},
        μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2 := by
  exact
    section13_typeP_prTIres_pf4_primeTIirr_spec_natural_pairwise_distinct_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation


/- Checked wrapper extracting the natural positivity bounds from the Section 13
notation package before delegating only the normalized table-function
convention. -/


public theorem section13_typeP_prTIres_natural_primeTIirr_package_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    μ 0 0 = Section1.principalCharacter Smax ∧
      (∀ i1 i2 : {i : ℕ // i < q},
        ∀ j1 j2 : {j : ℕ // j < p},
          μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2) ∧
        ∀ {I J : Type u}
          [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J],
          ∀ (Wsec : Subgroup Smax)
            (A0 : Set Smax)
            (i0 : I)
            (j0 : J)
            (piChar : I → J → Section1.ClassFunction Smax)
            (δSign : J → ℤ)
            (ωsec : I → J → Section1.ClassFunction Wsec)
            (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G),
            section13_typeP_prTIres_pf4_sourceSelectedPackageData
                Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS →
              0 < p →
                ∃ fI : {i : ℕ // i < q} → I,
              ∃ fJ : {j : ℕ // j < p} → J,
                ∀ i : {i : ℕ // i < q},
                  ∀ j : {j : ℕ // j < p},
                    piChar (fI i) (fJ j) = μ i.1 j.1 := by
  classical
  have hnotationForSource := _hnotation
  rcases _hnotation with ⟨hωData, _hnotationRest⟩
  rcases hωData with ⟨_h31Nat, hq0, hp0, _ωFin, _h33Nat, _hωeqNat⟩
  have hsourceAll := _hsource
  rcases hsourceAll with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, _hMin, hTauS, _hTauT⟩
  rcases hTauS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, _A, A0, i0, j0, piChar,
      δSign, ωsec, σsec, hnotation10, hSigmaAgree, ⟨H_cyclicA0, hCyclicA0, hTauCyclicA0, hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS :=
    ⟨_A, hnotation10, hSigmaAgree,
      ⟨H_cyclicA0, hCyclicA0, hTauCyclicA0, hBook⟩⟩
  rcases
      section13_typeP_prTIres_pf4_natural_table_normalized_functions_choice_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource hnotationForSource
        hq0 hp0
        Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
    ⟨fI, fJ, hfI0, hfJ0, hentry⟩
  have hselectedBase :
      piChar i0 j0 = Section1.principalCharacter Smax :=
    section13_typeP_prTIres_pf4_selected_table_base_principal
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  let jzero : {j : ℕ // j < p} := ⟨0, hp0⟩
  have hbaseNatural :
      μ 0 0 = Section1.principalCharacter Smax := by
    calc
      μ 0 0 = piChar (fI izero) (fJ jzero) := (hentry izero jzero).symm
      _ = piChar i0 j0 := by
        rw [← hfI0, ← hfJ0]
      _ = Section1.principalCharacter Smax := hselectedBase
  have hdistinctNatural :
      ∀ i1 i2 : {i : ℕ // i < q},
        ∀ j1 j2 : {j : ℕ // j < p},
          μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2 :=
    section13_typeP_prTIres_natural_mu_pairwise_distinct_core_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource hnotationForSource
  refine ⟨hbaseNatural, hdistinctNatural, ?_⟩
  intro I' J' instI' decI' instJ' decJ' Wsec' A0' i0' j0' piChar'
    δSign' ωsec' σsec' hpackage' _hp0'
  letI : Fintype I' := instI'
  letI : DecidableEq I' := decI'
  letI : Fintype J' := instJ'
  letI : DecidableEq J' := decJ'
  rcases
      section13_typeP_prTIres_pf4_natural_table_normalized_functions_choice_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource hnotationForSource
        hq0 _hp0'
        Wsec' A0' i0' j0' piChar' δSign' ωsec' σsec' hpackage' with
    ⟨fI', fJ', _hfI0', _hfJ0', hentry'⟩
  exact ⟨fI', fJ', hentry'⟩


public theorem section13_typeP_prTIres_natural_mu_base_principal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    μ 0 0 = Section1.principalCharacter Smax := by
  exact
    (section13_typeP_prTIres_natural_primeTIirr_package_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation).1


public theorem section13_typeP_prTIres_natural_mu_pairwise_distinct_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∀ i1 i2 : {i : ℕ // i < q},
      ∀ j1 j2 : {j : ℕ // j < p},
        μ i1.1 j1.1 = μ i2.1 j2.1 → i1 = i2 ∧ j1 = j2 := by
  exact
    section13_typeP_prTIres_natural_mu_pairwise_distinct_core_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation

/- Checked projection for the natural-row/Section `(4.6)` table convention once
the source-selected Section `(4.6)` package and natural positivity have already
been extracted.  Injectivity and zero-column normalization are checked
separately from natural `μ` source facts. -/
public theorem section13_typeP_prTIres_pf4_natural_table_entry_functions_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (_hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (hp0 : 0 < p) :
    ∃ fI : {i : ℕ // i < q} → I,
      ∃ fJ : {j : ℕ // j < p} → J,
        ∀ i : {i : ℕ // i < q},
          ∀ j : {j : ℕ // j < p},
            piChar (fI i) (fJ j) = μ i.1 j.1 := by
  exact
    (section13_typeP_prTIres_natural_primeTIirr_package_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation).2.2
        Wsec A0 i0 j0 piChar δSign ωsec σsec _hpackage hp0


public theorem section13_typeP_prTIres_pf4_natural_table_function_compatibility_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS)
    (hp0 : 0 < p) :
    ∃ fI : {i : ℕ // i < q} → I,
      ∃ fJ : {j : ℕ // j < p} → J,
        Function.Injective fI ∧
          Function.Injective fJ ∧
            fJ ⟨0, hp0⟩ = j0 ∧
              ∀ i : {i : ℕ // i < q},
                ∀ j : {j : ℕ // j < p},
                  piChar (fI i) (fJ j) = μ i.1 j.1 := by
  have hnotationAll := hnotation
  rcases hnotation with ⟨hωData, _hnotationRest⟩
  rcases hωData with ⟨_h31, hq0, _hp0Notation, _ωFin, _h33, _hωeq⟩
  rcases
      section13_typeP_prTIres_pf4_natural_table_entry_functions_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotationAll
        Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage hp0 with
    ⟨fI, fJ, hentry⟩
  have hmuDistinct :=
    section13_typeP_prTIres_natural_mu_pairwise_distinct_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotationAll
  have hmuBase :
      μ 0 0 = Section1.principalCharacter Smax :=
    section13_typeP_prTIres_natural_mu_base_principal_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotationAll
  have hselectedBase :
      piChar i0 j0 = Section1.principalCharacter Smax :=
    section13_typeP_prTIres_pf4_selected_table_base_principal
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  have hselectedDistinct :
      ∀ p q : I × J, p ≠ q → piChar p.1 p.2 ≠ piChar q.1 q.2 :=
    section13_typeP_prTIres_pf4_selected_table_pairwise_distinct
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS hpackage
  let izero : {i : ℕ // i < q} := ⟨0, hq0⟩
  let jzero : {j : ℕ // j < p} := ⟨0, hp0⟩
  have hzero : fJ jzero = j0 := by
    have hentryBase :
        piChar (fI izero) (fJ jzero) = piChar i0 j0 := by
      calc
        piChar (fI izero) (fJ jzero) = μ 0 0 := hentry izero jzero
        _ = Section1.principalCharacter Smax := hmuBase
        _ = piChar i0 j0 := hselectedBase.symm
    have hpair : (fI izero, fJ jzero) = (i0, j0) := by
      by_contra hne
      exact hselectedDistinct (fI izero, fJ jzero) (i0, j0) hne hentryBase
    exact congrArg Prod.snd hpair
  refine ⟨fI, fJ, ?_, ?_, hzero, hentry⟩
  · intro i1 i2 hfi
    have hmu :
        μ i1.1 (0 : ℕ) = μ i2.1 (0 : ℕ) := by
      calc
        μ i1.1 (0 : ℕ) = piChar (fI i1) (fJ ⟨0, hp0⟩) :=
          (hentry i1 ⟨0, hp0⟩).symm
        _ = piChar (fI i2) (fJ ⟨0, hp0⟩) := by rw [hfi]
        _ = μ i2.1 (0 : ℕ) := hentry i2 ⟨0, hp0⟩
    exact (hmuDistinct i1 i2 ⟨0, hp0⟩ ⟨0, hp0⟩ hmu).1
  · intro j1 j2 hfj
    have hmu :
        μ izero.1 j1.1 = μ izero.1 j2.1 := by
      calc
        μ izero.1 j1.1 = piChar (fI izero) (fJ j1) :=
          (hentry izero j1).symm
        _ = piChar (fI izero) (fJ j2) := by rw [hfj]
        _ = μ izero.1 j2.1 := hentry izero j2
    exact (hmuDistinct izero izero j1 j2 hmu).2

/- Checked notation unpacking around the remaining table-compatibility source
leaf.  Natural positivity comes from the Section 13 `ω` notation package. -/
public theorem section13_typeP_prTIres_pf4_natural_table_indexing_functions_for_package_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    {I J : Type u}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    (Wsec : Subgroup Smax)
    (A0 : Set Smax)
    (i0 : I)
    (j0 : J)
    (piChar : I → J → Section1.ClassFunction Smax)
    (δSign : J → ℤ)
    (ωsec : I → J → Section1.ClassFunction Wsec)
    (σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G)
    (hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS) :
    ∃ hp0 : 0 < p,
      ∃ fI : {i : ℕ // i < q} → I,
        ∃ fJ : {j : ℕ // j < p} → J,
          Function.Injective fI ∧
            Function.Injective fJ ∧
              fJ ⟨0, hp0⟩ = j0 ∧
                ∀ i : {i : ℕ // i < q},
                  ∀ j : {j : ℕ // j < p},
                    piChar (fI i) (fJ j) = μ i.1 j.1 := by
  have hnotationAll := hnotation
  rcases hnotation with ⟨hωData, _hnotationRest⟩
  rcases hωData with ⟨_h31, _hq0, hp0, _ωFin, _h33, _hωeq⟩
  rcases
      section13_typeP_prTIres_pf4_natural_table_function_compatibility_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotationAll
        Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage hp0 with
    ⟨fI, fJ, hfI, hfJ, hzero, hentry⟩
  exact ⟨hp0, fI, fJ, hfI, hfJ, hzero, hentry⟩

/- Checked extraction of the source-selected Section `(4.6)` package from the
Section 13 source data.  The only remaining source content is the compatibility
of that selected package with natural `μ i j` indexing. -/
public theorem section13_typeP_prTIres_pf4_natural_table_indexing_functions_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        ∃ Wsec : Subgroup Smax, ∃ A A0 : Set Smax,
          ∃ i0 : I, ∃ j0 : J,
            ∃ piChar : I → J → Section1.ClassFunction Smax,
              ∃ δSign : J → ℤ,
                ∃ ωsec : I → J → Section1.ClassFunction Wsec,
                  ∃ σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G,
                    @Section10.section10FourSixNotationSupportedData G _ _ I J
                        instI instJ decI decJ Smax W1 W2 Wsec A A0 i0 j0
                        piChar δSign ωsec σsec τS ∧
                      ∃ hp0 : 0 < p,
                        ∃ fI : {i : ℕ // i < q} → I,
                          ∃ fJ : {j : ℕ // j < p} → J,
                            Function.Injective fI ∧
                              Function.Injective fJ ∧
                                fJ ⟨0, hp0⟩ = j0 ∧
                                  ∀ i : {i : ℕ // i < q},
                                    ∀ j : {j : ℕ // j < p},
                                      piChar (fI i) (fJ j) = μ i.1 j.1 := by
  have hsourceAll := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, _hMin, hTauS, _hTauT⟩
  rcases hTauS with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, _A, A0, i0, j0, piChar,
      δSign, ωsec, σsec, hnotation10, hSigmaAgree, ⟨H_cyclicA0, hCyclicA0, hTauCyclicA0, hBook⟩⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  have hpackage : section13_typeP_prTIres_pf4_sourceSelectedPackageData
      Smax P U W1 W2 Wsec A0 i0 j0 piChar δSign ωsec σsec τS :=
    ⟨_A, hnotation10, hSigmaAgree,
      ⟨H_cyclicA0, hCyclicA0, hTauCyclicA0, hBook⟩⟩
  rcases
      section13_typeP_prTIres_pf4_natural_table_indexing_functions_for_package_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsourceAll hnotation
        Wsec A0 i0 j0 piChar δSign ωsec σsec hpackage with
    ⟨hp0, fI, fJ, hfI, hfJ, hzero, hentry⟩
  refine ⟨I, instI, decI, J, instJ, decJ, Wsec, _A, A0, i0, j0, piChar, δSign,
    ωsec, σsec, hnotation10, hp0, fI, fJ, hfI, hfJ, hzero, hentry⟩

/- Source leaf for the natural-row/Section `(4.6)` table convention.  At this
point the Section `(4.6)` package has already been extracted and checked from
the Section 13 source data; the remaining source content is the existence of
compatible bounded row/column equivalences, with natural zero mapped to the
source base column.  This is invariant under relabeling the arbitrary finite
Section `(4.6)` row and column types. -/
public theorem section13_typeP_prTIres_pf4_natural_table_indexing_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        ∃ Wsec : Subgroup Smax, ∃ A A0 : Set Smax,
          ∃ i0 : I, ∃ j0 : J,
            ∃ piChar : I → J → Section1.ClassFunction Smax,
              ∃ δSign : J → ℤ,
                ∃ ωsec : I → J → Section1.ClassFunction Wsec,
                  ∃ σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G,
                    @Section10.section10FourSixNotationSupportedData G _ _ I J
                        instI instJ decI decJ Smax W1 W2 Wsec A A0 i0 j0
                        piChar δSign ωsec σsec τS ∧
                      ∃ hp0 : 0 < p,
                        ∃ eI : {i : ℕ // i < q} ≃ I,
                          ∃ eJ : {j : ℕ // j < p} ≃ J,
                            eJ ⟨0, hp0⟩ = j0 ∧
                              ∀ i : {i : ℕ // i < q},
                                ∀ j : {j : ℕ // j < p},
                                  piChar (eI i) (eJ j) = μ i.1 j.1 := by
  classical
  rcases
      section13_typeP_prTIres_pf4_natural_table_indexing_functions_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hsource hnotation with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, piChar, δSign,
      ωsec, σsec, hnotation10, hp0, fI, fJ, hfI, hfJ, hzero, hentry⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, hp, hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, _hMin, _hTauS, _hTauT⟩
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMF.1 with ⟨hP_le_Smax, _hPnorm, _hPnil, _hPHall⟩
  rcases hW1Hall with ⟨hW1leSmax, _hW1HallSub⟩
  have hW2leSmax : W2 ≤ Smax := fun x hx => hP_le_Smax ((hW2le hx).1)
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨_σM, _xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, _h43b, _h43c, _h43d, _h45a, _h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hcardI : Fintype.card I = q := by
    calc
      Fintype.card I = Nat.card (W1.subgroupOf Smax) := hω.card_left
      _ = Nat.card W1 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hW1leSmax).toEquiv
      _ = q := hq.symm
  have hcardJ : Fintype.card J = p := by
    calc
      Fintype.card J = Nat.card (W2.subgroupOf Smax) := hω.card_right
      _ = Nat.card W2 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hW2leSmax).toEquiv
      _ = p := hp.symm
  have hcardBoundedI : Fintype.card {i : ℕ // i < q} = q := by
    let eFin : {i : ℕ // i < q} ≃ Fin q :=
      { toFun := fun i => ⟨i.1, i.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := by
          intro i
          cases i
          rfl
        right_inv := by
          intro i
          cases i
          rfl }
    exact (Fintype.card_congr eFin).trans (Fintype.card_fin q)
  have hcardBoundedJ : Fintype.card {j : ℕ // j < p} = p := by
    let eFin : {j : ℕ // j < p} ≃ Fin p :=
      { toFun := fun j => ⟨j.1, j.2⟩
        invFun := fun j => ⟨j.1, j.2⟩
        left_inv := by
          intro j
          cases j
          rfl
        right_inv := by
          intro j
          cases j
          rfl }
    exact (Fintype.card_congr eFin).trans (Fintype.card_fin p)
  have hbijI : Function.Bijective fI :=
    (Fintype.bijective_iff_injective_and_card fI).2
      ⟨hfI, hcardBoundedI.trans hcardI.symm⟩
  have hbijJ : Function.Bijective fJ :=
    (Fintype.bijective_iff_injective_and_card fJ).2
      ⟨hfJ, hcardBoundedJ.trans hcardJ.symm⟩
  let eI : {i : ℕ // i < q} ≃ I := Equiv.ofBijective fI hbijI
  let eJ : {j : ℕ // j < p} ≃ J := Equiv.ofBijective fJ hbijJ
  refine ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, piChar, δSign,
    ωsec, σsec, hnotation10, hp0, eI, eJ, ?_, ?_⟩
  · simpa [eJ] using hzero
  · intro i j
    simpa [eI, eJ] using hentry i j

/- Checked wrapper extracting the Section `(4.6)` package from the Section 13
source data before delegating only the natural table-indexing convention. -/
public theorem section13_typeP_prTIres_pf4_natural_muTable_equiv_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ I : Type u, ∃ instI : Fintype I, ∃ decI : DecidableEq I,
      ∃ J : Type u, ∃ instJ : Fintype J, ∃ decJ : DecidableEq J,
        ∃ Wsec : Subgroup Smax, ∃ A A0 : Set Smax,
          ∃ i0 : I, ∃ j0 : J,
            ∃ piChar : I → J → Section1.ClassFunction Smax,
              ∃ δSign : J → ℤ,
                ∃ ωsec : I → J → Section1.ClassFunction Wsec,
                  ∃ σsec : Section1.ClassFunction Wsec →ₗ[ℂ] Section1.ClassFunction G,
                    ∃ xCharD : J → Section1.ClassFunction (derivedSubgroup Smax),
                      @Section10.section10FourSixNotationSupportedData G _ _ I J
                          instI instJ decI decJ Smax W1 W2 Wsec A A0 i0 j0
                          piChar δSign ωsec σsec τS ∧
                        @Section4Scratch.theorem_4_5_a_statement Smax _ _
                            (derivedSubgroup Smax) I J instI instJ piChar xCharD ∧
                          @Section4Scratch.theorem_4_5_b_statement Smax _ _
                              (derivedSubgroup Smax) I J instI instJ piChar xCharD ∧
                            piChar i0 j0 = Section1.principalCharacter Smax ∧
                              Fintype.card I = q ∧
                                Fintype.card J = p ∧
                                  ∃ hp0 : 0 < p,
                                    ∃ eI : {i : ℕ // i < q} ≃ I,
                                      ∃ eJ : {j : ℕ // j < p} ≃ J,
                                        eJ ⟨0, hp0⟩ = j0 ∧
                                          ∀ i : {i : ℕ // i < q},
                                            ∀ j : {j : ℕ // j < p},
                                              piChar (eI i) (eJ j) = μ i.1 j.1 := by
  rcases
      section13_typeP_prTIres_pf4_natural_table_indexing_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, piChar, δSign,
      ωsec, σsec, hnotation10, hp0, eI, eJ, hzeroIndex, hentry⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, hp, hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, _hMin, _hTauS, _hTauT⟩
  rcases hptypeS with
    ⟨hMF, _hW1cyc, _hW1ne, hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMF.1 with ⟨hP_le_Smax, _hPnorm, _hPnil, _hPHall⟩
  rcases hW1Hall with ⟨hW1leSmax, _hW1HallSub⟩
  have hW2leSmax : W2 ≤ Smax := fun x hx => hP_le_Smax ((hW2le hx).1)
  rcases Section10.supportedFourSixData_of_section10FourSixNotationSupportedData hnotation10 with
    ⟨σM, xCharD, _H_A, _H_A0, hFull⟩
  rcases hFull with
    ⟨_h46, _hW2K, _h31, _hIso, _hVirt, _hClass, _hPrin, _h22A,
      hFullRest⟩
  rcases hFullRest with
    ⟨hω, h43b, _h43c, _h43d, h45a, h45b, _hTauCyc, _hTauA0,
      _hTauIso, _hTauPunct, _hTauVirt, _hPF39⟩
  have hbase :
      piChar i0 j0 = Section1.principalCharacter Smax :=
    (Section4.proposition_4_4_base
      (W1 := W1.subgroupOf Smax)
      (W2 := W2.subgroupOf Smax)
      (W := Wsec)
      (I := I)
      (J := J)
      (i0 := i0)
      (j0 := j0)
      (ω := ωsec)
      (σ := σM)
      (piChar := piChar)
      (deltaSign := fun j => (δSign j : ℂ))
      hω h43b).2
  have hcardI : Fintype.card I = q := by
    calc
      Fintype.card I = Nat.card (W1.subgroupOf Smax) := hω.card_left
      _ = Nat.card W1 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hW1leSmax).toEquiv
      _ = q := hq.symm
  have hcardJ : Fintype.card J = p := by
    calc
      Fintype.card J = Nat.card (W2.subgroupOf Smax) := hω.card_right
      _ = Nat.card W2 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hW2leSmax).toEquiv
      _ = p := hp.symm
  exact ⟨I, instI, decI, J, instJ, decJ, Wsec, A, A0, i0, j0, piChar,
    δSign, ωsec, σsec, xCharD, hnotation10, h45a, h45b, hbase, hcardI,
    hcardJ, hp0, eI, eJ, hzeroIndex, hentry⟩

private theorem section13_typeP_prTIres_nonrow_induced_irreducible_of_pf4_range
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax P U : Subgroup G}
    {p : ℕ}
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    (piChar : I → J → Section1.ClassFunction Smax)
    (xChar : J → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (h45b : Section4Scratch.theorem_4_5_b_statement
      ((P ⊔ U).subgroupOf Smax) piChar xChar)
    (rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hrange : Set.range (fun j : {j : ℕ // j < p} => rowSource j) =
      Set.range xChar)
    (ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψnonrow : ψ ∉ Set.range (fun j : {j : ℕ // j < p} => rowSource j)) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  exact (h45b.1 ψ hψirr (by
    intro hx
    exact hψnonrow (by simpa [hrange.symm] using hx))).1

/- Checked projection: the Type-P Section `(4.6)` package in the Section 13
source data contains the PF `(4.5.a)/(4.5.b)` row-source package over
`derivedSubgroup Smax`. -/


private theorem section13_typeP_prTIres_derivedSubgroup_eq_P_sup_U_subgroupOf
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    derivedSubgroup Smax = (P ⊔ U).subgroupOf Smax := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  have hsub : (P ⊔ U).subgroupOf Smax = derivedSubgroup Smax := by
    have hbase := section12_ambientDerivedSubgroup_subgroupOf_eq (G := G) (E := Smax)
    rw [hDercomp.2.2.1] at hbase
    exact hbase
  exact hsub.symm

private theorem section13_typeP_prTIres_pf4_transport_of_subgroup_eq
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax P U : Subgroup G}
    {I J : Type u}
    [Fintype I]
    [Fintype J]
    (hK : derivedSubgroup Smax = (P ⊔ U).subgroupOf Smax)
    (piChar : I → J → Section1.ClassFunction Smax)
    (xCharD : J → Section1.ClassFunction (derivedSubgroup Smax))
    (h45aD : Section4Scratch.theorem_4_5_a_statement
      (derivedSubgroup Smax) piChar xCharD)
    (h45bD : Section4Scratch.theorem_4_5_b_statement
      (derivedSubgroup Smax) piChar xCharD) :
    ∃ xChar : J → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      Section4Scratch.theorem_4_5_a_statement
          ((P ⊔ U).subgroupOf Smax) piChar xChar ∧
        Section4Scratch.theorem_4_5_b_statement
          ((P ⊔ U).subgroupOf Smax) piChar xChar := by
  rw [← hK]
  exact ⟨xCharD, h45aD, h45bD⟩

/- Checked wrapper adding PF `(4.5)` transport, the Section 13 row-sum
definition, and the base-column kernel fact to the source-provided compatible
table package. -/
public theorem section13_typeP_prTIres_pf4_natural_index_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ hp0 : 0 < p,
      ∃ I : Type u, ∃ instI : Fintype I,
        ∃ J : Type u, ∃ instJ : Fintype J,
          ∃ piChar : I → J → Section1.ClassFunction Smax,
            ∃ xChar : J → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
              ∃ e : {j : ℕ // j < p} ≃ J,
                @Section4Scratch.theorem_4_5_a_statement Smax _ _
                    ((P ⊔ U).subgroupOf Smax) I J instI instJ piChar xChar ∧
                  @Section4Scratch.theorem_4_5_b_statement Smax _ _
                      ((P ⊔ U).subgroupOf Smax) I J instI instJ piChar xChar ∧
                    (∀ j : {j : ℕ // j < p},
                      Section4Scratch.piColumn piChar (e j) = μsum j) ∧
                    Section1.subgroupInKernel' (xChar (e ⟨0, hp0⟩))
                      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) := by
  classical
  rcases
      section13_typeP_prTIres_pf4_natural_muTable_equiv_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hsource hnotation with
    ⟨I, instI, decI, J, instJ, decJ, _Wsec, _A, _A0, i0, j0, piChar,
      _δSign, _ωsec, _σsec, xCharD, _hnotation10, h45aD, h45bD, hbase,
      _hcardI, _hcardJ, hp0, eI, eJ, hzeroIndex, hentry⟩
  letI : Fintype I := instI
  letI : DecidableEq I := decI
  letI : Fintype J := instJ
  letI : DecidableEq J := decJ
  rcases hnotation with
    ⟨_homega, _hmap, _hη, _hδ, _hδ', _hμirr, _hνirr, _hμnonprincipal,
      _hνnonprincipal, _hμind, _hνind, hμsum, _hνsum⟩
  rcases section13_typeP_prTIres_pf4_transport_of_subgroup_eq
      (section13_typeP_prTIres_derivedSubgroup_eq_P_sup_U_subgroupOf
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        p q u v c d hsource)
      piChar xCharD h45aD h45bD with
    ⟨xChar, h45a, h45b⟩
  have hcolumn :
      ∀ j : {j : ℕ // j < p},
        Section4Scratch.piColumn piChar (eJ j) = μsum j := by
    intro j
    ext g
    have hsumI :
        (∑ i : I, piChar i (eJ j) g) =
          ∑ i : {i : ℕ // i < q}, piChar (eI i) (eJ j) g := by
      exact (Fintype.sum_equiv eI
        (fun i : {i : ℕ // i < q} => piChar (eI i) (eJ j) g)
        (fun i : I => piChar i (eJ j) g)
        (by intro i; rfl)).symm
    have hentrySum :
        (∑ i : {i : ℕ // i < q}, piChar (eI i) (eJ j) g) =
          ∑ i : {i : ℕ // i < q}, μ i.1 j.1 g := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact congrFun (hentry i j) g
    have hrangeSum :
        (∑ i : {i : ℕ // i < q}, μ i.1 j.1 g) =
          (Finset.range q).sum (fun i => μ i j.1 g) := by
      let eRange : {i : ℕ // i < q} ≃ {i : ℕ // i ∈ Finset.range q} :=
        { toFun := fun i => ⟨i.1, (Finset.mem_range).2 i.2⟩
          invFun := fun i => ⟨i.1, (Finset.mem_range).1 i.2⟩
          left_inv := by
            intro i
            cases i
            rfl
          right_inv := by
            intro i
            cases i
            rfl }
      calc
        (∑ i : {i : ℕ // i < q}, μ i.1 j.1 g) =
            ∑ i : {i : ℕ // i ∈ Finset.range q}, μ i.1 j.1 g := by
          exact Fintype.sum_equiv eRange
            (fun i : {i : ℕ // i < q} => μ i.1 j.1 g)
            (fun i : {i : ℕ // i ∈ Finset.range q} => μ i.1 j.1 g)
            (by intro i; rfl)
        _ = (Finset.range q).sum (fun i => μ i j.1 g) := by
          simpa using
            (Finset.sum_attach (s := Finset.range q) (f := fun i => μ i j.1 g))
    calc
      Section4Scratch.piColumn piChar (eJ j) g =
          (∑ i : I, piChar i (eJ j) g) := by
        simp [Section4Scratch.piColumn]
      _ = (Finset.range q).sum (fun i => μ i j.1 g) := by
        rw [hsumI, hentrySum, hrangeSum]
      _ = μsum j g := by
        simp [hμsum j.1 j.2]
  have hzeroBase :
      Section1.subgroupInKernel' (xChar j0)
        ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) :=
    section13_typeP_prTIres_xChar_base_subgroupInKernel
      i0 j0 piChar xChar h45a hbase
  have hzero :
      Section1.subgroupInKernel' (xChar (eJ ⟨0, hp0⟩))
        ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) := by
    simpa [hzeroIndex] using hzeroBase
  exact ⟨hp0, I, instI, J, instJ, piChar, xChar, eJ, h45a, h45b, hcolumn, hzero⟩

/- Checked glue from the natural-index source package to the concrete
natural-numbered row source used by the `S1cases` constituent split. -/
public theorem section13_typeP_prTIres_rowSource_pf4_alignment_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      (∀ j : ℕ, j < p →
        Section1.inducedCF ((P ⊔ U).subgroupOf Smax) (rowSource j) = μsum j) ∧
      Section1.subgroupInKernel' (rowSource 0)
        ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ∧
      ∃ I : Type u, ∃ instI : Fintype I,
        ∃ J : Type u, ∃ instJ : Fintype J,
          ∃ piChar : I → J → Section1.ClassFunction Smax,
            ∃ xChar : J → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
              @Section4Scratch.theorem_4_5_b_statement Smax _ _
                  ((P ⊔ U).subgroupOf Smax) I J instI instJ piChar xChar ∧
                Set.range (fun j : {j : ℕ // j < p} => rowSource j) =
                  Set.range xChar := by
  classical
  rcases
      section13_typeP_prTIres_pf4_natural_index_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨hp0, I, instI, J, instJ, piChar, xChar, e, h45a, h45b, hcolumn, hzero⟩
  letI : Fintype I := instI
  letI : Fintype J := instJ
  let rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax) :=
    fun j => if hj : j < p then xChar (e ⟨j, hj⟩) else xChar (e ⟨0, hp0⟩)
  refine ⟨rowSource, ?_, ?_, I, instI, J, instJ, piChar, xChar, h45b, ?_⟩
  · intro j hj
    have hcol := hcolumn ⟨j, hj⟩
    simpa [rowSource, hj, hcol] using h45a.2.2 (e ⟨j, hj⟩)
  · simpa [rowSource, hp0] using hzero
  · ext ψ
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨e j, ?_⟩
      simp [rowSource, j.property]
    · rintro ⟨j, rfl⟩
      refine ⟨e.symm j, ?_⟩
      simp [rowSource, (e.symm j).property]

/- Checked projection of the natural row-source part of the PF4 alignment
boundary. -/

/- Checked glue combining natural row-source alignment with the PF `(4.5)`
non-row irreducibility branch. -/
public theorem section13_typeP_prTIres_rowSource_classification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    ∃ rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      (∀ j : ℕ, j < p →
        Section1.inducedCF ((P ⊔ U).subgroupOf Smax) (rowSource j) = μsum j) ∧
      Section1.subgroupInKernel' (rowSource 0)
        ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ∧
      ∀ ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ψ ∉ Set.range (fun j : {j : ℕ // j < p} => rowSource j) →
            Section1.IsIrreducibleCharacterOnGroup
              (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  rcases
      section13_typeP_prTIres_rowSource_pf4_alignment_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨rowSource, hrowSource, hrowZero, I, instI, J, instJ, piChar, xChar, h45b,
      hrange⟩
  letI : Fintype I := instI
  letI : Fintype J := instJ
  refine ⟨rowSource, hrowSource, hrowZero, ?_⟩
  intro ψ hψirr hψnonrow
  exact section13_typeP_prTIres_nonrow_induced_irreducible_of_pf4_range
    piChar xChar h45b rowSource hrange ψ hψirr hψnonrow


public theorem section13_typeP_prTIres_constituent_raw_cases_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hH : H = P ⊔ C) :
    ∃ rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      (∀ j : ℕ, j < p →
        Section1.inducedCF ((P ⊔ U).subgroupOf Smax) (rowSource j) = μsum j) ∧
      Section1.subgroupInKernel' (rowSource 0)
        ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) ∧
      ∀ ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
        Section1.IsIrreducibleCharacterOnGroup ψ →
          (∃ j : ℕ, j < p ∧ ψ = rowSource j) ∨
            Section1.IsIrreducibleCharacterOnGroup
              (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  classical
  rcases
      section13_typeP_prTIres_rowSource_classification_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation with
    ⟨rowSource, hrowSource, hrowZero, hnonrow⟩
  refine ⟨rowSource, hrowSource, hrowZero, ?_⟩
  intro ψ hψirr
  by_cases hrow : ψ ∈ Set.range (fun j : {j : ℕ // j < p} => rowSource j)
  · rcases hrow with ⟨j, hj⟩
    exact Or.inl ⟨j.1, j.2, hj.symm⟩
  · exact Or.inr (hnonrow ψ hψirr hrow)

public theorem section13_typeP_prTIres_constituent_cases_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C) :
    ∃ rowSource : ℕ → Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      (∀ j : ℕ, 0 < j → j < p →
        Section1.inducedCF ((P ⊔ U).subgroupOf Smax) (rowSource j) = μsum j) ∧
      ∀ ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
        Section1.IsIrreducibleCharacterOnGroup ψ →
          ¬ Section1.subgroupInKernel' ψ
            ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) →
            (∃ j : ℕ, 0 < j ∧ j < p ∧ ψ = rowSource j) ∨
              Section1.IsIrreducibleCharacterOnGroup
                (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  rcases
      section13_typeP_prTIres_constituent_raw_cases_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨rowSource, hrowSource, hrowZero, hcases⟩
  refine ⟨rowSource, ?_, ?_⟩
  · intro j _hj0 hjp
    exact hrowSource j hjp
  · intro ψ hψirr hψnotker
    rcases hcases ψ hψirr with ⟨j, hjp, hψeq⟩ | hirr
    · by_cases hjzero : j = 0
      · subst j
        exfalso
        apply hψnotker
        simpa [hψeq] using hrowZero
      · exact Or.inl ⟨j, Nat.pos_of_ne_zero hjzero, hjp, hψeq⟩
    · exact Or.inr hirr

public theorem section13_calS1_P_sup_U_constituent_row_sum_or_induced_irreducible_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψnotker : ¬ Section1.subgroupInKernel' ψ
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))) :
    (∃ j : ℕ, 0 < j ∧ j < p ∧
      Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ = μsum j) ∨
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  rcases
      section13_typeP_prTIres_constituent_cases_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d hsource hnotation hH with
    ⟨rowSource, hrowSource, hcases⟩
  rcases hcases ψ hψirr hψnotker with ⟨j, hj0, hjp, hψeq⟩ | hirr
  · exact Or.inl ⟨j, hj0, hjp, by simpa [hψeq] using hrowSource j hj0 hjp⟩
  · exact Or.inr hirr

private theorem section13_scalarProduct_characters_ne_zero_of_common_irreducible
    {K : Type u} [Group K] [Finite K]
    (χ ξ φ : Section1.ClassFunction K)
    (hχchar : Section1.IsCharacter χ)
    (hξchar : Section1.IsCharacter ξ)
    (hφirr : Section1.IsIrreducibleCharacterOnGroup φ)
    (hχφ : Section1.scalarProduct K χ φ ≠ 0)
    (hφξ : Section1.scalarProduct K φ ξ ≠ 0) :
    Section1.scalarProduct K χ ξ ≠ 0 := by
  classical
  have hχne : χ ≠ 0 := by
    intro hχzero
    apply hχφ
    simp [hχzero, Section1.scalarProduct]
  rcases Section1.exists_positive_irreducible_decomposition_of_character
      χ hχchar hχne with
    ⟨ι, hι, hιdec, e, φs, _i0, hepos, hφsbook, _hφspair, hχdecomp⟩
  letI : Fintype ι := hι
  letI : DecidableEq ι := hιdec
  have hφsirr : ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (φs i) := by
    intro i
    exact Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (φs i) (hφsbook i)
  have hoccurs : ∃ i : ι, φs i = φ := by
    by_contra hnone
    push Not at hnone
    apply hχφ
    rw [hχdecomp, Section1.scalarProduct_weightedFamilySum_left]
    exact Finset.sum_eq_zero fun i _hi => by
      rw [Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hφsirr i) hφirr (hnone i)]
      simp
  rcases hoccurs with ⟨iφ, hiφ⟩
  choose n hn using fun i : ι =>
    Section1.scalarProduct_character_character_eq_nat
      (φs i) ξ (hφsbook i).1 hξchar
  haveI : Finite ι := Finite.of_fintype ι
  let univι : Finset ι := @Finset.univ ι (Fintype.ofFinite ι)
  let total : ℕ := ∑ i ∈ univι, e i * n i
  have hn_iφ_ne : n iφ ≠ 0 := by
    intro hnzero
    apply hφξ
    have hsp : Section1.scalarProduct K φ ξ = (n iφ : ℂ) := by
      simpa [hiφ] using hn iφ
    rw [hsp, hnzero]
    simp
  have hsum_nat :
      Section1.scalarProduct K χ ξ =
        (total : ℂ) := by
    rw [hχdecomp, Section1.scalarProduct_weightedFamilySum_left]
    change (∑ i ∈ univι, (e i : ℂ) * Section1.scalarProduct K (φs i) ξ) =
      (total : ℂ)
    calc
      (∑ i ∈ univι, (e i : ℂ) * Section1.scalarProduct K (φs i) ξ) =
          ∑ i ∈ univι, (e i : ℂ) * (n i : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [hn i]
      _ = (total : ℂ) := by
            simp [total, univι, Nat.cast_sum, Nat.cast_mul]
  have hsum_pos : 0 < total := by
    have hterm_pos : 0 < e iφ * n iφ :=
      Nat.mul_pos (hepos iφ) (Nat.pos_of_ne_zero hn_iφ_ne)
    exact lt_of_lt_of_le hterm_pos
      (Finset.single_le_sum
        (fun i _hi => Nat.zero_le (e i * n i)) (by simp [univι]))
  intro hzero
  rw [hsum_nat] at hzero
  have hnat_ne : (total : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hsum_pos)
  exact hnat_ne hzero

/- Source bridge for the character-theoretic induction step in the row branch:
if the irreducible `ψ` occurs in the character `θPU` and induces to the
nonzero row character, then that row has nonzero scalar product with the
induced `θPU`. -/
public theorem section13_inducedCF_pairing_ne_zero_of_constituent_row_source
    {G : Type u}
    [Group G]
    [Finite G]
    (T : Subgroup G)
    (θPU ψ : Section1.ClassFunction T)
    (rowG : Section1.ClassFunction G)
    (hθPUchar : Section1.IsCharacter θPU)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hrowchar : Section1.IsCharacter rowG)
    (hθψ : Section1.scalarProduct T θPU ψ ≠ 0)
    (hψrow : Section1.inducedCF T ψ = rowG) :
      Section1.scalarProduct G (Section1.inducedCF T θPU) rowG ≠ 0 := by
  classical
  have hrowclass : Section1.IsClassFunction rowG :=
    Section1.isCharacter_isClassFunction rowG hrowchar
  have hψdegree : Section1.degree ψ ≠ 0 := by
    rcases Section10.exists_pos_nat_degree_of_irreducible_character hψirr with
      ⟨n, hn, hdegree⟩
    rw [hdegree]
    exact_mod_cast (Nat.ne_of_gt hn)
  have hrowne : rowG ≠ 0 := by
    intro hrowzero
    have hindzero : Section1.inducedCF T ψ = 0 := hψrow.trans hrowzero
    have hdegreezero := congrArg Section1.degree hindzero
    rw [Section1.degree_inducedClassFunction] at hdegreezero
    have hindex : (Subgroup.index T : ℂ) ≠ 0 := by
      exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := T))
    apply mul_ne_zero hindex hψdegree
    simpa [Section1.degree] using hdegreezero
  have hrowself : Section1.scalarProduct G rowG rowG ≠ 0 := by
    rw [Section5.scalarProduct_self_eq_cfNormSq rowG]
    intro hnorm
    have hnormReal : Section5.cfNormSq rowG = 0 := by
      exact_mod_cast hnorm
    exact hrowne (Section5.cfNormSq_eq_zero hnormReal)
  have hψres : Section1.scalarProduct T ψ
      (Section1.subgroupRestriction T rowG) ≠ 0 := by
    rw [← Section1.scalarProduct_inducedCF_left T ψ rowG hrowclass]
    simpa [hψrow] using hrowself
  have hreschar : Section1.IsCharacter (Section1.subgroupRestriction T rowG) := by
    rcases Section1.subgroupRestriction_eq_representation_character_of_isCharacter
        T rowG hrowchar with
      ⟨V, _hadd, _hmod, _hfd, ρ, hres⟩
    exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hres⟩
  have htargetT : Section1.scalarProduct T θPU
      (Section1.subgroupRestriction T rowG) ≠ 0 :=
    section13_scalarProduct_characters_ne_zero_of_common_irreducible
      θPU (Section1.subgroupRestriction T rowG) ψ
      hθPUchar hreschar hψirr hθψ hψres
  rw [Section1.scalarProduct_inducedCF_left T θPU rowG hrowclass]
  exact htargetT


public theorem section13_calS1_P_sup_U_constituent_row_sum_pairing_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d j : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ)
    (hj0 : 0 < j)
    (hjp : j < p)
    (hψrow : Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ = μsum j) :
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) ≠ 0 := by
  have hHlePU := section13_H_le_P_sup_U_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
    hsource hH
  have hHT : H.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact hHlePU hx
  have hθchar : Section1.IsCharacter θ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθirr
  have hθsubchar : Section1.IsCharacter
      (Section1.subgroupOfClassFunction
        (T := (P ⊔ U).subgroupOf Smax) θ) :=
    Section1.isCharacter_subgroupOfClassFunction_of_le hHT θ hθchar
  have hθPUchar : Section1.IsCharacter θPU := by
    rw [hθPUeq]
    exact Section1.isCharacter_inducedCF_of_isCharacter
      ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
      (Section1.subgroupOfClassFunction
        (T := (P ⊔ U).subgroupOf Smax) θ)
      hθsubchar
  have h13_3 := (theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsource).1
  rcases (h13_3 ω η μ ν μsum νsum δ δ' σ hnotation).2 with
    ⟨_τ1, _hExt, houtput⟩
  have hrowchar : Section1.IsCharacter (μsum j) :=
    (houtput.1 j hj0 hjp).1
  have hψclass : Section1.IsClassFunction ψ :=
    Section1.isCharacter_isClassFunction ψ
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hψirr)
  have hspInd :
      Section1.scalarProduct ((P ⊔ U).subgroupOf Smax)
        (Section1.inducedCF
          ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
          (Section1.subgroupOfClassFunction θ)) ψ ≠ 0 :=
    (Section1.liesAbove_iff_scalarProduct_induced_ne_zero
      (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax) ψ θ hψclass).mp hψlies
  have hθψ : Section1.scalarProduct ((P ⊔ U).subgroupOf Smax) θPU ψ ≠ 0 := by
    simpa [hθPUeq] using hspInd
  exact section13_inducedCF_pairing_ne_zero_of_constituent_row_source
    ((P ⊔ U).subgroupOf Smax) θPU ψ (μsum j)
    hθPUchar hψirr hrowchar hθψ hψrow


public theorem section13_calS1_P_sup_U_constituent_row_pairing_or_induced_irreducible_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ)
    (hψnotker : ¬ Section1.subgroupInKernel' ψ
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))) :
    (∃ j : ℕ, 0 < j ∧ j < p ∧
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) ≠ 0) ∨
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  classical
  rcases
      section13_calS1_P_sup_U_constituent_row_sum_or_induced_irreducible_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hsource hnotation hH ψ hψirr hψnotker with
    ⟨j, hj0, hjp, hψrow⟩ | hirr
  · exact Or.inl ⟨j, hj0, hjp,
      section13_calS1_P_sup_U_constituent_row_sum_pairing_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d j
        hsource hnotation hH θ θPU ψ hθPUeq hθirr hψirr hψlies hj0 hjp hψrow⟩
  · exact Or.inr hirr


public theorem section13_calS1_inducedCF_P_sup_U_constituent_induced_irreducible_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (_hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ)
    (hψnotker : ¬ Section1.subgroupInKernel' ψ
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)))
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0) :
    Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  classical
  rcases
      section13_calS1_P_sup_U_constituent_row_pairing_or_induced_irreducible_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hsource hnotation hH θ θPU ψ hθPUeq hθirr hψirr hψlies hψnotker with
    ⟨j, hj0, hjp, hrow⟩ | hirr
  · exact False.elim (hrow (horth j hj0 hjp))
  · exact hirr


public theorem section13_calS1_inducedCF_P_sup_U_constituent_mem_irreducibleSubfamily_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ)
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0) :
    Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ ∈
      section13_irreducibleSubfamily Smax Sfam := by
  classical
  have hsourceAll := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, hSfam, _hTfam, _hDadeS, _hDadeT, _hnotationData⟩
  have hψnotker : ¬ Section1.subgroupInKernel' ψ
      ((P.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax)) :=
    section13_calS1_P_sup_U_constituent_not_subgroupInKernel_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsourceAll hH θ ψ hθirr hθnotker hψirr hψlies
  have hmemS : Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ ∈ Sfam :=
    (hSfam.2.2 (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ)).2
      ⟨ψ, hψirr, hψnotker, rfl⟩
  have hindirr : Section1.IsIrreducibleCharacterOnGroup
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) :=
    section13_calS1_inducedCF_P_sup_U_constituent_induced_irreducible_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsourceAll hnotation hH θ θPU ψ hθirr hθnotker hθPUeq
      hψirr hψlies hψnotker horth
  change Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ ∈
    Sfam.filter (fun φ => Section1.IsIrreducibleCharacterOnGroup φ)
  exact Finset.mem_filter.mpr ⟨hmemS, hindirr⟩


public theorem section13_calS1_inducedCF_P_sup_U_constituent_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU ψ : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hψirr : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hψlies : Section1.LiesAbove (H.subgroupOf Smax) ((P ⊔ U).subgroupOf Smax)
      ψ θ)
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0) :
    Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam)
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) ψ) := by
  exact Section5.integerSpan_of_mem (section13_irreducibleSubfamily Smax Sfam)
    (section13_calS1_inducedCF_P_sup_U_constituent_mem_irreducibleSubfamily_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH θ θPU ψ hθirr hθnotker hθPUeq
      hψirr hψlies horth)


public theorem section13_calS1_inducedCF_P_sup_U_constituent_span_decomposition_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0) :
    ∃ ι : Type u, ∃ _ : Finite ι,
      ∃ (e : ι → ℕ) (χ : ι → Section1.ClassFunction Smax),
        Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU =
          Section1.weightedFamilySum (fun i => (e i : ℂ)) χ ∧
        ∀ i, Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) (χ i) := by
  rcases section13_calS1_P_sup_U_constituent_decomposition_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH θ θPU hθirr hθnotker hθPUeq with
    ⟨ι, hι, e, ψ, hdecompPU, hψirr, hψlies⟩
  letI : Finite ι := hι
  refine ⟨ι, hι, e, (fun i =>
    Section1.inducedCF ((P ⊔ U).subgroupOf Smax) (ψ i)), ?_, ?_⟩
  · rw [hdecompPU]
    exact Section1.inducedCF_weightedFamilySum
      ((P ⊔ U).subgroupOf Smax) (fun i => (e i : ℂ)) ψ
  · intro i
    exact section13_calS1_inducedCF_P_sup_U_constituent_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH θ θPU (ψ i) hθirr hθnotker hθPUeq
      (hψirr i) (hψlies i) horth


public theorem section13_calS1_inducedCF_P_sup_U_integerSpan_of_constituent_classification_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0) :
    Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam)
      (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) := by
  rcases section13_calS1_inducedCF_P_sup_U_constituent_span_decomposition_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH θ θPU hθirr hθnotker hθPUeq horth with
    ⟨ι, hι, e, χ, hdecomp, hχspan⟩
  letI : Finite ι := hι
  rw [hdecomp]
  exact section13_integerSpan_weightedFamilySum_nat
    (section13_irreducibleSubfamily Smax Sfam) e χ hχspan

public theorem section13_calS1_integerSpan_of_intermediate_induced_row_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (ζ : Section1.ClassFunction Smax)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hθPUeq : θPU =
      Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ))
    (hζeqPU : ζ = Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU)
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax ζ (μsum j) = 0) :
    Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) ζ := by
  have horthPU : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax
        (Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU) (μsum j) = 0 := by
    intro j hj0 hjp
    simpa [hζeqPU] using horth j hj0 hjp
  simpa [hζeqPU] using
    section13_calS1_inducedCF_P_sup_U_integerSpan_of_constituent_classification_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH θ θPU hθirr hθnotker hθPUeq horthPU


public theorem section13_calS1_integerSpan_of_inducing_character_row_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (ζ : Section1.ClassFunction Smax)
    (θ : Section1.ClassFunction (H.subgroupOf Smax))
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hθnotker : ¬ Section1.subgroupInKernel' θ
      ((P.subgroupOf Smax).subgroupOf (H.subgroupOf Smax)))
    (hζeq : ζ = Section1.inducedCF (H.subgroupOf Smax) θ)
    (horth : ∀ j : ℕ, 0 < j → j < p →
      Section1.scalarProduct Smax ζ (μsum j) = 0) :
    Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) ζ := by
  rcases section13_calS1_inducedCF_from_P_sup_U_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource hH ζ θ hζeq with
    ⟨θPU, hθPUeq, hζeqPU⟩
  exact section13_calS1_integerSpan_of_intermediate_induced_row_orthogonal_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsource hnotation hH ζ θ θPU hθirr hθnotker hθPUeq hζeqPU horth

public theorem section13_calS1_integerSpan_of_row_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      (∀ j : ℕ, 0 < j → j < p →
        Section1.scalarProduct Smax ζ (μsum j) = 0) →
      Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) ζ := by
  intro ζ hζ horth
  rcases (hS1.2.2 ζ).mp hζ with ⟨θ, hθirr, hθnotker, hζeq⟩
  exact section13_calS1_integerSpan_of_inducing_character_row_orthogonal_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
    ω η μ ν μsum νsum δ δ' σ p q u v c d
    hsource hnotation hH ζ θ hθirr hθnotker hζeq horth


public theorem section13_calS1_cases_or_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      (∃ j : ℕ, 0 < j ∧ j < p ∧ ζ = μsum j) ∨
        Section5.integerSpan (section13_irreducibleSubfamily Smax Sfam) ζ := by
  intro ζ hζ
  by_cases hrow :
      ∃ j : ℕ, 0 < j ∧ j < p ∧
        Section1.scalarProduct Smax ζ (μsum j) ≠ 0
  · rcases hrow with ⟨j, hj0, hjp, hpair⟩
    exact Or.inl ⟨j, hj0, hjp,
      section13_calS1_eq_muSum_of_nonzero_scalarProduct
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d j
        hsource hnotation hH S1 hS1 ζ hζ hj0 hjp hpair⟩
  · have horth : ∀ j : ℕ, 0 < j → j < p →
        Section1.scalarProduct Smax ζ (μsum j) = 0 := by
      intro j hj0 hjp
      by_contra hpair
      exact hrow ⟨j, hj0, hjp, hpair⟩
    exact Or.inr
      (section13_calS1_integerSpan_of_row_orthogonal_source
        Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d
        hsource hnotation hH S1 hS1 ζ hζ horth)

private theorem theorem_13_6_calS1_cases_or_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hH : H = P ⊔ C)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      (∃ j : ℕ, 0 < j ∧ j < p ∧ ζ = μsum j) ∨
        Section5.integerSpan (theorem_13_6_irreducibleSubfamily Smax Sfam) ζ := by
  intro ζ hζ
  rcases section13_calS1_cases_or_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsource hnotation hH S1 hS1 ζ hζ with hrow | hspan
  · exact Or.inl hrow
  · exact Or.inr hspan

private theorem theorem_13_6_calS1_subset_integerSpan_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → Section5.integerSpan Sfam ζ := by
  classical
  have hsourceOrig := hsource
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      hnotationData, _hrest⟩
  rcases hnotationData with ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hnotation⟩
  rcases h6hyp with ⟨hH, _hlam_irred, _hdeg, _hind, _hlamτ_eq⟩
  intro ζ hζ
  rcases theorem_13_6_calS1_cases_or_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      ω η μ ν μsum νsum δ δ' σ p q u v c d
      hsourceOrig hnotation hH S1 hS1 ζ hζ with hrow | hspan
  ·
      rcases hrow with ⟨j, hj0, hjp, rfl⟩
      exact theorem_13_6_muSum_mem_integerSpan_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d j
        hsourceOrig hnotation hj0 hjp
  ·
      exact Section5.integerSpan_mono
        (theorem_13_6_irreducibleSubfamily_subset Smax Sfam) hspan

private theorem theorem_13_6_calS1_pairwise_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      ∀ η : Section1.ClassFunction Smax, η ∈ S1 → ζ ≠ η →
        Section1.scalarProduct Smax ζ η = 0 := by
  have hHnormal : (H.subgroupOf Smax).Normal :=
    theorem_13_6_H_subgroupOf_Smax_normal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource h6hyp
  exact theorem_13_6_nonkernelInducedFamily_pairwise_orthogonal
    Smax H P S1 hS1 hHnormal

private theorem theorem_13_6_calS1_split1_orthogonal_to_lambda_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hlamS1 : lam ∈ S1) :
    ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ lam →
      Section1.scalarProduct G (τ1 ζ) lamτ = 0 := by
  classical
  rcases h6hyp with ⟨_hH, _hlam_irred, _hdeg, _hind, hlamτ_eq⟩
  intro ζ hζ hζ_ne_lam
  have hζspan : Section5.integerSpan Sfam ζ :=
    theorem_13_6_calS1_subset_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS
      ⟨_hH, _hlam_irred, _hdeg, _hind, hlamτ_eq⟩ S1 hS1 ζ hζ
  have hlamspan : Section5.integerSpan Sfam lam :=
    Section5.integerSpan_of_mem Sfam hlamS
  have horthS : Section1.scalarProduct Smax ζ lam = 0 :=
    theorem_13_6_calS1_pairwise_orthogonal_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS
      ⟨_hH, _hlam_irred, _hdeg, _hind, hlamτ_eq⟩ S1 hS1
      ζ hζ lam hlamS1 hζ_ne_lam
  have horthTau : Section1.scalarProduct G (τ1 ζ) (τ1 lam) = 0 := by
    calc
      Section1.scalarProduct G (τ1 ζ) (τ1 lam) =
          Section1.scalarProduct Smax ζ lam := hcoh.1 ζ lam hζspan hlamspan
      _ = 0 := horthS
  simpa [hlamτ_eq] using horthTau

private theorem theorem_13_6_calS1_split1_orthogonality_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hlamS1 : lam ∈ S1) :
    ∃ ζ0 : Section1.ClassFunction Smax,
      ζ0 ∈ S1 ∧
        ζ0 ≠ lam ∧
        ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 → ζ ≠ lam →
          Section1.scalarProduct G (τ1 ζ) lamτ = 0 := by
  rcases theorem_13_6_calS1_split1_conjugate_choice_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS h6hyp S1 hS1 hlamS1 with
    ⟨ζ0, hζ0, hζ0_ne_lam⟩
  have horth := theorem_13_6_calS1_split1_orthogonal_to_lambda_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp S1 hS1 hlamS1
  exact ⟨ζ0, hζ0, hζ0_ne_lam, horth⟩

private theorem theorem_13_6_theorem_13_5_hypothesis_core_of_lambda_mem_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (S1 : Finset (Section1.ClassFunction Smax))
    (hS1 : nonkernelInducedFamily Smax H P S1)
    (hlamS1 : lam ∈ S1) :
    ∃ ζ0 : Section1.ClassFunction Smax,
      ζ0 ∈ S1 ∧
        ζ0 ≠ lam ∧
        (1 : ℂ) = Section1.scalarProduct G (τS (lam - ζ0)) lamτ ∧
        ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
          ζ ≠ ζ0 → ζ ≠ lam →
            Section1.scalarProduct G (τS (ζ - ζ0)) lamτ = 0 := by
  have hself : Section1.scalarProduct G (τ1 lam) lamτ = 1 :=
    theorem_13_6_tauS_lambda_scalarProduct_self_one_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp
  rcases theorem_13_6_calS1_split1_orthogonality_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp S1 hS1 hlamS1 with
    ⟨ζ0, hζ0, hζ0_ne_lam, horth⟩
  have hspan : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section5.integerSpan Sfam ζ :=
    theorem_13_6_calS1_subset_integerSpan_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS h6hyp S1 hS1
  letI : IsMulCommutative (H.subgroupOf Smax) :=
    theorem_13_5_H_subgroupOf_isMulCommutative
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
        p q u v c d hsource h6hyp.1 hS1.1
  have hdegree : ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
      Section1.degree ζ = Section1.degree ζ0 := by
    intro ζ hζ
    rcases (hS1.2.2 ζ).mp hζ with
      ⟨θ, hθirr, _hθnotker, hζind⟩
    rcases (hS1.2.2 ζ0).mp hζ0 with
      ⟨θ0, hθ0irr, _hθ0notker, hζ0ind⟩
    have hθdegree : Section1.degree θ = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθirr
    have hθ0degree : Section1.degree θ0 = 1 :=
      Section1.isIrreducibleCharacterOnGroup_degree_eq_one_of_commutative hθ0irr
    calc
      Section1.degree ζ =
          (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ := by
        rw [hζind, Section1.degree_inducedClassFunction]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) := by
        rw [hθdegree, mul_one]
      _ = (Subgroup.index (H.subgroupOf Smax) : ℂ) * Section1.degree θ0 := by
        rw [hθ0degree, mul_one]
      _ = Section1.degree ζ0 := by
        rw [hζ0ind, Section1.degree_inducedClassFunction]
  exact theorem_13_6_theorem_13_5_hypothesis_core_of_orthogonal_to_lambda
    Smax Sfam S1 τS τ1 lam lamτ ζ0 hcoh hspan hdegree
      hself hζ0 hlamS1 hζ0_ne_lam horth

private theorem theorem_13_6_theorem_13_5_hypothesis_core_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 : Section1.ClassFunction Smax),
        nonkernelInducedFamily Smax H P S1 ∧
          ζ0 ∈ S1 ∧
          lam ∈ S1 ∧
          ζ0 ≠ lam ∧
          Theory.Character.IsVirtualCharacter lamτ ∧
          (1 : ℂ) = Section1.scalarProduct G (τS (lam - ζ0)) lamτ ∧
          ∀ ζ : Section1.ClassFunction Smax, ζ ∈ S1 →
            ζ ≠ ζ0 → ζ ≠ lam →
              Section1.scalarProduct G (τS (ζ - ζ0)) lamτ = 0 := by
  rcases theorem_13_6_lambda_mem_S1_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hlamS h6hyp with
    ⟨S1, hS1, hlamS1⟩
  rcases theorem_13_6_theorem_13_5_hypothesis_core_of_lambda_mem_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp S1 hS1 hlamS1 with
    ⟨ζ0, hζ0, hζ0_ne_lam, ha, horth⟩
  have hvirt : Theory.Character.IsVirtualCharacter lamτ :=
    theorem_13_6_lamTau_virtual_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp
  exact ⟨S1, ζ0, hS1, hζ0, hlamS1, hζ0_ne_lam, hvirt, ha, horth⟩

private theorem theorem_13_6_theorem_13_5_hypothesis_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 : Section1.ClassFunction Smax),
        theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ) := by
  rcases h6hyp with ⟨hH, _hlam_irred, _hlam_deg, _hlam_linear, _hlamτ⟩
  rcases theorem_13_6_theorem_13_5_hypothesis_core_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource
      hcoh hlamS
      ⟨hH, _hlam_irred, _hlam_deg, _hlam_linear, _hlamτ⟩ with
    ⟨S1, ζ0, hS1, hζ0, hlam, hζ0_ne_lam, hvirt, ha, horth⟩
  exact ⟨S1, ζ0,
    theorem_13_6_theorem_13_5_hypothesis_of_core
      Smax H P C S1 τS ζ0 lam lamτ
      hH hS1 hζ0 hlam hζ0_ne_lam hvirt ha horth⟩

private theorem theorem_13_6_restrictionData_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H P C : Subgroup G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u : ℕ)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ lamH : Section1.ClassFunction H, classFunctionRestrictionData H Smax lam lamH := by
  rcases h6hyp with ⟨_hH, _hlam_irred, _hlam_deg, hlam_linear, _hlamτ⟩
  rcases hlam_linear with ⟨hHS, _θ, _hθ_irred, _hθ_deg, _hlam_ind⟩
  let lamH : Section1.ClassFunction H := fun x => lam ⟨(x : G), hHS x.property⟩
  exact ⟨lamH, hHS, fun x => rfl⟩

private theorem theorem_13_6_theorem_13_5_input_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ (S1 : Finset (Section1.ClassFunction Smax))
      (ζ0 : Section1.ClassFunction Smax)
      (lamH : Section1.ClassFunction H),
        theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ) ∧
          classFunctionRestrictionData H Smax lam lamH := by
  rcases theorem_13_6_theorem_13_5_hypothesis_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp with
    ⟨S1, ζ0, h5hyp⟩
  rcases theorem_13_6_restrictionData_of_hypothesis Smax H P C τ1 lam lamτ p q u
      h6hyp with
    ⟨lamH, hres⟩
  exact ⟨S1, ζ0, lamH, h5hyp, hres⟩

private theorem theorem_13_6_q_prime_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime q := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with hcaseA | hcaseB
  · rcases hcaseA with
      ⟨_hBarU, _a, _h92, _hH0le, _hCentIn, _hpPrime, hqPrime,
        _hpdata, _hquot, _hcardQuot, _hadvd, _hinj⟩
    exact hqPrime
  · rcases hcaseB with
      ⟨_h92, _hH0le, _hCentIn, _hpPrime, hqPrime, _hpdata, _hquot,
        _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv,
        _hprimeField⟩
    exact hqPrime

private theorem theorem_13_6_virtualCharacter_one_eq_int
    {G : Type u}
    [Group G]
    [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    ∃ n : ℤ, χ 1 = (n : ℂ) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  refine ⟨∑ i : Fin r, m i * (n i : ℤ), ?_⟩
  have hdeg : ∀ i : Fin r, (ρ i).character 1 = (n i : ℂ) := by
    intro i
    simp
  rw [hχeq]
  unfold Theory.Character.virtualCharacterOfRepresentations
  simp_rw [hdeg]
  exact_mod_cast (rfl : (∑ i : Fin r, m i * (n i : ℤ)) =
    ∑ i : Fin r, m i * (n i : ℤ))

private theorem theorem_13_6_congruentModOneSub_symm
    {etaRoot eps z w : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hwMem : w ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcong : Theory.Character.CongruentModOneSub etaRoot eps z w hepsMem hzMem hwMem) :
    Theory.Character.CongruentModOneSub etaRoot eps w z hepsMem hwMem hzMem := by
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  have hcongA : Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A)
      ⟨w, hwMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hcong
  rw [Theory.Character.congruentModIn_iff_dvd] at hcongA
  change Theory.Character.congruentModIn A oneSub (⟨w, hwMem⟩ : A) ⟨z, hzMem⟩
  rw [Theory.Character.congruentModIn_iff_dvd]
  obtain ⟨r, hr⟩ := hcongA
  refine ⟨-r, ?_⟩
  calc
    (⟨w, hwMem⟩ : A) - ⟨z, hzMem⟩ = -(⟨z, hzMem⟩ - ⟨w, hwMem⟩) := by
      ring
    _ = -(oneSub * r) := by rw [hr]
    _ = oneSub * (-r) := by ring

private theorem theorem_13_6_congruentModOneSub_trans
    {etaRoot eps z w v : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzMem : z ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hwMem : w ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hvMem : v ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hzw : Theory.Character.CongruentModOneSub etaRoot eps z w hepsMem hzMem hwMem)
    (hwv : Theory.Character.CongruentModOneSub etaRoot eps w v hepsMem hwMem hvMem) :
    Theory.Character.CongruentModOneSub etaRoot eps z v hepsMem hzMem hvMem := by
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  have hzwA : Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A)
      ⟨w, hwMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hzw
  have hwvA : Theory.Character.congruentModIn A oneSub (⟨w, hwMem⟩ : A)
      ⟨v, hvMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hwv
  rw [Theory.Character.congruentModIn_iff_dvd] at hzwA hwvA
  change Theory.Character.congruentModIn A oneSub (⟨z, hzMem⟩ : A) ⟨v, hvMem⟩
  rw [Theory.Character.congruentModIn_iff_dvd]
  obtain ⟨r, hr⟩ := hzwA
  obtain ⟨s, hs⟩ := hwvA
  refine ⟨r + s, ?_⟩
  calc
    (⟨z, hzMem⟩ : A) - ⟨v, hvMem⟩ =
        (⟨z, hzMem⟩ - ⟨w, hwMem⟩) + (⟨w, hwMem⟩ - ⟨v, hvMem⟩) := by
      ring
    _ = oneSub * r + oneSub * s := by rw [hr, hs]
    _ = oneSub * (r + s) := by ring

private theorem theorem_13_6_virtualCharacter_congruent_at_mul_of_order_dvd
    {K : Type*} [Group K] [Finite K]
    {p M : ℕ} {etaRoot eps : ℂ}
    (heps : IsPrimitiveRoot eps p) (hp : p ≠ 0)
    (hetaRoot : IsPrimitiveRoot etaRoot M) (hM : M ≠ 0)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    {χ : K → ℂ} (hχ : Theory.Character.IsVirtualCharacter χ)
    {x y : K}
    (hx_order : orderOf x = p)
    (hy_order_dvd : orderOf y ∣ M)
    (hcomm : x * y = y * x) :
    ∃ hxy : χ (x * y) ∈ Theory.Character.cyclotomicOrder etaRoot,
      ∃ hy : χ y ∈ Theory.Character.cyclotomicOrder etaRoot,
        Theory.Character.CongruentModOneSub etaRoot eps (χ (x * y)) (χ y)
          hepsMem hxy hy := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  let A := Theory.Character.cyclotomicOrder etaRoot
  have hrep : ∀ i : Fin r,
      ∃ hxy : (ρ i).character (x * y) ∈ A,
        ∃ hy : (ρ i).character y ∈ A,
          Theory.Character.CongruentModOneSub etaRoot eps
            ((ρ i).character (x * y)) ((ρ i).character y) hepsMem hxy hy := by
    intro i
    let N := orderOf y
    have hN : N ≠ 0 := Nat.ne_of_gt (orderOf_pos y)
    have hNM : N ∣ M := by
      simpa [N] using hy_order_dvd
    have hxpow : x ^ p = 1 := by
      rw [← hx_order]
      exact pow_orderOf_eq_one x
    have hf : (ρ i x) ^ p = 1 := by
      rw [← MonoidHom.map_pow, hxpow, MonoidHom.map_one]
    have hTpow : (ρ i y) ^ N = 1 := by
      subst N
      rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
    have hcommEnd : ρ i x * ρ i y = ρ i y * ρ i x := by
      calc
        ρ i x * ρ i y = ρ i (x * y) := (map_mul (ρ i) x y).symm
        _ = ρ i (y * x) := by rw [hcomm]
        _ = ρ i y * ρ i x := map_mul (ρ i) y x
    rcases Theory.Character.finite_order_commuting_trace_mul_congruent
        (η := etaRoot) (ξ := eps) (p := p) (N := N) (M := M)
        heps hp hetaRoot hM hNM hepsMem (f := ρ i x) (T := ρ i y)
        hN hf hTpow hcommEnd with
      ⟨hmul, hy, hcong⟩
    have hxy : (ρ i).character (x * y) ∈ A := by
      simpa [Representation.character, map_mul] using hmul
    refine ⟨hxy, hy, ?_⟩
    simpa [Theory.Character.CongruentModOneSub, Representation.character, map_mul] using hcong
  choose hxyi hyi hcongi using hrep
  have hxy_mem : χ (x * y) ∈ A := by
    rw [hχeq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)
  have hy_mem : χ y ∈ A := by
    rw [hχeq]
    exact A.sum_mem fun i _ =>
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)
  refine ⟨hxy_mem, hy_mem, ?_⟩
  let oneSub : A := ⟨1 - eps, A.sub_mem A.one_mem hepsMem⟩
  change Theory.Character.congruentModIn A oneSub
    (⟨χ (x * y), hxy_mem⟩ : A)
    (⟨χ y, hy_mem⟩ : A)
  let zterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (ρ i).character (x * y),
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hxyi i)⟩
  let wterm : Fin r → A := fun i =>
    ⟨(m i : ℂ) * (ρ i).character y,
      A.mul_mem (Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)) (hyi i)⟩
  unfold Theory.Character.congruentModIn
  have hdiff :
      (⟨χ (x * y), hxy_mem⟩ : A) - ⟨χ y, hy_mem⟩ =
        ∑ i : Fin r, (zterm i - wterm i) := by
    ext
    change χ (x * y) - χ y = ((∑ i : Fin r, (zterm i - wterm i) : A) : ℂ)
    rw [hχeq]
    simp [Theory.Character.virtualCharacterOfRepresentations, zterm, wterm,
      Finset.sum_sub_distrib]
  rw [hdiff]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hci : Theory.Character.congruentModIn A oneSub
      (⟨(ρ i).character (x * y), hxyi i⟩ : A)
      (⟨(ρ i).character y, hyi i⟩ : A) := by
    simpa [Theory.Character.CongruentModOneSub, oneSub] using hcongi i
  change Theory.Character.congruentModIn A oneSub (zterm i) (wterm i)
  have hmul := Theory.Character.congruentModIn_mul_left hci
    (⟨(m i : ℂ), Theory.Character.intCast_mem_cyclotomicOrder etaRoot (m i)⟩ : A)
  simpa [zterm, wterm] using hmul

private theorem theorem_13_6_alpha_one_q_multiple_of_congruence
    {G : Type u}
    [Group G]
    [Finite G]
    {q : ℕ}
    {α : Section1.ClassFunction G}
    (hq : Nat.Prime q)
    (hvirt : Theory.Character.IsVirtualCharacter α)
    {etaRoot eps : ℂ}
    (hetaInt : IsIntegral ℤ etaRoot)
    (heps : IsPrimitiveRoot eps q)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hαmem : α 1 ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcong : Theory.Character.CongruentModOneSub etaRoot eps (α 1) 0
      hepsMem hαmem (Theory.Character.cyclotomicOrder etaRoot).zero_mem) :
    ∃ b : ℤ, α 1 = (q : ℂ) * (b : ℂ) := by
  rcases theorem_13_6_virtualCharacter_one_eq_int hvirt with ⟨n, hn⟩
  have hcongInt : Theory.Character.CongruentModOneSub etaRoot eps (n : ℂ) 0
      hepsMem
      (Theory.Character.intCast_mem_cyclotomicOrder etaRoot n)
      (Theory.Character.cyclotomicOrder etaRoot).zero_mem := by
    simpa [hn, Theory.Character.CongruentModOneSub] using hcong
  have hdiv : (q : ℤ) ∣ n :=
    Theory.Character.prime_dvd_int_of_congruent_zero_mod_one_sub
      hq heps hetaInt hepsMem n hcongInt
  rcases hdiv with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rw [hn, hb]
  norm_num

private theorem theorem_13_6_lambda_normSq_one_of_hypothesis
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax H P C : Subgroup G}
    {τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {lam : Section1.ClassFunction Smax}
    (lamτ : Section1.ClassFunction G)
    {p q u : ℕ}
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    Section5.cfNormSq lam = 1 := by
  unfold Section5.cfNormSq
  rw [show Section1.scalarProduct Smax lam lam = 1 by
    rcases h6hyp.2.1 with ⟨_n, ρ, hρirr, hlam_char⟩
    rw [hlam_char]
    exact (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hρirr]
  simp

private theorem theorem_13_6_alpha_one_congruent_zero_mod_one_sub_of_lambda_congruence
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax H P : Subgroup G}
    {lam : Section1.ClassFunction Smax}
    {lamτ : Section1.ClassFunction G}
    {lamH α : Section1.ClassFunction H}
    {etaRoot eps : ℂ}
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcf : Section5.cfNormSq lam = 1)
    (hα : virtualCharacterKernelConstituentData H P α)
    (x : H)
    (hxne : (x : G) ≠ 1)
    (hxP : (x : G) ∈ P)
    (hexp : ∀ y : H, (y : G) ≠ 1 →
      lamτ (y : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH y + α y)
    (hτMem : lamτ (x : G) ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hLamMem : lamH x ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hαMem : α 1 ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hcong : Theory.Character.CongruentModOneSub etaRoot eps (lamτ (x : G)) (lamH x)
      hepsMem hτMem hLamMem) :
    Theory.Character.CongruentModOneSub etaRoot eps (α 1) 0
      hepsMem hαMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem := by
  let A := Theory.Character.cyclotomicOrder etaRoot
  let oneSub : A := ⟨1 - eps,
    A.sub_mem A.one_mem hepsMem⟩
  have hαker : Section1.subgroupInKernel' α (P.subgroupOf H) :=
    theorem_13_5_virtualCharacterKernelConstituent_subgroupInKernel H P α hα
  have hxmem : x ∈ P.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hxP
  have hαx : α x = α 1 := by
    simpa [Section1.subgroupInKernel', Section1.degree] using hαker ⟨x, hxmem⟩
  have hxexp : lamτ (x : G) = lamH x + α 1 := by
    simpa [hcf, hαx] using hexp x hxne
  have hdiff : α 1 - 0 = lamτ (x : G) - lamH x := by
    rw [hxexp]
    ring
  have hcongA : Theory.Character.congruentModIn A oneSub
      (⟨lamτ (x : G), hτMem⟩ : A) ⟨lamH x, hLamMem⟩ := by
    simpa [Theory.Character.CongruentModOneSub, A, oneSub] using hcong
  rw [Theory.Character.congruentModIn_iff_dvd] at hcongA
  change Theory.Character.congruentModIn A oneSub
    (⟨α 1, hαMem⟩ : A) (⟨0, A.zero_mem⟩ : A)
  rw [Theory.Character.congruentModIn_iff_dvd]
  rcases hcongA with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  ext
  change α 1 - 0 = ((oneSub * r : A) : ℂ)
  calc
    α 1 - 0 = lamτ (x : G) - lamH x := hdiff
    _ = (((⟨lamτ (x : G), hτMem⟩ : A) - ⟨lamH x, hLamMem⟩ : A) : ℂ) := by
      simp
    _ = ((oneSub * r : A) : ℂ) := by
      exact congrArg (fun z : A => (z : ℂ)) hr

private theorem theorem_13_6_primitive_root_package_of_q_prime
    {G : Type u}
    [Group G]
    [Finite G]
    {q : ℕ}
    (hqprime : Nat.Prime q)
    (hqdvd : q ∣ Nat.card G) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        eps ∈ Theory.Character.cyclotomicOrder etaRoot := by
  let etaRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))
  let eps : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G) := by
    dsimp [etaRoot]
    exact Complex.isPrimitiveRoot_exp (Nat.card G) hGne
  have heps : IsPrimitiveRoot eps q := by
    dsimp [eps]
    exact Complex.isPrimitiveRoot_exp q hqprime.ne_zero
  refine ⟨etaRoot, eps, hqprime, hetaRoot, heps, ?_⟩
  exact Theory.Character.primitive_root_mem_cyclotomicOrder_of_dvd
    hetaRoot hGne heps hqdvd

private theorem theorem_13_6_primitive_root_package_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ∃ (etaRoot eps : ℂ),
      Nat.Prime q ∧
        IsPrimitiveRoot etaRoot (Nat.card G) ∧
        IsPrimitiveRoot eps q ∧
        eps ∈ Theory.Character.cyclotomicOrder etaRoot := by
  have hqprime : Nat.Prime q :=
    theorem_13_6_q_prime_of_source Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  have hqdvd : q ∣ Nat.card G := by
    rcases hsource with
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hrest⟩
    rw [hq_card]
    exact Subgroup.card_subgroup_dvd_card W1
  exact theorem_13_6_primitive_root_package_of_q_prime hqprime hqdvd

private theorem theorem_13_6_lambda_congruent_mod_one_sub_of_vanish
    {G : Type u}
    [Group G]
    [Finite G]
    {Smax H : Subgroup G}
    {lam : Section1.ClassFunction Smax}
    {lamτ : Section1.ClassFunction G}
    {lamH : Section1.ClassFunction H}
    {q : ℕ}
    {x : H}
    {y : G}
    {etaRoot eps : ℂ}
    (hqprime : Nat.Prime q)
    (hetaRoot : IsPrimitiveRoot etaRoot (Nat.card G))
    (heps : IsPrimitiveRoot eps q)
    (hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot)
    (hτvirt : Theory.Character.IsVirtualCharacter lamτ)
    (hlamIrr : Section1.IsIrreducibleCharacterOnGroup lam)
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (hyS : y ∈ Smax)
    (hxyS : y * (x : G) ∈ Smax)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (hτzero : lamτ (y * (x : G)) = 0)
    (hlamzero : lam ⟨y * (x : G), hxyS⟩ = 0) :
    ∃ hτMem : lamτ (x : G) ∈ Theory.Character.cyclotomicOrder etaRoot,
      ∃ hLamMem : lamH x ∈ Theory.Character.cyclotomicOrder etaRoot,
        Theory.Character.CongruentModOneSub etaRoot eps (lamτ (x : G)) (lamH x)
          hepsMem hτMem hLamMem := by
  rcases hres with ⟨hHS, hres_eval⟩
  let xS : Smax := ⟨(x : G), hHS x.property⟩
  let yS : Smax := ⟨y, hyS⟩
  have hx_order_dvd : orderOf (x : G) ∣ Nat.card G :=
    orderOf_dvd_natCard (x : G)
  have hxS_order_dvd : orderOf xS ∣ Nat.card G :=
    (orderOf_dvd_natCard xS).trans (Subgroup.card_subgroup_dvd_card Smax)
  have hyS_order : orderOf yS = q := by
    simpa [yS, Subgroup.orderOf_coe] using hy_order
  have hcommS : yS * xS = xS * yS := by
    ext
    simpa [yS, xS] using hcomm
  rcases theorem_13_6_virtualCharacter_congruent_at_mul_of_order_dvd
      (K := G) (p := q) (M := Nat.card G) (etaRoot := etaRoot) (eps := eps)
      heps hqprime.ne_zero hetaRoot (Nat.card_pos (α := G)).ne' hepsMem
      (χ := lamτ) hτvirt (x := y) (y := (x : G)) hy_order hx_order_dvd hcomm with
    ⟨hτyxMem, hτxMem, hτcong⟩
  have hlamVirt : Theory.Character.IsVirtualCharacter lam :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hlamIrr
  rcases theorem_13_6_virtualCharacter_congruent_at_mul_of_order_dvd
      (K := Smax) (p := q) (M := Nat.card G) (etaRoot := etaRoot) (eps := eps)
      heps hqprime.ne_zero hetaRoot (Nat.card_pos (α := G)).ne' hepsMem
      (χ := lam) hlamVirt (x := yS) (y := xS) hyS_order hxS_order_dvd hcommS with
    ⟨hLamYXMem, hLamXMem, hLamConj⟩
  have hτ0x : Theory.Character.CongruentModOneSub etaRoot eps 0 (lamτ (x : G))
      hepsMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem hτxMem := by
    simpa [Theory.Character.CongruentModOneSub, hτzero] using hτcong
  have hyxS_eq : yS * xS = ⟨y * (x : G), hxyS⟩ := by
    ext
    rfl
  have hlam_yx_zero' : lam (yS * xS) = 0 := by
    rw [hyxS_eq]
    exact hlamzero
  have hLam0xS : Theory.Character.CongruentModOneSub etaRoot eps 0 (lam xS)
      hepsMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem hLamXMem := by
    simpa [Theory.Character.CongruentModOneSub, hlam_yx_zero'] using hLamConj
  have hLamMem : lamH x ∈ Theory.Character.cyclotomicOrder etaRoot := by
    rw [hres_eval x]
    exact hLamXMem
  have hLam0H : Theory.Character.CongruentModOneSub etaRoot eps 0 (lamH x)
      hepsMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem hLamMem := by
    simpa [Theory.Character.CongruentModOneSub, hres_eval x] using hLam0xS
  have hτx0 : Theory.Character.CongruentModOneSub etaRoot eps (lamτ (x : G)) 0
      hepsMem hτxMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem :=
    theorem_13_6_congruentModOneSub_symm hepsMem
      (Theory.Character.cyclotomicOrder etaRoot).zero_mem hτxMem hτ0x
  exact ⟨hτxMem, hLamMem,
    theorem_13_6_congruentModOneSub_trans hepsMem hτxMem
      (Theory.Character.cyclotomicOrder etaRoot).zero_mem hLamMem hτx0 hLam0H⟩

private theorem theorem_13_6_exists_Hsharp_mem_W2_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    ∃ x : H, (x : G) ∈ W2 ∧ (x : G) ≠ 1 := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      hW2le, _hW2cyc, hW2ne, _hcent, _hnorm⟩
  have hW2leP : W2 ≤ P := (le_inf_iff.mp hW2le).1
  have hW2_nontrivial : ∃ x : G, x ∈ W2 ∧ x ≠ 1 := by
    by_contra hnone
    have hW2_le_bot : W2 ≤ ⊥ := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · exact False.elim (hnone ⟨x, hx, hx1⟩)
    exact hW2ne (le_antisymm hW2_le_bot bot_le)
  rcases hW2_nontrivial with ⟨x, hxW2, hxne⟩
  have hxH : x ∈ H := by
    rw [hH]
    exact (le_sup_left : P ≤ P ⊔ C) (hW2leP hxW2)
  exact ⟨⟨x, hxH⟩, hxW2, hxne⟩

private theorem theorem_13_6_exists_W1_order_comm_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (x : H)
    (hxW2 : (x : G) ∈ W2) :
    ∃ y : G, y ∈ W1 ∧ y ≠ 1 ∧ orderOf y = q ∧
      y * (x : G) = (x : G) * y := by
  rcases hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨_hMF, hW1cyc, hW1ne, _hW1Hall, _hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      _hW2le, _hW2cyc, _hW2ne, hcentW1, _hnorm⟩
  letI : IsCyclic W1 := hW1cyc
  rcases IsCyclic.exists_generator (α := W1) with ⟨yW1, hygen⟩
  let y : G := yW1
  have hyW1 : y ∈ W1 := yW1.property
  have hy_order_sub : orderOf yW1 = Nat.card W1 :=
    orderOf_eq_card_of_forall_mem_zpowers hygen
  have hy_order : orderOf y = q := by
    have hy_order_card : orderOf y = Nat.card W1 := by
      simpa [y, Subgroup.orderOf_coe] using hy_order_sub
    exact hy_order_card.trans hq_card.symm
  have hq_gt_one : 1 < q := by
    have hW1card : 1 < Nat.card W1 :=
      (Subgroup.one_lt_card_iff_ne_bot (H := W1)).2 hW1ne
    simpa [hq_card] using hW1card
  have hyne : y ≠ 1 := by
    intro hy1
    have hq_eq_one : q = 1 := by
      have hone : orderOf y = 1 := by
        simp [hy1]
      exact hy_order.symm.trans hone
    exact (Nat.ne_of_gt hq_gt_one) hq_eq_one
  have hW2centW1 : W2 ≤ Subgroup.centralizer (W1 : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a haW1
    by_cases ha1 : a = 1
    · simp [ha1]
    · have hzCent : z ∈ elementCentralizerIn (ambientDerivedSubgroup Smax) a := by
        simpa [hcentW1 a haW1 ha1] using hz
      exact (Subgroup.mem_centralizer_singleton_iff.mp hzCent.2).symm
  have hcomm : y * (x : G) = (x : G) * y :=
    Subgroup.mem_centralizer_iff.mp (hW2centW1 hxW2) y hyW1
  exact ⟨y, hyW1, hyne, hy_order, hcomm⟩

private theorem theorem_13_6_C_le_U_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    C ≤ U := by
  rcases hsource with
    ⟨_hcaseB, _hptypeS, _hptypeT, _hp, _hq, hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rw [hC]
  exact inf_le_left

private theorem theorem_13_6_H_le_P_sup_U_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hH : H = P ⊔ C) :
    H ≤ P ⊔ U := by
  rw [hH]
  exact sup_le le_sup_left
    ((theorem_13_6_C_le_U_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT p q u v c d
      hsource).trans le_sup_right)


private theorem theorem_13_6_P_sup_U_subgroupOf_Smax_normal_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    ((P ⊔ U).subgroupOf Smax).Normal := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, _hMcomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, _hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hDercomp with ⟨_hPDer, _hUDer, hDer_eq, _hdisj⟩
  have hDnormal : ((ambientDerivedSubgroup Smax).subgroupOf Smax).Normal := by
    simpa using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := Smax)).2
  simpa [← hDer_eq] using hDnormal

private theorem theorem_13_6_lambda_inducedCF_from_P_sup_U_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    ∃ θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      lam = Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU := by
  rcases h6hyp with ⟨hH, _hlam_irred, _hlam_deg, hlam_linear, _hlamτ_eq⟩
  rcases hlam_linear with ⟨_hHleS, θ, _hθ_irred, _hθ_deg, hlam_eq⟩
  have hHlePU := theorem_13_6_H_le_P_sup_U_of_sourceContext
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
    hsource hH
  have hHT : H.subgroupOf Smax ≤ (P ⊔ U).subgroupOf Smax := by
    intro x hx
    change ((x : Smax) : G) ∈ P ⊔ U
    exact hHlePU hx
  refine
    ⟨Section1.inducedCF
        ((H.subgroupOf Smax).subgroupOf ((P ⊔ U).subgroupOf Smax))
        (Section1.subgroupOfClassFunction θ), ?_⟩
  rw [hlam_eq]
  exact
    (Section1.inducedCF_trans (H.subgroupOf Smax)
      ((P ⊔ U).subgroupOf Smax) hHT θ).symm

private theorem theorem_13_6_lambda_vanish_on_yx_of_not_mem_P_sup_U
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax P U : Subgroup G)
    (lam : Section1.ClassFunction Smax)
    (hind : ∃ θPU : Section1.ClassFunction ((P ⊔ U).subgroupOf Smax),
      lam = Section1.inducedCF ((P ⊔ U).subgroupOf Smax) θPU)
    (hnormal : ((P ⊔ U).subgroupOf Smax).Normal)
    {g : G}
    (hgS : g ∈ Smax)
    (hgPU : g ∉ P ⊔ U) :
    lam ⟨g, hgS⟩ = 0 := by
  rcases hind with ⟨θPU, hlam⟩
  letI : ((P ⊔ U).subgroupOf Smax).Normal := hnormal
  have hgPUsub : (⟨g, hgS⟩ : Smax) ∉ (P ⊔ U).subgroupOf Smax := by
    intro hg
    exact hgPU (by
      simpa [Subgroup.mem_subgroupOf] using hg)
  rw [hlam]
  exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
    ((P ⊔ U).subgroupOf Smax) θPU hgPUsub


private theorem theorem_13_6_yx_not_mem_P_sup_U_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (_hy_order : orderOf y = q)
    (_hcomm : y * (x : G) = (x : G) * y) :
    y * (x : G) ∉ P ⊔ U := by
  rcases hsource with
    ⟨_hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne, _hW1Hall, hMcomp, _hUleD, _hUnil, _hW1norm,
      hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer, hW2le, _hW2cyc,
      _hW2ne, _hcent, _hnorm⟩
  rcases hMcomp with ⟨_hDerS, _hW1S, _hS_eq, hDerW1disj⟩
  rcases hDercomp with ⟨_hPDer, _hUDer, hDer_eq, _hPUdisj⟩
  have hPUW1disj : Disjoint (P ⊔ U) W1 := by
    simpa [← hDer_eq] using hDerW1disj
  have hxPU : (x : G) ∈ P ⊔ U :=
    (le_sup_left : P ≤ P ⊔ U) ((le_inf_iff.mp hW2le).1 hxW2)
  intro hyxPU
  have hyPU : y ∈ P ⊔ U := by
    have hyx_inv : (y * (x : G)) * ((x : G))⁻¹ ∈ P ⊔ U :=
      (P ⊔ U).mul_mem hyxPU ((P ⊔ U).inv_mem hxPU)
    simpa [mul_assoc] using hyx_inv
  have hyBot : y ∈ (⊥ : Subgroup G) :=
    hPUW1disj.le_bot ⟨hyPU, hyW1⟩
  exact hyne (by simpa using hyBot)

private theorem theorem_13_6_yx_mem_cyclicTISet_of_sourceContext
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y) :
    y * (x : G) ∈ Section3.cyclicTISet W1 W2 W := by
  have hyx_not_PU : y * (x : G) ∉ P ⊔ U :=
    theorem_13_6_yx_not_mem_P_sup_U_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
      hsource x hxW2 hxne y hyW1 hyne hy_order hcomm
  rcases hsource with
    ⟨hcaseB, hptypeS, _hptypeT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcaseB with
    ⟨hprod, _hcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  rcases hprod with ⟨hW1leW, hW2leW, _hW, hW1W2disj, _hW1centW2⟩
  rcases hptypeS with
    ⟨_hMF, _hW1cyc, _hW1ne', _hW1Hall, _hMcomp, _hUleD, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      hW2le, _hW2cyc, _hW2ne', _hcent, _hnormHat⟩
  rw [Section3.cyclicTISet_mem_iff]
  refine ⟨W.mul_mem (hW1leW hyW1) (hW2leW hxW2), ?_, ?_⟩
  · intro hyxW1
    have hxW1 : (x : G) ∈ W1 := by
      have hxW1' : y⁻¹ * (y * (x : G)) ∈ W1 :=
        W1.mul_mem (W1.inv_mem hyW1) hyxW1
      simpa [mul_assoc] using hxW1'
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      hW1W2disj.le_bot ⟨hxW1, hxW2⟩
    exact hxne (by simpa using hxBot)
  · intro hyxW2
    exact hyx_not_PU
      ((le_sup_left : P ≤ P ⊔ U) ((le_inf_iff.mp hW2le).1 hyxW2))

private theorem theorem_13_6_coherentFamily_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Section6.coherentFamily Sfam τS := by
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _htype, _hq_lt_p, _hUcomm, _hfrob, _hPelem, _hPcard, _hu,
      hcoh, _hBook, _hA0, _hnormalizer⟩
  exact hcoh


private theorem theorem_13_6_tauS_lambda_vanish_on_cyclicTI_of_orthogonal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P U : Subgroup G)
    (_Sfam : Finset (Section1.ClassFunction Smax))
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (lam : Section1.ClassFunction Smax)
    (hτclass : Section1.IsClassFunction (τ1 lam))
    (horth : ∀ i j : ℕ, i < q → j < p →
      Section1.scalarProduct G (τ1 lam) (η i j) = 0)
    (g : G)
    (hgCyc : g ∈ Section3.cyclicTISet W1 W2 W) :
    (τ1 lam) g = 0 := by
  classical
  rcases hnotation with
    ⟨hωData, hσmap, hη, _hδ, _hδ', _hμirr, _hνirr,
      _hμzero_nonprincipal, _hνzero_nonprincipal, _hμind, _hνind,
      _hμsum, _hνsum⟩
  rcases hωData with ⟨h31, hqpos, hppos, ωFin, hωFin, hωNat⟩
  have horth_basis :
      ∀ i : Fin q, ∀ j : Fin p,
        Section1.scalarProduct G (τ1 lam) (σ (ωFin i j)) = 0 := by
    intro i j
    have hηeq : η (i : ℕ) (j : ℕ) = σ (ωFin i j) := by
      rw [hη (i : ℕ) (j : ℕ) i.isLt j.isLt,
        hωNat (i : ℕ) (j : ℕ) i.isLt j.isLt]
    simpa [hηeq] using horth (i : ℕ) (j : ℕ) i.isLt j.isLt
  exact
    (Section3.vanishesOn_of_orthogonal_theorem_3_2_basis
      (W1 := W1) (W2 := W2) (W := W)
      h31 hωFin σ hσmap hτclass horth_basis) g hgCyc


private theorem theorem_13_6_tauS_lambda_vanish_on_cyclicTI_of_coherent_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (Smax Tmax W W1 W2 P U : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q : ℕ)
    (lam : Section1.ClassFunction Smax)
    (hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (hcohBase : Section6.coherentFamily Sfam τS)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (hlamS : lam ∈ Sfam)
    (hlamIrr : Section1.IsIrreducibleCharacterOnGroup lam)
    (hτclass : Section1.IsClassFunction (τ1 lam))
    (g : G)
    (hgCyc : g ∈ Section3.cyclicTISet W1 W2 W) :
    (τ1 lam) g = 0 := by
  have horth : ∀ i j : ℕ, i < q → j < p →
      Section1.scalarProduct G (τ1 lam) (η i j) = 0 := by
    intro i j hi hj
    exact section13_typeP_coherentExtension_orthogonal_cyclicTIiso_source
      Smax Tmax W W1 W2 P U Sfam τS τ1 ω η μ ν μsum νsum δ δ' σ p q
      hTypeP hFourSix hSfam hcohBase hcoh hnotation lam hlamS hlamIrr i j hi hj
  exact theorem_13_6_tauS_lambda_vanish_on_cyclicTI_of_orthogonal_source
    Smax Tmax W W1 W2 P U Sfam τ1 ω η μ ν μsum νsum δ δ' σ p q
    hTypeP hnotation lam hτclass horth g hgCyc


private theorem theorem_13_6_lambda_tau_vanish_on_yx_of_coherent_source
    {G : Type u}
    [Group G]
    [Finite G]
    [IsMinCE G]
    (Smax Tmax W W1 W2 P U C H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u : ℕ)
    (lamH : Section1.ClassFunction H)
    (_hTypeP : Section8.typePDefinitionData Smax P U W1 W2)
    (_hFourSix : typePFourSixTauSourceData Smax P U W1 W2 τS)
    (_hSfam : nonkernelInducedFamily Smax (P ⊔ U) P Sfam)
    (_hcohBase : Section6.coherentFamily Sfam τS)
    (_hcoh : Section6.coherentExtension Sfam τS τ1)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ)
    (_hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH)
    (x : H)
    (_hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (_hyW1 : y ∈ W1)
    (_hyne : y ≠ 1)
    (_hy_order : orderOf y = q)
    (_hcomm : y * (x : G) = (x : G) * y)
    (_hxyCyc : y * (x : G) ∈ Section3.cyclicTISet W1 W2 W)
    (_hyS : y ∈ Smax)
    (_hxyS : y * (x : G) ∈ Smax) :
    lamτ (y * (x : G)) = 0 := by
  rcases h6hyp with ⟨_hH, hlamIrr, _hlam_deg, _hlinear, hlamτ_eq⟩
  rcases _h5hyp with
    ⟨_hH5, _hS1, _hζ0, _hlam, _hζ0_ne_lam, hlamτvirt, _ha, _horth5⟩
  have hτclass : Section1.IsClassFunction (τ1 lam) := by
    have hlamτclass : Section1.IsClassFunction lamτ :=
      Section1.isVirtualCharacter_isClassFunction hlamτvirt
    simpa [hlamτ_eq] using hlamτclass
  have hτ_vanish :
      (τ1 lam) (y * (x : G)) = 0 :=
    theorem_13_6_tauS_lambda_vanish_on_cyclicTI_of_coherent_source
      Smax Tmax W W1 W2 P U Sfam τS τ1 ω η μ ν μsum νsum δ δ' σ p q lam
      _hTypeP _hFourSix _hSfam _hcohBase _hcoh _hnotation _hlamS hlamIrr hτclass
      (y * (x : G)) _hxyCyc
  simpa [hlamτ_eq] using hτ_vanish


private theorem theorem_13_6_lambda_tau_vanish_on_yx_cyclicTI_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcohExt : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (hxyCyc : y * (x : G) ∈ Section3.cyclicTISet W1 W2 W)
    (hyS : y ∈ Smax)
    (hxyS : y * (x : G) ∈ Smax) :
    lamτ (y * (x : G)) = 0 := by
  have hcoh : Section6.coherentFamily Sfam τS :=
    theorem_13_6_coherentFamily_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  rcases hsource with
    ⟨_hcase, hTypeP, _hTypePT, _hp, _hq, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, hSfam, _hTfam, hDadeS, _hDadeT,
      hnotationData, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, hFourSixS, _hFourSixT⟩
  letI : IsMinCE G := _hMin
  rcases hnotationData with
    ⟨ω, η, μ, ν, μsum, νsum, δ, δ', σ, hnotation⟩
  exact theorem_13_6_lambda_tau_vanish_on_yx_of_coherent_source
    Smax Tmax W W1 W2 P U C H Sfam S1 τS τ1 ζ0 lam lamτ
    ω η μ ν μsum νsum δ δ' σ p q u lamH
    hTypeP hFourSixS hSfam hcoh hcohExt hnotation hlamS h6hyp h5hyp hres
    x hxW2 hxne y hyW1 hyne hy_order hcomm hxyCyc hyS hxyS


private theorem theorem_13_6_lambda_tau_vanish_on_yx_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH)
    (x : H)
    (_hxW2 : (x : G) ∈ W2)
    (_hxne : (x : G) ≠ 1)
    (y : G)
    (_hyW1 : y ∈ W1)
    (_hyne : y ≠ 1)
    (_hy_order : orderOf y = q)
    (_hcomm : y * (x : G) = (x : G) * y)
    (_hyS : y ∈ Smax)
    (_hxyS : y * (x : G) ∈ Smax) :
    lamτ (y * (x : G)) = 0 := by
  exact theorem_13_6_lambda_tau_vanish_on_yx_cyclicTI_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT ζ0 lam lamτ
    p q u v c d lamH _hsource _hcoh hlamS _h6hyp _h5hyp _hres x _hxW2 _hxne y
    _hyW1 _hyne _hy_order _hcomm
    (theorem_13_6_yx_mem_cyclicTISet_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT p q u v c d
      _hsource x _hxW2 _hxne y _hyW1 _hyne _hy_order _hcomm)
    _hyS _hxyS


private theorem theorem_13_6_lambda_vanish_on_yx_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (_hyS : y ∈ Smax)
    (hxyS : y * (x : G) ∈ Smax) :
    lam ⟨y * (x : G), hxyS⟩ = 0 := by
  exact theorem_13_6_lambda_vanish_on_yx_of_not_mem_P_sup_U
    Smax P U lam
    (theorem_13_6_lambda_inducedCF_from_P_sup_U_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource h6hyp)
    (theorem_13_6_P_sup_U_subgroupOf_Smax_normal_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    hxyS
    (theorem_13_6_yx_not_mem_P_sup_U_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsource x hxW2 hxne y hyW1 hyne hy_order hcomm)


private theorem theorem_13_6_lambda_congruence_vanish_values_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (x : H)
    (hxW2 : (x : G) ∈ W2)
    (hxne : (x : G) ≠ 1)
    (y : G)
    (hyW1 : y ∈ W1)
    (hyne : y ≠ 1)
    (hy_order : orderOf y = q)
    (hcomm : y * (x : G) = (x : G) * y)
    (hyS : y ∈ Smax)
    (hxyS : y * (x : G) ∈ Smax) :
    lamτ (y * (x : G)) = 0 ∧
      lam ⟨y * (x : G), hxyS⟩ = 0 := by
  constructor
  · exact theorem_13_6_lambda_tau_vanish_on_yx_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ζ0 lam lamτ p q u v c d lamH hsource hcoh hlamS h6hyp h5hyp hres
      x hxW2 hxne y hyW1 hyne hy_order hcomm hyS hxyS
  · exact theorem_13_6_lambda_vanish_on_yx_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ζ0 lam lamτ p q u v c d lamH hsource hlamS h6hyp h5hyp hres
      x hxW2 hxne y hyW1 hyne hy_order hcomm hyS hxyS

private theorem theorem_13_6_lambda_congruence_vanish_witness_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH) :
    ∃ (x : H) (y : G),
      (x : G) ≠ 1 ∧
        (x : G) ∈ P ∧
          ∃ _hyS : y ∈ Smax,
          ∃ hxyS : y * (x : G) ∈ Smax,
            orderOf y = q ∧
              y * (x : G) = (x : G) * y ∧
                lamτ (y * (x : G)) = 0 ∧
                  lam ⟨y * (x : G), hxyS⟩ = 0 := by
  have hsourceOrig := _hsource
  have h6hypOrig := _h6hyp
  rcases _h6hyp with ⟨hH, _hlamIrr, _hlamDeg, _hlamLinear, _hlamτ⟩
  rcases theorem_13_6_exists_Hsharp_mem_W2_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsourceOrig hH with
    ⟨x, hxW2, hxne⟩
  rcases theorem_13_6_exists_W1_order_comm_of_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τT
      p q u v c d hsourceOrig x hxW2 with
    ⟨y, hyW1, hyne, hy_order, hcomm⟩
  rcases _hsource with
    ⟨_hcase, hSTypeP, _hTTypeP, _hp_card, _hq_card, _hCeq, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau,
      _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases hSTypeP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1Hall, hScomp, _hUleDer, _hUnil,
      _hW1norm, _hDercomp, _hMFnotcyc, _hsecond, _hfit, _hfitDer,
      hW2le, _hW2cyc, _hW2ne, _hcent, _hnorm⟩
  rcases hMF with ⟨⟨hP_le_Smax, _hPNormal, _hPNil, _hPHall⟩, _hPmax⟩
  have hxP : (x : G) ∈ P := (le_inf_iff.mp hW2le).1 hxW2
  have hxS : (x : G) ∈ Smax := hP_le_Smax hxP
  have hyS : y ∈ Smax := hScomp.2.1 hyW1
  have hxyS : y * (x : G) ∈ Smax := Smax.mul_mem hyS hxS
  rcases theorem_13_6_lambda_congruence_vanish_values_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ζ0 lam lamτ p q u v c d lamH hsourceOrig _hcoh hlamS h6hypOrig _h5hyp _hres
      x hxW2 hxne y hyW1 hyne hy_order hcomm hyS hxyS with
    ⟨hτzero, hlamzero⟩
  exact ⟨x, y, hxne, hxP, hyS, hxyS, hy_order, hcomm, hτzero, hlamzero⟩

private theorem theorem_13_6_lambda_congruent_mod_one_sub_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (S1 : Finset (Section1.ClassFunction Smax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ζ0 lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (lamH : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH) :
    ∃ (x : H) (eps : ℂ),
      (x : G) ≠ 1 ∧
        (x : G) ∈ P ∧
          IsPrimitiveRoot eps q ∧
            ∃ (etaRoot : ℂ),
              IsIntegral ℤ etaRoot ∧
                ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
                ∃ hτMem : lamτ (x : G) ∈ Theory.Character.cyclotomicOrder etaRoot,
                  ∃ hLamMem : lamH x ∈ Theory.Character.cyclotomicOrder etaRoot,
                    Theory.Character.CongruentModOneSub etaRoot eps
                      (lamτ (x : G)) (lamH x) hepsMem hτMem hLamMem := by
  have h6hypOrig := h6hyp
  have h5hypOrig := h5hyp
  rcases h5hyp with
    ⟨_hH, _hS1, _hζ0, _hlam, _hζ0_ne_lam, hτvirt, _ha, _horth⟩
  rcases h6hyp with ⟨_hH6, hlamIrr, _hdeg, _hlin, _hlamτ⟩
  rcases theorem_13_6_primitive_root_package_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨etaRoot, eps, hqprime, hetaRoot, heps, hepsMem⟩
  rcases theorem_13_6_lambda_congruence_vanish_witness_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ζ0 lam lamτ p q u v c d lamH hsource hcoh hlamS h6hypOrig h5hypOrig hres with
    ⟨x, y, hxne, hxP, hyS, hxyS, hy_order, hcomm, hτzero, hlamzero⟩
  have hetaInt : IsIntegral ℤ etaRoot :=
    hetaRoot.isIntegral (Nat.card_pos (α := G))
  rcases theorem_13_6_lambda_congruent_mod_one_sub_of_vanish
      (Smax := Smax) (H := H) (lam := lam) (lamτ := lamτ) (lamH := lamH)
      (q := q) (x := x) (y := y) (etaRoot := etaRoot) (eps := eps)
      hqprime hetaRoot heps hepsMem hτvirt hlamIrr hres hyS hxyS hy_order
      hcomm hτzero hlamzero with
    ⟨hτMem, hLamMem, hcong⟩
  exact ⟨x, eps, hxne, hxP, heps, etaRoot, hetaInt, hepsMem, hτMem, hLamMem, hcong⟩

private theorem theorem_13_6_alpha_one_congruent_zero_mod_one_sub_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S1 : Finset (Section1.ClassFunction Smax))
    (ζ0 : Section1.ClassFunction Smax)
    (lamH α : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      lamτ (x : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH x + α x) :
    ∃ (etaRoot eps : ℂ),
      IsIntegral ℤ etaRoot ∧
        IsPrimitiveRoot eps q ∧
          ∃ hepsMem : eps ∈ Theory.Character.cyclotomicOrder etaRoot,
          ∃ hαMem : α 1 ∈ Theory.Character.cyclotomicOrder etaRoot,
            Theory.Character.CongruentModOneSub etaRoot eps (α 1) 0
              hepsMem hαMem (Theory.Character.cyclotomicOrder etaRoot).zero_mem := by
  have hcf : Section5.cfNormSq lam = 1 :=
    theorem_13_6_lambda_normSq_one_of_hypothesis lamτ h6hyp
  rcases theorem_13_6_lambda_congruent_mod_one_sub_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam S1 τS τ1 τT
      ζ0 lam lamτ p q u v c d lamH hsource hcoh hlamS h6hyp h5hyp hres with
    ⟨x, eps, hxne, hxP, heps, etaRoot, hetaInt, hepsMem, hτMem, hLamMem, hcong⟩
  rcases hα with ⟨hαvirt, hαker⟩
  rcases theorem_13_6_virtualCharacter_one_eq_int hαvirt with ⟨n, hn⟩
  have hαMem : α 1 ∈ Theory.Character.cyclotomicOrder etaRoot := by
    rw [hn]
    exact Theory.Character.intCast_mem_cyclotomicOrder etaRoot n
  exact ⟨etaRoot, eps, hetaInt, heps, hepsMem, hαMem,
    theorem_13_6_alpha_one_congruent_zero_mod_one_sub_of_lambda_congruence
      hepsMem hcf ⟨hαvirt, hαker⟩ x hxne hxP hexp hτMem hLamMem hαMem hcong⟩

private theorem theorem_13_6_alpha_one_q_multiple_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S1 : Finset (Section1.ClassFunction Smax))
    (ζ0 : Section1.ClassFunction Smax)
    (lamH α : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      lamτ (x : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH x + α x)
    (_hformula : theorem_13_5_squareSumFormula Smax H lam lamH α lamτ (1 : ℂ)) :
    ∃ b : ℤ, α 1 = (q : ℂ) * (b : ℂ) := by
  rcases hα with ⟨hαvirt, hαker⟩
  rcases theorem_13_6_alpha_one_congruent_zero_mod_one_sub_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d S1 ζ0 lamH α hsource hcoh hlamS h6hyp h5hyp hres
      ⟨hαvirt, hαker⟩ hexp with
    ⟨etaRoot, eps, hetaInt, heps, hepsMem, hαMem, hcong⟩
  exact theorem_13_6_alpha_one_q_multiple_of_congruence
    (theorem_13_6_q_prime_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    hαvirt hetaInt heps hepsMem hαMem hcong

private theorem theorem_13_6_energy_identity_of_lambda_normSq_one
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H : Subgroup G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (lamH α : Section1.ClassFunction H)
    (u q : ℕ)
    (b : ℤ)
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (hdeg : Section1.degree lam = (u * q : ℂ))
    (hcf : Section5.cfNormSq lam = 1)
    (hformula : theorem_13_5_squareSumFormula Smax H lam lamH α lamτ (1 : ℂ))
    (hα1 : α 1 = (q : ℂ) * (b : ℂ)) :
    Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
        2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
          Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  rcases hres with ⟨hHS, hres_eval⟩
  have hlamH_one : lamH 1 = lam 1 := by
    have htemp := hres_eval (1 : H)
    have hone : (⟨(1 : G), hHS (Subgroup.one_mem H)⟩ : Smax) = (1 : Smax) :=
      Subtype.ext (by simp)
    simpa [hone] using htemp
  have hlam_one : lam 1 = ((u * q : ℕ) : ℂ) := by
    simpa [Section1.degree_apply, Nat.cast_mul] using hdeg
  unfold theorem_13_5_squareSumFormula at hformula
  have hC :
      ((Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ : ℝ) : ℂ) =
        (((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
          2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
            Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α : ℝ) := by
    calc
      ((Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ : ℝ) : ℂ) =
          (1 ^ 2 / (Section5.cfNormSq lam : ℂ)) *
            ((Nat.card Smax : ℂ) - (lam 1) ^ 2 /
              (Section5.cfNormSq lam : ℂ)) -
              2 * 1 * lamH 1 * α 1 / (Section5.cfNormSq lam : ℂ) +
                (Section7.subgroupSupportEnergy H
                  (Section7.puncturedSubgroupSet H) α : ℂ) := hformula
      _ = (((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
          2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
            Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α : ℝ) := by
        rw [hcf, hlamH_one, hlam_one, hα1]
        simp [Complex.normSq, Nat.cast_mul]
        ring
  exact Complex.ofReal_inj.mp hC

private theorem theorem_13_6_energy_identity_of_alpha_one_q_multiple_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S1 : Finset (Section1.ClassFunction Smax))
    (ζ0 : Section1.ClassFunction Smax)
    (lamH α : Section1.ClassFunction H)
    (b : ℤ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      lamτ (x : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH x + α x)
    (_hformula : theorem_13_5_squareSumFormula Smax H lam lamH α lamτ (1 : ℂ))
    (_hα1 : α 1 = (q : ℂ) * (b : ℂ)) :
    Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
        2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
          Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α := by
  have hcf : Section5.cfNormSq lam = 1 :=
    theorem_13_6_lambda_normSq_one_of_hypothesis lamτ _h6hyp
  rcases _h6hyp with ⟨_hH, _hlam_irred, hdeg, _hlam_linear, _hlamτ⟩
  exact theorem_13_6_energy_identity_of_lambda_normSq_one Smax H lam lamτ
    lamH α u q b _hres hdeg hcf _hformula _hα1

private theorem theorem_13_6_p_prime_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    Nat.Prime p := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with hcaseA | hcaseB
  · rcases hcaseA with
      ⟨_hBarU, _a, _h92, _hH0le, _hCentIn, hpPrime, _hqPrime,
        _hpdata, _hquot, _hcardQuot, _hadvd, _hinj⟩
    exact hpPrime
  · rcases hcaseB with
      ⟨_h92, _hH0le, _hCentIn, hpPrime, _hqPrime, _hpdata, _hquot,
        _hcentBy, _hcyclicQuot, _hirr, _hfield, _hcop, _hdiv,
        _hprimeField⟩
    exact hpPrime

private theorem theorem_13_6_p_ne_two_of_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d) :
    p ≠ 2 := by
  rcases hsource with
    ⟨_hcase, _hptypeS, _hptypeT, hp_card, _hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotation, _hDadeDiff, _hZeroBase, _hConjIndex, _hConjBeta,
      _hChoice, hMin, _hTauS, _hTauT⟩
  have hoddG : Odd (Nat.card G) := by
    letI : IsMinCE G := hMin
    exact IsMinCE.odd_order
  have hW2_ne_two : Nat.card W2 ≠ 2 :=
    Odd.ne_two_of_dvd_nat hoddG (Subgroup.card_subgroup_dvd_card W2)
  intro hp2
  apply hW2_ne_two
  rw [← hp_card, hp2]

private theorem theorem_13_6_two_mul_u_le_card_P_sub_one_of_pf13_2
    {p q u cardP : ℕ}
    (hp : Nat.Prime p)
    (hp_ne_two : p ≠ 2)
    (hPcard : cardP = p ^ q)
    (hu : u ≤ (p ^ q - 1) / (p - 1)) :
    2 * u ≤ cardP - 1 := by
  have hp_ge3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have hden_ge : 2 ≤ p - 1 := by omega
  have hquot_le : (p ^ q - 1) / (p - 1) ≤ (p ^ q - 1) / 2 := by
    exact Nat.div_le_div (Nat.le_refl (p ^ q - 1)) hden_ge
      (by decide : (2 : ℕ) ≠ 0)
  have hu_half : u ≤ (p ^ q - 1) / 2 := hu.trans hquot_le
  have hmul : u * 2 ≤ p ^ q - 1 := by
    exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hu_half
  omega

private theorem theorem_13_6_two_mul_u_le_card_P_sub_one_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u) :
    2 * u ≤ Nat.card P - 1 := by
  rcases theorem_13_2 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with
    ⟨_hMF, _htype, _hlarge, _hUcomm, _hFrob, _hPelem, hPcard, huBound,
      _hcoh, _hBook, _hTau, _hnorm⟩
  exact theorem_13_6_two_mul_u_le_card_P_sub_one_of_pf13_2
    (theorem_13_6_p_prime_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    (theorem_13_6_p_ne_two_of_source
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource)
    hPcard huBound

private theorem theorem_13_6_congruence_arithmetic_input_of_components
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H P : Subgroup G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (α : Section1.ClassFunction H)
    (u q : ℕ)
    (b : ℤ)
    (henergy :
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
        ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
          2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
            Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α)
    (hα1 : α 1 = (q : ℂ) * (b : ℂ))
    (hu : 2 * u ≤ Nat.card P - 1) :
    ∃ b : ℤ,
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
          ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
            2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
              Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α ∧
        α 1 = (q : ℂ) * (b : ℂ) ∧
        2 * u ≤ Nat.card P - 1 := by
  exact ⟨b, henergy, hα1, hu⟩

private theorem theorem_13_6_congruence_arithmetic_input_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S1 : Finset (Section1.ClassFunction Smax))
    (ζ0 : Section1.ClassFunction Smax)
    (lamH α : Section1.ClassFunction H)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcoh : Section6.coherentExtension Sfam τS τ1)
    (hlamS : lam ∈ Sfam)
    (h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (hres : classFunctionRestrictionData H Smax lam lamH)
    (hα : virtualCharacterKernelConstituentData H P α)
    (hexp : ∀ x : H, (x : G) ≠ 1 →
      lamτ (x : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH x + α x)
    (hformula : theorem_13_5_squareSumFormula Smax H lam lamH α lamτ (1 : ℂ)) :
    ∃ b : ℤ,
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
          ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
            2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
              Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α ∧
        α 1 = (q : ℂ) * (b : ℂ) ∧
        2 * u ≤ Nat.card P - 1 := by
  rcases theorem_13_6_alpha_one_q_multiple_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d S1 ζ0 lamH α hsource hcoh hlamS h6hyp h5hyp hres hα hexp
      hformula with
    ⟨b, hα1⟩
  exact theorem_13_6_congruence_arithmetic_input_of_components Smax H P lam lamτ α u q b
    (theorem_13_6_energy_identity_of_alpha_one_q_multiple_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d S1 ζ0 lamH α b hsource h6hyp h5hyp hres hα
      hexp hformula hα1)
    hα1
    (theorem_13_6_two_mul_u_le_card_P_sub_one_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource h6hyp)

private theorem theorem_13_6_alpha_correction_nonnegative
    (m u q : ℕ) (b : ℤ) (hu : 2 * u ≤ m) :
    0 ≤ (m : ℝ) * (((q : ℝ) * (b : ℝ)) ^ 2) -
      2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) := by
  have hbase :
      0 ≤ (m : ℝ) * ((b : ℝ) ^ 2) - 2 * (u : ℝ) * (b : ℝ) := by
    rcases lt_trichotomy b 0 with hbneg | hbeq | hbpos
    · have hbR : (b : ℝ) < 0 := by exact_mod_cast hbneg
      have huR : 0 ≤ (u : ℝ) := by exact_mod_cast Nat.zero_le u
      have hmR : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      have hb2 : 0 ≤ (b : ℝ) ^ 2 := sq_nonneg (b : ℝ)
      nlinarith
    · subst b
      simp
    · have hbInt : (1 : ℤ) ≤ b := by omega
      have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbInt
      have huR : (2 * u : ℝ) ≤ (m : ℝ) := by exact_mod_cast hu
      nlinarith [sq_nonneg ((b : ℝ) - 1), sq_nonneg (b : ℝ)]
  have hq2 : 0 ≤ ((q : ℝ) ^ 2) := sq_nonneg (q : ℝ)
  have hmul : 0 ≤ ((q : ℝ) ^ 2) *
      ((m : ℝ) * ((b : ℝ) ^ 2) - 2 * (u : ℝ) * (b : ℝ)) :=
    mul_nonneg hq2 hbase
  norm_num [Nat.cast_mul] at hmul ⊢
  ring_nf at hmul ⊢
  linarith

private theorem theorem_13_6_squareSumLowerBound_of_arithmetic_input
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax H P : Subgroup G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (α : Section1.ClassFunction H)
    (u q : ℕ)
    (hinput : ∃ b : ℤ,
      Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ =
          ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) -
            2 * ((u * q : ℕ) : ℝ) * ((q : ℝ) * (b : ℝ)) +
              Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α ∧
        α 1 = (q : ℂ) * (b : ℂ) ∧
        2 * u ≤ Nat.card P - 1)
    (hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) lamτ
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) := by
  rcases hinput with ⟨b, henergy, hα1, hu⟩
  unfold squareSumLowerBound
  let m : ℕ := Nat.card P - 1
  let B : ℝ := (Nat.card Smax : ℝ) - Complex.normSq (lam 1)
  let A : ℝ := Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α
  let t : ℝ := (q : ℝ) * (b : ℝ)
  have hcorr : 0 ≤ (m : ℝ) * (t ^ 2) - 2 * ((u * q : ℕ) : ℝ) * t := by
    exact theorem_13_6_alpha_correction_nonnegative m u q b (by simpa [m] using hu)
  have hnorm : Complex.normSq (α 1) = t ^ 2 := by
    rw [hα1]
    simp [t, Complex.normSq]
    ring
  have hlower' : (m : ℝ) * (t ^ 2) ≤ A := by
    simpa [m, A, hnorm] using hlower
  have htarget : B ≤ B - 2 * ((u * q : ℕ) : ℝ) * t + A := by
    nlinarith
  calc
    ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) = B := rfl
    _ ≤ B - 2 * ((u * q : ℕ) : ℝ) * t + A := htarget
    _ = Section7.supportEnergy (Section7.puncturedSubgroupSet H) lamτ := by
      simpa [B, A, t] using henergy.symm

private theorem theorem_13_6_congruence_arithmetic_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (S1 : Finset (Section1.ClassFunction Smax))
    (ζ0 : Section1.ClassFunction Smax)
    (lamH α : Section1.ClassFunction H)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hcoh : Section6.coherentExtension Sfam τS τ1)
    (_hlamS : lam ∈ Sfam)
    (_h6hyp : theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u)
    (_h5hyp : theorem_13_5_hypothesis Smax H P C S1 τS ζ0 lam lamτ (1 : ℂ))
    (_hres : classFunctionRestrictionData H Smax lam lamH)
    (_hα : virtualCharacterKernelConstituentData H P α)
    (_hexp : ∀ x : H, (x : G) ≠ 1 →
      lamτ (x : G) =
        ((1 : ℂ) / (Section5.cfNormSq lam : ℂ)) * lamH x + α x)
    (_hformula : theorem_13_5_squareSumFormula Smax H lam lamH α lamτ (1 : ℂ))
    (_hlower : ((Nat.card P - 1 : ℕ) : ℝ) * Complex.normSq (α 1) ≤
      Section7.subgroupSupportEnergy H (Section7.puncturedSubgroupSet H) α) :
    squareSumLowerBound (Section7.puncturedSubgroupSet H) lamτ
      ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) := by
  exact theorem_13_6_squareSumLowerBound_of_arithmetic_input Smax H P lam lamτ α u q
    (theorem_13_6_congruence_arithmetic_input_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT lam lamτ
      p q u v c d S1 ζ0 lamH α _hsource _hcoh _hlamS _h6hyp _h5hyp _hres _hα _hexp
      _hformula)
    _hlower

public theorem theorem_13_6
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D H : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τ1 : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (lam : Section1.ClassFunction Smax)
    (lamτ : Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      Section6.coherentExtension Sfam τS τ1 →
      lam ∈ Sfam →
      theorem_13_6_hypothesis Smax H P C τ1 lam lamτ p q u →
        squareSumLowerBound (Section7.puncturedSubgroupSet H) lamτ
          ((Nat.card Smax : ℝ) - Complex.normSq (lam 1)) := by
  intro hsource hcoh hlamS h6hyp
  rcases theorem_13_6_theorem_13_5_input_source
      Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
      lam lamτ p q u v c d hsource hcoh hlamS h6hyp with
    ⟨S1, ζ0, lamH, h5hyp, hres⟩
  rcases theorem_13_5 Smax Tmax W W1 W2 P Q U V C D H
      Sfam Tfam S1 τS τT ζ0 lam lamH lamτ (1 : ℂ) p q u v c d
      hsource h5hyp hres with
    ⟨α, hα, hexp, hformula, hlower⟩
  exact theorem_13_6_congruence_arithmetic_source
    Smax Tmax W W1 W2 P Q U V C D H Sfam Tfam τS τ1 τT
    lam lamτ p q u v c d S1 ζ0 lamH α hsource hcoh hlamS h6hyp h5hyp hres
    hα hexp hformula hlower
end CFSG.Section13

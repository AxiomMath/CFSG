module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaRed
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35OmegaBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open CFSG.OddStandard.SmallF3.Omega CFSG.GroupTheory

open scoped Pointwise

theorem sylowPQMaximal_of_forall_le {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (h : ∀ H : Subgroup G, (S : Subgroup G) ≤ H →
      CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} H →
      ∃ M : Subgroup G, H ≤ M ∧ SylowPQMaximal p q M) :
    SylowPQMaximal p q G := by
  classical
  intro P H hPH hH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hPS0 : (P : Subgroup G) = (MulAut.conj g) • (S : Subgroup G) := by
    calc
      (P : Subgroup G) = ((g • S : Sylow p G) : Subgroup G) := by rw [hg]
      _ = (MulAut.conj g) • (S : Subgroup G) := Sylow.coe_subgroup_smul
  have hconj : (MulAut.conj g⁻¹) * (MulAut.conj g) = 1 := by
    simp
  have hPS : (MulAut.conj g⁻¹) • (P : Subgroup G) = (S : Subgroup G) := by
    rw [hPS0, ← mul_smul, hconj, one_smul]
  let H' : Subgroup G := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hSH' : (S : Subgroup G) ≤ H' := by
    dsimp only [H']
    rw [← hPS, CFSG.GroupActions.mulAut_smul_subgroup_eq_map]
    exact Subgroup.map_mono hPH
  have hcardH' : Nat.card H' = Nat.card H := by
    dsimp only [H']
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hH' : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q} H' := by
    intro r hr
    exact hH r (by rwa [hcardH'] at hr)
  obtain ⟨M, hH'M, hEM⟩ := h H' hSH' hH'
  have hSM : (S : Subgroup G) ≤ M := le_trans hSH' hH'M
  have hcontain : ((S.subtype hSM : Sylow p M) : Subgroup M) ≤ H'.subgroupOf M := by
    intro x hx
    exact hSH' hx
  have hcardHM : Nat.card (H'.subgroupOf M) = Nat.card H' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH'M).toEquiv
  have hHMpi : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = p ∨ (r : ℕ) = q}
      (H'.subgroupOf M) := by
    intro r hr
    exact hH' r (by rwa [hcardHM] at hr)
  have hPg : IsPGroup p (H'.subgroupOf M) :=
    hEM (S.subtype hSM) (H'.subgroupOf M) hcontain hHMpi
  have hP' : IsPGroup p H' := hPg.of_equiv (Subgroup.subgroupOfEquivOfLe hH'M)
  exact hP'.of_equiv (Subgroup.equivMapOfInjective H (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).symm

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sylowPQMaximal_omegaGroup_seven_of_twoSubgroup (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (T : Subgroup (OGroup Q))
    (hTΩ : T ≤ omegaGroup hQ) (hT2 : IsPGroup 2 T)
    (hT : ∀ W : Submodule (ZMod 3) V, W ≠ ⊥ → W ≠ ⊤ →
      (∀ g ∈ T, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W) →
      ∃ (s : OGroup Q) (hs : s * s = 1), commSp s = W ∧
        SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_fixSp hQ hs)) ∧
        SylowPQMaximal 2 5 (omegaGroup (nondegenerate_restrict_commSp hQ hs))) :
    SylowPQMaximal 2 5 (omegaGroup hQ) := by
  classical
  have hT'2 : IsPGroup 2 (T.subgroupOf (omegaGroup hQ)) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTΩ).symm
  obtain ⟨S, hT'S⟩ := hT'2.exists_le_sylow
  refine sylowPQMaximal_of_forall_le (p := 2) (q := 5) S ?_
  intro H hSH hH
  let f : omegaGroup hQ →* (V ≃ₗ[ZMod 3] V) :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp (omegaGroup hQ).subtype
  let H₂ : Subgroup (V ≃ₗ[ZMod 3] V) := H.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hcardH₂ : Nat.card H₂ = Nat.card H := by
    dsimp only [H₂]
    exact Subgroup.card_map_of_injective hf_inj
  have hH₂ : CFSG.IsPiSubgroup {r : Nat.Primes | (r : ℕ) = 2 ∨ (r : ℕ) = 5} H₂ := by
    intro r hr
    exact hH r (by rwa [hcardH₂] at hr)
  have hdet : ∀ g ∈ H₂, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1 := by
    intro g hg
    dsimp only [H₂] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    have hdetΩ : CFSG.ClassicalInvolution.detSpinorNorm hQ (h : OGroup Q) = 1 :=
      (mem_omegaGroup_iff hQ).mp h.2
    rw [CFSG.ClassicalInvolution.detSpinorNorm_apply] at hdetΩ
    have hdet' : QuadraticMap.orthogonalDet Q (h : OGroup Q) = 1 :=
      (Prod.ext_iff.mp hdetΩ).1
    rw [QuadraticMap.orthogonalDet_apply] at hdet'
    have hdetLin : LinearMap.det (((h : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) = 1 := by
      rw [← LinearEquiv.coe_det, hdet']
      rfl
    simpa [f] using hdetLin
  obtain ⟨W, hWbot, hWtop, hWinv⟩ :=
    exists_invariant_of_isPiSubgroup_two_five hdim H₂ hdet hH₂
  have hWinvT : ∀ g ∈ T, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W := by
    intro g hg w hw
    have hgT' : (⟨g, hTΩ hg⟩ : omegaGroup hQ) ∈ T.subgroupOf (omegaGroup hQ) := by
      exact hg
    have hgH : (⟨g, hTΩ hg⟩ : omegaGroup hQ) ∈ H := hSH (hT'S hgT')
    have hg₂ : (g : V ≃ₗ[ZMod 3] V) ∈ H₂ := by
      dsimp only [H₂]
      rw [Subgroup.mem_map]
      exact ⟨⟨g, hTΩ hg⟩, hgH, rfl⟩
    exact hWinv (g : V ≃ₗ[ZMod 3] V) hg₂ w hw
  obtain ⟨s, hs, hcommSp, hfix, hcomm⟩ := hT W hWbot hWtop hWinvT
  have hWinvH : ∀ g ∈ H, ∀ w ∈ W, (g : V ≃ₗ[ZMod 3] V) w ∈ W := by
    intro g hg w hw
    have hg₂ : (g : V ≃ₗ[ZMod 3] V) ∈ H₂ := by
      dsimp only [H₂]
      rw [Subgroup.mem_map]
      exact ⟨g, hg, rfl⟩
    exact hWinv (g : V ≃ₗ[ZMod 3] V) hg₂ w hw
  let M' : Subgroup (OGroup Q) :=
    omegaGroup hQ ⊓ Subgroup.centralizer ({s} : Set (OGroup Q))
  have hM'E : SylowPQMaximal 2 5 M' :=
    sylowPQMaximal_omegaGroup_inf_centralizer hQ hs hfix hcomm
  let M : Subgroup (omegaGroup hQ) := M'.subgroupOf (omegaGroup hQ)
  have hME : SylowPQMaximal 2 5 M :=
    SylowPQMaximal.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : M' ≤ omegaGroup hQ)).symm hM'E
  have hHM : H ≤ M := by
    intro h hh
    change (h : OGroup Q) ∈ M'
    refine ⟨h.2, ?_⟩
    change (h : OGroup Q) ∈ Subgroup.centralizer ({s} : Set (OGroup Q))
    rw [mem_centralizer_iff_map_commSp hQ hs]
    rw [hcommSp]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro x ⟨w, hw, rfl⟩
      exact hWinvH h hh w hw
    · exact LinearEquiv.finrank_map_eq ((h : OGroup Q) : V ≃ₗ[ZMod 3] V) W
  exact ⟨M, hHM, hME⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

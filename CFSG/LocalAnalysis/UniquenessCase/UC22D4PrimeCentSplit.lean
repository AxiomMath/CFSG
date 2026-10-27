module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentRank
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralMain
import CFSG.RankThree.Chevalley.SteinbergBLTrialitySplitInner
import CFSG.RankThree.PartOne.FOC.ExcD4Split

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne
open scoped MatrixGroups


theorem uc22d4_centShape_split {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrq : r ∣ ℓ ^ f - 1)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hx : orderOf x = r) :
    UC22D4CentShape ℓ (ℓ ^ f)
      (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hSyl, ⟨e, he⟩, -, -, hcases⟩ :=
    triality_split_prime_toral_Sylow_and_centralizers hℓ hf K hK σ hσ hr hr3 hrq
  have hPx : IsPGroup r (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := hSyl _ hPx
  have hgx : g * x * g⁻¹ ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hgxH : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := hgx
  have hordx : orderOf ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = r := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x).trans hx
  obtain ⟨ζ, hζ, hzζ⟩ :=
    CFSG.RankThree.Chevalley.TrialitySplitInner.exists_fixedUnit_orderOf_eq hℓ hf hK σ hσ hr hrq
  have hyp : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ^ r = 1 := by
    rw [← hordx]
    exact pow_orderOf_eq_one _
  obtain ⟨u, v, huv⟩ :=
    CFSG.RankThree.Chevalley.TrialitySplitInner.exists_torus_coords_of_pow_eq_one hr e he hζ hzζ
      hgxH hyp
  have hne1 : trialityOuterTorus K σ (trialityFixedUnit K σ ζ ^ u) *
      trialityMiddleTorus K σ (ζ ^ v) ≠ 1 := by
    intro h1
    rw [huv, h1, orderOf_one] at hordx
    exact hr.one_lt.ne hordx
  obtain ⟨a, hha, hao, hcase⟩ := hcases ζ hζ u v hne1
  have hxa : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag a := by
    rw [← hha]
    exact huv
  let Fx : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp (MulAut.conj g).toMonoidHom
  have hFx : Function.Injective Fx :=
    Subtype.val_injective.comp (MulAut.conj g).injective
  have hmap : (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map Fx =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.centralizer
          ({rootDiagUnit TwistTag.D4.tag a} : Set (ModGL TwistTag.D4.tag K)) := by
    change (centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
        ((graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp
          (MulAut.conj g).toMonoidHom) = _
    rw [← Subgroup.map_map, map_conj_centralizer_singleton_eq,
      CFSG.RankThree.Chevalley.map_subtype_centralizer_singleton, hxa]
  let F : ↥(centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) →*
      ModGL TwistTag.D4.tag K :=
    Fx.comp
      (Subgroup.centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).subtype
  have hF : Function.Injective F :=
    hFx.comp (Subgroup.subtype_injective _)
  have hFrange : F.range = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer
        ({rootDiagUnit TwistTag.D4.tag a} : Set (ModGL TwistTag.D4.tag K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hmap
  rcases hcase with ⟨-, hDH⟩ |
    ⟨α, hα, hα0, -, D, Q, hD, hQ, hDQ, -, hSL3, hSL1, hQq, hcomm, hcent, hZH, -, hZodd⟩
  ·
    refine Or.inl ?_
    have hHcomm : ∀ p q : ↥(graphFixedRootTorus TwistTag.D4 K σ.toRingHom), p * q = q * p := by
      intro p q
      obtain ⟨P, rfl⟩ := e.surjective p
      obtain ⟨Q, rfl⟩ := e.surjective q
      rw [← map_mul, ← map_mul, mul_comm P Q]
    intro p hp q hq
    have hpF : F ⟨p, hp⟩ ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
      rw [← hDH, ← hFrange]
      exact ⟨⟨p, hp⟩, rfl⟩
    have hqF : F ⟨q, hq⟩ ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
      rw [← hDH, ← hFrange]
      exact ⟨⟨q, hq⟩, rfl⟩
    have h1 : F (⟨p, hp⟩ * ⟨q, hq⟩) = F (⟨q, hq⟩ * ⟨p, hp⟩) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hHcomm ⟨_, hpF⟩ ⟨_, hqF⟩)
    exact congrArg Subtype.val (hF h1)
  · obtain ⟨hRmap, -, -⟩ :=
      CFSG.RankThree.Chevalley.TrialitySplitInner.derived_centralizer_embedding Fx hFx
        (hmap.trans hD.symm) hcomm hQq hcent hZH
    rcases CFSG.RankThree.PartOne.FOC.card_diagramOrbit_D4 hα with h | h
    ·
      refine Or.inr (Or.inr (Or.inl ?_))
      obtain ⟨eQ⟩ := hSL1 h
      refine ⟨trialityFixedField K σ.toRingHom, inferInstance, inferInstance,
        CFSG.RankThree.Chevalley.TrialitySplitInner.card_trialityFixedField hℓ hf hK σ hσ, ?_⟩
      exact ⟨(Subgroup.equivMapOfInjective _ Fx hFx).trans
        ((MulEquiv.subgroupCongr hRmap).trans eQ.symm)⟩
    ·
      refine Or.inr (Or.inr (Or.inr ?_))
      obtain ⟨eQ⟩ := hSL3 h
      have hRle : (⁅centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
            Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
          centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
        Subgroup.commutator_le_of_le le_rfl le_rfl
      have hK3 : Nat.card K = ℓ ^ (3 * f) := by
        rw [hK, ← pow_mul, Nat.mul_comm f 3]
      have eR : (⁅centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          centralizer ({x} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
            Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃* SL2 K :=
        (Subgroup.equivMapOfInjective _ Fx hFx).trans
          ((MulEquiv.subgroupCongr hRmap).trans eQ.symm)
      have h := uc22d4_le_pRank_of_sl2 hℓ hK3 hRle eR
      omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

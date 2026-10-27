module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralCentralizer
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise commutatorElement

@[expose] def sl2CongrRingEquiv {F F' : Type*} [Field F] [Field F'] (e : F ≃+* F') :
    SL2 F ≃* SL2 F' :=
  { Matrix.SpecialLinearGroup.map e.toRingHom with
    invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
    left_inv := fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp
    right_inv := fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp }

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem orbitConjRankOneHom_injective_D4 (hσ : σ ^ 3 = 1) (v : WeylGroup TwistTag.D4.tag)
    (b : Fin TwistTag.D4.foldedTag.rank) :
    Function.Injective (orbitConjRankOneHom TwistTag.D4 K σ.toRingHom v b) :=
  orbitConjRankOneHom_injective
    ((triality_all_characteristic_faithful_torus_coordinates K σ hσ).2.2.2.2.1 b).2

theorem nonempty_mulEquiv_graphFixedRootPair_D4 (hσ : σ ^ 3 = 1) {v : WeylGroup TwistTag.D4.tag}
    (hv : v ∈ relWeylTwist TwistTag.D4) (b : Fin TwistTag.D4.foldedTag.rank) :
    Nonempty (SL2 (orbitField TwistTag.D4 K σ.toRingHom b) ≃*
      graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b)) :=
  ⟨(MonoidHom.ofInjective (orbitConjRankOneHom_injective_D4 σ hσ v b)).trans
    (MulEquiv.subgroupCongr (range_orbitConjRankOneHom hv b))⟩

theorem triality_orbitPair_structure (hσ : σ ^ 3 = 1) {v : WeylGroup TwistTag.D4.tag}
    (hv : v ∈ relWeylTwist TwistTag.D4) (b : Fin TwistTag.D4.foldedTag.rank)
    (h4 : ∃ s : Finset (orbitField TwistTag.D4 K σ.toRingHom b), s.card = 4)
    (D : Subgroup (ModGL TwistTag.D4.tag K))
    (hD : D = graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
      graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b)) :
    CFSG.IsQuasisimple
        (graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b)) ∧
      ⁅D, D⁆ = graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b) ∧
      D ⊓ Subgroup.centralizer ((graphFixedRootPair TwistTag.D4 K σ.toRingHom
          (fixedOrbitImage TwistTag.D4 v b) : Subgroup (ModGL TwistTag.D4.tag K)) :
            Set (ModGL TwistTag.D4.tag K)) = (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hH
  set O := fixedOrbitImage TwistTag.D4 v b with hO
  set Q := graphFixedRootPair TwistTag.D4 K σ.toRingHom O with hQ
  set Φ := orbitConjRankOneHom TwistTag.D4 K σ.toRingHom v b with hΦ
  have hΦinj : Function.Injective Φ := orbitConjRankOneHom_injective_D4 σ hσ v b
  have hOroot : ∀ β ∈ O, IsRoot TwistTag.D4.tag β := fun β hβ =>
    isRoot_of_mem_fixedOrbitImage hβ
  obtain ⟨e⟩ := nonempty_mulEquiv_graphFixedRootPair_D4 σ hσ hv b
  have hquasi : CFSG.IsQuasisimple Q :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (CFSG.RankThree.Classical.isQuasisimple_SL2 h4)
  have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.1 hquasi.1
  have hDset : (D : Set (ModGL TwistTag.D4.tag K)) = (H : Set (ModGL TwistTag.D4.tag K)) * Q := by
    rw [hD]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (graphFixedRootTorus_le_normalizer hOroot)
  have hQD : Q ≤ D := hD ▸ le_sup_right
  have hHD : H ≤ D := hD ▸ le_sup_left
  have hcomm : ⁅D, D⁆ = Q := by
    refine le_antisymm ?_ (hperf ▸ Subgroup.commutator_mono hQD hQD)
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [← SetLike.mem_coe, hDset] at hx hy
    obtain ⟨h, hh, q, hq, rfl⟩ := hx
    obtain ⟨h', hh', q', hq', rfl⟩ := hy
    have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
        (h' * q'⁻¹ * h'⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1, ← graphFixedRootTorus_mul_comm hh hh']
    refine mul_mem (conj_mem_graphFixedRootPair hOroot (mul_mem hh hh') (mul_mem ?_
      (mul_mem hq' (inv_mem hq)))) (conj_mem_graphFixedRootPair hOroot hh' (inv_mem hq'))
    have := conj_mem_graphFixedRootPair hOroot (inv_mem hh') hq
    rwa [inv_inv] at this
  have hCH : D ⊓ Subgroup.centralizer (Q : Set (ModGL TwistTag.D4.tag K)) ≤ H := by
    intro z hz
    obtain ⟨hzD, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzD' : z ∈ (D : Set (ModGL TwistTag.D4.tag K)) := hzD
    rw [hDset] at hzD'
    obtain ⟨h, hh, q, hq, rfl⟩ := hzD'
    have hconj : ∀ x ∈ Q, q * x * q⁻¹ = h⁻¹ * x * h⁻¹⁻¹ := fun x hx => by
      have e2 : q * x * q⁻¹ = h⁻¹ * ((h * q) * x * (h * q)⁻¹) * h⁻¹⁻¹ := by group
      rw [e2, ← Subgroup.mem_centralizer_iff.1 hzC x hx, mul_inv_cancel_right]
    have hT : h⁻¹ ∈ torusGroup TwistTag.D4.tag K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (inv_mem hh)).1).1
    have hΓ : h⁻¹ ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (inv_mem hh)).1).2
    have hpres : ∀ S : Set (Fin TwistTag.D4.tag.rank → ℤ), (∀ β ∈ S, IsRoot TwistTag.D4.tag β) →
        ∀ x ∈ rootSpan TwistTag.D4.tag K S ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom,
          h⁻¹ * x * h⁻¹⁻¹ ∈ rootSpan TwistTag.D4.tag K S ⊓
            twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
      intro S hS x hx
      refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hΓ (Subgroup.mem_inf.1 hx).2)
        (inv_mem hΓ)⟩
      rw [← map_conj_rootSpan_of_mem_torusGroup hT hS]
      exact ⟨x, (Subgroup.mem_inf.1 hx).1, rfl⟩
    have hnegroot : ∀ β ∈ -O, IsRoot TwistTag.D4.tag β := fun β hβ => by
      have := IsRoot.neg (hOroot _ (Set.mem_neg.1 hβ))
      rwa [neg_neg] at this
    have hqrange : q ∈ Φ.range := by
      rw [hΦ, range_orbitConjRankOneHom hv b]
      exact hq
    obtain ⟨A, rfl⟩ := hqrange
    have hAu : ∃ c, A * uSL 1 * A⁻¹ = uSL c := by
      have hx := orbitConjRankOneHom_uSL_mem (K := K) (σ := σ.toRingHom) hv b 1
      have h1 := hconj _ (Subgroup.mem_sup_left hx)
      have h2 := hpres O hOroot _ hx
      rw [← h1] at h2
      obtain ⟨c, hc⟩ := exists_eq_orbitConjRankOneHom_uSL hv h2
      refine ⟨c, hΦinj ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact hc
    have hAv : ∃ c, A * vSL 1 * A⁻¹ = vSL c := by
      have hx := orbitConjRankOneHom_vSL_mem (K := K) (σ := σ.toRingHom) hv b 1
      have h1 := hconj _ (Subgroup.mem_sup_right hx)
      have h2 := hpres (-O) hnegroot _ hx
      rw [← h1] at h2
      obtain ⟨c, hc⟩ := exists_eq_orbitConjRankOneHom_vSL hv h2
      refine ⟨c, hΦinj ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact hc
    obtain ⟨c, hc⟩ := hAu
    obtain ⟨c', hc'⟩ := hAv
    obtain ⟨u, rfl⟩ := exists_eq_HSL_of_conj hc hc'
    exact mul_mem hh (orbitConjRankOneHom_HSL_mem hv b u)
  have hZ : D ⊓ Subgroup.centralizer (Q : Set (ModGL TwistTag.D4.tag K)) =
      (Subgroup.center D).map D.subtype := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzD, hzC⟩ := Subgroup.mem_inf.1 hz
      have hzH := hCH hz
      have hle : D ≤ Subgroup.centralizer {z} := by
        rw [hD]
        refine sup_le (fun t ht => ?_) (fun x hx => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact graphFixedRootTorus_mul_comm ht hzH
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.1 hzC x hx
      refine ⟨⟨z, hzD⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle g.2)
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hQD hx⟩)
  exact ⟨hquasi, hcomm, hZ, hZ ▸ hCH⟩

end CFSG.RankThree.Chevalley

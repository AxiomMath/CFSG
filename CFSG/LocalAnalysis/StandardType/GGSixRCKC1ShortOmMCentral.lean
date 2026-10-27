module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMS1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMS2
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.StandardType.RCKC1

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions QuadraticMap
  CFSG.ClassicalGroups.PCoreSection CFSG.Open

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rckSOmM_pCore_le_of_eichler [CharP K 2] [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V))
    (hρ : Function.Injective ρ) (hρΩ : ∀ g, ρ g ∈ omegaGroup Q hQ)
    (hE : ∀ u w, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ ρ.range) {e w : V} (he : Q e = 0)
    (he0 : e ≠ 0) (hew : polar Q e w = 0) (hw : Q w ≠ 0) {x : G} (hx : ρ x = eichler Q e w) :
    pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) ≤ (rootGroup Q e).comap ρ := by
  intro t ht
  rw [Subgroup.mem_comap]
  have hρO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g => omegaGroup_le Q hQ (hρΩ g)
  have hcomm : ∀ t' ∈ Subgroup.centralizer ({x} : Set G), ∀ y,
      ρ t' (eichler Q e w y) = eichler Q e w (ρ t' y) := by
    intro t' ht' y
    have h1 : t' * x = x * t' := Subgroup.mem_centralizer_singleton_iff.mp ht'
    have h2 := congrArg (fun g => ρ g y) h1
    simp only [map_mul, LinearEquiv.mul_apply, hx] at h2
    exact h2
  have hfix : ∀ t' ∈ Subgroup.centralizer ({x} : Set G),
      ρ t' e = e ∧ ∃ a : K, ρ t' (w + Q w • e) = (w + Q w • e) + a • e :=
    fun t' ht' => rckSOmM1_commute_fixes hQ he hew hw he0 (hρO t') (hcomm t' ht')
  have hperp := rckSOmM2_pCore_perp hQ ρ hρ hρO hE he he0 hew hw hx hfix ht
  have htS : t ∈ Subgroup.centralizer ({x} : Set G) := pCoreOf_le 2 _ ht
  exact rckSOmMR_mem_rootGroup hQ he he0 hew hw (hρΩ t) (hfix t htS).1 (hcomm t htS) hperp

end General

variable {K : Type} [Field K] {b c : K}

theorem rckSOmM_pCore_le [Finite K] [CharP K 2] (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) {m : ℕ}
    (hm : 3 ≤ m) {i : Fin (m - 1)} {s : Bool} {p : Fin 2 → K} (hp : p ≠ 0) :
    pCoreOf 2 (Subgroup.centralizer
        ({twShortRoot m hirr i s (.ofAdd p)} : Set (spinGroup (quadMinus m K b c)))) ≤
      (rootGroup (quadMinus m K b c) (minusVec m i s)).comap
        (spinAction (quadMinus m K b c)) := by
  have hQ : (polarBilin (quadMinus m K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  refine rckSOmM_pCore_le_of_eichler hQ (spinAction (quadMinus m K b c))
    (rckSOmM_spinAction_injective hirr) ?_ ?_ (quadMinus_minusVec m b c i s) ?_
    (polar_minusVec_planeVec m b c i s p) ?_
    (rckSOmM_spinAction_twShortRoot_eq_eichler hirr i s p)
  · intro g
    have hle : (spinAction (quadMinus m K b c)).range ≤ elementaryGroup (quadMinus m K b c) :=
      range_spinAction_le_elementaryGroup hQ
        (minusPair_orth (n := m) (K := K) (b := b) (c := c) (i := ⟨0, by omega⟩)
          (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
    exact elementaryGroup_le_omegaGroup hQ (hle ⟨g, rfl⟩)
  · intro u w hu huw
    refine eichler_mem_range_spinAction hQ ?_ hu huw
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  · intro h
    have h1 := polar_minusVec_minusVec m b c i i s (!s)
    have h2 : i = i ∧ s = !!s := ⟨rfl, by rw [Bool.not_not]⟩
    rw [if_pos h2, h, polar_zero_left] at h1
    exact zero_ne_one h1
  · rw [quadMinus_planeVec']
    exact planeNorm_ne_zero hirr hp

end CFSG.StandardType.RCKC1

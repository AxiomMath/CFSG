module

import CFSG.LocalAnalysis.UniquenessCase.K340.Lambda
import CFSG.LocalAnalysis.UniquenessCase.K340.Trivial
import CFSG.LocalAnalysis.UniquenessCase.K340.Setting
import CFSG.LocalAnalysis.UniquenessCase.K340.SeedVariant
import CFSG.LocalAnalysis.UniquenessCase.K340.Closure
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.TheoremA
public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

private theorem theoremA_pointwise {H T X : Subgroup G} {k : Type} [Field k] [Finite k]
    {ρ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) k}
    {ψ : Ecore ↥H →* Multiplicative (Fin 2 → k)}
    (P : Sylow 2 ↥H) (hP : (P : Subgroup ↥H).map H.subtype = T)
    (hseed : IsSeed P ρ (Ecore ↥H) ψ)
    (hΛ : CFSG.QuasithinUnique.Setup.CampbellJ.LamHyp P (lam P hP X))
    (hXN : X ≤ Subgroup.normalizer (thompsonJ T : Set G))
    (hFJ' : omegaOneZJ (CFSG.Open.pCoreOf 2 H) ≤ thompsonJ T) :
    ∀ x ∈ X, ⁅thompsonJ H, (omegaOneZJ (CFSG.Open.pCoreOf 2 H)).map
        (MulAut.conj x).toMonoidHom⁆ ≤ omegaOneZJ (CFSG.Open.pCoreOf 2 H) := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (thompsonJ T : Set G) := hXN hx
  let n : ↥(Subgroup.normalizer (thompsonJ T : Set G)) := ⟨x, hxN⟩
  have hnX : n ∈ X.subgroupOf (Subgroup.normalizer (thompsonJ T : Set G)) := hx
  let β : MulAut ↥(CFSG.Quasithin.thompsonJ (P : Subgroup ↥H)) :=
    MulAut.congr (jEquiv P hP).symm ((thompsonJ T).normalizerMonoidHom n)
  have hβ : β ∈ lam P hP X := Subgroup.mem_map.mpr ⟨n, hnX, rfl⟩
  have hA := CFSG.QuasithinUnique.Setup.CampbellJ.theoremA_J hseed hΛ hβ
  have hm := Subgroup.map_mono (f := H.subtype) hA
  rw [Subgroup.map_commutator, map_Hone P hP, map_aimg_lam P hP hxN (Fcore ↥H),
    map_Fcore] at hm
  rwa [inf_eq_left.mpr hFJ'] at hm

private theorem left_of_commutator_eq_bot {H L T F V X : Subgroup G} {n : ℕ}
    (hF : Fstar H = CFSG.Open.pCoreOf 2 H) (hL : L = CFSG.Quasithin.opResidual 2 H)
    (hL2 : IsL2 (Bar2 L) n) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hH : H = T ⊔ L)
    (hTLQ : T ≤ L ⊔ CFSG.Open.pCoreOf 2 H)
    (hZ : ¬ CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ (Subgroup.center ↥H).map H.subtype)
    (hFdef : F = omegaOneZJ (CFSG.Open.pCoreOf 2 H))
    (hVdef : V = ⁅L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆)
    (hFJ : F ≤ thompsonJ T)
    (hXN : X ≤ Subgroup.normalizer (thompsonJ T : Set G)) (hXJ : thompsonJ H ⊓ T ≤ X)
    (hcomm : ∀ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ = ⊥) :
    thompsonJ H ≤ Subgroup.normalizer (conjClosure X F : Set G) := by
  rw [hFdef]
  by_cases hJQ : thompsonJ T ≤ CFSG.Open.pCoreOf 2 H
  · exact first_of_thompsonJ_le_pCoreOf hT hJQ hXN
  · obtain ⟨k, hk, hkfin, hkchar, π, P, hP, hset⟩ :=
      exists_seedSetting hF hL hL2 hT hH hTLQ
    letI : Field k := hk
    letI : Finite k := hkfin
    letI : CharP k 2 := hkchar
    have hnc : ⁅(⊤ : Subgroup ↥H),
        CFSG.Open.quasithinOmegaOneCenter (P : Subgroup ↥H)⁆ ≠ ⊥ :=
      hnc_of_not_le_center P hP hZ
    have hJT : ¬ CFSG.Quasithin.thompsonJ (P : Subgroup ↥H) ≤ CFSG.pCore 2 ↥H :=
      not_thompsonJ_le_pCore_of P hP hJQ
    obtain ⟨k', hk'f, hk'fin, ρ, ψ, hseed⟩ :=
      exists_isSeed_of_setting' (G := ↥H) hset hnc hJT P rfl
    letI : Field k' := hk'f
    letI : Finite k' := hk'fin
    have hΛ := lamHyp_of P hP hseed hVdef hL hXN hXJ hcomm
    have hFJ' : omegaOneZJ (CFSG.Open.pCoreOf 2 H) ≤ thompsonJ T := by
      rwa [hFdef] at hFJ
    exact le_normalizer_conjClosure_of_commutator_le
      (theoremA_pointwise P hP hseed hΛ hXN hFJ')

theorem campbell_theoremA {H L T F V X : Subgroup G} {n : ℕ}
    (hF : Fstar H = CFSG.Open.pCoreOf 2 H) (hL : L = CFSG.Quasithin.opResidual 2 H)
    (hL2 : IsL2 (Bar2 L) n) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H) (hH : H = T ⊔ L)
    (hTLQ : T ≤ L ⊔ CFSG.Open.pCoreOf 2 H)
    (hZ : ¬ CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ (Subgroup.center ↥H).map H.subtype)
    (hFdef : F = omegaOneZJ (CFSG.Open.pCoreOf 2 H))
    (hVdef : V = ⁅L, CFSG.RankThree.PartOne.omegaOneCenterIn (CFSG.Open.pCoreOf 2 H)⁆)
    (hFJ : F ≤ thompsonJ T) (_hVJ : V ≤ thompsonJ T)
    (hXN : X ≤ Subgroup.normalizer (thompsonJ T : Set G)) (hXJ : thompsonJ H ⊓ T ≤ X) :
    thompsonJ H ≤ Subgroup.normalizer (conjClosure X F : Set G) ∨
      ∃ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ ≠ ⊥ := by
  by_cases hcomm : ∃ a ∈ X, ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ ≠ ⊥
  · exact Or.inr hcomm
  · left
    push Not at hcomm
    exact left_of_commutator_eq_bot hF hL hL2 hT hH hTLQ hZ hFdef hVdef hFJ hXN hXJ hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.Campbell340

end

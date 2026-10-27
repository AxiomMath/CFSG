module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIRows
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIExcTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.RootTw

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.K155X (excTw_frob_root excTw_exists_fieldActor_of_mem_markField
  excTwE6_exists_twConj_of_mem_markID excTwE6_orderOf_fieldActor excTwE6_fix_of_commute
  excTwE6_coe_fieldActor_mul)


theorem kgFieldRestrictionCont_twE6 {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) :
    KGFieldRestrictionCont p (LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (RecipeExcLang.markIDImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ)) := by
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := n * 2) (by rw [hK, ← pow_mul])
  have hOneModel := kgfniTw_hOne_model (t := TwistTag.E6) hp hp2 hn hK σ hσ
  intro f hf hord h hh hhp hcomm J₀ hJ₀ f' hf'
  by_cases hh1 : h = 1
  · exact hOneModel f hf hord h hh hhp hcomm hh1 J₀ hJ₀ f' hf'
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    Finite.of_injective
      (Subtype.val : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) → ModGL TwistTag.E6.tag K)
      Subtype.val_injective
  obtain ⟨w, hw⟩ := excTwE6_exists_twConj_of_mem_markID σ hh
  obtain ⟨δ, hδ⟩ := excTw_exists_fieldActor_of_mem_markField (t := TwistTag.E6) σ hf
  have hδp : orderOf δ = p := by
    rw [← excTwE6_orderOf_fieldActor hn hK σ hσ δ, ← hδ, MulEquiv.orderOf_eq, hord]
  have hp2' : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  obtain ⟨e, k, T, hep, he1, hT, hk, -⟩ := excTw_frob_root (m := 2) (a := 1) hp
    (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)) hn (by norm_num) hK σ hσ
    (by omega) δ hδp
  rw [pow_one] at hk
  have hfk : MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      (f ^ k) = fieldActor σ (σ * T) := by
    rw [map_pow, hδ, ← hk]
    exact (map_pow (fieldActorHom (t := TwistTag.E6) σ) δ k).symm
  have hcommk : h * f ^ k = f ^ k * h := (Commute.pow_right (show Commute h f from hcomm) k).eq
  have hcomm' : RecipeExcLang.twConj K σ w * fieldActor σ (σ * T) =
      fieldActor σ (σ * T) * RecipeExcLang.twConj K σ w := by
    have h1 := congrArg (MulAut.congr
      (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))) hcommk
    rw [map_mul, map_mul, hw, hfk] at h1
    exact h1
  have hfix := excTwE6_fix_of_commute hn hK σ hσ (σ * T) w hcomm'
  have hwp : w ^ p = 1 := by
    apply NoOffTwE6Three.twConj_injective hn hK σ hσ
    rw [map_pow, map_one, ← hw, ← map_pow, hhp, map_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hh1
    apply (MulAut.congr
      (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))).injective
    rw [hw, map_one, map_one]
  have hfix' : diagramMap TwistTag.E6 K * Units.map (entrywiseHom T.toRingHom)
      (w : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ =
        (w : ModGL TwistTag.E6.tag K) := by
    have h1 := congrArg Subtype.val hfix
    rw [RecipeExcLang.coe_twInndiagFieldAut] at h1
    rw [RecipeExcLang.diagramMap_conj_E6 hK hσ (RecipeExcLang.entrywise_mem_twInndiag T w.2),
      units_map_entrywiseHom_comp]
    exact h1
  have hKe : Nat.card K = (2 ^ (e * p)) ^ 2 := by rw [hep]; exact hK
  have hσe : ∀ c, σ c = c ^ (2 ^ (e * p)) := by rw [hep]; exact hσ
  obtain ⟨SL, Rt, a, ι, -, hq0, hTa, hap, ha1, hfa, hι, hrange, hβ, hφ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_frobRoot_twE6
      hp hp2 he1 hKe σ hσe T.toRingHom (fun c => hT c) (RecipeExcLang.twConj K σ w)
      (fieldActor σ (σ * T)) (w : ModGL TwistTag.E6.tag K)
      (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2)
      (fun c => RecipeExcLang.coe_twConj σ w c)
      (fun c => excTwE6_coe_fieldActor_mul hn hK σ hσ T c)
      (by rw [← Subgroup.coe_pow, hwp]; rfl) (fun h1 => hw1 (Subtype.ext h1)) hfix'
  exact kgFieldRestriction_of_langSetup hp hp2
    (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)) k SL Rt he1 hq0
    hTa hap ha1 hfa ι hι hrange (fun c => by rw [hw]; exact hβ c)
    (fun c => by rw [hfk]; exact hφ c) J₀ hJ₀ f' hf'

theorem kgFieldRestrictionOn_e6 : KGFieldRestrictionOn (kgfniRow .e6) := by
  intro p lab hp hp2 hlab _ht3 hrow
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨htag, hdvd⟩ := hrow
  simp only [KGFNIFamily.tagCase] at htag
  rcases htag with rfl | rfl
  · exact kgFieldRestrictionOn_of_excUntw_model (τ := .E6) (n := n)
      (lab := ⟨LargeEvenLieTag.E6, r, n⟩) hp hp2 (Or.inr (Or.inr (Or.inl rfl)))
      (le_trans hp.two_le (Nat.le_of_dvd hlab.1 hdvd)) hlab rfl rfl
  · exact kgFieldRestrictionOn_of_excTw_model (t := TwistTag.E6) hlab rfl fun K _ _ σ hK hσ =>
      kgFieldRestrictionCont_twE6 hp hp2 hlab.1 hK σ hσ

end CFSG.StandardType

end

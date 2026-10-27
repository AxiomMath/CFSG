module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1Core
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Core
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem ggNbrLSideRSExc_u1_twE6 :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
      GGNbrLSideRSExcTransport Tag.E6
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K
          (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) (2 ^ n) := by
  intro K _ _ n hn hK φ hφI ψ hψI hφ1 hφ3 hψ3 hcomm
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  obtain ⟨w, hw⟩ := (hε φ).2 hφI
  obtain ⟨w', hw'⟩ := (hε ψ).2 hψI
  set L := AlgebraicClosure K with hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  set u : ModGL TwistTag.E6.tag L :=
    baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K) with hu
  set u' : ModGL TwistTag.E6.tag L :=
    baseChangeGL (algebraMap K L) (w' : ModGL TwistTag.E6.tag K) with hu'
  set ι₀ : TwE6Delta.RecipeR K n →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp
      ((twistedE6RootGroup K σ).subtype.comp ε.symm.toMonoidHom) with hι₀def
  have hw3 : w ^ 3 = 1 := by
    apply TwE6Transport.recipeConj_injective σ ε hn hK hσ
    rw [map_pow, hw, hφ3, map_one]
  have hw'3 : w' ^ 3 = 1 := by
    apply TwE6Transport.recipeConj_injective σ ε hn hK hσ
    rw [map_pow, hw', hψ3, map_one]
  have hww' : w * w' = w' * w := by
    apply TwE6Transport.recipeConj_injective σ ε hn hK hσ
    rw [map_mul, map_mul, hw, hw', hcomm]
  have hw1 : w ≠ 1 := by
    intro h1
    apply hφ1
    rw [← hw, h1, map_one]
  have hw3M : (w : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hw3]
    rfl
  have hw'3M : (w' : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hw'3]
    rfl
  have hww'' : (w : ModGL TwistTag.E6.tag K) * w' = (w' : ModGL TwistTag.E6.tag K) * w := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hww']
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← map_pow (baseChangeGL (algebraMap K L)), hw3M, map_one]
  have hu'3 : u' ^ 3 = 1 := by
    rw [hu', ← map_pow (baseChangeGL (algebraMap K L)), hw'3M, map_one]
  have hcomm' : u * u' = u' * u := by
    rw [hu, hu', ← map_mul (baseChangeGL (algebraMap K L)),
      ← map_mul (baseChangeGL (algebraMap K L)), hww'']
  have hufix : u ∈ Blueprint.twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 n) := by
    rw [hu]
    exact map_twistedE6InndiagGL_le_twistedFixedGroup (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ
      (Fr := iterateFrobenius L 2 n) (fun c => iterateFrobenius_def 2 n c)
      (Subgroup.mem_map_of_mem _
        (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2))
  have hu'fix : u' ∈ Blueprint.twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 n) := by
    rw [hu']
    exact map_twistedE6InndiagGL_le_twistedFixedGroup (ℓ := 2) (f := n) Nat.prime_two hn hK σ hσ
      (Fr := iterateFrobenius L 2 n) (fun c => iterateFrobenius_def 2 n c)
      (Subgroup.mem_map_of_mem _
        (NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w'.2))
  have huG : u ∈ adjointGroup TwistTag.E6.tag L :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 L (iterateFrobenius L 2 n) hufix
  have hu'G : u' ∈ adjointGroup TwistTag.E6.tag L :=
    twistedFixedGroup_le_adjointGroup TwistTag.E6 L (iterateFrobenius L 2 n) hu'fix
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h1
    exact hw1 (Subtype.ext (baseChangeGL_injective (algebraMap K L) (by simpa using h1)))
  have hconj : ∃ g ∈ adjointGroup TwistTag.E6.tag L, g⁻¹ * u * g ∈ torusGroup TwistTag.E6.tag L :=
    exists_conj_torusGroup_of_pow_eq_one (τ := TwistTag.E6.tag) (p := 3) Nat.prime_three
      monomialToralAt_E6_three (ℓ := 2) (by norm_num)
      (isAlgebraic_zmod_algebraicClosure_of_finite K 2) huG hu3
  obtain ⟨D, hΦ, hDq, hmem⟩ :=
    exists_langDatum_of_toral_twisted TwistTag.E6 (ℓ := 2) n hn hufix.2 hconj
  have hfin : Finite D.model :=
    finite_model_twistedE6 (ℓ := 2) (f := n) Nat.prime_two hn hK hσ
      (Fr := iterateFrobenius L 2 n) (fun c => iterateFrobenius_def 2 n c) D hΦ
  have hι₀range : ι₀.range = (twistedE6RootGroup K σ).map (baseChangeGL (algebraMap K L)) := by
    rw [hι₀def,
      MonoidHom.range_comp (baseChangeGL (algebraMap K L))
        ((twistedE6RootGroup K σ).subtype.comp ε.symm.toMonoidHom),
      MonoidHom.range_comp (twistedE6RootGroup K σ).subtype ε.symm.toMonoidHom,
      MonoidHom.range_eq_top.2 (MulEquiv.surjective ε.symm), Subgroup.map_top,
      Subgroup.range_subtype]
  have hι₀inj : Function.Injective ι₀ := by
    rw [hι₀def]
    exact (baseChangeGL_injective (algebraMap K L)).comp
      ((Subgroup.subtype_injective _).comp (MulEquiv.injective ε.symm))
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [hι₀range]
    exact Γ_eq_map_twistedE6RootGroup (ℓ := 2) (f := n) Nat.prime_two hn hK hσ
      (Fr := iterateFrobenius L 2 n) (fun c => iterateFrobenius_def 2 n c) D hΦ
  have hι₀ε : ∀ x : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ι₀ (ε x) = baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K) := by
    intro x
    rw [hι₀def]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    have hx : ε.symm.toMonoidHom (ε x) = x := by
      change ε.symm (ε x) = x
      exact MulEquiv.symm_apply_apply ε x
    rw [hx]
  have hι₀apply : ∀ c : TwE6Delta.RecipeR K n,
      ι₀ c = baseChangeGL (algebraMap K L) (ε.symm c : ModGL TwistTag.E6.tag K) := by
    intro c
    rw [hι₀def]
    rfl
  have hφ_ind : ∀ c, ι₀ (φ c) = u * ι₀ c * u⁻¹ := by
    intro c
    calc ι₀ (φ c) = ι₀ (ε (RecipeExcLang.twConj K σ w (ε.symm c))) := by
          rw [← hw, TwE6Transport.recipeConj_apply]
      _ = baseChangeGL (algebraMap K L)
            (RecipeExcLang.twConj K σ w (ε.symm c)) := hι₀ε _
      _ = baseChangeGL (algebraMap K L)
            ((w : ModGL TwistTag.E6.tag K) * (ε.symm c : ModGL TwistTag.E6.tag K) *
              (w : ModGL TwistTag.E6.tag K)⁻¹) := by rw [RecipeExcLang.coe_twConj]
      _ = u * ι₀ c * u⁻¹ := by rw [hu, hι₀apply, map_mul, map_mul, map_inv]
  have hψ_ind : ∀ c, ι₀ (ψ c) = u' * ι₀ c * u'⁻¹ := by
    intro c
    calc ι₀ (ψ c) = ι₀ (ε (RecipeExcLang.twConj K σ w' (ε.symm c))) := by
          rw [← hw', TwE6Transport.recipeConj_apply]
      _ = baseChangeGL (algebraMap K L)
            (RecipeExcLang.twConj K σ w' (ε.symm c)) := hι₀ε _
      _ = baseChangeGL (algebraMap K L)
            ((w' : ModGL TwistTag.E6.tag K) * (ε.symm c : ModGL TwistTag.E6.tag K) *
              (w' : ModGL TwistTag.E6.tag K)⁻¹) := by rw [RecipeExcLang.coe_twConj]
      _ = u' * ι₀ c * u'⁻¹ := by rw [hu', hι₀apply, map_mul, map_mul, map_inv]
  have hu'Φ : D.Φ u' = u' := by
    rw [hΦ]
    exact hu'fix.2
  obtain ⟨S, a, e, y, hSq, hT, hap, ha1, hy, hyc, hy3, heφ, heψ⟩ :=
    ggNbrLSideRSExc_transport_of_datum (τ := TwistTag.E6.tag) hn D hDq Nat.prime_five
      (by norm_num) (Or.inl le_rfl) hfin ι₀ hι₀inj hΓ φ ψ hφ_ind hψ_ind hmem hu3 hu1 hu'G hu'Φ
      hu'3 hcomm'
  exact ⟨L, inferInstance, inferInstance, 5, S, a, e, y, CharP.cast_eq_zero L 2, hSq, hT, hap,
    ha1, hy, hyc, hy3, heφ, heψ⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeGen
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeExt
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldCoreDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoroot

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6RootAs
  CFSG.StandardType.TwE6RootKill

section Local


theorem exists_coroot_data_of_two_local (hRK : RootKill)
    (hD34 : TwE6FieldCore.SubfieldLangDatumThreeFour) (hGen : TwE6CorootCoreGen)
    (hOut : TwE6OuterRankFour) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) (hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥)
    (hodd : ∀ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ k : ℕ, φ ^ 2 ^ k = 1 →
      φ ∈ (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
        MulAut ↥(twistedE6RootGroup K σ)).range)
    {Y : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hY : IsElemAbelian 3 Y)
    (hYI : Y ≤ (RecipeExcLang.twConj K σ).range) (hYc : Nat.card Y = 3 ^ 4)
    {V : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hYV : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V) :
    ∃ τ ∈ Y, τ ≠ 1 ∧ ∃ X D' : Subgroup ↥(twistedE6RootGroup K σ), ggFix τ = X ⊔ D' ∧
      IsCyclic X ∧ X ≤ Subgroup.centralizer (D' : Set ↥(twistedE6RootGroup K σ)) ∧
      CFSG.IsQuasisimple D' ∧ 7 ∣ Nat.card D' ∧
      ∀ y ∈ Y, (∀ d ∈ D', y d = d) → ∃ d ∈ X, y = MulAut.conj d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have h2 : ringChar K = 2 := ringChar.eq K 2
  have hAI : twMatPre K σ Y ≤ twistedE6InndiagGL K σ := twMatPre_le σ Y
  have hAel : IsElemAbelian 3 (twMatPre K σ Y) := isElemAbelian_twMatPre σ hn hK hσ hY
  have hAc : Nat.card (twMatPre K σ Y) = 3 ^ 4 := (card_twMatPre σ hn hK hσ hYI).trans hYc
  have hnorm : ∀ a : ↥(twistedE6InndiagGL K σ), (a : ModGL TwistTag.E6.tag K) ∈ twMatPre K σ Y →
      ∀ u ∈ V, twistedE6InndiagConj K σ a * u * (twistedE6InndiagConj K σ a)⁻¹ ∈ V := by
    rintro ⟨a, ha⟩ haA u hu
    obtain ⟨hw, hwY⟩ := (mem_twMatPre σ).1 haA
    rw [twistedE6InndiagConj_eq_twConj σ ⟨a, hw⟩ ha]
    exact hYV _ hwY u hu
  obtain ⟨D, γ, hγ, ζ, hζ, hζ1, x, hxA, hx⟩ : ∃ D : TwLangData K σ (2 ^ n) (twMatPre K σ Y),
      ∃ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ ∧
        ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ ∃ x ∈ twMatPre K σ Y,
          rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) =
            D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x * D.g0 := by
    by_cases hV : ∀ u ∈ V, u ∈ (twistedE6InndiagConj K σ).range → u = 1
    ·
      obtain ⟨D, -, γ, hγ, ζ, hζ, hζ1, x, hxA, hx⟩ := hOut K σ (2 ^ n) hK hσ h2 h3 _ hAI hAel hAc
        ⟨V, hV1, hV2, hV, hnorm⟩
      exact ⟨D, γ, hγ, ζ, hζ, hζ1, x, hxA, hx⟩
    ·
      push Not at hV
      obtain ⟨u, huV, huR, hu1⟩ := hV
      have hV₁1 : V ⊓ (RecipeExcLang.twConj K σ).range ≠ ⊥ := fun h => hu1 (by
        have hu' : u ∈ V ⊓ (RecipeExcLang.twConj K σ).range :=
          ⟨huV, range_twistedE6InndiagConj_le σ huR⟩
        rw [h] at hu'
        exact hu')
      have hV₁2 : IsPGroup 2 ↥(V ⊓ (RecipeExcLang.twConj K σ).range) := hV2.to_le inf_le_left
      have hV₁I : V ⊓ (RecipeExcLang.twConj K σ).range ≤ (MulAut.conj : ↥(twistedE6RootGroup K σ) →*
          MulAut ↥(twistedE6RootGroup K σ)).range := fun φ hφ => by
        obtain ⟨k, hk⟩ := hV2 ⟨φ, hφ.1⟩
        exact hodd φ hφ.2 k (congrArg Subtype.val hk)
      have hV₁N : ∀ y ∈ Y, ∀ v ∈ V ⊓ (RecipeExcLang.twConj K σ).range,
          y * v * y⁻¹ ∈ V ⊓ (RecipeExcLang.twConj K σ).range := fun y hy v hv =>
        ⟨hYV y hy v hv.1,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hYI hy) hv.2) (Subgroup.inv_mem _ (hYI hy))⟩
      have hU : TwNormTwo K σ (twMatPre K σ Y) := twNormTwo_of_inner σ hZ hV₁1 hV₁2 hV₁I hV₁N
      obtain ⟨K₃, _, _, ι, σ₃, hK₃, hσ₃, hcomm⟩ := exists_cubic_ext hK h2 σ hσ
      obtain ⟨D, hc⟩ := hD34 K K₃ ι σ σ₃ (2 ^ n) hK hK₃ hσ hσ₃ h2 h3 _ hAI hAel hAc
        (twNormTwo_baseChange ι σ σ₃ hcomm hU)
      obtain ⟨β, hβ, hkill⟩ := hRK K σ (2 ^ n) hK hσ h2 3 Nat.prime_three h3 _ hAI hAel
        (by rw [if_pos rfl, hAc]) hU D
      obtain ⟨γ, hγ, -, ζ, hζ, hζ1, x, hxA, hx⟩ := exists_corootTuple_mem_of_kills D
        Nat.prime_three (by rw [h2]; norm_num) hAel (by rw [hAc]; norm_num) hβ hkill
      refine ⟨D, γ, hγ, ζ, hζ, hζ1, x, hxA, ?_⟩
      rwa [hc, one_mul, inv_one, mul_one] at hx
  exact exists_coroot_data_of_datum hGen hn hK σ hσ h3 hY hYI D hγ hζ hζ1 hxA hx

end Local

end CFSG.StandardType.TwE6EndNode3

end

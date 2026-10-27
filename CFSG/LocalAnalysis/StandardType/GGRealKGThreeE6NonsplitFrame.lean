module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exists_excFrame_of_coordinates {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : E6QPlusThreeFrame K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL .E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * eqpN (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (hFrζ : Units.map Fr.toMonoidHom ζ = ζ ^ 2)
    (hcoord : ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.frame s : ModGL .E6 K) = g0 * e6ThreeDiag ζ hζ s * g0⁻¹) :
    ∃ F : ExcFrame .E6 K 3 D.frame.range,
      F.w = e6W0 ∧ F.D.g0 = g0 ∧
      F.D.Φ = Units.map (entrywiseHom Fr) := by
  classical
  let F : LangDatum .E6 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr e6W0 hg0C hg0
  refine ⟨⟨F, e6W0, rfl, ⟨Fr, hFr, fun _ => rfl⟩, rfl, ?_⟩, rfl, rfl, rfl⟩
  intro x
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_pow, CFSG.RankThree.CentralCover.pow_eq_one_of_zmod, map_one]
    · change g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.frame s : ModGL .E6 K) * g0 ∈
        twistedTorusOf (eqpN (AlgebraicClosure K)) (Units.map (entrywiseHom Fr))
      rw [hcoord s]
      have heq : g0⁻¹ * (g0 * e6ThreeDiag ζ hζ s * g0⁻¹) * g0 =
          e6ThreeDiag ζ hζ s := by group
      rw [heq, mem_twistedTorusOf_iff_negPhi]
      refine ⟨?_, negPhi_eqpN_e6ThreeDiag Fr hζ hFrζ s⟩
      exact rootDiagUnit_mem_torusGroup _
  · rintro ⟨hx3, hxtor⟩
    let y := g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL .E6 K) * g0
    have hy3 : y ^ 3 = 1 := by
      have hxM : (x : ModGL .E6 K) ^ 3 = 1 := congrArg Subtype.val hx3
      dsimp [y]
      conv_lhs => arg 1; arg 2; rw [← inv_inv g0]
      rw [conj_pow, ← map_pow, hxM, map_one]
      group
    obtain ⟨s, hs⟩ := exists_e6ThreeDiag_eq Fr hζo hζ hFrζ hxtor hy3
    refine ⟨s, ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    rw [hcoord s, hs]
    change g0 * (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL .E6 K) * g0) * g0⁻¹ = _
    group

theorem exists_e6QPlusThreeFrame_excFrame {K : Type} [Field K] [Finite K] [CharP K 2]
    (h3 : 3 ∣ Nat.card K + 1) :
    ∃ (D : E6QPlusThreeFrame K) (F : ExcFrame .E6 K 3 D.frame.range)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ζ : (AlgebraicClosure K)ˣ)
      (hζ : ζ ^ 3 = 1),
      F.w = e6W0 ∧ (∀ c, Fr c = c ^ Nat.card K) ∧
      F.D.Φ = Units.map (entrywiseHom Fr) ∧ orderOf ζ = 3 ∧
      Units.map Fr.toMonoidHom ζ = ζ ^ 2 ∧ Function.Surjective D.weyl ∧
      ∀ s, baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.frame s : ModGL .E6 K) =
        F.D.g0 * e6ThreeDiag ζ hζ s * F.D.g0⁻¹ := by
  obtain ⟨Fr, g0, ζ, hζ, D, hFr, hg0C, hg0, hζo, hFrζ, hsurj, hcoord⟩ :=
    exists_e6QPlusThreeFrame_with_coordinates h3
  obtain ⟨F, hw, hg, hΦ⟩ := exists_excFrame_of_coordinates D hFr hg0C hg0 hζ hζo hFrζ hcoord
  exact ⟨D, F, Fr, ζ, hζ, hw, hFr, hΦ, hζo, hFrζ, hsurj, hg.symm ▸ hcoord⟩

end CFSG.StandardType.ExcFrames.E6QPlusThree

end

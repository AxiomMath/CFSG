module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenLang
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenInvol
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenGraph
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenF4
import CFSG.LocalAnalysis.StandardType.GGTwE6OuterGenCoord

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem twE6OuterRankFour_of_coord
    (hCoord : ∀ {K : Type} [Field K] [Finite K] {Y : Subgroup (ModGL TwistTag.E6.tag K)},
      IsElemAbelian 3 Y → Nat.card Y = 3 ^ 4 → ∀ {N : ModGL TwistTag.E6.tag K},
      (∀ x ∈ Y, N * x * N⁻¹ ∈ torusGroup TwistTag.E6.tag K ∧
        diagramMap TwistTag.E6 K * (N * x * N⁻¹) = N * x * N⁻¹ * diagramMap TwistTag.E6 K) →
      ∀ {ζ : Kˣ}, ζ ^ 3 = 1 → ∃ x ∈ Y, N * x * N⁻¹ = rootDiagUnit TwistTag.E6.tag
        (corootTuple (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) ζ)) :
    TwE6OuterRankFour := by
  intro K _ _ σ q hK hσ h2 h3q A hAI hel hcard hU
  obtain ⟨U, hU1, hU2, hUI, hAU⟩ := hU
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := ringChar.of_eq h2
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hdvd : q ∣ 2 ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hf : 1 ≤ f := Nat.pos_of_ne_zero (by rintro rfl; norm_num at h3q)
  obtain ⟨t, -, ht2, htI, htc⟩ :=
    TwE6OuterGen.exists_outer_involution_commute Nat.prime_two hf hK σ hσ hU1 hU2 hUI
  have hxt : ∀ x (hx : x ∈ A), twistedE6InndiagConj K σ ⟨x, hAI hx⟩ * t =
      t * twistedE6InndiagConj K σ ⟨x, hAI hx⟩ := fun x hx =>
    htc _ ⟨_, rfl⟩ (hAU ⟨x, hAI hx⟩ hx)
  have hAC : ∀ x (hx : x ∈ A), x ∈ twistedE6RootGroup K σ := fun x hx =>
    TwE6OuterGen.coe_mem_of_conj_mem_range Nat.prime_two hf hK σ hσ (a := ⟨x, hAI hx⟩)
      (TwE6OuterGen.mem_range_conj_of_commute_outer hf hK σ hσ ht2 htI ⟨_, rfl⟩ (hxt x hx).symm)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  have htfix : ∀ x (hx : x ∈ A), t ⟨x, hAC x hx⟩ = ⟨x, hAC x hx⟩ := fun x hx => by
    have he : twistedE6InndiagConj K σ ⟨x, hAI hx⟩ = MulAut.conj ⟨x, hAC x hx⟩ :=
      MulEquiv.ext fun _ => Subtype.ext rfl
    exact TwE6OuterGen.apply_eq_self_of_commute_conj hZ (by rw [← he]; exact (hxt x hx).symm)
  obtain ⟨⟨c, hcI⟩, hcP⟩ := TwE6OuterGen.exists_inndiag_diagramMap_commute hf hK σ hσ ht2 htI
  have hYΓ : A.map (MulAut.conj c).toMonoidHom ≤
      twistedFixedGroup TwistTag.E6 K (RingHom.id K) := by
    rintro _ ⟨x, hx, rfl⟩
    have hC := (twistedE6InndiagConj K σ ⟨c, hcI⟩ ⟨x, hAC x hx⟩).2
    exact mem_twistedFixedGroup_id_iff.2 ⟨twistedFixedGroup_le_adjointGroup _ _ _
      (graphFixedRootGroup_le _ _ _ hC), hcP ⟨x, hAC x hx⟩ (htfix x hx)⟩
  have h3 : 3 ∣ Nat.card K - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 f
    rw [one_pow] at h
    rw [hK, ← pow_mul, mul_comm f 2, pow_mul]
    exact h
  obtain ⟨g, hgΓ, hgT⟩ := TwE6OuterGen.exists_conj_mem_torusGroup_of_le h3 hYΓ (hel.map _)
    ((Subgroup.card_map_of_injective (MulAut.conj c).injective).trans hcard)
  have hN : ∀ x ∈ A, g * c * x * (g * c)⁻¹ ∈ torusGroup TwistTag.E6.tag K ∧
      diagramMap TwistTag.E6 K * (g * c * x * (g * c)⁻¹) =
        g * c * x * (g * c)⁻¹ * diagramMap TwistTag.E6 K := by
    intro x hx
    have hy : c * x * c⁻¹ ∈ A.map (MulAut.conj c).toMonoidHom := ⟨x, hx, rfl⟩
    rw [show g * c * x * (g * c)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ by group]
    exact ⟨hgT _ hy, (mem_twistedFixedGroup_id_iff.1
      (mul_mem (mul_mem hgΓ (hYΓ hy)) (inv_mem hgΓ))).2⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units]; exact h3)
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  obtain ⟨x₀, hx₀A, hx₀⟩ := hCoord hel hcard hN hζ3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ a, iterateFrobenius (AlgebraicClosure K) 2 f a = a ^ 2 ^ f :=
    fun a => iterateFrobenius_def 2 f a
  have hmapF := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hf hK σ hσ _ hFr
  have hFixL : ∀ y ∈ A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 f) y =
        y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (hmapF (Subgroup.mem_map_of_mem _ (hAI hx)))).2
  have hNL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c) ∈
      adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [map_mul]
    exact mul_mem (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _
      (mem_twistedFixedGroup_id_iff.1 hgΓ).1)
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (hmapF (Subgroup.mem_map_of_mem _ hcI))).1
  have hconjL : ∀ x, (baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c))⁻¹⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c))⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c * x * (g * c)⁻¹) := fun x => by
    simp only [map_mul, map_inv, inv_inv]
  have hgA : ∀ y ∈ A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c))⁻¹⁻¹ * y *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (g * c))⁻¹ ∈
          torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconjL]
    exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup _ (hN x hx).1
  obtain ⟨v, g0, hg0C, hg0, hg0A⟩ :=
    TwE6OuterGen.exists_lang_frame_conj_eq_twisted 2 TwistTag.E6 f hf hFixL (inv_mem hNL) hgA
  have hT : ∀ y ∈ A.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      g0⁻¹ * y * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := fun y hy => by
    rw [hg0A y hy]
    exact hgA y hy
  refine ⟨⟨v, iterateFrobenius (AlgebraicClosure K) 2 f, hFr, g0, hg0C, hg0, 1, one_mem _,
    fun x hx => ?_⟩, rfl, Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ),
    CFSG.Blueprint.Chevalley.isRoot_single _ 1,
    Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ,
    by rw [← map_pow, hζ3, map_one], fun h => ?_, x₀, hx₀A, ?_⟩
  · rw [one_mul, inv_one, mul_one]
    exact mem_lang_torus_of_datum _ hFixL hg0 hT _ (Subgroup.mem_map_of_mem _ hx)
  · have h1 : ζ = 1 :=
      Units.map_injective (f := (algebraMap K (AlgebraicClosure K)).toMonoidHom)
        (algebraMap K (AlgebraicClosure K)).injective (by rw [h, map_one])
    rw [h1, orderOf_one] at hζ
    exact absurd hζ (by norm_num)
  · show _ = g0⁻¹ * _ * g0
    rw [hg0A _ (Subgroup.mem_map_of_mem _ hx₀A), hconjL, hx₀,
      CFSG.LieType.Chevalley.baseChangeGL_rootDiagUnit]
    congr 1
    funext k
    simp only [corootTuple, map_zpow]

theorem twE6OuterRankFour_holds : TwE6OuterRankFour :=
  twE6OuterRankFour_of_coord TwE6OuterGen.exists_mem_conj_eq_corootTuple

end CFSG.StandardType.TwE6RootAs

end

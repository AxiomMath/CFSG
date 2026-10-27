module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)

section Certificates


private theorem le_twoLocalRank_of_torusLift_raw {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) {p r : ℕ} (hp : p.Prime) (hr : 5 ≤ r) {lab : LargeEvenLabel}
    (hraw : LargeEvenRawDatum lab fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R))
    (hall : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p r R) :
    5 ≤ LargeEvenTwoLocalRank p X := by
  have hmain := hall _ hraw
  obtain ⟨R, hRgrp, I, F, ⟨θ⟩, hlift⟩ := largeEvenRawDatum_exists hmain
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    refine ⟨x, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center X) x) = r
    rw [hx]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : θ (QuotientGroup.mk' (Subgroup.center X) x) = 1 := by simpa [ψ] using hx
    have hx'' : QuotientGroup.mk' (Subgroup.center X) x = 1 := θ.injective (by simpa using hx')
    exact (QuotientGroup.eq_one_iff x).mp hx''
  obtain ⟨U, E, hU, hU2, hEU, hE, hEcard, -⟩ := hlift X ψ hψ hker_le hperf
  have hTL : IsTwoLocal (Subgroup.normalizer (U : Set X)) := ⟨U, hU, hU2, rfl⟩
  have hpr : r ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set X)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hEU hE hEcard
  have h5 : 5 ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set X)) := le_trans hr hpr
  exact TableB.le_twoLocalRank hp.one_lt hTL h5

private theorem recipeChevalleyE6_torusLift {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpn : p ∣ 2 ^ n - 1) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false Q) :
    LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGTorusLift p 6 R := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    TableBExc.ggTorusLift_E6 hp hp2 hp3 (by rw [hK]; exact hpn)⟩

private theorem largeEvenLabelAll_torusLift_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {lab : LargeEvenLabel} (htag : lab.tag = .E6) (hpq : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 6 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  exact recipeChevalleyE6_torusLift hp hp2 hp3 hpq hQ

end Certificates

theorem rckExc_E6_floor_pf
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .E6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .E6 n f ψ p G₀ A B₁ D J L R Rm K e) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f - 1) :
    p ^ 5 ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  have hperf : commutator ↥G₀ = ⊤ := hGG.2.2.1
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hc : ChevalleyExceptionalModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 2 f :=
    hGG.2.2.2.chevalleyExceptionalModel (by decide)
  have hrec : LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ f) false
      (fun R _ _ _ => Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R)) :=
    recipeChevalley_of_untwistedChevalleyModel .E6 hc.2
  have hraw : LargeEvenRawDatum (⟨.E6, 0, f⟩ : LargeEvenLabel)
      (fun R _ _ _ => Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R)) := hrec
  have hp3 : p ≠ 3 := by omega
  have hall := largeEvenLabelAll_torusLift_E6 hp hp2 hp3 (lab := ⟨.E6, 0, f⟩) rfl
    (by simpa using hpq)
  have h5 : 5 ≤ LargeEvenTwoLocalRank p ↥G₀ :=
    le_twoLocalRank_of_torusLift_raw hperf hp (by norm_num) hraw hall
  have h5' : 5 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
    h5.trans (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective
      hp (Subgroup.inclusion (le_sup_right : G₀ ≤ A ⊔ G₀))
      (Subgroup.inclusion_injective _))
  calc p ^ 5 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := Nat.pow_le_pow_right hp.pos h5'
    _ ≤ Nat.card A := hrank2

theorem rckExc_twE6_floor_pf
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU .twistedE6 n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig .twistedE6 n f ψ p G₀ A B₁ D J L R Rm K e) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) :
    p ^ 5 ≤ Nat.card A := by
  unfold RCKRPConfig at h
  rcases h with
    ⟨hGG, hOddG0, hp, hp2, hAel, hB1A, hDB1, hDcard, hAnorm, hMarkG0, hB1J, hB1Jc,
      hp4, hA2, hrank2, -⟩
  have hperf : commutator ↥G₀ = ⊤ := hGG.2.2.1
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hc : ChevalleyExceptionalModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 2 f :=
    hGG.2.2.2.chevalleyExceptionalModel (by decide)
  have htw : TwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) .E6 (2 ^ f) := hc.2
  have hrec : LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 f
      (fun R _ _ _ => Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R)) :=
    recipeTwisted_of_twistedChevalleyModel .E6 htw
  have hraw : LargeEvenRawDatum (⟨.twE6, 0, f⟩ : LargeEvenLabel)
      (fun R _ _ _ => Nonempty (↥G₀ ⧸ Subgroup.center ↥G₀ ≃* R)) := hrec
  have hΛ : LargeEvenInLambda2 (⟨.twE6, 0, f⟩ : LargeEvenLabel) := ⟨hf, rfl⟩
  have hp3 : p ≠ 3 := by omega
  have hall' := largeEvenLabelAll_torusLift_twE6Add_holds (p := p) hp hΛ
    ⟨rfl, by simpa using hpq⟩
  have hall : LargeEvenLabelAll (⟨.twE6, 0, f⟩ : LargeEvenLabel)
      fun R _ _ _ => GGTorusLift p 5 R := by
    simpa [TwE6Delta.liftRank_of_ne hp3] using hall'
  have h5 : 5 ≤ LargeEvenTwoLocalRank p ↥G₀ :=
    le_twoLocalRank_of_torusLift_raw hperf hp le_rfl hraw hall
  have h5' : 5 ≤ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) :=
    h5.trans (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective
      hp (Subgroup.inclusion (le_sup_right : G₀ ≤ A ⊔ G₀))
      (Subgroup.inclusion_injective _))
  calc p ^ 5 ≤ p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) := Nat.pow_le_pow_right hp.pos h5'
    _ ≤ Nat.card A := hrank2

end CFSG.StandardType.RCKRP

module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck1515Six
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.Main
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck1515

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

private theorem eq_bot_of_normal_isPGroup_two {W : Type*} [Group W]
    [Finite W] (hW : Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON) (N : Subgroup W)
    [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
  rcases Ronan148W.card_normal_of_isTripleCover hW N with h | h
  · rw [hk] at h
    exact Subgroup.eq_bot_of_card_eq N
      (hk.trans (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num)) h))
  · rw [CFSG.Sporadic.ON.card_ON, hk] at h
    have h3 : 3 ∣ 2 ^ k := (show 3 ∣ 460815505920 by norm_num).trans h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

private theorem isQuasisimple_of_isTripleCover_ON {W : Type*}
    [Group W] (hW : Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON)
    (hp : Group.IsPerfect W) : CFSG.IsQuasisimple W := by
  obtain ⟨-, ⟨e⟩⟩ := hW
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  refine ⟨hp, e.isSimpleGroup, ?_⟩
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative (W ⧸ Subgroup.center W) := ⟨⟨hcon⟩⟩
  have hprime : (Nat.card (W ⧸ Subgroup.center W)).Prime :=
    Group.is_simple_iff_prime_card.mp e.isSimpleGroup
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON] at hprime
  norm_num at hprime

section KFact


private theorem eq_bot_of_surj_seven_core {Q : Type} [Group Q] [Finite Q]
    (hQ : Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON) (hQp : Group.IsPerfect Q)
    {F V : Subgroup Q} (hV : IsPGroup 2 V) (hFV : F ≤ Subgroup.normalizer (V : Set Q))
    (hS : (∃ (_ : Fact (Nat.Prime 7))
        (f : ↥F →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥F →* alternatingGroup (Fin 7), Function.Surjective f) : V = ⊥ := by
  have hT : Sec4.IsTripleCover ↥(⊤ : Subgroup Q) CFSG.Blueprint.NativeSporadic.ON :=
    KFacts.KS14.isTripleCover_congr Subgroup.topEquiv.symm hQ
  have hP : CFSG.pCore 2 ↥(⊤ : Subgroup Q) = ⊥ :=
    eq_bot_of_normal_isPGroup_two hT _ CFSG.pCore_isPGroup
  let eQ : ↥(⊤ : Subgroup Q) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hP).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hqs : CFSG.IsQuasisimple (↥(⊤ : Subgroup Q) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup Q)) :=
    CFSG.IsQuasisimple.of_mulEquiv eQ (isQuasisimple_of_isTripleCover_ON hQ hQp)
  have hTC : Sec4.IsTripleCover (↥(⊤ : Subgroup Q) ⧸ CFSG.pCore 2 ↥(⊤ : Subgroup Q))
      CFSG.Blueprint.NativeSporadic.ON :=
    KFacts.KS14.isTripleCover_congr eQ.symm hQ
  have hK := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.ks1523ONCent_holds Q ⊤ F V hqs
    hTC le_top hS hV (by rw [Subgroup.normalizer_eq_top]; exact le_top) hFV
  have hpc : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Q) = ⊥ := by
    rw [CFSG.Open.pCoreOf, hP, Subgroup.map_bot]
  rw [hpc] at hK
  have hVn : V.Normal := by
    refine ⟨fun v hv g => ?_⟩
    have h1 : ⁅v, g⁆ ∈ ⁅V, (⊤ : Subgroup Q)⁆ :=
      Subgroup.commutator_mem_commutator hv (Subgroup.mem_top g)
    have h2 := hK h1
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    have h3 : g * v * g⁻¹ = v := by rw [← h2]; group
    rwa [h3]
  exact eq_bot_of_normal_isPGroup_two hQ V hV

private theorem eq_bot_of_surj_seven {Q : Type*} [Group Q] [Finite Q]
    (hQ : Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON) (hQp : Group.IsPerfect Q)
    {F V : Subgroup Q} (hV : IsPGroup 2 V) (hFV : F ≤ Subgroup.normalizer (V : Set Q))
    (hS : (∃ (_ : Fact (Nat.Prime 7))
        (f : ↥F →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥F →* alternatingGroup (Fin 7), Function.Surjective f) : V = ⊥ := by
  let σ : Q ≃* Shrink.{0} Q := Shrink.mulEquiv.symm
  haveI : Group.IsPerfect Q := hQp
  have hperf : Group.IsPerfect (Shrink.{0} Q) :=
    Group.IsPerfect.ofSurjective (f := σ.toMonoidHom) σ.surjective
  have hbot : V.map σ.toMonoidHom = ⊥ := by
    refine eq_bot_of_surj_seven_core (F := F.map σ.toMonoidHom) (V := V.map σ.toMonoidHom)
      (KFacts.KS14.isTripleCover_congr σ hQ) hperf
      (hV.of_surjective (σ.toMonoidHom.subgroupMap V) (σ.toMonoidHom.subgroupMap_surjective V))
      ((Subgroup.map_mono hFV).trans (Subgroup.le_normalizer_map _)) ?_
    let ι : ↥(F.map σ.toMonoidHom) ≃* ↥F := (F.equivMapOfInjective σ.toMonoidHom σ.injective).symm
    rcases hS with ⟨hp, f, hf⟩ | ⟨f, hf⟩
    · exact Or.inl ⟨hp, f.comp ι.toMonoidHom, hf.comp ι.surjective⟩
    · exact Or.inr ⟨f.comp ι.toMonoidHom, hf.comp ι.surjective⟩
  exact (Subgroup.map_eq_bot_iff_of_injective V σ.injective).mp hbot

theorem false_of_isTripleCover_ON {Q X : Type*} [Group Q] [Group X] [Finite Q]
    (hQ : Sec4.IsTripleCover Q CFSG.Blueprint.NativeSporadic.ON)
    (hQp : Group.IsPerfect Q) {F V : Subgroup Q} (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥)
    (hFV : F ≤ Subgroup.normalizer (V : Set Q)) (φ : ↥F →* X) (hφ : Function.Surjective φ)
    (hX : IsType1483 X) : False := by
  haveI : Finite X := Finite.of_surjective φ hφ
  have hQc : Nat.card Q = 3 * 460815505920 := card_eq_of_isTripleCover_ON hQ
  have hXQ : Nat.card X ∣ Nat.card Q :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card F)
  have h25 : ¬ 25 ∣ Nat.card Q := by
    rw [hQc]
    norm_num
  rcases hX with hON | hcp | ha5 | h55 | h7 | ⟨hp7, hL37⟩
  · have h1 : Nat.card X ≤ Nat.card F := Nat.card_le_card_of_surjective φ hφ
    have h2 : Nat.card X = Nat.card Q := by rw [card_eq_of_isTripleCover_ON hON, hQc]
    have hF : F = ⊤ := Subgroup.eq_top_of_card_eq F
      (le_antisymm (Subgroup.card_le_card_group F) (h2 ▸ h1))
    rw [hF] at hFV
    haveI : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hFV)
    exact hV1 (eq_bot_of_normal_isPGroup_two hQ V hV)
  · exact h25 ((twentyFive_dvd_card (Or.inl hcp)).trans hXQ)
  · exact h25 ((twentyFive_dvd_card (Or.inr (Or.inl ha5))).trans hXQ)
  · exact h25 ((twentyFive_dvd_card (Or.inr (Or.inr h55))).trans hXQ)
  · obtain ⟨e⟩ := h7
    exact hV1 (eq_bot_of_surj_seven hQ hQp hV hFV
      (Or.inr ⟨e.toMonoidHom.comp φ, e.surjective.comp hφ⟩))
  · obtain ⟨e⟩ := hL37
    exact hV1 (eq_bot_of_surj_seven hQ hQp hV hFV
      (Or.inl ⟨hp7, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩))

end KFact

end CFSG.RankThree.PartTwo.Sec15.Liebeck1515

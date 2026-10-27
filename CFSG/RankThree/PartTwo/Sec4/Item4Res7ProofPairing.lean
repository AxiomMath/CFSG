module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofPairing
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightG2

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def K424PairingG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Type) [Field K] [Finite K], ringChar K ≠ 3 →
    4 ≤ Nat.card K → Nonempty (X ≃* adjointGroup .G2 K) →
    ∀ (D : Subgroup X) (c d : X) (J : Subgroup X), InnerConfig424 X D c d J →
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6)

@[expose] def K424PairingD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X → Subgroup.center X = ⊥ →
    ¬ IsSLThreePiAny X →
    (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) →
    ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6)

namespace Res4Seven


theorem exists_mulEquiv_adjointGroup_of_g2 {X : Type} [Group X]
    (hX : ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 3 ≤ Nat.card K ∧
      Nonempty (X ≃* adjointGroup .G2 K) := by
  obtain ⟨q, hq, ⟨f⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact GaloisField.card _ _ q.exponent_pos.ne'
  have hq3 : 3 ≤ q.card := by
    have h1 := ((TauCeti.LieTypeIndex.valid_iff _).mp hq).1
    rwa [TauCeti.LieTypeIndex.inStandardRange_iff] at h1
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hq K hK
  exact ⟨K, inferInstance, inferInstance, hK ▸ hq3,
    ⟨(f.trans b.symm).trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)⟩⟩

theorem false_of_config_g2_charThree {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    [Finite K] [CharP K 3] (E : X ≃* adjointGroup .G2 K) {D : Subgroup X} {c d : X}
    {J : Subgroup X} (h : InnerConfig424 X D c d J) : False := by
  have hc3 : c ^ 3 = 1 := h.maximal.prop.2 c h.c_mem
  have hHas : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (MulAut.conj c)) := by
    rw [Item424Res2.fixSub_conj_eq_centralizer_singleton]
    exact Sec11.KS11Lie2Proof.hasType424_of_mem h.mem_thetaComponentsIn h.isType424
  have hT := hHas.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr E (MulAut.conj c))
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hT
  refine Sec11.KS11Lie3Proof.not_hasType424_fixSub_g2_three (z := E c) ?_ ?_ hT
  · intro h1
    exact h.c_ne_one (E.injective (h1.trans (map_one E).symm))
  · rw [← map_pow, hc3, map_one]

end Res4Seven

open Res4Seven

theorem k424PairingLie_of
    (hG : K424PairingG2) (hD : K424PairingD4) : K424PairingLie := by
  intro X _ _ hX hq hZ hSL hXT D c d K h
  rcases hXT with hG2 | hD4
  · obtain ⟨F, _, _, hF3, ⟨E⟩⟩ := exists_mulEquiv_adjointGroup_of_g2 hG2
    by_cases h3 : ringChar F = 3
    · have : CharP F 3 := ringChar.of_eq h3
      exact (false_of_config_g2_charThree E h).elim
    · have hF4 : 4 ≤ Nat.card F := by
        by_contra hlt
        have hF : Nat.card F = 3 := by omega
        have : Fintype F := Fintype.ofFinite F
        obtain ⟨n, hpr, hcard⟩ := FiniteField.card F (ringChar F)
        have hdvd : ringChar F ∣ 3 := by
          rw [← hF, Nat.card_eq_fintype_card, hcard]
          exact dvd_pow_self _ n.pos.ne'
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
        · exact hpr.one_lt.ne' h1
        · exact h3 h1
      exact hG X F h3 hF4 ⟨E⟩ D c d K h
  · exact hD X hX hq hZ hSL hD4 D c d K h

end CFSG.RankThree.PartTwo.Sec4

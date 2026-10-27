module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggRowPRankLeTwo_smallMinus :
    GGRowPRankLeTwo fun p lab => ((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
      (lab.tag = .twD ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n - 1 := by
  rintro p hp - ⟨t, l, n⟩ hlab ⟨⟨ht, hl⟩ | ⟨ht, hl⟩, hpq⟩
  · dsimp only at ht hl hpq
    subst ht
    rintro Q ⟨K, _, _, hK, hQ⟩
    refine ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ X hXI hX => ?_⟩
    have hd3 : 3 ≤ l + 1 := by omega
    have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := fun h => by
      simp only [Prod.mk.injEq] at h
      omega
    have hd : (l + 1) / 2 < 3 := by omega
    exact (TwDThree.card_le_of_subset_unitaryConj (d := l + 1)
      ⟨Nat.prime_two, hlab.1, by rw [hK, ← pow_mul, mul_comm]⟩ hd3 hdq hp hpq hX hXI).trans_lt
      (Nat.pow_lt_pow_right hp.one_lt hd)
  · exact (largeEvenLabelAll_card_lt_twDThree hp hlab ⟨ht, hl, hpq⟩).mono
      fun _ _ _ _ h _ _ => h

theorem ggRow_absurd_of_clauseFive
    {S : ℕ → LargeEvenLabel → Prop}
    (h3 : ∀ p lab, S p lab → p ≠ 3 ∨ ∀ (X : Type) [Group X], MarkedModel lab X →
      ∀ lab' : LargeEvenLabel, markChar lab' ≠ 2 → ¬ MarkedModel lab' X)
    (hout : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I))
    (hdet : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → ∀ (X : Type) [Group X], MarkedModel lab X → ∀ lab' : LargeEvenLabel,
        LargeEvenInLambda2 lab' → markChar lab' = 2 → MarkedModel lab' X →
          ∀ c, ¬ LargeEvenHalfSplit p lab' c)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {K : Subgroup G}
    (hK : GGSecFiveWeakNbr p B Bs x L D J 𝒦 K) (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨y, hnb⟩ := hK.1
  have hc := hcfg.1.1
  have h5 := (hc.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hc.2.2, hnb.2⟩).2
  have hxB : x ∈ B := hc.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hc.1.2.2.2.2.2.2.1.1.1.2 x hxB
  have hxBs : x ∈ Bs := hc.2.1.1 hxB
  obtain ⟨hKp, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hrow
  have hSl : S p lab := by
    obtain ⟨_, _, _, _, -, -, _, ⟨hS, -⟩, -⟩ := largeEvenRawDatum_exists hraw
    exact hS
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, ⟨-, hN, hind⟩, hMM⟩, hO⟩ :=
    largeEvenRawDatum_exists (hout p lab hp hp2 hlab hSl _ hraw)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  have hxI : ggLAut K θ ⟨x, hxK⟩ ∈ I := ggLAut_mem_of_induces K θ hN hind hxBs
  have hφp : ggLAut K θ ⟨x, hxK⟩ ^ p = 1 := by
    have e : (⟨x, hxK⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [← map_pow, e, map_one]
  obtain ⟨r, hr⟩ := hO hs hna _ hxI hφp
  obtain ⟨k, hk, hkx⟩ := NbrInnerMore.exists_conj_of_ggLAut_eq_conj hKp θ hxK hr.symm
  have hMK : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv θ.symm hMM
  rcases h3 p lab hSl with hp3 | hX3
  · exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 ⟨k, hk, hkx⟩
      (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
      (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
  · exact NbrInnerMore.not_ggNbrClauseFiveMarking_of_inner' ⟨k, hk, hkx⟩
      (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
      (fun lab' hc' hM' => hX3 _ hMK lab' hc' hM')
      (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5

end CFSG.StandardType

end

module

public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFTwistedE6CommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2Defining
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient

public section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (localRank)

theorem twisted_E6_defining_prime_actual_component_exclusion {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) (f : ℕ) :
    ¬ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .twistedE6 p f := by
  rintro ⟨⟨-, hf, -⟩, hmod⟩
  have hQ := CFSG.RankThree.Classical2.localRank_quotient_le hp (by omega) N hN
  obtain ⟨K, _, _, hK, σ, hσ, φ, hφ, hker⟩ := exists_surj_graphFixedRootGroup_of_model hp hf hmod
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card hp (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])]
    omega
  obtain ⟨ι, hι, hcomm⟩ := twisted_E6_four_commuting_faithful_fixed_SL2 K hchar σ
  have : Fintype (RingHom.eqLocusField σ (RingHom.id K)) := Fintype.ofFinite _
  have hk : Fintype.card (RingHom.eqLocusField σ (RingHom.id K)) = p ^ f := by
    rw [Fintype.card_eq_nat_card]
    exact card_eqLocusField_of_pow hp hf hK hσ
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_defining_local_rank L hp hp3
      hf (by norm_num : 1 ≤ 4) hk φ hφ hker.le ι hι hcomm
  have : 4 * f ≤ 3 := hrank.trans (hQ.trans hX)
  omega

end CFSG.RankThree.Chevalley

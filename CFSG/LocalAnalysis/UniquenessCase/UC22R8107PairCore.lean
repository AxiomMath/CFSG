module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

namespace R8107Pair

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_of_fixed_pair {M K L : Subgroup G} (hK : K ∈ calC M)
    (hL : L ∈ calC M) (hKL : K ≠ L)
    (hKN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (K : Set G))
    (hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G))
    (hKZ : center (Bar2 K) = ⊥) (hKc : ∀ B : Subgroup G, B ≤ K → IsPGroup 3 B → IsCyclic B)
    (hLc : ∀ B : Subgroup G, B ≤ L → IsPGroup 3 B → IsCyclic B) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsElemAbelian p Q)
    (hQc : p ^ 2 ≤ Nat.card Q) {b₁ : G} (hb₁K : b₁ ∈ K) (hb₁ : orderOf b₁ = 3)
    (hb₁Q : ∀ u ∈ Q, b₁⁻¹ * (u * b₁ * u⁻¹) ∈ pCoreOf 2 K) {b₂ : G} (hb₂L : b₂ ∈ L)
    (hb₂ : orderOf b₂ = 3) (hb₂Q : ∀ u ∈ Q, b₂⁻¹ * (u * b₂ * u⁻¹) ∈ pCoreOf 2 L) :
    ∃ R E A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ A ≤ M ⊓ centralizer (E : Set G) ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Q := hQ.isPGroup
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hQK := hKN Q hQM hQodd
  have hQL := hLN Q hQM hQodd
  have hLC := P2251c.le_centralizerMod_of_ne hK hL hKL
  obtain ⟨a₂, ha₂L, ha₂, ha₂Q, -⟩ := P2251c.exists_orderOf_three (P₂ := ⊥) hp2 hQp
    IsPGroup.of_bot bot_le hQL bot_le hb₂L hb₂ hb₂Q fun u hu => by rw [mem_bot.1 hu]; simp
  have hz₂ : IsPGroup 3 (zpowers a₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₂, pow_one])
  have hz₂K : zpowers a₂ ≤ normalizer (K : Set G) :=
    hKN _ (zpowers_le.2 (hL.1.le ha₂L)) (by rw [Nat.card_zpowers, ha₂]; decide)
  obtain ⟨a₁, ha₁K, ha₁, ha₁Q, ha₁₂⟩ := P2251c.exists_orderOf_three (P₂ := zpowers a₂) hp2 hQp hz₂
    (zpowers_le.2 ha₂Q) hQK hz₂K hb₁K hb₁ hb₁Q fun v hv =>
    P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hLC (zpowers_le.2 ha₂L hv)) hb₁K
  have hna : a₂ ∉ zpowers a₁ := fun h => P2251c.not_mem_of_orderOf_eq_three
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ha₂
    (P2251c.mem_pCoreOf_of_mem_centralizerMod hKZ (zpowers_le.2 ha₁K h) (hLC ha₂L))
  obtain ⟨hEel, hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁ ha₂
      (mem_centralizer_iff.1 ha₁₂ a₂ (mem_zpowers a₂)).symm hna
  have hEM : zpowers a₁ ⊔ zpowers a₂ ≤ M :=
    sup_le (zpowers_le.2 (hK.1.le ha₁K)) (zpowers_le.2 (hL.1.le ha₂L))
  obtain ⟨R, hR, hER⟩ : ∃ R, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ zpowers a₁ ⊔ zpowers a₂ ≤ R := by
    obtain ⟨S, hS⟩ := (((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      hEel).isPGroup.comap_subtype (K := M)).exists_le_sylow
    exact ⟨_, ⟨S, rfl⟩, fun y hy => ⟨⟨y, hEM hy⟩, hS (by exact hy), rfl⟩⟩
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hR.isPGroup
    rw [hn]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  have ha₁R : a₁ ∈ R := hER (mem_sup_left (mem_zpowers a₁))
  have ha₂R : a₂ ∈ R := hER (mem_sup_right (mem_zpowers a₂))
  have ha₁C := P2251c.mem_centralizer_of_isCyclic hR.isPGroup (hKN R hR.le hRodd)
    (hKc _ inf_le_right (hR.isPGroup.to_le inf_le_left)) ha₁R ha₁K ha₁
  have ha₂C := P2251c.mem_centralizer_of_isCyclic hR.isPGroup (hLN R hR.le hRodd)
    (hLc _ inf_le_right (hR.isPGroup.to_le inf_le_left)) ha₂R ha₂L ha₂
  obtain ⟨A, hAQ, hA, hAc⟩ := UC6S846.exists_card_p_sq hp hQ hQc
  refine ⟨R, _, A, hR,
    sup_le (zpowers_le.2 (mem_inf.2 ⟨ha₁R, ha₁C⟩)) (zpowers_le.2 (mem_inf.2 ⟨ha₂R, ha₂C⟩)),
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hEel, hEc,
    le_inf (hAQ.trans hQM) (hAQ.trans ?_), hA, hAc⟩
  exact le_centralizer_iff.1 (sup_le (zpowers_le.2 ha₁Q) (zpowers_le.2 ha₂Q))

end R8107Pair

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

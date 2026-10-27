module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Loss
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107PairCore
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Pair

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_lossAt {K : Subgroup G} {p : ℕ} (hloss : R8107Loss.LossAt (Bar2 K) p)
    {Q : Subgroup G} (hQN : Q ≤ normalizer (K : Set G)) (hQ : IsElemAbelian p Q) :
    ∃ Q' : Subgroup G, Q' ≤ Q ∧ Nat.card Q ≤ p * Nat.card Q' ∧ ∃ b ∈ K, orderOf b = 3 ∧
      ∀ u ∈ Q', b⁻¹ * (u * b * u⁻¹) ∈ pCoreOf 2 K := by
  obtain ⟨x, hx3, Q₀, hQ₀, hQ₀x⟩ := hloss ↥Q
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hQ.2 _ x.2))
    (fun x y => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hQ.comm x.2 y.2))
    ((UC6S846.rhoL K).comp (inclusion hQN))
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have h3l : 3 ∣ orderOf l := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) l
    rwa [QuotientGroup.mk'_apply, hx3] at h
  have hfix : ∀ v ∈ Q₀, UC6S846.rhoL K (inclusion hQN v) ((l ^ (orderOf l / 3) : ↥K) : Bar2 K) =
      ((l ^ (orderOf l / 3) : ↥K) : Bar2 K) := fun v hv => by
    rw [QuotientGroup.mk_pow, map_pow]
    exact congrArg (· ^ (orderOf l / 3)) (hQ₀x v hv)
  refine ⟨Q₀.map Q.subtype, map_subtype_le _, ?_, _, (l ^ (orderOf l / 3)).2, by
    rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l, ?_⟩
  · rw [card_map_of_injective Q.subtype_injective, ← Q₀.card_mul_index, mul_comm]
    exact Nat.mul_le_mul_right _ hQ₀
  · rintro _ ⟨v, hv, rfl⟩
    exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hQN v) (l ^ (orderOf l / 3)).2 (hfix v hv)

theorem exists_elemAbelian_of_lossAt_pair {M K L : Subgroup G} (hK : K ∈ calC M) (hL : L ∈ calC M)
    (hKL : K ≠ L)
    (hKN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (K : Set G))
    (hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G))
    (hKZ : center (Bar2 K) = ⊥) (hKc : ∀ B : Subgroup G, B ≤ K → IsPGroup 3 B → IsCyclic B)
    (hLc : ∀ B : Subgroup G, B ≤ L → IsPGroup 3 B → IsCyclic B) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hM : 4 ≤ CFSG.Open.pRank p M) (hKloss : R8107Loss.LossAt (Bar2 K) p)
    (hLloss : R8107Loss.LossAt (Bar2 L) p) :
    ∃ R E A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ A ≤ M ⊓ centralizer (E : Set G) ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hM
  have hodd : ∀ Q ≤ A₀, Odd (Nat.card Q) := fun Q hQ =>
    Odd.of_dvd_nat (hA₀c ▸ (hp.odd_of_ne_two hp2).pow) (Subgroup.card_dvd_of_le hQ)
  obtain ⟨Q₁, hQ₁A, hQ₁c, b₁, hb₁K, hb₁, hb₁Q⟩ :=
    exists_fixed_of_lossAt hKloss (hKN A₀ hA₀M (hodd A₀ le_rfl)) hA₀
  obtain ⟨Q₂, hQ₂Q₁, hQ₂c, b₂, hb₂L, hb₂, hb₂Q⟩ := exists_fixed_of_lossAt hLloss
    (hLN Q₁ (hQ₁A.trans hA₀M) (hodd Q₁ hQ₁A)) (hA₀.mono hQ₁A)
  have hQ₂c' : p ^ 2 ≤ Nat.card Q₂ := by
    refine Nat.le_of_mul_le_mul_left (a := p ^ 2) ?_ (pow_pos hp.pos 2)
    calc p ^ 2 * p ^ 2 = Nat.card A₀ := by rw [hA₀c]; ring
      _ ≤ p * Nat.card Q₁ := hQ₁c
      _ ≤ p * (p * Nat.card Q₂) := Nat.mul_le_mul_left _ hQ₂c
      _ = p ^ 2 * Nat.card Q₂ := by ring
  exact exists_elemAbelian_of_fixed_pair hK hL hKL hKN hLN hKZ hKc hLc hp hp2
    (hQ₂Q₁.trans (hQ₁A.trans hA₀M)) (hA₀.mono (hQ₂Q₁.trans hQ₁A)) hQ₂c' hb₁K hb₁
    (fun u hu => hb₁Q u (hQ₂Q₁ hu)) hb₂L hb₂ hb₂Q

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Pair

end

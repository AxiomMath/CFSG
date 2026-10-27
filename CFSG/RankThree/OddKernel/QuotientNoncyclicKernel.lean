module

public import CFSG.RankThree.OddKernel.RankTwoPowerStructure

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open scoped Pointwise

universe u

variable {p : ℕ}

theorem isCyclic_quotient_map_of_mul_eq_univ {P : Type*} [Group P] {E X : Subgroup P}
    [E.Normal] [IsCyclic X] (hEX : (E : Set P) * (X : Set P) = Set.univ) (N : Subgroup P)
    [N.Normal] [(E.map (QuotientGroup.mk' N)).Normal] :
    IsCyclic ((P ⧸ N) ⧸ E.map (QuotientGroup.mk' N)) := by
  let ρ : P →* (P ⧸ N) ⧸ E.map (QuotientGroup.mk' N) :=
    (QuotientGroup.mk' _).comp (QuotientGroup.mk' N)
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective N)
  refine isCyclic_of_surjective (ρ.comp X.subtype) fun q => ?_
  obtain ⟨g, rfl⟩ := hρ q
  have hg : g ∈ (E : Set P) * (X : Set P) := hEX ▸ Set.mem_univ g
  obtain ⟨e, he, x, hx, rfl⟩ := Set.mem_mul.1 hg
  refine ⟨⟨x, hx⟩, ?_⟩
  have hρe : ρ e = 1 := (QuotientGroup.eq_one_iff _).2 (mem_map_of_mem _ he)
  change ρ x = ρ (e * x)
  rw [map_mul, hρe, one_mul]

theorem rank_two_large_prime_quotient_noncyclic_kernel (hp : p.Prime) (hp3 : 3 < p)
    {Q : Type u} [Group Q] [Finite Q] (hQ : IsPGroup p Q) (hrank : pRank p Q ≤ 2)
    (N : Subgroup Q) [N.Normal] (hN : 2 ≤ pRank p N) : pRank p (Q ⧸ N) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hstr := rank_two_large_prime_power_structure_and_section_bound hp hp3 hQ hrank
  have htors := hstr.1
  obtain ⟨j, hj⟩ := (hQ.to_subgroup (omega₁ Q (p := p))).exists_card_eq
  have hj3 : j ≤ 3 := by
    have h := htors.2
    rw [hj] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  rcases (show j ≤ 2 ∨ j = 3 by omega) with hj2 | rfl
  · exact (hstr.2.1 (hj ▸ Nat.pow_le_pow_right hp.pos hj2)).2 N
  obtain ⟨-, -, -, ⟨X, hXc, hEX⟩, -⟩ := hstr.2.2.1 hj
  have hEn : (omega₁ Q (p := p)).Normal :=
    @normal_of_characteristic _ _ _ (omega₁_characteristic Q (p := p))
  rw [pRank_eq_open_pRank_top] at hN
  obtain ⟨B, -, hB, hBcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup N)
  have hBle : B.map N.subtype ≤ omega₁ Q (p := p) ⊓ N := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨subset_closure (show (b : Q) ^ (p ^ 1) = 1 by
      rw [pow_one]; exact congrArg Subtype.val (hB.2 b hb)), b.2⟩
  have hEN : p ^ 2 ≤ Nat.card (omega₁ Q (p := p) ⊓ N : Subgroup Q) := by
    calc p ^ 2 ≤ p ^ CFSG.Open.pRank p (⊤ : Subgroup N) := Nat.pow_le_pow_right hp.pos hN
      _ = Nat.card (B.map N.subtype) := by rw [card_map_of_injective N.subtype_injective, hBcard]
      _ ≤ _ := card_le_of_le hBle
  have hcard := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker
    (QuotientGroup.mk' N) (omega₁ Q (p := p))
  rw [QuotientGroup.ker_mk', hj] at hcard
  have hK : Nat.card ((omega₁ Q (p := p)).map (QuotientGroup.mk' N)) ≤ p := by
    have h1 : Nat.card ((omega₁ Q (p := p)).map (QuotientGroup.mk' N)) * p ^ 2 ≤ p * p ^ 2 := by
      calc _ ≤ Nat.card ((omega₁ Q (p := p)).map (QuotientGroup.mk' N)) *
            Nat.card (omega₁ Q (p := p) ⊓ N : Subgroup Q) := Nat.mul_le_mul_left _ hEN
        _ = p * p ^ 2 := by rw [← hcard]; ring
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos hp.pos 2)
  have hKn : ((omega₁ Q (p := p)).map (QuotientGroup.mk' N)).Normal :=
    hEn.map _ (QuotientGroup.mk'_surjective N)
  have hKc := isCyclic_quotient_map_of_mul_eq_univ hEX N
  rw [pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA => ?_
  refine card_le_of_isCyclic_quotient hp ((omega₁ Q (p := p)).map (QuotientGroup.mk' N)) (r := 1)
    (fun B hBK _ => ?_) hA
  rw [pow_one]
  exact (card_le_of_le hBK).trans hK

end CFSG.RankThree.OddKernel

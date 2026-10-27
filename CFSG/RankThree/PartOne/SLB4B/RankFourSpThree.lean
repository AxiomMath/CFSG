module

public import CFSG.RankThree.PartOne.SLB4B.RankFourSpProd
public import CFSG.RankThree.PartOne.SLB4B.RadicalSp
public import CFSG.RankThree.PartOne.SLB4B.CommCover

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.RankThree.PartOne.SRC CFSG.RankThree.PartTwo.Census
  CFSG.Assembly.LowTwoRank

section Three

variable {K : Type} [Field K] [Finite K]

theorem sp4_quasisimple_three (h : Nat.card K = 3) : CFSG.IsQuasisimple (StatedSp 2 K) :=
  CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inr (Or.inl ⟨h, le_rfl⟩))

theorem cover_sp4_prod_three {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : p = 3)
    (hK : Nat.card K = p) (W : Type) [Group W] [Finite W]
    (ρ : W →* StatedSp 2 K × Multiplicative K) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hπ, hπker, hker1⟩ := fst_cover_data hK W ρ hρ hker
  obtain ⟨E₀, hE₀, hcard, hcomm, hlift⟩ := exists_sp4_three_radical hp3 hK
  have hK3 : Nat.card K = 3 := by rw [hK, hp3]
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  exact rank_four_of_cover_quasisimple_ker_comm hp2 (sp4_quasisimple_three hK3) sp4_coprime_center _
    (planeInvolution_noncentral hp2) (planeInvolution_coprime hp2) (pow_four_dvd_card_sp4 hK1 le_rfl)
    hE₀ hcard hcomm hlift _ hπ hπker hker1

theorem rankFourCover_psp6_three {p e : ℕ} [Fact p.Prime] [CharP K p] (hp3 : p = 3) (he : e = 1)
    (hK : Nat.card K = p ^ e) : RankFourCover p (StatedProj (StatedSp 3 K)) := by
  subst he
  rw [pow_one] at hK
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  exact rankFourCover_of_cover_ker hp hp2
    (fun W _ _ ρ hρ hker => cover_sp4_prod_three hp3 hK W ρ hρ hker) (sp6ProdProj (K := K))
    (fun A hA => by rw [sp6ProdProj_injective (hA.trans (map_one _).symm), one_pow])
    (orderOf_sp6Invol (two_ne_zero_of_charP hp2)) sp6ProdProj_comm

end Three

end CFSG.RankThree.PartOne.SLB4B

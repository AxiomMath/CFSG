module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Pair
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Fitting

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.Ch1Sec3

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem quotient_main (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ) (h37 : A37Statement Γ)
    (h38 : A38Part3 Γ) (hC : TheoremCSimple) (hF : Facts134E9He) {P T N O : Subgroup Γ}
    (hP9 : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T)
    (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) → U = ⊥ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hTON : T ≤ O ⊔ N) (hOX : ∀ K : Subgroup Γ, K.Normal → P ≤ K → O ≤ K)
    (hPc : P ≤ commutator Γ) :
    P.Normal ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧ L.Normal ∧ P ≤ L ∧
        E9Outcome L P T) ∨
      (∃ L : Subgroup Γ, L ∈ cComp (⊤ : Subgroup Γ) ∧ CFSG.IsComponent L ∧
        ∃ n ∈ N, n ∉ Subgroup.normalizer (L : Set Γ) ∧
          L ⊓ L.map (MulAut.conj n).toMonoidHom = ⊥ ∧
          P ≤ L ⊔ L.map (MulAut.conj n).toMonoidHom ∧ Nat.card (P ⊓ L : Subgroup Γ) = 3 ∧
          ((∃ m : ℕ, Even m ∧ StatedClassicalModel ↥L .PSL 2 2 m) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel ↥L .PSL 2 q 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r (⊤ : Subgroup Γ) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hPP : ⁅P, P⁆ = ⊥ := commutator_eq_bot_of_card_nine hP9
  have hirr' : ∀ U : Subgroup Γ, ⁅P, P⁆ ≤ U → U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) →
      U = ⁅P, P⁆ ∨ U = P := by
    intro U _ hUP hNU
    rw [hPP]
    exact hirr U hUP hNU
  rcases normal_or_centralizes_fitting hyp.o2 hrank (by norm_num : 3 ≠ 2) hPp hexp
      (by rw [hP9]; norm_num) (by rw [hP9]; norm_num) hNP hirr' hPc with hn | ⟨hFit, hrk⟩
  · exact Or.inl hn
  right
  have hrkP : 2 ≤ Open.pRank 3 P := two_le_pRank_of_pow_eq_one hexp (by rw [hP9]; norm_num)
  obtain ⟨L, hL, hLP⟩ := exists_component_not_le_centralizer hPp hrkP hFit hrk
  have hLc : L ∈ cComp (⊤ : Subgroup Γ) := mem_cComp_top_of_isComponent hL
  by_cases hLn : L.Normal
  · obtain ⟨hPL, hout⟩ := normal_case hyp h36 hC hF hP9 hexp hT hNT hNP hirr hmul hLc hL hLn hLP
    exact Or.inl ⟨L, hLc, hL, hLn, hPL, hout⟩
  · exact Or.inr ⟨L, hLc, hL, pair_case hyp h36 h37 h38 hF hP9 hexp hT hNT hNP hirr hmul hTON hOX
      hLc hL hLn hLP⟩

end CFSG.Quasithin.P134

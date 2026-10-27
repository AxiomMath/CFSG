module

public import CFSG.Quasithin.EmptyFaithful.SBc11Cent
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.SzN15Br2
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc11

section Ctx

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
private theorem nonempty_quot_equiv {H : Type} [Group H] (α : ↥L →* H)
    (hα : IsModO2Surj L α) : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα.1)⟩

private theorem twenty_le_card_star (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlie : IsSL3Quot L ∨ IsSp4Quot L) : 20160 ≤ Nat.card ↥(Star153 T I L) := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  obtain ⟨hLN, hker, hnt⟩ := ctx_star c
  exact (SzN15.xOrd_autOn hLN hker hnt c25.conc.2.2.2.2.2 hlie).1

theorem not_isSp4Block (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) :
    ¬ IsSp4Block L := by
  rintro ⟨-, F, hF, hFin, hcard, α, hαs, hαk, -⟩
  obtain ⟨e⟩ := nonempty_quot_equiv α ⟨hαs, hαk⟩
  have h := twenty_le_card_star c (Or.inr ⟨F, hF, hFin, hcard, ⟨e⟩⟩)
  rcases card_of_list hlist with h1 | h1 | h1 <;> omega

private theorem card_of_sl3_two (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L))
    {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hF : Fintype.card F = 2) (hmod : IsModO2Surj L α) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 ∧ Nat.card ↥(Star153 T I L) = 168 := by
  obtain ⟨ψ, hψs, -, -⟩ := exists_star_hom c
  obtain ⟨e⟩ := nonempty_quot_equiv α hmod
  have hFc : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card]; exact hF
  have hL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hFc]
    norm_num
  have hle : Nat.card ↥(Star153 T I L) ≤ 168 :=
    hL ▸ Nat.card_le_card_of_surjective ψ hψs
  refine ⟨hL, ?_⟩
  rcases card_of_list hlist with h | h | h <;> omega

theorem sl3_case (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L))
    {n : ℕ} {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hcard : Fintype.card F = 2 ^ n) (hmod : IsModO2Surj L α) :
    n = 1 ∧ IsPSL 3 2 1 ↥(Star153 T I L) := by
  have hn : n = 1 := by
    by_contra hne
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · simp at hcard
          omega
        · exact absurd rfl hne
      · exact h
    obtain ⟨e⟩ := nonempty_quot_equiv α hmod
    have h := twenty_le_card_star c (Or.inl ⟨n, F, inferInstance, inferInstance, hn2, hcard, ⟨e⟩⟩)
    rcases card_of_list hlist with h1 | h1 | h1 <;> omega
  subst hn
  have hF : Fintype.card F = 2 := by simpa using hcard
  have h168 := (card_of_sl3_two c hlist hF hmod).2
  refine ⟨rfl, ?_⟩
  rcases hlist with h | h | h
  · exact h
  · have := card_of_isAlt_six h
    omega
  · have := card_of_isPSU_three_three h
    omega

theorem sl3_centralizer (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L))
    {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hF : Fintype.card F = 2) (hmod : IsModO2Surj L α) :
    L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L := by
  obtain ⟨hL, hS⟩ := card_of_sl3_two c hlist hF hmod
  obtain ⟨ψ, hψs, -, hψ1⟩ := exists_star_hom c
  refine centralizer_UI_eq_pCoreOf_of_ker_eq_bot c hψ1 ?_
  have hmul : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(Star153 T I L) * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]
  rw [hL, hS] at hmul
  have h1 : Nat.card ψ.ker = 1 := by omega
  exact Subgroup.card_eq_one.mp h1

end Ctx

end SBc11

end CFSG.Quasithin

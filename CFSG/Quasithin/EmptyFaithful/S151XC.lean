module

public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Ctx15124 (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G) : Prop where
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  h17 : Lemma15117Concl T M Z₁
  h18 : Lemma15118Concl T Mc M Z₁
  h19 : Lemma15119Used T Mc M Z₁ V₂
  hL : IsL1519 Mc Z₁ L
  h22 : Lemma15122Concl T Mc M Z₁ L
  small : Ce15Small T Mc M

@[expose] def Input15124SevenBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Seven T Mc M → IsLnBlock L 3

@[expose] def Input15124BlockV2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L → IsLnBlock L 3 → Nat.card V₂ = 4

@[expose] def Input15124NotBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Four T Mc M → IsLnBlock L 3 → False

theorem lemma15124InputU_of_named_inputs (nA : Input15124SevenBlock) (nB : Input15124BlockV2)
    (nC : Input15124NotBlock) : Lemma15124InputU := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 hsmall
  have hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h22, hsmall⟩
  have hS := hC.setting
  have hnb : ¬ IsLnBlock L 3 := by
    intro hb
    have h4 : Nat.card V₂ = 4 := nB G T Mc M Z₁ Z₂ V₁ V₂ L hc hb
    rcases hsmall with h | h | h
    · exact nC G T Mc M Z₁ Z₂ V₁ V₂ L hc h hb
    · have h16 := (hS.ranks_six ⟨3, Or.inl rfl, h⟩).2.1
      omega
    · have h16 := (hS.ranks_seven h).2.2.1
      omega
  refine ⟨?_, hnb⟩
  rcases hsmall with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hnb (nA G T Mc M Z₁ Z₂ V₁ V₂ L hc h)).elim

end CFSG.Quasithin

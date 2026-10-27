module

public import CFSG.CGT.Foote82.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem factorial_div_two_ne (N : ℕ) : N.factorial / 2 ≠ 25920 := by
  rcases Nat.lt_or_ge N 9 with h | h
  · interval_cases N <;> decide
  · have := Nat.factorial_le h
    have h9 : Nat.factorial 9 = 362880 := by decide
    omega

theorem isFType_of_footeArrow (h7S : CFSG.CGT.Foote82.FooteSevenSharpF) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hc : CFSG.Assembly.IsCharTwoType G) (he3 : CFSG.Assembly.evenRank G = 3)
    {J₁ J₂ : Subgroup G} (h1 : InFooteB J₁) (h2 : InFooteB J₂) (hne : J₁ ≠ J₂)
    (harr : FooteArrow J₁ J₂) (hF : IsFType J₁) : IsFType J₂ :=
  h7S G hs hnab hK hc he3 J₁ J₂ h1 h2 hne harr hF

theorem exists_inFooteBStar_isFType (h7S : CFSG.CGT.Foote82.FooteSevenSharpF)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) (hc : CFSG.Assembly.IsCharTwoType G)
    (he3 : CFSG.Assembly.evenRank G = 3) {L : Subgroup G} (hL : InFooteB L)
    (hF : IsFType L) : ∃ J : Subgroup G, InFooteBStar J ∧ IsFType J := by
  classical
  let r : Subgroup G → Subgroup G → Prop := fun A B => InFooteB B ∧ FooteArrow A B
  let R : Set (Subgroup G) := {J | Relation.ReflTransGen r L J}
  have hR : ∀ J ∈ R, InFooteB J ∧ IsFType J := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨hL, hF⟩
    | @tail A B _ hstep ih =>
      refine ⟨hstep.1, ?_⟩
      by_cases hAB : A = B
      · rw [← hAB]
        exact ih.2
      · exact isFType_of_footeArrow h7S hs hnab hK hc he3 ih.1 hstep.1 hAB hstep.2 ih.2
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfin : R.Finite := Set.toFinite R
  obtain ⟨J, hJR, hJmax⟩ := Finset.exists_max_image hfin.toFinset (fun J => Nat.card J)
    ⟨L, hfin.mem_toFinset.mpr Relation.ReflTransGen.refl⟩
  rw [Set.Finite.mem_toFinset] at hJR
  refine ⟨J, ⟨(hR J hJR).1, fun J' hJ' harr => ?_⟩, (hR J hJR).2⟩
  have hJ'R : J' ∈ R := Relation.ReflTransGen.tail hJR ⟨hJ', harr⟩
  have hle := hJmax J' (hfin.mem_toFinset.mpr hJ'R)
  exact (Subgroup.eq_of_le_of_card_ge harr.1 hle).symm

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

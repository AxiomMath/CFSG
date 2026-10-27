module

public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item64One : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G →
    ∀ E ∈ partTwoE G, (fourGroups E).Nonempty

@[expose] def Item612Sec21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Sec21Std G A →
    ∀ E ∈ collectionIn (partTwoE G) A, ∀ U ∈ fourGroups E, (lThreeStarPairs A E U).Nonempty

@[expose] def Item233 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → CFSG.Open.GLBStronglyEmbedded 3 (nGroup A)

@[expose] def Item234 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∃ z ∈ nGroup A, orderOf z = 2 ∧
      (∃ T : Sylow 2 (nGroup A), z ∈ (T : Subgroup (nGroup A)).map (nGroup A).subtype ∧
        (T : Subgroup (nGroup A)).map (nGroup A).subtype ≤ Subgroup.centralizer {z}) ∧
      Subgroup.centralizer {z} ≤ nGroup A ∧
      ∀ x ∈ nGroup A, orderOf x = 2 →
        0 < CFSG.Open.pRank 3 (nGroup A ⊓ Subgroup.centralizer {x})

variable {G : Type} [Group G]

theorem partTwoE_eq_partTwoF_of_subset [Finite G] (h : partTwoF G ⊆ partTwoE G) :
    partTwoE G = partTwoF G := by
  apply Set.Subset.antisymm _ h
  intro E hE
  obtain ⟨A, hEA, hmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hE.1
  have hF : A ∈ partTwoF G :=
    ⟨hmax.prop, fun B hB hAB => le_antisymm (hmax.2 hB hAB) hAB, E, hE, hEA⟩
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [(h hF).2.1, hE.2.1])
  exact hEeq ▸ hF

theorem exists_sec21Std [Finite G] (hG : PartTwoStanding G) (hS : partTwoS G ≠ ∅) :
    ∃ A : Subgroup G, Sec21Std G A := by
  by_cases hFE : partTwoF G ⊆ partTwoE G
  · obtain ⟨A, hA⟩ := Set.nonempty_iff_ne_empty.mpr hS
    exact ⟨A, hG, hA, fun _ => partTwoE_eq_partTwoF_of_subset hFE⟩
  · obtain ⟨A, hAF, hAE⟩ := Set.not_subset.mp hFE
    exact ⟨A, hG, hG.toTheoremFourHyp.partTwoF_diff_partTwoE_subset ⟨hAF, hAE⟩,
      fun h => absurd h hAE⟩

theorem item236_of_items (h64 : Item64One) (h612 : Item612Sec21) (h233 : Item233)
    (h234 : Item234) (hHolt : HoltUniqueFixedPointSimple) : Item236 := by
  intro G _ _ hG
  by_contra hS
  have := hG.isSimpleGroup
  obtain ⟨A, hA⟩ := exists_sec21Std hG hS
  obtain ⟨E, hE, hEA⟩ := hA.mem_S.1.2.2
  obtain ⟨U, hU⟩ := h64 G hA.standing E hE
  obtain ⟨⟨c, L⟩, hcL⟩ := h612 G A hA E ⟨hE, hEA⟩ U hU
  have hpair : Sec21Pair G A E U c L := ⟨hA, ⟨hE, hEA⟩, hU, hcL⟩
  have hN := h233 G A E U c L hpair
  obtain ⟨z, hzN, hz, hT, hC, hm⟩ := h234 G A E U c L hpair
  have h3 : ∀ x ∈ nGroup A, orderOf x = 2 →
      3 ∣ Nat.card (nGroup A ⊓ Subgroup.centralizer {x} : Subgroup G) := by
    intro x hx hx2
    exact (dvd_pow_self 3 (hm x hx hx2).ne').trans
      (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card 3 Nat.prime_three _)
  have hfix := rank3II_23_5 hN hzN hz hC h3
  exact hG.not_inCatalog (inCatalog_of_unique_fixed hHolt hG.nonabelian hN.1 hz hfix hT)

end CFSG.RankThree.PartTwo.Sec21

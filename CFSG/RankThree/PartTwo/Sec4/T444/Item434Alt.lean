module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34
import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.RankThree.Asc83Table.E27
import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

theorem pRank_three_mulAut_alternatingGroup_five_le_one :
    CFSG.pRank 3 (MulAut (alternatingGroup (Fin 5))) ≤ 1 := by
  set c := CFSG.Quasithin.SteinbergCB.conjPerm 5
  have e : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective c ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩
  rw [← CFSG.RankThree.Asc83Table.pRank_congr e]
  refine csSup_le' ?_
  rintro r ⟨B, -, hcard⟩
  have hdvd : 3 ^ r ∣ 120 := by
    rw [← hcard]
    have h := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_perm, Nat.card_fin] at h
    exact h
  by_contra hr
  have h9 : 3 ^ 2 ∣ 3 ^ r := Nat.pow_dvd_pow 3 (by omega)
  have := h9.trans hdvd
  norm_num at this

@[expose] def IsAltIn (ns : List ℕ) (X : Type) [Group X] : Prop :=
  ∃ n ∈ ns, Nonempty (X ≃* alternatingGroup (Fin n))

section Families


@[expose] def Item434AltLie : Prop :=
  Item434SecFor (IsAltIn [6, 8])

@[expose] def Item434AltSeven : Prop :=
  Item434SecFor (IsAltIn [7])

@[expose] def Item434AltNine : Prop :=
  Item434SecFor (IsAltIn [9])

@[expose] def Item434AltTenEleven : Prop :=
  Item434SecFor (IsAltIn [10, 11])

@[expose] def Item434AltTwelve : Prop :=
  Item434SecFor (IsAltIn [12])

theorem item434Alt_of (hLie : Item434AltLie) (h7 : Item434AltSeven) (h9 : Item434AltNine)
    (h1011 : Item434AltTenEleven) (h12 : Item434AltTwelve) : Item434Alt := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := hL
  interval_cases n
  · exact (hc.false_of_pRank_mulAut_le_one e
      pRank_three_mulAut_alternatingGroup_five_le_one).elim
  · exact hLie G₀ hG₀ H G f hf hker A M Q hc ⟨6, by simp, ⟨e⟩⟩
  · exact h7 G₀ hG₀ H G f hf hker A M Q hc ⟨7, by simp, ⟨e⟩⟩
  · exact hLie G₀ hG₀ H G f hf hker A M Q hc ⟨8, by simp, ⟨e⟩⟩
  · exact h9 G₀ hG₀ H G f hf hker A M Q hc ⟨9, by simp, ⟨e⟩⟩
  · exact h1011 G₀ hG₀ H G f hf hker A M Q hc ⟨10, by simp, ⟨e⟩⟩
  · exact h1011 G₀ hG₀ H G f hf hker A M Q hc ⟨11, by simp, ⟨e⟩⟩
  · exact h12 G₀ hG₀ H G f hf hker A M Q hc ⟨12, by simp, ⟨e⟩⟩

end Families

end CFSG.RankThree.PartTwo.Sec4

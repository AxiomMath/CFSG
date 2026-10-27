module

public import CFSG.LocalAnalysis.WeakClosure81.FiveInputs
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneOddFix
public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneOddMove

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

theorem r3_1_holds :
    R3_1 := by
  unfold R3_1
  intro n hn H T K hA hT hXK hKH
  obtain ⟨σ, hσ, hTσ, huniq⟩ := ThreeOne.exists_matching hT
  have hN := ThreeOne.setNormalizer_eq_centralizer hσ hTσ
  rw [hN] at hXK ⊢
  have hTC : T ≤ Subgroup.centralizer {σ} := ThreeOne.le_centralizer_of_matching hσ hTσ
  by_cases hfix : ∀ x, σ x ≠ x
  · have heven : Even n := by
      simpa using ThreeOne.even_card_of_forall_apply_ne (Ω := Fin n) hσ hfix
    have hn6 : 6 ≤ n := by
      obtain ⟨m, hm⟩ := heven
      omega
    have h6 : 6 ≤ Fintype.card (Fin n) := by simpa using hn6
    rcases ThreeOne.overgroups_of_forall_apply_ne (Ω := Fin n) h6 hσ hfix hA hT hTC hXK hKH with
      h | h | ⟨hc8, hHA, hE8⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hn8 : n = 8 := by
        rw [← Fintype.card_fin n]
        exact hc8
      subst hn8
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨MulEquiv.subgroupCongr hHA⟩, ?_⟩)))
      unfold ThreeOne.IsE8L3 at hE8
      exact hE8
  · push Not at hfix
    obtain ⟨α, hα⟩ := hfix
    have hfixα : ∀ x, x ≠ α → σ x ≠ x := by
      intro x hx hσx
      exact hx (huniq x α hσx hα)
    have hOdd : Odd n := by
      simpa using ThreeOne.odd_card_of_apply_eq (Ω := Fin n) hσ hα hfixα
    have hfixT : ∀ t ∈ T, t.IsSwap → t α = α := by
      intro t htT _
      exact ThreeOne.apply_eq_of_mem_centralizer hα hfixα (hTC htT)
    by_cases hKα : K ≤ MulAction.stabilizer (Perm (Fin n)) α
    · rcases ThreeOne.overgroups_of_le_stabilizer hn hσ hα hfixα hA hT hTC hXK hKH hKα with
        h | h | ⟨hH9, hE8⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl ⟨hOdd, α, hfixT, h⟩))
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr hH9, ?_⟩)))
        unfold ThreeOne.IsE8L3 at hE8
        exact hE8
    · obtain ⟨k, hkK, hkα⟩ := SetLike.not_le_iff_exists.mp hKα
      have hkα' : k α ≠ α := by
        intro h
        exact hkα (MulAction.mem_stabilizer_iff.mpr (by simpa [Equiv.Perm.smul_def] using h))
      rcases ThreeOne.overgroups_of_apply_ne hn hσ hα hfixα hA hT hTC hXK hKH hkK hkα' with
        h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end CFSG.LocalAnalysis.WeakClosure81

end

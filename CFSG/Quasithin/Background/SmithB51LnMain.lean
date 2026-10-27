module

public import CFSG.Quasithin.Background.SmithB51LnTopE
public import CFSG.Quasithin.Background.SmithB51LnTopA
public import CFSG.Quasithin.Background.SmithB51LnTopD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Ln

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem case_top (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hI16 : AsI16Cover)
    (hB492 : AsB492Split) (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (htop : commV L = ⊤) :
    (∃ m, B51Case1iii G L m) ∨ B51Case1iv G L := by
  obtain ⟨A₁, hA₁⟩ := exists_offender h
  obtain ⟨A, hA, -⟩ := B1Red.exists_isFFStarMin_below hA₁
  obtain ⟨hAL, I, π₁, hI, hMI, hR₁⟩ := top_first hA21 hB42 hIH hV h hU hn eL hA
  obtain ⟨hIL, -, hIlt, -⟩ := irr_data hI
  have hItop : I ≠ ⊤ := fun h0 => hU (by rw [htop]; rw [h0] at hI; exact hI)
  obtain ⟨U₀, hU₀inv, hIU₀, hU₀top, hch₀⟩ := exists_max_sub hIL hItop
  obtain ⟨π, hRtop⟩ := top_natural hA21 hB42 hIH hV h hn eL htop hA hAL hMI hR₁ hU₀inv hIU₀
    hU₀top hch₀
  have hcomm := commSub_eq_of_top_natural hI16 hV htop hU₀inv hU₀top hch₀ hn hRtop
  have hU₀ne : U₀ ≠ ⊥ := by
    intro h0
    rw [h0, le_bot_iff] at hIU₀
    rw [hIU₀] at hIlt
    exact not_lt_bot hIlt
  have hstr := sub_structure hA21 hB42 hI16 hIH hV h hn eL hA hAL hU₀inv hU₀top hU₀ne hcomm hRtop
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  rcases top_structure hB492 hV h hn hA hAL hU₀top hRtop hstr with hS | ⟨k, hk1, hk, hD⟩
  · left
    exact ⟨n, eq_L_of_sumNatDual h hV hS, by rw [htop]; exact hS⟩
  · right
    exact ⟨eq_L_of_copies h hn3 hk1 hD, n, hn, k, hk1, hk, by rw [htop]; exact hD⟩

end Ln

theorem asB51NonirrLnIH_holds (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hI16 : AsI16Cover)
    (hB492 : AsB492Split) : AsB51NonirrLnIH := by
  intro V _ _ hIH hV G L h hU hLn
  obtain ⟨n, hn, ⟨eL⟩⟩ : ∃ n, (n = 4 ∨ n = 5) ∧ Nonempty (↥L ≃* ↥(StatedSL n (ZMod 2))) := by
    rcases hLn with ⟨K, hK, hKf, hc, ⟨e⟩⟩ | ⟨K, hK, hKf, hc, ⟨e⟩⟩
    · obtain ⟨ι⟩ := Ln.exists_equiv_zmod_two hc 4
      exact ⟨4, Or.inl rfl, ⟨e.trans ι.symm⟩⟩
    · obtain ⟨ι⟩ := Ln.exists_equiv_zmod_two hc 5
      exact ⟨5, Or.inr rfl, ⟨e.trans ι.symm⟩⟩
  by_cases htop : commV L = ⊤
  · exact Ln.case_top hA21 hB42 hI16 hB492 hIH hV h hU hn eL htop
  · exact Ln.case_lt hA21 hIH hV h hU hn eL htop

end CFSG.Quasithin.B5

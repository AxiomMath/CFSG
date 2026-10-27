module

public import CFSG.Quasithin.Background.SmithB51P5L2
public import CFSG.Quasithin.Background.B5P4
public import CFSG.Quasithin.Background.SmithB51P5L3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

section Part5

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem alternatingNatural_of_part4b (hI : B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (h1 : B51Part1 G L) (hD : IsIntDirect (commV L) (fixV L) ⊤)
    (hnd : ¬ IsIntDirect (commV L) (fixV G) ⊤)
    (hS : ∃ n, (n = 6 ∨ n = 8) ∧ SymmetricNatural G (commV L) ⊥ n) :
    AlternatingNatural L (commV L) ⊥ 6 ∨ AlternatingNatural L (commV L) ⊥ 8 := by
  have hGL : G ≠ L := by
    rintro rfl
    exact hnd hD
  have hcase : B51Case1i G L := by
    rcases h1.2 with h' | h' | ⟨n, h'⟩ | h'
    · exact h'
    · exact absurd h'.1 hGL
    · exact absurd h'.1 hGL
    · exact absurd h'.1 hGL
  have hU : commV L ∈ IrrPlus L ⊤ := hcase.1
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf G
  have hGT : G = L ⊔ T := by
    rcases hcase.2.2 T hT with hh | ⟨hh, -⟩
    · exact absurd hh hGL
    · exact hh
  have hC : (⊥ : Subgroup V) = fixV L ⊓ commV L := by rw [inf_comm]; exact hD.2.symm
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  obtain ⟨A₀, hA₀G, hA₀T, B, hBA, hB⟩ := exists_section_offender' hV h hU hT hC
  have hb4 := b4Hyp_section' hV h hU hT.1 hT.2.1 hC
  have hconcl := hI.b42 (Sec (commV L) ⊥) (sq_eq_one_sec hV _ _) _ _ hb4 B hB
  have hcases := b42_cases hI.ident (sq_eq_one_sec hV _ _) hb4 hB hconcl
  rcases hcases with ⟨hJL, -, hQ⟩ | ⟨-, hbeta⟩
  · exact absurd (alpha_branch hI.i16 hI.nonsplit hV h hU hT hC hJL hQ) hGL
  obtain ⟨-, hLcomm, -, -⟩ := hbeta
  have hMG : L ⊔ T ≤ G := sup_le (le_G h) hT.1
  have hMU : L ⊔ T ≤ stabSub (commV L) := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub (⊥ : Subgroup V) := hMG.trans hGC
  have hLeq : L = ⁅L ⊔ T, L ⊔ T⁆ := by
    refine eq_of_autSec_eq hMU hMC hfM le_sup_left (commutator_le_self _) ?_
    rw [autSec_commutator hMU hMC]
    exact hLcomm
  obtain ⟨n, hn, hSn⟩ := hS
  rw [hGT] at hSn
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hA : AlternatingNatural ⁅L ⊔ T, L ⊔ T⁆ (commV L) ⊥ n := alternatingNatural_derived hn5 hSn
  rw [← hLeq] at hA
  rcases hn with rfl | rfl
  · exact Or.inl hA
  · exact Or.inr hA

theorem part5_of_inputs (hI : B51IrrInputs) (hG2 : AsB51G2Dual)
    (h2 : AsB51P2) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (h1 : B51Part1 G L) :
    B51Part5 G L := by
  by_cases htop : commV L ⊔ fixV G = ⊤
  · exact Or.inl htop
  right
  have hnd : ¬ IsIntDirect (commV L) (fixV G) ⊤ := fun hd => htop hd.1
  obtain ⟨hU, h4⟩ := part4_of_inputs hI h2 hV h h1 hnd
  have hL3 : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1 → fixV L ⊓ commV L = ⊥ :=
    fun hnat => P5.fixV_inf_commV_eq_bot_of_l3 hV h hU hnat htop
  refine ⟨hU, ?_, hL3⟩
  rcases h4 with hD | ⟨hD, hS, -⟩
  · obtain ⟨-, hlist⟩ := h2 V hV G L h h1 hD
    rcases hlist with ⟨n, hL2⟩ | ⟨n, hSp⟩ | ⟨n, hG⟩ | hA6 | hA8 | hG2' | hL3'
    · exact absurd (P5.sup_fixV_eq_top_of_l2 hV h h1 hL2) htop
    · exact Or.inl ⟨n, hSp⟩
    · exact absurd (hG2 V hV G L h hU (Or.inl ⟨n, hG⟩)) htop
    · exact Or.inr (Or.inl hA6)
    · exact Or.inr (Or.inr (Or.inl hA8))
    · exact absurd (hG2 V hV G L h hU (Or.inr hG2')) htop
    · exact Or.inr (Or.inr (Or.inr hL3'))
  · have hZ : fixV L ⊓ commV L = ⊥ := by rw [inf_comm]; exact hD.2
    rw [hZ]
    rcases alternatingNatural_of_part4b hI hV h h1 hD hnd hS with h6 | h8
    · exact Or.inr (Or.inl h6)
    · exact Or.inr (Or.inr (Or.inl h8))

end Part5

theorem asB51P5_of_p2 (hI : B51IrrInputs) (hG2 : AsB51G2Dual)
    (h2 : AsB51P2) : AsB51P5 :=
  fun _ _ _ hV _ _ h h1 => part5_of_inputs hI hG2 h2 hV h h1

end B5

end CFSG.Quasithin

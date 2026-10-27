module

public import CFSG.Quasithin.Background.FFC6T
public import CFSG.Quasithin.Background.FFC6K
public import CFSG.Quasithin.Background.FFC6M
public import CFSG.Quasithin.Background.FFC6O
public import CFSG.Quasithin.Background.FFC6R

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B59

section Assembly

theorem card_commV_eq_sixteen {M : Type} [CommGroup M] [Finite M] {K : Subgroup (MulAut M)}
    (hnat : BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 3 1) (hne : fixV K ⊓ commV K ≠ ⊥)
    (hle : Nat.card ↥(commV K) ≤ 2 ^ 4) : Nat.card ↥(commV K) = 2 ^ 4 := by
  obtain ⟨K', hK', hfin, hc, π, hπ⟩ := hnat
  have e := card_eq_of_realizes (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K')) rfl hπ
  rw [card_sec_nat, hc] at e
  have hZ : 1 < Nat.card ↥(fixV K ⊓ commV K) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  rw [show ((2 : ℕ) ^ 1) ^ 3 = 8 by norm_num] at e
  rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hle ⊢
  omega

theorem asB59_of_inputs
    (hP4 : AsB15Part4) (hB51 : AsB51) (hB42 : AsB42) (hA21 : AsA21SQTKSection)
    (h57 : B57Input) (hLast : B59Last) (hI16 : AsI16Cover) : AsB59 := by
  intro V _ _ G hc A L hmin hL hLA
  have hV := hc.hV
  have hb : B53Hyp G := hc.hyp
  have hO2 : pCoreOf 2 G = ⊥ := hb.1
  have hnG : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := B55.normalizes_comp hP4 hV hb.2.1 hL
  have hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun g hg l hl =>
    B19Aux.conj_mem_of_le_normalizer hnG hg hl
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hL hmin.1 hLA
  have hLU : L ≤ stabSub (W0 L A) := le_sup_left.trans hst
  have hfaithL := faithL hV hO2 hL hmin hLA
  obtain ⟨-, -, -, hLbH, -, hHb2, hoff, -, -⟩ := red_aut hV hL hmin.1 hLA
  have hno : ¬ ThreeRank2 ↥(Kr L A) := fun h =>
    h57 V G hc L hL (h.of_mulEquiv (resEquiv hLU hfaithL).symm)
  have hb51 : B51Hyp (Xr L A) (Kr L A) := b51Hyp_red hA21 hV hO2 hb hL hmin.1 hLA
  have hVM : ∀ v : ↥(W0 L A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨P1, P2, -, -, P5, -⟩ := hB51 ↥(W0 L A) hVM (Xr L A) (Kr L A) hb51
  have hne : Xr L A ≠ ⊥ := fun h => hoff.2.1 (le_bot_iff.1 (h ▸ hoff.1))
  have hnoX : ¬ ThreeRank2 ↥(Xr L A) := fun h => hno (threeRank2_sq hHb2 h)
  obtain ⟨-, hcases⟩ := P1
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨hirr, hcl⟩ := classify_i b58Inputs hb51.2.2.2.2.2 hne hLbH hHb2 hno P2 P5 hi
    rcases hcl with ⟨hXK, hα, hnat⟩ | ⟨hXK, m, hm, hnat3⟩ | ⟨hXK, hα, hfc, hS⟩
    · exact Or.inl (caseA b58Inputs hB42 hV hO2 hmin hL hLA hn hno hb51 hXK hirr hα hnat)
    · by_cases hC : fixV (Kr L A) ⊓ commV (Kr L A) = ⊥
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          (caseIV hLast hc hV hO2 hmin hL hLA hXK hC ⟨m, hm, hnat3⟩))))
      · have hm1 : m = 1 := by
          by_contra hne1
          have hm2 : 1 < m := by
            obtain ⟨k, hk⟩ := hm
            omega
          exact hC (hI16 ↥(W0 L A) hVM (Kr L A) hirr (Or.inl ⟨m, hm2, hnat3⟩))
        subst hm1
        have hα : commV (Kr L A) ⊔ fixV (Kr L A) = ⊤ := by
          rcases P5 with h | ⟨-, -, h⟩
          · rw [hXK] at h
            exact h
          · exact absurd (h hnat3) hC
        have hle := card_commV_le_sixteen hVM hirr hnat3
        have hcard := card_commV_eq_sixteen hnat3 hC hle
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (caseV hV hO2 hmin hL hLA hn hXK hirr hα hnat3 hcard))))
    · exact Or.inr (Or.inl (caseB hV hO2 hmin hL hLA hn hXK hα hfc hS))
  · exact Or.inr (Or.inr (Or.inl (caseD hV hO2 hmin hL hLA hn hno P5 hii)))
  · exact (false_of_case_iii hLbH hnoX hiii.2).elim
  · exact (false_of_case_iv hLbH hnoX hiv.2).elim

end Assembly

end B59

end FFC

end CFSG.Quasithin

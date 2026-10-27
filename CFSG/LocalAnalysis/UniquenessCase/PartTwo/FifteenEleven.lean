module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenElevenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Eleven_s_four (D : Data G) (h1217 : R1217 D) (h159 : R15_9 D) (hT8 : RT8 D)
    {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥)
    (hs4 : s15 D.M V₀ V hV L = 4) (hγ : 3 ≤ gamma15 D.M V₀ V hV L) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) (hvg : v ∈ conjSubgroup D.M g)
    (hcard : (suppAct (wConjG D.M V₀ V hV L g) v).ncard =
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({v} : Set G)))
    (hle : (suppAct (wConjG D.M V₀ V hV L g) v).ncard ≤ 3) : False := by
  have hY := E3.isElemAbelian_conjSubgroup hV g
  have hind := s15_Glue3_wConjG_indep D h.hyp151 hV hL hV1 g
  have hspan := s15_Glue3_wConjG_sSup D h1217 h.hyp151 hV hL g
  have hγΔ : ∀ E ∈ wConjG D.M V₀ V hV L g, rk ↥E = gamma15 D.M V₀ V hV L :=
    fun E hE => s15_Glue3_wConjG_rk D h.hyp151 hV hV1 g hE
  have ht : v * v = 1 := s15_Eleven_sq hV hcfg.v_mem
  have hperm : ∀ E ∈ wConjG D.M V₀ V hV L g, conjSubgroup E v ∈ wConjG D.M V₀ V hV L g :=
    fun E hE => s15_Glue3_wConjG_perm D hV hvg hE
  have hfix := s15_Support_eq_of_ncard_eq hY hind hspan hγΔ hγ ht hperm hcard
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hcent := hT8 V₀ V L h hL hV1 hs4 hγ g v hvg ht hle hfix a (hcfg.A_le haA) ha
  exact s15_Eleven_not_centralizer_le D h159 h hV hL hcfg haA hcent

theorem fifteen_eleven (D : Data G) (h1217 : R1217 D) (h159 : R15_9 D) (hT7 : RT7 D)
    (hT8 : RT8 D) : R15_11 D := by
  intro V₀ V L h hL i hi hC
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hV1 := s15_Eleven_v1_eq_bot D h hV hC
  refine ⟨hV1, ?_⟩
  by_contra hcon
  obtain ⟨hn1, hn2⟩ := not_or.1 hcon
  have hev := s15_Eleven_even D h hV hL hV1 hC
  have hspos := s15_Eleven_pos_s D h.hyp151 hV
  have h4 := s15_Eleven_h4 D h hV hL hev hn2
  obtain ⟨g, A, hAg, hAM, hmA, hAN⟩ := s15_Eleven_exists_A D h hV hL hV1 hC
  obtain ⟨B, v, hcfg⟩ := s15_Eleven_exists_Bv D h hV hL hV1 hAg hAM hmA hAN
  have hvg := s15_Eleven_v_mem_conj D hi hcfg h4
  obtain ⟨hc2, hcs, hcn, hn⟩ := s15_Eleven_support D h1217 h159 h hV hL hV1 hcfg hvg
  rcases s15_Eleven_cases hev hspos hi hc2 hcs hcn hn with hs2 | ⟨hs4, hi2, hc3, hn3⟩
  · have hγ : 4 ≤ gamma15 D.M V₀ V hV L := by
      by_contra hlt
      exact hn2 ⟨hs2, by omega⟩
    exact s15_Eleven_s_two D h1217 h159 hT7 h hV hL hV1 hs2 hγ hi h4 hAg hAM hmA hAN
  · have hγ : 3 ≤ gamma15 D.M V₀ V hV L := by
      have h2 := two_le_gamma15 D h.hyp151 hV hL
      by_contra hlt
      exact hn1 ⟨by omega, hs4, hi2⟩
    exact s15_Eleven_s_four D h1217 h159 hT8 h hV hL hV1 hs4 hγ hcfg hvg (by omega) (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

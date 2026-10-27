module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row9A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row9T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_case9_data (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h9 : Case168_9 D ⊥ V hV L) :
    ∃ (g : MulAut (Vtil ⊥ V hV)) (Z : Subgroup (MulAut (Vtil ⊥ V hV))),
      s16n9b_case9Two (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) g ∧
      s16n9b_case9Rank (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) 3 ∧
      rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)) = 9 ∧
      rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 18 ∧
      (∀ x ∈ lBar ⊥ V hV L, (∀ y ∈ lBar ⊥ V hV L, x * y = y * x) → x = 1) ∧
      (∃ a ∈ lBar ⊥ V hV L, orderOf a = 7) ∧
      Z ≤ Mbar D.M ⊥ V hV ∧ Nat.card ↥Z = 7 ∧
      (∀ x ∈ Mbar D.M ⊥ V hV, Z.map (MulAut.conj x).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ a ∈ lBar ⊥ V hV L, z * a = a * z) ∧
      (∀ z ∈ Z, ∀ w ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L),
        z w ∈ commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)) := by
  obtain ⟨g, htwo⟩ := s1614e3_case9_two D h1217 hV hc h9
  have hrank := s1614e3_case9_rank D h1217 hV hc h9
  have hL3 : IsL3 ↥(lBar ⊥ V hV L) 1 := h9.2.1
  have hs15 : s15 D.M ⊥ V hV L = 2 := h9.2.2.1
  have hsum := h9.2.2.2.1
  have hH : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hv1 : v1Sub D.M ⊥ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_case9 D hV rfl h9
  have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hW9 : rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L)) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrk18 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hH hv1 hc.ne_bot hs15 hsum
  have hcen : ∀ x ∈ lBar ⊥ V hV L, (∀ y ∈ lBar ⊥ V hV L, x * y = y * x) → x = 1 := by
    intro x hx hxcomm
    have h1 : (⟨x, hx⟩ : ↥(lBar ⊥ V hV L)) = 1 := by
      apply (s16c167_isPSL_simpleCentreless hL).center
      intro y
      exact Subtype.ext (hxcomm (y : MulAut (Vtil ⊥ V hV)) y.2)
    exact Subtype.ext_iff.mp h1
  have hA7 : ∃ a ∈ lBar ⊥ V hV L, orderOf a = 7 := by
    have hcard : Nat.card ↥(lBar ⊥ V hV L) = 168 := card_eq_168_of_isPSL_three_two hL
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, hx7⟩ := exists_prime_orderOf_dvd_card' (G := ↥(lBar ⊥ V hV L)) 7
      (by rw [hcard]; norm_num)
    exact ⟨(x : MulAut (Vtil ⊥ V hV)), x.2, (Subgroup.orderOf_coe x).trans hx7⟩
  obtain ⟨Z, hZM, hZcard, hZnorm, hZcomm, hZW, -, -⟩ := s1614e3_case9_frame D h1217 hV hc h9
  exact ⟨g, Z, htwo, hrank, hW9, hrk18, hcen, hA7, hZM, hZcard, hZnorm, hZcomm, hZW⟩

theorem s1614e3_row9_false (D : Data G) (h61 : UC6.R6_1 D) (h1217 : R1217 D)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    (h9 : Case168_9 D ⊥ V hV L) {U : Subgroup G} (hU : Min1614 D V U)
    (hUΓ : U ∉ gammaEleven D.M V) : False := by
  obtain ⟨g, Z, h2, hrank, hW9, hrk18, hcen, hA7, hZM, hZcard, hZnorm, hZcomm, hZW⟩ :=
    s1614e3_case9_data D h1217 hV hc h9
  have hT := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hk2 := s16c167_k_le_two D
  have hv1 : v1Sub D.M ⊥ V hV L = ⊥ := s16c167_v1Sub_eq_bot_of_case9 D hV rfl h9
  have hm3 : 3 ≤ mBar D.M ⊥ V hV := by
    obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
    have hL : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 hL3
    have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) |
        ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
      unfold s15 at hs15
      exact hs15
    have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar ⊥ V hV L)
        (commSub (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) (lBar ⊥ V hV L)) ⊥ 3 := hsum
    obtain ⟨hind, hsup⟩ := s16t_case9_directSum D h1217 hV hc.setting.hyp151 hv1 hc.ne_bot
    have hrk0 : rk ↥(wTil ⊥ V hV L) = 9 :=
      s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
    have hn2 : (conjSubs (Mbar D.M ⊥ V hV) (wTil ⊥ V hV L)).ncard = 2 :=
      s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrk18
    exact (s16c167_cfg9_abstract (X := Mbar D.M ⊥ V hV) (L := lBar ⊥ V hV L) hT hL hsum' hcls
      hn2 hind hsup).2.2.2
  have h7σ : (7 : ℕ) ∈ D.sig := by rw [h9.2.2.2.2]; exact Set.mem_singleton 7
  have hrk' : rk (Vtil ⊥ V hV) = 18 := by rwa [rk_top] at hrk18
  refine s1614_false_of_row D h61 hV hc hU hUΓ (by omega) (by omega) ?_
  intro t ht ht2 hkt W hW hWr
  obtain ⟨w, hwW, hw1, B, hBM, hB7, hBc, hwB⟩ :=
    s1614e3_row9_witness hT hrk18 h2 hrank hW9 hcen hA7 hZM hZcard hZnorm hZcomm hZW ht ht2 hW
      (by omega)
  exact ⟨w, hwW, hw1, 7, h7σ, B, hBM, hB7, hBc, hwB⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

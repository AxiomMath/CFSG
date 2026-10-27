module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3G
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3Nine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M6_noncyclic (D : Data G) (S : s16h_Std D)
    (hr3 : CFSG.Open.evenRank G = 3)
    (hσ : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) 3)
    (hrk : rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6)
    (hs : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2) (h3 : D.sig = {3}) :
    ∃ R : Subgroup G, R ≤ preBarSub D.M V₀ V h.hyp151.isElemAbelian
        (centSub (wTil V₀ V h.hyp151.isElemAbelian L)) ∧ IsPGroup 3 R ∧ ¬ IsCyclic ↥R := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp16.hyp125.pairFacts.le_normalizer h.hyp16.hyp125.pairFacts.le_normalizer₀
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hp3 : (3 : ℕ).Prime := by norm_num
  have h3mem : 3 ∈ D.sig := by rw [h3]; exact Set.mem_singleton 3
  have hc136 : Conc4_136 D V₀ V h.hyp151.isElemAbelian L := hc
  obtain ⟨E, hEM, hEea, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3) hp3
      (by rw [UC6.groupPRank_eq_pRank]; exact S.hx.three_le 3 h3mem)
  let X : Subgroup G := preBarSub D.M V₀ V h.hyp151.isElemAbelian
    (centSub (wTil V₀ V h.hyp151.isElemAbelian L))
  let Q : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)) :=
    barSub V₀ V h.hyp151.isElemAbelian E
  have hQA : Q ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian := barSub_mono V₀ V h.hyp151.isElemAbelian hEM
  have hQea : IsElemAbelian 3 Q :=
    (hEea.subgroupOf (stabTil V₀ V)).map (actTil V₀ V h.hyp151.isElemAbelian)
  by_cases hcase : (3 : ℕ) ^ 2 ≤ Nat.card ↥(E ⊓ X)
  · refine ⟨E ⊓ X, inf_le_right, (hEea.mono inf_le_left).isPGroup, ?_⟩
    exact s16c7_not_isCyclic_of_elemAbelian hp3 (hEea.mono inf_le_left) hcase
  · have hdvd : Nat.card ↥(E ⊓ X) ∣ 3 ^ 3 := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 3) hp3).1 hdvd
    have hklt : 3 ^ k < 3 ^ 2 := by
      calc 3 ^ k = Nat.card ↥(E ⊓ X) := hk.symm
        _ < 3 ^ 2 := not_le.1 hcase
    have hk2 : k < 2 := by
      by_contra h
      have h2 : 2 ≤ k := not_lt.1 h
      have hpow : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h2
      omega
    have hle3 : Nat.card ↥(E ⊓ X) ≤ 3 := by
      rw [hk]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 3 := by norm_num
    have hcard := s16h_card_mul_card_barSub_inf (V₀ := V₀) (V := V) (M := D.M) (E := E)
      h.hyp151.isElemAbelian hEM hM hMs (centSub (wTil V₀ V h.hyp151.isElemAbelian L))
    have hcard' : 3 * (9 * Nat.card ↥(Q ⊓ centSub (wTil V₀ V h.hyp151.isElemAbelian L))) ≤
        3 * Nat.card ↥Q := by
      calc 3 * (9 * Nat.card ↥(Q ⊓ centSub (wTil V₀ V h.hyp151.isElemAbelian L)))
          = Nat.card ↥E * Nat.card ↥(Q ⊓ centSub (wTil V₀ V h.hyp151.isElemAbelian L)) := by
            rw [hEcard]; ring
        _ = Nat.card ↥Q * Nat.card ↥(E ⊓ X) := hcard
        _ ≤ Nat.card ↥Q * 3 := Nat.mul_le_mul_left _ hle3
        _ = 3 * Nat.card ↥Q := by ring
    have hQ9 : 9 * Nat.card ↥(Q ⊓ centSub (wTil V₀ V h.hyp151.isElemAbelian L)) ≤ Nat.card ↥Q :=
      Nat.le_of_mul_le_mul_left hcard' (by norm_num)
    have hodd : Odd (Nat.card ↥(lBar V₀ V h.hyp151.isElemAbelian L)) := by
      rw [hLp.2]; norm_num
    have hfix : commSub (⊤ : Subgroup (Vtil V₀ V h.hyp151.isElemAbelian))
        (lBar V₀ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar V₀ V h.hyp151.isElemAbelian L) = ⊥ := by
      simpa [wTil, lBar] using
        s16c167_wTil_inf_fixV_eq_bot_of_odd h.hyp151.isElemAbelian L hodd
    obtain ⟨t, htM, ht2, ht1, htr, hW⟩ := hc
    obtain ⟨-, -, -, hLt, hind, -⟩ := s16h_conc4_133_of_prime_card hp3 hLp.2 hW
    obtain ⟨⟨x, hxA, hxL⟩, hpermAll⟩ :=
      c23a_two_conj (A := MulAut (Vtil V₀ V h.hyp151.isElemAbelian))
        (Mb := Mbar D.M V₀ V h.hyp151.isElemAbelian)
        (L := lBar V₀ V h.hyp151.isElemAbelian L) hs
    have hperm := (hpermAll x hxA hxL).2
    have hB : s16h_Z3Blocks (Mbar D.M V₀ V h.hyp151.isElemAbelian)
        (lBar V₀ V h.hyp151.isElemAbelian L)
        ((lBar V₀ V h.hyp151.isElemAbelian L).map (MulAut.conj x).toMonoidHom) x :=
      s16h_z3_blocks hW hind hxA hxL hperm
    have hLA : lBar V₀ V h.hyp151.isElemAbelian L ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian := by
      simpa [lBar] using barSub_mono V₀ V h.hyp151.isElemAbelian h.hyp151.le
    have hO2 : ∀ P : Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)),
        P ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian →
          (P.subgroupOf (Mbar D.M V₀ V h.hyp151.isElemAbelian)).Normal →
          IsPGroup 2 P → P = ⊥ :=
      fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp151.hyp125 hP hN h2
    have hm : E3.mParam (Mbar D.M V₀ V h.hyp151.isElemAbelian) ≤ 2 :=
      s16h_mParam_le_two_of_Z3_six_two (D := D) (S := S) (hσ := hσ) (h := h)
        (hc := hc136) (hLp := hLp) (hrk := hrk) (hs := hs) (h3 := h3)
    obtain ⟨P, hPle, hPe, hP9⟩ :=
      s16h_exists_elem_nine_of_Z3_six_two_nine
        (fun w => s15_Infra_vtil_sq_eq_one V₀ V h.hyp151.isElemAbelian w)
        hB hLA hLp.2 hrk hfix hO2 hm htM ht2 htr hLt hQA hQea hQ9
    have hPM : P ≤ Mbar D.M V₀ V h.hyp151.isElemAbelian := hPle.trans inf_le_left
    have hP9' : 3 ^ 2 ≤ Nat.card ↥P := by
      have hnine : (3 : ℕ) ^ 2 = 9 := by norm_num
      rwa [hnine]
    obtain ⟨R, hRle, hRp, hRnc⟩ :=
      s16h_exists_noncyclic_le_preBarSub h.hyp151.isElemAbelian hMs hp3 P hPM hPe hP9'
    refine ⟨R, ?_, hRp, hRnc⟩
    have hPcent : P ≤ centSub (wTil V₀ V h.hyp151.isElemAbelian L) :=
      hPle.trans inf_le_right
    intro g hg
    obtain ⟨hgM, hgs, hgx⟩ :=
      (mem_preBarSub D.M V₀ V h.hyp151.isElemAbelian P).1 (hRle hg)
    exact (mem_preBarSub D.M V₀ V h.hyp151.isElemAbelian
      (centSub (wTil V₀ V h.hyp151.isElemAbelian L))).2
      ⟨hgM, hgs, hPcent hgx⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

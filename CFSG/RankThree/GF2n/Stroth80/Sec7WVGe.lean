module

public import CFSG.RankThree.GF2n.Stroth80.Sec7NoInvariantFormProof
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommForm
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step2
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix


theorem sec7WVGe_of (h34 : Stroth34Statement) (hW : Sec7WVOrderStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (h52c : Stroth52cStatement) :
    Sec7WVGeStatement := by
  intro G _ _ M Q Z B hc n t hs hp
  classical
  by_contra hlt
  have hn10 : n < 10 := by omega
  obtain ⟨y, hy, hn⟩ := (hW G M Q Z B hc n t hs 3 (by norm_num)).2 hp (le_refl 3)
  have hy1 : y = 1 := by
    norm_num at hn
    omega
  subst hy1
  have hn8 : n = 8 := by
    norm_num at hn
    omega
  subst hn8
  obtain ⟨r, hr⟩ := hA G M Q Z B hc 8 t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hQc : Nat.card Q = Nat.card Z ^ (2 * 8 + 1) := hs.toSec5.width
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    le_sup_right.trans hr.gen.ge
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  have hWn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx y hy =>
    sec7WVOrd_conj_mem hc ht hx hy
  obtain ⟨-, hNW⟩ := h52a G M Q Z B hc 8 t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hd := h52b G M Q Z B hc 8 t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := hd.1.trans hd.2.1
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc 8 t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl) hWQ hZV
  have hV := n12N_card_V hc t 3 (by norm_num) (Or.inl hp)
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc 8 t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV)
    subst hmm
    have hsecWV : SecHyp (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
        (Vt M (LB M Q B) B Z t) := SecHyp.of_isOppDecomp hd hWn hVn
    obtain ⟨Y, iY, iD, κ, hκ, hkerY⟩ := exists_sectionModule_ker hker hsecWV hNW
    haveI : Finite Y := hκ.finite
    have hdec := isCompl_fixedSub_of_isOppDecomp hWn hκ hd hLR hL2R
    have hWcard := natCard_eq_of_isSecMod hVW hκ
    have hYcard : Nat.card Y = Nat.card K ^ 4 := by
      rw [hKZ]
      have hVc : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ (2 * 3) := hV
      have e1 : Nat.card Z ^ 14 * Nat.card Z ^ 4 = Nat.card Z ^ 14 * Nat.card Y := by
        calc Nat.card Z ^ 14 * Nat.card Z ^ 4 = Nat.card Q * Nat.card Z := by
              rw [hQc]
              ring
          _ = Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
              Nat.card ↥(Vt M (LB M Q B) B Z t) := hchi
          _ = Nat.card Z ^ 14 * Nat.card Y := by
              rw [hWcard, hVc]
              ring
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) e1).symm
    obtain ⟨lam, hlam⟩ := n12Lam_holds G M Q Z B hc
    obtain ⟨hZQ, hZc, hcomm, hsq⟩ := n12Q_holds G M Q Z B hc
    have hnd := n12Lemma1_holds G M Q Z B hc lam hlam
    have hW2 := (n12Lemma2_of h34 h52c G M Q Z B hc 8 t hs).2 lam hlam
    have hrad := lamOrth_radical_le lam hZQ hZc hcomm hsq hnd hZV hVW hWQ hW2
    have hVW1 : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅v, w⁆ = 1 := by
      intro v hv w hw
      have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact this
    have hRZ : ∀ x ∈ Rt M (LB M Q B) t, ∀ z ∈ Z, x * z * x⁻¹ = z := by
      intro x hx z hz
      have := Subgroup.mem_centralizer_iff.mp (hc.Rt_le_H0 t hx).2 z hz
      rw [← this]
      group
    obtain ⟨β, hinv, hnd'⟩ := exists_commForm_WV lam hZQ hZc hcomm hZV hVW hWQ hVW1 hκ hRZ hWn hrad
    exact noInvariantForm_frame_hom (hKZ ▸ (by omega : 4 ≤ Nat.card Z)) φ hrange hu hu' hu0 huu' Y
      hκ.two hkerY ((LB M Q B).subgroupOf (Rt M (LB M Q B) t))
      ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t))
      (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hdec hYcard ⟨β, hinv, hnd'⟩
  · exfalso
    have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV)
    have hMinusM : OmegaMinusNat hc t 3 := by
      rw [← hmm]
      exact ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩
    exact omegaSignStatement_holds G M Q Z B hc t 3 (by norm_num) hp hMinusM

end CFSG.RankThree.GF2n.Stroth80

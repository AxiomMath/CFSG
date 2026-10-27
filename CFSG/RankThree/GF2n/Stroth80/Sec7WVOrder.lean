module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSecOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step6

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix


theorem sec7WVOrd_conj_mem {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    {x : G} (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    r * x * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hVn : r ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hr
  have hrM : r ∈ M := hc.Rt_le_M t hr
  unfold Wt at hx ⊢
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hrM) x).mp hxQ
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := by
      refine (Subgroup.mem_normalizer_iff.mp hVn (r⁻¹ * v * r)).mpr ?_
      rw [show r * (r⁻¹ * v * r) * r⁻¹ = v by group]
      exact hv
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC (r⁻¹ * v * r) hu
    calc v * (r * x * r⁻¹) = r * (r⁻¹ * v * r * x) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * v * r)) * r⁻¹ := by rw [hcomm]
      _ = r * x * r⁻¹ * v := by group

theorem sec7WVOrd_lt {q n m N Qc : ℕ} (hq : 4 ≤ q) (hQc : Qc = q ^ (2 * n + 1))
    (hN : N * q ^ (4 * m) = Qc ^ 2) (hlarge : Qc * q < N) : 4 * m < 2 * n := by
  subst hQc
  by_contra hcon
  have h3 : q ^ (2 * n + 1) * q * q ^ (4 * m) < N * q ^ (4 * m) :=
    mul_lt_mul_of_pos_right hlarge (pow_pos (by omega) _)
  have e1 : q ^ (2 * n + 1) * q * q ^ (4 * m) = q ^ (2 * n + 2 + 4 * m) := by ring
  have e2 : (q ^ (2 * n + 1)) ^ 2 = q ^ (4 * n + 2) := by ring
  rw [hN, e1, e2] at h3
  exact absurd h3 (not_lt.2 (Nat.pow_le_pow_right (by omega) (by omega)))

theorem sec7WVOrd_exp {q n m e k Qc V W : ℕ} (hq : 4 ≤ q) (hQc : Qc = q ^ (2 * n + 1))
    (hV : V = q * q ^ (2 * m)) (hchi : Qc * q = W * V) (hW : W = V * q ^ (e * k)) :
    2 * n = 4 * m + e * k := by
  subst hQc
  subst hV
  subst hW
  have hp : q ^ (2 * n + 2) = q ^ (4 * m + 2 + e * k) := by
    calc q ^ (2 * n + 2) = q ^ (2 * n + 1) * q := by ring
      _ = q * q ^ (2 * m) * q ^ (e * k) * (q * q ^ (2 * m)) := hchi
      _ = q ^ (4 * m + 2 + e * k) := by ring
  have h2 : 2 * n + 2 = 4 * m + 2 + e * k := Nat.pow_right_injective (by omega) hp
  omega

theorem sec7WVOrder_of (hNO : Sec7NOrderStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h52c : Stroth52cStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Sec7WVOrderStatement := by
  intro G _ _ M Q Z B hc n t hs m hm2
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
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
  obtain ⟨-, hPN⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc n t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl)
    hWQ sec39_Z_le_Vt
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  refine ⟨fun hMinus => ?_, fun hPlus _ => ?_⟩
  · have hV := n12N_card_V hc t m hm2 (Or.inr hMinus)
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      have hPlusM : OmegaPlusNat hc t m := by
        rw [← hmm]
        exact ⟨K, hKf, hKfin, hKZ, hnat⟩
      exact omegaSignStatement_holds G M Q Z B hc t m hm2 hPlusM hMinus
    · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaMinus (ElemMatrixIso.minus hm' hirr) hm'
        (isMinus_quadMinus (by omega) hirr) φ hrange hker hWn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu')
      rw [hKZ, hmm] at hk
      have hNc := hNO G M Q Z B hc n t hs m hm2 (Or.inr hMinus)
      have hlt := sec7WVOrd_lt hq4 hQc hNc hs.large
      have hexp := sec7WVOrd_exp (e := 2 ^ m) hq4 hQc hV hchi hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero, Nat.add_zero] at hexp
          omega
        · omega
      exact ⟨k, hk1, by rw [Nat.mul_comm k (2 ^ m)]; exact hexp⟩
  · have hV := n12N_card_V hc t m hm2 (Or.inl hPlus)
    rcases hcases with
      ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
      ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
    · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      obtain ⟨k, hk⟩ := stroth_2_1_ii_secOmegaPlus (ElemMatrixIso.plus hm') hm'
        (isPlus_quadPlus m') φ hrange hker hWn hVn hPN hd hLR hL2R hu hu' huu'
        (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
        (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu')
      rw [hKZ, hmm] at hk
      have hNc := hNO G M Q Z B hc n t hs m hm2 (Or.inl hPlus)
      have hlt := sec7WVOrd_lt hq4 hQc hNc hs.large
      have hexp := sec7WVOrd_exp (e := 2 ^ (m - 1)) hq4 hQc hV hchi hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero, Nat.add_zero] at hexp
          omega
        · omega
      exact ⟨k, hk1, by rw [Nat.mul_comm k (2 ^ (m - 1))]; exact hexp⟩
    · exfalso
      have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
      have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
      have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hι] at hcard
      have hmm : m' = m := sec7_pin_dim hq (hcard.symm.trans hV)
      have hMinusM : OmegaMinusNat hc t m := by
        rw [← hmm]
        exact ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩
      exact omegaSignStatement_holds G M Q Z B hc t m hm2 hPlus hMinusM

end CFSG.RankThree.GF2n.Stroth80

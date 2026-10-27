module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Core
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS6

theorem dim_arith {z a v u q1 w T n m : ℕ} (hz : 2 ≤ z) (ha : a = z ^ (2 * n + 1))
    (hv : v = z ^ (m + 1)) (h1 : a * T = w * u) (h2 : a * z = q1 * u) (h3 : w * v = a * z)
    (hvT : v ≤ T) (huq : u ≤ q1) : 2 * m ≤ n := by
  have ha0 : 0 < a := by rw [ha]; exact pow_pos (by omega) _
  have e1 : T * v = z * u := by
    apply Nat.eq_of_mul_eq_mul_left ha0
    calc a * (T * v) = (a * T) * v := by ring
      _ = (w * u) * v := by rw [h1]
      _ = (w * v) * u := by ring
      _ = (a * z) * u := by rw [h3]
      _ = a * (z * u) := by ring
  have e2 : v * v ≤ z * u := by
    calc v * v ≤ T * v := Nat.mul_le_mul_right v hvT
      _ = z * u := e1
  have e3 : u * u ≤ a * z := by
    calc u * u ≤ q1 * u := Nat.mul_le_mul_right u huq
      _ = a * z := h2.symm
  have e4 : (v * v) * (v * v) ≤ z * z * (a * z) := by
    calc (v * v) * (v * v) ≤ (z * u) * (z * u) := Nat.mul_le_mul e2 e2
      _ = z * z * (u * u) := by ring
      _ ≤ z * z * (a * z) := Nat.mul_le_mul_left _ e3
  have e5 : z ^ (4 * (m + 1)) ≤ z ^ (2 * n + 4) := by
    have e6 : (v * v) * (v * v) = z ^ (4 * (m + 1)) := by rw [hv]; ring
    have e7 : z * z * (a * z) = z ^ (2 * n + 4) := by rw [ha]; ring
    rw [← e6, ← e7]
    exact e4
  have := (Nat.pow_le_pow_iff_right (by omega : 1 < z)).mp e5
  omega

end HS6

theorem stroth6SLDim_of_34 (h34 : Stroth34Statement) : Stroth6SLDimStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hsl
  have hSL : SLMNat hc t m := HS6.slMNat_of_alt hsl
  have hSLN : SLNat hc t := hSL.toSLNat hm
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have htM : t ∈ M := hc.LB_le_M hs.mem
  let V : Subgroup G := Vt M (LB M Q B) B Z t
  let W : Subgroup G := Wt Q V
  let U : Subgroup G := Ut Q Z t
  let T : Subgroup G := Tt Q Z V t
  have hVT : V ≤ T := hc.Vt_le_Tt_of_SLNat hs h35 hSLN
  have hUQ : U ≤ Q := hc.Ut_le_Q htM
  have hTQ : T ≤ Q := Tt_le_Q hc.Z_le_Q (hc.hyp.Q_normal.2 htM)
  have hTU : T ≤ U := sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  have hUN : U ≤ Subgroup.normalizer (T : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun u hu x hx => ?_
    have hcomm : ⁅u, x⁆ ∈ Z := CFSG.RankThree.GF2n.Smith81.comm_mem_Z hc.hyp (hUQ hu) (hTQ hx)
    have hconj : u * x * u⁻¹ = ⁅u, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hconj]
    exact T.mul_mem (show ⁅u, x⁆ ∈ T from Subgroup.mem_sup_right hcomm) hx
  haveI : ((Tt Q Z V t).subgroupOf (Ut Q Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hUN
  have hchi : IsChiIso Q (Rt M (LB M Q B) t) W U T t := hc.isChiIso_Wt_Ut_Tt hs.mem hVT
  have h1 : Nat.card Q * Nat.card T = Nat.card W * Nat.card U :=
    card_mul_card_of_isChiIso hchi inf_le_left hTU
  have hU1 : U ≤ Q1 hc t := by
    intro x hx
    have h := hc.Ut_eq_center_Q1 hs.mem
    change x ∈ Ut Q Z t at hx
    rw [h] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hQ1Q : Q1 hc t ≤ Q := fun x hx => ((hc.mem_Q1_iff htM).mp hx).1
  haveI : (Z.subgroupOf (Ut Q Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hUQ.trans (hc.hyp.Q_normal.1.trans hc.hyp.Z_normal.2))
  have hchi' : IsChiIso Q (Rt M (LB M Q B) t) (Q1 hc t) U Z t := hc.isChiIso_Q1_Ut hs.mem
  have h2 : Nat.card Q * Nat.card Z = Nat.card (Q1 hc t) * Nat.card U :=
    card_mul_card_of_isChiIso hchi' hQ1Q le_sup_right
  have h3 : Nat.card W * Nat.card V = Nat.card Q * Nat.card Z := hc.card_Wt_mul_card_Vt t
  have hz : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  exact HS6.dim_arith hz hs.width (SLMNat.card_Vt hSL) h1 h2 h3 (Subgroup.card_le_of_le hVT)
    (Subgroup.card_le_of_le hU1)

end CFSG.RankThree.GF2n.Stroth80

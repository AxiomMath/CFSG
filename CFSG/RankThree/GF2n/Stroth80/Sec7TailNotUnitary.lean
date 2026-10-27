module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailNotUnitaryAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneBar
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogCtx

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem step717NotUnitary_of_inputs
    (h34 : Stroth34Statement) (h311a : Stroth311aStatement) (h713 : Stroth713Statement)
    (hLevi : UnitarySixLeviStatement) (hOutU : OutSolvableUnitarySixStatement) :
    Step717NotUnitaryStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 hU
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (Q := Q) hQR
  have hn4 : ¬ OmegaPlusNat hc t 4 := fun h => by have := hp3.eq_of_plus h; omega
  have hF := h713 G M Q Z B hc n t hs hn4 Z0 hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hRK : Rt M (LB M Q B) t ≤ NormH0 M Z Z0 := fun ρ hρ =>
    Subgroup.mem_inf.mpr ⟨hc.Rt_le_H0 t hρ, IsCentrePre.mem_normalizer hZ0 hnormR hρ⟩
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hHM : H0 M Z ≤ M := fun x hx => hx.1
  have hN2 := sec7_CN_pgroup_bar h34 h311a hc hs
  have hNH : bar M Q (hc.CN t) ≤ bar M Q (H0 M Z) := bar_mono' (hNR.trans hRH)
  have hKH : bar M Q (NormH0 M Z Z0) ≤ bar M Q (H0 M Z) :=
    bar_mono' (S := NormH0 M Z Z0) (T := H0 M Z) (fun x hx => hx.1)
  have hNK : bar M Q (hc.CN t) ≤ bar M Q (NormH0 M Z Z0) := bar_mono' (hNR.trans hRK)
  have hCKN := Ctx.yCKN hc hF hNK hKH
  have hNn := Ctx.yNn hc hF hNK hKH
  have hNRy : (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hNR (Subgroup.mem_subgroupOf.mp hx))
  have hRKy : (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hRK (Subgroup.mem_subgroupOf.mp hx))
  have hN2y : IsPGroup 2 ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  obtain ⟨K₀, hKf, hKfin, hK₀, hnormN, hquot⟩ := Ctx.recog_quot_equiv hc hp3
  haveI := hnormN
  obtain ⟨hnormY, hquotY⟩ := nonempty_quot_equiv_bar (M := M) (Q := Q) (H := H0 M Z) hQN hNR
    hRH hHM hquot
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ f : ℕ, 1 ≤ f ∧ Nat.card Z = 2 ^ f := by
    obtain ⟨g, k, hg, -⟩ := hc.hyp.cp
    refine ⟨g, ?_, hg⟩
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0, pow_zero] at hg
      omega
    · exact h0
  exact notUnitary_abstract hLevi hOutU (Nat.card Z) hq4 hq2 hU
    ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))
    ((bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z))) hNRy hRKy hN2y hNn hCKN K₀ hK₀
    ⟨hnormY, hquotY⟩

end CFSG.RankThree.GF2n.Stroth80

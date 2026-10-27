module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XPart
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExY
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XD10

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

variable {L : ZLab Γ G}

theorem exists_good_partner (F : FanTree Γ G) (h7 : Fan7 F L)
    (hN1 : ∀ (A : V) (D' : D10Set L A) (δ'' : V), D'.IsYPair δ'' → FixedPair D')
    {α : V} (D₀ : D10Set L α) {w₀ : G} (hw : IsW1 D₀ w₀) :
    ∃ η' : V, D₀.IsYPair η' ∧ w₀ • ((D₀.x ^ 2)⁻¹ • η') = (D₀.x ^ 2)⁻¹ • η' := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have hA5 : valence Γ (D₀.alpha 2) = 5 := D₀.valence_alpha F 2
  have hAξ : Γ.Adj (D₀.alpha 2) (D₀.xi 2) := D₀.adj_alpha_xi 2
  have hξδ : Γ.Adj (D₀.xi 2) (D₀.delta 2) := D₀.adj_xi_delta 2
  have hAδ : D₀.alpha 2 ≠ D₀.delta 2 := (D₀.delta_ne_alpha 2).symm
  have hAβ : Γ.Adj (D₀.alpha 2) (D₀.beta 2) := (D₀.adj_beta_alpha 2).symm
  have hβα : Γ.Adj (D₀.beta 2) α := (D₀.adj_start_beta 2).symm
  have hAα : D₀.alpha 2 ≠ α := D₀.alpha_ne_start 2
  obtain ⟨Q0, hQ00, hQ01, hQ02⟩ := exists_arc4_of_three F hAξ hξδ hAδ
  obtain ⟨Q2, hQ20, hQ21, hQ22⟩ := exists_arc4_of_three F hAβ hβα hAα
  have hne : Q0.vert 1 ≠ Q2.vert 1 := by
    rw [hQ01, hQ21]
    exact ((D₀.P 2).nb 1 (by norm_num)).symm
  obtain ⟨D', hD'0, hD'2⟩ := exists_d10Set_arcs h71a h71c hA5 Q0 Q2 hQ00 hQ20 hne
  have hα0 : D'.alpha 0 = D₀.delta 2 := by
    show (D'.P 0).vert 2 = _
    rw [hD'0 2 (by norm_num), hQ02]
  have hα2 : D'.alpha 2 = α := by
    show (D'.P 2).vert 2 = _
    rw [hD'2 2 (by norm_num), hQ22]
  have hβ2 : D'.beta 2 = D₀.beta 2 := by
    show (D'.P 2).vert 1 = _
    rw [hD'2 1 (by norm_num), hQ21]
  obtain ⟨δ'', hδ''⟩ := exists_isYPair h7 D'
  have hwδ : w₀ • D₀.delta 2 = D₀.delta 2 := (Arc.mem_stab G).1 hw.fixes 4 (by norm_num)
  have hwα : w₀ • α = α := by
    have := (Arc.mem_stab G).1 hw.fixes 0 (by norm_num)
    rwa [D₀.start 2] at this
  obtain ⟨m, hm, hwm⟩ := hN1 _ D' δ'' hδ'' w₀ (by rw [hα0]; exact hwδ) (by rw [hα2]; exact hwα)
    (orderOf_w_eq_four F h71c hw) (by rw [hα0, hα2]; exact hw.sq)
  have hZ : IsZ2Pair Γ G α (D₀.alpha 2) (D₀.beta 2) (D₀.delta 2) (D'.alpha m) 2 := by
    have := D'.isZ2Pair_alpha F h71c (i := 2) (j := 0) (k := m) (by decide)
      (by rcases hm with rfl | rfl <;> decide) (by rcases hm with rfl | rfl <;> decide)
    rwa [hα2, hβ2, hα0] at this
  have hsh : ∀ n, n ≤ 4 → D₀.x ^ 2 • (D₀.P 2).vert n = (D₀.P 0).vert n := fun n hn =>
    (inv_smul_eq_iff.1 (D₀.x_pow_inv_smul_vert F h71c 2 0 hn)).symm
  have e1 : D₀.x ^ 2 • α = α := MulAction.mem_stabilizer_iff.1
    (Subgroup.pow_mem _ (D₀.x_mem_stabilizer F h71c) 2)
  have e2 : D₀.x ^ 2 • D₀.alpha 2 = D₀.alpha 0 := hsh 2 (by norm_num)
  have e3 : D₀.x ^ 2 • D₀.beta 2 = D₀.beta 0 := hsh 1 (by norm_num)
  have e4 : D₀.x ^ 2 • D₀.delta 2 = D₀.delta 0 := hsh 4 (by norm_num)
  refine ⟨D₀.x ^ 2 • D'.alpha m, ?_, ?_⟩
  · have h := IsZ2Pair.smul F (D₀.x ^ 2) hZ
    rw [e1, e2, e3, e4] at h
    exact h
  · rw [inv_smul_smul]
    exact hwm

end P4X

end CFSG.Quasithin.Fan86

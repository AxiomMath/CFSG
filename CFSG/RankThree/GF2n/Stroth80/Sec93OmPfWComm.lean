module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec94ConjV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_Wt_le_Vt_of_card (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {x : G} (hxL : x ∈ LB M Q B) (hxN : x ∉ hc.CN t)
    (hUx : Nat.card ↥(Ut Q Z x) = Nat.card ↥(Vt M (LB M Q B) B Z t)) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hxR : x ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hxL
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun v hv =>
    ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun h hh =>
      hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ h hh v hv⟩
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hβV : ∀ y ∈ Vt M (LB M Q B) B Z t, x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hxR) y).mp hy
  have hβW : ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t), x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun y hy => conj_mem_Wt (hc.hyp.Q_normal.2 hxM) (hc.Rt_normalizes_Vt ht hxR) hy
  obtain ⟨C₂, hC₂⟩ := HS9.exists_subgroup_comm_mem_Vt91 hc hZV hVQ hWQ x
  have hC₂W : C₂ ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun y hy => ((hC₂ y).mp hy).1
  have hVC₂ : Vt M (LB M Q B) B Z t ≤ C₂ := fun v hv => (hC₂ v).mpr ⟨hVW hv, by
    have e : ⁅x, v⁆ = (x * v * x⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hβV v hv) ((Vt M (LB M Q B) B Z t).inv_mem hv)⟩
  have hχ := stroth91c_of_34 h34 G M Q Z B hc n t hs (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  obtain ⟨C₃, hWC₃, hC₃Q, hC₃iff, hC₃card⟩ := HS9.exists_chiTransport91 hc ht hχ hxR
  have hfilt := card_Q1_mul_le_filtration hc hxM hZV hVW hWQ hβV hβW hVC₂ hC₂W
    (fun y hy => ⟨fun h => ((hC₂ y).mp h).2, fun h => (hC₂ y).mpr ⟨hy, h⟩⟩) hWC₃ hC₃Q hC₃iff
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
  haveI := hn
  have h3 := HS9.card_Vt_inf_Q1_plus4_91 P ht hxL hxN
  have hq : 0 < Nat.card Z := Nat.card_pos
  have hWpos : 0 < Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := Nat.card_pos
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs5.width
  have hVc : Nat.card (Vt M (LB M Q B) B Z t) = Nat.card Z ^ 5 := hs.card_V
  have hWc : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * n - 3) :=
    hs.card_W h34
  have hn3 : 2 < n := hs5.n_gt
  have hQ1Q : Q1 hc x ≤ Q := fun y hy => hy.1
  haveI : (Z.subgroupOf (Ut Q Z x)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q hxM hv)))
  have hQ1U : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc x) * Nat.card ↥(Ut Q Z x) :=
    card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut hxL) hQ1Q (le_sup_right : Z ≤ Ut Q Z x)
  have h5 : 0 < Nat.card Z ^ 5 := by positivity
  have hQ1 : Nat.card ↥(Q1 hc x) = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := by
    have h := hQ1U
    rw [hUx, hVc, hQc] at h
    have e1 : Nat.card Z ^ (2 * n - 3) * Nat.card Z ^ 5 =
        Nat.card Z ^ (2 * n + 1) * Nat.card Z := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [hWc]
    refine Nat.eq_of_mul_eq_mul_right h5 ?_
    rw [e1]
    exact h.symm
  have hC3 : Nat.card ↥C₃ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 2 := by
    have h := hC₃card
    rw [h3] at h
    refine Nat.eq_of_mul_eq_mul_right hq ?_
    rw [h]
    ring
  have hle : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) ≤ Nat.card ↥C₂ := by
    have hpos : 0 < Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 *
          Nat.card (Wt Q (Vt M (LB M Q B) B Z t))
        = Nat.card ↥(Q1 hc x) * Nat.card (Vt M (LB M Q B) B Z t) *
            Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) := by rw [hQ1, hVc]
      _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc x) * Nat.card ↥C₂ * Nat.card ↥C₃ := hfilt
      _ = Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card Z ^ 5 * Nat.card ↥C₂ := by
        rw [h3, hC3]
        ring
  have hCW : C₂ = Wt Q (Vt M (LB M Q B) B Z t) := Subgroup.eq_of_le_of_card_ge hC₂W hle
  intro w hwW
  have hwC : w ∈ C₂ := by rw [hCW]; exact hwW
  exact ((hC₂ w).mp hwC).2

end HS9

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.GF2n.Stroth80.Sec52Orders
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootAux
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_centralizer_QB_Wt (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hZc : Sec7CentreMpStatement) (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {y : G} (hy : y ∈ LB M Q B)
    (hcomm : ∀ x ∈ QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t), ⁅y, x⁆ ∈ Z) : y ∈ Z0 := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨K, fK, finK, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hcard := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hZQB : Z ≤ QB B := hc.Z_le_QB.1
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hZQB
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    sec7ctr_Vt_le_Wt h34 hc hs5
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec39_Z_le_Vt.trans hVW
  obtain ⟨U, hU⟩ := hc.exists_submodule_inf_QB hs5.width hcard.2.2.2 h
  set Y : Subgroup G := QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t) with hY
  have hZY : Z ≤ Y := le_inf hZQB hZW
  have hYQ : Y ≤ Q ⊓ QB B := fun x hx => ⟨hWQ hx.2, hx.1⟩
  have hBY : B ≤ Y := fun x hx => ⟨hc.B_le_QB hx, hVW (hc.B_le_Vt ht hx)⟩
  have hYsc : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y := by
    intro c e he
    obtain ⟨y₀, hy₀, hy₀Q, rfl⟩ := he
    have h1 : c • M₀.π y₀ ∈ U := U.smul_mem c ((hU _).mpr (M₀.pi_mem_img (hYQ hy₀) hy₀Q))
    have h2 : c • M₀.π y₀ ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) :=
      smul_mem_img_Wt M₀ h.reg hVQ c (M₀.pi_mem_img hy₀.2 hy₀Q)
    obtain ⟨y', hy'Q, hy'⟩ := M₀.π_surj (c • M₀.π y₀)
    rw [← hy'] at h1 h2
    have h1' : y' ∈ Q ⊓ QB B := (M₀.mem_img_iff hZX hy'Q).mp ((hU _).mp h1)
    have h2' : y' ∈ Wt Q (Vt M (LB M Q B) B Z t) := (M₀.mem_img_iff hZW hy'Q).mp h2
    exact ⟨y', ⟨h1'.2, h2'⟩, hy'Q, hy'⟩
  obtain ⟨b, hbY, hb0, hB, hel3, hel4, hcount⟩ := hc.elation_package hs5.width hs5.n_gt
    hs5.noA2 hcard.2.2.1 hcard.2.2.2 h hBY hYQ hYsc
  obtain ⟨T, hT⟩ := hc.exists_centSub (Y : Set G)
  have hcnt := hcount T hT
  have hYcard : Nat.card ↥Y = Nat.card Z ^ n := card_QB_inf_Wt h34 hRoot hc hs5 hs.omegaNat
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hK2 : 2 ≤ Nat.card K := by
    rw [hKZ]
    have := hc.hyp.q4
    omega
  have hYimg : Nat.card ↥Z * Nat.card (M₀.img Y) = Nat.card Z ^ n := by
    rw [← M₀.card_eq (hYQ.trans inf_le_left) hZY, hYcard]
  have hdim : Module.finrank K (imgSub M₀ Y hYsc) = n - 1 := by
    have h1 : Nat.card (imgSub M₀ Y hYsc) = Nat.card (M₀.img Y) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => mem_imgSub)
    have e : Nat.card Z ^ n = Nat.card Z * Nat.card Z ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      have := hs5.n_gt
      omega
    have h2 : Nat.card Z * Nat.card (M₀.img Y) = Nat.card Z * Nat.card Z ^ (n - 1) := by
      rw [hYimg, e]
    have h3 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    have h4 : Nat.card K ^ Module.finrank K (imgSub M₀ Y hYsc) = Nat.card K ^ (n - 1) := by
      rw [← Module.natCard_eq_pow_finrank (K := K), h1, h3, hKZ]
    exact Nat.pow_right_injective hK2 h4
  rw [hdim, hcard.2.2.1, hKZ] at hcnt
  have hn3 : 3 ≤ n := hs5.n_gt
  have hTcard : Nat.card T = Nat.card Q * Nat.card Z := by
    have hpos : 0 < Nat.card Z ^ (n - 1 - 1) := pow_pos Nat.card_pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    have e : Nat.card Z ^ (n - 1) = Nat.card Z ^ (n - 1 - 1) * Nat.card Z := by
      rw [← pow_succ]
      congr 1
      omega
    calc Nat.card T * Nat.card Z ^ (n - 1 - 1) = Nat.card Q * Nat.card Z ^ (n - 1) := hcnt.symm
      _ = Nat.card Q * Nat.card Z * Nat.card Z ^ (n - 1 - 1) := by rw [e]; ring
  have hZ0T : Z0 ≤ T := by
    intro z hz
    obtain ⟨hzL, hzW⟩ := hZc G M Q Z B hc n t hs Z0 hZ0 z hz
    exact (hT z).mpr ⟨hzL, fun y' hy' => hzW y' hy'.2⟩
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z := hZcard G M Q Z B hc n t hs Z0 hZ0
  have heq : Z0 = T := Subgroup.eq_of_le_of_card_ge hZ0T (by rw [hTcard, hZ0card])
  rw [heq]
  exact (hT y).mpr ⟨hy, hcomm⟩

end CFSG.RankThree.GF2n.Stroth80

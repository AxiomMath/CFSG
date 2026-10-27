module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Pts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem smul_mem_img_cent (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hcardL : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1))
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (h : GlobalModelData M Q Z γ M₀) {D : Subgroup G} (hD : D ≤ LB M Q B) (c : K) {e : M₀.E}
    (he : e ∈ M₀.img (Q ⊓ QB B ⊓ CQtGrp hc D)) :
    c • e ∈ M₀.img (Q ⊓ QB B ⊓ CQtGrp hc D) := by
  classical
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  obtain ⟨U, hU⟩ := hc.exists_submodule_inf_QB hw hcardL h
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨y₀, hy₀, hy₀Q, rfl⟩ := he
  have h1 : c • M₀.π y₀ ∈ U := U.smul_mem c ((hU _).mpr (M₀.pi_mem_img hy₀.1 hy₀Q))
  obtain ⟨y', hy'Q, hy'⟩ := M₀.π_surj (c • M₀.π y₀)
  rw [← hy'] at h1
  have h1' : y' ∈ Q ⊓ QB B := (M₀.mem_img_iff hZX hy'Q).mp ((hU _).mp h1)
  refine ⟨y', ⟨h1', hy'Q, fun l hl => ?_⟩, hy'Q, hy'⟩
  have hlH : l ∈ H0 M Z := hc.LB_le_H0 (hD hl)
  have hlM : l ∈ M := hc.LB_le_M (hD hl)
  have hl1 : M₀.π (l * y₀ * l⁻¹) = M₀.π y₀ :=
    (M₀.comm_mem_iff hy₀Q ((hc.conj_mem_Q_of_mem_M hlM).1 y₀ hy₀Q)).mp
      ((mem_CQtGrp.mp hy₀.2).2 l hl)
  have e1 : M₀.π (l * y' * l⁻¹) = φ ⟨l, hlH⟩ (M₀.π y') := hφπ ⟨l, hlH⟩ y' hy'Q
  have e2 : M₀.π (l * y₀ * l⁻¹) = φ ⟨l, hlH⟩ (M₀.π y₀) := hφπ ⟨l, hlH⟩ y₀ hy₀Q
  have h2 : M₀.π (l * y' * l⁻¹) = M₀.π y' := by
    rw [e1, hy', map_smul, ← e2, hl1]
  exact (M₀.comm_mem_iff hy'Q ((hc.conj_mem_Q_of_mem_M hlM).1 y' hy'Q)).mpr h2

theorem p1_95 (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {w : G} (hw : w ∈ Q ⊓ QB B)
    (hcomm : ∀ x ∈ LB M Q B ⊓ hc.CN t, ⁅x, w⁆ ∈ Z) :
    w ∈ Vt M (LB M Q B) B Z t := by
  classical
  have hs5 := hs.toSec5
  obtain ⟨K, fK, finK, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  have hcard := stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen
  set V := Vt M (LB M Q B) B Z t with hV
  set D := LB M Q B ⊓ hc.CN t
  set Y : Subgroup G := Q ⊓ QB B ⊓ CQtGrp hc D
  have hZX : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hYL : Y ≤ Q ⊓ QB B := inf_le_left
  have hBY : B ≤ Y := fun u hu =>
    ⟨⟨hc.le hu, hc.B_le_QB hu⟩, hc.le hu, fun x hx => hc.comm_B_mem_Z hx.1 hu⟩
  have hZY : Z ≤ Y := fun z hz => ⟨hZX hz, hc.Z_le_Q hz, fun x hx => by
    have e : ⁅x, z⁆ = 1 := by
      rw [commutatorElement_def, hc.LB_centralizes_Z hx.1 z hz]
      group
    rw [e]
    exact Z.one_mem⟩
  have hYsc : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Y → c • e ∈ M₀.img Y := fun c e he =>
    smul_mem_img_cent hc hs5.width hcard.2.2.2 h inf_le_left c he
  obtain ⟨-, -, -, -, -, -, hcount⟩ := hc.elation_package hs5.width hs5.n_gt
    hs5.noA2 hcard.2.2.1 hcard.2.2.2 h hBY hYL hYsc
  obtain ⟨T, hT⟩ := hc.exists_centSub (Y : Set G)
  have hcnt := hcount T hT
  have hKZ : Nat.card K = Nat.card Z := h.card
  have hq2 : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hrel := Subgroup.relIndex_mul_card (H := hc.CN t) (K := LB M Q B)
  rw [relIndex_LB_CN h34 hs, inf_comm] at hrel
  have hLN : D ≤ T := fun x hx => (hT x).mpr ⟨hx.1, fun y hy => (mem_CQtGrp.mp hy.2).2 x hx⟩
  have hle : Nat.card ↥D ≤ Nat.card T := Subgroup.card_le_of_le hLN
  have hpos : 0 < Nat.card ↥D := Nat.card_pos
  rw [hKZ] at hcnt
  have hpow : Nat.card Z ^ (Module.finrank K (imgSub M₀ Y hYsc) - 1) ≤ Nat.card Z ^ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card ↥D * Nat.card Z ^ (Module.finrank K (imgSub M₀ Y hYsc) - 1)
        ≤ Nat.card T * Nat.card Z ^ (Module.finrank K (imgSub M₀ Y hYsc) - 1) :=
          Nat.mul_le_mul_right _ hle
      _ = Nat.card Z ^ 2 * Nat.card ↥D := by rw [← hcnt, ← hrel]
      _ = Nat.card ↥D * Nat.card Z ^ 2 := mul_comm _ _
  have hdim : Module.finrank K (imgSub M₀ Y hYsc) ≤ 3 := by
    have := (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card Z)).mp hpow
    omega
  have hYcard : Nat.card Z * Nat.card (M₀.img Y) = Nat.card ↥Y :=
    (M₀.card_eq (hYL.trans inf_le_left) hZY).symm
  have himg : Nat.card (imgSub M₀ Y hYsc) = Nat.card (M₀.img Y) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => mem_imgSub)
  have himgK : Nat.card (imgSub M₀ Y hYsc) =
      Nat.card Z ^ Module.finrank K (imgSub M₀ Y hYsc) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := imgSub M₀ Y hYsc), hKZ]
  have hYle : Nat.card ↥Y ≤ Nat.card Z ^ 4 := by
    rw [← hYcard, ← himg, himgK]
    calc Nat.card Z * Nat.card Z ^ Module.finrank K (imgSub M₀ Y hYsc)
        ≤ Nat.card Z * Nat.card Z ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdim)
      _ = Nat.card Z ^ 4 := by ring
  have hVY : V ⊓ QB B ≤ Y := fun v hv =>
    ⟨⟨hc.Vt_le_Q t hv.1, hv.2⟩, hc.Vt_le_Q t hv.1, fun x hx => (Ctx.mem_CN.mp hx.2).2 v hv.1⟩
  have hVcard : Nat.card ↥(V ⊓ QB B) = Nat.card Z ^ 4 :=
    step91OrderVQB_of h34 G M Q Z B hc n t hs V hV
  have heq : V ⊓ QB B = Y := Subgroup.eq_of_le_of_card_ge hVY (by rw [hVcard]; exact hYle)
  have hwY : w ∈ Y := ⟨hw, hw.1, hcomm⟩
  rw [← heq] at hwY
  exact hwY.1

end HS9

end CFSG.RankThree.GF2n.Stroth80

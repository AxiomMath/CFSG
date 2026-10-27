module

public import CFSG.RankThree.GF2n.Stroth80.Sec33Ulu
public import CFSG.RankThree.GF2n.Stroth80.Sec33InvolA0
public import CFSG.RankThree.GF2n.Stroth80.Sec31
public import CFSG.RankThree.GF2n.Stroth80.Sec33Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.A0_comm (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ A0 Q Z B) (hr : r ∈ Q ⊓ QB B) :
    t * r = r * t := by
  obtain ⟨g, hg⟩ := hc.conj
  have htQB : t ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ ht.1.1
  have hrQB : r ∈ conjSubgroup g Q := (Ctx.QB_eq hc hg).2 ▸ hr.2
  have h1 : ⁅t, r⁆ ∈ B := hg ▸ hc.hyp.toHyp79.comm_mem_conj g htQB hrQB
  have h2 : ⁅t, r⁆ ∈ Z := ht.2 r hr
  have h3 : ⁅t, r⁆ ∈ Z ⊓ B := ⟨h2, h1⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem Ctx.isA2_of_involution (hc : Ctx M Q Z B) {t : G} (ht : t ∈ A0 Q Z B) (htQ : t ∉ Q)
    (ht2 : t ^ 2 = 1) : IsA2 Q Z t := by
  classical
  obtain ⟨u, hu, l, hl, huC, h1, h2, h3, h4⟩ := hc.exists_weyl_ulu
  obtain ⟨m, γ, M₀, hm, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨b, hb0, hbs, hB, hcent, -⟩ := hc.dictB h
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 m)
  have htM : t ∈ M := by have := ht.1; rw [← hc.QB_inf_M_eq] at this; exact this.2
  have htc : ∀ z ∈ Z, t * z * t⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp ht.1.2 z hz
    rw [← this]; group
  obtain ⟨T, hTπ, hTQ, hTB⟩ := h.linear_of_centralizes htM htc
  obtain ⟨u₀, hu₀B, hu₀Q, hu₀⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul _ b).symm⟩
  have hTb : T b = b := by
    have := hc.act_fix_B ht.1 (T := T) hTπ u₀ hu₀B
    rwa [hu₀] at this
  have hlam : M₀.B b (M₀.π u) ≠ 0 := by
    intro h0
    apply huC
    rw [hcent u hu, Tim79.QuadModel.B_comm, h0, neg_zero]
  set lam := M₀.B b (M₀.π u) with hlamdef
  set f₀ : M₀.E := lam⁻¹ • M₀.π u with hf₀def
  have hf₀ : M₀.B b f₀ = 1 := by rw [hf₀def, map_smul, smul_eq_mul, inv_mul_cancel₀ hlam]
  have hct : t * u⁻¹ * t⁻¹ ∈ Q := hc.L0_normalizes_Q ht.1 u⁻¹ (Q.inv_mem hu)
  have hcQ : ⁅u, t⁆ ∈ Q := by
    rw [show ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) by rw [commutatorElement_def]; group]
    exact Q.mul_mem hu hct
  have hπc : M₀.π ⁅u, t⁆ = M₀.π u - T (M₀.π u) := by
    rw [show ⁅u, t⁆ = u * (t * u⁻¹ * t⁻¹) by rw [commutatorElement_def]; group,
      M₀.π_mul _ hu _ hct, hTπ u⁻¹ (Q.inv_mem hu), Tim79.QuadModel.pi_inv M₀ hu, map_neg,
      sub_eq_add_neg]
  set n' := u * l * u with hn'
  have htQB : t ∈ QB B := ht.1.1
  have hxQ : n' * t * n'⁻¹ ∈ Q := by
    have : n' * t * n'⁻¹ ∈ conjSubgroup n' (QB B) :=
      mem_conjSubgroup.mpr (by rw [show n'⁻¹ * (n' * t * n'⁻¹) * n' = t by group]; exact htQB)
    rwa [h2] at this
  have hrL : n' * t * n'⁻¹ * ⁅u, t⁆ ∈ Q ⊓ QB B :=
    hc.weyl_conj_mul_comm_mem hu hl h1 h2 h3 h4 ht.1
  have hπr : M₀.π (n' * t * n'⁻¹) + M₀.π ⁅u, t⁆ = M₀.π (n' * t * n'⁻¹ * ⁅u, t⁆) :=
    (M₀.π_mul _ hxQ _ hcQ).symm
  have hsing : ∀ e ∈ M₀.img (Q ⊓ QB B), M₀.Qf e = 0 :=
    (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian
  have hQr : M₀.Qf (M₀.π (n' * t * n'⁻¹ * ⁅u, t⁆)) = 0 :=
    hsing _ (M₀.pi_mem_img hrL hrL.1)
  have hx2 : (n' * t * n'⁻¹) ^ 2 = 1 := by
    have : (n' * t * n'⁻¹) ^ 2 = n' * t ^ 2 * n'⁻¹ := by rw [pow_two, pow_two]; group
    rw [this, ht2]; group
  have hQx : M₀.Qf (M₀.π (n' * t * n'⁻¹)) = 0 := (M₀.sq_iff_Qf h.reg hxQ).mp hx2
  have hxcomm : ∀ r ∈ Q ⊓ QB B, (n' * t * n'⁻¹) * r = r * (n' * t * n'⁻¹) := by
    intro r hr
    have hr1 : n'⁻¹ * r * n' ∈ Q := mem_conjSubgroup.mp (h1 ▸ hr.2)
    have hr2 : n'⁻¹ * r * n' ∈ QB B := mem_conjSubgroup.mp (h2 ▸ hr.1)
    have hcm := hc.A0_comm ht ⟨hr1, hr2⟩
    calc (n' * t * n'⁻¹) * r = n' * (t * (n'⁻¹ * r * n')) * n'⁻¹ := by group
      _ = n' * ((n'⁻¹ * r * n') * t) * n'⁻¹ := by rw [hcm]
      _ = r * (n' * t * n'⁻¹) := by group
  have hBxr : M₀.B (M₀.π (n' * t * n'⁻¹)) (M₀.π (n' * t * n'⁻¹ * ⁅u, t⁆)) = 0 :=
    (M₀.comm_iff_B h.reg hxQ hrL.1).mp (hxcomm _ hrL)
  have hBrx : M₀.B (M₀.π (n' * t * n'⁻¹ * ⁅u, t⁆)) (M₀.π (n' * t * n'⁻¹)) = 0 := by
    rw [Tim79.QuadModel.B_comm, hBxr, neg_zero]
  have hQneg : ∀ v : M₀.E, M₀.Qf (-v) = M₀.Qf v := fun v => by
    rw [← neg_one_smul (GaloisField 2 m) v, M₀.Qf_smul]; simp
  have hQc : M₀.Qf (M₀.π ⁅u, t⁆) = 0 := by
    have h5 : M₀.π ⁅u, t⁆ = M₀.π (n' * t * n'⁻¹ * ⁅u, t⁆) + -M₀.π (n' * t * n'⁻¹) := by
      rw [← hπr]; abel
    rw [h5, M₀.Qf_add, hQr, hQneg, hQx, map_neg, hBrx]
    simp
  have hqu : M₀.Qf (T (M₀.π u) - M₀.π u) = 0 := by
    have : T (M₀.π u) - M₀.π u = -M₀.π ⁅u, t⁆ := by rw [hπc]; abel
    rw [this, hQneg, hQc]
  have hqv : M₀.Qf (T f₀ - f₀) = 0 := by
    have : T f₀ - f₀ = lam⁻¹ • (T (M₀.π u) - M₀.π u) := by
      rw [hf₀def, map_smul, smul_sub]
    rw [this, M₀.Qf_smul, hqu, mul_zero]
  exact hc.isA2_of_A0_qf h ht htQ hb0 hbs hB hcent T hTπ hTQ hTb hf₀ hqv

theorem stroth_3_3 (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 1 ≤ n) :
    Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ (n - 1) ∨ ∃ a ∈ LB M Q B, IsA2 Q Z a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hno⟩ := hcon
  have hge := hc.card_LB_ge hw hn
  have hlt' : Nat.card Q * Nat.card Z ^ (n - 1) < Nat.card (LB M Q B) :=
    lt_of_le_of_ne hge (Ne.symm hne)
  have hmul := hc.card_LB_mul hw
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hlt : Nat.card ↥(Q ⊓ QB B) < Nat.card Z ^ (n + 1) := by
    by_contra hge'
    push Not at hge'
    have h1 : Nat.card Q * Nat.card Z ^ (n - 1) * Nat.card Z ^ (n + 1) <
        Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) :=
      calc Nat.card Q * Nat.card Z ^ (n - 1) * Nat.card Z ^ (n + 1)
          < Nat.card (LB M Q B) * Nat.card Z ^ (n + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt' (pow_pos hqpos _)
        _ ≤ Nat.card (LB M Q B) * Nat.card ↥(Q ⊓ QB B) := Nat.mul_le_mul_left _ hge'
    have h2 : Nat.card Q * Nat.card Z ^ (n - 1) * Nat.card Z ^ (n + 1) =
        Nat.card Q * Nat.card Z ^ (2 * n) := by
      rw [mul_assoc, ← pow_add]; congr 2; omega
    rw [h2, ← hmul] at h1
    exact lt_irrefl _ h1
  obtain ⟨t, htA, htQ, ht2⟩ := hc.exists_involution_A0 hw hlt
  exact hno t (hc.L0_le_LB htA.1) (hc.isA2_of_involution htA htQ ht2)

end CFSG.RankThree.GF2n.Stroth80

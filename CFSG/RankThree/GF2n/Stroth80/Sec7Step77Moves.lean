module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LBElation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec7_LB_N_moves_conj (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hSplit : Sec7WVSplitStatement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
      ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q →
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
      ∃ y ∈ LB M Q B ⊓ hc.CN t, ∃ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), ⁅y, v⁆ ∉ Z := by
  intro G _ _ M Q Z B hc n t hs hno hom g hgM s hs1 hs2 hVZ
  classical
  haveI := hc.normal_Q_in_M
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre hs.toSec5.mem
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  obtain ⟨ψs, hψs, hrs, hker⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hgM hsM hs1
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hd⟩ := sec7_pair_card_meet hc M₀ ρ b hS hgM ψs hrs hUcard
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  obtain ⟨hUperp, hRW, hYinv⟩ := sec7_pair_section h71 h310chi h52a hA hc hs hno hZ0 M₀ ρ b hS ψ
    hψ hW hgM hsM hs1 hs2 ψs hψs
  let A : Submodule K M₀.E := (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs
  let Y : Submodule K M₀.E := A ⊔ hc.VtSub hS.model t
  have hAle : A ≤ M₀.B.orthogonal (hc.VtSub hS.model t) :=
    LinearMap.map_le_range.trans hRW
  have hYle : Y ≤ M₀.B.orthogonal (hc.VtSub hS.model t) := sup_le hAle hUperp
  obtain ⟨hVP, hPW, hPR⟩ := sec7_section_pre hc hs M₀ ρ b hS ψ hW Y le_sup_right hYle hYinv
  let Pg : Subgroup G := sec7Pre M₀ Y.toAddSubgroup
  have hfU : Module.finrank K (hc.VtSub hS.model t) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := K) (V := hc.VtSub hS.model t)
    rw [hUcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hfR : Module.finrank K (LinearMap.range ψs) = 4 := by
    have hcard : Nat.card (LinearMap.range ψs) = Nat.card K ^ 4 := by
      have h1 : Nat.card (LinearMap.range ψs) = Nat.card (M₀.img (conjSubgroup g
          (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψs)
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hd0 : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = 0 := by
    rw [hVZ, hZK] at hc1
    have h1 : 1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = 1 :=
      Nat.pow_right_injective hK2 (hc1.symm.trans (pow_one _).symm)
    omega
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψs hker (hc.VtSub hS.model t)
  rw [hd0, hfR] at hmap
  have hAnotU : ¬ A ≤ hc.VtSub hS.model t := by
    intro hAU
    have hle : A ≤ hc.VtSub hS.model t ⊓ LinearMap.range ψs :=
      le_inf hAU (LinearMap.map_le_range)
    have := Submodule.finrank_mono hle
    rw [hd0] at this
    have h4 : Module.finrank K A = 4 := by simpa using hmap
    omega
  obtain ⟨a₀, ha₀A, ha₀U⟩ := Set.not_subset.mp hAnotU
  obtain ⟨x₀, hx₀Q, rfl⟩ := M₀.π_surj a₀
  have hx₀P : x₀ ∈ Pg := ⟨hx₀Q, Submodule.mem_sup_left ha₀A⟩
  have hPnotV : ¬ Pg ≤ Vt M (LB M Q B) B Z t := fun h =>
    ha₀U ((hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img (h hx₀P) hx₀Q))
  have hmove : ∃ l ∈ LB M Q B, ∃ p ∈ Pg, ⁅l, p⁆ ∉ Vt M (LB M Q B) B Z t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr, hdec⟩ := hSplit G M Q Z B hc n t hs Pg hVP hPW hPR
    obtain ⟨-, hA₁P, -, hA₂P, -, hinf, -, -, hA₁mem, -⟩ := hdec
    have hconjV : conjSubgroup r (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
      conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr.mem)
    have hconjW : conjSubgroup r (Wt Q (Vt M (LB M Q B) B Z t)) =
        Wt Q (Vt M (LB M Q B) B Z t) :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun x hx =>
        sec7WVOrd_conj_mem hc ht hr.mem hx)
    have hconj : conjSubgroup r (Pg ⊓ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t)) =
        Pg ⊓ ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t) := by
      rw [conjSubgroup_inf, conjSubgroup_sup', conjSubgroup_inf, QB_conj, hconjW, hconjV,
        hPR r hr.mem]
    have hA₁eq : Pg ⊓ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) = Pg :=
      le_antisymm hA₁P fun x hx => (hA₁mem x hx).mpr fun l hl => hcon l hl x hx
    have hA₂V : Pg ⊓ ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
      have h1 := hinf
      rw [hA₁eq] at h1
      rwa [inf_eq_right.mpr hA₂P] at h1
    have hcard : Nat.card Pg = Nat.card (Vt M (LB M Q B) B Z t) := by
      calc Nat.card Pg = Nat.card (conjSubgroup r (Pg ⊓ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
            Vt M (LB M Q B) B Z t))) := by rw [hA₁eq, card_conjSubgroup]
        _ = Nat.card (Vt M (LB M Q B) B Z t) := by rw [hconj, hA₂V]
    exact hPnotV (Subgroup.eq_of_le_of_card_ge hVP (le_of_eq hcard)).symm.le
  obtain ⟨l, hlL, p, hpP, hlp⟩ := hmove
  have hlM : l ∈ M := hc.LB_le_M hlL
  have hlbar : (QuotientGroup.mk (⟨l, hlM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr (hc.LB_le_H0 hlL), rfl⟩
  let Sl : M₀.E ≃ₗ[K] M₀.E :=
    AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨l, hlM⟩ : ↥M))).toAdd (hS.lin _ hlbar)
  have hSl : ∀ x ∈ Q, M₀.π (l * x * l⁻¹) = Sl (M₀.π x) := fun x hx => hS.conj ⟨l, hlM⟩ x hx
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hlL
  have hpQ : p ∈ Q := hpP.1
  have hlpQ : ⁅l, p⁆ ∈ Q := sec7_comm_mem_Q hc hlM hpQ
  have hepi : Sl (M₀.π p) - M₀.π p = M₀.π ⁅l, p⁆ := sec7_act_sub_comm hc M₀ ρ b hS hlM hpQ
  have he₁Y : M₀.π ⁅l, p⁆ ∈ Y := by
    rw [← hepi]
    exact Y.sub_mem (hYinv l hlR _ hpP.2) hpP.2
  have he₁U : M₀.π ⁅l, p⁆ ∉ hc.VtSub hS.model t := fun h =>
    hlp ((Tim79.QuadModel.mem_img_iff M₀ hZV' hlpQ).mp ((hc.mem_VtSub hS.model t).mp h))
  have hcard35 := stroth_3_5 h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen
  obtain ⟨T, bT, hT, hfT, -, hb0, hB, hact, -⟩ :=
    sec7_LB_elation hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hcard35.2.2.1
      hcard35.2.2.2 hS.model
  have hbimg : (bT : M₀.E) ∈ M₀.img B := (hB bT).mpr ⟨1, (one_smul K _).symm⟩
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hBp : M₀.B (M₀.π p) bT = 0 :=
    (mem_img_Wt_iff M₀ hS.model.reg hVQ).mp (M₀.pi_mem_img (hPW hpP) hpQ) _
      (M₀.img_mono hBV hbimg)
  have he₁T : M₀.π ⁅l, p⁆ ∈ T := by
    obtain ⟨-, -, hflag, -⟩ := hact l hlL Sl hSl
    rw [← hepi]
    exact hflag _ hBp
  set e₁ : M₀.E := M₀.π ⁅l, p⁆ with he₁def
  have hK1 : 1 < Nat.card K := hK2
  let Y' : Submodule K M₀.E := Y ⊓ T
  have hLZ : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q hc.Z_le_QB.1
  have hBL : B ≤ Q ⊓ QB B := le_inf hc.le hc.B_le_QB
  have hHU : ∀ e ∈ sec7Hset M₀ (Vt M (LB M Q B) B Z t) B, e ∈ hc.VtSub hS.model t := fun e he =>
    M₀.img_mono (sup_le inf_le_left hZV') he
  have hHT : ∀ e ∈ sec7Hset M₀ (Vt M (LB M Q B) B Z t) B, e ∈ T := fun e he =>
    (hT e).mpr (M₀.img_mono (sup_le (le_inf (inf_le_left.trans hVQ) inf_le_right) hLZ) he)
  have hYT' : ∀ e ∈ Y', e ∈ M₀.img (Q ⊓ QB B) := fun e he => (hT e).mp he.2
  have hBT : ∀ e ∈ M₀.img B, e ∈ Y' := fun e he =>
    ⟨Submodule.mem_sup_right ((hc.mem_VtSub hS.model t).mpr (M₀.img_mono hBV he)),
      (hT e).mpr (M₀.img_mono hBL he)⟩
  let fmap : (sec7Hset M₀ (Vt M (LB M Q B) B Z t) B) × K → ↥Y' := fun hk =>
    ⟨(hk.1 : M₀.E) + hk.2 • e₁,
      ⟨Y.add_mem (Submodule.mem_sup_right (hHU _ hk.1.2)) (Y.smul_mem _ he₁Y),
        T.add_mem (hHT _ hk.1.2) (T.smul_mem _ he₁T)⟩⟩
  have hfinj : Function.Injective fmap := by
    rintro ⟨h₁, c₁⟩ ⟨h₂, c₂⟩ heq
    have h0 : (h₁ : M₀.E) + c₁ • e₁ = (h₂ : M₀.E) + c₂ • e₁ := congrArg Subtype.val heq
    have hc12 : c₁ = c₂ := by
      by_contra hne
      have hsub : (c₁ - c₂) • e₁ = (h₂ : M₀.E) - h₁ := by
        rw [sub_smul]
        calc c₁ • e₁ - c₂ • e₁
            = ((h₁ : M₀.E) + c₁ • e₁ - ((h₂ : M₀.E) + c₂ • e₁)) + ((h₂ : M₀.E) - h₁) := by abel
          _ = (h₂ : M₀.E) - h₁ := by rw [h0, sub_self, zero_add]
      have hmem : (c₁ - c₂) • e₁ ∈ hc.VtSub hS.model t := by
        rw [hsub]
        exact (hc.VtSub hS.model t).sub_mem (hHU _ h₂.2) (hHU _ h₁.2)
      refine he₁U ?_
      have := (hc.VtSub hS.model t).smul_mem (c₁ - c₂)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
    subst hc12
    have : (h₁ : M₀.E) = h₂ := add_right_cancel h0
    rw [Subtype.ext this]
  have hfY' : 4 ≤ Module.finrank K Y' := by
    have h1 := Nat.card_le_card_of_injective fmap hfinj
    rw [Nat.card_prod, hHcard, Module.natCard_eq_pow_finrank (K := K) (V := Y')] at h1
    have h2 : Nat.card K ^ 4 ≤ Nat.card K ^ Module.finrank K Y' := by
      calc Nat.card K ^ 4 = Nat.card K ^ 3 * Nat.card K := by ring
        _ ≤ _ := h1
    exact (Nat.pow_le_pow_iff_right hK1).mp h2
  have hfYn : Module.finrank K Y' ≤ n := hfT ▸ Submodule.finrank_mono (inf_le_right : Y ⊓ T ≤ T)
  obtain ⟨r₀, hr₀⟩ := hA G M Q Z B hc n t hs
  obtain ⟨d, -, hVd, hLd⟩ := sec7ctr_card_LB hPts hc hs hr₀
  have hd4 : d = 4 := by
    have hcV := Tim79.QuadModel.card_eq M₀ hVQ hZV'
    have hcimg : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) = Nat.card K ^ 4 := hUcard
    have h1 : Nat.card Z * Nat.card Z ^ d = Nat.card Z * Nat.card K ^ 4 := by
      rw [← hVd, hcV, hcimg]
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    rw [hZK] at h2
    exact Nat.pow_right_injective hK2 h2
  rw [hd4] at hLd
  have hDmul : Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 =
      Nat.card Q * Nat.card Z ^ (n - 1) := hLd.symm.trans hcard35.2.2.1
  rw [hZK] at hDmul
  have hnY : n - Module.finrank K Y' + 2 < n - 1 := by omega
  have hDlarge : Nat.card Q * Nat.card K ^ (n - Module.finrank K Y') <
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    refine Nat.lt_of_mul_lt_mul_right (a := Nat.card K ^ 2) ?_
    rw [hDmul, mul_assoc, ← pow_add]
    exact (Nat.mul_lt_mul_left Nat.card_pos).mpr (Nat.pow_lt_pow_right hK1 hnY)
  obtain ⟨l', hl'D, x, hxL, hxY', hl'x⟩ := sec7_LB_elation_exists_moved hc hs.toSec5.width
    hs.toSec5.n_gt hs.toSec5.noA2 hcard35.2.2.1 hcard35.2.2.2 hS.model Y' hYT' hBT
    (LB M Q B ⊓ hc.CN t) inf_le_left hDlarge
  by_contra hcon2
  push Not at hcon2
  have hl'M : l' ∈ M := hc.LB_le_M hl'D.1
  have hl'bar : (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨l', hl'M⟩, Subgroup.mem_subgroupOf.mpr (hc.LB_le_H0 hl'D.1), rfl⟩
  have hxQ : x ∈ Q := hxL.1
  have hl'xQ : ⁅l', x⁆ ∈ Q := sec7_comm_mem_Q hc hl'M hxQ
  have hfixV : ∀ v ∈ Vt M (LB M Q B) B Z t,
      (ρ (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M))).toAdd (M₀.π v) = M₀.π v := by
    intro v hv
    have h1 := sec7_act_sub_comm hc M₀ ρ b hS hl'M (hVQ hv)
    have h2 : M₀.π ⁅l', v⁆ = 0 := (M₀.π_ker _ (sec7_comm_mem_Q hc hl'M (hVQ hv))).mpr
      ((Ctx.mem_CN.mp hl'D.2).2 v hv)
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  have hVgQ : ∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t), v ∈ Q := by
    intro v hv
    have h1 : g⁻¹ * v * g ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hv
    have h2 : g * (g⁻¹ * v * g) * g⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hgM).1 _ (hVQ h1)
    simpa [mul_assoc] using h2
  have hfixVg : ∀ v ∈ conjSubgroup g (Vt M (LB M Q B) B Z t),
      (ρ (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M))).toAdd (M₀.π v) = M₀.π v := by
    intro v hv
    have h1 := sec7_act_sub_comm hc M₀ ρ b hS hl'M (hVgQ v hv)
    have h2 : M₀.π ⁅l', v⁆ = 0 := (M₀.π_ker _ (sec7_comm_mem_Q hc hl'M (hVgQ v hv))).mpr
      (hcon2 l' hl'D v hv)
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  have hfixY : ∀ e ∈ Y, (ρ (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M))).toAdd e = e := by
    intro e he
    obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.mp he
    have har : a ∈ LinearMap.range ψs := LinearMap.map_le_range ha
    obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((hrs a).mp har)
    obtain ⟨v', hvV', hvQ', hv'⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    have h1 : (ρ (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M))).toAdd a = a := by
      rw [← hv]
      exact hfixVg v hvV
    have h2 : (ρ (QuotientGroup.mk (⟨l', hl'M⟩ : ↥M))).toAdd u = u := by
      rw [← hv']
      exact hfixV v' hvV'
    rw [map_add, h1, h2]
  have h1 := sec7_act_sub_comm hc M₀ ρ b hS hl'M hxQ
  rw [hfixY _ hxY'.1, sub_self] at h1
  exact hl'x ((M₀.π_ker _ hl'xQ).mp h1.symm)

theorem step77FromOneMoves_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hSplit : Sec7WVSplitStatement) : Step77FromOneMovesStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV
  classical
  have htM : t ∈ M := hc.LB_le_M hs.toSec5.mem
  have hg'M : g⁻¹ ∈ M := M.inv_mem hgM
  have hs1' : (g⁻¹ * t * (g⁻¹)⁻¹) * (g⁻¹ * t * (g⁻¹)⁻¹)⁻¹ ∈ Q := by
    rw [mul_inv_cancel]
    exact Q.one_mem
  have hu0 : ⁅g * t * g⁻¹, t⁆ ∈ Q := by
    have e : ⁅g * t * g⁻¹, t⁆ = (s * (g * t * g⁻¹)⁻¹)⁻¹ * ⁅s, t⁆ *
        (t * (s * (g * t * g⁻¹)⁻¹) * t⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hs1) hs2) ((hc.conj_mem_Q_of_mem_M htM).1 _ hs1)
  have hs2' : ⁅g⁻¹ * t * (g⁻¹)⁻¹, t⁆ ∈ Q := by
    have e : ⁅g⁻¹ * t * (g⁻¹)⁻¹, t⁆ = (g⁻¹ * ⁅g * t * g⁻¹, t⁆ * (g⁻¹)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.inv_mem ((hc.conj_mem_Q_of_mem_M hg'M).1 _ hu0)
  have hV' : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) = Z := by
    have h1 := congrArg (conjSubgroup g⁻¹) hV
    rw [conjSubgroup_inf, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one,
      hc.conj_Z_eq hg'M, inf_comm] at h1
    exact h1
  obtain ⟨y', hy'D, v', hv'V, hy'v'⟩ :=
    sec7_LB_N_moves_conj h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hPts hSplit G M Q Z B hc n t
      hs hno hom g⁻¹ hg'M (g⁻¹ * t * (g⁻¹)⁻¹) hs1' hs2' hV'
  refine ⟨g * y' * g⁻¹, ?_, g * v' * g⁻¹, ?_, fun hZ' => hy'v' ?_⟩
  · rw [mem_conjSubgroup]
    simpa [mul_assoc] using hy'D
  · have := mem_conjSubgroup.mp hv'V
    simpa using this
  · have e : ⁅y', v'⁆ = g⁻¹ * ⁅g * y' * g⁻¹, g * v' * g⁻¹⁆ * (g⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hg'M) _).mp hZ'

theorem step77FromOneCore_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hSplit : Sec7WVSplitStatement) : Step77FromOneCoreStatement :=
  step77FromOneCore_of_moves h34 hRoot h71 h310chi hZc hZV hZcard h52a hA
    (step77FromOneMoves_of_inputs h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hPts hSplit)

theorem step77FromOneCore_of_stmts (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Step77FromOneCoreStatement :=
  step77FromOneCore_of_inputs h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hPts
    (sec7WVSplit_of hA hPts h52a h52b)

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor
public import CFSG.Quasithin.Vol2.KGFactJ4M2Cent
public import CFSG.RankThree.Asc83Table.J4
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

theorem z0_mul_self :
    z0 * z0 = 1 := by
  change eta uJ 11 1131 * eta uJ 11 1131 = 1
  exact eta_sq (elem_uJ j4Facts.mat) 1131

theorem eq_z0_of_mem_zpowers
    {x : J} (hx : x ∈ Subgroup.zpowers z0) (hx1 : x ≠ 1) : x = z0 := by
  have hz2 : orderOf z0 = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact z0_mul_self) (z0_ne_one j4Facts.mat)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk : z0 ^ k = z0 ^ (k % 2) := by
    rw [← zpow_mod_orderOf, hz2]
    norm_num
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [hk, h, zpow_zero] at hx1
    exact absurd rfl hx1
  · rw [hk, h, zpow_one]

theorem exists_conj_eq_z0
    {l : J} (hl1 : l ≠ 1) (S : Sylow 2 J)
    (hS : ∀ s ∈ (S : Subgroup J), s * l = l * s) : ∃ g : J, g⁻¹ * l * g = z0 := by
  have hF := j4Facts
  have hM := hF.mat
  let P' : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P' S
  have hS' : (S : Subgroup J) = MulAut.conj g • P0 := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  refine ⟨g, eq_z0_of_mem_zpowers (CFSG.Quasithin.J4M2Core.centralizer_pCoreOf_M2_le ?_) ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqQ : q ∈ Qgrp := by
      have := CFSG.Quasithin.J4M2Core.pCoreOf_M2_eq
      rw [← this]
      exact hq
    have hqS : g * q * g⁻¹ ∈ (S : Subgroup J) := by
      rw [hS']
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨q, Qgrp_le_P0 hF hqQ, rfl⟩
    have h1 := hS _ hqS
    calc q * (g⁻¹ * l * g) = g⁻¹ * ((g * q * g⁻¹) * l) * g := by group
      _ = g⁻¹ * (l * (g * q * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * l * g * q := by group
  · intro h1
    apply hl1
    calc l = g * (g⁻¹ * l * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem not_autConf_j4_z0
    {ν Lb Pb} (h : AutConf J ν Lb Pb) (h9 : Nat.card Pb = 9)
    (hZ : Subgroup.center J = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer J))
    (hl : ∀ x, ν x = z0⁻¹ * x * z0) : False := by
  have hF := j4Facts
  obtain ⟨-, hfix⟩ := h.involution_of_inner hZ hl
  have hinj := conj_injective_of_center_eq_bot hZ
  have hΛM : innerPart Lb ≤ M2 := fun c hc => (hfix c).mp (h.fix_of_mem_innerPart hZ hc)
  have hPin : Pb ≤ (MulAut.conj (G := J)).range := fun a ha =>
    mem_range_conj_of_pow_three hout a (h.elem.2 a ha)
  have hE9 : Nat.card (Pb.comap (MulAut.conj (G := J))) = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hPin, h9]
  obtain ⟨c₀, hcP, hcK⟩ : ∃ c₀ ∈ Pb.comap (MulAut.conj (G := J)), c₀ ∉ Kgrp := by
    by_contra hcon
    push Not at hcon
    have hd := Subgroup.card_dvd_of_le (show Pb.comap (MulAut.conj (G := J)) ≤ Kgrp
      from fun x hx => hcon x hx)
    rw [hE9, card_Kgrp hF] at hd
    norm_num at hd
  have hcΛ : c₀ ∈ innerPart Lb := h.le hcP
  have hc3 : c₀ ^ 3 = 1 := hinj (by rw [map_pow, map_one]; exact h.elem.2 _ hcP)
  set cM : ↥M2 := ⟨c₀, hΛM hcΛ⟩ with hcM
  have hρc1 : rho hF cM ≠ 1 := fun h1 => hcK ((mem_Kgrp_iff hF cM).mpr h1)
  have hρc3 : rho hF cM ^ 3 = 1 := by
    have : cM ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hc3)
    rw [← map_pow, this, map_one]
  have hidx : (MbarP.subgroupOf Mbar).index = 2 := by
    have hc := Subgroup.card_mul_index (MbarP.subgroupOf Mbar)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe MbarP_le_Mbar).toEquiv, card_MbarP,
      card_Mbar hF] at hc
    omega
  have hρMbar : ∀ m : ↥M2, rho hF m ∈ Mbar := fun m => by
    rw [← range_rho_eq hF]
    exact ⟨m, rfl⟩
  have hρcP : rho hF cM ∈ MbarP := by
    have hy := Subgroup.mul_self_mem_of_index_two hidx
      ⟨rho hF cM ^ 2, Mbar.pow_mem (hρMbar cM) 2⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hy
    have e : rho hF cM ^ 2 * rho hF cM ^ 2 = rho hF cM := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hρc3, one_mul]
    rwa [e] at hy
  set N : Subgroup ↥MbarP := (((innerPart Lb).subgroupOf M2).map (rho hF)).subgroupOf MbarP
    with hN
  have hNn : N.Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨w, hw, hwx⟩ := hx
    obtain ⟨m₀, hm₀⟩ : (m : Equiv.Perm (Fin 77)) ∈ (rho hF).range := by
      rw [range_rho_eq hF]
      exact MbarP_le_Mbar m.2
    refine ⟨m₀ * w * m₀⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw ⊢
      have hν : ν (m₀ : J) = m₀ := (hfix _).mpr m₀.2
      simpa using h.conj_mem_innerPart hν hw
    · rw [map_mul, map_mul, map_inv, hm₀, hwx]
      rfl
  have hNne : N ≠ ⊥ := by
    intro hb
    have hmem : (⟨rho hF cM, hρcP⟩ : ↥MbarP) ∈ N := by
      rw [hN, Subgroup.mem_subgroupOf]
      exact ⟨cM, Subgroup.mem_subgroupOf.mpr hcΛ, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hρc1 (congrArg Subtype.val hmem)
  have : IsSimpleGroup ↥MbarP := isSimpleGroup_MbarP
  have hNtop : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hNne
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥MbarP) 11 (by rw [card_MbarP]; norm_num)
  have hyN : y ∈ N := hNtop ▸ Subgroup.mem_top y
  rw [hN, Subgroup.mem_subgroupOf] at hyN
  obtain ⟨w, hw, hwy⟩ := hyN
  have h11 : 11 ∣ orderOf w := by
    have hd := orderOf_map_dvd (rho hF) w
    rw [hwy, Subgroup.orderOf_coe, hy] at hd
    exact hd
  have hμo : orderOf (w ^ (orderOf w / 11)) = 11 := orderOf_pow_orderOf_div (orderOf_pos w).ne' h11
  have hμ : ((w ^ (orderOf w / 11) : ↥M2) : J) ∈ innerPart Lb := by
    have := ((innerPart Lb).subgroupOf M2).pow_mem hw (orderOf w / 11)
    rwa [Subgroup.mem_subgroupOf] at this
  have hμ3 := h.pow_three_of_mem_innerPart hZ hμ (by rw [Subgroup.orderOf_coe, hμo]; decide)
  have hd := orderOf_dvd_of_pow_eq_one hμ3
  rw [Subgroup.orderOf_coe, hμo] at hd
  norm_num at hd

theorem not_autConf_j4
    {ν Lb Pb} (h : AutConf J ν Lb Pb) (h9 : Nat.card Pb = 9)
    (hZ : Subgroup.center J = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer J))
    (hν : ∃ l : J, ∀ x, ν x = l⁻¹ * x * l) : False := by
  obtain ⟨l, hl⟩ := hν
  obtain ⟨hl2, hfix⟩ := h.involution_of_inner hZ hl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow_fixed
  have hl1 : l ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hl2; exact absurd hl2 (by norm_num)
  obtain ⟨g, hgz⟩ := exists_conj_eq_z0 hl1 S fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff (G := J)).mp ((hfix s).mp (hS s hs))
  refine not_autConf_j4_z0 (h.map (MulAut.conj g⁻¹))
    ((card_map_mulAut_congr (MulAut.conj g⁻¹) Pb).trans h9) hZ hout fun x => ?_
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hl, ← hgz]
  simp only [MulAut.conj_apply, MulAut.conj_symm_apply]
  group

@[expose] def mulEquivOfGroup {M N : Type} [Group M] [Group N] (f : M ≃ N)
    (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N :=
  MulEquiv.mk' f h

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_j4
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .J4) : False := by
  have := hQ.finite
  have hF := j4Facts
  have e₁ : ↥K ≃* NativeSporadic.J4 := e
  have e₂ := mulEquivOfGroup (M := ↥K) (N := NativeSporadic.J4) e₁.toEquiv
    (fun x y => map_mul e₁ x y)
  have φ := mulEquivOfGroup (M := ↥K) (N := J) (e₁.trans (seedEquiv hF.mat)).toEquiv
    (fun x y => map_mul (e₁.trans (seedEquiv hF.mat)) x y)
  have hZJ : Subgroup.center J = ⊥ := by
    have : IsSimpleGroup J := isSimpleGroup_J hF
    refine center_eq_bot_of_simple_of_not_prime ?_
    rw [card_J hF]
    norm_num
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_mulEquiv φ hZJ
  obtain ⟨E, hE3, hE9⟩ := exists_elemAbelian_nine_of_mulEquiv (M := ↥K)
    (M' := NativeSporadic.J4) e₂
    ⟨_, isElemAbelian_closure_pair (CFSG.RankThree.Asc83Table.J4.E 0).ha
      (CFSG.RankThree.Asc83Table.J4.E 0).hb (CFSG.RankThree.Asc83Table.J4.E 0).hab,
      (CFSG.RankThree.Asc83Table.J4.E 0).card⟩
  have hA := h.autConf
  have h9 : Nat.card h.rhoP.range = 9 :=
    h.card_rhoP_range_eq_nine hQ hE3 hE9 fun z hz _ => by rwa [hZK, Subgroup.mem_bot] at hz
  obtain ⟨l, hl⟩ := isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName])
    (by decide) e h.nu (apply_apply_of_sq hA.sq) hA.exists_sylow_fixed
  refine not_autConf_j4 (hA.map φ)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr (G := ↥K) (H := J) φ).injective, h9])
    hZJ
    CFSG.RankThree.PartTwo.Sec4.Item47CoreOut.not_three_dvd_card_outer_J ⟨φ l, fun x => ?_⟩
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hl, map_mul, map_mul,
    map_inv, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.H13.S126C

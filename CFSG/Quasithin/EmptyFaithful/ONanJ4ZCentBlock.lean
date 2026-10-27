module

public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentSound
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentLat
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentModO2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lift

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
open CFSG.Quasithin.J4M2 (M2 Kgrp Qgrp rho Tbar Mbar MbarP card_Mbar card_MbarP MbarP_le_Mbar
  range_rho_eq mem_Kgrp_iff isSolvable_Kgrp Kgrp_conj_mem Kgrp_normalizes_Qgrp card_Kgrp card_Qgrp
  Qgrp_le_Kgrp Qgrp_le_P0 P0_le_M2 mem_map_of_gE gE_k_mem_P0 gE_u_mem_P0 tPerms)
open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat (p5Gens)
open scoped commutatorElement

section Image

theorem index_MbarP
    (hF : J4Facts) : (MbarP.subgroupOf Mbar).index = 2 := by
  have h1 := Subgroup.card_mul_index (MbarP.subgroupOf Mbar)
  have h2 : Nat.card ↥(MbarP.subgroupOf Mbar) = Nat.card ↥MbarP :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe MbarP_le_Mbar).toEquiv
  rw [h2, card_MbarP, card_Mbar hF] at h1
  omega

theorem rhoB_perfect
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) :
    ⁅rhoB hF B, rhoB hF B⁆ = rhoB hF B := by
  unfold rhoB
  rw [← Subgroup.map_commutator, perfect_subgroupOf hBM hB]

theorem rhoB_normalized
    (hF : J4Facts) {B : Subgroup J} (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) :
    ∀ t ∈ rhoB hF P0, ∀ x ∈ rhoB hF B, t * x * t⁻¹ ∈ rhoB hF B := by
  intro t ht x hx
  obtain ⟨p, hp, hpM, rfl⟩ := (mem_rhoB hF).1 ht
  obtain ⟨b, hb, hbM, rfl⟩ := (mem_rhoB hF).1 hx
  have hpbM : p * b * p⁻¹ ∈ M2 := M2.mul_mem (M2.mul_mem hpM hbM) (M2.inv_mem hpM)
  refine (mem_rhoB hF).2 ⟨p * b * p⁻¹, ((Subgroup.mem_normalizer_iff.1 (hPB hp) b).1 hb), hpbM, ?_⟩
  have e : (⟨p * b * p⁻¹, hpbM⟩ : ↥M2) = ⟨p, hpM⟩ * ⟨b, hbM⟩ * ⟨p, hpM⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

theorem Tbar_le_rhoB_P0
    (hF : J4Facts) :
    Tbar ≤ rhoB hF P0 := by
  rw [Tbar, Subgroup.closure_le]
  intro x hx
  simp only [tPerms, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hx
  rcases hx with h | h | h | h
  · exact mem_map_of_gE hF (n := 28) (by norm_num) (gE_k_mem_P0 (i := 0) (by norm_num)) h
  · exact mem_map_of_gE hF (n := 29) (by norm_num) (gE_k_mem_P0 (i := 1) (by norm_num)) h
  · exact mem_map_of_gE hF (n := 30) (by norm_num) (gE_k_mem_P0 (i := 2) (by norm_num)) h
  · exact mem_map_of_gE hF (n := 17) (by norm_num) (gE_u_mem_P0 (j := 0) (by norm_num)) h

theorem rhoB_le_MbarP
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) : rhoB hF B ≤ MbarP := by
  have hle : rhoB hF B ≤ Mbar := by
    rw [← range_rho_eq hF]
    exact Subgroup.map_le_range _ _
  exact perfect_le_of_index_two (index_MbarP hF) hle (rhoB_perfect hF hBM hB)

theorem rhoB_ne_bot
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥) :
    rhoB hF B ≠ ⊥ := by
  intro h
  apply hB1
  have hBK : B ≤ Kgrp := by
    intro b hb
    have hmem : rho hF ⟨b, hBM hb⟩ ∈ rhoB hF B := (mem_rhoB hF).2 ⟨b, hb, hBM hb, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact (mem_Kgrp_iff hF ⟨b, hBM hb⟩).2 hmem
  exact eq_bot_of_perfect_of_le_solvable (isSolvable_Kgrp hF) hBK hB

end Image

section Kernel

theorem inf_Kgrp_le_pCoreOf
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hS : IsSimpleGroup (ModO2 B))
    (hnc : ¬ (Nat.card (ModO2 B)).Prime) : B ⊓ Kgrp ≤ CFSG.Open.pCoreOf 2 B := by
  have := isSolvable_Kgrp hF
  refine le_pCoreOf_of_solvable_normal hS hnc inf_le_left ?_ ?_
  · intro b hb n hn
    exact ⟨B.mul_mem (B.mul_mem hb hn.1) (B.inv_mem hb), Kgrp_conj_mem hF b (hBM hb) n hn.2⟩
  · exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : B ⊓ Kgrp ≤ Kgrp))
      (Subgroup.inclusion_injective _)

theorem card_rhoB_mul
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hS : IsSimpleGroup (ModO2 B))
    (hnc : ¬ (Nat.card (ModO2 B)).Prime) :
    ∃ a b : ℕ, Nat.card (rhoB hF B) * 2 ^ a = Nat.card (ModO2 B) * 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥B →* Equiv.Perm (Fin 77) := (rho hF).comp (Subgroup.inclusion hBM)
  have hrange : φ.range = rhoB hF B := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_rhoB hF).2 ⟨x, x.2, hBM x.2, rfl⟩
    · intro hp
      obtain ⟨x, hx, hxM, rfl⟩ := (mem_rhoB hF).1 hp
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : φ.ker ≤ CFSG.pCore 2 ↥B := by
    intro x hx
    have hxK : (x : J) ∈ Kgrp := (mem_Kgrp_iff hF ⟨x, hBM x.2⟩).2 hx
    have hO := inf_Kgrp_le_pCoreOf hF hBM hS hnc ⟨x.2, hxK⟩
    rw [pCoreOf_two_eq_map] at hO
    obtain ⟨y, hy, hyx⟩ := hO
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have h2 : IsPGroup 2 φ.ker := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).to_le hker
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp h2
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  have e1 := Subgroup.card_ker_mul_card_range φ
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
  refine ⟨a, b, ?_⟩
  rw [hrange, ha] at e1
  rw [hb] at e2
  calc Nat.card (rhoB hF B) * 2 ^ a = 2 ^ a * Nat.card (rhoB hF B) := mul_comm _ _
    _ = Nat.card ↥B := e1
    _ = _ := e2

end Kernel

section Cases

theorem rhoB_cases
    (hF : J4Facts)
    (hρ : B0Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) :
    rhoB hF B = LamP ∨ Nat.card (rhoB hF B) = 5760 ∨ Nat.card (rhoB hF B) = 443520 :=
  perfect_overgroups_77 hρ.phi (rhoB_le_MbarP hF hBM hB) (rhoB_perfect hF hBM hB)
    (rhoB_ne_bot hF hBM hB hB1) (fun t ht x hx =>
      rhoB_normalized hF hPB t (Tbar_le_rhoB_P0 hF ht) x hx)

theorem rhoB_eq_LamP_of_alt5
    (hF : J4Facts)
    (hρ : B0Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) (hS : IsSimpleGroup (ModO2 B))
    (hcard : Nat.card (ModO2 B) = 60) : rhoB hF B = LamP := by
  have hnc : ¬ (Nat.card (ModO2 B)).Prime := by rw [hcard]; norm_num
  obtain ⟨a, b, hab⟩ := card_rhoB_mul hF hBM hS hnc
  rw [hcard] at hab
  rcases rhoB_cases hF hρ hBM hB hB1 hPB with h | h | h
  · exact h
  · rw [h] at hab
    exact (card_match_false_alt5 (Or.inl rfl) hab).elim
  · rw [h] at hab
    exact (card_match_false_alt5 (Or.inr rfl) hab).elim

theorem false_of_psl32
    (hF : J4Facts)
    (hρ : B0Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) (hS : IsSimpleGroup (ModO2 B))
    (hcard : Nat.card (ModO2 B) = 168) : False := by
  have hnc : ¬ (Nat.card (ModO2 B)).Prime := by rw [hcard]; norm_num
  obtain ⟨a, b, hab⟩ := card_rhoB_mul hF hBM hS hnc
  rw [hcard] at hab
  rcases rhoB_cases hF hρ hBM hB hB1 hPB with h | h | h
  · rw [h, card_LamP hρ] at hab
    exact card_match_false_psl32 (Or.inl rfl) hab
  · rw [h] at hab
    exact card_match_false_psl32 (Or.inr (Or.inl rfl)) hab
  · rw [h] at hab
    exact card_match_false_psl32 (Or.inr (Or.inr rfl)) hab

end Cases

section Lifts

theorem rhoB_lift
    (hF : J4Facts) {B B' : Subgroup J} (hBM : B ≤ M2) (h : rhoB hF B = rhoB hF B') :
    ∀ b ∈ B, ∃ x ∈ B', ∃ k ∈ Kgrp, b = x * k := by
  intro b hb
  have hmem : rho hF ⟨b, hBM hb⟩ ∈ rhoB hF B' := h ▸ (mem_rhoB hF).2 ⟨b, hb, hBM hb, rfl⟩
  obtain ⟨x, hx, hxM, hxb⟩ := (mem_rhoB hF).1 hmem
  have hkM : x⁻¹ * b ∈ M2 := M2.mul_mem (M2.inv_mem hxM) (hBM hb)
  refine ⟨x, hx, x⁻¹ * b, ?_, by group⟩
  refine (mem_Kgrp_iff hF ⟨x⁻¹ * b, hkM⟩).2 ?_
  have e : (⟨x⁻¹ * b, hkM⟩ : ↥M2) = ⟨x, hxM⟩⁻¹ * ⟨b, hBM hb⟩ := rfl
  rw [e, map_mul, map_inv, hxb, inv_mul_cancel]

theorem mem_Qgrp_of_pow_eq_one
    (hF : J4Facts) {m : J} (hm : m ∈ Kgrp) (h : m ^ 2 ^ 15 = 1) : m ∈ Qgrp :=
  mem_of_pow_two_pow_fifteen Qgrp_le_Kgrp (Kgrp_normalizes_Qgrp hF)
    (CFSG.Quasithin.J4M2.NormalTwoGroup.index_subgroupOf_eq_of_card_eq_mul Qgrp_le_Kgrp
      (by rw [card_Kgrp hF, card_Qgrp hF.mat])) hm h

end Lifts

section Endgame

theorem eq_B0_of_rhoB_eq
    (hF : J4Facts) {B : Subgroup J} (hBM : B ≤ M2) (hB : ⁅B, B⁆ = B)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) (h : rhoB hF B = LamP) : B = B0 := by
  have hR := r0Facts_spec
  have hρ := b0Facts_spec
  have hM := hF.mat
  have hBB0 : rhoB hF B = rhoB hF B0 := h.trans (rhoB_B0 hF hρ).symm
  refine eq_of_perfect_lifts (isSolvable_Kgrp hF) hB hρ.perfect
    (fun k hk x hx => (Subgroup.mem_normalizer_iff.1 (hρ.knorm hk) x).1 hx) (rhoB_lift hF hBM hBB0)
    (rhoB_lift hF (B0_le_M2 hM) hBB0.symm) ?_
  intro m hm hmK
  have hm2 : m ∈ M2 := B0_le_M2 hM hm
  have h1 : rhoJ hF m = 1 := by
    rw [rhoJ_of_mem hF hm2]
    exact (mem_Kgrp_iff hF ⟨m, hm2⟩).1 hmK
  have hmR : m ∈ R0 := mem_R0_of_rhoJ_eq_one hF hρ hR hm h1
  have hpow : m ^ 2 ^ 15 = 1 := by
    have h2 := pow_card_eq_one' (G := ↥R0) (x := ⟨m, hmR⟩)
    rw [card_R0 hR] at h2
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    exact h3
  exact hPB (Qgrp_le_P0 hF (mem_Qgrp_of_pow_eq_one hF hmK hpow))

theorem j4_center_of_alt5
    (hF : J4Facts) {B : Subgroup J} (hB : ⁅B, B⁆ = B)
    (hB1 : B ≠ ⊥) (hBz : ∀ b ∈ B, z0 * b = b * z0)
    (hPB : P0 ≤ Subgroup.normalizer (B : Set J)) (hS : IsSimpleGroup (ModO2 B))
    (hcard : Nat.card (ModO2 B) = 60) :
    ∀ x ∈ CFSG.Open.pCoreOf 2 B, (∀ r ∈ CFSG.Open.pCoreOf 2 B, x * r = r * x) →
      ∀ b ∈ B, x * b = b * x := by
  have hR := r0Facts_spec
  have hρ := b0Facts_spec
  have hBM : B ≤ M2 := fun b hb' => Subgroup.mem_centralizer_singleton_iff.2 (hBz b hb').symm
  have hBeq := eq_B0_of_rhoB_eq hF hBM hB hPB (rhoB_eq_LamP_of_alt5 hF hρ hBM hB hB1 hPB hS hcard)
  subst hBeq
  have hR0 : IsPGroup 2 R0 := IsPGroup.of_card (card_R0 hR)
  have hR0O : R0 ≤ CFSG.Open.pCoreOf 2 B0 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 R0_le_B0
      (B0_le_normalizer_R0 hR) hR0
  have hcardO : Nat.card (CFSG.Open.pCoreOf 2 B0) ≤ 2 ^ 15 := by
    have e := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B0)
    have e' : Nat.card (CFSG.Open.pCoreOf 2 B0) = Nat.card (CFSG.pCore 2 ↥B0) := by
      rw [pCoreOf_two_eq_map]
      exact Subgroup.card_map_of_injective B0.subtype_injective
    have hle := card_B0_le hR
    rw [e, hcard] at hle
    rw [e']
    omega
  have hpO : R0 = CFSG.Open.pCoreOf 2 B0 :=
    Subgroup.eq_of_le_of_card_ge hR0O (by rw [card_R0 hR]; exact hcardO)
  intro x hx hc
  rw [← hpO] at hx hc
  exact center_R0 hR hx hc

theorem j4_false_of_psl32
    (hF : J4Facts) {B : Subgroup J} (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥)
    (hBz : ∀ b ∈ B, z0 * b = b * z0) (hPB : P0 ≤ Subgroup.normalizer (B : Set J))
    (hS : IsSimpleGroup (ModO2 B)) (hcard : Nat.card (ModO2 B) = 168) : False :=
  false_of_psl32 hF b0Facts_spec (fun b hb' =>
    Subgroup.mem_centralizer_singleton_iff.2 (hBz b hb').symm) hB hB1 hPB hS hcard

end Endgame

end CFSG.Quasithin.J4ZCent

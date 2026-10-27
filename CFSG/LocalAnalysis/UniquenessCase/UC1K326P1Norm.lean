module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Loc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem exists_central_three (h : Hyp326 G n P) :
    ∃ z : ↥P, z ∈ Subgroup.center ↥P ∧ orderOf z = 3 ∧ (z : G) ∈ Subgroup.center G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ew⟩ := h.wr
  obtain ⟨-, -, hc⟩ := zwr_card_center h.one_le ew
  have hdvd : 3 ∣ Nat.card (Subgroup.center ↥P) := by
    rw [hc]
    exact dvd_pow_self 3 (by have := h.one_le; omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥P) 3 hdvd
  have hxo : orderOf (x : ↥P) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  exact ⟨(x : ↥P), x.2, hxo, h.central (x : ↥P) x.2 (by rw [← hxo]; exact pow_orderOf_eq_one _)⟩

theorem rank_four_contradiction (h : Hyp326 G n P) {L₁ L₂ L₃ : Subgroup G}
    (h₁ : CFSG.Open.IsComponentOf L₁ ⊤) (h₂ : CFSG.Open.IsComponentOf L₂ ⊤)
    (h₃ : CFSG.Open.IsComponentOf L₃ ⊤)
    (h₁₂ : L₁ ≠ L₂) (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) : False := by
  obtain ⟨z, -, hzo, hzG⟩ := exists_central_three h
  obtain ⟨t₁, ht₁, hord₁, l₁, hl₁, hlt₁⟩ := exists_order_three_component h.core h₁
  obtain ⟨t₂, ht₂, hord₂, l₂, hl₂, hlt₂⟩ := exists_order_three_component h.core h₂
  obtain ⟨t₃, ht₃, hord₃, l₃, hl₃, hlt₃⟩ := exists_order_three_component h.core h₃
  have hzo' : orderOf (z : G) = 3 := by rw [Subgroup.orderOf_coe, hzo]
  have hzc : ∀ x : G, (z : G) * x = x * (z : G) := fun x => (Subgroup.mem_center_iff.1 hzG x).symm
  have hS1 : ∀ s ∈ ({(z : G)} : Set G), ∀ x ∈ L₁, s * x = x * s := by
    intro s hs x _
    rw [Set.mem_singleton_iff.mp hs]
    exact hzc x
  have hS2 : ∀ s ∈ ({(z : G), t₁} : Set G), ∀ x ∈ L₂, s * x = x * s := by
    intro s hs x hx
    rcases Set.mem_insert_iff.mp hs with h | h
    · rw [h]
      exact hzc x
    · rw [Set.mem_singleton_iff.mp h]
      exact component_commute h₁ h₂ h₁₂ ht₁ hx
  have hS3 : ∀ s ∈ ({(z : G), t₁, t₂} : Set G), ∀ x ∈ L₃, s * x = x * s := by
    intro s hs x hx
    rcases Set.mem_insert_iff.mp hs with h | hs
    · rw [h]
      exact hzc x
    rcases Set.mem_insert_iff.mp hs with h | h
    · rw [h]
      exact component_commute h₁ h₃ h₁₃ ht₁ hx
    · rw [Set.mem_singleton_iff.mp h]
      exact component_commute h₂ h₃ h₂₃ ht₂ hx
  have hb1 : t₁ ∉ Subgroup.closure ({(z : G)} : Set G) := nf_notMem_closure hS1 hl₁ hlt₁
  have hc1 : t₂ ∉ Subgroup.closure ({(z : G), t₁} : Set G) := nf_notMem_closure hS2 hl₂ hlt₂
  have hd1 : t₃ ∉ Subgroup.closure ({(z : G), t₁, t₂} : Set G) := nf_notMem_closure hS3 hl₃ hlt₃
  have hpow : ∀ t : G, orderOf t = 3 → t ^ 3 = 1 := fun t ht => by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hne : ∀ t : G, orderOf t = 3 → t ≠ 1 := fun t ht h => by
    rw [h, orderOf_one] at ht
    norm_num at ht
  obtain ⟨hE, hcard⟩ := card_closure_four (hzc t₁) (hzc t₂) (hzc t₃)
    (component_commute h₁ h₂ h₁₂ ht₁ ht₂) (component_commute h₁ h₃ h₁₃ ht₁ ht₃)
    (component_commute h₂ h₃ h₂₃ ht₂ ht₃) (hpow _ hzo') (hpow _ hord₁) (hpow _ hord₂)
    (hpow _ hord₃) (hne _ hzo') hb1 hc1 hd1
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE (hcard.trans (by norm_num))
  have h3 := pRank_top_le_three h
  omega

theorem map_conj_map_conj (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_ne_of_odd_order {g : G} (hg : Odd (orderOf g)) {L : Subgroup G}
    (hne : L.map (MulAut.conj g).toMonoidHom ≠ L) :
    L ≠ L.map (MulAut.conj (g ^ 2)).toMonoidHom ∧
      L.map (MulAut.conj g).toMonoidHom ≠ L.map (MulAut.conj (g ^ 2)).toMonoidHom := by
  have hpow : ∀ a : G, L.map (MulAut.conj a).toMonoidHom = L →
      ∀ m : ℕ, L.map (MulAut.conj (a ^ m)).toMonoidHom = L := by
    intro a ha m
    induction m with
    | zero =>
      ext x
      simp [MulAut.conj_apply]
    | succ m ih =>
      rw [pow_succ', ← map_conj_map_conj, ih, ha]
  refine ⟨fun h => hne ?_, fun h => hne ?_⟩
  · obtain ⟨j, hj⟩ := hg
    have hg' : g = (g ^ 2) ^ (j + 1) := by
      rw [← pow_mul, show 2 * (j + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have h2 : L.map (MulAut.conj (g ^ 2)).toMonoidHom = L := h.symm
    conv_lhs => rw [hg']
    exact hpow (g ^ 2) h2 (j + 1)
  · have h1 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
    rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel,
      show g⁻¹ * g ^ 2 = g by group] at h1
    have h0 : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
      ext x
      simp [MulAut.conj_apply]
    rw [h0] at h1
    exact h1.symm

theorem comp_normalized (h : Hyp326 G n P) {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) :
    P ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  by_contra hgn
  have hodd : Odd (orderOf g) := by
    obtain ⟨m, hm⟩ := h.sylow.isPGroup ⟨g, hg⟩
    have hdvd : orderOf g ∣ 3 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg (fun y : ↥P => (y : G)) hm
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat hdvd
  have hne : L.map (MulAut.conj g).toMonoidHom ≠ L := by
    intro heq
    apply hgn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← heq]
      exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := by simpa [MulAut.conj_apply] using hyx
      exact hyx' ▸ hy
  obtain ⟨h1, h2⟩ := conj_ne_of_odd_order hodd hne
  exact rank_four_contradiction h hL
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.isComponentOf_map_conj hL g)
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.isComponentOf_map_conj hL (g ^ 2))
    (fun he => hne he.symm) h1 h2

theorem comp_center_ne_bot (h : Hyp326 G n P) {L : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤) :
    Subgroup.center ↥L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ew⟩ := h.wr
  obtain ⟨z, hzP, hzo, hzG⟩ := exists_central_three h
  have hnorm := comp_normalized h hL
  have hN : ((P ⊓ L).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
    refine ⟨(g * x * g⁻¹ : ↥P).2, ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hnorm g.2) (x : G)).1 hx.2
    simpa using this
  have hN1 : (P ⊓ L).subgroupOf P ≠ ⊥ := by
    intro hbot
    have hcard := (comp_isSylowOf_inf h.sylow hL).card_eq
    have hdvd := comp_three_dvd_card h.core hL
    have hpos : 0 < (Nat.card ↥L).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hdvd
    have h1 : Nat.card ↥(P ⊓ L) = 1 := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ L ≤ P)).toEquiv,
        hbot]
      simp
    rw [hcard] at h1
    have h2 : 3 ^ 1 ≤ 3 ^ (Nat.card ↥L).factorization 3 :=
      Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hzN : z ∈ (P ⊓ L).subgroupOf P :=
    zwr_normal_contains_omega_center h.one_le ew hN hN1 z hzP
      (by rw [← hzo]; exact pow_orderOf_eq_one z)
  have hzL : (z : G) ∈ L := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hzN)).2
  intro hbot
  have hmem : (⟨(z : G), hzL⟩ : ↥L) ∈ Subgroup.center ↥L :=
    Subgroup.mem_center_iff.2 (fun g => Subtype.ext (Subgroup.mem_center_iff.1 hzG g))
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1' : (z : G) = 1 := congrArg (fun y : ↥L => (y : G)) hmem
  have hz1 : z = 1 := Subtype.ext hz1'
  rw [hz1, orderOf_one] at hzo
  norm_num at hzo

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF81Sec52C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81F4Fusion

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, Commute x y) {x : G} :
    x ∈ H ⊔ K ↔ ∃ y ∈ H, ∃ z ∈ K, y * z = x := by
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, K.one_mem, by simp⟩
      · exact ⟨1, H.one_mem, x, hx, by simp⟩
    · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      refine ⟨y₁ * y₂, H.mul_mem hy₁ hy₂, z₁ * z₂, K.mul_mem hz₁ hz₂, ?_⟩
      have := (h y₂ hy₂ z₁ hz₁).eq
      calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
        _ = y₁ * (z₁ * y₂) * z₂ := by rw [this]
        _ = y₁ * z₁ * (y₂ * z₂) := by group
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      refine ⟨y⁻¹, H.inv_mem hy, z⁻¹, K.inv_mem hz, ?_⟩
      have := (h y hy z hz).eq
      calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
        _ = (y * z)⁻¹ := by rw [← this]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

section Loc

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem cenS_K0_eq (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    CenS (Subgroup.closure ({b, t₀} : Set G)) = L := by
  have h0 := h5.opp_eq_bot
  have hB := h5.basis
  have hbord : orderOf b = 3 := hB.hyp.ord
  apply le_antisymm
  · intro x hx
    have hxb : x ∈ Cen b := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx b (Subgroup.subset_closure (by simp))).symm
    have hxt : t₀ * x = x * t₀ :=
      Subgroup.mem_centralizer_iff.1 hx t₀ (Subgroup.subset_closure (by simp))
    obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h0 hxb
    have hlt : t₀ * l = l * t₀ := (Subgroup.mem_centralizer_iff.1 h5.ht₀L l hl).symm
    have h1 : t₀ * b ^ i * t₀⁻¹ = (b ^ i)⁻¹ := by
      have : t₀ * b ^ i * t₀⁻¹ = (t₀ * b * t₀⁻¹) ^ i := (conj_zpow).symm
      rw [this, h5.ht₀b, inv_zpow]
    have h2 : (b ^ i)⁻¹ * l = b ^ i * l := by
      have : t₀ * (b ^ i * l) * t₀⁻¹ = b ^ i * l := by
        rw [mul_inv_eq_iff_eq_mul]; exact hxt
      calc (b ^ i)⁻¹ * l = (t₀ * b ^ i * t₀⁻¹) * (t₀ * l * t₀⁻¹) := by
            rw [h1, show t₀ * l * t₀⁻¹ = l by rw [hlt]; group]
        _ = t₀ * (b ^ i * l) * t₀⁻¹ := by group
        _ = b ^ i * l := this
    have h3 : b ^ i * b ^ i = 1 := by
      have h' := mul_right_cancel h2
      calc b ^ i * b ^ i = (b ^ i)⁻¹ * b ^ i := by nth_rw 1 [← h']
        _ = 1 := inv_mul_cancel _
    have h4 : b ^ i = 1 := by
      have h5' : b ^ (i * 2) = 1 := by
        rw [show i * 2 = i + i by ring, zpow_add]; exact h3
      have hd : (orderOf b : ℤ) ∣ i * 2 := orderOf_dvd_iff_zpow_eq_one.2 h5'
      rw [hbord] at hd
      have : (3 : ℤ) ∣ i := by omega
      exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hbord]; exact_mod_cast this)
    rw [h4, one_mul]
    exact hl
  · rw [← Subgroup.le_centralizer_iff, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.1 (hB.hyp.hLC hl)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h5.ht₀L

theorem cenS_K4_eq (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    (hM : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G)) = M := by
  obtain ⟨hMc, -, -, hMβ, -, -⟩ := hM
  apply le_antisymm
  · intro x hx
    have hxβ : x ∈ Cen (β' b₂ b₃) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx (β' b₂ b₃) (Subgroup.subset_closure (by simp))).symm
    have hxs : s₀ * x = x * s₀ :=
      Subgroup.mem_centralizer_iff.1 hx s₀ (Subgroup.subset_closure (by simp))
    have hMβc : ∀ m ∈ M, Commute (β' b₂ b₃) m := fun m hm =>
      (Subgroup.mem_centralizer_iff.1 (hMc hm) (β' b₂ b₃) (Subgroup.subset_closure (by simp)))
    have hMs : ∀ m ∈ M, s₀ * m = m * s₀ := fun m hm =>
      Subgroup.mem_centralizer_iff.1 (hMc hm) s₀ (Subgroup.subset_closure (by simp))
    rw [← hMβ] at hxβ
    obtain ⟨y, hy, m, hm, rfl⟩ := (mem_sup_of_commute (H := Subgroup.zpowers (β' b₂ b₃)) (K := M)
      (fun x hx y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        exact (hMβc y hy).zpow_left k)).1 hxβ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h1 : s₀ * β' b₂ b₃ ^ k = β' b₂ b₃ ^ k * s₀ := by
      apply mul_right_cancel (b := m)
      calc s₀ * β' b₂ b₃ ^ k * m = s₀ * (β' b₂ b₃ ^ k * m) := by group
        _ = β' b₂ b₃ ^ k * m * s₀ := hxs
        _ = β' b₂ b₃ ^ k * (m * s₀) := by group
        _ = β' b₂ b₃ ^ k * (s₀ * m) := by rw [hMs m hm]
        _ = β' b₂ b₃ ^ k * s₀ * m := by group
    have h2 : s₀ * β' b₂ b₃ ^ k * s₀⁻¹ = (β' b₂ b₃ ^ k)⁻¹ := by
      have : s₀ * β' b₂ b₃ ^ k * s₀⁻¹ = (s₀ * β' b₂ b₃ * s₀⁻¹) ^ k := conj_zpow.symm
      rw [this, h5.hs₀b, inv_zpow]
    have h3 : β' b₂ b₃ ^ k = (β' b₂ b₃ ^ k)⁻¹ := by
      rw [← h2, h1]; group
    have h4 : β' b₂ b₃ ^ k * β' b₂ b₃ ^ k = 1 := by
      calc β' b₂ b₃ ^ k * β' b₂ b₃ ^ k = (β' b₂ b₃ ^ k)⁻¹ * β' b₂ b₃ ^ k := by nth_rw 1 [← h3]
        _ = 1 := inv_mul_cancel _
    have h5' : β' b₂ b₃ ^ (k * 2) = 1 := by
      rw [show k * 2 = k + k by ring, zpow_add]; exact h4
    have hd : (orderOf (β' b₂ b₃) : ℤ) ∣ k * 2 := orderOf_dvd_iff_zpow_eq_one.2 h5'
    rw [h5.β_orderOf] at hd
    have h3k : (3 : ℤ) ∣ k := by omega
    have : β' b₂ b₃ ^ k = 1 :=
      orderOf_dvd_iff_zpow_eq_one.1 (by rw [h5.β_orderOf]; exact_mod_cast h3k)
    rw [this, one_mul]
    exact hm
  · exact hMc

theorem card_cen_beta (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    (hM : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Nat.card ↥(Cen (β' b₂ b₃)) = 3 * Nat.card ↥M := by
  have hcomm : M ≤ Subgroup.centralizer ((Subgroup.zpowers (β' b₂ b₃) : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have : Commute (β' b₂ b₃) m :=
      Subgroup.mem_centralizer_iff.1 (hM.1 hm) (β' b₂ b₃) (Subgroup.subset_closure (by simp))
    exact (this.zpow_left k).eq
  rw [← hM.2.2.2.1, CFSG.SeitzReduction.F4Pilot.card_sup_eq_mul_of_le_centralizer hcomm
    hM.2.2.2.2.1, Nat.card_zpowers, h5.β_orderOf]

omit [Finite G] in
theorem card_eq_mul_of_setMul {H K C : Subgroup G} (h : setMul H K = (C : Set G))
    (hd : H ⊓ K = ⊥) : Nat.card C = Nat.card H * Nat.card K := by
  rw [← Nat.card_prod]
  have hmem : ∀ p : H × K, (p.1 : G) * p.2 ∈ C := fun p => by
    have : (p.1 : G) * p.2 ∈ setMul H K := ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
    rw [h] at this
    exact this
  refine (Nat.card_congr (Equiv.ofBijective (fun p : H × K => (⟨(p.1 : G) * p.2, hmem p⟩ : C))
    ⟨fun p p' hpp => ?_, fun x => ?_⟩)).symm
  · have h1 : (p.1 : G) * p.2 = p'.1 * p'.2 := congrArg Subtype.val hpp
    have h2 : ((p'.1 : G))⁻¹ * p.1 = p'.2 * (p.2 : G)⁻¹ := by
      calc ((p'.1 : G))⁻¹ * p.1 = (p'.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
        _ = (p'.1 : G)⁻¹ * (p'.1 * p'.2) * (p.2 : G)⁻¹ := by rw [h1]
        _ = p'.2 * (p.2 : G)⁻¹ := by group
    have h3 : ((p'.1 : G))⁻¹ * p.1 ∈ H ⊓ K :=
      ⟨H.mul_mem (H.inv_mem p'.1.2) p.1.2, h2 ▸ K.mul_mem p'.2.2 (K.inv_mem p.2.2)⟩
    rw [hd, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : p.1 = p'.1 := Subtype.ext h3.symm
    have h5 : (p.2 : G) = p'.2 := by
      have := h1
      rw [show (p.1 : G) = p'.1 from h3.symm] at this
      exact mul_left_cancel this
    exact Prod.ext h4 (Subtype.ext h5)
  · have hx : (x : G) ∈ setMul H K := by rw [h]; exact x.2
    obtain ⟨a, ha, k, hk, hak⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨k, hk⟩), Subtype.ext hak.symm⟩

theorem op_two_inf_eq_bot {x : G} {M : Subgroup G} (hM : StatedClassicalModel M .PSp 3 2 1)
    (hMc : M ≤ Cen x) : Op 2 (Cen x) ⊓ M = ⊥ := by
  haveI : IsSimpleGroup ↥M := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hM
  have hN : ((Op 2 (Cen x) ⊓ M).subgroupOf M).Normal := ⟨fun n hn m => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, M.mul_mem (M.mul_mem m.2 hn.2) (M.inv_mem m.2)⟩
    have := Op_conj_mem (p := 2) (H := Cen x) (hMc m.2) hn.1
    simpa using this⟩
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Op 2 (Cen x) ⊓ M).subgroupOf M) with h | h
  · rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hy.2⟩ : ↥M) ∈ (Op 2 (Cen x) ⊓ M).subgroupOf M := hy
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hle : M ≤ Op 2 (Cen x) := fun y hy => by
      have : (⟨y, hy⟩ : ↥M) ∈ (Op 2 (Cen x) ⊓ M).subgroupOf M := by rw [h]; trivial
      exact this.1
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥M :=
      (Op_isPGroup (p := 2) (Cen x)).of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [CFSG.RankThree.PartTwo.Sec21.FF81.F4.card_model_sp6 hM] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem card_cen_of_decomp {x : G} {M : Subgroup G} (hM : StatedClassicalModel M .PSp 3 2 1)
    (hMc : M ≤ Cen x) (hdec : setMul (Op 2 (Cen x)) M = (Cen x : Set G))
    {S₀ S₁ : Subgroup G} (h0 : IsElemAb 2 6 S₀) (h1 : IsExtraspecialPlus 4 S₁)
    (hsup : S₀ ⊔ S₁ = Op 2 (Cen x)) (hinf : S₀ ⊓ S₁ = ⊥) (hc : S₀ ≤ CenS S₁) :
    Nat.card ↥(Cen x) = 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  have hS : Nat.card ↥(Op 2 (Cen x)) = 2 ^ 15 := by
    rw [← hsup, sup_comm,
      CFSG.SeitzReduction.F4Pilot.card_sup_eq_mul_of_le_centralizer hc
        (by rw [inf_comm]; exact hinf),
      h0.2, h1.2.1]
    norm_num
  rw [card_eq_mul_of_setMul hdec (op_two_inf_eq_bot hM hMc), hS,
    CFSG.RankThree.PartTwo.Sec21.FF81.F4.card_model_sp6 hM]
  norm_num

theorem K0_le_cenS (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {R : Subgroup G} (hRL : R ≤ L) :
    Subgroup.closure ({b, t₀} : Set G) ≤ CenS R := by
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | hy
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (h5.basis.hyp.hLC (hRL hl))
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 h5.ht₀L l (hRL hl))

theorem cenS_le_M (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    (hM : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) {R : Subgroup G}
    (hR : Subgroup.closure ({β' b₂ b₃, s₀} : Set G) ≤ R) : CenS R ≤ M := by
  rw [← cenS_K4_eq h5 hM]
  exact Subgroup.centralizer_le hR

theorem card_M_inf_cenS_K0 (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    (hM : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) :
    Nat.card ↥(M ⊓ CenS (Subgroup.closure ({b, t₀} : Set G))) =
      Nat.card ↥(L ⊓ CenS (Subgroup.closure ({β' b₂ b₃, s₀} : Set G))) := by
  rw [cenS_K0_eq h5, cenS_K4_eq h5 hM, inf_comm]

theorem card_M_inf_cen_b (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G} (hbM : b ∈ M) :
    Nat.card ↥(M ⊓ Cen b) = 3 * Nat.card ↥(M ⊓ L) := by
  have h0 := h5.opp_eq_bot
  have hB := h5.basis
  have hbord : orderOf b = 3 := hB.hyp.ord
  have hset : setMul (Subgroup.zpowers b) (M ⊓ L) = ((M ⊓ Cen b : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨u, hu, l, hl, rfl⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      refine ⟨M.mul_mem (M.zpow_mem hbM i) hl.1, ?_⟩
      show b ^ i * l ∈ Cen b
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : b * b ^ i = b ^ i * b := (Commute.self_zpow b i).eq
      have h2 : b * l = l * b :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hB.hyp.hLC hl.2)).symm
      calc b ^ i * l * b = b ^ i * (l * b) := by group
        _ = b ^ i * (b * l) := by rw [h2]
        _ = (b ^ i * b) * l := by group
        _ = b * b ^ i * l := by rw [h1]
        _ = b * (b ^ i * l) := by group
    · intro hy
      obtain ⟨i, l, hl, hyl⟩ := hB.cen_dec' h0 hy.2
      refine ⟨b ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) i, l, ⟨?_, hl⟩, hyl⟩
      have : l = (b ^ i)⁻¹ * y := by rw [hyl]; group
      rw [this]
      exact M.mul_mem (M.inv_mem (M.zpow_mem hbM i)) hy.1
  have hdisj : Subgroup.zpowers b ⊓ (M ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxb, hxM, hxL⟩
    have hxcL : x ∈ CenS L := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hcomm : Commute b l := (Subgroup.mem_centralizer_singleton_iff.1
        (hB.hyp.hLC hl)).symm
      exact ((hcomm.zpow_left i).eq).symm
    have := hB.inf_cenS_self
    rw [eq_bot_iff] at this
    exact this ⟨hxL, hxcL⟩
  rw [card_eq_mul_of_setMul hset hdisj, Nat.card_zpowers, hbord]

theorem exists_mem_M_conj_b (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    (hM : FF81Conc5_7 b b₁ b₂ b₃ s₀ M) : ∃ m ∈ M, m * b * m⁻¹ = b₁ := by
  have hB := h5.basis
  obtain ⟨n, -, hn0, hn1, hn2, hn3⟩ := h5.mono4.1.2.2.2.1
  have hnβ : n * β' b₂ b₃ = β' b₂ b₃ * n := by
    have : n * β' b₂ b₃ * n⁻¹ = β' b₂ b₃ := by
      simp only [β']
      rw [show n * (b₂ * b₃ ^ 2) * n⁻¹ = (n * b₂ * n⁻¹) * ((n * b₃ * n⁻¹) * (n * b₃ * n⁻¹)) by
        rw [pow_two]; group, hn2, hn3, sq]
    exact (mul_inv_eq_iff_eq_mul.1 this)
  have hnC : n ∈ Cen (β' b₂ b₃) := Subgroup.mem_centralizer_singleton_iff.2 hnβ
  rw [← hM.2.2.2.1] at hnC
  obtain ⟨y, hy, m, hm, hnm⟩ := (mem_sup_of_commute (H := Subgroup.zpowers (β' b₂ b₃)) (K := M)
    (fun x hx y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact (Commute.zpow_left (Subgroup.mem_centralizer_iff.1 (hM.1 hy) (β' b₂ b₃)
        (Subgroup.subset_closure (by simp))) k))).1 hnC
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨m, hm, ?_⟩
  have hβB : β' b₂ b₃ ∈ B := h5.β_mem
  have hβk : β' b₂ b₃ ^ k ∈ B := B.zpow_mem hβB k
  have hb₁B : b₁ ∈ B := hB.mem_B (by simp)
  have hcomm : b₁ * β' b₂ b₃ ^ k = β' b₂ b₃ ^ k * b₁ := hB.B_comm hb₁B hβk
  have hmn : m = (β' b₂ b₃ ^ k)⁻¹ * n := by rw [← hnm]; group
  calc m * b * m⁻¹ = (β' b₂ b₃ ^ k)⁻¹ * (n * b * n⁻¹) * β' b₂ b₃ ^ k := by rw [hmn]; group
    _ = (β' b₂ b₃ ^ k)⁻¹ * b₁ * β' b₂ b₃ ^ k := by rw [hn0]
    _ = b₁ := by rw [mul_assoc, hcomm, inv_mul_cancel_left]

omit [Finite G] in
theorem card_M_inf_cen_conj {M : Subgroup G} {m : G} (hm : m ∈ M) (x : G) :
    Nat.card ↥(M ⊓ Cen (m * x * m⁻¹)) = Nat.card ↥(M ⊓ Cen x) := by
  have h : M ⊓ Cen (m * x * m⁻¹) = (M ⊓ Cen x).map (MulAut.conj m).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨hyM, hyC⟩
      refine ⟨m⁻¹ * y * m, ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm, ?_⟩, by simp [mul_assoc]⟩
      have hyC' : y * (m * x * m⁻¹) = (m * x * m⁻¹) * y :=
        Subgroup.mem_centralizer_singleton_iff.1 hyC
      show m⁻¹ * y * m ∈ Cen x
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc m⁻¹ * y * m * x = m⁻¹ * (y * (m * x * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x * m⁻¹) * y) * m := by rw [hyC']
        _ = x * (m⁻¹ * y * m) := by group
    · rintro ⟨z, ⟨hzM, hzC⟩, rfl⟩
      refine ⟨M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm), ?_⟩
      have hzC' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.1 hzC
      show (MulAut.conj m).toMonoidHom z ∈ Cen (m * x * m⁻¹)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc m * z * m⁻¹ * (m * x * m⁻¹) = m * (z * x) * m⁻¹ := by group
        _ = m * (x * z) * m⁻¹ := by rw [hzC']
        _ = m * x * m⁻¹ * (m * z * m⁻¹) := by group
  rw [h, Subgroup.card_map_of_injective (MulAut.conj m).injective]

omit [Finite G] in
theorem zpow_eq_one_of_inv_eq_self {a : G} (ha : orderOf a = 3) {i : ℤ} (h : (a ^ i)⁻¹ = a ^ i) :
    a ^ i = 1 := by
  have h3 : a ^ i * a ^ i = 1 := by
    calc a ^ i * a ^ i = (a ^ i)⁻¹ * a ^ i := by nth_rw 1 [← h]
      _ = 1 := inv_mul_cancel _
  have h4 : a ^ (i * 2) = 1 := by rw [show i * 2 = i + i by ring, zpow_add]; exact h3
  have hd : (orderOf a : ℤ) ∣ i * 2 := orderOf_dvd_iff_zpow_eq_one.2 h4
  rw [ha] at hd
  have h3i : (3 : ℤ) ∣ i := by omega
  exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [ha]; exact_mod_cast h3i)

theorem card_M_inf_cenS_K2 (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {M : Subgroup G}
    {K₂ K₂' : Subgroup G} {t₁ : G} (hK₂ : K₂ = Subgroup.closure ({b₁, t₁} : Set G))
    (ht₁b : t₁ * b₁ * t₁⁻¹ = b₁⁻¹) (hK₂L : K₂ ≤ L) (hK₂M : K₂ ≤ M)
    (hK₂'L : K₂' ≤ L) (hK₂'M : K₂' ≤ M) (hK₂'6 : Nat.card ↥K₂' = 6)
    (hcomm : ∀ z ∈ K₂, ∀ w ∈ K₂', z * w = w * z)
    (hK₀M : Subgroup.closure ({b, t₀} : Set G) ≤ M)
    (hK₀card : Nat.card ↥(Subgroup.closure ({b, t₀} : Set G)) = 6)
    (hb₁3 : orderOf b₁ = 3) (hcard : Nat.card ↥(M ⊓ Cen b₁) = 108) :
    Nat.card ↥(M ⊓ CenS K₂) = 36 := by
  have hB := h5.basis
  set K₀ : Subgroup G := Subgroup.closure ({b, t₀} : Set G) with hK₀def
  have hK₀L : K₀ ≤ CenS L := K0_le_cenS h5 (le_refl L)
  have hb₁K₂ : b₁ ∈ K₂ := hK₂ ▸ Subgroup.subset_closure (by simp)
  have ht₁K₂ : t₁ ∈ K₂ := hK₂ ▸ Subgroup.subset_closure (by simp)
  have hK₀x : ∀ x ∈ K₀, ∀ l ∈ L, x * l = l * x := fun x hx l hl =>
    (Subgroup.mem_centralizer_iff.1 (hK₀L hx) l hl).symm
  have hK₀K₂' : K₂' ≤ Subgroup.centralizer (K₀ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hK₀x x hx w (hK₂'L hw)
  have hdisj : K₀ ⊓ K₂' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx0, hx2⟩
    have := hB.inf_cenS_self
    rw [eq_bot_iff] at this
    exact this ⟨hK₂'L hx2, hK₀L hx0⟩
  have hU : Nat.card ↥(K₀ ⊔ K₂') = 36 := by
    rw [CFSG.SeitzReduction.F4Pilot.card_sup_eq_mul_of_le_centralizer hK₀K₂' hdisj, hK₀card,
      hK₂'6]
  have hK₀K₂'c : ∀ x ∈ K₀, ∀ w ∈ K₂', Commute x w := fun x hx w hw => hK₀x x hx w (hK₂'L hw)
  have hUc : ∀ u ∈ K₀ ⊔ K₂', ∀ k ∈ K₂, u * k = k * u := by
    intro u hu k hk
    obtain ⟨x, hx, w, hw, rfl⟩ := (mem_sup_of_commute hK₀K₂'c).1 hu
    have h1 : x * k = k * x := hK₀x x hx k (hK₂L hk)
    have h2 : w * k = k * w := (hcomm k hk w hw).symm
    calc x * w * k = x * (w * k) := by group
      _ = x * (k * w) := by rw [h2]
      _ = (x * k) * w := by group
      _ = (k * x) * w := by rw [h1]
      _ = k * (x * w) := by group
  have hUM : K₀ ⊔ K₂' ≤ M := sup_le hK₀M hK₂'M
  have hb₁U : Subgroup.zpowers b₁ ⊓ (K₀ ⊔ K₂') = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxb, hxU⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxb
    obtain ⟨y, hy, w, hw, hyw⟩ := (mem_sup_of_commute hK₀K₂'c).1 hxU
    have hyL : y ∈ L := by
      have : y = b₁ ^ i * w⁻¹ := by rw [← hyw]; group
      rw [this]
      exact L.mul_mem (L.zpow_mem (hK₂L hb₁K₂) i) (L.inv_mem (hK₂'L hw))
    have hy1 : y = 1 := by
      have := hB.inf_cenS_self
      rw [eq_bot_iff] at this
      exact Subgroup.mem_bot.1 (this ⟨hyL, hK₀L hy⟩)
    rw [hy1, one_mul] at hyw
    have hcw : t₁ * w = w * t₁ := hcomm t₁ ht₁K₂ w hw
    have h1 : t₁ * b₁ ^ i * t₁⁻¹ = (b₁ ^ i)⁻¹ := by
      rw [show t₁ * b₁ ^ i * t₁⁻¹ = (t₁ * b₁ * t₁⁻¹) ^ i from conj_zpow.symm, ht₁b, inv_zpow]
    have h2 : (b₁ ^ i)⁻¹ = b₁ ^ i := by
      rw [← h1, ← hyw]
      calc t₁ * w * t₁⁻¹ = w * t₁ * t₁⁻¹ := by rw [hcw]
        _ = w := by group
    rw [zpow_eq_one_of_inv_eq_self hb₁3 h2]
    exact Subgroup.one_mem _
  have hb₁c : ∀ a ∈ Subgroup.zpowers b₁, ∀ u ∈ K₀ ⊔ K₂', Commute a u := by
    intro a ha u hu
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact (hUc u hu (b₁ ^ i) (K₂.zpow_mem hb₁K₂ i)).symm
  have hUb₁ : K₀ ⊔ K₂' ≤ Subgroup.centralizer ((Subgroup.zpowers b₁ : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hb₁c a ha u hu).eq
  have hV : Nat.card ↥(Subgroup.zpowers b₁ ⊔ (K₀ ⊔ K₂')) = 108 := by
    rw [CFSG.SeitzReduction.F4Pilot.card_sup_eq_mul_of_le_centralizer hUb₁ hb₁U, Nat.card_zpowers,
      hb₁3, hU]
  have hVle : Subgroup.zpowers b₁ ⊔ (K₀ ⊔ K₂') ≤ M ⊓ Cen b₁ := by
    refine sup_le ?_ ?_
    · refine le_inf (Subgroup.zpowers_le.2 (hK₂M hb₁K₂)) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · refine le_inf hUM fun u hu => ?_
      exact Subgroup.mem_centralizer_singleton_iff.2 (hUc u hu b₁ hb₁K₂)
  have hVeq : Subgroup.zpowers b₁ ⊔ (K₀ ⊔ K₂') = M ⊓ Cen b₁ :=
    Subgroup.eq_of_le_of_card_ge hVle (by rw [hV, hcard])
  have hEq : M ⊓ CenS K₂ = K₀ ⊔ K₂' := by
    apply le_antisymm
    · rintro x ⟨hxM, hxC⟩
      have hxb : x ∈ M ⊓ Cen b₁ := ⟨hxM, Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hxC b₁ hb₁K₂).symm⟩
      rw [← hVeq] at hxb
      obtain ⟨y, hy, u, hu, hyu⟩ := (mem_sup_of_commute hb₁c).1 hxb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      subst hyu
      have hct : t₁ * (b₁ ^ i * u) = (b₁ ^ i * u) * t₁ :=
        Subgroup.mem_centralizer_iff.1 hxC t₁ ht₁K₂
      have hut : u * t₁ = t₁ * u := hUc u hu t₁ ht₁K₂
      have hcomm' : t₁ * b₁ ^ i = b₁ ^ i * t₁ := by
        apply mul_right_cancel (b := u)
        calc t₁ * b₁ ^ i * u = t₁ * (b₁ ^ i * u) := by group
          _ = (b₁ ^ i * u) * t₁ := hct
          _ = b₁ ^ i * (u * t₁) := by group
          _ = b₁ ^ i * (t₁ * u) := by rw [hut]
          _ = b₁ ^ i * t₁ * u := by group
      have h1 : t₁ * b₁ ^ i * t₁⁻¹ = (b₁ ^ i)⁻¹ := by
        rw [show t₁ * b₁ ^ i * t₁⁻¹ = (t₁ * b₁ * t₁⁻¹) ^ i from conj_zpow.symm, ht₁b, inv_zpow]
      have h2 : (b₁ ^ i)⁻¹ = b₁ ^ i := by
        rw [← h1, hcomm']; group
      rw [zpow_eq_one_of_inv_eq_self hb₁3 h2, one_mul]
      exact hu
    · intro u hu
      refine ⟨hUM hu, ?_⟩
      show u ∈ CenS K₂
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hUc u hu k hk).symm
  rw [hEq, hU]

end Loc

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6

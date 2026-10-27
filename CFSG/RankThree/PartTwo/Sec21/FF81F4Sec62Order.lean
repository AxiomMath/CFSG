module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62Lib
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.Classical

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

def K3Clause (Y : Subgroup G) : Prop :=
  ∀ x ∈ Y, orderOf x = 3 → 3 ^ 6 ∣ Nat.card ↥(Y ⊓ Cen x) ∨
    Nat.card ↥(Y ⊓ Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7

theorem card_sp6 {M : Subgroup G} (hM : StatedClassicalModel M .PSp 3 2 1) :
    Nat.card M = 1451520 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem not_dvd_card_cen (hB : FF81Basis b L B b₁ b₂ b₃) : ¬ 3 ^ 6 ∣ Nat.card (Cen b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Cen b ⊓ CenS L with hD
  have hDN : D ≤ Nor L := fun d hd =>
    Subgroup.centralizer_le_normalizer _ hd.2
  have hsup : D ⊔ L = Cen b := by
    refine le_antisymm (sup_le inf_le_left hB.hyp.hLC) fun x hx => ?_
    obtain ⟨l, hl, hd⟩ := hB.hyp.exists_decomp hx
    have : x = l * (l⁻¹ * x) := by group
    rw [this]
    exact (D ⊔ L).mul_mem (Subgroup.mem_sup_right hl) (Subgroup.mem_sup_left hd)
  have hinf : D ⊓ L = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← hB.inf_cenS_self]
    exact ⟨hx.2, hx.1.2⟩
  have e := card_sup_mul_card_inf D L hDN
  rw [hsup, hinf, Subgroup.card_bot, mul_one] at e
  intro h6
  rw [e, hB.card_L] at h6
  have h2 : 3 ^ 2 ∣ Nat.card D := by
    have h1 : 3 ^ 2 * 3 ^ 4 ∣ 3 ^ 4 * (Nat.card D * (2 ^ 9 * 5 * 7)) := by
      have : (3 : ℕ) ^ 2 * 3 ^ 4 = 3 ^ 6 := by norm_num
      rw [this]
      convert h6 using 1
      norm_num
      ring
    have h3 : 3 ^ 2 ∣ Nat.card D * (2 ^ 9 * 5 * 7) := by
      rw [mul_comm (3 ^ 2) (3 ^ 4)] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) h3
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h2
  have hKp : IsPGroup 3 (K.map D.subtype) := (IsPGroup.of_card hK).map D.subtype
  have hKle : K.map D.subtype ≤ Subgroup.zpowers b := by
    intro y hy
    have hyD : y ∈ D := Subgroup.map_subtype_le K hy
    refine hB.mem_zpowers_of_isPGroup hyD.1 hyD.2 ?_
    exact hKp.to_le (Subgroup.zpowers_le.mpr hy)
  have := Subgroup.card_le_of_le hKle
  rw [Subgroup.card_map_of_injective D.subtype_injective, hK, Nat.card_zpowers,
    hB.hyp.ord] at this
  norm_num at this

theorem cen_eq_sup_of_le {Y : Subgroup G} (hB : FF81Basis b L B b₁ b₂ b₃)
    (hCb : Cen b ≤ Y) (K3 : K3Clause Y) :
    Nat.card (Cen b) = 2 ^ 9 * 3 ^ 5 * 5 * 7 ∧ Cen b = Subgroup.zpowers b ⊔ L := by
  have hbY : b ∈ Y := hCb (b_mem_cen b)
  have hcard : Nat.card (Cen b) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
    rcases K3 b hbY hB.hyp.ord with h | h
    · rw [inf_of_le_right hCb] at h
      exact absurd h (not_dvd_card_cen hB)
    · rwa [inf_of_le_right hCb] at h
  refine ⟨hcard, ?_⟩
  have hN : Subgroup.zpowers b ≤ Nor L :=
    Subgroup.zpowers_le.mpr (hB.hyp.hLN (b_mem_cen b))
  have e := card_sup_mul_card_inf _ _ hN
  rw [hB.hyp.zpowers_inf_L, Subgroup.card_bot, mul_one, Nat.card_zpowers, hB.hyp.ord,
    hB.card_L] at e
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr (b_mem_cen b))
    hB.hyp.hLC) ?_).symm
  rw [hcard, e]
  norm_num

theorem cenS_eq_of_cen_eq (hB : FF81Basis b L B b₁ b₂ b₃)
    (h : Cen b = Subgroup.zpowers b ⊔ L) : CenS B = B := by
  have hcomm := comm_of_isElemAb hB.mono.1
  have hBC : B ≤ CenS B := fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  refine le_antisymm (fun x hx => ?_) hBC
  have hbB := hB.mem.1
  have hxb : x ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hx b hbB).symm
  rw [h] at hxb
  have hN : Subgroup.zpowers b ≤ Nor L :=
    Subgroup.zpowers_le.mpr (hB.hyp.hLN (b_mem_cen b))
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN
  have hx' : x ∈ (Subgroup.zpowers b : Set G) * (L : Set G) := by
    rw [← hmul]
    exact hxb
  obtain ⟨h1, h1m, l, hl, rfl⟩ := hx'
  have hh1 : h1 ∈ B := (Subgroup.zpowers_le.mpr hbB) h1m
  have hh1C : h1 ∈ CenS B := hBC hh1
  have hlC : l ∈ CenS B := by
    have : l = h1⁻¹ * (h1 * l) := by group
    rw [this]
    exact (CenS B).mul_mem ((CenS B).inv_mem hh1C) hx
  obtain ⟨hb1, hb2, hb3⟩ := hB.mem.2
  have hlB₁ : l ∈ L ⊓ CenS (Subgroup.closure {b₁, b₂, b₃}) := by
    refine ⟨hl, Subgroup.centralizer_le ?_ hlC⟩
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hb1, hb2, hb3]
  rw [hB.selfcen] at hlB₁
  have hlB : l ∈ B := by
    refine (Subgroup.closure_le B).mpr ?_ hlB₁
    intro y hy
    rcases hy with rfl | rfl | rfl
    exacts [hb1, hb2, hb3]
  exact B.mul_mem hh1 hlB

theorem β'_mem (hB : FF81Basis b L B b₁ b₂ b₃) : β' b₂ b₃ ∈ B := by
  obtain ⟨-, -, hb2, hb3⟩ := hB.mem
  exact B.mul_mem hb2 (B.pow_mem hb3 2)

theorem orderOf_β' (hB : FF81Basis b L B b₁ b₂ b₃) : orderOf (β' b₂ b₃) = 3 := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h12, h13, h23⟩⟩ := triple_facts hB.elem
  have hE : IsElemAb 3 3 (Subgroup.closure ({b₂, b₃, b₁} : Set G)) :=
    (isElemAb_perm (isElemAb_perm hB.elem).2.2).2.2
  have hne := ne_of_basis hE
  have hb3inv : b₃ ^ 2 = b₃⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  refine orderOf_eq_prime ?_ ?_
  · show (b₂ * b₃ ^ 2) ^ 3 = 1
    rw [(Commute.mul_pow (show Commute b₂ (b₃ ^ 2) from (Commute.pow_right h23 2)) 3), h2,
      ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, h3, one_pow, one_mul]
  · intro h
    apply hne
    left
    show b₂ = b₃
    have : b₂ * b₃⁻¹ = 1 := by rw [← hb3inv]; exact h
    exact mul_inv_eq_one.mp this

theorem card_cen_β' (hB : FF81Basis b L B b₁ b₂ b₃) {M Y : Subgroup G}
    (hM : StatedClassicalModel M .PSp 3 2 1)
    (hMC : Subgroup.zpowers (β' b₂ b₃) ⊔ M = Cen (β' b₂ b₃))
    (hCY : Cen (β' b₂ b₃) ≤ Y) (K3 : K3Clause Y) :
    Nat.card (Cen (β' b₂ b₃)) = 2 ^ 9 * 3 ^ 5 * 5 * 7 := by
  set β := β' b₂ b₃ with hβ
  have hβY : β ∈ Y := hCY (b_mem_cen β)
  have hMβ : M ≤ Cen β := hMC ▸ le_sup_right
  have hN : Subgroup.zpowers β ≤ Nor M := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun m hm => ?_)
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMβ hm)
    rw [show β * m * β⁻¹ = m by rw [← this]; group]
    exact hm
  have e := card_sup_mul_card_inf _ _ hN
  rw [hMC, Nat.card_zpowers, orderOf_β' hB, card_sp6 hM] at e
  have hI : Nat.card ↥(Subgroup.zpowers β ⊓ M) ∣ 3 := by
    rw [← orderOf_β' hB, ← Nat.card_zpowers β]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hK := K3 β hβY (orderOf_β' hB)
  rw [inf_of_le_right hCY] at hK
  rcases (Nat.dvd_prime Nat.prime_three).mp hI with h1 | h3
  · rw [h1, mul_one] at e
    rw [e]
    norm_num
  · exfalso
    rw [h3] at e
    have e' : Nat.card (Cen β) = 1451520 := by omega
    rcases hK with h | h <;> rw [e'] at h <;> norm_num at h

theorem cen_le_of_card {Y : Subgroup G} (K3 : K3Clause Y) {x : G} (hxY : x ∈ Y)
    (hx3 : orderOf x = 3) (hc : Nat.card (Cen x) = 2 ^ 9 * 3 ^ 5 * 5 * 7) : Cen x ≤ Y := by
  rcases K3 x hxY hx3 with h | h
  · have := (Nat.dvd_trans h (Subgroup.card_dvd_of_le (inf_le_right : Y ⊓ Cen x ≤ Cen x)))
    rw [hc] at this
    norm_num at this
  · have : Y ⊓ Cen x = Cen x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hc])
    exact inf_eq_right.mp this

theorem card_cen_conj (g x : G) : Nat.card (Cen (g * x * g⁻¹)) = Nat.card (Cen x) := by
  rw [cen_conj, card_conjBy]

theorem card_cen_t₀ (hB : FF81Basis b L B b₁ b₂ b₃) {t₀ : G} (ht₀L : t₀ ∈ CenS L)
    (h58 : setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧ ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧
      IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧ T₀ ⊓ T₁ = ⊥)
    {Y : Subgroup G} (hCY : Cen t₀ ≤ Y) (hY : Nat.card Y = 3311126603366400) :
    Nat.card (Cen t₀) = 2 ^ 24 * 3 ^ 4 * 5 * 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, T₀, T₁, hT₀, hT₁, hTsup, hTinf⟩ := h58
  set T := Op 2 (Cen t₀) with hT
  have hLt : L ≤ Cen t₀ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp ht₀L x hx)
  have hTn : ∀ g ∈ Cen t₀, ∀ s ∈ T, g * s * g⁻¹ ∈ T := fun g hg s hs => op_two_conj hg hs
  have hTle : T ≤ Cen t₀ := op_two_le t₀
  have hTp : IsPGroup 2 T := op_two_isPGroup t₀
  have hTL : T ⊓ L = ⊥ := by
    haveI : IsSimpleGroup L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1
        hB.hyp.model
    haveI hn : ((T ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hTn g (hLt g.2) n hn.1, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((T ⊓ L).subgroupOf L) with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : L) ∈ (T ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hLT : L ≤ T := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (T ⊓ L).subgroupOf L := by rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      obtain ⟨n, hn⟩ := (hTp.to_le hLT).exists_card_eq
      rw [hB.card_L] at hn
      have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have hLN : L ≤ Nor T := fun l hl =>
    Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hTn l (hLt hl) s hs, fun hs => by
      have := hTn l⁻¹ ((Cen t₀).inv_mem (hLt hl)) _ hs
      rwa [show l⁻¹ * (l * s * l⁻¹) * l⁻¹⁻¹ = s by group] at this⟩
  have hCt : L ⊔ T = Cen t₀ := by
    refine le_antisymm (sup_le hLt hTle) fun x hx => ?_
    have hx' : x ∈ setMul T L := by rw [h1]; exact hx
    obtain ⟨s, hs, l, hl, rfl⟩ := hx'
    exact (L ⊔ T).mul_mem (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hl)
  have e := card_sup_mul_card_inf L T hLN
  rw [inf_comm, hTL, Subgroup.card_bot, mul_one, hCt, hB.card_L] at e
  obtain ⟨j, hj⟩ := hTp.exists_card_eq
  have hj15 : 15 ≤ j := by
    have h6 : Nat.card T₀ = 2 ^ 6 := hT₀.2
    have h9 : Nat.card T₁ = 2 ^ 9 := by rw [hT₁.2.1]
    have := card_mul_le_card_sup hTinf
    rw [h6, h9, hTsup, hj, ← pow_add] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hdvd : 2 ^ (j + 9) ∣ 2 ^ 24 * 197358525 := by
    have h := Subgroup.card_dvd_of_le hCY
    rw [e, hj, hY] at h
    have h' : 2 ^ (j + 9) ∣ 1451520 * 2 ^ j := ⟨2835, by rw [pow_add]; ring⟩
    exact h'.trans (by simpa [mul_comm] using h)
  have hj24 : j + 9 ≤ 24 := by
    have hcop : Nat.Coprime (2 ^ (j + 9)) 197358525 :=
      Nat.Coprime.pow_left _ (by norm_num)
    have := hcop.dvd_of_dvd_mul_right hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hj' : j = 15 := by omega
  rw [e, hj, hj']
  norm_num

end CFSG.RankThree.PartTwo.Sec21.FF81.S6

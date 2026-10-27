module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.GH74.KGroups.M11
public import Certificates.Certificate8037
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.Blueprint
open Item434Kit Item434Alt Item434Spor

namespace Item434SporM11

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M11 Equiv

theorem m11_cent3_check :
    ∀ x ∈ NativeSporadic.M11, x ^ 3 = 1 → x ≠ 1 →
      Nat.card ↥(NativeSporadic.M11 ⊓ Subgroup.centralizer ({x} : Set (Perm (Fin 11)))) = 18 :=
  Certificates.certificate8037

theorem card_inf_centralizer_eq
    {x : Perm (Fin 11)} (hx : x ∈ CFSG.GH74.KGroups.M11.Q.originalSubgroup) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    Nat.card (CFSG.GH74.KGroups.M11.Q.originalSubgroup ⊓
      Subgroup.centralizer ({x} : Set (Perm (Fin 11))) : Subgroup (Perm (Fin 11))) = 18 := by
  rw [Q_subgroup] at hx ⊢
  exact m11_cent3_check x hx hx3 hx1

theorem card_centralizer_eq
    {x : NativeSporadic.M11} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer ({x} : Set NativeSporadic.M11)) = 18 := by
  have hmap : (Subgroup.centralizer ({x} : Set NativeSporadic.M11)).map
      NativeSporadic.M11.subtype = CFSG.GH74.KGroups.M11.Q.originalSubgroup ⊓
        Subgroup.centralizer ({(x : Perm (Fin 11))} : Set (Perm (Fin 11))) := by
    rw [Q_subgroup]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx, rfl⟩
  rw [← Subgroup.card_map_of_injective NativeSporadic.M11.subtype_injective, hmap]
  refine card_inf_centralizer_eq (by rw [Q_subgroup]; exact x.2) ?_ ?_
  · rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  · intro h
    exact hx1 (Subtype.ext h)

theorem eq_of_mem_of_card_eq_two {Y : Type*} [Group Y] {W : Subgroup Y} (hW : Nat.card W = 2)
    {s t : Y} (hs : s ∈ W) (ht : t ∈ W) (hs1 : s ≠ 1) (ht1 : t ≠ 1) : s = t := by
  have : Finite W := Nat.finite_of_card_ne_zero (by omega)
  have hot : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := hW ▸ Subgroup.orderOf_dvd_natCard W ht
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h2
  have hWt : Subgroup.zpowers t = W :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ht)
      (by rw [hW, Nat.card_zpowers, hot])
  rw [← hWt] at hs
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  rw [← zpow_mod_orderOf, hot] at hs1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exact absurd (by rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]) hs1
  · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]

theorem eq_bot_of_le_normalizer
    {B Y : Subgroup NativeSporadic.M11} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hBY : B ≤ Subgroup.normalizer (Y : Set NativeSporadic.M11)) : Y = ⊥ := by
  have hX : NativeSporadic.IsSporadic NativeSporadic.M11 .M11 := ⟨MulEquiv.refl _⟩
  have hBe : ElemAb 3 B :=
    ⟨fun a ha b hb => congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩), hB.2⟩
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hB (by rw [hB9]; norm_num) hBY
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY3) ?_
  intro v hv hv1
  set W := Y ⊓ Subgroup.centralizer ({v} : Set NativeSporadic.M11) with hWdef
  have hW18 : Nat.card W ∣ 18 := by
    rw [← card_centralizer_eq (hB.2 v hv) hv1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hW3 : Nat.Coprime (Nat.card W) 9 := by
    have hcop : Nat.Coprime (Nat.card W) 3 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      exact fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact Nat.Coprime.pow_right 2 hcop
  have hW2 : Nat.card W ∣ 2 :=
    hW3.dvd_of_dvd_mul_right (by rw [show (2 : ℕ) * 9 = 18 by norm_num]; exact hW18)
  by_contra hne
  obtain ⟨t, htW, ht1⟩ : ∃ t ∈ W, t ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne fun x hx => (Subgroup.mem_bot).mpr (hall x hx)
  have hWc : Nat.card W = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hW2 with h1 | h2
    · exfalso
      have hW1 := Subgroup.card_eq_one.mp h1
      rw [hW1] at htW
      exact ht1 (Subgroup.mem_bot.mp htW)
    · exact h2
  have htB : ∀ c ∈ B, t * c = c * t := by
    intro c hc
    have hcv : c * v = v * c := congrArg Subtype.val (hB.1.is_comm.comm ⟨c, hc⟩ ⟨v, hv⟩)
    have htv : t * v = v * t := Subgroup.mem_centralizer_singleton_iff.mp htW.2
    have hctc : c * t * c⁻¹ ∈ W := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hBY hc) t).mp htW.1,
        Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hcv' : c⁻¹ * v = v * c⁻¹ := by
        calc c⁻¹ * v = c⁻¹ * (v * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * v) * c⁻¹ := by rw [hcv]
          _ = v * c⁻¹ := by group
      calc c * t * c⁻¹ * v = c * t * (v * c⁻¹) := by rw [mul_assoc (c * t), hcv']
        _ = c * (t * v) * c⁻¹ := by group
        _ = c * (v * t) * c⁻¹ := by rw [htv]
        _ = (c * v) * t * c⁻¹ := by group
        _ = (v * c) * t * c⁻¹ := by rw [hcv]
        _ = v * (c * t * c⁻¹) := by group
    have hne1 : c * t * c⁻¹ ≠ 1 := by
      intro h1
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have heq := eq_of_mem_of_card_eq_two hWc hctc htW hne1 ht1
    calc t * c = c * t * c⁻¹ * c := by rw [heq]
      _ = c * t := by group
  have htBmem : t ∈ B := centralizer3 hX B hBe hB9 t htB
  have ht3 : t ^ 3 = 1 := hB.2 t htBmem
  have ht2 : t ^ 2 = 1 := by
    have hdvd : orderOf t ∣ 2 := hWc ▸ Subgroup.orderOf_dvd_natCard W htW
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  apply ht1
  calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
    _ = 1 := by rw [ht3, ht2, inv_one, mul_one]

theorem eq_bot_of_le_normalizer_mulAut
    {R Y : Subgroup (MulAut NativeSporadic.M11)} (hR : CFSG.Assembly.IsElemAbelian 3 R)
    (hR9 : Nat.card R = 9) (hY3 : ¬ 3 ∣ Nat.card Y)
    (hRY : R ≤ Subgroup.normalizer (Y : Set (MulAut NativeSporadic.M11))) : Y = ⊥ := by
  have hX : NativeSporadic.IsSporadic NativeSporadic.M11 .M11 := ⟨MulEquiv.refl _⟩
  have : IsSimpleGroup NativeSporadic.M11 := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hcen : Subgroup.center NativeSporadic.M11 = ⊥ :=
    center_eq_bot_of_simple (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num)
  set ι := (MulAut.conj : NativeSporadic.M11 →* MulAut NativeSporadic.M11) with hι
  have hinj : Function.Injective ι := conj_injective_of_center_eq_bot hcen
  have hsurj : Function.Surjective ι := by
    have : Finite (MulAut NativeSporadic.M11) := finite_mulAut hX
    have hle : Nat.card (MulAut NativeSporadic.M11) ≤ Nat.card NativeSporadic.M11 := by
      rw [card_mulAut hX, CFSG.Sporadic.Mathieu.card_M11]
    exact (hinj.bijective_of_nat_card_le hle).2
  set B := R.comap ι with hBdef
  set Y₀ := Y.comap ι with hY₀def
  have hBmap : B.map ι = R := Subgroup.map_comap_eq_self_of_surjective hsurj R
  have hYmap : Y₀.map ι = Y := Subgroup.map_comap_eq_self_of_surjective hsurj Y
  have hB9 : Nat.card B = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hBmap, hR9]
  have hY₀ : Nat.card Y₀ = Nat.card Y := by
    rw [← Subgroup.card_map_of_injective hinj, hYmap]
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_map_injective hinj (hBmap ▸ hR)
  have hBY : B ≤ Subgroup.normalizer (Y₀ : Set NativeSporadic.M11) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [hY₀def, Subgroup.mem_comap, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp (hRY hb) (ι y)
  have hY₀bot := eq_bot_of_le_normalizer hBe hB9 (hY₀ ▸ hY3) hBY
  rw [← hYmap, hY₀bot, Subgroup.map_bot]

end Item434SporM11

namespace Item434Spor

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_m11
    (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* Spor .M11) : False := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : NativeSporadic.M11 ≃* Spor .M11 := b
  have e : layer G ⧸ Subgroup.center (layer G) ≃* NativeSporadic.M11 := e₀.trans b'.symm
  have hX : NativeSporadic.IsSporadic NativeSporadic.M11 .M11 := ⟨MulEquiv.refl _⟩
  have hRe := isElemAbelian_map_quotConj h e
  have hle : Nat.card (A.map (quotConj e)) ≤ 9 :=
    CFSG.GH74.KGroups.M11.autRank3_le_two hX _
      ⟨fun a ha b hb => congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩), hRe.2⟩
  have h9 : Nat.card (A.map (quotConj e)) = 9 := by
    rw [card_map_quotConj h e] at hle ⊢
    rcases h.card_layerStar with h9 | ⟨h27, -⟩
    · exact h9
    · omega
  exact false_of_normalizer h e fun Y hY3 hAY =>
    Item434SporM11.eq_bot_of_le_normalizer_mulAut hRe h9 hY3 hAY

end Item434Spor

section Families


theorem item434SporM11 :
    Item434SporAt .M11 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e₀⟩ := hL
  exact (Item434Spor.false_of_m11 hc e₀).elim

end Families

end CFSG.RankThree.PartTwo.Sec4

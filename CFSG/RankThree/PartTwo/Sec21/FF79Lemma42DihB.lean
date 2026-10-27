module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MStruct2

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem m42_center_trivial {N : Subgroup G} [IsSimpleGroup ↥N]
    (hn : ∃ a b : ↥N, a * b ≠ b * a) {d : G} (hd : d ∈ N) (hc : ∀ y ∈ N, y * d = d * y) :
    d = 1 := by
  have hz : (⟨d, hd⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g.1 g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  · obtain ⟨a, b, hab⟩ := hn
    have : a ∈ Subgroup.center ↥N := by rw [h]; exact Subgroup.mem_top _
    exact absurd (Subgroup.mem_center_iff.mp this b).symm hab

namespace M42Sit

variable [Finite G] {β e f : G} {H Λ Δ X : Subgroup G} (S : M42Sit β e f H Λ Δ X)
include S

theorem lay_cen_eq_one (hN : FF79LemmaN) (hQ : FF84.LemmaQ) {x : G} (hx : x ∈ Lay H)
    (hxΛ : ∀ y ∈ Λ, y * x = x * y) (hxΔ : ∀ y ∈ Δ, y * x = x * y) : x = 1 := by
  haveI : IsSimpleGroup ↥Λ := S.Λiso.simple
  haveI : IsSimpleGroup ↥Δ := S.Δiso.simple
  rw [S.Lay_eq hN hQ] at hx
  obtain ⟨d, hd, k, hk, rfl⟩ := m42_mem_sup_of_comm
    (fun a ha y hy => (S.comm_ΛΔ hN hQ y hy a ha).symm) hx
  have hd1 : d = 1 := by
    refine m42_center_trivial S.Δ_nonab hd fun y hy => ?_
    have h1 := hxΔ y hy
    have h2 := S.comm_ΛΔ hN hQ k hk y hy
    have : y * d * k = d * y * k := by
      calc y * d * k = y * (d * k) := by rw [mul_assoc]
        _ = d * k * y := h1
        _ = d * (k * y) := by rw [mul_assoc]
        _ = d * (y * k) := by rw [h2]
        _ = d * y * k := by rw [mul_assoc]
    exact mul_right_cancel this
  have hk1 : k = 1 := by
    refine m42_center_trivial S.Λ_nonab hk fun y hy => ?_
    have h1 := hxΛ y hy
    have h2 := S.comm_ΛΔ hN hQ y hy d hd
    have : d * (y * k) = d * (k * y) := by
      calc d * (y * k) = (d * y) * k := by rw [mul_assoc]
        _ = (y * d) * k := by rw [h2]
        _ = y * (d * k) := by rw [mul_assoc]
        _ = d * k * y := h1
        _ = d * (k * y) := by rw [mul_assoc]
    exact mul_left_cancel this
  rw [hd1, hk1, one_mul]

theorem three_cen_eq_one (hN : FF79LemmaN) (hQ : FF84.LemmaQ) {x : G} (hxH : x ∈ H)
    (hx3 : orderOf x = 3) (hxΛ : ∀ y ∈ Λ, y * x = x * y) (hxΔ : ∀ y ∈ Δ, y * x = x * y) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPH, -, hPidx⟩ := S.syl
  have hPcard := S.card_P
  have hPp : IsPGroup 3 (Subgroup.closure ({e, f} : Set G)) :=
    IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)
  have hxP : Subgroup.closure ({e, f} : Set G) ≤ Cen x := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact m42_mem_cen (hxΔ _ S.e_Δ).symm
    · exact m42_mem_cen (hxΛ _ S.f_Λ).symm
  have hc : ∀ y ∈ Subgroup.closure ({e, f} : Set G), x * y = y * x := fun y hy =>
    m42_cen_comm (hxP hy)
  have hPnor : Subgroup.zpowers x ≤ Nor (Subgroup.closure ({e, f} : Set G)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    constructor
    · intro hy
      rw [hc y hy, mul_inv_cancel_right]; exact hy
    · intro hy
      have h2 := hc _ hy
      have h3 : x * y * x⁻¹ = y := by
        have : x * (x * y * x⁻¹) = x * y := by
          calc x * (x * y * x⁻¹) = x * y * x⁻¹ * x := h2
            _ = x * y := by group
        exact mul_left_cancel this
      rwa [h3] at hy
  have hT : IsPGroup 3 (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) :=
    hxp.to_sup_of_normal_right' hPp hPnor
  have hTH : (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) ≤ H :=
    sup_le (Subgroup.zpowers_le.mpr hxH) hPH
  have hPT : Subgroup.closure ({e, f} : Set G) ≤
      (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) := le_sup_right
  have hTP : (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) =
      Subgroup.closure ({e, f} : Set G) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    have hdvd : Nat.card (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) ∣
        Nat.card H := Subgroup.card_dvd_of_le hTH
    have hHcard : (Subgroup.closure ({e, f} : Set G)).relIndex H * 9 = Nat.card H := by
      have := Subgroup.relIndex_mul_card (H := Subgroup.closure ({e, f} : Set G)) (K := H)
      rwa [inf_eq_left.mpr hPH, hPcard] at this
    have hcop : Nat.Coprime (3 ^ k) ((Subgroup.closure ({e, f} : Set G)).relIndex H) :=
      Nat.Coprime.pow_left k hPidx
    have h9 : 3 ^ k ∣ 9 := by
      rw [hk, ← hHcard, mul_comm] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    have hle : Nat.card (Subgroup.zpowers x ⊔ Subgroup.closure ({e, f} : Set G) : Subgroup G) ≤
        Nat.card (Subgroup.closure ({e, f} : Set G)) := by
      rw [hk, hPcard]; exact Nat.le_of_dvd (by norm_num) h9
    exact (Subgroup.eq_of_le_of_card_ge hPT hle).symm
  have hxP' : x ∈ Subgroup.closure ({e, f} : Set G) := by
    rw [← hTP]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxLay : x ∈ Lay H := by
    have : Subgroup.closure ({e, f} : Set G) ≤ Lay H := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact S.Δ_le_Lay hN hQ S.e_Δ
      · exact S.Λ_le_Lay hN hQ S.f_Λ
    exact this hxP'
  have := S.lay_cen_eq_one hN hQ hxLay hxΛ hxΔ
  rw [this, orderOf_one] at hx3
  omega

theorem two_cen_eq_one (hN : FF79LemmaN) (hQ : FF84.LemmaQ) {z : G} (hzH : z ∈ H) {k : ℕ}
    (hzk : orderOf z = 2 ^ k) (hzΛ : ∀ y ∈ Λ, y * z = z * y) (hzΔ : ∀ y ∈ Δ, y * z = z * y) :
    z = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Z : Subgroup G := H ⊓ CenS Λ ⊓ CenS Δ
  have hZH : Z ≤ H := fun x hx => hx.1.1
  have hZn : ∀ h ∈ H, ∀ n ∈ Z, h * n * h⁻¹ ∈ Z := by
    intro h hh n hn
    refine ⟨⟨H.mul_mem (H.mul_mem hh (hZH hn)) (H.inv_mem hh), ?_⟩, ?_⟩
    · refine m42_mem_cenS fun y hy => ?_
      have h1 := m42_cenS_comm hn.1.2 (S.Λ_normal hN hQ h⁻¹ (H.inv_mem hh) y hy)
      simp only [inv_inv] at h1
      calc y * (h * n * h⁻¹) = h * ((h⁻¹ * y * h) * n) * h⁻¹ := by group
        _ = h * (n * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
        _ = (h * n * h⁻¹) * y := by group
    · refine m42_mem_cenS fun y hy => ?_
      have h1 := m42_cenS_comm hn.2 (S.Δ_normal hN hQ h⁻¹ (H.inv_mem hh) y hy)
      simp only [inv_inv] at h1
      calc y * (h * n * h⁻¹) = h * ((h⁻¹ * y * h) * n) * h⁻¹ := by group
        _ = h * (n * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
        _ = (h * n * h⁻¹) * y := by group
  have hZ3 : ¬ 3 ∣ Nat.card Z := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 h3
    refine S.three_cen_eq_one hN hQ (hZH x.2) (by rw [Subgroup.orderOf_coe]; exact hx) ?_ ?_
    · intro y hy
      exact m42_cenS_comm x.2.1.2 hy
    · intro y hy
      exact m42_cenS_comm x.2.2 hy
  have hZX : Z ≤ X := by
    rw [← S.Opp_eq hN hQ]
    exact m42_le_Opp hZH hZn ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3)
  have hzZ : z ∈ Z := ⟨⟨hzH, m42_mem_cenS fun y hy => hzΛ y hy⟩, m42_mem_cenS fun y hy => hzΔ y hy⟩
  have hd : orderOf z ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X (hZX hzZ)
  rw [hzk] at hd
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hne
    have := h2.trans hd
    exact (Nat.not_even_iff_odd.mpr S.Xodd) (even_iff_two_dvd.mpr this)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hzk
  exact hzk

end M42Sit

end CFSG.RankThree.PartTwo.Sec21.FF79

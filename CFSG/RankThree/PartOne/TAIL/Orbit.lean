module

public import CFSG.RankThree.PartOne.TAIL.Trv
public import CFSG.RankThree.PartOne.TAIL.ConjOrbit

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

theorem exists_inv_mod_seven {i : ℤ} (hi : ¬ (7 : ℤ) ∣ i) : ∃ t u : ℤ, i * t = 1 + 7 * u := by
  have h : i % 7 = 1 ∨ i % 7 = 2 ∨ i % 7 = 3 ∨ i % 7 = 4 ∨ i % 7 = 5 ∨ i % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h
  · exact ⟨1, (i * 1 - 1) / 7, by omega⟩
  · exact ⟨4, (i * 4 - 1) / 7, by omega⟩
  · exact ⟨5, (i * 5 - 1) / 7, by omega⟩
  · exact ⟨2, (i * 2 - 1) / 7, by omega⟩
  · exact ⟨3, (i * 3 - 1) / 7, by omega⟩
  · exact ⟨6, (i * 6 - 1) / 7, by omega⟩

variable {G : Type} [Group G]

theorem conjSub_zpowers (n c : G) :
    conjSub n (Subgroup.zpowers c) = Subgroup.zpowers (n * c * n⁻¹) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow, hk]
    group
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, conj_zpow]
    group

theorem zpowers_conj_eq {z z' : G} (g : G) (h : Subgroup.zpowers z = Subgroup.zpowers z') :
    Subgroup.zpowers (g * z * g⁻¹) = Subgroup.zpowers (g * z' * g⁻¹) := by
  have := congrArg (conjSub g) h
  rwa [conjSub_zpowers, conjSub_zpowers] at this

@[expose] def cOrb (A : Subgroup G) (c : G) : Set (Subgroup G) :=
  {Z | ∃ n ∈ Subgroup.normalizer (A : Set G), Z = Subgroup.zpowers (n * c * n⁻¹)}

theorem mem_cOrb {A : Subgroup G} {c : G} {Z : Subgroup G} :
    Z ∈ cOrb A c ↔ ∃ n ∈ Subgroup.normalizer (A : Set G), Z = Subgroup.zpowers (n * c * n⁻¹) :=
  Iff.rfl

theorem cOrb_eq (A : Subgroup G) (c : G) :
    cOrb A c = {Z | ∃ n ∈ Subgroup.normalizer (A : Set G), Z = conjSub n (Subgroup.zpowers c)} := by
  ext Z
  constructor
  · rintro ⟨n, hn, hZ⟩
    exact ⟨n, hn, by rw [hZ, conjSub_zpowers]⟩
  · rintro ⟨n, hn, hZ⟩
    exact ⟨n, hn, by rw [hZ, conjSub_zpowers]⟩

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h

theorem B_pow {x : G} (hx : x ∈ B) : x ^ 7 = 1 := h.A_pow (h.B_le hx)

theorem c_pow : c ^ 7 = 1 := h.A_pow h.c_mem

theorem dvd_of_c_zpow_mem {i : ℤ} (hi : c ^ i ∈ B) : (7 : ℤ) ∣ i := by
  by_contra hn
  obtain ⟨t, u, htu⟩ := exists_inv_mod_seven hn
  have hc : c = (c ^ i) ^ t := by
    rw [← zpow_mul, htu, zpow_add, zpow_one, zpow_mul]
    have : c ^ (7 : ℤ) = 1 := by exact_mod_cast h.c_pow
    rw [this, one_zpow, mul_one]
  exact h.c_notMem (hc ▸ B.zpow_mem hi t)

theorem zpowers_eq_c_mul {z : G} (hzA : z ∈ A) (hzB : z ∉ B) :
    ∃ β ∈ B, Subgroup.zpowers z = Subgroup.zpowers (c * β) := by
  obtain ⟨i, β, hβ, hz⟩ := h.mem_A_iff.mp hzA
  have hc7 : c ^ (7 : ℤ) = 1 := by exact_mod_cast h.c_pow
  have hz7 : z ^ (7 : ℤ) = 1 := by exact_mod_cast h.A_pow hzA
  have hi : ¬ (7 : ℤ) ∣ i := by
    rintro ⟨k, hk⟩
    apply hzB
    have : c ^ i = 1 := by
      rw [hk, zpow_mul, hc7, one_zpow]
    rw [hz, this, one_mul]
    exact hβ
  obtain ⟨t, u, htu⟩ := exists_inv_mod_seven hi
  have hcomm : Commute (c ^ i) β := Commute.zpow_left (show Commute c β from h.c_comm_B hβ) i
  have hzt : z ^ t = c * β ^ t := by
    rw [hz, hcomm.mul_zpow, ← zpow_mul, htu, zpow_add, zpow_one, zpow_mul, hc7, one_zpow, mul_one]
  have hzz : z = (z ^ t) ^ i := by
    rw [← zpow_mul, mul_comm t i, htu, zpow_add, zpow_one, zpow_mul, hz7, one_zpow, mul_one]
  refine ⟨β ^ t, B.zpow_mem hβ t, ?_⟩
  rw [← hzt]
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, hzz.symm⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) t

theorem eq_of_zpowers_eq {β₁ β₂ : G} (h₁ : β₁ ∈ B) (h₂ : β₂ ∈ B)
    (he : Subgroup.zpowers (c * β₁) = Subgroup.zpowers (c * β₂)) : β₁ = β₂ := by
  have hm : c * β₂ ∈ Subgroup.zpowers (c * β₁) := by
    rw [he]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  have hcomm : Commute c β₁ := h.c_comm_B h₁
  have hk' : c ^ k * β₁ ^ k = c * β₂ := by rw [← hcomm.mul_zpow]; exact hk
  have e2 : c ^ k = c * c ^ (k - 1) := by rw [← zpow_one_add]; congr 1; ring
  have e3 : c ^ (k - 1) * β₁ ^ k = β₂ := by
    have : c * (c ^ (k - 1) * β₁ ^ k) = c * β₂ := by rw [← hk', e2, mul_assoc]
    exact mul_left_cancel this
  have hB : c ^ (k - 1) ∈ B := by
    have : c ^ (k - 1) = β₂ * (β₁ ^ k)⁻¹ := eq_mul_inv_of_mul_eq e3
    rw [this]
    exact B.mul_mem h₂ (B.inv_mem (B.zpow_mem h₁ k))
  obtain ⟨s, hs⟩ := h.dvd_of_c_zpow_mem hB
  have hk1 : k = 1 + 7 * s := by omega
  have hc1 : c ^ (k - 1) = 1 := by
    rw [hs, zpow_mul]
    have : c ^ (7 : ℤ) = 1 := by exact_mod_cast h.c_pow
    rw [this, one_zpow]
  rw [hc1, one_mul] at e3
  rw [← e3, hk1, zpow_add, zpow_one, zpow_mul]
  have : β₁ ^ (7 : ℤ) = 1 := by exact_mod_cast h.B_pow h₁
  rw [this, one_zpow, mul_one]

theorem zpowers_cb_mem_cOrb {β : G} (hβ : β ∈ B) : Subgroup.zpowers (c * β) ∈ cOrb A c := by
  obtain ⟨x, hx⟩ := h.epsHom_surjective ⟨β, hβ⟩
  have hx' : eps c (x : G) = β := by
    have := congrArg Subtype.val hx
    rwa [SchemeHyp.epsHom_apply] at this
  refine ⟨(x : G), Xs_le_normalizer x.2, ?_⟩
  have e : (x : G) * c * (x : G)⁻¹ = c * β := by
    calc (x : G) * c * (x : G)⁻¹ = ((x : G) * c * (x : G)⁻¹ * c⁻¹) * c := by group
      _ = β * c := by rw [show (x : G) * c * (x : G)⁻¹ * c⁻¹ = eps c (x : G) from rfl, hx']
      _ = c * β := (h.c_comm_B hβ).symm
  rw [e]

theorem cOrb_sdiff_eq :
    cOrb A c \ {Z | Z ≤ B} = (fun β : G => Subgroup.zpowers (c * β)) '' (B : Set G) := by
  ext Z
  constructor
  · intro hZ
    obtain ⟨hZ1, hZ2⟩ := hZ
    obtain ⟨n, hn, rfl⟩ := mem_cOrb.mp hZ1
    have hzA : n * c * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn c).mp h.c_mem
    have hzB : n * c * n⁻¹ ∉ B := fun hzB => hZ2 ((Subgroup.zpowers_le).mpr hzB)
    obtain ⟨β, hβ, he⟩ := h.zpowers_eq_c_mul hzA hzB
    exact ⟨β, hβ, he.symm⟩
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨h.zpowers_cb_mem_cOrb hβ, ?_⟩
    intro hle
    have h1 : c * β ∈ B := hle (Subgroup.mem_zpowers _)
    apply h.c_notMem
    have := B.mul_mem h1 (B.inv_mem hβ)
    simpa using this

theorem ncard_cOrb_sdiff : (cOrb A c \ {Z | Z ≤ B}).ncard = 49 := by
  rw [h.cOrb_sdiff_eq]
  have hinj : Set.InjOn (fun β : G => Subgroup.zpowers (c * β)) (B : Set G) :=
    fun β₁ h₁ β₂ h₂ he => h.eq_of_zpowers_eq h₁ h₂ he
  rw [hinj.ncard_image, ← Nat.card_coe_set_eq]
  have := h.B_card
  norm_num at this
  exact this

theorem ncard_cOrb_inter_le : (cOrb A c ∩ {Z | Z ≤ B}).ncard ≤ 48 := by
  have hsub : cOrb A c ∩ {Z | Z ≤ B} ⊆
      (fun z : G => Subgroup.zpowers z) '' ((B : Set G) \ {1}) := by
    intro Z hZ
    obtain ⟨hZ1, hZ2⟩ := hZ
    obtain ⟨n, hn, rfl⟩ := mem_cOrb.mp hZ1
    have hzB : n * c * n⁻¹ ∈ B := hZ2 (Subgroup.mem_zpowers _)
    have hz1 : n * c * n⁻¹ ≠ 1 := by
      intro h1
      apply h.c_ne_one
      calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    exact ⟨n * c * n⁻¹, ⟨hzB, hz1⟩, rfl⟩
  have : Finite (Subgroup G) := finite_subgroups
  have hB : (B : Set G).ncard = 49 := by
    rw [← Nat.card_coe_set_eq]
    have := h.B_card
    norm_num at this
    exact this
  calc (cOrb A c ∩ {Z | Z ≤ B}).ncard
      ≤ ((fun z : G => Subgroup.zpowers z) '' ((B : Set G) \ {1})).ncard := Set.ncard_le_ncard hsub
    _ ≤ ((B : Set G) \ {1}).ncard := Set.ncard_image_le
    _ = (B : Set G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem B.one_mem
    _ = 48 := by rw [hB]

theorem seven_pow_five_dvd_card_normalizer :
    7 ^ 5 ∣ Nat.card (Subgroup.normalizer (A : Set G)) := by
  have h1 : Nat.card (Xs A B) ∣ Nat.card (Subgroup.normalizer (A : Set G)) :=
    Subgroup.card_dvd_of_le Xs_le_normalizer
  have hle : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact h.A_comm hy hx
  have h2 : 7 ^ 3 ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [h.A_card] at this
  rw [h.card_Xs] at h1
  have h3 : 7 ^ 3 * 7 ^ 2 ∣ Nat.card (Subgroup.centralizer (A : Set G)) * 7 ^ 2 :=
    mul_dvd_mul_right h2 _
  have h4 : (7 : ℕ) ^ 5 = 7 ^ 3 * 7 ^ 2 := by norm_num
  rw [h4]
  exact h3.trans h1

theorem card_Hc : ∃ m : ℕ, ¬ 7 ∣ m ∧
    Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) =
      m * 7 ^ 3 := by
  obtain ⟨hAle, hAidx⟩ := h.A_sylow_NH
  refine ⟨A.relIndex (Subgroup.normalizer (A : Set G) ⊓
    Subgroup.normalizer (Subgroup.zpowers c : Set G)), hAidx, ?_⟩
  have := Subgroup.relIndex_mul_card A (Subgroup.normalizer (A : Set G) ⊓
    Subgroup.normalizer (Subgroup.zpowers c : Set G))
  rw [inf_eq_left.mpr hAle, h.A_card] at this
  exact this.symm

theorem seven_sq_dvd_ncard : 49 ∣ (cOrb A c).ncard := by
  obtain ⟨m, hm, hHc⟩ := h.card_Hc
  have h1 := card_mul_ncard_conj (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)
  rw [← cOrb_eq] at h1
  rw [hHc] at h1
  have h2 := h.seven_pow_five_dvd_card_normalizer
  rw [← h1] at h2
  have h3 : 7 ^ 2 * 7 ^ 3 ∣ ((cOrb A c).ncard * m) * 7 ^ 3 := by
    have e : (cOrb A c).ncard * (m * 7 ^ 3) = ((cOrb A c).ncard * m) * 7 ^ 3 := by ring
    rw [e] at h2
    have e2 : (7 : ℕ) ^ 5 = 7 ^ 2 * 7 ^ 3 := by norm_num
    rwa [e2] at h2
  have h4 : 7 ^ 2 ∣ (cOrb A c).ncard * m := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3
  have hcop : Nat.Coprime (7 ^ 2) m :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hm)
  have h5 : 7 ^ 2 ∣ (cOrb A c).ncard := hcop.dvd_of_dvd_mul_right h4
  simpa using h5

theorem cOrb_card_and_inter :
    (cOrb A c).ncard = 49 ∧ cOrb A c ∩ {Z | Z ≤ B} = ∅ := by
  have : Finite (Subgroup G) := finite_subgroups
  have h1 := Set.ncard_inter_add_ncard_sdiff_eq_ncard (cOrb A c) {Z | Z ≤ B}
  have h2 := h.ncard_cOrb_sdiff
  have h3 := h.ncard_cOrb_inter_le
  have h4 := h.seven_sq_dvd_ncard
  have h5 : (cOrb A c ∩ {Z | Z ≤ B}).ncard = 0 := by omega
  refine ⟨by omega, ?_⟩
  exact (Set.ncard_eq_zero (Set.toFinite _)).mp h5

theorem normalizer_A_le_normalizer_B :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem B fun β hβ => ?_
  by_contra hcon
  have hzA : n * β * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hn β).mp (h.B_le hβ)
  obtain ⟨β', hβ', he⟩ := h.zpowers_eq_c_mul hzA hcon
  obtain ⟨n', hn', he'⟩ := mem_cOrb.mp (h.zpowers_cb_mem_cOrb hβ')
  have h1 : Subgroup.zpowers (n * β * n⁻¹) = Subgroup.zpowers (n' * c * n'⁻¹) := he.trans he'
  have h2 := zpowers_conj_eq n⁻¹ h1
  have e1 : n⁻¹ * (n * β * n⁻¹) * n⁻¹⁻¹ = β := by group
  have e2 : n⁻¹ * (n' * c * n'⁻¹) * n⁻¹⁻¹ = (n⁻¹ * n') * c * (n⁻¹ * n')⁻¹ := by group
  rw [e1, e2] at h2
  have h3 : Subgroup.zpowers β ∈ cOrb A c :=
    ⟨n⁻¹ * n', Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hn', h2⟩
  have h4 : Subgroup.zpowers β ∈ cOrb A c ∩ {Z | Z ≤ B} :=
    ⟨h3, (Subgroup.zpowers_le).mpr hβ⟩
  rw [h.cOrb_card_and_inter.2] at h4
  exact h4

theorem card_normalizer_A : ∃ m : ℕ, ¬ 7 ∣ m ∧
    Nat.card (Subgroup.normalizer (A : Set G)) = 7 ^ 5 * m := by
  obtain ⟨m, hm, hHc⟩ := h.card_Hc
  refine ⟨m, hm, ?_⟩
  have h1 := card_mul_ncard_conj (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c)
  rw [← cOrb_eq, h.cOrb_card_and_inter.1, hHc] at h1
  rw [← h1]
  ring

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL

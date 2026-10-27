module

public import CFSG.RankThree.PartOne.TAIL.Xs

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] (H : Subgroup G) {g : G}
    (hg : ∀ a ∈ H, g * a * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  let f : H → H := fun a => ⟨g * a * g⁻¹, hg a a.2⟩
  have hinj : Function.Injective f := fun a a' haa' => by
    apply Subtype.ext
    have := congrArg Subtype.val haa'
    simpa [f] using this
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => hg a ha, fun ha => ?_⟩
  obtain ⟨a', ha'⟩ := hsurj ⟨g * a * g⁻¹, ha⟩
  have h2 : g * (a' : G) * g⁻¹ = g * a * g⁻¹ := congrArg Subtype.val ha'
  have h3 : (a' : G) = a := by simpa using h2
  exact h3 ▸ a'.2

theorem eps_conj_of_comm {c g y : G} (hgc : c * g = g * c) :
    eps c (g * y * g⁻¹) = g * eps c y * g⁻¹ := by
  unfold eps
  have e : g * c * g⁻¹ = c := by
    calc g * c * g⁻¹ = (c * g) * g⁻¹ := by rw [hgc]
      _ = c := by group
  calc g * y * g⁻¹ * c * (g * y * g⁻¹)⁻¹ * c⁻¹
      = g * y * g⁻¹ * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * c * g⁻¹)⁻¹ := by rw [e]
    _ = g * (y * c * y⁻¹ * c⁻¹) * g⁻¹ := by group

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h

theorem mem_Xs_of_moves {x : G} (hxB : ∀ β ∈ B, x * β * x⁻¹ = β)
    (hxc : x * c * x⁻¹ * c⁻¹ ∈ B) : x ∈ Xs A B := by
  have key : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B := by
    intro a ha
    obtain ⟨i, β, hβ, rfl⟩ := h.mem_A_iff.mp ha
    set u := x * c * x⁻¹ * c⁻¹ with hu
    have hxc' : x * c * x⁻¹ = u * c := by rw [hu]; group
    have hcu : Commute u c := (h.c_comm_B hxc).symm
    have e1 : x * (c ^ i * β) * x⁻¹ = u ^ i * c ^ i * β := by
      calc x * (c ^ i * β) * x⁻¹ = (x * c ^ i * x⁻¹) * (x * β * x⁻¹) := by group
        _ = (x * c * x⁻¹) ^ i * β := by rw [conj_zpow, hxB β hβ]
        _ = u ^ i * c ^ i * β := by rw [hxc', hcu.mul_zpow]
    rw [e1]
    have : u ^ i * c ^ i * β * (c ^ i * β)⁻¹ = u ^ i := by group
    rw [this]
    exact B.zpow_mem hxc i
  refine ⟨?_, hxB, key⟩
  refine mem_normalizer_of_conj_mem A fun a ha => ?_
  have := B.mul_mem (key a ha) (B.one_mem)
  have e : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
  rw [e]
  exact A.mul_mem (h.B_le (key a ha)) ha

theorem eps_eq_one_iff {x : G} (hx : x ∈ Xs A B) : eps c x = 1 ↔ x ∈ Subgroup.centralizer (A : Set G) := by
  constructor
  · intro h1
    have hxc : x * c = c * x := by
      have : x * c * x⁻¹ * c⁻¹ = 1 := h1
      calc x * c = (x * c * x⁻¹ * c⁻¹) * (c * x) := by group
        _ = c * x := by rw [this, one_mul]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨i, β, hβ, rfl⟩ := h.mem_A_iff.mp ha
    have hxcz : x * c ^ i = c ^ i * x := (Commute.zpow_right (show Commute x c from hxc) i).eq
    have hxβ : x * β = β * x := by
      have := hx.2.1 β hβ
      calc x * β = (x * β * x⁻¹) * x := by group
        _ = β * x := by rw [this]
    calc c ^ i * β * x = c ^ i * (β * x) := by group
      _ = c ^ i * (x * β) := by rw [hxβ]
      _ = (c ^ i * x) * β := by group
      _ = (x * c ^ i) * β := by rw [hxcz]
      _ = x * (c ^ i * β) := by group
  · intro hxc
    have := Subgroup.mem_centralizer_iff.mp hxc c h.c_mem
    show x * c * x⁻¹ * c⁻¹ = 1
    calc x * c * x⁻¹ * c⁻¹ = (c * x) * x⁻¹ * c⁻¹ := by rw [this]
      _ = 1 := by group

theorem ker_epsHom : (h.epsHom).ker = (Subgroup.centralizer (A : Set G)).subgroupOf (Xs A B) := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [← h.eps_eq_one_iff x.2]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    simpa [SchemeHyp.epsHom_apply] using this
  · intro h1
    exact Subtype.ext (by simpa [SchemeHyp.epsHom_apply] using h1)

theorem mem_normalizer_A_of_comm {g : G} (hgc : c * g = g * c)
    (hgN : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer (A : Set G) := by
  refine mem_normalizer_of_conj_mem A fun a ha => ?_
  obtain ⟨i, β, hβ, rfl⟩ := h.mem_A_iff.mp ha
  have hgβ : g * β * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgN β).mp hβ
  have e : g * c * g⁻¹ = c := by
    calc g * c * g⁻¹ = (c * g) * g⁻¹ := by rw [hgc]
      _ = c := by group
  have e2 : g * (c ^ i * β) * g⁻¹ = c ^ i * (g * β * g⁻¹) := by
    calc g * (c ^ i * β) * g⁻¹ = (g * c * g⁻¹) ^ i * (g * β * g⁻¹) := by
          rw [conj_zpow]; group
      _ = c ^ i * (g * β * g⁻¹) := by rw [e]
  rw [e2]
  exact A.mul_mem (A.zpow_mem h.c_mem i) (h.B_le hgβ)

theorem epsHom_surjective : Function.Surjective h.epsHom := by
  obtain ⟨β₀, hβ₀B, hβ₀1, hy⟩ := h.y₀_c
  have hy' : eps c y₀ = β₀ := by
    unfold eps
    calc y₀ * c * y₀⁻¹ * c⁻¹ = (c * β₀) * c⁻¹ := by rw [hy]
      _ = β₀ := by rw [h.c_comm_B hβ₀B]; group
  have hy₀X : y₀ ∈ Xs A B := h.mem_Xs_of_moves h.y₀_cB (by
    show eps c y₀ ∈ B
    rw [hy']; exact hβ₀B)
  let R : Subgroup ↥B := (h.epsHom).range
  let β₀' : ↥B := ⟨β₀, hβ₀B⟩
  have hβ₀R : β₀' ∈ R := ⟨⟨y₀, hy₀X⟩, Subtype.ext (by simpa [SchemeHyp.epsHom_apply] using hy')⟩
  obtain ⟨g, hgM, hg⟩ := h.irr β₀ hβ₀B hβ₀1
  have hgc : c * g = g * c := (Subgroup.mem_centralizer_singleton_iff.mp (h.M₀_cent hgM)).symm
  have hgN : g ∈ Subgroup.normalizer (B : Set G) := h.M₀_nrm hgM
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := h.mem_normalizer_A_of_comm hgc hgN
  have hgβ : g * β₀ * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgN β₀).mp hβ₀B
  have hgy : g * y₀ * g⁻¹ ∈ Xs A B := conj_mem_Xs hgA hgN hy₀X
  have hgβR : (⟨g * β₀ * g⁻¹, hgβ⟩ : ↥B) ∈ R :=
    ⟨⟨g * y₀ * g⁻¹, hgy⟩, Subtype.ext (by
      simp only [SchemeHyp.epsHom_apply]
      rw [eps_conj_of_comm hgc, hy'])⟩
  have h7 : Nat.card B = 7 ^ 2 := h.B_card
  have hfact : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hord : orderOf β₀' = 7 := by
    have hpow : β₀' ^ 7 = 1 := Subtype.ext (h.A_pow (h.B_le hβ₀B))
    exact orderOf_eq_prime hpow (fun h1 => hβ₀1 (congrArg Subtype.val h1))
  have hz : Nat.card (Subgroup.zpowers β₀') = 7 := by rw [Nat.card_zpowers, hord]
  have hle : Subgroup.zpowers β₀' ≤ R := (Subgroup.zpowers_le).mpr hβ₀R
  have h7R : 7 ∣ Nat.card R := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hz] at this
  have hdvd : Nat.card R ∣ 7 ^ 2 := by
    have := Subgroup.card_subgroup_dvd_card R
    rwa [h7] at this
  have hR : R = ⊤ := by
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hdvd with ⟨k, hk, hk'⟩
    interval_cases k
    · exfalso
      rw [hk'] at h7R
      exact absurd h7R (by decide)
    · exfalso
      have heq : Subgroup.zpowers β₀' = R :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hz, hk']; simp)
      apply hg
      have hmem : (⟨g * β₀ * g⁻¹, hgβ⟩ : ↥B) ∈ Subgroup.zpowers β₀' := by
        rw [heq]; exact hgβR
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by simpa [β₀'] using congrArg Subtype.val hj⟩
    · exact Subgroup.eq_top_of_card_eq R (by rw [hk', h7])
  exact MonoidHom.range_eq_top.mp hR

theorem card_Xs : Nat.card (Xs A B) = Nat.card (Subgroup.centralizer (A : Set G)) * 7 ^ 2 := by
  have h1 := Subgroup.card_ker_mul_card_range h.epsHom
  have hr : (h.epsHom).range = ⊤ := MonoidHom.range_eq_top.mpr h.epsHom_surjective
  rw [hr, Subgroup.card_top, h.ker_epsHom] at h1
  have h2 : Nat.card ((Subgroup.centralizer (A : Set G)).subgroupOf (Xs A B)) =
      Nat.card (Subgroup.centralizer (A : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (centralizer_le_Xs h.B_le)).toEquiv
  rw [h2, h.B_card] at h1
  exact h1.symm

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL

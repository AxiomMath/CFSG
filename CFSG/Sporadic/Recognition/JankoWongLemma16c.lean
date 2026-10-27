module

public import CFSG.Sporadic.Recognition.JankoWongLemma16b
public import CFSG.Sporadic.Recognition.JankoWongCyclicBurnside
public import CFSG.Sporadic.Recognition.JankoWongFourOnNine
public import CFSG.Sporadic.Recognition.JankoWongTwoAbelian
public import CFSG.Sporadic.Recognition.JankoWongSylowByNormalizer

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} {c : Ctx S}

theorem IsW.Ca_facts
    {W : Subgroup G} (hW : c.IsW W) :
    (∃ g : G, g ∈ c.NG ∧ g * (c.a : G) = (c.a : G) * g ∧ orderOf g = 4) ∧
    (∀ k : G, k ∈ c.NG → k * (c.a : G) = (c.a : G) * k → ∀ w : G, w ∈ W → k * w * k⁻¹ ∈ W) ∧
    (∀ R : Subgroup G, R ≤ c.NG ⊓ centralizer ({(c.a : G)} : Set G) → IsPGroup 3 R → R ≤ W) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K : Subgroup G := c.NG ⊓ centralizer ({(c.a : G)} : Set G) with hKdef
  have hK : Nat.card K = 2916 := c.card_NG_inf_centralizer_a
  have hno : ∀ u v : ↥K, u ≠ 1 → v ≠ 1 → u ≠ v → u * v = v * u → u ^ 2 = 1 → v ^ 2 = 1 →
      False := by
    intro u v hu1 hv1 huv hc hu2 hv2
    refine c.false_of_klein_four_centralizing_a (u := (u : G)) (v := (v : G))
      (by simpa using congrArg Subtype.val hu2) (by simpa using congrArg Subtype.val hv2)
      (fun e => hu1 (Subtype.ext e)) (fun e => hv1 (Subtype.ext e))
      (fun e => huv (Subtype.ext e)) (congrArg Subtype.val hc)
      (Subgroup.mem_centralizer_singleton_iff.mp u.2.2)
      (Subgroup.mem_centralizer_singleton_iff.mp v.2.2)
  obtain ⟨⟨g, hg4⟩, X, hXn, hXcard, hXmax⟩ := exists_orderOf_four_and_normal_sylow_three hK hno
  have hWK : W ≤ K := fun w hw => ⟨hW.le_NG hw,
    Subgroup.mem_centralizer_singleton_iff.mpr (hW.comm_a w hw)⟩
  have hWp : IsPGroup 3 (W.subgroupOf K) :=
    hW.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hWK).symm
  have hWX : W.subgroupOf K ≤ X := hXmax _ hWp
  have hWcard : Nat.card (W.subgroupOf K) = 3 ^ 6 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv, hW.card]
  have hXeq : W.subgroupOf K = X :=
    Subgroup.eq_of_le_of_card_ge hWX (by rw [hXcard, hWcard])
  have hnorm : ∀ k : ↥K, ∀ w : G, w ∈ W → (k : G) * w * (k : G)⁻¹ ∈ W := by
    intro k w hw
    have h1 : (⟨w, hWK hw⟩ : ↥K) ∈ X := by rw [← hXeq]; exact hw
    have h2 := hXn.conj_mem _ h1 k
    rw [← hXeq] at h2
    exact h2
  refine ⟨⟨(g : G), g.2.1, Subgroup.mem_centralizer_singleton_iff.mp g.2.2, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hg4
  · intro k hk hka w hw
    exact hnorm ⟨k, hk, Subgroup.mem_centralizer_singleton_iff.mpr hka⟩ w hw
  · intro R hRK hRp
    have hRp' : IsPGroup 3 (R.subgroupOf K) :=
      hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
    have h1 : R.subgroupOf K ≤ W.subgroupOf K := hXeq ▸ hXmax _ hRp'
    intro r hr
    have hrK : r ∈ K := hRK hr
    have h2 : (⟨r, hrK⟩ : ↥K) ∈ R.subgroupOf K := Subgroup.mem_subgroupOf.mpr hr
    exact Subgroup.mem_subgroupOf.mp (h1 h2)

theorem IsW.exists_cyclic_four
    {W : Subgroup G} (hW : c.IsW W) :
    ∃ g : G, g ∈ c.NG ∧ g * (c.a : G) = (c.a : G) * g ∧ orderOf g = 4 ∧
      ∀ w : G, w ∈ W ↔ g * w * g⁻¹ ∈ W := by
  obtain ⟨⟨g, hgNG, hga, hg4⟩, hnorm, -⟩ := hW.Ca_facts
  refine ⟨g, hgNG, hga, hg4, fun w => ⟨fun hw => hnorm g hgNG hga w hw, fun hw => ?_⟩⟩
  have hgi : g⁻¹ ∈ c.NG := c.NG.inv_mem hgNG
  have hgia : g⁻¹ * (c.a : G) = (c.a : G) * g⁻¹ := by
    calc g⁻¹ * (c.a : G) = g⁻¹ * ((c.a : G) * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * (c.a : G)) * g⁻¹ := by rw [hga]
      _ = (c.a : G) * g⁻¹ := by group
  have h := hnorm g⁻¹ hgi hgia _ hw
  have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
  rwa [e] at h

omit [Finite G] in
theorem centerW_abelian (W : Subgroup G) :
    ∀ x ∈ centerW W, ∀ y ∈ centerW W, x * y = y * x := fun _ hx _ hy =>
  ((mem_centerW.mp hx).2 _ (mem_centerW.mp hy).1).symm

theorem IsW.zpowers_a_le_centerW
    {W : Subgroup G} (hW : c.IsW W) : zpowers (c.a : G) ≤ centerW W :=
  Subgroup.zpowers_le.mpr hW.aG_mem_centerW

theorem orderOf_aG : orderOf (c.a : G) = 3 := orderOf_eq_prime c.aG_cube c.aG_ne_one

theorem IsW.card_centerW_eq_three
    {W : Subgroup G} (hW : c.IsW W) : Nat.card (centerW W) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card (centerW W) := by
    have := Subgroup.card_dvd_of_le hW.zpowers_a_le_centerW
    rwa [Nat.card_zpowers, orderOf_aG] at this
  have hle := hW.card_centerW_le_nine
  have hdvd : Nat.card (centerW W) ∣ 3 ^ 6 := by
    rw [← hW.card]; exact Subgroup.card_dvd_of_le inf_le_left
  by_contra hne
  have h9 : Nat.card (centerW W) = 9 := by
    obtain ⟨j, hj, hj3⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hj3] at h3 hle hne ⊢
    interval_cases j <;> simp_all
  obtain ⟨g, hgNG, hga, hg4, hgW⟩ := hW.exists_cyclic_four
  have hgZ : ∀ x ∈ centerW W, g * x * g⁻¹ ∈ centerW W := by
    intro x hx
    obtain ⟨hxW, hxc⟩ := mem_centerW.mp hx
    refine mem_centerW.mpr ⟨(hgW x).mp hxW, fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (hgW (g⁻¹ * w * g)).mp
      refine (hgW _).mpr ?_
      simpa [mul_assoc] using hw
    have h1 := hxc _ hw'
    calc w * (g * x * g⁻¹) = g * ((g⁻¹ * w * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * w := by group
  have hg4' : g ^ 4 = 1 := by rw [← hg4]; exact pow_orderOf_eq_one g
  have hq2 : (g ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hg4'
  have hq1 : g ^ 2 ≠ 1 := fun e => by
    have := orderOf_dvd_of_pow_eq_one e
    rw [hg4] at this
    omega
  have hZa : ∀ y ∈ centerW W, y ≠ 1 → IsConj (c.a : G) y := fun y hy hy1 => by
    obtain ⟨n, -, hn⟩ := hW.exists_conj_a_of_mem_centerW hy hy1
    exact isConj_iff.mpr ⟨n, hn.symm⟩
  refine false_of_four_acting_on_nine (centerW W) h9 (centerW_abelian W)
    (fun x hx => c.OG_pow_three x (hW.centerW_le_OG hx)) hW.aG_mem_centerW c.aG_ne_one ?_ hg4'
    hgZ ?_
  · calc g * (c.a : G) * g⁻¹ = (c.a : G) * g * g⁻¹ := by rw [hga]
      _ = (c.a : G) := by group
  · by_contra hcon
    push Not at hcon
    refine c.false_of_involution_centralizes hq2 hq1 h9 (fun y hy => ?_) hZa
    have := hcon y hy
    calc y * g ^ 2 = (g ^ 2 * y * (g ^ 2)⁻¹) * g ^ 2 := by rw [this]
      _ = g ^ 2 * y := by group

theorem IsW.centerW_eq_zpowers_a
    {W : Subgroup G} (hW : c.IsW W) : centerW W = zpowers (c.a : G) :=
  (Subgroup.eq_of_le_of_card_ge hW.zpowers_a_le_centerW
    (by rw [hW.card_centerW_eq_three, Nat.card_zpowers, orderOf_aG])).symm

theorem IsW.conj_OG_le
    {W : Subgroup G} (hW : c.IsW W) {g : G} (hg : g ∈ normalizer (W : Set G)) :
    ∀ y ∈ c.OG, g * y * g⁻¹ ∈ c.OG := by
  set N' : Subgroup G := c.OG.map (MulAut.conj g).toMonoidHom with hN'
  have hN'card : Nat.card N' = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, c.card_OG_eq_81]
  have hmem : ∀ y : G, y ∈ N' ↔ ∃ n ∈ c.OG, g * n * g⁻¹ = y := by
    intro y
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, by simp⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, by simp⟩
  have hN'W : N' ≤ W := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := (hmem y).mp hy
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp (hW.OG_le hn)
  have hN'ab : ∀ x ∈ N', ∀ y ∈ N', x * y = y * x := by
    intro x hx y hy
    obtain ⟨n, hn, rfl⟩ := (hmem x).mp hx
    obtain ⟨m, hm, rfl⟩ := (hmem y).mp hy
    calc g * n * g⁻¹ * (g * m * g⁻¹) = g * (n * m) * g⁻¹ := by group
      _ = g * (m * n) * g⁻¹ := by rw [c.OG_comm n hn m hm]
      _ = g * m * g⁻¹ * (g * n * g⁻¹) := by group
  have hcent : ∀ x ∈ W, x ∉ c.OG →
      Nat.card ↥(c.OG ⊓ centralizer ({x} : Set G)) ≤ 9 := by
    intro x hx hxN
    have h3 : ∃ n : ℕ, x ^ (3 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hW.isPGroup ⟨x, hx⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    exact c.card_centralizer_le_nine h3 hxN
  have hZ : ∀ D : Subgroup G, D ≤ W → (∀ y ∈ D, ∀ w ∈ W, w * y = y * w) →
      Nat.card D ≤ 3 := by
    intro D hDW hD
    have hle : D ≤ centerW W := fun y hy => mem_centerW.mpr ⟨hDW hy, hD y hy⟩
    exact (Subgroup.card_le_of_le hle).trans (hW.card_centerW_eq_three.le)
  have hEq : c.OG = N' :=
    eq_of_abelian_of_card_eighty_one hW.card c.card_OG_eq_81 hN'card hW.OG_le hN'W
      c.OG_comm hN'ab hcent hZ
  intro y hy
  have h1 : g * y * g⁻¹ ∈ N' := (hmem _).mpr ⟨y, hy, rfl⟩
  rwa [← hEq] at h1

theorem IsW.normalizer_le_NG
    {W : Subgroup G} (hW : c.IsW W) : normalizer (W : Set G) ≤ c.NG := by
  intro g hg
  refine c.mem_NG_of_conj (hW.conj_OG_le hg) (fun y hy => ?_)
  have hg' : g⁻¹ ∈ normalizer (W : Set G) := (normalizer (W : Set G)).inv_mem hg
  simpa using hW.conj_OG_le hg' y hy

theorem IsW.card_eq_sylow
    {W : Subgroup G} (hW : c.IsW W) : Nat.card W = 3 ^ (Nat.card G).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact card_eq_pow_factorization_of_normalizer_le hW.isPGroup hW.le_NG
    (fun R hR hRp => (hW.le_card R hR hRp).trans_eq hW.card.symm) hW.normalizer_le_NG

theorem IsW.factorization_three_card
    {W : Subgroup G} (hW : c.IsW W) : (Nat.card G).factorization 3 = 6 := by
  have h := hW.card_eq_sylow
  rw [hW.card] at h
  exact (Nat.pow_right_injective (a := 3) (by norm_num) h).symm

theorem IsW.not_abelian_of_card
    {W : Subgroup G} (hW : c.IsW W) {A : Subgroup G} (hAW : A ≤ W) (hA : Nat.card A = 3 ^ 5)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : False := by
  have h81 := c.card_OG_eq_81
  have hAN : ¬ A ≤ c.OG := fun h => by
    have := Subgroup.card_le_of_le h
    rw [hA, h81] at this
    norm_num at this
  obtain ⟨x, hxA, hxN⟩ := Set.not_subset.mp hAN
  have h3 : ∃ n : ℕ, x ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hW.isPGroup ⟨x, hAW hxA⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have h9 := c.card_centralizer_le_nine h3 hxN
  have hnotle : 27 ≤ Nat.card ↥(A ⊓ c.OG) := by
    have e1 : A.relIndex W * Nat.card A = Nat.card W := by
      have := Subgroup.relIndex_mul_card A W
      rwa [inf_eq_left.mpr hAW] at this
    have e2 : c.OG.relIndex W * Nat.card c.OG = Nat.card W := by
      have := Subgroup.relIndex_mul_card c.OG W
      rwa [inf_eq_left.mpr hW.OG_le] at this
    have e3 : (A ⊓ c.OG).relIndex W * Nat.card (A ⊓ c.OG : Subgroup G) = Nat.card W := by
      have := Subgroup.relIndex_mul_card (A ⊓ c.OG) W
      rwa [inf_eq_left.mpr (inf_le_left.trans hAW)] at this
    have h1 : A.relIndex W = 3 := by rw [hA, hW.card] at e1; omega
    have h2 : c.OG.relIndex W = 9 := by rw [h81, hW.card] at e2; omega
    have h4 : (A ⊓ c.OG).relIndex W ≤ A.relIndex W * c.OG.relIndex W :=
      Subgroup.relIndex_inf_le
    rw [h1, h2] at h4
    rw [hW.card] at e3
    by_contra hlt
    push Not at hlt
    have : (A ⊓ c.OG).relIndex W * Nat.card (A ⊓ c.OG : Subgroup G) < 27 * 27 := by nlinarith
    omega
  have hle : A ⊓ c.OG ≤ c.OG ⊓ centralizer ({x} : Set G) := fun y hy =>
    ⟨hy.2, Subgroup.mem_centralizer_singleton_iff.mpr (hAab y hy.1 x hxA)⟩
  have := Subgroup.card_le_of_le hle
  omega

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong

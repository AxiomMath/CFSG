module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.G11BridgeSQTK

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open

section E27

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem commute_of_mem_sup_zpowers {x y z : Ω} (hx : Commute z x) (hy : Commute z y) {e : Ω}
    (he : e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Commute e z := by
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({z} : Set Ω) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hx
    · intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hy
  exact (Subgroup.mem_centralizer_iff.1 (hle he) z rfl).symm

theorem three_le_pRank_three_of_gens {X : Subgroup Ω} {x y c : Ω} (hx : x ∈ X) (hy : y ∈ X)
    (hc : c ∈ X) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hxy : Commute x y) (hxc : Commute x c) (hyc : Commute y c)
    (hyx : y ∉ Subgroup.zpowers x) (hcxy : c ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    3 ≤ CFSG.Open.pRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hordy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hc1 : c ≠ 1 := fun h => hcxy (h ▸ Subgroup.one_mem _)
  have hordc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hE0 : IsElemAbelian 3 (⊥ : Subgroup Ω) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]
    · rw [Subgroup.mem_bot.1 ha, one_pow]
  obtain ⟨hE1, hc1'⟩ := exists_elemAbelian_sup_zpowers (E := ⊥) hE0 hordx
    (fun e he => by rw [Subgroup.mem_bot.1 he]; exact Commute.one_left _)
    (fun h => hx1 (Subgroup.mem_bot.1 h))
  rw [bot_sup_eq] at hE1 hc1'
  obtain ⟨hE2, hc2'⟩ := exists_elemAbelian_sup_zpowers hE1 hordy
    (fun e he => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact hxy.zpow_left n) hyx
  obtain ⟨hE3, hc3'⟩ := exists_elemAbelian_sup_zpowers hE2 hordc
    (fun e he => commute_of_mem_sup_zpowers (z := c) hxc.symm hyc.symm he) hcxy
  refine le_pRank Nat.prime_three (E := Subgroup.zpowers x ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers c)
    ?_ hE3 (k := 3) ?_
  · exact sup_le (sup_le ((Subgroup.zpowers_le).2 hx) ((Subgroup.zpowers_le).2 hy))
      ((Subgroup.zpowers_le).2 hc)
  · rw [hc3', hc2', hc1', Subgroup.card_bot]
    norm_num


omit [Finite Ω] in
theorem layer_sup_eq_top {L K : Subgroup Ω} (hLq : CFSG.IsQuasisimple ↥L)
    (hKq : CFSG.IsQuasisimple ↥K) (hcomm : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) :
    CFSG.layer ↥(L ⊔ K) = ⊤ := by
  have hLM : L ≤ L ⊔ K := le_sup_left
  have hKM : K ≤ L ⊔ K := le_sup_right
  have hnormal : ∀ {A B : Subgroup Ω}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      A ⊔ B ≤ Subgroup.normalizer (A : Set Ω) := by
    intro A B hAB
    refine sup_le Subgroup.le_normalizer fun k hk => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro l
    have hcl : ∀ m ∈ A, k * m * k⁻¹ = m := fun m hm => by
      rw [← hAB m hm k hk]
      simp
    have hcl' : ∀ m ∈ A, k⁻¹ * m * k = m := fun m hm => by
      rw [← hAB m hm k⁻¹ (B.inv_mem hk)]
      simp
    constructor
    · intro hl
      rw [hcl l hl]
      exact hl
    · intro hl
      have h2 : k⁻¹ * (k * l * k⁻¹) * k = l := by group
      have h3 := hcl' _ hl
      have : l = k * l * k⁻¹ := h2.symm.trans h3
      rw [this]
      exact hl
  have hcomm' : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := fun k hk l hl => (hcomm l hl k hk).symm
  have hnL : (L.subgroupOf (L ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 (hnormal hcomm)
  have hnK : (K.subgroupOf (L ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 (by
      rw [sup_comm]
      exact hnormal hcomm')
  have hcL : CFSG.IsComponent (L.subgroupOf (L ⊔ K)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLM).symm hLq,
      hnL.isSubnormal⟩
  have hcK : CFSG.IsComponent (K.subgroupOf (L ⊔ K)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKM).symm hKq,
      hnK.isSubnormal⟩
  have htop : L.subgroupOf (L ⊔ K) ⊔ K.subgroupOf (L ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLM hKM, Subgroup.subgroupOf_self]
  refine eq_top_iff.2 ?_
  rw [← htop]
  exact sup_le (CFSG.LocalCores.component_le_layer hcL) (CFSG.LocalCores.component_le_layer hcK)

theorem sqtk_sup (hA21 : AsA21SQTKSection) {Γ L K : Subgroup Ω}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hLΓ : L ≤ Γ) (hKΓ : K ≤ Γ)
    (hLq : CFSG.IsQuasisimple ↥L) (hKq : CFSG.IsQuasisimple ↥K)
    (hcomm : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) : SQTKGroup ↥(L ⊔ K) := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := IsQuotientOfSQTKTauCeti.of_le (sup_le hLΓ hKΓ) hq
  have hlayer : CFSG.layer ↥(⊤ : Subgroup ↥(L ⊔ K)) = ⊤ :=
    CFSG.LocalCores.layer_eq_top_of_surjective (layer_sup_eq_top hLq hKq hcomm)
      (Subgroup.topEquiv (G := ↥(L ⊔ K))).symm.toMonoidHom
      (Subgroup.topEquiv (G := ↥(L ⊔ K))).symm.surjective
  have h2 : IsPGroup 2 (↥(L ⊔ K) ⧸ (⊤ : Subgroup ↥(L ⊔ K))) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_top _
  exact hA21 S ⟨hst, hkg⟩ ⊤ ↥(L ⊔ K) (φ.comp (⊤ : Subgroup S).subtype)
    (hφ.comp (Subgroup.topEquiv (G := S)).surjective) ⊤ hlayer h2

theorem false_of_commuting_components (hA21 : AsA21SQTKSection) {Γ L K : Subgroup Ω}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hLΓ : L ≤ Γ) (hKΓ : K ≤ Γ)
    (hLq : CFSG.IsQuasisimple ↥L) (hKq : CFSG.IsQuasisimple ↥K)
    (hcomm : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) {x y c : Ω} (hx : x ∈ L) (hy : y ∈ L)
    (hc : c ∈ K) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) (hcL : c ∉ L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSQ := sqtk_sup hA21 hq hLΓ hKΓ hLq hKq hcomm
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(L ⊔ K)) ≤ 2 :=
    hSQ.1 3 Nat.prime_three (by norm_num)
  rw [pRank_top_subtype] at hr
  have h3 : 3 ≤ CFSG.Open.pRank 3 (L ⊔ K) := by
    refine three_le_pRank_three_of_gens (x := x) (y := y) (c := c) (Subgroup.mem_sup_left hx)
      (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hc) hx1 hx3 hy3 hc3 hxy (hcomm x hx c hc)
      (hcomm y hy c hc) hyx fun hmem => hcL ?_
    have : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ L :=
      sup_le ((Subgroup.zpowers_le).2 hx) ((Subgroup.zpowers_le).2 hy)
    exact this hmem
  omega

end E27

end FFC

end CFSG.Quasithin

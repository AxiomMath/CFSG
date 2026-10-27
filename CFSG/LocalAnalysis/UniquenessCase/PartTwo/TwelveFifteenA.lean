module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nC
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace TwelveFifteen

theorem mem_centralizer_sup {U W : Subgroup G} {y : G}
    (hU : y ∈ centralizer (U : Set G)) (hW : y ∈ centralizer (W : Set G)) :
    y ∈ centralizer ((U ⊔ W : Subgroup G) : Set G) := by
  have h1 : zpowers y ≤ centralizer ((U ⊔ W : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.mp (zpowers_le.mpr hU))
      (le_centralizer_iff.mp (zpowers_le.mpr hW))
  exact zpowers_le.mp h1

theorem le_normalizer_centralizer {M K : Subgroup G} (hMK : M ≤ normalizer (K : Set G)) :
    M ≤ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ normalizer (K : Set G), ∀ c ∈ centralizer (K : Set G),
      m * c * m⁻¹ ∈ centralizer (K : Set G) := by
    intro m hm c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro k hk
    have hk' : m⁻¹ * k * m⁻¹⁻¹ ∈ K := (mem_normalizer_iff.1 (inv_mem hm) k).1 hk
    have := hc _ hk'
    calc k * (m * c * m⁻¹) = m * ((m⁻¹ * k * m⁻¹⁻¹) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * k * m⁻¹⁻¹)) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * k := by group
  intro m hm
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key m (hMK hm) c hc, fun hc => ?_⟩
  have := key m⁻¹ (inv_mem (hMK hm)) _ hc
  simpa [mul_assoc] using this

theorem le_normalizer_inf {M A B : Subgroup G} (hA : M ≤ normalizer (A : Set G))
    (hB : M ≤ normalizer (B : Set G)) : M ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro z
  simp only [mem_inf]
  rw [(mem_normalizer_iff.1 (hA hm)) z, (mem_normalizer_iff.1 (hB hm)) z]

theorem le_normalizer_sup {M A B : Subgroup G} (hA : M ≤ normalizer (A : Set G))
    (hB : M ≤ normalizer (B : Set G)) : M ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hA hm),
    mem_normalizer_iff_map_conj_eq.mp (hB hm)]

theorem exists_index_eq_two_pow {K X : Subgroup G} (hK : K ≤ normalizer (X : Set G))
    (h : ∀ x ∈ K, Odd (orderOf x) → x ∈ centralizer (X : Set G)) :
    ∃ n : ℕ, ((centralizer (X : Set G)).subgroupOf K).index = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hN : ((centralizer (X : Set G)).subgroupOf K).Normal := kerAct_normal K X hK
  have hP : IsPGroup 2 (↥K ⧸ (centralizer (X : Set G)).subgroupOf K) := by
    rw [IsPGroup.iff_orderOf]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    have hdvd : m ∣ orderOf g := ⟨2 ^ a, by rw [hgm, mul_comm]⟩
    have hord : orderOf (g ^ 2 ^ a) = m := by
      have := orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvd
      rwa [show orderOf g / m = 2 ^ a by rw [hgm, Nat.mul_div_cancel _ hm.pos]] at this
    have hmem : ((g ^ 2 ^ a : ↥K) : G) ∈ centralizer (X : Set G) := by
      apply h _ (g ^ 2 ^ a).2
      rw [Subgroup.orderOf_coe, hord]
      exact hm
    have h1 : (QuotientGroup.mk g : ↥K ⧸ (centralizer (X : Set G)).subgroupOf K) ^ 2 ^ a = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hmem
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨b, hb⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  exact ⟨n, hn⟩

theorem mem_centralizer_of_index_eq_two_pow {K X : Subgroup G}
    (hK : K ≤ normalizer (X : Set G))
    (h : ∃ n : ℕ, ((centralizer (X : Set G)).subgroupOf K).index = 2 ^ n) {x : G} (hx : x ∈ K)
    (hodd : Odd (orderOf x)) : x ∈ centralizer (X : Set G) := by
  haveI hN : ((centralizer (X : Set G)).subgroupOf K).Normal := kerAct_normal K X hK
  obtain ⟨n, hn⟩ := h
  have h1 : orderOf (QuotientGroup.mk ⟨x, hx⟩ :
      ↥K ⧸ (centralizer (X : Set G)).subgroupOf K) ∣ orderOf x := by
    have := orderOf_map_dvd (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf K)) ⟨x, hx⟩
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (QuotientGroup.mk ⟨x, hx⟩ :
      ↥K ⧸ (centralizer (X : Set G)).subgroupOf K) ∣ 2 ^ n := by
    rw [← hn]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_centralizer_of_commute {U K : Subgroup G} {x : G} (hU : IsPGroup 2 U)
    (hxU : x ∈ normalizer (U : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hodd : Odd (orderOf x))
    (hK2 : ∃ n : ℕ, ((centralizer (U : Set G)).subgroupOf K).index = 2 ^ n)
    (hcomm : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ centralizer (U : Set G))
    (hfix : ∀ u ∈ U, (∀ k ∈ K, k * u = u * k) → x * u = u * x) :
    x ∈ centralizer (U : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : zpowers x ≤ normalizer (U : Set G) := zpowers_le.mpr hxU
  let α : ↥(zpowers x) →* MulAut ↥U := U.normalizerMonoidHom.comp (inclusion hA)
  let β₀ : ↥K →* MulAut ↥U := U.normalizerMonoidHom.comp (inclusion hKU)
  let β : ↥β₀.range →* MulAut ↥U := β₀.range.subtype
  have hα : ∀ (a : ↥(zpowers x)) (u : ↥U), ((α a u : ↥U) : G) = a * u * (a : G)⁻¹ :=
    fun a u => normalizerMonoidHom_apply_apply_coe U (inclusion hA a) u
  have hβ₀ : ∀ (k : ↥K) (u : ↥U), ((β₀ k u : ↥U) : G) = k * u * (k : G)⁻¹ :=
    fun k u => normalizerMonoidHom_apply_apply_coe U (inclusion hKU k) u
  have hker : β₀.ker = (centralizer (U : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff]
    constructor
    · intro hk u hu
      have h := congrArg (fun f : MulAut ↥U => ((f ⟨u, hu⟩ : ↥U) : G)) hk
      simp only [hβ₀, MulAut.one_apply] at h
      calc u * (k : G) = k * u * (k : G)⁻¹ * k := by rw [h]
        _ = k * u := by group
    · intro hk
      refine MulEquiv.ext fun u => Subtype.ext ?_
      rw [hβ₀, MulAut.one_apply, ← hk u u.2]
      group
  haveI : Finite ↥β₀.range := Finite.of_surjective _ β₀.rangeRestrict_surjective
  have hB : IsPGroup 2 ↥β₀.range := by
    obtain ⟨n, hn⟩ := hK2
    apply IsPGroup.of_card (n := n)
    rw [← Subgroup.index_ker, hker, hn]
  have hA2 : ¬ 2 ∣ Nat.card ↥(zpowers x) := by
    rw [Nat.card_zpowers]
    rintro ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hodd
    omega
  have hcx : ∀ k : ↥K, α ⟨x, mem_zpowers x⟩ * β₀ k = β₀ k * α ⟨x, mem_zpowers x⟩ := by
    intro k
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ₀, hβ₀, hα]
    simp only
    have hc := mem_centralizer_iff.mp (hcomm k k.2)
    have hxu : x * (u : G) * x⁻¹ ∈ U := (mem_normalizer_iff.1 hxU u).1 u.2
    have hv : (k : G) * (x * u * x⁻¹) * (k : G)⁻¹ ∈ U :=
      (mem_normalizer_iff.1 (hKU k.2) _).1 hxu
    have := hc _ hv
    calc x * (k * u * (k : G)⁻¹) * x⁻¹
        = (x * k * x⁻¹ * (k : G)⁻¹) * (k * (x * u * x⁻¹) * (k : G)⁻¹) *
            (x * k * x⁻¹ * (k : G)⁻¹)⁻¹ := by group
      _ = k * (x * u * x⁻¹) * (k : G)⁻¹ := by rw [← this]; group
  have hcomm' : ∀ a b, α a * β b = β b * α a := by
    intro a b
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp a.2
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp b.2
    have ha : a = (⟨x, mem_zpowers x⟩ : ↥(zpowers x)) ^ j := Subtype.ext (by simp [hj])
    have hb : β b = β₀ k := by
      show (b : MulAut ↥U) = β₀ k
      exact hk.symm
    rw [hb, ha, map_zpow]
    exact ((Commute.zpow_left (hcx k) j)).eq
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    have hrK : ∀ k ∈ K, k * (r : G) = r * k := by
      intro k hk
      have h := congrArg Subtype.val (hr ⟨β₀ ⟨k, hk⟩, ⟨k, hk⟩, rfl⟩)
      have h' : ((β₀ ⟨k, hk⟩ r : ↥U) : G) = r := h
      rw [hβ₀] at h'
      calc k * (r : G) = k * r * k⁻¹ * k := by group
        _ = r * k := by rw [h']
    have hxr : Commute x (r : G) := hfix r r.2 hrK
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp a.2
    apply Subtype.ext
    rw [hα, ← hj, (hxr.zpow_left j).eq]
    group
  have key := CFSG.GroupTheory.thompson_A_times_B hU hA2 hB α β hcomm' hfix'
  rw [mem_centralizer_iff]
  intro u hu
  have h := congrArg (fun f : MulAut ↥U => ((f ⟨u, hu⟩ : ↥U) : G)) (key ⟨x, mem_zpowers x⟩)
  simp only [hα, MulAut.one_apply] at h
  calc u * x = x * u * x⁻¹ * x := by rw [h]
    _ = x * u := by group

theorem inf_centralizer_le_centralizer {M U W K : Subgroup G} (hU : IsPGroup 2 U)
    (hMU : M ≤ normalizer (U : Set G)) (hMW : M ≤ normalizer (W : Set G))
    (hred : TwoReduced M (U ⊔ W)) (hKM : K ≤ M) (hMK : M ≤ normalizer (K : Set G))
    (hCK : M ⊓ centralizer (U : Set G) ≤ K)
    (hK2 : ∃ n : ℕ, ((centralizer (U : Set G)).subgroupOf K).index = 2 ^ n) :
    M ⊓ centralizer (((U ⊓ centralizer (K : Set G)) ⊔ W : Subgroup G) : Set G) ≤
      centralizer ((U ⊔ W : Subgroup G) : Set G) := by
  set Y : Subgroup G := (U ⊓ centralizer (K : Set G)) ⊔ W with hY
  set N : Subgroup G := M ⊓ centralizer (Y : Set G) with hN
  have hMY : M ≤ normalizer (Y : Set G) :=
    le_normalizer_sup (le_normalizer_inf hMU (le_normalizer_centralizer hMK)) hMW
  have hMUW : M ≤ normalizer ((U ⊔ W : Subgroup G) : Set G) := le_normalizer_sup hMU hMW
  have hMN : M ≤ normalizer (N : Set G) := uc22p22nc_le_normalizer_inf_centralizer hMY
  have hYUW : Y ≤ U ⊔ W := sup_le_sup_right inf_le_left W
  have hCUW_N : M ⊓ centralizer ((U ⊔ W : Subgroup G) : Set G) ≤ N :=
    inf_le_inf_left M (centralizer_le hYUW)
  have hCUW_U : centralizer ((U ⊔ W : Subgroup G) : Set G) ≤ centralizer (U : Set G) :=
    centralizer_le (le_sup_left : U ≤ U ⊔ W)
  have hNW : N ≤ centralizer (W : Set G) :=
    inf_le_right.trans (centralizer_le (le_sup_right : W ≤ Y))
  have hKU : K ≤ normalizer (U : Set G) := hKM.trans hMU
  have hNK : N ⊓ K ≤ centralizer ((U ⊔ W : Subgroup G) : Set G) := by
    apply hred (N ⊓ K) (inf_le_right.trans hKM) (le_normalizer_inf hMN hMK)
      (le_inf hCUW_N (le_trans (inf_le_inf_left M hCUW_U) hCK))
    apply exists_index_eq_two_pow ((inf_le_right.trans hKM).trans hMUW)
    intro y hy hyo
    exact mem_centralizer_sup
      (mem_centralizer_of_index_eq_two_pow hKU hK2 hy.2 hyo) (hNW hy.1)
  have hodd : ∀ x ∈ N, Odd (orderOf x) → x ∈ centralizer (U : Set G) := by
    intro x hx hxo
    have hxM : x ∈ M := hx.1
    apply mem_centralizer_of_commute hU (hMU hxM) hKU hxo hK2
    · intro k hk
      apply hCUW_U
      apply hNK
      refine ⟨?_, ?_⟩
      · have hkN : k * x⁻¹ * k⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hMN (hKM hk)) x⁻¹).mp (N.inv_mem hx)
        have := N.mul_mem hx hkN
        simpa [mul_assoc] using this
      · have hxk : x * k * x⁻¹ ∈ K := (mem_normalizer_iff.mp (hMK hxM) k).mp hk
        exact K.mul_mem hxk (K.inv_mem hk)
    · intro u hu hku
      have huY : u ∈ Y :=
        (le_sup_left : U ⊓ centralizer (K : Set G) ≤ Y) ⟨hu, mem_centralizer_iff.mpr hku⟩
      exact (mem_centralizer_iff.mp hx.2 u huY).symm
  apply hred N inf_le_left hMN hCUW_N
  apply exists_index_eq_two_pow (inf_le_left.trans hMUW)
  intro x hx hxo
  exact mem_centralizer_sup (hodd x hx hxo) (hNW hx)

theorem twoReduced_of_forall_eq {M U W : Subgroup G} (hU : IsPGroup 2 U)
    (hMU : M ≤ normalizer (U : Set G)) (hMW : M ≤ normalizer (W : Set G))
    (hred : TwoReduced M (U ⊔ W))
    (hmin : ∀ U' : Subgroup G, U' ≤ U → M ≤ normalizer (U' : Set G) →
      M ⊓ centralizer ((U' ⊔ W : Subgroup G) : Set G) ≤
        centralizer ((U ⊔ W : Subgroup G) : Set G) → U' = U) :
    TwoReduced M U := by
  intro K hKM hMK hCK hK2
  have hc := inf_centralizer_le_centralizer hU hMU hMW hred hKM hMK hCK hK2
  have heq := hmin (U ⊓ centralizer (K : Set G)) inf_le_left
    (le_normalizer_inf hMU (le_normalizer_centralizer hMK)) hc
  have hUK : U ≤ centralizer (K : Set G) := by
    rw [← heq]
    exact inf_le_right
  exact le_centralizer_iff.mp hUK

end TwelveFifteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

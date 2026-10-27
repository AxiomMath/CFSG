module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Sylow

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open Subgroup (zpowers)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_CJ_conj_iff_of_inv {g σ : G} (hg : g ∈ H z) (hgσ : g * σ * g⁻¹ = σ⁻¹) (a : G) :
    a ∈ CJ z σ ↔ g * a * g⁻¹ ∈ CJ z σ := by
  have key : ∀ x y : G, x ∈ H z → x * σ * x⁻¹ = σ⁻¹ → y ∈ CJ z σ → x * y * x⁻¹ ∈ CJ z σ := by
    intro x y hx hxσ hy
    obtain ⟨hyc, hyJ⟩ := mem_CJ.mp hy
    refine mem_CJ.mpr ⟨?_, conj_mem_J hx hyJ⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    have hyσ' : y * σ⁻¹ = σ⁻¹ * y := by
      calc y * σ⁻¹ = σ⁻¹ * (σ * y) * σ⁻¹ := by group
        _ = σ⁻¹ * (y * σ) * σ⁻¹ := by rw [hyc]
        _ = σ⁻¹ * y := by group
    have hx' : x * σ⁻¹ * x⁻¹ = σ := by
      calc x * σ⁻¹ * x⁻¹ = (x * σ * x⁻¹)⁻¹ := by group
        _ = σ := by rw [hxσ, inv_inv]
    calc x * y * x⁻¹ * σ = x * y * x⁻¹ * (x * σ⁻¹ * x⁻¹) := by rw [hx']
      _ = x * (y * σ⁻¹) * x⁻¹ := by group
      _ = x * (σ⁻¹ * y) * x⁻¹ := by rw [hyσ']
      _ = (x * σ⁻¹ * x⁻¹) * (x * y * x⁻¹) := by group
      _ = σ * (x * y * x⁻¹) := by rw [hx']
  have hgσ' : g⁻¹ * σ * g⁻¹⁻¹ = σ⁻¹ := by
    have h1 : g⁻¹ * σ⁻¹ * g = σ := by
      calc g⁻¹ * σ⁻¹ * g = g⁻¹ * (g * σ * g⁻¹) * g := by rw [hgσ]
        _ = σ := by group
    calc g⁻¹ * σ * g⁻¹⁻¹ = (g⁻¹ * σ⁻¹ * g)⁻¹ := by group
      _ = σ⁻¹ := by rw [h1]
  constructor
  · exact key g a hg hgσ
  · intro h
    have := key g⁻¹ (g * a * g⁻¹) ((H z).inv_mem hg) hgσ' h
    simpa [mul_assoc] using this

theorem mem_commutator_conj_iff_of_inv {g σ : G} (hg : g ∈ H z) (hgσ : g * σ * g⁻¹ = σ⁻¹)
    (a : G) : a ∈ ⁅zpowers σ, J z⁆ ↔ g * a * g⁻¹ ∈ ⁅zpowers σ, J z⁆ := by
  have hmap : ∀ x : G, x ∈ H z → x * σ * x⁻¹ = σ⁻¹ →
      ⁅zpowers σ, J z⁆.map (MulAut.conj x).toMonoidHom = ⁅zpowers σ, J z⁆ := by
    intro x hx hxσ
    rw [Subgroup.map_commutator, map_conj_J hx, MonoidHom.map_zpowers]
    congr 1
    change zpowers (x * σ * x⁻¹) = zpowers σ
    rw [hxσ, Subgroup.zpowers_inv]
  have hgσ' : g⁻¹ * σ * g⁻¹⁻¹ = σ⁻¹ := by
    have h1 : g⁻¹ * σ⁻¹ * g = σ := by
      calc g⁻¹ * σ⁻¹ * g = g⁻¹ * (g * σ * g⁻¹) * g := by rw [hgσ]
        _ = σ := by group
    calc g⁻¹ * σ * g⁻¹⁻¹ = (g⁻¹ * σ⁻¹ * g)⁻¹ := by group
      _ = σ⁻¹ := by rw [h1]
  constructor
  · intro ha
    rw [← hmap g hg hgσ]
    exact ⟨a, ha, by simp⟩
  · intro ha
    have h := hmap g⁻¹ ((H z).inv_mem hg) hgσ'
    rw [← h]
    exact ⟨g * a * g⁻¹, ha, by simp [mul_assoc]⟩

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem s_pow_three : (s1 * s2⁻¹) ^ 3 = 1 := by
  have h1 : s1 ^ 3 = 1 := hy.s1_pow_three
  have h2 : s2 ^ 3 = 1 := by rw [← hy.orderOf_s2, pow_orderOf_eq_one]
  have hc : Commute s1 s2⁻¹ := (show Commute s1 s2 from hy.comm12).inv_right
  rw [hc.mul_pow, inv_pow, h1, h2, inv_one, mul_one]

theorem s_fix_imV_R {v : V z} (hv : v ∈ imV z hy.R)
    (hfix : conjVA z (⟨s1 * s2⁻¹, hy.s_mem⟩ : ↥(H z)) v = v) : v = 1 := by
  obtain ⟨r, hr, rfl⟩ := mem_imV.mp hv
  have hc := (conjVA_pi_eq_iff hy.hA1 _ r).mp hfix
  have hcomm := hy.commute_of_cube hy.s_mem hy.s_pow_three hc
  have hrC : (r : G) ∈ CJ z (s1 * s2⁻¹) := by
    refine mem_CJ.mpr ⟨?_, r.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  exact (pi_eq_one_iff hy.hA1).mpr (hy.mem_zpowers_of_mem_CJs_of_mem_R hrC hr)

theorem free_of_inv {g : G} (hg : g ∈ H z) (hgs : g * (s1 * s2⁻¹) * g⁻¹ = (s1 * s2⁻¹)⁻¹)
    (hg2 : g * g ∈ J z) :
    ∀ v ∈ imV z hy.R, conjVA z (⟨g, hg⟩ : ↥(H z)) v = v →
      ∃ w ∈ imV z hy.R, v = conjVA z (⟨g, hg⟩ : ↥(H z)) w * w := by
  set gH : ↥(H z) := ⟨g, hg⟩ with hgH
  set sH : ↥(H z) := ⟨s1 * s2⁻¹, hy.s_mem⟩ with hsH
  set τ := conjVA z gH with hτ
  set β := conjVA z sH with hβ
  have hτB : ∀ v, τ v ∈ imV z hy.R ↔ v ∈ imV z hy.R :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R gH (mem_commutator_conj_iff_of_inv hg hgs)
  have hβB : ∀ v, β v ∈ imV z hy.R ↔ v ∈ imV z hy.R :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R sH (mem_commutator_conj_iff hy.s_mem rfl)
  have hτ2 : ∀ v ∈ imV z hy.R, τ (τ v) = v := by
    intro v _
    have h := conjVA_apply_of_mem_J hy.hA1 (g := gH * gH) hg2 v
    rwa [map_mul, MulAut.mul_apply] at h
  have hβ3 : ∀ v ∈ imV z hy.R, (β ^ 3) v = v := by
    intro v _
    have : sH ^ 3 = 1 := Subtype.ext (by simpa [hsH] using hy.s_pow_three)
    rw [← map_pow, this, map_one]
    rfl
  have hτβ : ∀ v ∈ imV z hy.R, τ (β v) = (β ^ 2) (τ v) := by
    intro v _
    have e : gH * sH = sH⁻¹ * gH := by
      apply Subtype.ext
      change g * (s1 * s2⁻¹) = (s1 * s2⁻¹)⁻¹ * g
      rw [← hgs]
      group
    have e2 : sH⁻¹ = sH ^ 2 := by
      have : sH ^ 3 = 1 := Subtype.ext (by simpa [hsH] using hy.s_pow_three)
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact this
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_pow, ← map_mul, e, e2]
  have hcard := card_fix_sq_le_of_conj_inv (imV z hy.R) τ β hβB hβ3
    (fun v hv hfix => hy.s_fix_imV_R hv hfix) hτβ
  exact exists_eq_mul_of_card_fix_sq_le (V_comm hy.hA1) (imV z hy.R) τ hτB hτ2
    (fun v _ => V_sq hy.hA1 v) hcard

theorem commute_of_mem_CJs_of_swap {u₁ : G} (hu₁H : u₁ ∈ H z) (hus1 : u₁ * s1 * u₁⁻¹ = s2)
    (hus2 : u₁ * s2 * u₁⁻¹ = s1) (huJ0 : ∀ a ∈ CJ z s1, u₁ * a = a * u₁) (hu2 : u₁ * u₁ ∈ J z) :
    ∀ c ∈ CJ z (s1 * s2⁻¹), u₁ * c = c * u₁ := by
  have hus : u₁ * (s1 * s2⁻¹) * u₁⁻¹ = (s1 * s2⁻¹)⁻¹ := by
    have hc : s2 * s1⁻¹ = (s1 * s2⁻¹)⁻¹ := by group
    calc u₁ * (s1 * s2⁻¹) * u₁⁻¹ = (u₁ * s1 * u₁⁻¹) * (u₁ * s2 * u₁⁻¹)⁻¹ := by group
      _ = (s1 * s2⁻¹)⁻¹ := by rw [hus1, hus2, hc]
  have hW : ∀ a : G, a ∈ ⁅zpowers s1, J z⁆ ↔ u₁ * a * u₁⁻¹ ∈ ⁅zpowers s1, J z⁆ := by
    have hcomm : ∀ x : G, x ∈ H z → (∀ a ∈ CJ z s1, x * a = a * x) →
        ∀ a, a ∈ ⁅zpowers s1, J z⁆ → x * a * x⁻¹ ∈ ⁅zpowers s1, J z⁆ := by
      intro x hx hxJ0 a ha
      rw [hy.W_eq] at ha ⊢
      obtain ⟨haJ, hac⟩ := ha
      refine ⟨conj_mem_J hx haJ, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have h1 : b * a = a * b := Subgroup.mem_centralizer_iff.mp hac b hb
      have h2 : x⁻¹ * b * x = b := by
        calc x⁻¹ * b * x = x⁻¹ * (b * x) := by group
          _ = x⁻¹ * (x * b) := by rw [hxJ0 b hb]
          _ = b := by group
      calc b * (x * a * x⁻¹) = x * ((x⁻¹ * b * x) * a) * x⁻¹ := by group
        _ = x * (b * a) * x⁻¹ := by rw [h2]
        _ = x * (a * b) * x⁻¹ := by rw [h1]
        _ = x * a * (x⁻¹ * b * x) * x⁻¹ := by rw [h2]; group
        _ = x * a * x⁻¹ * b := by group
    have hinvJ0 : ∀ a ∈ CJ z s1, u₁⁻¹ * a = a * u₁⁻¹ := by
      intro a ha
      calc u₁⁻¹ * a = u₁⁻¹ * (a * u₁) * u₁⁻¹ := by group
        _ = u₁⁻¹ * (u₁ * a) * u₁⁻¹ := by rw [huJ0 a ha]
        _ = a * u₁⁻¹ := by group
    intro a
    constructor
    · exact hcomm u₁ hu₁H huJ0 a
    · intro h
      have := hcomm u₁⁻¹ ((H z).inv_mem hu₁H) hinvJ0 _ h
      simpa [mul_assoc] using this
  have hQ : ∀ a : G, a ∈ hy.Q ↔ u₁ * a * u₁⁻¹ ∈ hy.Q := by
    intro a
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_CJ_conj_iff_of_inv hu₁H hus a).mp h1, (hW a).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_CJ_conj_iff_of_inv hu₁H hus a).mpr h1, (hW a).mpr h2⟩
  have hk : u₁ ^ 2 ^ 10 = 1 := by
    have h1 := pow_card_eq_one' (G := J z) (x := ⟨u₁ * u₁, hu2⟩)
    rw [hy.hA1.card_J] at h1
    have h2 : (u₁ * u₁) ^ 2 ^ 9 = 1 := congrArg Subtype.val h1
    rw [show (2 : ℕ) ^ 10 = 2 * 2 ^ 9 by norm_num, pow_mul, pow_two]
    exact h2
  have hbs : ∀ q ∈ hy.Q, u₁ * (s1 * q * s1⁻¹) * u₁⁻¹ = s1 * (u₁ * q * u₁⁻¹) * s1⁻¹ := by
    intro q hq
    have hq' : u₁ * q * u₁⁻¹ ∈ hy.Q := (hQ q).mp hq
    have hcs : (u₁ * q * u₁⁻¹) * (s1 * s2⁻¹) = (s1 * s2⁻¹) * (u₁ * q * u₁⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hq'.1).1
    have e : s1⁻¹ * s2 = (s1 * s2⁻¹)⁻¹ := by
      calc s1⁻¹ * s2 = s1⁻¹ * (s2 * s1) * s1⁻¹ := by group
        _ = s1⁻¹ * (s1 * s2) * s1⁻¹ := by rw [hy.comm12]
        _ = (s1 * s2⁻¹)⁻¹ := by group
    have hcomm' : s1⁻¹ * s2 * (u₁ * q * u₁⁻¹) = (u₁ * q * u₁⁻¹) * (s1⁻¹ * s2) := by
      rw [e]
      calc (s1 * s2⁻¹)⁻¹ * (u₁ * q * u₁⁻¹)
          = (s1 * s2⁻¹)⁻¹ * ((u₁ * q * u₁⁻¹) * (s1 * s2⁻¹)) * (s1 * s2⁻¹)⁻¹ := by group
        _ = (s1 * s2⁻¹)⁻¹ * ((s1 * s2⁻¹) * (u₁ * q * u₁⁻¹)) * (s1 * s2⁻¹)⁻¹ := by rw [hcs]
        _ = (u₁ * q * u₁⁻¹) * (s1 * s2⁻¹)⁻¹ := by group
    calc u₁ * (s1 * q * s1⁻¹) * u₁⁻¹
        = (u₁ * s1 * u₁⁻¹) * (u₁ * q * u₁⁻¹) * (u₁ * s1 * u₁⁻¹)⁻¹ := by group
      _ = s2 * (u₁ * q * u₁⁻¹) * s2⁻¹ := by rw [hus1]
      _ = s1 * (s1⁻¹ * s2 * (u₁ * q * u₁⁻¹)) * s2⁻¹ := by group
      _ = s1 * ((u₁ * q * u₁⁻¹) * (s1⁻¹ * s2)) * s2⁻¹ := by rw [hcomm']
      _ = s1 * (u₁ * q * u₁⁻¹) * s1⁻¹ := by group
  have hQc := hy.commute_of_mem_Q hu₁H hQ hk hbs
  intro c hc
  obtain ⟨a, ha, q, hq, rfl⟩ := hy.exists_mul_of_mem_CJs hc
  calc u₁ * (a * q) = (u₁ * a) * q := by group
    _ = (a * u₁) * q := by rw [huJ0 a ha]
    _ = a * (u₁ * q) := by group
    _ = a * (q * u₁) := by rw [hQc q hq]
    _ = a * q * u₁ := by group

end Hyp

section Lift

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

omit [Finite G] in
theorem mem_J_of_qHP_eq_one {x : ↥(H z)} (hx : qHP D x = 1) : (x : G) ∈ J z := by
  have hk : x ∈ (qHP D).ker := hx
  rw [ker_qHP] at hk
  exact Subgroup.mem_subgroupOf.mp hk

theorem exists_u1 (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G))
    (hJ0 : H z ≤ Subgroup.normalizer (CJ z ((s1HP D : ↥(H z)) : G) : Set G))
    (hus1 : ((uHP D : ↥(H z)) : G) * ((s1HP D : ↥(H z)) : G) * ((uHP D : ↥(H z)) : G)⁻¹ =
      ((s2HP D : ↥(H z)) : G)) :
    ∃ u₁ : G, u₁ ∈ H z ∧ ((uHP D : ↥(H z)) : G)⁻¹ * u₁ ∈ J z ∧
      u₁ * ((s1HP D : ↥(H z)) : G) * u₁⁻¹ = ((s2HP D : ↥(H z)) : G) ∧
      u₁ * ((s2HP D : ↥(H z)) : G) * u₁⁻¹ = ((s1HP D : ↥(H z)) : G) ∧
      ∀ a ∈ CJ z ((s1HP D : ↥(H z)) : G), u₁ * a = a * u₁ := by
  set s1 : G := ((s1HP D : ↥(H z)) : G) with hs1
  set s2 : G := ((s2HP D : ↥(H z)) : G) with hs2
  set uu : G := ((uHP D : ↥(H z)) : G) with huu
  set tt : G := ((tHP D : ↥(H z)) : G) with htt
  set b : G := ((betaHP D : ↥(H z)) : G) with hb
  have hbH : b ∈ H z := (betaHP D).2
  have huH : uu ∈ H z := (uHP D).2
  have hus2 : uu * s2 * uu⁻¹ = s1 := congrArg Subtype.val (uHP_conj_s2HP D)
  obtain ⟨t₁, ht₁H, ht₁J, -, -, htJ0, -⟩ := exists_t1 D hy
  have hgJ : t₁⁻¹ * (b * uu * b⁻¹) ∈ J z := by
    have hq : qHP D ((tHP D)⁻¹ * (betaHP D * uHP D * (betaHP D)⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, qHP_tHP, qHP_betaHP, qHP_uHP]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [beta_mul_u]
      group
    have hk := mem_J_of_qHP_eq_one D hq
    have hk' : tt⁻¹ * (b * uu * b⁻¹) ∈ J z := by simpa using hk
    have ht₁' : t₁⁻¹ * tt ∈ J z := by
      have e : t₁⁻¹ * tt = (tt⁻¹ * t₁)⁻¹ := by group
      rw [e]
      exact (J z).inv_mem ht₁J
    have e : t₁⁻¹ * (b * uu * b⁻¹) = (t₁⁻¹ * tt) * (tt⁻¹ * (b * uu * b⁻¹)) := by group
    rw [e]
    exact (J z).mul_mem ht₁' hk'
  have htriv : ∀ a ∈ CJ z s1, uu * a * uu⁻¹ * a⁻¹ ∈ zpowers z := by
    intro a ha
    set g := b * uu * b⁻¹ with hg
    set j := t₁⁻¹ * g with hj
    have ha' : b * a * b⁻¹ ∈ CJ z s1 :=
      (Subgroup.mem_normalizer_iff.mp (hJ0 hbH) a).mp ha
    set a' := b * a * b⁻¹ with ha'def
    set ε := j * a' * j⁻¹ * a'⁻¹ with hε
    have hεz : ε ∈ zpowers z := hy.comm_mem hgJ ((CJ_le_J _) ha')
    have ht₁ε : t₁ * ε = ε * t₁ := hy.commute_of_mem_zpowers_of_mem_H ht₁H hεz
    have ht₁a' : t₁ * a' = a' * t₁ := htJ0 a' ha'
    have hgt : g = t₁ * j := by rw [hj]; group
    have hga : g * a' * g⁻¹ * a'⁻¹ = ε := by
      have hja : j * a' * j⁻¹ = ε * a' := by rw [hε]; group
      calc g * a' * g⁻¹ * a'⁻¹ = t₁ * (j * a' * j⁻¹) * t₁⁻¹ * a'⁻¹ := by rw [hgt]; group
        _ = t₁ * (ε * a') * t₁⁻¹ * a'⁻¹ := by rw [hja]
        _ = (t₁ * ε) * a' * t₁⁻¹ * a'⁻¹ := by group
        _ = (ε * t₁) * a' * t₁⁻¹ * a'⁻¹ := by rw [ht₁ε]
        _ = ε * (t₁ * a') * t₁⁻¹ * a'⁻¹ := by group
        _ = ε * (a' * t₁) * t₁⁻¹ * a'⁻¹ := by rw [ht₁a']
        _ = ε := by group
    have e : uu * a * uu⁻¹ * a⁻¹ = b⁻¹ * (g * a' * g⁻¹ * a'⁻¹) * b := by
      rw [hg, ha'def]; group
    have hb' := conj_eq_of_mem_zpowers ((H z).inv_mem hbH) hεz
    rw [inv_inv] at hb'
    rw [e, hga, hb']
    exact hεz
  have hnorm_u : ∀ a : G, a ∈ CJ z s1 ↔ uu * a * uu⁻¹ ∈ CJ z s1 :=
    Subgroup.mem_normalizer_iff.mp (hJ0 huH)
  let σ : MulAut ↥(CJ z s1) := conjAut (CJ z s1) uu hnorm_u
  obtain ⟨q₀, hq₀⟩ := CFSG.GroupTheory.exists_conj_eq_of_forall_apply_mul_inv_mem_center
    (CFSG.IsExtraspecial2.toIsExtraspecialPGroup hy.isExtraspecial2_J0) σ (by
      intro x
      have hmem := htriv x x.2
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAut_apply_coe, σ]
      exact (hy.commute_of_mem_zpowers_of_mem_H (J_le_H ((CJ_le_J _) c.2)) hmem))
  have hq₀' : ∀ a ∈ CJ z s1, uu * a * uu⁻¹ = (q₀ : G) * a * (q₀ : G)⁻¹ := by
    intro a ha
    have := congrArg Subtype.val (hq₀ ⟨a, ha⟩)
    simpa [σ, conjAut_apply_coe] using this
  have hq₀s1 : (q₀ : G) * s1 = s1 * (q₀ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp q₀.2).1
  have hq₀2 : (q₀ : G) ∈ CJ z s2 := by
    rw [← hy.heq]
    exact q₀.2
  have hq₀s2 : (q₀ : G) * s2 = s2 * (q₀ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hq₀2).1
  have hq₀J : (q₀ : G) ∈ J z := (CJ_le_J _) q₀.2
  refine ⟨(q₀ : G)⁻¹ * uu, (H z).mul_mem ((H z).inv_mem (J_le_H hq₀J)) huH, ?_, ?_, ?_, ?_⟩
  · have e : uu⁻¹ * ((q₀ : G)⁻¹ * uu) = uu⁻¹ * (q₀ : G)⁻¹ * uu⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_J ((H z).inv_mem huH) ((J z).inv_mem hq₀J)
  · calc (q₀ : G)⁻¹ * uu * s1 * ((q₀ : G)⁻¹ * uu)⁻¹
        = (q₀ : G)⁻¹ * (uu * s1 * uu⁻¹) * (q₀ : G) := by group
      _ = (q₀ : G)⁻¹ * s2 * (q₀ : G) := by rw [hus1]
      _ = (q₀ : G)⁻¹ * (s2 * (q₀ : G)) := by group
      _ = (q₀ : G)⁻¹ * ((q₀ : G) * s2) := by rw [hq₀s2]
      _ = s2 := by group
  · calc (q₀ : G)⁻¹ * uu * s2 * ((q₀ : G)⁻¹ * uu)⁻¹
        = (q₀ : G)⁻¹ * (uu * s2 * uu⁻¹) * (q₀ : G) := by group
      _ = (q₀ : G)⁻¹ * s1 * (q₀ : G) := by rw [hus2]
      _ = (q₀ : G)⁻¹ * (s1 * (q₀ : G)) := by group
      _ = (q₀ : G)⁻¹ * ((q₀ : G) * s1) := by rw [hq₀s1]
      _ = s1 := by group
  · intro a ha
    have h := hq₀' a ha
    calc (q₀ : G)⁻¹ * uu * a = (q₀ : G)⁻¹ * (uu * a * uu⁻¹) * uu := by group
      _ = (q₀ : G)⁻¹ * ((q₀ : G) * a * (q₀ : G)⁻¹) * uu := by rw [h]
      _ = a * ((q₀ : G)⁻¹ * uu) := by group

omit [Finite G] in
theorem qHP_eq_of_inv_mul_mem_J {x y : ↥(H z)} (h : (x : G)⁻¹ * y ∈ J z) :
    qHP D y = qHP D x := by
  have hk : x⁻¹ * y ∈ (qHP D).ker := by
    rw [ker_qHP]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using h)
  have h1 : qHP D (x⁻¹ * y) = 1 := hk
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem betaHP_conj_mem {u₁ t₁ : G} (hu₁H : u₁ ∈ H z) (ht₁H : t₁ ∈ H z)
    (hu₁J : ((uHP D : ↥(H z)) : G)⁻¹ * u₁ ∈ J z) (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z) :
    t₁⁻¹ * (((betaHP D : ↥(H z)) : G) * u₁ * ((betaHP D : ↥(H z)) : G)⁻¹) ∈ J z := by
  have hq : qHP D ((⟨t₁, ht₁H⟩ : ↥(H z))⁻¹ * (betaHP D * ⟨u₁, hu₁H⟩ * (betaHP D)⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv,
      qHP_eq_of_inv_mul_mem_J D (x := tHP D) (y := ⟨t₁, ht₁H⟩) ht₁J,
      qHP_eq_of_inv_mul_mem_J D (x := uHP D) (y := ⟨u₁, hu₁H⟩) hu₁J,
      qHP_tHP, qHP_uHP, qHP_betaHP]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    rw [beta_mul_u]
    group
  simpa using mem_J_of_qHP_eq_one D hq

theorem sq_mem_J_and_comm_mem_J {u₁ t₁ : G} (hu₁H : u₁ ∈ H z) (ht₁H : t₁ ∈ H z)
    (hu₁J : ((uHP D : ↥(H z)) : G)⁻¹ * u₁ ∈ J z) (ht₁J : ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z) :
    u₁ * u₁ ∈ J z ∧ u₁ * t₁ * u₁⁻¹ * t₁⁻¹ ∈ J z ∧ (u₁ * t₁) * (u₁ * t₁) ∈ J z := by
  have hu := qHP_eq_of_inv_mul_mem_J D (x := uHP D) (y := ⟨u₁, hu₁H⟩) hu₁J
  have ht := qHP_eq_of_inv_mul_mem_J D (x := tHP D) (y := ⟨t₁, ht₁H⟩) ht₁J
  rw [qHP_uHP] at hu
  rw [qHP_tHP] at ht
  refine ⟨?_, ?_, ?_⟩
  · have hq : qHP D (⟨u₁, hu₁H⟩ * ⟨u₁, hu₁H⟩) = 1 := by
      rw [map_mul, hu]
      exact Subtype.ext u_sq
    simpa using mem_J_of_qHP_eq_one D hq
  · have hq : qHP D (⟨u₁, hu₁H⟩ * ⟨t₁, ht₁H⟩ * (⟨u₁, hu₁H⟩ : ↥(H z))⁻¹ *
        (⟨t₁, ht₁H⟩ : ↥(H z))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu, ht]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [← t_commute_u]
      group
    simpa using mem_J_of_qHP_eq_one D hq
  · have hq : qHP D ((⟨u₁, hu₁H⟩ * ⟨t₁, ht₁H⟩) * (⟨u₁, hu₁H⟩ * ⟨t₁, ht₁H⟩)) = 1 := by
      rw [map_mul, map_mul, hu, ht]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_one]
      calc u * t * (u * t) = u * (t * u) * t := by group
        _ = u * (u * t) * t := by rw [t_commute_u]
        _ = (u * u) * (t * t) := by group
        _ = 1 := by rw [u_sq, t_sq, one_mul]
    simpa using mem_J_of_qHP_eq_one D hq

end Lift

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem exists_mul_sq_mem_zpowers {g : G} (hg : g ∈ H z)
    (hgC : ∀ c ∈ CJ z (s1 * s2⁻¹), g * c = c * g) (hg2 : g * g ∈ J z)
    (hfree : ∀ v ∈ imV z hy.R, conjVA z (⟨g, hg⟩ : ↥(H z)) v = v →
      ∃ w ∈ imV z hy.R, v = conjVA z (⟨g, hg⟩ : ↥(H z)) w * w) :
    ∃ w ∈ hy.R, (g * w) * (g * w) ∈ zpowers z := by
  have hg2R : g * g ∈ hy.R := by
    obtain ⟨c, hc, r, hr, hcr⟩ := hy.exists_mul_of_mem_J hg2
    have hcz : c ∈ zpowers z := by
      apply hy.mem_zpowers_of_mem_CJs_of_commute hc
      intro d hd
      have h1 : (g * g) * d = d * (g * g) := by
        calc (g * g) * d = g * (g * d) := by group
          _ = g * (d * g) := by rw [hgC d hd]
          _ = (g * d) * g := by group
          _ = (d * g) * g := by rw [hgC d hd]
          _ = d * (g * g) := by group
      have h2 : r⁻¹ * d = d * r⁻¹ := by
        have h3 : r * d = d * r := (hy.commute_CJs_R d hd r hr).symm
        calc r⁻¹ * d = r⁻¹ * (d * r) * r⁻¹ := by group
          _ = r⁻¹ * (r * d) * r⁻¹ := by rw [h3]
          _ = d * r⁻¹ := by group
      have hc' : c = (g * g) * r⁻¹ := by rw [hcr]; group
      rw [hc']
      calc (g * g) * r⁻¹ * d = (g * g) * (r⁻¹ * d) := by group
        _ = (g * g) * (d * r⁻¹) := by rw [h2]
        _ = ((g * g) * d) * r⁻¹ := by group
        _ = (d * (g * g)) * r⁻¹ := by rw [h1]
        _ = d * ((g * g) * r⁻¹) := by group
    rw [hcr]
    exact hy.R.mul_mem (hy.zpowers_le_R hcz) hr
  set gH : ↥(H z) := ⟨g, hg⟩ with hgH
  set τ := conjVA z gH with hτ
  have hfix : τ (pi z ⟨g * g, hg2⟩) = pi z ⟨g * g, hg2⟩ := by
    rw [hτ, conjVA_pi_eq_iff hy.hA1]
    change g * (g * g) * g⁻¹ * (g * g)⁻¹ ∈ zpowers z
    have e : g * (g * g) * g⁻¹ * (g * g)⁻¹ = 1 := by group
    rw [e]
    exact Subgroup.one_mem _
  obtain ⟨wb, hwb, hvw⟩ := hfree _ (pi_mem_imV hg2R) hfix
  obtain ⟨w, hwR, rfl⟩ := mem_imV.mp hwb
  refine ⟨w, hwR, ?_⟩
  have hginv : g⁻¹ * (w : G) * g⁻¹⁻¹ ∈ J z := conj_mem_J ((H z).inv_mem hg) w.2
  have hprod : (g * w) * (g * w) = (g * g) * (g⁻¹ * w * g⁻¹⁻¹) * w := by group
  have hmemJ : (g * g) * (g⁻¹ * w * g⁻¹⁻¹) * w ∈ J z :=
    (J z).mul_mem ((J z).mul_mem hg2 hginv) w.2
  rw [hprod]
  rw [← pi_eq_one_iff hy.hA1 (a := ⟨_, hmemJ⟩)]
  have e1 : (⟨(g * g) * (g⁻¹ * w * g⁻¹⁻¹) * w, hmemJ⟩ : J z) =
      ⟨g * g, hg2⟩ * ⟨g⁻¹ * w * g⁻¹⁻¹, hginv⟩ * w := rfl
  have e2 : pi z ⟨g⁻¹ * w * g⁻¹⁻¹, hginv⟩ = τ (pi z w) := by
    have h1 : conjVA z gH⁻¹ (pi z w) = pi z ⟨g⁻¹ * w * g⁻¹⁻¹, hginv⟩ := conjVA_pi gH⁻¹ w
    have h2 : gH⁻¹ = gH * (gH * gH)⁻¹ := by group
    have hJ2 : ((gH * gH)⁻¹ : ↥(H z)) ∈ (J z).subgroupOf (H z) := by
      rw [Subgroup.mem_subgroupOf]
      exact (J z).inv_mem hg2
    rw [← h1, h2, map_mul, MulAut.mul_apply,
      conjVA_apply_of_mem_J hy.hA1 (Subgroup.mem_subgroupOf.mp hJ2)]
  rw [e1, map_mul, map_mul, e2, hvw]
  calc τ (pi z w) * pi z w * τ (pi z w) * pi z w
      = (τ (pi z w) * τ (pi z w)) * (pi z w * pi z w) := by
        rw [V_comm hy.hA1 (τ (pi z w) * pi z w) (τ (pi z w)), mul_assoc, mul_assoc, mul_assoc]
    _ = 1 := by rw [V_sq hy.hA1, V_sq hy.hA1, one_mul]

end Hyp

section Lift2

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientDataPSp (z := z) hN)

theorem exists_c1 (hy : Hyp z ((s1HP D : ↥(H z)) : G) ((s2HP D : ↥(H z)) : G))
    (hJ0 : H z ≤ Subgroup.normalizer (CJ z ((s1HP D : ↥(H z)) : G) : Set G))
    (hus1 : ((uHP D : ↥(H z)) : G) * ((s1HP D : ↥(H z)) : G) * ((uHP D : ↥(H z)) : G)⁻¹ =
      ((s2HP D : ↥(H z)) : G)) :
    ∃ u₁ t₁ c₁ : G, ∃ hc₁ : c₁ ∈ H z, u₁ ∈ H z ∧ t₁ ∈ H z ∧
      ((uHP D : ↥(H z)) : G)⁻¹ * u₁ ∈ J z ∧ ((tHP D : ↥(H z)) : G)⁻¹ * t₁ ∈ J z ∧
      (u₁ * t₁)⁻¹ * c₁ ∈ hy.R ∧
      u₁ * ((s1HP D : ↥(H z)) : G) * u₁⁻¹ = ((s2HP D : ↥(H z)) : G) ∧
      u₁ * ((s2HP D : ↥(H z)) : G) * u₁⁻¹ = ((s1HP D : ↥(H z)) : G) ∧
      t₁ * ((s1HP D : ↥(H z)) : G) = ((s1HP D : ↥(H z)) : G) * t₁ ∧
      t₁ * ((s2HP D : ↥(H z)) : G) = ((s2HP D : ↥(H z)) : G) * t₁ ∧
      (∀ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹), u₁ * c = c * u₁) ∧
      (∀ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹), t₁ * c = c * t₁) ∧
      (∀ c ∈ CJ z (((s1HP D : ↥(H z)) : G) * ((s2HP D : ↥(H z)) : G)⁻¹), c₁ * c = c * c₁) ∧
      t₁ * t₁ ∈ zpowers z ∧ u₁ * u₁ ∈ J z ∧ u₁ * t₁ * u₁⁻¹ * t₁⁻¹ ∈ J z ∧
      c₁ * c₁ ∈ zpowers z ∧ (∀ a : G, a ∈ hy.R ↔ c₁ * a * c₁⁻¹ ∈ hy.R) ∧
      (∀ v ∈ imV z hy.R, conjVA z (⟨c₁, hc₁⟩ : ↥(H z)) v = v →
        ∃ w ∈ imV z hy.R, v = conjVA z (⟨c₁, hc₁⟩ : ↥(H z)) w * w) := by
  set s1 : G := ((s1HP D : ↥(H z)) : G) with hs1
  set s2 : G := ((s2HP D : ↥(H z)) : G) with hs2
  obtain ⟨u₁, hu₁H, hu₁J, hus1', hus2', huJ0⟩ := exists_u1 D hy hJ0 hus1
  obtain ⟨t₁, ht₁H, ht₁J, hts1, hts2, htJ0, ht2⟩ := exists_t1 D hy
  obtain ⟨hu₁2, hut, hg2⟩ := sq_mem_J_and_comm_mem_J D hu₁H ht₁H hu₁J ht₁J
  have huC := hy.commute_of_mem_CJs_of_swap hu₁H hus1' hus2' huJ0 hu₁2
  have htC := hy.commute_of_mem_CJs_of_t1 ht₁H hts1 hts2 htJ0 ht2
  have hts := Hyp.commute_s_of_t1 hts1 hts2
  set g := u₁ * t₁ with hg
  have hgH : g ∈ H z := (H z).mul_mem hu₁H ht₁H
  have hgs : g * (s1 * s2⁻¹) * g⁻¹ = (s1 * s2⁻¹)⁻¹ := by
    have hc : s2 * s1⁻¹ = (s1 * s2⁻¹)⁻¹ := by group
    calc g * (s1 * s2⁻¹) * g⁻¹ = u₁ * (t₁ * (s1 * s2⁻¹)) * t₁⁻¹ * u₁⁻¹ := by rw [hg]; group
      _ = u₁ * ((s1 * s2⁻¹) * t₁) * t₁⁻¹ * u₁⁻¹ := by rw [hts]
      _ = (u₁ * s1 * u₁⁻¹) * (u₁ * s2 * u₁⁻¹)⁻¹ := by group
      _ = (s1 * s2⁻¹)⁻¹ := by rw [hus1', hus2', hc]
  have hgC : ∀ c ∈ CJ z (s1 * s2⁻¹), g * c = c * g := by
    intro c hc
    calc g * c = u₁ * (t₁ * c) := by rw [hg]; group
      _ = u₁ * (c * t₁) := by rw [htC c hc]
      _ = (u₁ * c) * t₁ := by group
      _ = (c * u₁) * t₁ := by rw [huC c hc]
      _ = c * g := by rw [hg]; group
  have hfree := hy.free_of_inv hgH hgs hg2
  obtain ⟨w, hwR, hw2⟩ := hy.exists_mul_sq_mem_zpowers hgH hgC hg2 hfree
  have hwJ : w ∈ J z := hy.R_le_J hwR
  have hc₁H : g * w ∈ H z := (H z).mul_mem hgH (J_le_H hwJ)
  refine ⟨u₁, t₁, g * w, hc₁H, hu₁H, ht₁H, hu₁J, ht₁J, ?_, hus1', hus2', hts1, hts2, huC, htC,
    ?_, ht2, hu₁2, hut, hw2, ?_, ?_⟩
  · have e : (u₁ * t₁)⁻¹ * (g * w) = w := by rw [hg]; group
    rw [e]
    exact hwR
  · intro c hc
    have hwc : w * c = c * w := (hy.commute_CJs_R c hc w hwR).symm
    calc g * w * c = g * (w * c) := by group
      _ = g * (c * w) := by rw [hwc]
      _ = (g * c) * w := by group
      _ = (c * g) * w := by rw [hgC c hc]
      _ = c * (g * w) := by group
  · intro a
    have hgR := mem_commutator_conj_iff_of_inv hgH hgs
    constructor
    · intro ha
      have h1 : w * a * w⁻¹ ∈ hy.R := hy.R.mul_mem (hy.R.mul_mem hwR ha) (hy.R.inv_mem hwR)
      have h2 := (hgR _).mp h1
      have e : g * w * a * (g * w)⁻¹ = g * (w * a * w⁻¹) * g⁻¹ := by group
      rw [e]
      exact h2
    · intro ha
      have e : g * w * a * (g * w)⁻¹ = g * (w * a * w⁻¹) * g⁻¹ := by group
      rw [e] at ha
      have h1 := (hgR _).mpr ha
      have e2 : a = w⁻¹ * (w * a * w⁻¹) * w := by group
      rw [e2]
      exact hy.R.mul_mem (hy.R.mul_mem (hy.R.inv_mem hwR) h1) hwR
  · have hact : ∀ v, conjVA z (⟨g * w, hc₁H⟩ : ↥(H z)) v = conjVA z (⟨g, hgH⟩ : ↥(H z)) v := by
      intro v
      have e : (⟨g * w, hc₁H⟩ : ↥(H z)) = ⟨g, hgH⟩ * ⟨w, J_le_H hwJ⟩ := rfl
      rw [e, map_mul, MulAut.mul_apply, conjVA_apply_of_mem_J hy.hA1 (g := ⟨w, J_le_H hwJ⟩) hwJ]
    intro v hv hfix
    rw [hact] at hfix
    obtain ⟨w', hw', hvw'⟩ := hfree v hv hfix
    exact ⟨w', hw', by rw [hact]; exact hvw'⟩

end Lift2


end CFSG.RankThree.GF2n.Parrott.A1Section2Local

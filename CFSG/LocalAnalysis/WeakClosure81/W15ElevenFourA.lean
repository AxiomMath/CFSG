module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeA
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeC
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ R X : Subgroup G} {p : ℕ} {v : G}

theorem inf_centralizer_kHull15_eq_bot
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) (hRP : R ≤ P) :
    V ⊓ centralizer (kHull15 V₀ H : Set G) = ⊥ := by
  by_contra hne
  have hRK : R ≤ normalizer (kHull15 V₀ H : Set G) :=
    hRP.trans (c.hyp.sylow.le.trans (Hyp1510.le_normalizer_kHull15 V₀ H))
  have h6 := c.cex.hyp.h6
  have hRV : R ≤ normalizer (V : Set G) := by
    rw [h6.normalizer_eq]
    exact hR.le.trans (cTilde_le_M M V₀ V)
  have hRW : R ≤ normalizer ((V ⊓ centralizer (kHull15 V₀ H : Set G) : Subgroup G) : Set G) :=
    (le_inf hRV (le_normalizer_centralizer_of_le_normalizer hRK)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hW2 : IsPGroup 2 ↥(V ⊓ centralizer (kHull15 V₀ H : Set G)) :=
    c.cex.hyp.isPGroup.to_le inf_le_left
  have hfix := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot
    Nat.prime_two hR.isPGroup hW2 hne hRW
  apply hfix
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨hyV, hyK⟩, hyR⟩ := hy
  have hCeven : ¬ F11.CTilde M V₀ V ≤ centralizer (V : Set G) := by
    obtain ⟨a, ha, haV⟩ := c.cex.hyp.exists_cTilde_not_le
    exact fun h => haV (h ha)
  have hyV₀ : y ∈ V₀ :=
    fourteen_four h6.elemAbelian h6.normalizer_eq.ge h6.le_normalizer₀ h6.le
      (h6.conjGenerated c.cex.hyp.ne_bot) hCeven hR ⟨hyV, hyR⟩
  have := hX.inf_centralizer_kHull15 c
  have hy1 : y ∈ V₀ ⊓ centralizer (kHull15 V₀ H : Set G) := ⟨hyV₀, hyK⟩
  rw [this] at hy1
  exact hy1

theorem card_eq_pow_three
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hCV : V ⊓ centralizer (kHull15 V₀ H : Set G) = ⊥) : Nat.card ↥X = p ^ 3 := by
  haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hcardX : Nat.card ↥X = (iHull15 V₀ U H).relIndex Q₀ := by
    rw [nat_card_eq_of_complement hX.le hX.inf_eq hX.sup_eq, Subgroup.relIndex,
      Subgroup.index_eq_card]
  rcases c.relIndex_eq with h | h
  swap
  · rw [hcardX, h]
  exfalso
  have hcardp : Nat.card ↥X = p := hcardX.trans h
  haveI : IsCyclic ↥X := isCyclic_of_prime_card hcardp
  obtain ⟨⟨x, hxX⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥X)
  have hx : x ^ p = 1 := by
    have h1 := congrArg Subtype.val
      (pow_card_eq_one' (G := ↥X) (x := (⟨x, hxX⟩ : ↥X)))
    rw [hcardp] at h1
    simpa using h1
  have hx1 : x ≠ 1 := by
    intro h1
    obtain ⟨⟨z, hzX⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (hX.ne_bot c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨z, hzX⟩)
    apply hz1
    have h2 := congrArg Subtype.val hk
    subst h1
    simpa using h2.symm
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hXz : ∀ z ∈ X, ∃ k : ℤ, x ^ k = z := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨z, hz⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hv2 : v * v = 1 := hX.mul_self c
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hvX : v * x * v⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hX.normalizes x).1 hxX
  obtain ⟨a, ha⟩ := hXz _ hvX
  have hinv : v * x * v⁻¹ = x⁻¹ := by
    have h1 : x ^ (a * a - 1) = 1 := by
      have h2 : v * (v * x * v⁻¹) * v⁻¹ = x := by
        rw [hvinv]
        calc v * (v * x * v) * v = (v * v) * x * (v * v) := by group
          _ = x := by rw [hv2]; group
      have h3 : v * (v * x * v⁻¹) * v⁻¹ = x ^ (a * a) := by
        rw [← ha, show v * x ^ a * v⁻¹ = (v * x * v⁻¹) ^ a from (conj_zpow).symm, ← ha,
          ← zpow_mul]
      rw [zpow_sub, zpow_one, ← h3, h2, mul_inv_cancel]
    have h4 : (p : ℤ) ∣ (a - 1) * (a + 1) := by
      have := orderOf_dvd_iff_zpow_eq_one.2 h1
      rw [hord] at this
      have h8 : (a - 1) * (a + 1) = a * a - 1 := by ring
      rw [h8]
      exact this
    rcases (Nat.prime_iff_prime_int.mp c.prime).dvd_or_dvd h4 with h5 | h5
    · exfalso
      have h6 : x ^ (a - 1) = 1 := by
        apply orderOf_dvd_iff_zpow_eq_one.1
        rw [hord]
        exact h5
      have h7 : v * x * v⁻¹ = x := by
        rw [← ha]
        rw [zpow_sub, zpow_one, mul_inv_eq_one] at h6
        exact h6
      have hcomm : ⁅X, zpowers v⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        obtain ⟨k, rfl⟩ := hXz z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have hxv : Commute x v := (mul_inv_eq_iff_eq_mul.1 h7).symm
        exact ((hxv.zpow_zpow k m).symm).eq
      exact hX.ne_bot c (by rw [← hX.comm_eq, hcomm])
    · rw [← ha]
      have h6 : x ^ (a + 1) = 1 := by
        apply orderOf_dvd_iff_zpow_eq_one.1
        rw [hord]
        exact h5
      rw [zpow_add, zpow_one, mul_eq_one_iff_eq_inv] at h6
      exact h6
  have hI : IsElemAbelian 2 (iHull15 V₀ U H) :=
    B2F.isElemAbelian_mono (Hyp1510.iHull15_le_zSub15 V₀ U H)
      (c.hyp.fam.isElemAbelian_zSub15 c.cex)
  have hIN := Hyp1510.le_normalizer_iHull15 V₀ U H
  have hxN : x ∈ normalizer (iHull15 V₀ U H : Set G) := hIN (hX.le_H c hxX)
  have hvN : v ∈ normalizer (iHull15 V₀ U H : Set G) := hIN (c.hyp.V₀_le_H hX.mem)
  have hcx : iHull15 V₀ U H ⊓ centralizer ({x} : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hX.cent]
    refine inf_le_inf_left _ ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨k, rfl⟩ := hXz z hz
    have hxy : Commute x y := hy x rfl
    exact (hxy.zpow_left k).eq
  have hfree := inf_centralizer_le_commutator_of_inv hI c.prime c.p_ne_two hx hxN hvN hv2 hinv hcx
  rw [hX.commutator_eq] at hfree
  apply c.cex.ne_bot
  rw [eq_bot_iff]
  intro u hu
  have hCI : cSub15 M V₀ V U H P ≤ normalizer (iHull15 V₀ U H : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer (iHull15 V₀ U H : Set G)
      (Subgroup.centralizer_le (Hyp1510.iHull15_le_kHull15 V₀ U H)
        (cSub15_le_centralizer M V₀ V U H P hy))
  have huQ : u ∈ qSub15 M V₀ V U H P := c.U_le_qSub15 hu
  rw [c.qSub15_eq_sup hX] at huQ
  have huQ' : u ∈ (iHull15 V₀ U H : Set G) * (cSub15 M V₀ V U H P : Set G) :=
    (Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCI) ▸ huQ
  obtain ⟨i, hi, c₀, hc₀, hic'⟩ := huQ'
  have hic : i * c₀ = u := hic'
  have hvV : v ∈ V := c.cex.hyp.h6.le hX.mem
  have huv : u * v = v * u :=
    B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.le hu) hvV
  have hc₀v : v * c₀ = c₀ * v :=
    Subgroup.mem_centralizer_iff.1 (cSub15_le_centralizer M V₀ V U H P hc₀) v
      (Hyp1510.V₀_le_kHull15 V₀ H hX.mem)
  have hiv : i * v = v * i := by
    have h1 : i * v * c₀ = v * i * c₀ := by
      calc i * v * c₀ = i * (v * c₀) := by rw [mul_assoc]
        _ = i * (c₀ * v) := by rw [hc₀v]
        _ = (i * c₀) * v := by rw [mul_assoc]
        _ = u * v := by rw [hic]
        _ = v * u := huv
        _ = v * (i * c₀) := by rw [hic]
        _ = v * i * c₀ := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hiC : i ∈ iHull15 V₀ U H ⊓ centralizer ({v} : Set G) :=
    ⟨hi, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hiv.symm⟩
  have hiV₁ : i ∈ v1Sub15 V₀ U := hfree hiC
  have hiV : i ∈ V := c.cex.hyp.h6.le (v1Sub15_le_left V₀ U hiV₁)
  have hc₀eq : c₀ = i⁻¹ * u := eq_inv_mul_of_mul_eq hic
  have hc₀V : c₀ ∈ V := by
    rw [hc₀eq]
    exact V.mul_mem (V.inv_mem hiV) (c.cex.le hu)
  have hc₀1 : c₀ = 1 := by
    have : c₀ ∈ V ⊓ centralizer (kHull15 V₀ H : Set G) :=
      ⟨hc₀V, cSub15_le_centralizer M V₀ V U H P hc₀⟩
    rw [hCV] at this
    exact this
  have hui : u = i := by rw [← hic, hc₀1, mul_one]
  have hmem : u ∈ U ⊓ V₀ := ⟨hu, hui ▸ v1Sub15_le_left V₀ U hiV₁⟩
  rw [c.cex.inf_eq_bot] at hmem
  exact hmem

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81

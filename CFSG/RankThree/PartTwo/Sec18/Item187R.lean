module

import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

private abbrev r187Comm (H : Subgroup G) (c : G) : Subgroup G :=
  ⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆

private theorem r187_conj_pCore {H : Subgroup G} {x q : G} (hx : x ∈ H)
    (hq : q ∈ CFSG.Open.pCoreOf 2 H) : x * q * x⁻¹ ∈ CFSG.Open.pCoreOf 2 H :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hx) q).mp hq

private theorem r187_mem_normalizer {R : Subgroup G} {g : G}
    (h1 : ∀ x ∈ R, g * x * g⁻¹ ∈ R) (h2 : ∀ x ∈ R, g⁻¹ * x * g⁻¹⁻¹ ∈ R) :
    g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have h := h2 _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

private theorem r187_conj_mem {X Y : Subgroup G} {g : G}
    (h : ∀ q ∈ X, ∀ z ∈ Y, g * ⁅q, z⁆ * g⁻¹ ∈ ⁅X, Y⁆) :
    ∀ x ∈ ⁅X, Y⁆, g * x * g⁻¹ ∈ ⁅X, Y⁆ := by
  have hle : ⁅X, Y⁆ ≤ ⁅X, Y⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro q hq z hz
    exact h q hq z hz
  intro x hx
  exact hle hx

private def r187Central (H : Subgroup G) (c : G) : Subgroup G where
  carrier := {x | x ∈ H ∧ x * c * x⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 H}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have e : a * b * c * (a * b)⁻¹ * c⁻¹ =
        (a * (b * c * b⁻¹ * c⁻¹) * a⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 H).mul_mem (r187_conj_pCore ha hb') ha'
  one_mem' := ⟨H.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, ?_⟩
    have e : a⁻¹ * c * a⁻¹⁻¹ * c⁻¹ = a⁻¹ * (a * c * a⁻¹ * c⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact r187_conj_pCore (H.inv_mem ha) ((CFSG.Open.pCoreOf 2 H).inv_mem ha')

private theorem mem_r187Central {H : Subgroup G} {c x : G} :
    x ∈ r187Central H c ↔ x ∈ H ∧ x * c * x⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 H :=
  Iff.rfl

private def r187Test (H : Subgroup G) (c : G)
    (hN : H ≤ Subgroup.normalizer (r187Comm H c : Set G)) : Subgroup G where
  carrier := {x | x ∈ H ∧ ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ r187Comm H c}
  mul_mem' := by
    rintro x y ⟨hx, hxz⟩ ⟨hy, hyz⟩
    refine ⟨H.mul_mem hx hy, fun z hz => ?_⟩
    have e : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (r187Comm H c).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hN hx) _).mp (hyz z hz)) (hxz z hz)
  one_mem' := by
    refine ⟨H.one_mem, fun z _ => ?_⟩
    rw [commutatorElement_one_left]
    exact (r187Comm H c).one_mem
  inv_mem' := by
    rintro x ⟨hx, hxz⟩
    refine ⟨H.inv_mem hx, fun z hz => ?_⟩
    have e : ⁅x⁻¹, z⁆ = x⁻¹ * ⁅x, z⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hN (H.inv_mem hx)) _).mp
      ((r187Comm H c).inv_mem (hxz z hz))

private theorem mem_r187Test {H : Subgroup G} {c x : G}
    {hN : H ≤ Subgroup.normalizer (r187Comm H c : Set G)} :
    x ∈ r187Test H c hN ↔ x ∈ H ∧ ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ r187Comm H c :=
  Iff.rfl

private theorem r187_A_le (hH : Sec18H G A M H c) : A ≤ H :=
  (le_sup_right.trans le_sup_left :
      A ≤ inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M)).trans
    (le_of_eq hH.mem_scriptH.2.1.symm)

section Certified


theorem commutator_mem_pCoreOf (h1812 : Item181_2) (hH : Sec18H G A M H c) {h : G}
    (hh : h ∈ H) : h * c * h⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcA, hcL⟩ := mem_and_commutator_mem_of_sec18H hH
  have hAH : A ≤ H := r187_A_le hH
  have hcH : c ∈ H := hAH hcA
  have hLH : inSubgroup perfectResidual H ≤ H := Subgroup.map_subtype_le _
  have hOL : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ CFSG.Open.pCoreOf 2 H := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLH) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (CFSG.RankThree.PartTwo.Sec18.le_normalizer_inSubgroup_perfectResidual H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hLc : ∀ x ∈ inSubgroup perfectResidual H, x * c * x⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 H := by
    intro x hx
    have e : x * c * x⁻¹ * c⁻¹ = (c * x * c⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact hOL (inv_mem (hcL x hx))
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val
      ((isE27_of_mem_partTwoE hH.mem_partTwoE).1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hHK : H ≤ r187Central H c := by
    have hdec : H ≤ inSubgroup perfectResidual H ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) :=
      le_of_eq hH.mem_scriptH.2.1
    refine hdec.trans (sup_le (sup_le ?_ ?_) ?_)
    · intro x hx
      exact mem_r187Central.mpr ⟨hLH hx, hLc x hx⟩
    · intro a ha
      refine mem_r187Central.mpr ⟨hAH ha, ?_⟩
      have e : a * c * a⁻¹ * c⁻¹ = 1 := by rw [hAcomm a ha c hcA]; group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 H).one_mem
    · obtain ⟨s, hsC, hSdecomp, -⟩ := h1812 G A M hH.toSec18Std H hH.mem_scriptH
      obtain ⟨hsS, hsCent, -⟩ := hsC
      have hsH : s ∈ H := ((CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left) hsS
      have hcs : c * s = s * c := Subgroup.mem_centralizer_iff.mp hsCent c hcA
      rw [hSdecomp]
      refine sup_le (Subgroup.zpowers_le.mpr (mem_r187Central.mpr ⟨hsH, ?_⟩)) ?_
      · have e : s * c * s⁻¹ * c⁻¹ = 1 := by rw [← hcs]; group
        rw [e]
        exact (CFSG.Open.pCoreOf 2 H).one_mem
      · intro q hq
        refine mem_r187Central.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hq, ?_⟩
        have e : q * c * q⁻¹ * c⁻¹ = q * (c * q⁻¹ * c⁻¹) := by group
        rw [e]
        exact (CFSG.Open.pCoreOf 2 H).mul_mem hq
          (r187_conj_pCore hcH ((CFSG.Open.pCoreOf 2 H).inv_mem hq))
  exact (mem_r187Central.mp (hHK hh)).2

theorem le_normalizer_commutator (h1812 : Item181_2) (hH : Sec18H G A M H c) :
    H ≤ Subgroup.normalizer ((⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAH : A ≤ H := r187_A_le hH
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hcH : c ∈ H := hAH hcA
  have hc3 : c ^ 3 = 1 := pow_three_eq_one_of_sec18H hH
  by_cases hc1 : c = 1
  · rw [hc1, Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro g
    simp
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hCH : Subgroup.zpowers c ≤ H := Subgroup.zpowers_le.mpr hcH
  have hHN : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hCN : Subgroup.zpowers c ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    hCH.trans hHN
  have hQR : ∀ y ∈ CFSG.Open.pCoreOf 2 H, ∀ x ∈ r187Comm H c, y * x * y⁻¹ ∈ r187Comm H c := by
    intro y hy
    apply r187_conj_mem
    intro q hq z hz
    have e : y * ⁅q, z⁆ * y⁻¹ = ⁅y * q, z⁆ * ⁅y, z⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (r187Comm H c).mul_mem
      (Subgroup.commutator_mem_commutator ((CFSG.Open.pCoreOf 2 H).mul_mem hy hq) hz)
      ((r187Comm H c).inv_mem (Subgroup.commutator_mem_commutator hy hz))
  have hCQR : ∀ z ∈ Subgroup.zpowers c, ∀ x ∈ r187Comm H c, z * x * z⁻¹ ∈ r187Comm H c := by
    intro z hz
    apply r187_conj_mem
    intro q hq w hw
    have hzw : Commute z w := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact Commute.zpow_zpow_self c m n
    have h1 : z * w * z⁻¹ = w := by rw [hzw.eq, mul_inv_cancel_right]
    have e : z * ⁅q, w⁆ * z⁻¹ = ⁅z * q * z⁻¹, z * w * z⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, h1]
    exact Subgroup.commutator_mem_commutator (r187_conj_pCore (hCH hz) hq) hw
  have hDN : CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c ≤
      Subgroup.normalizer (r187Comm H c : Set G) := by
    refine sup_le ?_ ?_
    · intro y hy
      exact r187_mem_normalizer (hQR y hy) (hQR y⁻¹ (inv_mem hy))
    · intro z hz
      exact r187_mem_normalizer (hCQR z hz) (hCQR z⁻¹ (inv_mem hz))
  have hDQ : CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) :=
    sup_le Subgroup.le_normalizer hCN
  obtain ⟨k₂, hk₂⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).exists_card_eq
  have hcard_inter : Nat.card (Subgroup.zpowers c ⊓ CFSG.Open.pCoreOf 2 H : Subgroup G) = 1 := by
    have h3 : Nat.card (Subgroup.zpowers c ⊓ CFSG.Open.pCoreOf 2 H : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_left : Subgroup.zpowers c ⊓ CFSG.Open.pCoreOf 2 H ≤ Subgroup.zpowers c)
      rwa [Nat.card_zpowers, hord] at this
    have h2 : Nat.card (Subgroup.zpowers c ⊓ CFSG.Open.pCoreOf 2 H : Subgroup G) ∣ 2 ^ k₂ := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.zpowers c ⊓ CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 H)
      rwa [hk₂] at this
    have hcop : Nat.Coprime 3 (2 ^ k₂) := Nat.Coprime.pow_right k₂ (by norm_num)
    have hg := Nat.dvd_gcd h3 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    exact Nat.dvd_one.mp hg
  have hCcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hord]
  have hDcard : Nat.card (CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c : Subgroup G) =
      3 * Nat.card (CFSG.Open.pCoreOf 2 H) := by
    have hprod := Sec6.card_sup_mul_card_inf hCN
    rw [hcard_inter, hCcard, mul_one, sup_comm] at hprod
    exact hprod
  have hsyl : ∀ x ∈ CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c, x ^ 3 = 1 → x ≠ 1 →
      CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers x)
        (CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c) := by
    intro x hxD hx3 hx1
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨Subgroup.zpowers_le.mpr hxD, IsPGroup.of_card (n := 1) ?_, ?_⟩
    · rw [Nat.card_zpowers, hxord, pow_one]
    · have hrel := Subgroup.relIndex_mul_card (H := Subgroup.zpowers x)
        (K := CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c)
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxD), Nat.card_zpowers, hxord, hDcard] at hrel
      have hrel' : (Subgroup.zpowers x).relIndex (CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c) =
          Nat.card (CFSG.Open.pCoreOf 2 H) := by omega
      rw [hrel', hk₂]
      intro h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      norm_num at this
  have hcD : c ∈ CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hstep : ∀ h ∈ H, ∀ x ∈ r187Comm H c, h * x * h⁻¹ ∈ r187Comm H c := by
    intro h hh
    have hc'D : h * c * h⁻¹ ∈ CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c := by
      have e : h * c * h⁻¹ = (h * c * h⁻¹ * c⁻¹) * c := by group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 H ⊔ Subgroup.zpowers c).mul_mem
        (Subgroup.mem_sup_left (commutator_mem_pCoreOf h1812 hH hh)) hcD
    have hc'3 : (h * c * h⁻¹) ^ 3 = 1 := by rw [conj_pow, hc3, mul_one, mul_inv_cancel]
    have hc'1 : h * c * h⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      calc c = h⁻¹ * (h * c * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨k, hkD, hk⟩ :=
      (hsyl c hcD hc3 hc1).exists_mem_conj (hsyl _ hc'D hc'3 hc'1)
    have hkR : k ∈ Subgroup.normalizer (r187Comm H c : Set G) := hDN hkD
    have hkQ : k ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) := hDQ hkD
    apply r187_conj_mem
    intro q hq z hz
    have hX : k⁻¹ * (h * q * h⁻¹) * k ∈ CFSG.Open.pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff''.mp hkQ (h * q * h⁻¹)).mp (r187_conj_pCore hh hq)
    have hzc : h * z * h⁻¹ ∈ Subgroup.zpowers (h * c * h⁻¹) := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [conj_zpow]⟩
    have hY : k⁻¹ * (h * z * h⁻¹) * k ∈ Subgroup.zpowers c := (hk _).mp hzc
    have hmem := (Subgroup.mem_normalizer_iff.mp hkR
      (⁅k⁻¹ * (h * q * h⁻¹) * k, k⁻¹ * (h * z * h⁻¹) * k⁆)).mp
      (Subgroup.commutator_mem_commutator hX hY)
    have e : h * ⁅q, z⁆ * h⁻¹ =
        k * ⁅k⁻¹ * (h * q * h⁻¹) * k, k⁻¹ * (h * z * h⁻¹) * k⁆ * k⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact hmem
  intro h hh
  exact r187_mem_normalizer (hstep h hh) (hstep h⁻¹ (inv_mem hh))

theorem commutator_pCoreOf_inf_eq (h1812 : Item181_2) (hH : Sec18H G A M H c) :
    ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ =
      ⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hAH : A ≤ H := r187_A_le hH
  have hcH : c ∈ H := hAH hcA
  obtain ⟨s, hsC, hSdecomp, -⟩ := h1812 G A M hH.toSec18Std H hH.mem_scriptH
  obtain ⟨hsS, hsCent, -⟩ := hsC
  have hsH : s ∈ H := ((CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left) hsS
  have hcs : c * s = s * c := Subgroup.mem_centralizer_iff.mp hsCent c hcA
  have hQS : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
    rw [hSdecomp]
    exact le_sup_right
  have hN := le_normalizer_commutator h1812 hH
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx z hz
    have hST : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ r187Test H c hN := by
      rw [hSdecomp]
      refine sup_le (Subgroup.zpowers_le.mpr (mem_r187Test.mpr ⟨hsH, ?_⟩)) ?_
      · intro z' hz'
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
        have hsc : Commute s c := hcs.symm
        have hsz : ⁅s, c ^ m⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hsc.zpow_right m).eq
        rw [hsz]
        exact (r187Comm H c).one_mem
      · intro q hq
        exact mem_r187Test.mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H hq,
          fun z' hz' => Subgroup.commutator_mem_commutator hq hz'⟩
    exact (mem_r187Test.mp (hST hx)).2 z hz
  · exact Subgroup.commutator_mono hQS le_rfl

end Certified

theorem commutator_ne_bot (h184 : Item184_1) (h186 : Item186H) (hH : Sec18H G A M H c)
    (h187 : Hyp187 A M H c) : ⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆ ≠ ⊥ := by
  intro hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcA, -⟩ := mem_and_commutator_mem_of_sec18H hH
  have hcH : c ∈ H := r187_A_le hH hcA
  have hord : orderOf c = 3 := orderOf_eq_three_of_sec18H h184 hH
  have hcC : c ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hmem : ⁅q, c⁆ ∈ ⁅CFSG.Open.pCoreOf 2 H, Subgroup.zpowers c⁆ :=
      Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers c)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  have hF := (h186 G A M H c hH h187).1
  have hcQ : c ∈ CFSG.Open.pCoreOf 2 H :=
    CFSG.RankThree.GF2n.Tim78.inf_centralizer_le_of_generalizedFitting_eq hF ⟨hcH, hcC⟩
  obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨c, hcQ⟩
  have hcn : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h3 : 3 ∣ 2 ^ n := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hcn
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

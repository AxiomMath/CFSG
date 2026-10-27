module

public import CFSG.Quasithin.Background.A1cRankLemmas
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.L3YC

section Defs

variable {G : Type} [Group G]

@[expose] def N0 [Finite G] (L : Subgroup G) : Subgroup G where
  carrier := {n | n ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ x ∈ L, n * x * n⁻¹ * x⁻¹ ∈ pCoreOf 2 L}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, fun x hx => ?_⟩
    have haO : a ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 L haN
    have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp haO _).mp (hb x hx)
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (ha x hx)
  inv_mem' := by
    rintro n ⟨hnN, hn⟩
    refine ⟨Subgroup.inv_mem _ hnN, fun x hx => ?_⟩
    have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnN) x).mp hx
    have h1 := Subgroup.inv_mem _ (hn _ hx')
    have e : n⁻¹ * x * n⁻¹⁻¹ * x⁻¹ =
        (n * (n⁻¹ * x * n⁻¹⁻¹) * n⁻¹ * (n⁻¹ * x * n⁻¹⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact h1

end Defs

section Cyclic

variable {G : Type} [Group G] [Finite G]

theorem exists_central_of_normal {p : ℕ} [Fact p.Prime] {P W : Subgroup G} (hP : IsPGroup p ↥P)
    (hWP : W ≤ P) (hWn : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hne : W ≠ ⊥) :
    ∃ z ∈ W, z ≠ 1 ∧ z ^ p = 1 ∧ ∀ x ∈ P, x * z = z * x := by
  classical
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hWn g g.2 n hn
    simpa using this
  have hsub : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have : (⟨g, hWP hg⟩ : ↥P) ∈ W.subgroupOf P := hg
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hcent := Group.IsNilpotent.inf_center_ne_bot_of_normal hsub
  set C : Subgroup ↥P := W.subgroupOf P ⊓ Subgroup.center ↥P with hC
  have hCp : IsPGroup p ↥C := hP.to_subgroup C
  have hCdvd : p ∣ Nat.card ↥C := by
    rcases hCp.card_eq_or_dvd with h0 | h0
    · exact absurd (Subgroup.card_eq_one.mp h0) hcent
    · exact h0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hCdvd
  refine ⟨((c : ↥P) : G), c.2.1, ?_, ?_, ?_⟩
  · intro h1
    have : c = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hc
    exact (Fact.out : p.Prime).one_lt.ne hc
  · have := pow_orderOf_eq_one c
    rw [hc] at this
    exact congrArg Subtype.val (congrArg Subtype.val this)
  · intro q hq
    have := Subgroup.mem_center_iff.1 c.2.2 ⟨q, hq⟩
    exact congrArg Subtype.val this

theorem exists_commuting_order_three {L E : Subgroup G} (hE3 : IsPGroup 3 ↥E)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hL3 : 3 ∣ Nat.card ↥L) :
    ∃ x ∈ L, orderOf x = 3 ∧ ∀ e ∈ E, e * x = x * e := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXN : L ⊔ E ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hEL
  have hnormal : (L.subgroupOf (L ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hXN
  obtain ⟨S, hS, hES⟩ := exists_isSylowIn_ge 3 (le_sup_right : E ≤ L ⊔ E) hE3
  have hSL : IsSylowIn 3 (S ⊓ L) L := hS.inf_normal le_sup_left hnormal
  have hcard := hSL.card_eq
  have hne : S ⊓ L ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card ↥L).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hL3
    have : 3 ^ (Nat.card ↥L).factorization 3 = 1 := hcard.symm
    have h2 : 3 ≤ 3 ^ (Nat.card ↥L).factorization 3 := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  obtain ⟨z, hzW, hz1, hz3, hzS⟩ := exists_central_of_normal (p := 3) hS.isPGroup
    (inf_le_left : S ⊓ L ≤ S)
    (fun x hx w hw => ⟨S.mul_mem (S.mul_mem hx hw.1) (S.inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp (hXN (hS.le hx)) w).mp hw.2⟩) hne
  have hord : orderOf z = 3 := by
    have h1 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  exact ⟨z, hzW.2, hord, fun e he => hzS e (hES he)⟩

theorem cyclic_of_three_subgroup_N0 {L M : Subgroup G} (hev : evenRank G ≤ 2)
    (hM : IsTwoLocal M) (hLM : Subgroup.normalizer (L : Set G) ≤ M) (hL3 : 3 ∣ Nat.card ↥L)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L)
    {P : Subgroup G} (hP : IsPGroup 3 ↥P) (hPN : P ≤ N0 L) : IsCyclic ↥P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnc
  obtain ⟨E, hEP, hE, hEcard⟩ := A1c.exists_isElemAbelian_card_sq (by norm_num : (3 : ℕ) ≠ 2) hP hnc
  have hE3 : IsPGroup 3 ↥E := hP.to_le hEP
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := fun e he => (hPN (hEP he)).1
  obtain ⟨x, hxL, hx3, hxE⟩ := exists_commuting_order_three hE3 hEL hL3
  have hxnE : x ∉ E := by
    intro hx
    have hxO : x ∈ pCoreOf 2 L := hZ x hxL (hPN (hEP hx)).2
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨x, hxO⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers (p := 3) hE hx3
    (fun e he => hxE e he) hxnE
  have hAM : E ⊔ Subgroup.zpowers x ≤ M :=
    sup_le (hEL.trans hLM) (Subgroup.zpowers_le.mpr (hLM (Subgroup.le_normalizer hxL)))
  have h3 : 3 ≤ pRank 3 M :=
    le_pRank Nat.prime_three hAM hA (k := 3) (by rw [hAcard, hEcard]; norm_num)
  have h4 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) M hM
  omega

end Cyclic

end Stellmacher.L3YC

end CFSG.Quasithin

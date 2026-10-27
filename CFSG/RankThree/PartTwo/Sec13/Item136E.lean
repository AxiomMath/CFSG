module

public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec13.Item136Lift

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open scoped commutatorElement

section HeisE

variable {X : Type} [Group X]

theorem mul_pow_three_of_commutator {x y : X} (hx : Commute (x * y * x⁻¹ * y⁻¹) x)
    (hy : Commute (x * y * x⁻¹ * y⁻¹) y) (ht : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  set t := x * y * x⁻¹ * y⁻¹ with htdef
  have e1 : y * x = t⁻¹ * (x * y) := by rw [htdef]; group
  have hx' : ∀ w : X, x * (t⁻¹ * w) = t⁻¹ * (x * w) := fun w => by
    rw [← mul_assoc, ← mul_assoc, (hx.inv_left).eq]
  have hy' : ∀ w : X, y * (t⁻¹ * w) = t⁻¹ * (y * w) := fun w => by
    rw [← mul_assoc, ← mul_assoc, (hy.inv_left).eq]
  have e1' : ∀ w : X, y * (x * w) = t⁻¹ * (x * (y * w)) := fun w => by
    rw [← mul_assoc, e1, mul_assoc, mul_assoc]
  have h3 : (x * y) ^ 3 = x * (y * (x * (y * (x * y)))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h4 : x ^ 3 * y ^ 3 = x * (x * (x * (y * (y * y)))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have ht3 : t⁻¹ * (t⁻¹ * t⁻¹) = 1 := by
    rw [← mul_assoc, ← pow_two, ← pow_succ, inv_pow, ht, inv_one]
  rw [h3, h4]
  calc x * (y * (x * (y * (x * y)))) = x * (t⁻¹ * (x * (y * (y * (x * y))))) := by
        rw [e1']
    _ = t⁻¹ * (x * (x * (y * (y * (x * y))))) := by rw [hx']
    _ = t⁻¹ * (x * (x * (y * (t⁻¹ * (x * (y * y)))))) := by rw [e1' y]
    _ = t⁻¹ * (x * (x * (t⁻¹ * (y * (x * (y * y)))))) := by rw [hy']
    _ = t⁻¹ * (x * (t⁻¹ * (x * (y * (x * (y * y)))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (x * (x * (y * (x * (y * y)))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (x * (x * (t⁻¹ * (x * (y * (y * y))))))) := by rw [e1' (y * y)]
    _ = t⁻¹ * (t⁻¹ * (x * (t⁻¹ * (x * (x * (y * (y * y))))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (t⁻¹ * (x * (x * (x * (y * (y * y))))))) := by rw [hx']
    _ = x * (x * (x * (y * (y * y)))) := by rw [← mul_assoc, ← mul_assoc, mul_assoc t⁻¹ t⁻¹,
          ht3, one_mul]

theorem not_isCyclic_of_nine_le [Finite X] {H : Subgroup X} (hexp : ∀ x ∈ H, x ^ 3 = 1)
    (h9 : 9 ≤ Nat.card H) : ¬ IsCyclic H := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  have hcard : Nat.card H = orderOf g := by
    rw [← Nat.card_zpowers g]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hg).symm
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hexp g g.2)
  have := orderOf_le_of_pow_eq_one (by norm_num) hg3
  omega

theorem exists_elemAbelian_heis [Finite X] {Q Λ Ab U : Subgroup X} {z : X}
    (hΛQ : Λ ≤ Q) (hUQ : U ≤ Q) (hAbQ : Ab ≤ Q) (hQ : Nat.card Q ≤ 9 * Nat.card Λ)
    (hAbΛ : Ab ≤ Subgroup.normalizer (Λ : Set X))
    (hAb : CFSG.Assembly.IsElemAbelian 3 Ab) (hAb27 : Nat.card Ab = 27)
    (hz : z ∈ Ab) (hzΛ : z ∈ Λ) (hzc : ∀ x ∈ Q, z * x = x * z) (hzo : orderOf z = 3)
    (hzU : z ∈ U) (hU9 : 9 ≤ Nat.card U) (hU3 : ∀ x ∈ U, x ^ 3 = 1)
    (hUΛ : ∀ u ∈ U, ∀ l ∈ Λ, u * l = l * u)
    (hUΛz : ∀ u ∈ U, u ∈ Λ → u ∈ Subgroup.zpowers z)
    (hAbU : ∀ a ∈ Ab, ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers z)
    (hAbUz : ∀ a ∈ Ab, a ∈ U → a ∈ Subgroup.zpowers z) :
    (∀ w ∈ Ab ⊔ U, w ^ 3 = 1) ∧
    (∀ a ∈ Ab, ∀ w ∈ Ab ⊔ U, a * w * a⁻¹ * w⁻¹ ∈ Subgroup.zpowers z) ∧
    ∃ E : Subgroup X, E ≤ Ab ⊔ U ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ z ∈ E ∧
      9 ≤ Nat.card (E ⊓ U : Subgroup X) ∧ 9 ≤ Nat.card (E ⊓ Λ : Subgroup X) := by
  have hzQ : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le.mpr (hAbQ hz)
  have hzcen : ∀ w ∈ Subgroup.zpowers z, ∀ x ∈ Q, w * x = x * w := by
    intro w hw x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute z x from hzc x hx) i).eq
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzle : Subgroup.zpowers z ≤ U := Subgroup.zpowers_le.mpr hzU
  have hcardz : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hconjU : ∀ a ∈ Ab, ∀ v ∈ U, a * v * a⁻¹ ∈ U := by
    intro a ha v hv
    have h1 : a * v * a⁻¹ = (a * v * a⁻¹ * v⁻¹) * v := by group
    rw [h1]
    exact U.mul_mem (hzle (hAbU a ha v hv)) hv
  have hUn : Ab ≤ Subgroup.normalizer (U : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hconjU a ha v, fun hv => ?_⟩
    have h1 := hconjU a⁻¹ (Ab.inv_mem ha) _ hv
    simpa [mul_assoc] using h1
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right Ab U hUn
  have hdec : ∀ w ∈ Ab ⊔ U, ∃ b ∈ Ab, ∃ v ∈ U, b * v = w := by
    intro w hw
    have hw' : w ∈ ((Ab ⊔ U : Subgroup X) : Set X) := hw
    rw [hcoe] at hw'
    obtain ⟨b, hb, v, hv, rfl⟩ := Set.mem_mul.mp hw'
    exact ⟨b, hb, v, hv, rfl⟩
  have := hAb.1
  have hAbc : ∀ a ∈ Ab, ∀ b ∈ Ab, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Ab) ⟨b, hb⟩)
  have hcomm : ∀ a ∈ Ab, ∀ w ∈ Ab ⊔ U, a * w * a⁻¹ * w⁻¹ ∈ Subgroup.zpowers z := by
    intro a ha w hw
    obtain ⟨b, hb, v, hv, rfl⟩ := hdec w hw
    have h1 := hAbU a ha v hv
    have hb' : (a * v * a⁻¹ * v⁻¹) * b = b * (a * v * a⁻¹ * v⁻¹) :=
      hzcen _ h1 b (hAbQ hb)
    have : a * (b * v) * a⁻¹ * (b * v)⁻¹ = a * v * a⁻¹ * v⁻¹ := by
      calc a * (b * v) * a⁻¹ * (b * v)⁻¹ = (a * b) * v * a⁻¹ * v⁻¹ * b⁻¹ := by group
        _ = (b * a) * v * a⁻¹ * v⁻¹ * b⁻¹ := by rw [hAbc a ha b hb]
        _ = b * (a * v * a⁻¹ * v⁻¹) * b⁻¹ := by group
        _ = a * v * a⁻¹ * v⁻¹ := by rw [← hb', mul_inv_cancel_right]
    rw [this]
    exact h1
  have hexp : ∀ w ∈ Ab ⊔ U, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨b, hb, v, hv, rfl⟩ := hdec w hw
    have ht := hAbU b hb v hv
    have hbQ := hAbQ hb
    have hvQ := hUQ hv
    rw [mul_pow_three_of_commutator (hzcen _ ht b hbQ) (hzcen _ ht v hvQ) ?_, hAb.2 b hb,
      hU3 v hv, one_mul]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← hi, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz3,
      _root_.one_zpow]
  refine ⟨hexp, hcomm, ?_⟩
  have hAbUcard : 81 ≤ Nat.card (Ab ⊔ U : Subgroup X) := by
    have h1 := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hUn
    have h2 : Nat.card (Ab ⊓ U : Subgroup X) ≤ 3 := by
      rw [← hcardz]
      exact Subgroup.card_le_of_le fun a ha => hAbUz a ha.1 ha.2
    rw [hAb27] at h1
    nlinarith
  have hsupΛ : Ab ⊔ U ≤ Subgroup.normalizer (Λ : Set X) := by
    refine sup_le hAbΛ fun u hu => ?_
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro l hl
    exact (hUΛ u hu l hl).symm
  have hinter : 9 ≤ Nat.card ((Ab ⊔ U) ⊓ Λ : Subgroup X) := by
    have h1 := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hsupΛ
    have h2 : Nat.card ((Ab ⊔ U) ⊔ Λ : Subgroup X) ≤ Nat.card Q :=
      Subgroup.card_le_of_le (sup_le (sup_le hAbQ hUQ) hΛQ)
    have hΛpos : 0 < Nat.card Λ := Nat.card_pos
    nlinarith
  obtain ⟨l, hlΛ, hlz⟩ : ∃ l ∈ (Ab ⊔ U) ⊓ Λ, l ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show (Ab ⊔ U) ⊓ Λ ≤ Subgroup.zpowers z from hne)
    omega
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show U ≤ Subgroup.zpowers z from hne)
    omega
  have hl3 : l ^ 3 = 1 := hexp l hlΛ.1
  have hu3 : u ^ 3 = 1 := hU3 u huU
  have hzl : z * l = l * z := hzc l (hΛQ hlΛ.2)
  have hzu : z * u = u * z := hzc u (hUQ huU)
  have hlu : l * u = u * l := (hUΛ u huU l hlΛ.2).symm
  set D := Subgroup.zpowers z ⊔ Subgroup.zpowers l with hD
  have hDab : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_zpowers_sup hz3 hl3 hzl
  have hD9 : Nat.card D = 9 := Sec4.card_zpowers_sup_zpowers hl3 hzo hlz hzl.symm
  have hDΛ : D ≤ Λ := sup_le (Subgroup.zpowers_le.mpr hzΛ) (Subgroup.zpowers_le.mpr hlΛ.2)
  have hDu : ∀ x ∈ D, ∀ y ∈ Subgroup.zpowers u, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine (Commute.zpow_right ?_ j).eq
    have hxΛ := hDΛ hx
    exact (hUΛ u huU x hxΛ).symm
  set E := D ⊔ Subgroup.zpowers u with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_sup hDab (isElemAbelian_zpowers hu3) hDu
  have hDu0 : D ⊓ Subgroup.zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hxz : x ∈ Subgroup.zpowers z :=
      hUΛz x ((Subgroup.zpowers_le.mpr huU) hx.2) (hDΛ hx.1)
    have hxo : orderOf x = 3 := orderOf_eq_prime ((isElemAbelian_zpowers hu3).2 x hx.2) hx1
    have heq : Subgroup.zpowers x = Subgroup.zpowers u :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx.2) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hxo]
        exact orderOf_le_of_pow_eq_one (by norm_num) hu3)
    apply huz
    have hux : u ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers u
    exact (Subgroup.zpowers_le.mpr hxz) hux
  have hE27 : Nat.card E = 27 := by
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hDu).1
    have huo : orderOf u = 3 := orderOf_eq_prime hu3 (fun h => huz (h ▸ Subgroup.one_mem _))
    rw [hDu0, Subgroup.card_bot, mul_one, hD9, Nat.card_zpowers, huo] at h1
    exact h1
  refine ⟨E, ?_, hEab, hE27, ?_, ?_, ?_⟩
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact (Subgroup.zpowers_le.mpr hz).trans le_sup_left
    · exact Subgroup.zpowers_le.mpr hlΛ.1
    · exact (Subgroup.zpowers_le.mpr huU).trans le_sup_right
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  ·
    have hzu' : u ∉ Subgroup.zpowers z := huz
    have h9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers u : Subgroup X) = 9 :=
      Sec4.card_zpowers_sup_zpowers hu3 hzo hzu' hzu.symm
    rw [← h9]
    refine Subgroup.card_le_of_le (le_inf ?_ ?_)
    · exact sup_le ((le_sup_left : Subgroup.zpowers z ≤ D).trans le_sup_left) le_sup_right
    · exact sup_le hzle (Subgroup.zpowers_le.mpr huU)
  · rw [← hD9]
    exact Subgroup.card_le_of_le (le_inf le_sup_left hDΛ)

end HeisE

section Center

theorem card_center_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) :
    Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have hcenter : ∀ {Y : Type} [Group Y] (e : X ≃* Y),
      Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) := by
    intro Y _ e
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · have hpf : PiField true (ringChar K) n K := ⟨hp, n.2, hnc⟩
    have hq' : ModThree true (ringChar K ^ (n : ℕ)) := by
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    rw [hcenter e]
    exact KFacts.card_center_slPi hpf hq'
  ·
    have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hm
        rw [hm] at hq
        norm_num at hq
      · exact h0
    have hpf : PiField false (ringChar K) m K := ⟨hp, hm1, by
      rw [hK, hm]
      rfl⟩
    have hq' : ModThree false (ringChar K ^ m) := by
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
    rw [hcenter e]
    have h := KFacts.card_center_slPi hpf hq'
    rw [← hm] at h
    exact h

end Center

section Transport

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem mem_thetaQuotCentralizer_of_mk_commute (hL : L ∈ thetaComponentsAt 3 c)
    {g : Subgroup.normalizer (Subgroup.zpowers c : Set G)}
    (hgL : (g : G) ∈ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ l : Subgroup.normalizer (Subgroup.zpowers c : Set G), (l : G) ∈ L →
      QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G))) g * QuotientGroup.mk' _ l =
        QuotientGroup.mk' _ l * QuotientGroup.mk' _ g) :
    (g : G) ∈ Sec4.thetaQuotCentralizer L := by
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hgL, fun l hl => ?_⟩
  have hlN : l ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    le_normalizer_zpowers_of_mem hL hl
  set l₁ : Subgroup.normalizer (Subgroup.zpowers c : Set G) := ⟨l, hlN⟩
  have hx : l₁⁻¹ * (g * l₁ * g⁻¹) ∈
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
      map_inv, map_inv, hcomm l₁ hl]
    group
  have hxN : l⁻¹ * ((g : G) * l * (g : G)⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := ⟨_, hx, rfl⟩
  have hxL : l⁻¹ * ((g : G) * l * (g : G)⁻¹) ∈ L :=
    L.mul_mem (L.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hgL l).mp hl)
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL, inSubgroup_theta_centralizer]
  exact ⟨hxL, Sec6.le_centralizer_of_mem_thetaComponentsAt hL hxL, hxN⟩

theorem mem_zpowers_of_aBarHom_commute (h : Sec13Data G A c L) (a : A)
    (hcomm : ∀ y ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
      aBarHom h a * y = y * aBarHom h a) : (a : G) ∈ Subgroup.zpowers c := by
  have hmem := mem_thetaQuotCentralizer_of_mk_commute h.mem_thetaComponentsAt
    (g := ⟨a, h.A_le_normalizer_zpowers a.2⟩) (h.le_normalizer a.2) (fun l hl => by
      have hlN : (l : _) ∈ (L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl)
      have hy : (⟨QuotientGroup.mk' _ l, Subgroup.mem_map_of_mem _ hlN⟩ : lBarA c L A) ∈
          (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
        Subgroup.mem_subgroupOf.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      exact congrArg Subtype.val (hcomm _ hy))
  obtain ⟨-, hzl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hmem
  have hsc : (a : G) ∈
      Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨a.2, fun x hx => ?_⟩
    have h1 := hzl x hx
    have h2 : (a : G) * x * (a : G)⁻¹ * x⁻¹ = x * (x⁻¹ * ((a : G) * x * (a : G)⁻¹)) * x⁻¹ := by
      group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hx) _).mp h1
  rw [h.sectionCentralizer_eq] at hsc
  exact hsc

end Transport

section Case7

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem isHeisCentral_facts (h : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ U : Subgroup (lBarA c L A), Sec4.IsHeisThree U ∧
      (∀ u ∈ U, ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * v = v * u) ∧
      U ⊔ (Sec12.lBar c L).subgroupOf (lBarA c L A) = ⊤ ∧
      (Subgroup.center U).map U.subtype = U ⊓ (Sec12.lBar c L).subgroupOf (lBarA c L A) := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hZU : (Subgroup.center U).map U.subtype = U ⊓ V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨hwU, hwV⟩
      refine ⟨⟨w, hwU⟩, Subgroup.mem_center_iff.mpr fun u => Subtype.ext ?_, rfl⟩
      exact hcomm u u.2 w hwV
    · rw [hcard, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  let φ : U × V →* lBarA c L A := MonoidHom.noncommCoprod U.subtype V.subtype
    (fun u v => hcomm u u.2 v v.2)
  have hφapp : ∀ y : U × V, φ y = (y.1 : lBarA c L A) * y.2 := fun y => rfl
  have hφ : ∀ x : lBarA c L A, ∃ y : U × V, φ y = x := by
    have hrange : φ.range = ⊤ := by
      rw [eq_top_iff, ← hUV, sup_le_iff]
      constructor
      · intro u hu
        exact ⟨(⟨u, hu⟩, 1), by rw [hφapp]; simp⟩
      · intro v hv
        exact ⟨(1, ⟨v, hv⟩), by rw [hφapp]; simp⟩
    intro x
    exact MonoidHom.mem_range.mp (hrange ▸ Subgroup.mem_top x)
  have hcommV : commutator (lBarA c L A) ≤ V := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨⟨u, v⟩, rfl⟩ := hφ x
    obtain ⟨⟨u', v'⟩, rfl⟩ := hφ y
    rw [← map_commutatorElement, hφapp]
    have h1 : ((⁅(u, v), (u', v')⁆ : U × V).1 : lBarA c L A) ∈ V := by
      have h2 : (⁅u, u'⁆ : U) ∈ commutator U :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hU.1.2.1] at h2
      have h3 : ((⁅u, u'⁆ : U) : lBarA c L A) ∈ (Subgroup.center U).map U.subtype :=
        ⟨_, h2, rfl⟩
      rw [hZU] at h3
      exact h3.2
    exact V.mul_mem h1 (⁅(u, v), (u', v')⁆ : U × V).2.2
  have hΛperf : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar h
  have hΛV : Λ ≤ V := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator (lBarA c L A) := Subgroup.commutator_mono le_top le_top
      _ ≤ V := hcommV
  have hVq : IsQuasisimple V := LocalCores.isQuasisimple_of_mulEquiv eV.symm
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have hΛn : (Λ.subgroupOf V).Normal := (lBar_normal h).subgroupOf V
  have hVΛ : V ≤ Λ := by
    rcases LocalCores.quasisimple_normal_subgroups hVq hΛn with htop | hcen
    · intro v hv
      have : (⟨v, hv⟩ : V) ∈ Λ.subgroupOf V := htop ▸ Subgroup.mem_top _
      exact this
    · exfalso
      have hab : ∀ x y : Λ, x * y = y * x := by
        intro x y
        have hx : (⟨x, hΛV x.2⟩ : V) ∈ Subgroup.center V := hcen x.2
        have := Subgroup.mem_center_iff.mp hx ⟨y, hΛV y.2⟩
        exact Subtype.ext (congrArg Subtype.val this).symm
      have hbot : commutator Λ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hΛperf.commutator_eq_top] at hbot
      apply subgroupOf_lBar_ne_bot h
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : Λ) ∈ (⊥ : Subgroup Λ) := hbot ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
  have hVeq : V = Λ := le_antisymm hVΛ hΛV
  subst hVeq
  exact ⟨U, hU, hcomm, hUV, hZU⟩

theorem mkC_eq_aBarHom (h : Sec13Data G A c L) :
    mkC (L := L) h.mem_A = aBarHom h ⟨c, h.mem_A⟩ :=
  Subtype.ext rfl

theorem orderOf_mkC (h : Sec13Data G A c L) : orderOf (mkC (L := L) h.mem_A) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (mkC_ne_one h)
  rw [mkC_eq_aBarHom h, ← map_pow]
  have : (⟨c, h.mem_A⟩ : A) ^ 3 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← h.orderOf_eq]
    exact pow_orderOf_eq_one c)
  rw [this, map_one]

theorem mkC_mem_lBar (h : Sec13Data G A c L) (hcL : c ∈ L) :
    mkC (L := L) h.mem_A ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
  Subgroup.mem_subgroupOf.mpr ⟨⟨c, le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt hcL⟩,
    Subgroup.mem_subgroupOf.mpr hcL, rfl⟩

theorem card_center_lBar (h : Sec13Data G A c L) :
    Nat.card (Subgroup.center ((Sec12.lBar c L).subgroupOf (lBarA c L A))) =
      Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  set e := (Subgroup.subgroupOfEquivOfLe (lBar_le_lBarA (A := A))).trans η.symm
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem exists_U_of_isHeisCentral (h : Sec13Data G A c L) (hcL : c ∈ L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L))
    (hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3) :
    ∃ U : Subgroup (lBarA c L A), mkC (L := L) h.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧
      (∀ x ∈ U, x ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
      (∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
        u ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) ∧
      (∀ a ∈ (aBarHom h).range, ∀ u ∈ U,
        a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) := by
  obtain ⟨U, hU, hUΛ, hUV, hZU⟩ := isHeisCentral_facts h hH
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set z := mkC (L := L) h.mem_A with hz
  have hzΛ : z ∈ Λ := mkC_mem_lBar h hcL
  set ZΛ := (Subgroup.center Λ).map Λ.subtype with hZΛ
  have hZΛcard : Nat.card ZΛ = 3 := by
    rw [hZΛ, Subgroup.card_map_of_injective Λ.subtype_injective, card_center_lBar h, hZ3]
  have hUΛZ : U ⊓ Λ ≤ ZΛ := by
    rintro x ⟨hxU, hxΛ⟩
    refine ⟨⟨x, hxΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact (hUΛ x hxU y y.2).symm
  have hUΛcard : Nat.card (U ⊓ Λ : Subgroup _) = 3 := by
    rw [← hZU, Subgroup.card_map_of_injective U.subtype_injective, hU.1.2.2.2]
  have hUΛeq : U ⊓ Λ = ZΛ := Subgroup.eq_of_le_of_card_ge hUΛZ (by rw [hZΛcard, hUΛcard])
  have hzZ : z ∈ ZΛ := by
    refine ⟨⟨z, hzΛ⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_center_iff.mp (mkC_mem_center h) y
  rw [← hUΛeq] at hzZ
  have hzpow : Subgroup.zpowers z = U ⊓ Λ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
    rw [hUΛcard, Nat.card_zpowers, orderOf_mkC h]
  refine ⟨U, hzZ.1, ?_, ?_, hUΛ, ?_, ?_⟩
  · rw [hU.2.1]
    norm_num
  · intro x hx
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : U)
    rw [hU.2.2] at h1
    simpa using congrArg Subtype.val h1
  · intro u hu huΛ
    rw [hzpow]
    exact ⟨hu, huΛ⟩
  · intro a _ u hu
    have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U Λ hUΛ).2
    have ha : a ∈ ((U ⊔ Λ : Subgroup _) : Set _) := by rw [hUV]; exact Subgroup.mem_top a
    rw [hcoe] at ha
    obtain ⟨u', hu', v', hv', rfl⟩ := Set.mem_mul.mp ha
    have hvu : v' * u = u * v' := (hUΛ u hu v' hv').symm
    have h1 : u' * v' * u * (u' * v')⁻¹ * u⁻¹ = u' * u * u'⁻¹ * u⁻¹ := by
      calc u' * v' * u * (u' * v')⁻¹ * u⁻¹ = u' * (v' * u) * v'⁻¹ * u'⁻¹ * u⁻¹ := by group
        _ = u' * (u * v') * v'⁻¹ * u'⁻¹ * u⁻¹ := by rw [hvu]
        _ = u' * u * u'⁻¹ * u⁻¹ := by group
    rw [h1, hzpow, ← hZU]
    have h2 : (⁅(⟨u', hu'⟩ : U), ⟨u, hu⟩⁆ : U) ∈ commutator U :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [hU.1.2.1] at h2
    exact ⟨_, h2, by simp [commutatorElement_def]⟩

omit [Finite G] in
theorem closure_le_centralizer_closure {X : Type*} [Group X] {s : Set X}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure s : Set X) := by
  have h1 : Subgroup.closure s ≤ Subgroup.centralizer s := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact hs y hy x hx
  rw [Subgroup.closure_le]
  intro y hy
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro w hw
  exact (Subgroup.mem_centralizer_iff.mp (h1 hw) y hy).symm

omit [Finite G] in
theorem commutator_mem_of_mem_closure {X : Type*} [Group X] {Z S : Subgroup X}
    (hZ : ∀ w ∈ Z, ∀ x : X, w * x = x * w) {u : X}
    (hS : ∀ g ∈ S, g * u * g⁻¹ * u⁻¹ ∈ Z) :
    ∀ g ∈ S, ∀ x ∈ Subgroup.closure ({u} : Set X) ⊔ Z, g * x * g⁻¹ * x⁻¹ ∈ Z := by
  intro g hg
  let T : Subgroup X :=
    { carrier := {x | g * x * g⁻¹ * x⁻¹ ∈ Z}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        have hgy : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
        have : g * (x * y) * g⁻¹ * (x * y)⁻¹ =
            (g * x * g⁻¹ * x⁻¹) * (x * ((g * y * g⁻¹ * y⁻¹)) * x⁻¹) := by group
        rw [this, ← hZ _ hy x, mul_inv_cancel_right]
        exact Z.mul_mem hx hy
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        have : g * x⁻¹ * g⁻¹ * x⁻¹⁻¹ =
            x⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * x := by group
        rw [this, ← hZ _ (Z.inv_mem hx) x⁻¹, inv_mul_cancel_right]
        exact Z.inv_mem hx }
  have hT : Subgroup.closure ({u} : Set X) ⊔ Z ≤ T := by
    refine sup_le ?_ fun w hw => ?_
    · rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact hS g hg
    · change g * w * g⁻¹ * w⁻¹ ∈ Z
      have h1 : g * w * g⁻¹ * w⁻¹ = 1 := by
        rw [← hZ w hw g]
        group
      rw [h1]
      exact Z.one_mem
  exact fun x hx => hT hx

omit [Finite G] in
theorem commutator_mem_of_mem_closure_left {X : Type*} [Group X] {Z : Subgroup X}
    (hZ : ∀ w ∈ Z, ∀ x : X, w * x = x * w) {u : X} {s : Set X}
    (hs : ∀ g ∈ s, g * u * g⁻¹ * u⁻¹ ∈ Z) :
    ∀ g ∈ Subgroup.closure s, g * u * g⁻¹ * u⁻¹ ∈ Z := by
  let T : Subgroup X :=
    { carrier := {g | g * u * g⁻¹ * u⁻¹ ∈ Z}
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_ofPred_eq] at hg hh ⊢
        have h1 : g * h * u * (g * h)⁻¹ * u⁻¹ = g * (h * u * h⁻¹ * u⁻¹) * u * g⁻¹ * u⁻¹ := by
          group
        rw [h1, ← hZ _ hh g]
        have h2 : (h * u * h⁻¹ * u⁻¹) * g * u * g⁻¹ * u⁻¹ =
            (h * u * h⁻¹ * u⁻¹) * (g * u * g⁻¹ * u⁻¹) := by group
        rw [h2]
        exact Z.mul_mem hh hg
      one_mem' := by simp
      inv_mem' := by
        intro g hg
        simp only [Set.mem_ofPred_eq] at hg ⊢
        have h1 : g⁻¹ * u * g⁻¹⁻¹ * u⁻¹ = g⁻¹ * ((g * u * g⁻¹ * u⁻¹)⁻¹ * g) := by group
        rw [h1, hZ _ (Z.inv_mem hg) g, inv_mul_cancel_left]
        exact Z.inv_mem hg }
  have hT : Subgroup.closure s ≤ T := (Subgroup.closure_le T).mpr hs
  exact fun g hg => hT hg

theorem exists_U_of_isSLThreePiTwo (h : Sec13Data G A c L) (hcL : c ∈ L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) :
    ∃ U : Subgroup (lBarA c L A), mkC (L := L) h.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧
      (∀ x ∈ U, x ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
      (∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
        u ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) ∧
      (∀ a ∈ (aBarHom h).range, ∀ u ∈ U,
        a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) := by
  set Q := lBarA c L A with hQ
  set Λ := (Sec12.lBar c L).subgroupOf Q with hΛ
  set z := mkC (L := L) h.mem_A with hz
  obtain ⟨L₀, hL₀, u, a, hL₀SL, huC, huL₀, huo, ha3, hgen, -, huaZ, -⟩ := hSL
  have hzc : ∀ x : Q, z * x = x * z := fun x =>
    (Subgroup.mem_center_iff.mp (mkC_mem_center h) x).symm
  have hzo : orderOf z = 3 := orderOf_mkC h
  have hcommL₀ : commutator Q ≤ L₀ := by
    set f := QuotientGroup.mk' L₀ with hf
    have hfua : f u * f a = f a * f u := by
      have h1 : f (u * a * u⁻¹ * a⁻¹) = 1 := by
        rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact huaZ.1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc f u * f a = (f u * f a * (f u)⁻¹ * (f a)⁻¹) * (f a * f u) := by group
        _ = f a * f u := by rw [h1, one_mul]
    have hrange : f.range ≤ Subgroup.closure {f u, f a} := by
      rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup, MonoidHom.map_closure]
      refine sup_le ?_ ?_
      · rw [Subgroup.map_le_iff_le_comap]
        intro l hl
        rw [Subgroup.mem_comap]
        have h1 : f l = 1 := by
          rw [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hl
        rw [h1]
        exact Subgroup.one_mem _
      · rw [Set.image_pair]
    have hab := closure_le_centralizer_closure (s := ({f u, f a} : Set (Q ⧸ L₀))) (by
      intro x hx y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hfua
      · exact hfua.symm
      · rfl)
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.ker_mk' L₀, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    have hx := hrange (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    have hy := hrange (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    exact (Subgroup.mem_centralizer_iff.mp (hab hy) _ hx)
  have hΛperf : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar h
  have hΛL₀ : Λ ≤ L₀ := by
    have h1 : (⊤ : Subgroup Λ).map Λ.subtype = Λ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc Λ = (commutator Λ).map Λ.subtype := by rw [hΛperf.commutator_eq_top, h1]
      _ = ⁅Λ, Λ⁆ := by rw [commutator_def, Subgroup.map_commutator, h1]
      _ ≤ commutator Q := Subgroup.commutator_mono le_top le_top
      _ ≤ L₀ := hcommL₀
  set Z₀ := (Subgroup.center L₀).map L₀.subtype with hZ₀
  have hZ₀card : Nat.card Z₀ = 3 := by
    rw [hZ₀, Subgroup.card_map_of_injective L₀.subtype_injective]
    exact card_center_of_isSLThreePi hL₀SL
  have hzL₀ : z ∈ L₀ := hΛL₀ (mkC_mem_lBar h hcL)
  have hzZ₀ : z ∈ Z₀ :=
    ⟨⟨z, hzL₀⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hzc y).symm, rfl⟩
  have hzpow : Subgroup.zpowers z = Z₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ₀) ?_
    rw [hZ₀card, Nat.card_zpowers, hzo]
  have hzpowL₀ : Subgroup.zpowers z ≤ L₀ := Subgroup.zpowers_le.mpr hzL₀
  have hz3 : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hzo] at h1
  have hu3 : u ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one u
    rwa [huo] at h1
  have huz : u ∉ Subgroup.zpowers z := fun hu => huL₀ (hzpowL₀ hu)
  have hzu : z * u = u * z := hzc u
  set U := Subgroup.zpowers z ⊔ Subgroup.zpowers u with hU
  have hUab : CFSG.Assembly.IsElemAbelian 3 U := isElemAbelian_zpowers_sup hz3 hu3 hzu
  have hzcen : ∀ w ∈ Subgroup.zpowers z, ∀ x : Q, w * x = x * w := by
    intro w hw x
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (show Commute z x from hzc x) i).eq
  have hUC : U ≤ Subgroup.centralizer (Λ : Set Q) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun l _ => (hzc l).symm
    · exact Subgroup.centralizer_le hΛL₀ huC
  refine ⟨U, Subgroup.mem_sup_left (Subgroup.mem_zpowers z), ?_, hUab.2, ?_, ?_, ?_⟩
  · rw [hU, Sec4.card_zpowers_sup_zpowers hu3 hzo huz hzu.symm]
  · intro x hx l hl
    exact (Subgroup.mem_centralizer_iff.mp (hUC hx) l hl).symm
  · intro x hx hxΛ
    have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers z)
      (Subgroup.zpowers u) (fun w hw y _ => hzcen w hw y)).2
    have hx' : x ∈ ((U : Subgroup Q) : Set Q) := hx
    rw [hU, hcoe] at hx'
    obtain ⟨w, hw, v, hv, rfl⟩ := Set.mem_mul.mp hx'
    have hvL₀ : v ∈ L₀ := by
      have h1 : v = w⁻¹ * (w * v) := by group
      rw [h1]
      exact L₀.mul_mem (L₀.inv_mem (hzpowL₀ hw)) (hΛL₀ hxΛ)
    have hv1 : v = 1 := by
      by_contra hv1
      have hvo : orderOf v = 3 := by
        refine orderOf_eq_prime ?_ hv1
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu3,
          _root_.one_zpow]
      have heq : Subgroup.zpowers v = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv) (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hvo, huo])
      have hu : u ∈ Subgroup.zpowers v := heq ▸ Subgroup.mem_zpowers u
      exact huL₀ ((Subgroup.zpowers_le.mpr hvL₀) hu)
    rw [hv1, mul_one]
    exact hw
  · intro g _ x hx
    have hua : u * a * u⁻¹ * a⁻¹ ∈ Subgroup.zpowers z := by
      rw [hzpow]
      exact ⟨⟨_, huaZ.1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext
        ((Subgroup.mem_centralizer_iff.mp huaZ.2 y y.2)), rfl⟩
    have hgen' : ∀ g : Q, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
      intro g
      have hgs : g ∈ Subgroup.closure ((L₀ : Set Q) ∪ {u, a}) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, hgen]
        exact Subgroup.mem_top g
      refine commutator_mem_of_mem_closure_left hzcen (fun g' hg' => ?_) g hgs
      rcases hg' with hg' | hg' | hg'
      · have h1 : g' * u = u * g' := Subgroup.mem_centralizer_iff.mp huC g' hg'
        rw [h1, mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [hg', mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · rw [Set.mem_singleton_iff] at hg'
        rw [hg']
        have h1 : a * u * a⁻¹ * u⁻¹ = (u * a * u⁻¹ * a⁻¹)⁻¹ := by group
        rw [h1]
        exact Subgroup.inv_mem _ hua
    have hall := commutator_mem_of_mem_closure (Z := Subgroup.zpowers z) hzcen
      (S := ⊤) (u := u) (fun g' _ => hgen' g') g (Subgroup.mem_top g) x (by
        rw [← Subgroup.zpowers_eq_closure, sup_comm]
        exact hx)
    exact hall

omit [Finite G] in
theorem map_inf_comap_eq {M M' : Type*} [Group M] [Group M'] (f : M →* M') (H : Subgroup M)
    (K : Subgroup M') : (H ⊓ K.comap f).map f = H.map f ⊓ K := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyH, hyK⟩, rfl⟩
    exact ⟨⟨y, hyH, rfl⟩, hyK⟩
  · rintro ⟨⟨y, hyH, rfl⟩, hyK⟩
    exact ⟨y, ⟨hyH, hyK⟩, rfl⟩

omit [Finite G] in
theorem isElemAbelian_of_injOn {M M' : Type*} [Group M] [Group M'] (f : M →* M')
    {E : Subgroup M} (hinj : Set.InjOn f E) (hE : CFSG.Assembly.IsElemAbelian 3 (E.map f)) :
    CFSG.Assembly.IsElemAbelian 3 E := by
  have := hE.1
  have hc : ∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E.map f) ⟨y, hy⟩)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · refine hinj (E.mul_mem a.2 b.2) (E.mul_mem b.2 a.2) ?_
    simp only [Subgroup.coe_mul, map_mul]
    exact hc _ (Subgroup.mem_map_of_mem f a.2) _ (Subgroup.mem_map_of_mem f b.2)
  · refine hinj (E.pow_mem hx 3) E.one_mem ?_
    rw [map_pow, hE.2 _ (Subgroup.mem_map_of_mem f hx), map_one]

theorem exists_E_of_U (h : Sec13Data G A c L) (hcL : c ∈ L) {U : Subgroup (lBarA c L A)}
    (hzU : mkC (L := L) h.mem_A ∈ U) (hU9 : 9 ≤ Nat.card U) (hU3 : ∀ x ∈ U, x ^ 3 = 1)
    (hUΛ : ∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u)
    (hUΛz : ∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
      u ∈ Subgroup.zpowers (mkC (L := L) h.mem_A))
    (hAbU : ∀ a ∈ (aBarHom h).range, ∀ u ∈ U,
      a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) h.mem_A)) :
    ∃ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∧
      ¬ IsCyclic (E ⊓ L : Subgroup G) ∧ A ≤ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set Ab := (aBarHom h).range with hAb
  set z := mkC (L := L) h.mem_A with hz
  have hzo : orderOf z = 3 := orderOf_mkC h
  have hzAb : z ∈ Ab := ⟨⟨c, h.mem_A⟩, (mkC_eq_aBarHom h).symm⟩
  have hzΛ : z ∈ Λ := mkC_mem_lBar h hcL
  have hΛn : Λ.Normal := lBar_normal h
  have hAbΛ : Ab ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hΛn.conj_mem y hy x, fun hy => ?_⟩
    have h1 := hΛn.conj_mem _ hy x⁻¹
    simpa [mul_assoc] using h1
  have hAbel : CFSG.Assembly.IsElemAbelian 3 Ab := by
    have := h.isElemAbelian.1
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, rfl⟩⟩ := y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, mul_comm' a b]
    · rintro _ ⟨a, rfl⟩
      have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using h.isElemAbelian.2 _ a.2)
      rw [← map_pow, h3, map_one]
  have hAb27 : Nat.card Ab = 27 := by
    rw [hAb, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective h)).toEquiv,
      h.card_eq]
  have hQcard : Nat.card (⊤ : Subgroup (lBarA c L A)) ≤ 9 * Nat.card Λ := by
    have h1 := CFSG.RankThree.PartTwo.Sec6.card_sup_mul_card_inf hAbΛ
    have h2 : Ab ⊔ Λ = ⊤ := by rw [sup_comm]; exact lBar_sup_range_aBarHom h
    have h3 : 3 ≤ Nat.card (Ab ⊓ Λ : Subgroup (lBarA c L A)) := by
      have := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr (show z ∈ Ab ⊓ Λ from ⟨hzAb, hzΛ⟩))
      rwa [Nat.card_zpowers, hzo] at this
    rw [h2, hAb27] at h1
    nlinarith
  have hAbUz : ∀ a ∈ Ab, a ∈ U → a ∈ Subgroup.zpowers z := by
    rintro _ ⟨a, rfl⟩ haU
    have hac := mem_zpowers_of_aBarHom_commute h a (fun y hy => hUΛ _ haU y hy)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hac
    have hai : a = (⟨c, h.mem_A⟩ : A) ^ i := Subtype.ext (by simp [hi])
    rw [hai, map_zpow, ← mkC_eq_aBarHom h]
    exact Subgroup.zpow_mem_zpowers _ _
  obtain ⟨hexp, hcomm, Eb, hEbAU, hEbab, hEb27, hzEb, hEbU, hEbΛ⟩ :=
    exists_elemAbelian_heis (X := lBarA c L A) (Q := ⊤) (Λ := Λ) (Ab := Ab) (U := U) (z := z) le_top
      le_top le_top hQcard hAbΛ hAbel hAb27 hzAb hzΛ
      (fun x _ => (Subgroup.mem_center_iff.mp (mkC_mem_center h) x).symm) hzo hzU hU9 hU3 hUΛ
      hUΛz hAbU hAbUz
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3
    (Subgroup.normalizer (Subgroup.zpowers c : Set G))) with hπ
  set M := (L ⊔ A).subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hM
  set Ebar := Eb.map (lBarA c L A).subtype with hEbar
  set B := (Ab ⊔ Eb).map (lBarA c L A).subtype with hB
  have hAbEbU : Ab ⊔ Eb ≤ Ab ⊔ U := sup_le le_sup_left hEbAU
  have hB3 : IsPGroup 3 B := by
    rintro ⟨_, ⟨w, hw, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h1 := hexp w (hAbEbU hw)
    simpa using congrArg Subtype.val h1
  have hBM : B ≤ M.map π := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  set A₁ := A.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G)) with hA₁
  have hA₁3 : IsPGroup 3 A₁ := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using h.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp x.2)
  have hA₁M : A₁ ≤ M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hπa : ∀ a : Subgroup.normalizer (Subgroup.zpowers c : Set G), ∀ ha : (a : G) ∈ A,
      π a = ((aBarHom h ⟨a, ha⟩ : lBarA c L A) : _) := fun a ha => by
    rw [aBarHom_apply]
  have hA₁B : A₁.map π ≤ B := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hπa a (Subgroup.mem_subgroupOf.mp ha)]
    exact ⟨_, Subgroup.mem_sup_left ⟨_, rfl⟩, rfl⟩
  obtain ⟨S, hA₁S, hSM, hS3, hSB⟩ := exists_isPGroup_le_map_eq hB3 hBM hA₁3 hA₁M hA₁B
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hS3
  set E₁ := S ⊓ Ebar.comap π with hE₁
  have hE₁S : E₁ ≤ S := inf_le_left
  have hE₁map : E₁.map π = Ebar := by
    rw [hE₁, map_inf_comap_eq, hSB]
    exact inf_eq_right.mpr (Subgroup.map_mono le_sup_right)
  have hinjE : Set.InjOn π E₁ := hinj.mono hE₁S
  have hE₁card : Nat.card E₁ = 27 := by
    rw [← card_map_eq_of_injOn π hinjE, hE₁map, hEbar,
      Subgroup.card_map_of_injective (lBarA c L A).subtype_injective, hEb27]
  have hE₁ab : CFSG.Assembly.IsElemAbelian 3 E₁ :=
    isElemAbelian_of_injOn π hinjE (by rw [hE₁map]; exact isElemAbelian_map hEbab _)
  have hEmem : ∀ e ∈ E₁, ∃ eb ∈ Eb, ((eb : lBarA c L A) : _) = π e := by
    rintro e ⟨-, he⟩
    obtain ⟨eb, heb, hebe⟩ := he
    exact ⟨eb, heb, hebe⟩
  have hzEbar : ∀ w ∈ Subgroup.zpowers z, w ∈ Eb := fun w hw => (Subgroup.zpowers_le.mpr hzEb) hw
  have hzAbar : ∀ w ∈ Subgroup.zpowers z, w ∈ Ab := fun w hw => (Subgroup.zpowers_le.mpr hzAb) hw
  have hconjE : ∀ a ∈ A₁, ∀ e ∈ E₁, a * e * a⁻¹ ∈ E₁ := by
    intro a ha e he
    refine ⟨S.mul_mem (S.mul_mem (hA₁S ha) (hE₁S he)) (S.inv_mem (hA₁S ha)), ?_⟩
    obtain ⟨eb, heb, hebe⟩ := hEmem e he
    set a' := aBarHom h ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
    have ha' : a' ∈ Ab := ⟨_, rfl⟩
    have hk := hcomm a' ha' eb (hEbAU heb)
    have hmem : a' * eb * a'⁻¹ ∈ Eb := by
      have h1 : a' * eb * a'⁻¹ = (a' * eb * a'⁻¹ * eb⁻¹) * eb := by group
      rw [h1]
      exact Eb.mul_mem (hzEbar _ hk) heb
    refine ⟨_, hmem, ?_⟩
    change ((a' : _) * (eb : _) * (a' : _)⁻¹) = π (a * e * a⁻¹)
    rw [hebe, map_mul, map_mul, map_inv, hπa a (Subgroup.mem_subgroupOf.mp ha)]
    rfl
  have hconjA : ∀ e ∈ E₁, ∀ a ∈ A₁, e * a * e⁻¹ ∈ A₁ := by
    intro e he a ha
    have hxS : e * a * e⁻¹ ∈ S := S.mul_mem (S.mul_mem (hE₁S he) (hA₁S ha)) (S.inv_mem (hE₁S he))
    obtain ⟨eb, heb, hebe⟩ := hEmem e he
    set a' := aBarHom h ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
    have ha' : a' ∈ Ab := ⟨_, rfl⟩
    have hk := hcomm a'⁻¹ (Ab.inv_mem ha') eb (hEbAU heb)
    have hmem : eb * a' * eb⁻¹ ∈ Ab := by
      have h1 : eb * a' * eb⁻¹ = a' * (a'⁻¹ * eb * a'⁻¹⁻¹ * eb⁻¹) := by group
      rw [h1]
      exact Ab.mul_mem ha' (hzAbar _ hk)
    obtain ⟨b, hb⟩ := hmem
    have hb₁ : (⟨b, h.A_le_normalizer_zpowers b.2⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈ A₁ :=
      Subgroup.mem_subgroupOf.mpr b.2
    have heq : π (e * a * e⁻¹) = π ⟨b, h.A_le_normalizer_zpowers b.2⟩ := by
      have h3 : π ⟨b, h.A_le_normalizer_zpowers b.2⟩ = ((aBarHom h b : lBarA c L A) : _) :=
        hπa ⟨b, h.A_le_normalizer_zpowers b.2⟩ b.2
      rw [h3, map_mul, map_mul, map_inv, ← hebe, hπa a (Subgroup.mem_subgroupOf.mp ha), hb]
      rfl
    have := hinj hxS (hA₁S hb₁) heq
    rw [this]
    exact hb₁
  have hE₁N : E₁ ≤ Subgroup.normalizer (A₁ : Set (Subgroup.normalizer
      (Subgroup.zpowers c : Set G))) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hconjA e he a, fun ha => ?_⟩
    have h1 := hconjA e⁻¹ (E₁.inv_mem he) _ ha
    simpa [mul_assoc] using h1
  have hA₁N : A₁ ≤ Subgroup.normalizer (E₁ : Set (Subgroup.normalizer
      (Subgroup.zpowers c : Set G))) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨hconjE a ha e, fun he => ?_⟩
    have h1 := hconjE a⁻¹ (A₁.inv_mem ha) _ he
    simpa [mul_assoc] using h1
  have hAmap : A₁.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype = A := by
    rw [hA₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.A_le_normalizer_zpowers]
  set E := E₁.map (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype with hE
  have hLAN : L ⊔ A ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer h.le_normalizer
  have hEexp : ∀ x ∈ E, x ^ 3 = 1 := (isElemAbelian_map hE₁ab _).2
  have hEcard : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective Subtype.coe_injective, hE₁card]
  have hcardInf : ∀ T : Subgroup (lBarA c L A), Nat.card (Eb ⊓ T : Subgroup _) ≤
      Nat.card ((E₁ ⊓ (T.map (lBarA c L A).subtype).comap π).map
        (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype) := by
    intro T
    rw [Subgroup.card_map_of_injective Subtype.coe_injective,
      ← card_map_eq_of_injOn π (hinjE.mono inf_le_left), map_inf_comap_eq, hE₁map, hEbar,
      ← Subgroup.map_inf_eq _ _ _ (lBarA c L A).subtype_injective,
      Subgroup.card_map_of_injective (lBarA c L A).subtype_injective]
  refine ⟨E, le_inf ?_ ?_, isElemAbelian_map hE₁ab _, hEcard, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hSM (hE₁S he))
  · rw [← hAmap]
    exact (Subgroup.map_mono hE₁N).trans (Subgroup.le_normalizer_map _)
  · refine not_isCyclic_of_nine_le (fun x hx => hEexp x hx.1) ?_
    refine (hEbU.trans (hcardInf U)).trans (Subgroup.card_le_of_le ?_)
    rintro _ ⟨e, ⟨he, heU⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    obtain ⟨u₀, hu₀, hu₀e⟩ := heU
    refine mem_thetaQuotCentralizer_of_mk_commute h.mem_thetaComponentsAt
      (hLAN (Subgroup.mem_subgroupOf.mp (hSM (hE₁S he)))) fun l hl => ?_
    have hlA : l ∈ M := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hl)
    have hlb : (⟨π l, Subgroup.mem_map_of_mem π hlA⟩ : lBarA c L A) ∈ Λ :=
      Subgroup.mem_subgroupOf.mpr ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have h1 := congrArg Subtype.val (hUΛ u₀ hu₀ _ hlb)
    simp only [Subgroup.coe_mul] at h1
    change π e * π l = π l * π e
    rw [← hu₀e]
    exact h1
  · refine not_isCyclic_of_nine_le (fun x hx => hEexp x hx.1) ?_
    refine (hEbΛ.trans (hcardInf Λ)).trans (Subgroup.card_le_of_le ?_)
    rintro _ ⟨e, ⟨he, heΛ⟩, rfl⟩
    refine ⟨⟨e, he, rfl⟩, ?_⟩
    obtain ⟨l₀, hl₀, hl₀e⟩ := heΛ
    have he3 : e ^ 3 ^ 1 = 1 := by
      rw [pow_one]
      exact hE₁ab.2 e he
    refine mem_of_mk_mem_lBar h.mem_thetaComponentsAt he3 ?_
    have := Subgroup.mem_subgroupOf.mp hl₀
    change π e ∈ Sec12.lBar c L
    rw [← hl₀e]
    exact this
  · intro a ha
    have ha₁ : (⟨a, h.A_le_normalizer_zpowers ha⟩ :
        Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∈ A₁ := Subgroup.mem_subgroupOf.mpr ha
    exact Subgroup.le_normalizer_map _ ⟨_, hA₁N ha₁, rfl⟩

end Case7

end CFSG.RankThree.PartTwo.Sec13

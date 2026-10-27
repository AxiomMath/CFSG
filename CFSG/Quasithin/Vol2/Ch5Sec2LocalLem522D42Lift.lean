module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Para
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem center_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

theorem eq_one_of_commutator_mem {K : Type*} [Group K] [Finite K]
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) {c : K} (hc7 : c ^ 7 = 1)
    (hc : ∀ x : K, c * x * c⁻¹ * x⁻¹ ∈ CFSG.pCore 2 K) : c = 1 := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 K) with hπ
  have hcen : π c ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have h1 : π (c * x * c⁻¹ * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr (hc x)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← commutatorElement_def,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  rw [hZ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := K)) ⟨c, hcen⟩
  have h1 : c ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h2 : orderOf c ∣ Nat.gcd (2 ^ m) 7 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hc7)
  have h3 : Nat.gcd (2 ^ m) 7 = 1 :=
    Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 7)
  rw [h3] at h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)

theorem mem_of_mem_normalizer {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hm : ChevalleyExceptionalModel Y .trialityD4 2 1) {U K : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) (hUK : U ≤ Subgroup.normalizer (K : Set Y)) (hK1 : K ≠ ⊥)
    (hKt : K ≠ ⊤) (h7 : 7 ∣ Nat.card ↥K) {c : Y} (hc7 : c ^ 7 = 1)
    (hcN : c ∈ Subgroup.normalizer (K : Set Y)) : c ∈ K := by
  by_contra hcK
  have hc1 : c ≠ 1 := fun h => hcK (h ▸ K.one_mem)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf c = 7 := orderOf_eq_prime hc7 hc1
  have hinf : Subgroup.zpowers c ⊓ K = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ K) ∣ 7 := by
      rw [← hord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hcK
      have heq : Subgroup.zpowers c ⊓ K = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hord])
      exact (heq ▸ inf_le_right : Subgroup.zpowers c ≤ K) (Subgroup.mem_zpowers c)
  have hNK : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set Y) :=
    (Subgroup.zpowers_le).mpr hcN
  have hcard := C5.card_sup_mul_card_inf_of_le_normalizer hNK
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord] at hcard
  have h49 : 49 ∣ Nat.card ↥(Subgroup.zpowers c ⊔ K) := by
    rw [hcard, show (49 : ℕ) = 7 * 7 from rfl]
    exact Nat.mul_dvd_mul_left 7 h7
  have hNt : Subgroup.normalizer (K : Set Y) ≠ ⊤ := by
    intro htop
    have hn : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · exact hK1 h
    · exact hKt h
  exact not_dvd_card_of_sylow_le hm hU hUK hNt
    (h49.trans (Subgroup.card_dvd_of_le (sup_le hNK Subgroup.le_normalizer)))

theorem elemAbelian_sup_zpowers {Q : Type*} [Group Q] [Finite Q] {Y E : Subgroup Q} (hEY : E ≤ Y)
    (hE : IsElemAbelian 7 E) (hE49 : Nat.card ↥E = 49) {m : Q} (hm7 : m ^ 7 = 1) (hmY : m ∉ Y)
    (hmc : ∀ y ∈ Y, m * y = y * m) :
    IsElemAbelian 7 (Subgroup.zpowers m ⊔ E) ∧ Nat.card ↥(Subgroup.zpowers m ⊔ E) = 7 ^ 3 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hm1 : m ≠ 1 := fun h => hmY (h ▸ Y.one_mem)
  have hord : orderOf m = 7 := orderOf_eq_prime hm7 hm1
  have hcomm : ∀ x ∈ Subgroup.zpowers m, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (hmc y (hEY hy)) i).eq
  have hinf : Subgroup.zpowers m ⊓ E = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers m ⊓ E) ∣ 7 := by
      rw [← hord, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hmY
      have heq : Subgroup.zpowers m ⊓ E = Subgroup.zpowers m :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hord])
      exact hEY ((heq ▸ inf_le_right : Subgroup.zpowers m ≤ E) (Subgroup.mem_zpowers m))
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hord, hE49] at hcard
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmem : ∀ x ∈ Subgroup.zpowers m ⊔ E, ∃ a ∈ Subgroup.zpowers m, ∃ e ∈ E, a * e = x := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers m ⊔ E : Subgroup Q) : Set Q) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, e, he, hae⟩ := hx'
    exact ⟨a, ha, e, he, hae⟩
  have hzc : ∀ x ∈ Subgroup.zpowers m, ∀ y ∈ Subgroup.zpowers m, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self m i j).eq
  have hz7 : ∀ x ∈ Subgroup.zpowers m, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm7, one_zpow]
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, by rw [hcard]; norm_num⟩
  · obtain ⟨a, ha, e, he, hx⟩ := hmem x x.2
    obtain ⟨a', ha', e', he', hy⟩ := hmem y y.2
    change (x : Q) * y = y * x
    rw [← hx, ← hy]
    calc a * e * (a' * e') = (a * a') * (e * e') := by
          rw [mul_assoc, ← mul_assoc e, ← hcomm a' ha' e he, mul_assoc, mul_assoc]
      _ = (a' * a) * (e' * e) := by rw [hzc a ha a' ha', hEc e he e' he']
      _ = a' * e' * (a * e) := by
          rw [mul_assoc, ← mul_assoc a, hcomm a ha e' he', mul_assoc, mul_assoc]
  · obtain ⟨a, ha, e, he, rfl⟩ := hmem x hx
    rw [(show Commute a e from hcomm a ha e he).mul_pow, hz7 a ha, hE.2 e he, one_mul]

theorem three_le_pRank_of_quotient {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {F : Subgroup (O2Q X)} (hF : IsElemAbelian 7 F) (hF3 : Nat.card ↥F = 7 ^ 3) :
    3 ≤ CFSG.Open.pRank 7 X := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h1 : 3 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup (O2Q X)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hF hF3
  have h7 : ¬ 7 ∣ Nat.card ↥(CFSG.pCore 2 ↥X) := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
    rw [hj]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h))
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ h7] at h1
  refine h1.trans ((CFSG.SectionRank.pRank_le_map (by norm_num) X.subtype X.subtype_injective
    ⊤).trans ?_)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin.H13.D42

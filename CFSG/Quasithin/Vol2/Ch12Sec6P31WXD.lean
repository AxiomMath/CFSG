module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXLie
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXA
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXB
public import CFSG.Quasithin.Vol2.Ch12Sec6P31e

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126

variable {Y : Type} [Group Y]

theorem exists_decomp {X₁ X₂ : Subgroup Y} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) {y : Y}
    (hy : y ∈ X₁ ⊔ X₂) : ∃ a ∈ X₁, ∃ b ∈ X₂, a * b = y := by
  have hK2N : X₂ ≤ Subgroup.normalizer X₁ := P31A.le_normalizer_of_comm le_rfl hcomm
  have h := Subgroup.coe_mul_of_right_le_normalizer_left X₁ X₂ hK2N
  have hy' : y ∈ ((X₁ ⊔ X₂ : Subgroup Y) : Set Y) := hy
  rw [h] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hy'
  exact ⟨a, ha, b, hb, hab⟩

theorem decomp_unique {X₁ X₂ : Subgroup Y} (hX : X₁ ⊓ X₂ = ⊥) {a a' b b' : Y} (ha : a ∈ X₁)
    (ha' : a' ∈ X₁) (hb : b ∈ X₂) (hb' : b' ∈ X₂) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a ∈ X₁ ⊓ X₂ := by
    refine ⟨X₁.mul_mem (X₁.inv_mem ha') ha, ?_⟩
    have : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    rw [this]
    exact X₂.mul_mem hb' (X₂.inv_mem hb)
  rw [hX, Subgroup.mem_bot] at h1
  have e1 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h1, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact mul_left_cancel h

theorem indep_of_not_mem_zpowers {u v : Y} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (hv3 : v ^ 3 = 1)
    (hv : v ∉ Subgroup.zpowers u) {a b : ℕ} (h : u ^ a * v ^ b = 1) : 3 ∣ a ∧ 3 ∣ b := by
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hb : 3 ∣ b := by
    by_contra h3b
    apply hv
    have hvb : v ^ b = (u ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hmem : v ^ b ∈ Subgroup.zpowers u := by
      rw [hvb]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) a)
    have hmod : b % 3 = 1 ∨ b % 3 = 2 := by omega
    have hvb' : v ^ b = v ^ (b % 3) := by
      conv_lhs => rw [← Nat.div_add_mod b 3, pow_add, pow_mul, hv3, one_pow, one_mul]
    rcases hmod with h1 | h1
    · rw [hvb', h1, pow_one] at hmem
      exact hmem
    · rw [hvb', h1] at hmem
      have : v = (v ^ 2) ^ 2 := by
        calc v = v ^ 3 * v := by rw [hv3, one_mul]
          _ = (v ^ 2) ^ 2 := by group
      rw [this]
      exact Subgroup.pow_mem _ hmem 2
  refine ⟨?_, hb⟩
  obtain ⟨t, rfl⟩ := hb
  have hvb : v ^ (3 * t) = 1 := by rw [pow_mul, hv3, one_pow]
  rw [hvb, mul_one] at h
  have := orderOf_dvd_of_pow_eq_one h
  rwa [huord] at this

theorem inf_ne_bot_of_threeRank [Finite Y] (hR : P31D.ThreeRankLE2 Y) {X₁ X₂ S : Subgroup Y}
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥) (h₁ : 3 ∣ Nat.card X₁)
    (hSK : S ≤ X₁ ⊔ X₂) (hSe : IsElemAbelian 3 S) (hS9 : Nat.card S = 9) : S ⊓ X₁ ≠ ⊥ := by
  intro hSX
  have hS3 : ∀ x ∈ S, x ^ 3 = 1 := hSe.2
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hSe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hSnt : Nontrivial S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hS9]; norm_num
  obtain ⟨u', hu'⟩ := exists_ne (1 : S)
  set u : Y := (u' : Y) with hu
  have huS : u ∈ S := u'.2
  have hu1 : u ≠ 1 := fun h => hu' (Subtype.ext h)
  have hv : ∃ v ∈ S, v ∉ Subgroup.zpowers u := by
    by_contra hall
    push Not at hall
    have hle : S ≤ Subgroup.zpowers u := hall
    have hu3 := hS3 u huS
    have hcard := Subgroup.card_le_of_le hle
    rw [hS9, Nat.card_zpowers, orderOf_eq_prime hu3 hu1] at hcard
    omega
  obtain ⟨v, hvS, hvu⟩ := hv
  have hind : ∀ a b : ℕ, u ^ a * v ^ b = 1 → 3 ∣ a ∧ 3 ∣ b := fun a b h =>
    indep_of_not_mem_zpowers (hS3 u huS) hu1 (hS3 v hvS) hvu h
  obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := exists_decomp hcomm (hSK huS)
  obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := exists_decomp hcomm (hSK hvS)
  have hcu : ∀ n : ℕ, u ^ n = a₁ ^ n * b₁ ^ n := fun n => by
    rw [← e₁]; exact (hcomm a₁ ha₁ b₁ hb₁ ▸ (Commute.mul_pow (hcomm a₁ ha₁ b₁ hb₁) n))
  have hcv : ∀ n : ℕ, v ^ n = a₂ ^ n * b₂ ^ n := fun n => by
    rw [← e₂]; exact (hcomm a₂ ha₂ b₂ hb₂ ▸ (Commute.mul_pow (hcomm a₂ ha₂ b₂ hb₂) n))
  have hb₁3 : b₁ ^ 3 = 1 := by
    have h := hS3 u huS
    rw [hcu 3] at h
    have := (decomp_unique hX (X₁.pow_mem ha₁ 3) X₁.one_mem (X₂.pow_mem hb₁ 3) X₂.one_mem
      (by rw [h, mul_one])).2
    exact this
  have hb₂3 : b₂ ^ 3 = 1 := by
    have h := hS3 v hvS
    rw [hcv 3] at h
    have := (decomp_unique hX (X₁.pow_mem ha₂ 3) X₁.one_mem (X₂.pow_mem hb₂ 3) X₂.one_mem
      (by rw [h, mul_one])).2
    exact this
  have hb12 : b₁ * b₂ = b₂ * b₁ := by
    have h := hScomm u huS v hvS
    rw [← e₁, ← e₂] at h
    have h2 : (a₁ * a₂) * (b₁ * b₂) = (a₂ * a₁) * (b₂ * b₁) := by
      calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
        _ = (a₂ * b₂) * (a₁ * b₁) := h
        _ = a₂ * (b₂ * a₁) * b₁ := by group
        _ = a₂ * (a₁ * b₂) * b₁ := by rw [hcomm a₁ ha₁ b₂ hb₂]
        _ = (a₂ * a₁) * (b₂ * b₁) := by group
    exact (decomp_unique hX (X₁.mul_mem ha₁ ha₂) (X₁.mul_mem ha₂ ha₁) (X₂.mul_mem hb₁ hb₂)
      (X₂.mul_mem hb₂ hb₁) h2).2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X₁) 3 h₁
  set y : Y := (y' : Y) with hy
  have hyX : y ∈ X₁ := y'.2
  have hyord : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe, hy']
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hby₁ : Commute b₁ y := (hcomm y hyX b₁ hb₁).symm
  have hby₂ : Commute b₂ y := (hcomm y hyX b₂ hb₂).symm
  refine hR b₁ b₂ y hb₁3 hb₂3 hy3 hb12 hby₁ hby₂ ?_
  intro a b c habc
  have hyc : y ^ c = (b₁ ^ a * b₂ ^ b)⁻¹ := eq_inv_of_mul_eq_one_right habc
  have hmem : y ^ c ∈ X₁ ⊓ X₂ :=
    ⟨X₁.pow_mem hyX c, by rw [hyc]; exact X₂.inv_mem (X₂.mul_mem (X₂.pow_mem hb₁ a)
      (X₂.pow_mem hb₂ b))⟩
  rw [hX, Subgroup.mem_bot] at hmem
  have hbb : b₁ ^ a * b₂ ^ b = 1 := by
    rw [hmem, mul_one] at habc
    exact habc
  have hc3 : 3 ∣ c := by
    have := orderOf_dvd_of_pow_eq_one hmem
    rwa [hyord] at this
  have hab : u ^ a * v ^ b = a₁ ^ a * a₂ ^ b := by
    rw [hcu, hcv]
    calc a₁ ^ a * b₁ ^ a * (a₂ ^ b * b₂ ^ b) = a₁ ^ a * (b₁ ^ a * a₂ ^ b) * b₂ ^ b := by group
      _ = a₁ ^ a * (a₂ ^ b * b₁ ^ a) * b₂ ^ b := by
          rw [hcomm (a₂ ^ b) (X₁.pow_mem ha₂ b) (b₁ ^ a) (X₂.pow_mem hb₁ a)]
      _ = a₁ ^ a * a₂ ^ b * (b₁ ^ a * b₂ ^ b) := by group
      _ = a₁ ^ a * a₂ ^ b := by rw [hbb, mul_one]
  have hmemS : u ^ a * v ^ b ∈ S ⊓ X₁ :=
    ⟨S.mul_mem (S.pow_mem huS a) (S.pow_mem hvS b), by
      rw [hab]; exact X₁.mul_mem (X₁.pow_mem ha₁ a) (X₁.pow_mem ha₂ b)⟩
  rw [hSX, Subgroup.mem_bot] at hmemS
  obtain ⟨ha3, hb3⟩ := hind a b hmemS
  have hbord1 : 3 ∣ a := ha3
  refine ⟨?_, ?_, hc3⟩
  ·
    exact ha3
  · exact hb3

section Pair

variable [Finite Y] {X₁ X₂ Ts : Subgroup Y}

theorem sylow_pair (hTs : IsSylowTwoOf Ts ⊤) (hnormal : (X₁ ⊔ X₂).Normal)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥) :
    IsSylowTwoOf (Ts ⊓ (X₁ ⊔ X₂)) (X₁ ⊔ X₂) ∧ IsSylowTwoOf (Ts ⊓ X₁) X₁ ∧
      IsSylowTwoOf (Ts ⊓ X₂) X₂ ∧ Ts ⊓ (X₁ ⊔ X₂) = (Ts ⊓ X₁) ⊔ (Ts ⊓ X₂) := by
  have hN₁ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) := sup_le_normalizer_left hcomm
  have hN₂ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₂ : Set Y) := by
    rw [sup_comm]
    exact sup_le_normalizer_left (fun b hb a ha => (hcomm a ha b hb).symm)
  have h0 : IsSylowTwoOf (Ts ⊓ (X₁ ⊔ X₂)) (X₁ ⊔ X₂) :=
    A4.isSylowTwoOf_inf_normal hTs le_top Subgroup.le_normalizer_of_normal
  have h1 : IsSylowTwoOf (Ts ⊓ X₁) X₁ := by
    have := A4.isSylowTwoOf_inf_normal h0 (le_sup_left : X₁ ≤ X₁ ⊔ X₂) hN₁
    rwa [inf_assoc, inf_eq_right.2 (le_sup_left : X₁ ≤ X₁ ⊔ X₂)] at this
  have h2 : IsSylowTwoOf (Ts ⊓ X₂) X₂ := by
    have := A4.isSylowTwoOf_inf_normal h0 (le_sup_right : X₂ ≤ X₁ ⊔ X₂) hN₂
    rwa [inf_assoc, inf_eq_right.2 (le_sup_right : X₂ ≤ X₁ ⊔ X₂)] at this
  refine ⟨h0, h1, h2, ?_⟩
  have hsp := P31A.sylow_inter_prod (K := X₁) (C := X₂) (T := Ts ⊓ (X₁ ⊔ X₂)) hX hcomm
    h0.2.1 inf_le_right (fun S hSK hS2 hTS => h0.eq_of_le hTS hSK hS2)
  rw [inf_assoc, inf_eq_right.2 (le_sup_left : X₁ ≤ X₁ ⊔ X₂), inf_assoc,
    inf_eq_right.2 (le_sup_right : X₂ ≤ X₁ ⊔ X₂)] at hsp
  exact hsp

theorem borel_pair_le (hTs : IsSylowTwoOf Ts ⊤) (hnormal : (X₁ ⊔ X₂).Normal)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥) :
    borel X₁ Ts ⊔ borel X₂ Ts ≤ borel (X₁ ⊔ X₂) Ts := by
  obtain ⟨-, -, -, hsplit⟩ := sylow_pair hTs hnormal hcomm hX
  have hcomm' : ∀ b ∈ X₂, ∀ a ∈ X₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  refine sup_le ?_ ?_
  · intro x hx
    obtain ⟨hxX, hxN⟩ := hx
    refine ⟨(le_sup_left : X₁ ≤ X₁ ⊔ X₂) hxX, ?_⟩
    have hx2 : x ∈ Subgroup.normalizer ((Ts ⊓ X₂ : Subgroup Y) : Set Y) :=
      P31A.le_normalizer_of_comm (inf_le_right : Ts ⊓ X₂ ≤ X₂) hcomm' hxX
    show x ∈ Subgroup.normalizer ((Ts ⊓ (X₁ ⊔ X₂) : Subgroup Y) : Set Y)
    rw [hsplit]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hxN, hx2⟩
  · intro x hx
    obtain ⟨hxX, hxN⟩ := hx
    refine ⟨(le_sup_right : X₂ ≤ X₁ ⊔ X₂) hxX, ?_⟩
    have hx1 : x ∈ Subgroup.normalizer ((Ts ⊓ X₁ : Subgroup Y) : Set Y) :=
      P31A.le_normalizer_of_comm (inf_le_right : Ts ⊓ X₁ ≤ X₁) hcomm hxX
    show x ∈ Subgroup.normalizer ((Ts ⊓ (X₁ ⊔ X₂) : Subgroup Y) : Set Y)
    rw [hsplit]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hx1, hxN⟩

theorem inf_eq_borel_pair [Finite Y] (hTs : IsSylowTwoOf Ts ⊤) (hnormal : (X₁ ⊔ X₂).Normal)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥)
    (hs₁ : IsSimpleGroup ↥X₁) (hs₂ : IsSimpleGroup ↥X₂) {Ms : Subgroup Y}
    (hBM : borel (X₁ ⊔ X₂) Ts ≤ Ms) (hKM : ¬ X₁ ≤ Ms)
    (hc₁ : IsCoatom ((borel X₁ Ts).subgroupOf X₁)) (hc₂ : IsCoatom ((borel X₂ Ts).subgroupOf X₂))
    (hne₁ : borel X₁ Ts ≠ ⊥) {t : Y} (htM : t ∈ Ms) (ht₁ : ∀ x ∈ X₁, t * x * t⁻¹ ∈ X₂)
    (ht₂ : ∀ x ∈ X₂, t * x * t⁻¹ ∈ X₁) :
    Ms ⊓ (X₁ ⊔ X₂) = borel X₁ Ts ⊔ borel X₂ Ts ∧ Ms ⊓ (X₁ ⊔ X₂) ⊓ X₁ = borel X₁ Ts ∧
      Ms ⊓ (X₁ ⊔ X₂) ⊓ X₂ = borel X₂ Ts := by
  have hBle := borel_pair_le hTs hnormal hcomm hX
  have htN : t ∈ Subgroup.normalizer ((Ms ⊓ (X₁ ⊔ X₂) : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.normalizer_eq_top_iff.2 hnormal ▸
      Subgroup.mem_top t) x)
    constructor
    · rintro ⟨hxM, hxK⟩
      exact ⟨Ms.mul_mem (Ms.mul_mem htM hxM) (Ms.inv_mem htM), h1.1 hxK⟩
    · rintro ⟨hxM, hxK⟩
      refine ⟨?_, h1.2 hxK⟩
      have := Ms.mul_mem (Ms.mul_mem (Ms.inv_mem htM) hxM) htM
      simpa [mul_assoc] using this
  have hBY : borel X₁ Ts ⊔ borel X₂ Ts ≤ Ms ⊓ (X₁ ⊔ X₂) :=
    le_inf (hBle.trans hBM) (hBle.trans inf_le_left)
  have hYK : Ms ⊓ (X₁ ⊔ X₂) ≤ X₁ ⊔ X₂ := inf_le_right
  haveI := hs₁
  haveI := hs₂
  rcases P31D.borel_pair_maximal_overgroups hcomm hX (inf_le_left : borel X₁ Ts ≤ X₁)
    (inf_le_left : borel X₂ Ts ≤ X₂) hc₁ hc₂ hne₁ hBY hYK ht₁ ht₂ htN with ⟨h1, h2, h3⟩ | ⟨h1, -, -⟩
  · exact ⟨h3, h1, h2⟩
  · exact absurd (fun x hx => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (h1.ge hx)).1).1) hKM

end Pair

theorem le_of_normal_sylow [Finite Y] {B U W : Subgroup Y} (hU : IsSylowTwoOf U B)
    (hUN : B ≤ Subgroup.normalizer (U : Set Y)) (hWB : W ≤ B) (hW : IsPGroup 2 W) : W ≤ U := by
  obtain ⟨S, hWS, hS⟩ := exists_isSylowTwoOf_of_le hWB hW
  obtain ⟨h, hh, hSU⟩ := hU.exists_conj hS
  have hSU' : S = U := by
    rw [hSU]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (hUN hh)
  rw [← hSU']
  exact hWS

theorem mul_pow_mem {B U : Subgroup Y} (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set Y))
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ U) {a b : Y} (ha : a ∈ B) (hb : b ∈ B)
    {p k l : ℕ} (hak : a ^ (p ^ k) ∈ U) (hbl : b ^ (p ^ l) ∈ U) :
    (a * b) ^ (p ^ (k + l)) ∈ U := by
  haveI hN : (U.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 hBU
  have hc : (QuotientGroup.mk ⟨a, ha⟩ : ↥B ⧸ U.subgroupOf B) *
      (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ U.subgroupOf B) =
      (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ U.subgroupOf B) * QuotientGroup.mk ⟨a, ha⟩ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hcomm (b⁻¹) (B.inv_mem hb) (a⁻¹) (B.inv_mem ha)
    simpa [mul_assoc] using this
  have hA : (QuotientGroup.mk ⟨a, ha⟩ : ↥B ⧸ U.subgroupOf B) ^ (p ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hak
  have hB' : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ U.subgroupOf B) ^ (p ^ l) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hbl
  have hAB : ((QuotientGroup.mk ⟨a, ha⟩ : ↥B ⧸ U.subgroupOf B) *
      QuotientGroup.mk ⟨b, hb⟩) ^ (p ^ (k + l)) = 1 := by
    rw [Commute.mul_pow hc]
    have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥B ⧸ U.subgroupOf B) ^ (p ^ (k + l)) = 1 := by
      rw [pow_add, pow_mul, hA, one_pow]
    have h2 : (QuotientGroup.mk ⟨b, hb⟩ : ↥B ⧸ U.subgroupOf B) ^ (p ^ (k + l)) = 1 := by
      rw [add_comm, pow_add, pow_mul, hB', one_pow]
    rw [h1, h2, one_mul]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hAB
  simpa using hAB

@[expose] def pTors (p : ℕ) (B U : Subgroup Y) (hUB : U ≤ B)
    (hBU : B ≤ Subgroup.normalizer (U : Set Y))
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ U) : Subgroup Y where
  carrier := {b | b ∈ B ∧ ∃ k : ℕ, b ^ (p ^ k) ∈ U}
  mul_mem' := by
    rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
    exact ⟨B.mul_mem ha hb, k + l, mul_pow_mem hUB hBU hcomm ha hb hk hl⟩
  one_mem' := ⟨B.one_mem, 0, by simpa using U.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, k, hk⟩
    refine ⟨B.inv_mem ha, k, ?_⟩
    rw [inv_pow]
    exact U.inv_mem hk

theorem eq_one_of_pow_three {P : Subgroup Y} (hP : IsPGroup 2 P) {x : Y} (hx : x ∈ P)
    (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have : orderOf x ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

theorem normalizer_left_of_inverts {X₁ X₂ Ts : Subgroup Y} [Finite Y] (hX₁ : IsSimpleGroup ↥X₁)
    (hX₂ : IsSimpleGroup ↥X₂) (hnc₁ : ¬ ∀ a b : ↥X₁, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥) {r s₁ : Y}
    (hr : r ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Y) : Set Y)) (hs₁X : s₁ ∈ X₁)
    (hs₁3 : s₁ ^ 3 = 1) (hs₁ne : s₁ ≠ 1) (hTs2 : IsPGroup 2 Ts)
    (hinv : r * s₁ * r⁻¹ * s₁ ∈ (Ts ⊓ X₁) ⊔ (Ts ⊓ X₂)) :
    r ∈ Subgroup.normalizer (X₁ : Set Y) := by
  have hN₁ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) := sup_le_normalizer_left hcomm
  by_contra hrN
  have hc : X₁.map (MulAut.conj r).toMonoidHom = X₂ := by
    rcases map_conj_pair hX₁ hX₂ hX₁ hnc₁ hcomm hr le_sup_left hN₁ with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.2 h) hrN
    · exact h
  have hrs : r * s₁ * r⁻¹ ∈ X₂ := by
    rw [← hc]
    exact ⟨s₁, hs₁X, by simp [MulAut.conj_apply]⟩
  have hcU : ∀ a ∈ Ts ⊓ X₁, ∀ b ∈ Ts ⊓ X₂, a * b = b * a := fun a ha b hb =>
    hcomm a ha.2 b hb.2
  obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := exists_decomp hcU hinv
  have hprod : (r * s₁ * r⁻¹) * s₁ = s₁ * (r * s₁ * r⁻¹) := (hcomm s₁ hs₁X _ hrs).symm
  have h1 : s₁ * (r * s₁ * r⁻¹) = u₁ * u₂ := by rw [← hprod, ← hu]
  obtain ⟨hs, -⟩ := decomp_unique hX hs₁X hu₁.2 hrs hu₂.2 h1
  apply hs₁ne
  exact eq_one_of_pow_three hTs2 (hs ▸ hu₁.1) hs₁3

structure PairData (Y : Type) [Group Y] (m : ℕ) (Ts Ms Ls Tls X₁ X₂ : Subgroup Y) : Prop where
  threeRank : P31D.ThreeRankLE2 Y
  sylow : IsSylowTwoOf Ts ⊤
  psl₁ : IsPSL 2 2 m ↥X₁
  psl₂ : IsPSL 2 2 m ↥X₂
  comm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a
  inf_eq : X₁ ⊓ X₂ = ⊥
  normal : (X₁ ⊔ X₂).Normal
  swap : ∃ t ∈ Ts, X₁.map (MulAut.conj t).toMonoidHom = X₂
  Ts_le : Ts ≤ Ms
  borel_le : borel (X₁ ⊔ X₂) Ts ≤ Ms
  not_le : ¬ X₁ ≤ Ms
  no27 : ¬ 27 ∣ Nat.card Ms
  Ls_le : Ls ≤ Ms
  Ls_gen : Ls = Subgroup.closure {x | x ∈ Ls ∧ x ^ 3 = 1}
  Tls_le : Tls ≤ Ts
  f7 : ∃ r ∈ Tls, ∃ S : Subgroup Y, S ≤ Ls ∧ IsElemAbelian 3 S ∧ Nat.card S = 9 ∧
    ∀ s ∈ S, r * s * r⁻¹ * s ∈ pCoreOf 2 Ls

theorem commutator_prod_mem {X₁ X₂ U₁ U₂ : Subgroup Y} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    {a₁ b₁ a₂ b₂ : Y} (ha₁ : a₁ ∈ X₁)
    (hb₁ : b₁ ∈ X₁) (ha₂ : a₂ ∈ X₂) (hb₂ : b₂ ∈ X₂)
    (h₁ : a₁ * b₁ * a₁⁻¹ * b₁⁻¹ ∈ U₁) (h₂ : a₂ * b₂ * a₂⁻¹ * b₂⁻¹ ∈ U₂) :
    (a₁ * a₂) * (b₁ * b₂) * (a₁ * a₂)⁻¹ * (b₁ * b₂)⁻¹ ∈ U₁ ⊔ U₂ := by
  have hc : ∀ x ∈ X₂, ∀ y ∈ X₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have c1 : a₂ * b₁ = b₁ * a₂ := hc a₂ ha₂ b₁ hb₁
  have hX1 : (a₂ * b₂ * a₂⁻¹) * a₁⁻¹ = a₁⁻¹ * (a₂ * b₂ * a₂⁻¹) :=
    hc _ (X₂.mul_mem (X₂.mul_mem ha₂ hb₂) (X₂.inv_mem ha₂)) _ (X₁.inv_mem ha₁)
  have hX2 : (a₂ * b₂ * a₂⁻¹ * b₂⁻¹) * b₁⁻¹ = b₁⁻¹ * (a₂ * b₂ * a₂⁻¹ * b₂⁻¹) :=
    hc _ (X₂.mul_mem (X₂.mul_mem (X₂.mul_mem ha₂ hb₂) (X₂.inv_mem ha₂)) (X₂.inv_mem hb₂)) _
      (X₁.inv_mem hb₁)
  have e : (a₁ * a₂) * (b₁ * b₂) * (a₁ * a₂)⁻¹ * (b₁ * b₂)⁻¹ =
      (a₁ * b₁ * a₁⁻¹ * b₁⁻¹) * (a₂ * b₂ * a₂⁻¹ * b₂⁻¹) := by
    calc (a₁ * a₂) * (b₁ * b₂) * (a₁ * a₂)⁻¹ * (b₁ * b₂)⁻¹
        = a₁ * (a₂ * b₁) * b₂ * a₂⁻¹ * a₁⁻¹ * b₂⁻¹ * b₁⁻¹ := by group
      _ = a₁ * (b₁ * a₂) * b₂ * a₂⁻¹ * a₁⁻¹ * b₂⁻¹ * b₁⁻¹ := by rw [c1]
      _ = a₁ * b₁ * ((a₂ * b₂ * a₂⁻¹) * a₁⁻¹) * b₂⁻¹ * b₁⁻¹ := by group
      _ = a₁ * b₁ * (a₁⁻¹ * (a₂ * b₂ * a₂⁻¹)) * b₂⁻¹ * b₁⁻¹ := by rw [hX1]
      _ = a₁ * b₁ * a₁⁻¹ * ((a₂ * b₂ * a₂⁻¹ * b₂⁻¹) * b₁⁻¹) := by group
      _ = a₁ * b₁ * a₁⁻¹ * (b₁⁻¹ * (a₂ * b₂ * a₂⁻¹ * b₂⁻¹)) := by rw [hX2]
      _ = (a₁ * b₁ * a₁⁻¹ * b₁⁻¹) * (a₂ * b₂ * a₂⁻¹ * b₂⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup h₁ h₂

theorem permData_build {Ts Ms Tls Bs Us : Subgroup Y} {p : ℕ} {n r : Y} (hp : p.Prime)
    (hp3 : 3 < p) (hUsB : Us ≤ Bs) (hBsN : Bs ≤ Subgroup.normalizer (Us : Set Y))
    (hab : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b * a⁻¹ * b⁻¹ ∈ Us) (hBsM : Bs ≤ Ms)
    (hTsB : ∀ t ∈ Ts, ∀ b ∈ Bs, t * b * t⁻¹ ∈ Bs) (hTsU : ∀ t ∈ Ts, ∀ u ∈ Us, t * u * t⁻¹ ∈ Us)
    (hUsT : Us ≤ Ts) (hnB : n ∈ Bs) (hnp : n ^ p ∈ Us) (hrTls : r ∈ Tls)
    (hmoved : n * r * n⁻¹ * r⁻¹ ∉ Us) : PermData Ts Ms Tls := by
  refine ⟨p, pTors p Bs Us hUsB hBsN hab, Us, n, r, hp, hp3, ?_, ?_, hUsT, ?_,
    fun x hx => hBsN hx.1, fun x hx => hx.2, ?_, hrTls, hmoved⟩
  · exact fun x hx => hBsM hx.1
  ·
    have hconj : ∀ u ∈ Ts, ∀ b ∈ pTors p Bs Us hUsB hBsN hab,
        u * b * u⁻¹ ∈ pTors p Bs Us hUsB hBsN hab := by
      intro u hu b hb
      obtain ⟨hbB, k', hk'⟩ := hb
      refine ⟨hTsB u hu b hbB, k', ?_⟩
      have e : (u * b * u⁻¹) ^ (p ^ k') = u * b ^ (p ^ k') * u⁻¹ := by
        simpa [MulAut.conj_apply] using ((MulAut.conj u).toMonoidHom.map_pow b (p ^ k'))
      rw [e]
      exact hTsU u hu _ hk'
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconj u hu x hx, fun hx => ?_⟩
    have := hconj u⁻¹ (Ts.inv_mem hu) _ hx
    simpa [mul_assoc] using this
  · intro u hu
    exact ⟨hUsB hu, 0, by simpa using hu⟩
  · exact ⟨hnB, 1, by simpa using hnp⟩

theorem permData_of_pair [Finite Y] (hL : L2BorelFacts) {m : ℕ} (hm : 3 ≤ m)
    {Ts Ms Ls Tls X₁ X₂ : Subgroup Y} (h : PairData Y m Ts Ms Ls Tls X₁ X₂) :
    PermData Ts Ms Tls := by
  obtain ⟨hR, hTs, hX₁, hX₂, hcomm, hX, hnormal, ⟨t, htTs, htX⟩, hTsMs, hBM, hKM, h27, hLM,
    hLgen, hTlsTs, r, hrTls, S, hSL, hSe, hS9, hSinv⟩ := h
  have hcomm' : ∀ b ∈ X₂, ∀ a ∈ X₁, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hnorm : ∀ x : Y, x ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Y) : Set Y) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.2 hnormal]
    exact Subgroup.mem_top x
  have hN₁ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) := sup_le_normalizer_left hcomm
  have hN₂ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₂ : Set Y) := by
    rw [sup_comm]
    exact sup_le_normalizer_left hcomm'
  have h8 : 8 ≤ 2 ^ m := calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h64 : 64 ≤ 4 ^ m := calc 64 = 4 ^ 3 := by norm_num
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI hs₁ : IsSimpleGroup ↥X₁ := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m hX₁).2
  haveI hs₂ : IsSimpleGroup ↥X₂ := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 m hX₂).2
  obtain ⟨hSylK, hSyl₁, hSyl₂, hsplit⟩ := sylow_pair hTs hnormal hcomm hX
  obtain ⟨hcX₁, hcU₁, hcB₁, hcoat₁, hab₁, hcyc₁, hfrob₁⟩ :=
    hL m (by omega) Y X₁ (Ts ⊓ X₁) hX₁ hSyl₁
  obtain ⟨hcX₂, hcU₂, hcB₂, hcoat₂, hab₂, hcyc₂, hfrob₂⟩ :=
    hL m (by omega) Y X₂ (Ts ⊓ X₂) hX₂ hSyl₂
  have hnp : ∀ (X : Subgroup Y) [IsSimpleGroup ↥X], Nat.card ↥X = 2 ^ m * (4 ^ m - 1) →
      ¬ ∀ a b : ↥X, a * b = b * a := by
    intro X _ hc
    refine S126P31.not_comm_of_simple_card (X := ↥X) ?_
    rw [hc]
    exact Nat.not_prime_mul (by omega) (by omega)
  have hnc₁ := hnp X₁ hcX₁
  have hnc₂ := hnp X₂ hcX₂
  have h3dvd : 3 ∣ 4 ^ m - 1 := by
    have h4m : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    omega
  have h₁ : 3 ∣ Nat.card ↥X₁ := by rw [hcX₁]; exact Dvd.dvd.mul_left h3dvd _
  have h₂ : 3 ∣ Nat.card ↥X₂ := by rw [hcX₂]; exact Dvd.dvd.mul_left h3dvd _
  have hX₁X₂ : X₁ ≠ X₂ := by
    intro h
    obtain ⟨a, b, hab⟩ := hs₁.exists_pair_ne
    apply hab
    have ha : (a : Y) ∈ X₁ ⊓ X₂ := ⟨a.2, h ▸ a.2⟩
    have hb : (b : Y) ∈ X₁ ⊓ X₂ := ⟨b.2, h ▸ b.2⟩
    rw [hX] at ha hb
    exact Subtype.ext ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)
  have hLK : Ls ≤ X₁ ⊔ X₂ := by
    refine hLgen.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨-, hx3⟩
    exact mem_sup_of_order_three hR hs₁ hs₂ hnc₁ hnc₂ hcomm hX h₁ h₂ (hnorm x) hx3
  have ht₁ : ∀ x ∈ X₁, t * x * t⁻¹ ∈ X₂ := fun x hx => by
    rw [← htX]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have ht₂ : ∀ x ∈ X₂, t * x * t⁻¹ ∈ X₁ := by
    have hm2 : X₂.map (MulAut.conj t).toMonoidHom = X₁ := by
      rcases map_conj_pair hs₁ hs₂ hs₂ hnc₂ hcomm (hnorm t) le_sup_right hN₂ with h | h
      · exact h
      · exact absurd (Subgroup.map_injective (MulAut.conj t).injective
          (h.trans htX.symm)).symm hX₁X₂
    intro x hx
    rw [← hm2]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hne₁ : borel X₁ Ts ≠ ⊥ := by
    intro h0
    have h' : X₁ ⊓ Subgroup.normalizer ((Ts ⊓ X₁ : Subgroup Y) : Set Y) = ⊥ := h0
    rw [h', Subgroup.card_bot] at hcB₁
    have h56 : 8 * 7 ≤ 2 ^ m * (2 ^ m - 1) := Nat.mul_le_mul h8 (by omega)
    omega
  obtain ⟨hMB, hMB₁, hMB₂⟩ := inf_eq_borel_pair hTs hnormal hcomm hX hs₁ hs₂ hBM hKM hcoat₁
    hcoat₂ hne₁ (hTsMs htTs) ht₁ ht₂
  have hSK : S ≤ X₁ ⊔ X₂ := hSL.trans hLK
  have hSX : S ⊓ X₁ ≠ ⊥ := inf_ne_bot_of_threeRank hR hcomm hX h₁ hSK hSe hS9
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hSX
  have hs₁S : (a : Y) ∈ S := (Subgroup.mem_inf.1 a.2).1
  have hs₁X : (a : Y) ∈ X₁ := (Subgroup.mem_inf.1 a.2).2
  have hs₁ne : (a : Y) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hs₁3 : (a : Y) ^ 3 = 1 := hSe.2 _ hs₁S
  have hUsB : Ts ⊓ (X₁ ⊔ X₂) ≤ Ms ⊓ (X₁ ⊔ X₂) := le_inf (inf_le_left.trans hTsMs) inf_le_right
  have hBsN : Ms ⊓ (X₁ ⊔ X₂) ≤ Subgroup.normalizer ((Ts ⊓ (X₁ ⊔ X₂) : Subgroup Y) : Set Y) := by
    rw [hMB]
    exact (borel_pair_le hTs hnormal hcomm hX).trans inf_le_right
  have hSylBs : IsSylowTwoOf (Ts ⊓ (X₁ ⊔ X₂)) (Ms ⊓ (X₁ ⊔ X₂)) :=
    A4.isSylowTwoOf_mono hSylK hUsB inf_le_right
  have hLBs : Ls ≤ Ms ⊓ (X₁ ⊔ X₂) := le_inf hLM hLK
  have hO2 : pCoreOf 2 Ls ≤ Ts ⊓ (X₁ ⊔ X₂) :=
    le_of_normal_sylow hSylBs hBsN ((pCoreOf_le 2 Ls).trans hLBs) (pCoreOf_isPGroup 2 Ls)
  have hrTs : r ∈ Ts := hTlsTs hrTls
  have hinv : r * (a : Y) * r⁻¹ * (a : Y) ∈ (Ts ⊓ X₁) ⊔ (Ts ⊓ X₂) := by
    rw [← hsplit]
    exact hO2 (hSinv _ hs₁S)
  have hrN : r ∈ Subgroup.normalizer (X₁ : Set Y) :=
    normalizer_left_of_inverts hs₁ hs₂ hnc₁ hcomm hX (hnorm r) hs₁X hs₁3 hs₁ne hTs.2.1 hinv
  have hrU : r ∈ Subgroup.normalizer ((Ts ⊓ X₁ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hrTs) x
    have h2 := Subgroup.mem_normalizer_iff.1 hrN x
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  have hs₁B : (a : Y) ∈ borel X₁ Ts := by
    rw [← hMB₁]
    exact ⟨hLBs (hSL hs₁S), hs₁X⟩
  have hs₁U : (a : Y) ∉ Ts ⊓ X₁ := fun h => hs₁ne (eq_one_of_pow_three hTs.2.1 h.1 hs₁3)
  have hinvU : r * (a : Y) * r⁻¹ * (a : Y) ∈ Ts ⊓ X₁ := by
    refine ⟨?_, ?_⟩
    ·
      have := hO2 (hSinv _ hs₁S)
      exact this.1
    · have h2 := (Subgroup.mem_normalizer_iff.1 hrN (a : Y)).1 hs₁X
      exact X₁.mul_mem h2 hs₁X
  obtain ⟨j, hj⟩ := hfrob₁ r ⟨hrN, hrU⟩
  have hjodd : Odd j := by
    by_contra hje
    rw [Nat.not_odd_iff_even] at hje
    have h3j : 3 ∣ 2 ^ j - 1 := P31NT.three_dvd_two_pow_sub_one_iff.2 hje
    have hpow : (a : Y) ^ (2 ^ j) = a := by
      obtain ⟨t', ht'⟩ := h3j
      have h2j : 2 ^ j = 3 * t' + 1 := by
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      rw [h2j, pow_succ, pow_mul, hs₁3, one_pow, one_mul]
    have h1 := hj (a : Y) hs₁B
    rw [hpow] at h1
    have h2 : (a : Y) * a ∈ Ts ⊓ X₁ := by
      have e : (a : Y) * a = (r * a * r⁻¹ * (a : Y)⁻¹)⁻¹ * (r * a * r⁻¹ * a) := by group
      rw [e]
      exact (Ts ⊓ X₁).mul_mem ((Ts ⊓ X₁).inv_mem h1) hinvU
    apply hs₁U
    have e : (a : Y) = ((a : Y) * a)⁻¹ := by
      calc (a : Y) = ((a : Y) * a)⁻¹ * ((a : Y) * a * a) := by group
        _ = ((a : Y) * a)⁻¹ := by
          rw [← pow_three', hs₁3, mul_one]
    rw [e]
    exact (Ts ⊓ X₁).inv_mem h2
  have hcB₁' : Nat.card ↥(borel X₁ Ts) = 2 ^ m * (2 ^ m - 1) := hcB₁
  have hcB₂' : Nat.card ↥(borel X₂ Ts) = 2 ^ m * (2 ^ m - 1) := hcB₂
  have hm_even : Even m := by
    have hord : orderOf (a : Y) = 3 := orderOf_eq_prime hs₁3 hs₁ne
    have hd : orderOf (a : Y) ∣ Nat.card ↥(borel X₁ Ts) := Subgroup.orderOf_dvd_natCard _ hs₁B
    rw [hord, hcB₁'] at hd
    have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    exact P31NT.three_dvd_two_pow_sub_one_iff.1 (hcop.dvd_of_dvd_mul_left hd)
  have hm3 : ¬ 3 ∣ m := by
    intro h3m
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hv := P31NT.padicValNat_three_two_pow_sub_one hm_even (by omega)
    have hv3 : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd (by omega) h3m
    have h9 : 3 ^ 2 ∣ 2 ^ m - 1 := (padicValNat_dvd_iff_le (by omega)).2 (by omega)
    have h9' : 9 ∣ 2 ^ m - 1 := by simpa using h9
    have hB1 : 9 ∣ Nat.card ↥(borel X₁ Ts) := by rw [hcB₁']; exact Dvd.dvd.mul_left h9' _
    have hB2 : 9 ∣ Nat.card ↥(borel X₂ Ts) := by rw [hcB₂']; exact Dvd.dvd.mul_left h9' _
    have hcB : ∀ x ∈ borel X₁ Ts, ∀ y ∈ borel X₂ Ts, x * y = y * x := fun x hx y hy =>
      hcomm x hx.1 y hy.1
    have hiB : borel X₁ Ts ⊓ borel X₂ Ts = ⊥ :=
      le_bot_iff.1 (hX ▸ inf_le_inf inf_le_left inf_le_left)
    have hcard := L1233.card_sup_of_commute hcB hiB
    have h81 : 81 ∣ Nat.card ↥(borel X₁ Ts ⊔ borel X₂ Ts) := by
      rw [hcard]
      exact (by norm_num : (81 : ℕ) = 9 * 9) ▸ mul_dvd_mul hB1 hB2
    have hBM' : borel X₁ Ts ⊔ borel X₂ Ts ≤ Ms := by
      rw [← hMB]
      exact inf_le_left
    have hdvdMs : Nat.card ↥(borel X₁ Ts ⊔ borel X₂ Ts) ∣ Nat.card ↥Ms :=
      Subgroup.card_dvd_of_le hBM'
    exact h27 ((by norm_num : 27 ∣ 81).trans (h81.trans hdvdMs))
  obtain ⟨k, hk⟩ := hm_even
  have hk2 : 2 ≤ k := by omega
  have hk3 : k ≠ 3 := fun h => hm3 (by omega)
  obtain ⟨p, hp, hp5, hpk⟩ := P31NT.exists_prime_ge_five_dvd_two_pow_add_one hk2 hk3
  have hcard' : Nat.card ↥(borel X₁ Ts) = Nat.card ↥(Ts ⊓ X₁) * (2 ^ (2 * k) - 1) := by
    have hm2 : m = 2 * k := by omega
    rw [hcB₁', hcU₁, hm2]
  obtain ⟨n, hnB, hnp, hnr⟩ := exists_moved_p_element (B := borel X₁ Ts) (U := Ts ⊓ X₁) (r := r)
    (k := k) (j := j) (p := p) (le_inf inf_le_right Subgroup.le_normalizer) inf_le_right hcard'
    hj hp (by omega) hpk hjodd
  have hab : ∀ x ∈ Ms ⊓ (X₁ ⊔ X₂), ∀ y ∈ Ms ⊓ (X₁ ⊔ X₂),
      x * y * x⁻¹ * y⁻¹ ∈ Ts ⊓ (X₁ ⊔ X₂) := by
    intro x hx y hy
    rw [hMB] at hx hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := exists_decomp (X₁ := borel X₁ Ts) (X₂ := borel X₂ Ts)
      (fun a ha b hb => hcomm a ha.1 b hb.1) hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := exists_decomp (X₁ := borel X₁ Ts) (X₂ := borel X₂ Ts)
      (fun a ha b hb => hcomm a ha.1 b hb.1) hy
    have := commutator_prod_mem (X₁ := X₁) (X₂ := X₂) (U₁ := Ts ⊓ X₁) (U₂ := Ts ⊓ X₂) hcomm
      hx₁.1 hy₁.1 hx₂.1 hy₂.1 (hab₁ x₁ hx₁ y₁ hy₁) (hab₂ x₂ hx₂ y₂ hy₂)
    rw [← hsplit] at this
    exact this
  refine permData_build (n := n) hp (by omega) hUsB hBsN hab inf_le_left ?_ ?_ inf_le_left ?_ ?_ hrTls ?_
  ·
    intro u hu b hb
    exact ⟨Ms.mul_mem (Ms.mul_mem (hTsMs hu) hb.1) (Ms.inv_mem (hTsMs hu)),
      (Subgroup.mem_normalizer_iff.1 (hnorm u) b).1 hb.2⟩
  · intro u hu b hb
    exact ⟨Ts.mul_mem (Ts.mul_mem hu hb.1) (Ts.inv_mem hu),
      (Subgroup.mem_normalizer_iff.1 (hnorm u) b).1 hb.2⟩
  ·
    rw [hMB]
    exact Subgroup.mem_sup_left hnB
  · have : n ^ p ∈ Ts ⊓ X₁ := hnp
    exact ⟨this.1, (le_sup_left : X₁ ≤ X₁ ⊔ X₂) this.2⟩
  ·
    intro hmem
    apply hnr
    refine ⟨hmem.1, ?_⟩
    have hnX : n ∈ X₁ := hnB.1
    have h2 := (Subgroup.mem_normalizer_iff.1 hrN n⁻¹).1 (X₁.inv_mem hnX)
    have e : n * r * n⁻¹ * r⁻¹ = n * (r * n⁻¹ * r⁻¹) := by group
    rw [e]
    exact X₁.mul_mem hnX h2

end CFSG.Quasithin.H13.P31X

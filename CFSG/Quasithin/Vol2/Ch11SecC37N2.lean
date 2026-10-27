module

public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_orderOf_pow (x : G) : ∃ e : ℕ, Odd (orderOf (x ^ 2 ^ e)) := by
  suffices h : ∀ m : ℕ, ∀ y : G, orderOf y = m → ∃ e : ℕ, Odd (orderOf (y ^ 2 ^ e)) from
    h _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hy
    rcases Nat.even_or_odd m with he | ho
    · have hpos : 0 < orderOf y := orderOf_pos y
      have h2 : orderOf (y ^ 2) = m / 2 := by
        rw [orderOf_pow_of_dvd (by norm_num) (hy ▸ even_iff_two_dvd.mp he), hy]
      obtain ⟨e, he'⟩ := ih (m / 2) (by omega) (y ^ 2) h2
      refine ⟨e + 1, ?_⟩
      rwa [pow_succ', pow_mul]
    · exact ⟨0, by rwa [pow_zero, pow_one, hy]⟩

omit [Finite G] in
theorem pow_eq_one_of_pow_two_pow {y : G} (hy : Odd (orderOf y)) {e k : ℕ}
    (h : (y ^ 2 ^ e) ^ k = 1) : y ^ k = 1 := by
  rw [← pow_mul] at h
  have h1 : orderOf y ∣ 2 ^ e * k := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (orderOf y) (2 ^ e) :=
    Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hy)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left h1)

theorem le_normalizer_of_borel {T L : Subgroup G} (hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L)
    {Q : Type} [Group Q] [Finite Q] {a m n : ℕ} (hm : Odd m) (hQ : Nat.card Q = 2 ^ a * m)
    (ψ : ↥L →* Q) (hψs : Function.Surjective ψ) (hψker : ∀ y, ψ y = 1 → (y : G) ∈ T)
    (hBorel : ∀ Y U : Subgroup Q, U ≤ Y → IsPGroup 2 U → Nat.card U = 2 ^ a →
      (∀ y ∈ Y, Odd (orderOf y) → y ^ (2 ^ n - 1) = 1) → Y ≤ Subgroup.normalizer (U : Set Q))
    {Y₀ : Subgroup G} (hTY : T ⊓ L ≤ Y₀) (hY₀L : Y₀ ≤ L)
    (hY₀ : ∀ x ∈ Y₀, Odd (orderOf x) → x ^ (2 ^ n - 1) = 1) :
    Y₀ ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' : Subgroup Q := ((T ⊓ L).subgroupOf L).map ψ with hU'
  set Y' : Subgroup Q := (Y₀.subgroupOf L).map ψ with hY'
  have hU'Y' : U' ≤ Y' := Subgroup.map_mono fun x hx => hTY hx
  have hU'2 : IsPGroup 2 ↥U' := by
    refine IsPGroup.map ?_ ψ
    exact hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL.1).symm
  have hU'card : Nat.card ↥U' = 2 ^ a := by
    obtain ⟨b, hb⟩ := hU'2.exists_card_eq
    have hodd : ¬ 2 ∣ U'.index :=
      fun h => hTL.2.2 (h.trans (Subgroup.index_map_dvd _ hψs))
    have h1 := Subgroup.card_mul_index U'
    rw [hb, hQ] at h1
    have hidx : Odd U'.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    rw [hb, SecA.eq_of_two_pow_mul_odd hidx hm h1]
  have hY'odd : ∀ y ∈ Y', Odd (orderOf y) → y ^ (2 ^ n - 1) = 1 := by
    rintro _ ⟨x, hx, rfl⟩ hyo
    obtain ⟨e, he⟩ := exists_odd_orderOf_pow x
    have hxe : (x : G) ^ 2 ^ e ∈ Y₀ := Y₀.pow_mem (Subgroup.mem_subgroupOf.mp hx) _
    have h1 : ((x : G) ^ 2 ^ e) ^ (2 ^ n - 1) = 1 := hY₀ _ hxe (by
      rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
      exact he)
    refine pow_eq_one_of_pow_two_pow hyo (e := e) ?_
    rw [← map_pow, ← map_pow]
    have h2 : (x ^ 2 ^ e) ^ (2 ^ n - 1) = 1 := Subtype.ext (by simpa using h1)
    rw [h2, map_one]
  have hN := hBorel Y' U' hU'Y' hU'2 hU'card hY'odd
  have hpre : ∀ y : ↥L, ψ y ∈ U' → (y : G) ∈ T := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hy
    have h1 : ψ (y * t⁻¹) = 1 := by rw [map_mul, map_inv, hty, mul_inv_cancel]
    have h2 := hψker _ h1
    have : (y : G) = ((y * t⁻¹ : ↥L) : G) * t := by simp
    rw [this]
    exact T.mul_mem h2 (Subgroup.mem_subgroupOf.mp ht).1
  have key : ∀ y : ↥L, ψ y ∈ Subgroup.normalizer (U' : Set Q) → ∀ t ∈ T ⊓ L,
      (y : G) * t * (y : G)⁻¹ ∈ T ⊓ L := by
    intro y hy t ht
    have hmem : ψ (y * ⟨t, ht.2⟩ * y⁻¹) ∈ U' := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp
        ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    exact ⟨hpre _ hmem, L.mul_mem (L.mul_mem y.2 ht.2) (L.inv_mem y.2)⟩
  intro x hx
  have hxN : ψ ⟨x, hY₀L hx⟩ ∈ Subgroup.normalizer (U' : Set Q) :=
    hN ⟨⟨x, hY₀L hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key _ hxN t, fun ht => ?_⟩
  have := key (⟨x, hY₀L hx⟩⁻¹) (by rw [map_inv]; exact Subgroup.inv_mem _ hxN) _ ht
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch11.SecC

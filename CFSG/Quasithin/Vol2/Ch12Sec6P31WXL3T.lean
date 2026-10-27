module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXBT

public section

namespace CFSG.Quasithin.H13.P31X

open CFSG.QuasithinUnique
open scoped Pointwise

theorem l3_transport {n : ℕ} {Y : Type} [Group Y] [Finite Y] {X U : Subgroup Y} {G : Type}
    [Group G] [Finite G] (hU : IsSylowTwoOf U X) (e : ↥X ≃* G) {UG : Subgroup G}
    (he : (U.subgroupOf X).map e.toMonoidHom = UG) {zc : ℕ}
    (hcardU : Nat.card ↥UG = (2 ^ n) ^ 3)
    (hcardN : Nat.card ↥(Subgroup.normalizer (UG : Set G)) * Nat.gcd 3 (2 ^ n - 1) =
      (2 ^ n) ^ 3 * (2 ^ n - 1) ^ 2 * zc)
    (hcomm : ∀ a ∈ Subgroup.normalizer (UG : Set G), ∀ b ∈ Subgroup.normalizer (UG : Set G),
      a * b * a⁻¹ * b⁻¹ ∈ UG)
    (hsolv : ∀ A : Subgroup G, UG ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer (UG : Set G))
    (hmodel : Even n → ¬ 3 ∣ n → ∀ α : MulAut G, UG.map α.toMonoidHom = UG →
      ∀ c ∈ Subgroup.normalizer (UG : Set G), c ∉ UG → c ^ 3 ∈ UG → α c * c ∈ UG →
        ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (n / 2) + 1 →
          ∃ b ∈ Subgroup.normalizer (UG : Set G), b ^ p ∈ UG ∧ α b * b⁻¹ ∉ UG) :
    Nat.card ↥(X ⊓ Subgroup.normalizer (U : Set Y)) * Nat.gcd 3 (2 ^ n - 1) =
        Nat.card ↥U * (2 ^ n - 1) ^ 2 * zc ∧
      (∀ a ∈ X ⊓ Subgroup.normalizer (U : Set Y), ∀ b ∈ X ⊓ Subgroup.normalizer (U : Set Y),
        a * b * a⁻¹ * b⁻¹ ∈ U) ∧
      (∀ A : Subgroup Y, A ≤ X → U ≤ A → Group.IsSolvable ↥A →
        A ≤ X ⊓ Subgroup.normalizer (U : Set Y)) ∧
      (Even n → ¬ 3 ∣ n →
        ∀ r ∈ Subgroup.normalizer (X : Set Y) ⊓ Subgroup.normalizer (U : Set Y),
          (∃ c ∈ X ⊓ Subgroup.normalizer (U : Set Y), c ∉ U ∧ c ^ 3 ∈ U ∧ r * c * r⁻¹ * c ∈ U) →
          ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ (n / 2) + 1 →
            ∃ b ∈ X ⊓ Subgroup.normalizer (U : Set Y), b ^ p ∈ U ∧ r * b * r⁻¹ * b⁻¹ ∉ U) := by
  refine ⟨?_, bt_abel hU e he hcomm, bt_solv hU e he hsolv, ?_⟩
  · rw [bt_card_B hU e he, bt_card_U hU e he, hcardU]
    exact hcardN
  · intro hev h3 r hr hc p hp hp5 hpn
    obtain ⟨c, hcB, hcU, hc3, hrc⟩ := hc
    obtain ⟨α, hαU, hαx⟩ := bt_conj hU e he r hr
    have hcX : c ∈ X := (Subgroup.mem_inf.mp hcB).1
    have hcN : c ∈ Subgroup.normalizer (U : Set Y) := (Subgroup.mem_inf.mp hcB).2
    have hrX : r * c * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hr.1 c).1 hcX
    have hc'N : e ⟨c, hcX⟩ ∈ Subgroup.normalizer (UG : Set G) :=
      (bt_mem_B hU e he ⟨c, hcX⟩).1 hcB
    have hc'U : e ⟨c, hcX⟩ ∉ UG := by
      intro h
      exact hcU ((bt_mem_U e he ⟨c, hcX⟩).2 h)
    have hc'3 : e ⟨c, hcX⟩ ^ 3 ∈ UG := by
      rw [← map_pow]
      exact (bt_mem_U e he (⟨c, hcX⟩ ^ 3)).1 (by simpa using hc3)
    have hαc' : α (e ⟨c, hcX⟩) * e ⟨c, hcX⟩ ∈ UG := by
      have key : e (⟨r * c * r⁻¹, hrX⟩ * ⟨c, hcX⟩) = α (e ⟨c, hcX⟩) * e ⟨c, hcX⟩ := by
        rw [map_mul, hαx ⟨c, hcX⟩ hrX]
      rw [← key]
      exact (bt_mem_U e he _).1 (by simpa using hrc)
    obtain ⟨b', hb'N, hb'p, hb'α⟩ :=
      hmodel hev h3 α hαU _ hc'N hc'U hc'3 hαc' p hp hp5 hpn
    obtain ⟨b, rfl⟩ : ∃ b : ↥X, e b = b' := ⟨e.symm b', by simp⟩
    have hbX : (b : Y) ∈ X := b.2
    have hbB : (b : Y) ∈ X ⊓ Subgroup.normalizer (U : Set Y) := (bt_mem_B hU e he b).2 hb'N
    refine ⟨(b : Y), hbB, ?_, ?_⟩
    · apply (bt_mem_U e he (b ^ p)).2
      rw [map_pow]
      exact hb'p
    · intro hmem
      apply hb'α
      have hxb : r * (b : Y) * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hr.1 b).1 hbX
      have key : e ⟨r * (b : Y) * r⁻¹ * (b : Y)⁻¹, by
          exact X.mul_mem hxb (X.inv_mem hbX)⟩ = α (e b) * (e b)⁻¹ := by
        have h1 : (⟨r * (b : Y) * r⁻¹ * (b : Y)⁻¹, X.mul_mem hxb (X.inv_mem hbX)⟩ : ↥X) =
            ⟨r * (b : Y) * r⁻¹, hxb⟩ * b⁻¹ := by
          apply Subtype.ext
          simp [mul_assoc]
        rw [h1, map_mul, map_inv, hαx b hxb]
      rw [← key]
      exact (bt_mem_U e he _).1 hmem

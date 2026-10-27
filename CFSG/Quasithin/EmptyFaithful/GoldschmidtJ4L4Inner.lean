module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Open CFSG.LieType.BorelTits

variable {Y : Type} [Group Y]

theorem innerOnModO2_of_mul {B K : Subgroup Y} {x b : Y} (hb : b ∈ B) (hKp : IsPGroup 2 K)
    (hBK : ∀ y ∈ B, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hxB : ∀ y ∈ B, x * y * x⁻¹ ∈ B)
    (hc : b⁻¹ * x ∈ K) : A38c8.InnerOnModO2 B x := by
  refine ⟨b, hb, fun y hy => ?_⟩
  set c : Y := b⁻¹ * x with hcdef
  have hxc : x = b * c := by rw [hcdef]; group
  have hy' : y⁻¹ ∈ B := B.inv_mem hy
  have hcB : c * y⁻¹ * c⁻¹ ∈ B := by
    have : c * y⁻¹ * c⁻¹ = b⁻¹ * (x * y⁻¹ * x⁻¹) * b := by rw [hcdef]; group
    rw [this]
    exact B.mul_mem (B.mul_mem (B.inv_mem hb) (hxB _ hy')) hb
  have hwK : c * y⁻¹ * c⁻¹ * y ∈ K := by
    have h1 : y⁻¹ * c⁻¹ * y ∈ K := by
      have := hBK y⁻¹ hy' c⁻¹ (K.inv_mem hc)
      simpa using this
    have : c * y⁻¹ * c⁻¹ * y = c * (y⁻¹ * c⁻¹ * y) := by group
    rw [this]
    exact K.mul_mem hc h1
  have hwB : c * y⁻¹ * c⁻¹ * y ∈ B := B.mul_mem hcB hy
  have hnorm : B ≤ Subgroup.normalizer ((K ⊓ B : Subgroup Y) : Set Y) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hwK, hwB⟩
      exact ⟨hBK z hz w hwK, B.mul_mem (B.mul_mem hz hwB) (B.inv_mem hz)⟩
    · rintro ⟨hwK, hwB⟩
      refine ⟨?_, ?_⟩
      · have := hBK z⁻¹ (B.inv_mem hz) _ hwK
        simpa [mul_assoc] using this
      · have := B.mul_mem (B.mul_mem (B.inv_mem hz) hwB) hz
        simpa [mul_assoc] using this
  have hp : IsPGroup 2 (K ⊓ B : Subgroup Y) := hKp.to_le inf_le_left
  have hmem : c * y⁻¹ * c⁻¹ * y ∈ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm hp ⟨hwK, hwB⟩
  have hconj : b * (c * y⁻¹ * c⁻¹ * y) * b⁻¹ ∈ pCoreOf 2 B :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 B hb) _).1 hmem
  have e : (x * y * x⁻¹)⁻¹ * (b * y * b⁻¹) = b * (c * y⁻¹ * c⁻¹ * y) * b⁻¹ := by
    rw [hxc]; group
  rw [e]
  exact hconj

theorem isPGroup_of_map_le {G X : Type*} [Group G] [Group X] (π : G →* X) {K : Subgroup G}
    {Q : Subgroup X} (hker : IsPGroup 2 π.ker) (hQ : IsPGroup 2 Q) (hKQ : K.map π ≤ Q) :
    IsPGroup 2 K := by
  intro k
  have h1 : π (k : G) ∈ Q := hKQ ⟨k, k.2, rfl⟩
  obtain ⟨n, hn⟩ := hQ ⟨π k, h1⟩
  have h2 : (k : G) ^ 2 ^ n ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val hn
  obtain ⟨m, hm⟩ := hker ⟨(k : G) ^ 2 ^ n, h2⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simpa [pow_add, pow_mul] using this

section Quotient

variable {X : Type*} [Group X] [Finite X]

theorem innerOnModO2_of_quotient {H P B : Subgroup Y} (π : ↥H →* X) (hker : IsPGroup 2 π.ker)
    (hPH : P ≤ H) (hBH : B ≤ H) (hPB : P ≤ Subgroup.normalizer (B : Set Y))
    (hM : ∀ t ∈ (P.subgroupOf H).map π, ∃ b ∈ (B.subgroupOf H).map π,
      b⁻¹ * t ∈ pCoreOf 2 ((B.subgroupOf H).map π ⊔ (P.subgroupOf H).map π)) :
    ∀ x ∈ P, A38c8.InnerOnModO2 B x := by
  intro x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Yq : Subgroup X := (B.subgroupOf H).map π ⊔ (P.subgroupOf H).map π with hYq
  set Q : Subgroup X := pCoreOf 2 Yq with hQ
  have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 Yq
  have hQn : Yq ≤ Subgroup.normalizer (Q : Set X) := le_normalizer_pCoreOf 2 Yq
  let K₀ : Subgroup ↥H := Q.comap π ⊓ (B ⊔ P).subgroupOf H
  let K : Subgroup Y := K₀.map H.subtype
  have hKp : IsPGroup 2 K := by
    refine (isPGroup_of_map_le π hker hQp (K := K₀) ?_).map H.subtype
    rintro _ ⟨k, hk, rfl⟩
    exact hk.1
  have hBK : ∀ y ∈ B, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    obtain ⟨k₀, ⟨hk1, hk2⟩, rfl⟩ := hk
    let y' : ↥H := ⟨y, hBH hy⟩
    have hy'B : y' ∈ B.subgroupOf H := Subgroup.mem_subgroupOf.2 hy
    have hπy : π y' ∈ Yq := Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π hy'B)
    refine ⟨y' * k₀ * y'⁻¹, ⟨?_, ?_⟩, rfl⟩
    · show π (y' * k₀ * y'⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hQn hπy) (π k₀)).1 hk1
    · have hk2' : (k₀ : Y) ∈ B ⊔ P := Subgroup.mem_subgroupOf.1 hk2
      show y * (k₀ : Y) * y⁻¹ ∈ B ⊔ P
      exact (B ⊔ P).mul_mem ((B ⊔ P).mul_mem (Subgroup.mem_sup_left hy) hk2')
        ((B ⊔ P).inv_mem (Subgroup.mem_sup_left hy))
  have hxB : ∀ y ∈ B, x * y * x⁻¹ ∈ B := fun y hy =>
    (Subgroup.mem_normalizer_iff.1 (hPB hx) y).1 hy
  have hxP : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
  obtain ⟨bq, hbq, hbqQ⟩ := hM _ (Subgroup.mem_map_of_mem π hxP)
  obtain ⟨b', hb', rfl⟩ := hbq
  have hb : (b' : Y) ∈ B := Subgroup.mem_subgroupOf.1 hb'
  refine innerOnModO2_of_mul hb hKp hBK hxB ?_
  refine ⟨b'⁻¹ * ⟨x, hPH hx⟩, ⟨?_, ?_⟩, rfl⟩
  · show π (b'⁻¹ * ⟨x, hPH hx⟩) ∈ Q
    rw [map_mul, map_inv]
    exact hbqQ
  · show (b' : Y)⁻¹ * x ∈ B ⊔ P
    exact (B ⊔ P).mul_mem (Subgroup.mem_sup_left (B.inv_mem hb)) (Subgroup.mem_sup_right hx)

end Quotient

end CFSG.Quasithin.J4L4

module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.F146Field.Case1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

theorem pow_mem_inf_of_pow_mul_eq_one {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    {c d : G} (hc : c ∈ A) (hd : d ∈ B) {n : ℕ} (h : (c * d) ^ n = 1) : c ^ n ∈ A ⊓ B := by
  have hAN : A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hAB hx⟩
  have hBN : B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hBA hx, Subgroup.le_normalizer hx⟩
  have : ((A ⊓ B).subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans le_sup_left)).mpr
      (sup_le hAN hBN)
  set c' : ↥(A ⊔ B) := ⟨c, Subgroup.mem_sup_left hc⟩ with hc'
  set d' : ↥(A ⊔ B) := ⟨d, Subgroup.mem_sup_right hd⟩ with hd'
  have hcomm : Commute (QuotientGroup.mk c' : ↥(A ⊔ B) ⧸ (A ⊓ B).subgroupOf (A ⊔ B))
      (QuotientGroup.mk d') := by
    show QuotientGroup.mk c' * QuotientGroup.mk d' = QuotientGroup.mk d' * QuotientGroup.mk c'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (c * d)⁻¹ * (d * c) ∈ A ⊓ B
    rw [mul_inv_rev]
    refine ⟨?_, ?_⟩
    · have h1 : d⁻¹ * c⁻¹ * d ∈ A :=
        ((Subgroup.mem_normalizer_iff''.mp (hBA hd) c⁻¹).mp (A.inv_mem hc))
      have : d⁻¹ * c⁻¹ * (d * c) = (d⁻¹ * c⁻¹ * d) * c := by group
      rw [this]
      exact A.mul_mem h1 hc
    · have h1 : c⁻¹ * d * c ∈ B :=
        ((Subgroup.mem_normalizer_iff''.mp (hAB hc) d).mp hd)
      have : d⁻¹ * c⁻¹ * (d * c) = d⁻¹ * (c⁻¹ * d * c) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem hd) h1
  have h1 : (QuotientGroup.mk (c' ^ n) : ↥(A ⊔ B) ⧸ (A ⊓ B).subgroupOf (A ⊔ B)) *
      QuotientGroup.mk (d' ^ n) = 1 := by
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, ← hcomm.mul_pow, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (c' * d') ^ n = 1 := Subtype.ext (by simpa using h)
    rw [this]
    exact Subgroup.one_mem _
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have h2 : c ^ n * d ^ n ∈ A ⊓ B := by simpa [c', d'] using h1
  refine ⟨A.pow_mem hc n, ?_⟩
  have : c ^ n = (c ^ n * d ^ n) * (d ^ n)⁻¹ := by group
  rw [this]
  exact B.mul_mem h2.2 (B.inv_mem (B.pow_mem hd n))

variable [Finite G]

theorem mem_of_mul_mem {A B T : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hT : IsPGroup 2 T)
    (hC : IsPGroup 2 ↥(A ⊓ B)) (hS : IsSylowTwoOf (T ⊓ A) A) {c d : G} (hc : c ∈ A) (hd : d ∈ B)
    (hcd : c * d ∈ T) : c ∈ T := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ A ∧ ∃ y ∈ B, x * y ∈ T}
      one_mem' := ⟨A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, y₁, hy₁, h₁⟩ ⟨hx₂, y₂, hy₂, h₂⟩
        refine ⟨A.mul_mem hx₁ hx₂, (x₂⁻¹ * y₁ * x₂ * y₁⁻¹) * y₁ * y₂, ?_, ?_⟩
        · exact B.mul_mem (B.mul_mem (B.mul_mem
            ((Subgroup.mem_normalizer_iff''.mp (hAB hx₂) y₁).mp hy₁) (B.inv_mem hy₁)) hy₁) hy₂
        · have : x₁ * x₂ * ((x₂⁻¹ * y₁ * x₂ * y₁⁻¹) * y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) := by
            group
          rw [this]
          exact T.mul_mem h₁ h₂
      inv_mem' := by
        rintro x ⟨hx, y, hy, h⟩
        refine ⟨A.inv_mem hx, x * y⁻¹ * x⁻¹, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hAB hx) y⁻¹).mp (B.inv_mem hy)
        · have : x⁻¹ * (x * y⁻¹ * x⁻¹) = (x * y)⁻¹ := by group
          rw [this]
          exact T.inv_mem h }
  have hSA : S ≤ A := fun x hx => hx.1
  have hTS : T ⊓ A ≤ S := fun x hx => ⟨hx.2, 1, B.one_mem, by simpa using hx.1⟩
  have hS2 : IsPGroup 2 ↥S := by
    rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨k, hk⟩ := hT ⟨x * y, hxy⟩
    have h1 : (x * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 := pow_mem_inf_of_pow_mul_eq_one hAB hBA hx hy h1
    obtain ⟨j, hj⟩ := hC ⟨x ^ 2 ^ k, h2⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have h3 : (x ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using h3
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp hS).2.2 S hSA hS2 hTS
  exact (hmax ⟨hc, d, hd, hcd⟩).1

theorem mem_normalizer_inf_sup {A B T : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hT : IsPGroup 2 T) (hC : A ⊓ B ≤ T)
    (hS : IsSylowTwoOf (T ⊓ A) A) {a : G} (ha : a ∈ A)
    (haN : a ∈ Subgroup.normalizer ((T ⊓ A : Subgroup G) : Set G)) :
    a ∈ Subgroup.normalizer ((T ⊓ (A ⊔ B) : Subgroup G) : Set G) := by
  have hC2 : IsPGroup 2 ↥(A ⊓ B) := hT.to_le hC
  refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨hyT, hyAB⟩ := hy
  have hmul : y ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hBA]
    exact hyAB
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_mul.mp hmul
  have hcT : c ∈ T := mem_of_mul_mem hAB hBA hT hC2 hS hc hd hyT
  have hdT : d ∈ T := by
    have := T.mul_mem (T.inv_mem hcT) hyT
    simpa using this
  have h1 : a * c * a⁻¹ ∈ T ⊓ A := (Subgroup.mem_normalizer_iff.mp haN c).mp ⟨hcT, hc⟩
  have hdB : a * d * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hAB ha) d).mp hd
  have he : a * d * a⁻¹ * d⁻¹ ∈ A ⊓ B := by
    refine ⟨?_, B.mul_mem hdB (B.inv_mem hd)⟩
    have h3 : d * a⁻¹ * d⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hBA hd) a⁻¹).mp (A.inv_mem ha)
    have : a * d * a⁻¹ * d⁻¹ = a * (d * a⁻¹ * d⁻¹) := by group
    rw [this]
    exact A.mul_mem ha h3
  have h2 : a * d * a⁻¹ ∈ T := by
    have : a * d * a⁻¹ = (a * d * a⁻¹ * d⁻¹) * d := by group
    rw [this]
    exact T.mul_mem (hC he) hdT
  have hsplit : a * (c * d) * a⁻¹ = (a * c * a⁻¹) * (a * d * a⁻¹) := by group
  rw [hsplit]
  exact ⟨T.mul_mem h1.1 h2,
    (A ⊔ B).mul_mem (Subgroup.mem_sup_left h1.2) (Subgroup.mem_sup_right hdB)⟩

end CFSG.Quasithin.F146Field.Case1

module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHom

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem forall_mulVec_eq_zero_iff_mem_of_le_radNil {n : ℕ}
    {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))} (h𝒜 : 𝒜 ≤ radNil n D)
    (hk : (n - (Module.finrank (ZMod 2) D + 1)) * Module.finrank (ZMod 2) D <
      Module.finrank (ZMod 2) 𝒜) (x : Fin n → ZMod 2) :
    (∀ N ∈ 𝒜, N *ᵥ x = 0) ↔ x ∈ D := by
  refine ⟨fun hx => ?_, fun hx N hN => (mem_radNil.1 (h𝒜 hN)).2 x hx⟩
  by_contra hxD
  have hle : 𝒜 ≤ homMat n D (D ⊔ Submodule.span (ZMod 2) {x}) := by
    intro N hN
    refine mem_homMat.2 ⟨(mem_radNil.1 (h𝒜 hN)).1, fun u hu => ?_⟩
    obtain ⟨d, hd, s, hs, rfl⟩ := Submodule.mem_sup.1 hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
    rw [Matrix.mulVec_add, (mem_radNil.1 (h𝒜 hN)).2 d hd, Matrix.mulVec_smul, hx N hN, smul_zero,
      add_zero]
  have h1 := Submodule.finrank_mono hle
  rw [finrank_homMat] at h1
  have hlt : D < D ⊔ Submodule.span (ZMod 2) {x} := by
    refine lt_of_le_of_ne le_sup_left fun h => hxD ?_
    rw [h]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 : n - Module.finrank (ZMod 2) ↥(D ⊔ Submodule.span (ZMod 2) {x}) ≤
      n - (Module.finrank (ZMod 2) D + 1) := Nat.sub_le_sub_left h2 n
  have h4 := Nat.mul_le_mul_right (Module.finrank (ZMod 2) D) h3
  exact absurd (lt_of_lt_of_le hk (h1.trans h4)) (lt_irrefl _)

theorem span_mulVec_eq_of_le_radNil {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))} (h𝒜 : 𝒜 ≤ radNil n D)
    (hk : (n - Module.finrank (ZMod 2) D) * (Module.finrank (ZMod 2) D - 1) <
      Module.finrank (ZMod 2) 𝒜) :
    Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ a : Fin n → ZMod 2, y = N *ᵥ a} = D := by
  have hSD : Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ a : Fin n → ZMod 2, y = N *ᵥ a} ≤ D := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨N, hN, a, rfl⟩
    exact (mem_radNil.1 (h𝒜 hN)).1 a
  by_contra hne
  have hlt := lt_of_le_of_ne hSD hne
  have hle : 𝒜 ≤ homMat n
      (Submodule.span (ZMod 2) {y | ∃ N ∈ 𝒜, ∃ a : Fin n → ZMod 2, y = N *ᵥ a}) D := by
    intro N hN
    exact mem_homMat.2 ⟨fun a => Submodule.subset_span ⟨N, hN, a, rfl⟩,
      fun u hu => (mem_radNil.1 (h𝒜 hN)).2 u hu⟩
  have h1 := Submodule.finrank_mono hle
  rw [finrank_homMat] at h1
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 := Nat.mul_le_mul_left (n - Module.finrank (ZMod 2) D) (Nat.le_sub_one_of_lt h2)
  exact absurd (lt_of_lt_of_le hk (h1.trans h3)) (lt_irrefl _)

end CFSG.ASVolI.ChH

module

public import CFSG.Quasithin.Background.B1MoreElevenA

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B1Red
open scoped commutatorElement

theorem eq_of_central_ratio {P : Type*} [Group P] (hP : commutator P = ⊤) (φ : P →* P)
    (h : ∀ x, φ x * x⁻¹ ∈ Subgroup.center P) (x : P) : φ x = x := by
  have hcomm : ∀ a b : P, φ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    obtain ⟨z₁, hz₁, ha⟩ : ∃ z₁ ∈ Subgroup.center P, φ a = z₁ * a :=
      ⟨φ a * a⁻¹, h a, by group⟩
    obtain ⟨z₂, hz₂, hb⟩ : ∃ z₂ ∈ Subgroup.center P, φ b = z₂ * b :=
      ⟨φ b * b⁻¹, h b, by group⟩
    have k1 : ∀ g : P, z₁ * g * z₁⁻¹ = g := fun g => by
      rw [← Subgroup.mem_center_iff.1 hz₁ g]; group
    have k2 : ∀ g : P, z₂ * g * z₂⁻¹ = g := fun g => by
      rw [← Subgroup.mem_center_iff.1 hz₂ g]; group
    rw [map_commutatorElement, ha, hb]
    calc ⁅z₁ * a, z₂ * b⁆ = (z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹) * b⁻¹ * z₂⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a * z₂ * b * a⁻¹ * b⁻¹ * z₂⁻¹ := by rw [k1]
      _ = a * (z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹) := by group
      _ = a * (b * a⁻¹ * b⁻¹) := by rw [k2]
      _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group
  have hle : commutator P ≤ φ.eqLocus (MonoidHom.id P) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact hcomm g₁ g₂
  have hx : x ∈ φ.eqLocus (MonoidHom.id P) := hle (by rw [hP]; trivial)
  exact hx

section FStar

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem quasithinGenFitting_eq_of_two_group_quot {Y L : Subgroup Ω} (hLY : L ≤ Y)
    (hn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hL : CFSG.Open.IsQuasisimple ↥L ∨ Group.IsNilpotent ↥L)
    (h2 : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ L) (hO2 : pCoreOf 2 Y = ⊥) :
    quasithinGenFitting Y = L := by
  have hmem : ∀ {x : Ω} {k : ℕ}, x ^ 2 ^ k ∈ L → Odd (orderOf x) → x ∈ L := by
    intro x k hxk ho
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 ho)
    exact (Subgroup.zpowers_le.2 hxk) (A4.mem_zpowers_pow_of_coprime hcop)
  have hnormal : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff hLY).2 fun l y hl hy => hn y hy l hl
  apply le_antisymm
  · unfold quasithinGenFitting
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNY, hNn, hNnil⟩ x hx
      have hn' : ∀ y ∈ Y, ∀ z ∈ N, y * z * y⁻¹ ∈ N := by
        intro y hy z hz
        have := hNn.conj_mem ⟨z, hNY hz⟩ (by rw [Subgroup.mem_subgroupOf]; exact hz) ⟨y, hy⟩
        rw [Subgroup.mem_subgroupOf] at this
        simpa using this
      have hodd := odd_orderOf_of_nilpotent_normal hNY hn' hO2 x hx
      obtain ⟨k, hk⟩ := h2 x (hNY hx)
      exact hmem hk hodd
    · rintro K ⟨hKY, -, hKq⟩ k hk
      have hperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
      have h1 : K ≤ oTwoUpper Y := perfect_le_oTwoUpper' hKY hperf
      exact (oTwoUpper_le_of_pow_mem h2) (h1 hk)
  · rcases hL with hq | hnil
    · refine le_sup_of_le_right (le_sSup ⟨hLY, ?_, hq⟩)
      exact IsSubnormal.step hLY hnormal (IsSubnormal.refl _)
    · exact le_sup_of_le_left (le_sSup ⟨hLY, hnormal, hnil⟩)

end FStar

end CFSG.Quasithin.C124

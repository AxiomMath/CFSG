module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

@[expose] def NoACentral (A B : Subgroup D) : Prop :=
  ∀ c ∈ centerOf (A ⊓ B), c ^ 2 = 1 → (∀ a ∈ A, a * c * a⁻¹ = c) → c = 1

variable [Finite D]

theorem NoACentral.natural_of_moved (h : GoldHyp A B) (hA : NoACentral A B) {ω : D}
    (hωZ : ω ∈ centerOf (A ⊓ B)) (hω2 : ω ^ 2 = 1) (hmove : ∃ g ∈ A, g * ω * g⁻¹ ≠ ω) :
    ∃ (x : D) (V' : Subgroup D), x ∈ A ∧ x * x * x = 1 ∧ x * ω * x⁻¹ ≠ ω ∧
      IsNaturalAt A (A ⊓ B) ω V' := by
  obtain ⟨x, ν, V', hxA, hx3, hxω, hν, hn, -⟩ :=
    exists_natural_data h.vertex_left hωZ hω2 hmove
  have hνZ : ν ∈ centerOf (A ⊓ B) := hn.z_mem
  have hν2 : ν * ν = 1 := by have := hn.z_sq; rwa [pow_two] at this
  have hω2' : ω * ω = 1 := by rwa [pow_two] at hω2
  have hcomm : ω * ν = ν * ω := Subgroup.mem_centralizer_iff.mp hνZ.2 ω hωZ.1
  have hsZ : ω * ν ∈ centerOf (A ⊓ B) := (centerOf (A ⊓ B)).mul_mem hωZ hνZ
  have hs2 : (ω * ν) ^ 2 = 1 := by
    rw [pow_two]
    calc ω * ν * (ω * ν) = ω * (ν * ω) * ν := by group
      _ = ω * (ω * ν) * ν := by rw [← hcomm]
      _ = (ω * ω) * (ν * ν) := by group
      _ = 1 := by rw [hω2', hν2]; group
  have e1 : x * (ω * ν) * x⁻¹ = (x * ω * x⁻¹) * (x * (x * ω * x⁻¹) * x⁻¹) *
      (x * (x * x * ω * (x * x)⁻¹) * x⁻¹) := by rw [hν]; group
  have e2 : x * (x * ω * x⁻¹) * x⁻¹ = x * x * ω * (x * x)⁻¹ := by group
  have e3 : x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = ω := by
    have : x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = (x * x * x) * ω * (x * x * x)⁻¹ := by group
    rw [this, hx3]; group
  have hsx : x * (ω * ν) * x⁻¹ = ω * ν := by
    rw [e1, e2, e3]
    calc (x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹) * ω = ν * ω := by rw [hν]
      _ = ω * ν := hcomm.symm
  have hx1 : x ≠ 1 := fun e => hxω (by rw [e]; group)
  have hxord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three']; exact hx3) hx1
  have hsup : A ⊓ B ⊔ Subgroup.zpowers x = A := by
    have h1 := GoldAmN.inf_sup_zpowers_eq_right_vTriple
      h.symm.amalgam.toIsGoldschmidtVTriple hxA hxord
    rwa [inf_comm] at h1
  have hle : A ⊓ B ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({ω * ν} : Set D) := by
    refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      rw [Set.mem_singleton_iff.mp hu]
      exact (Subgroup.mem_centralizer_iff.mp hsZ.2 t ht).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      rw [Set.mem_singleton_iff.mp hu]
      exact (mul_eq_of_conj_eq hsx).symm
  have hsA : ∀ a ∈ A, a * (ω * ν) * a⁻¹ = ω * ν := by
    intro a ha
    have hax : a ∈ A ⊓ B ⊔ Subgroup.zpowers x := by rw [hsup]; exact ha
    have hc : a * (ω * ν) = (ω * ν) * a :=
      (Subgroup.mem_centralizer_iff.mp (hle hax) (ω * ν) rfl).symm
    calc a * (ω * ν) * a⁻¹ = (ω * ν) * a * a⁻¹ := by rw [hc]
      _ = ω * ν := by group
  have hs1 : ω * ν = 1 := hA _ hsZ hs2 hsA
  have hνω : ν = ω := by
    have : ν = ω⁻¹ := by
      calc ν = ω⁻¹ * (ω * ν) := by group
        _ = ω⁻¹ := by rw [hs1, mul_one]
    rw [this]
    exact inv_eq_of_mul_eq_one_right hω2'
  exact ⟨x, V', hxA, hx3, hxω, hνω ▸ hn⟩

theorem NoACentral.false_of_moved_moved (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hA : NoACentral A B) {ω : D} (hωZ : ω ∈ centerOf (A ⊓ B)) (hω2 : ω ^ 2 = 1)
    (hmoveA : ∃ g ∈ A, g * ω * g⁻¹ ≠ ω) (hmoveB : ∃ y ∈ B, y * ω * y⁻¹ ≠ ω) : False := by
  obtain ⟨x, V₁, -, -, -, hn₁⟩ := hA.natural_of_moved h hωZ hω2 hmoveA
  obtain ⟨y, μ, V₂, -, -, -, -, hn₂, -⟩ := exists_natural_data h.vertex_right hωZ hω2 hmoveB
  have hμA : ∃ g ∈ A, g * μ * g⁻¹ ≠ μ := by
    by_contra hcon
    push Not at hcon
    exact hn₂.z_ne (hA μ hn₂.z_mem hn₂.z_sq hcon)
  have h32' : 32 ≤ Nat.card ↥(B ⊓ A) := by rwa [inf_comm]
  have hn₂' : IsNaturalAt B (B ⊓ A) μ V₂ := by rw [inf_comm]; exact hn₂
  exact GoldAmLab6.false_of_twoNat
    ⟨h, h32, hn₁, hn₂, hn₁.le_pCoreOf_of_large h h32, hn₂'.le_pCoreOf_of_large h.symm h32',
      hmoveB, hμA⟩

theorem NoACentral.centralizes_of_involution (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hA : NoACentral A B) {ω : D} (hωZ : ω ∈ centerOf (A ⊓ B)) (hω2 : ω ^ 2 = 1) :
    ∀ y ∈ B, y * ω * y⁻¹ = ω := by
  by_contra hcon
  push Not at hcon
  by_cases hω1 : ω = 1
  · obtain ⟨y, -, hy⟩ := hcon
    exact hy (by rw [hω1]; group)
  · have hmoveA : ∃ g ∈ A, g * ω * g⁻¹ ≠ ω := by
      by_contra hc
      push Not at hc
      exact hω1 (hA ω hωZ hω2 hc)
    exact hA.false_of_moved_moved h h32 hωZ hω2 hmoveA hcon

end GoldAmL3

end F6

end CFSG.Quasithin

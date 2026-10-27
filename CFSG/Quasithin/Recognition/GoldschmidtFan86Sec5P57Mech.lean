module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PEdge
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P57

variable (F : FanTree Γ G)
include F

theorem mech {v p q : V} (hvp : Γ.Adj v p) (hvq : Γ.Adj v q) {z w : G} (hz2 : z * z = 1)
    (hw2 : w * w = 1) (hzK : z ∈ nbrStab Γ G v)
    (hzc : ∀ h : G, h • p = p → h • v = v → h * z = z * h)
    (hwv : w • v = v) (hwq : w • q = q) (hwK : w ∉ nbrStab Γ G v) :
    z * (w * z * w⁻¹) * (z * (w * z * w⁻¹)) = 1 ∧
      ∀ g : G, g • v = v → g • q = q → (g * g ∈ nbrStab Γ G v ∨ valence Γ v = 3) →
        g * (z * (w * z * w⁻¹)) = z * (w * z * w⁻¹) * g := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hww : w⁻¹ * w⁻¹ = 1 := by rw [hwinv, hw2]
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : G, z₁ = w * z * w⁻¹ := ⟨_, rfl⟩
  rw [← hz₁]
  have hz₁K : z₁ ∈ nbrStab Γ G v := by
    have h := (F.mem_nbrStab_smul_iff w v (h := z₁)).2 (by
      rw [hz₁, show w⁻¹ * (w * z * w⁻¹) * w = z by group]; exact hzK)
    rwa [hwv] at h
  have hz₁p : z₁ • p = p := mem_nbrStab.1 hz₁K p hvp
  have hz₁v : z₁ • v = v := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer v hz₁K)
  have hcomm : z₁ * z = z * z₁ := hzc z₁ hz₁p hz₁v
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [hz₁]
    calc w * z * w⁻¹ * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hu2 : z * z₁ * (z * z₁) = 1 := by
    calc z * z₁ * (z * z₁) = z * (z₁ * z) * z₁ := by group
      _ = z * (z * z₁) * z₁ := by rw [hcomm]
      _ = (z * z) * (z₁ * z₁) := by group
      _ = 1 := by rw [hz2, hz₁2]; simp
  refine ⟨hu2, fun g hgv hgq hg => ?_⟩
  have hKcomm : ∀ k ∈ nbrStab Γ G v, k * (z * z₁) = z * z₁ * k := by
    intro k hk
    have hkp : k • p = p := mem_nbrStab.1 hk p hvp
    have hkv : k • v = v := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer v hk)
    have e1 : k * z = z * k := hzc k hkp hkv
    have hk' : w⁻¹ * k * w ∈ nbrStab Γ G v :=
      (F.mem_nbrStab_smul_iff w v (h := k)).1 (by rwa [hwv])
    have e2 : w⁻¹ * k * w * z = z * (w⁻¹ * k * w) :=
      hzc _ (mem_nbrStab.1 hk' p hvp)
        (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer v hk'))
    have e3 : k * z₁ = z₁ * k := by
      rw [hz₁]
      calc k * (w * z * w⁻¹) = w * ((w⁻¹ * k * w) * z) * w⁻¹ := by group
        _ = w * (z * (w⁻¹ * k * w)) * w⁻¹ := by rw [e2]
        _ = w * z * w⁻¹ * k := by group
    calc k * (z * z₁) = (k * z) * z₁ := by group
      _ = (z * k) * z₁ := by rw [e1]
      _ = z * (k * z₁) := by group
      _ = z * (z₁ * k) := by rw [e3]
      _ = z * z₁ * k := by group
  have hwz₁ : w * z₁ * w⁻¹ = z := by
    rw [hz₁]
    calc w * (w * z * w⁻¹) * w⁻¹ = (w * w) * z * (w⁻¹ * w⁻¹) := by group
      _ = z := by rw [hw2, hww]; group
  have hwu : w * (z * z₁) = z * z₁ * w := by
    calc w * (z * z₁) = (w * z * w⁻¹) * (w * z₁ * w⁻¹) * w := by group
      _ = z₁ * z * w := by rw [← hz₁, hwz₁]
      _ = z * z₁ * w := by rw [hcomm]
  have hKM : ∀ k ∈ nbrStab Γ G v, k ∈ Subgroup.centralizer ({z * z₁} : Set G) := fun k hk => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKcomm k hk
  have hwM : w ∈ Subgroup.centralizer ({z * z₁} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hwu
  suffices hgM : g ∈ Subgroup.centralizer ({z * z₁} : Set G) by
    rw [Subgroup.mem_centralizer_singleton_iff] at hgM
    exact hgM
  by_cases h3 : valence Γ v = 3
  · rcases F.mem_ker_or hvq.symm h3 hwq hwv hwK hgq hgv with h | h
    · exact hKM g h
    · have := Subgroup.mul_mem _ hwM (hKM _ h)
      simpa using this
  · have hv35 : valence Γ v = 3 ∨ valence Γ v = 5 := F.valence v
    have h5 : valence Γ v = 5 := hv35.resolve_left h3
    have hgg : g * g ∈ nbrStab Γ G v := hg.resolve_right h3
    exact F.gcirc_mem_of_elt hvq h5 hKM hwM hwv hwq hwK
      ⟨⟨MulAction.mem_stabilizer_iff.2 hgv, MulAction.mem_stabilizer_iff.2 hgq⟩, hgg⟩

theorem edgeCirc_cond (ℓ : Line Γ) {i : ℤ} {g : G} (hg : g ∈ ℓ.edgeCirc (G := G) i) :
    (g * g ∈ nbrStab Γ G (ℓ.vert i) ∨ valence Γ (ℓ.vert i) = 3) ∧
      (g * g ∈ nbrStab Γ G (ℓ.vert (i + 1)) ∨ valence Γ (ℓ.vert (i + 1)) = 3) := by
  have hi : valence Γ (ℓ.vert i) = 3 ∨ valence Γ (ℓ.vert i) = 5 := F.valence _
  have hj : valence Γ (ℓ.vert (i + 1)) = 3 ∨ valence Γ (ℓ.vert (i + 1)) = 5 := F.valence _
  have hne : valence Γ (ℓ.vert i) ≠ valence Γ (ℓ.vert (i + 1)) := F.alternating _ _ (ℓ.adj i)
  by_cases h5 : valence Γ (ℓ.vert i) = 5
  · rw [ℓ.edgeCirc_of_five h5] at hg
    exact ⟨Or.inl hg.2, Or.inr (by omega)⟩
  · rw [ℓ.edgeCirc_of_ne_five h5] at hg
    exact ⟨Or.inr (by omega), Or.inl hg.2⟩

end P57

end CFSG.Quasithin.Fan86

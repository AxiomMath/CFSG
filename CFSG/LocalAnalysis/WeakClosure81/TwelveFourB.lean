module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

section FourB

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem b12_TwelveFourB_mem_fixSub_zpowers {ρ : G →* LGL 2 V} {a : G} {v : V} :
    v ∈ fixSub ((zpowers a).map ρ) ↔ ρ a v = v := by
  constructor
  · intro hv
    exact hv (ρ a) (Subgroup.mem_map_of_mem ρ (Subgroup.mem_zpowers a))
  · intro hv g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hmem : a ∈ (MulAction.stabilizer (LGL 2 V) v).comap ρ := hv
    exact Subgroup.zpowers_le.mpr hmem hy

theorem fixSub_eq_of_conj_decomposition {ρ : G →* LGL 2 V} {S A D : Subgroup G} {b : G}
    (hAS : A ≤ S) (hD : D ≤ A.map (MulAut.conj b).toMonoidHom) (hD1 : D ≠ ⊥)
    (hSAC : ∀ s ∈ S, ∃ a ∈ A, ∃ c ∈ A.map (MulAut.conj b).toMonoidHom, s = a * c)
    (hCA : ∀ a ∈ A, a ≠ 1 → fixSub (A.map ρ) = fixSub ((zpowers a).map ρ))
    (hAD : fixSub (A.map ρ) = fixSub (D.map ρ)) :
    fixSub (S.map ρ) = fixSub (A.map ρ) := by
  apply le_antisymm
  · exact fixSub_anti _ _ (Subgroup.map_mono hAS)
  · intro v hv
    obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hD1
    have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
    obtain ⟨a₀, ha₀, hda₀⟩ := hD hdD
    have hda₀' : b * a₀ * b⁻¹ = d := by
      rw [← hda₀]
      simp [MulAut.conj_apply]
    have ha₀1 : a₀ ≠ 1 := by
      rintro rfl
      apply hd1'
      rw [← hda₀']
      group
    have hvD : v ∈ fixSub (D.map ρ) := hAD ▸ hv
    have hdv : ρ d v = v := hvD (ρ d) (Subgroup.mem_map_of_mem ρ hdD)
    have hw : ρ a₀ (ρ b⁻¹ v) = ρ b⁻¹ v := by
      have h1 : ρ d v = ρ b (ρ a₀ (ρ b⁻¹ v)) := by
        rw [← hda₀', map_mul, map_mul]
        rfl
      have h2 : ρ b (ρ a₀ (ρ b⁻¹ v)) = v := h1 ▸ hdv
      have h3 : ρ b⁻¹ (ρ b (ρ a₀ (ρ b⁻¹ v))) = ρ b⁻¹ v := by rw [h2]
      have h4 : ρ b⁻¹ (ρ b (ρ a₀ (ρ b⁻¹ v))) = ρ a₀ (ρ b⁻¹ v) := by
        rw [map_inv]
        exact inv_apply_apply' _ _
      rw [← h4]
      exact h3
    have hwW : ρ b⁻¹ v ∈ fixSub (A.map ρ) := by
      rw [hCA a₀ ha₀ ha₀1, b12_TwelveFourB_mem_fixSub_zpowers]
      exact hw
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := hSAC s hs
    obtain ⟨a', ha', rfl⟩ := hc
    have h5 : ρ a' (ρ b⁻¹ v) = ρ b⁻¹ v := hwW (ρ a') (Subgroup.mem_map_of_mem ρ ha')
    have h6 : ρ b (ρ b⁻¹ v) = v := by
      rw [map_inv]
      exact apply_inv_apply' _ _
    have h7 : ρ a v = v := hv (ρ a) (Subgroup.mem_map_of_mem ρ ha)
    have h8 : ρ (a * (MulAut.conj b).toMonoidHom a') v = v := by
      have : ρ (a * (MulAut.conj b).toMonoidHom a') v = ρ a (ρ b (ρ a' (ρ b⁻¹ v))) := by
        simp [MulAut.conj_apply, map_mul]
      rw [this, h5, h6, h7]
    exact h8

theorem fixSub_zpowers_le_of_trans {ρ : G →* LGL 2 V} {S A : Subgroup G}
    (hCA : ∀ a ∈ A, a ≠ 1 → fixSub (A.map ρ) = fixSub ((zpowers a).map ρ))
    (hW : fixSub (S.map ρ) = fixSub (A.map ρ))
    (htrans : ∀ s ∈ S, s ≠ 1 → ∃ x ∈ normalizer (S : Set G), ∃ a ∈ A, a ≠ 1 ∧ x * a * x⁻¹ = s) :
    ∀ s ∈ S, s ≠ 1 → fixSub ((zpowers s).map ρ) ≤ fixSub (S.map ρ) := by
  intro s hs hs1 v hv
  obtain ⟨x, hxN, a, ha, ha1, rfl⟩ := htrans s hs hs1
  have hv' : ρ (x * a * x⁻¹) v = v := b12_TwelveFourB_mem_fixSub_zpowers.1 hv
  have hw : ρ a (ρ x⁻¹ v) = ρ x⁻¹ v := by
    have h1 : ρ x (ρ a (ρ x⁻¹ v)) = v := by
      have : ρ (x * a * x⁻¹) v = ρ x (ρ a (ρ x⁻¹ v)) := by
        rw [map_mul, map_mul]
        rfl
      rw [← this]
      exact hv'
    have h2 : ρ x⁻¹ (ρ x (ρ a (ρ x⁻¹ v))) = ρ a (ρ x⁻¹ v) := by
      rw [map_inv]
      exact inv_apply_apply' _ _
    rw [← h2, h1]
  have hwS : ρ x⁻¹ v ∈ fixSub (S.map ρ) := by
    rw [hW, hCA a ha ha1, b12_TwelveFourB_mem_fixSub_zpowers]
    exact hw
  rintro _ ⟨y, hy, rfl⟩
  have hxi : x⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hxN
  have hy' : x⁻¹ * y * x ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp hxi y).mp hy
    simpa using this
  have h9 : ρ (x⁻¹ * y * x) (ρ x⁻¹ v) = ρ x⁻¹ v := hwS (ρ (x⁻¹ * y * x))
    (Subgroup.mem_map_of_mem ρ hy')
  have h10 : ρ y v = ρ x (ρ (x⁻¹ * y * x) (ρ x⁻¹ v)) := by
    have : ρ y v = ρ (x * (x⁻¹ * y * x) * x⁻¹) v := by
      congr 2
      group
    rw [this, map_mul, map_mul]
    rfl
  rw [h10, h9, map_inv]
  exact apply_inv_apply' _ _

theorem repQuad_of_fixSub_zpowers_le {ρ : G →* LGL 2 V} {S : Subgroup G}
    (hSsq : ∀ s ∈ S, s * s = 1)
    (h : ∀ s ∈ S, s ≠ 1 → fixSub ((zpowers s).map ρ) ≤ fixSub (S.map ρ)) : RepQuad ρ S := by
  have hneg : ∀ x : V, -x = x := fun x => by
    have h1 : (-1 : ZMod 2) = 1 := by decide
    calc -x = (-1 : ZMod 2) • x := (neg_one_smul (ZMod 2) x).symm
      _ = x := by rw [h1, one_smul]
  have hcomm : commSub (S.map ρ) ≤ fixSub (S.map ρ) := by
    rw [commSub_le_iff]
    rintro _ ⟨s, hs, rfl⟩ v
    by_cases hs1 : s = 1
    · subst hs1
      simp
    · apply h s hs hs1
      rw [b12_TwelveFourB_mem_fixSub_zpowers]
      have h1 : ρ s (ρ s v - v) = v - ρ s v := by
        rw [map_sub]
        have : ρ s (ρ s v) = v := by
          have := congrArg (fun g => g v) (congrArg ρ (hSsq s hs))
          simpa [map_mul] using this
        rw [this]
      rw [h1, ← hneg (ρ s v - v), neg_sub]
  unfold RepQuad
  rw [eq_bot_iff, commSpace_le_iff]
  intro k hk u hu
  have h1 : u ∈ fixSub (S.map ρ) := hcomm hu
  have h2 : k u = u := h1 k hk
  rw [h2, sub_self]
  exact Submodule.zero_mem _

end FourB

end CFSG.LocalAnalysis.WeakClosure81

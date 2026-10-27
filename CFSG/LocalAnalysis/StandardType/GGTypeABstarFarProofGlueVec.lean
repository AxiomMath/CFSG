module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofGlueCtx
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarShape

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Vec

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* G} {x y : G}

theorem ggActsVec_perm_fix {X : Type*} [Group X] {m : ℕ}
    {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) (h2 : (2 : F) = 0)
    (hm : 3 ≤ m) {z : X} {k : Fin m} {τ : Fˣ} (hτ : τ ≠ 1) (hz : GGActsVec φ z (diagAt k τ))
    {π : Equiv.Perm (Fin m)} (hπ : φ (slPerm h2 π) * z * (φ (slPerm h2 π))⁻¹ = z) : π k = k := by
  by_contra hne
  have hp := GGActsVec.conj_perm h2 hz π
  rw [hπ, diagAt_comp_perm] at hp
  have he := GGActsVec.vecEq hker hz hp
  have hs : ({k, π k} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    have hle : ({k, π k} : Finset (Fin m)).card ≤ 2 := by
      have h := Finset.card_insert_le k ({π k} : Finset (Fin m))
      simpa using h
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  obtain ⟨hlk, hlp⟩ := hl
  have h := he k l
  rw [diagAt_apply_self, diagAt_apply_of_ne (Ne.symm hne) τ, diagAt_apply_of_ne hlk τ,
    diagAt_apply_of_ne hlp τ] at h
  simp only [inv_one, mul_one] at h
  exact hτ h

theorem GGFarCtx.exists_y_vec (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ₁ y (diagAt (0 : Fin (n + 1)) τ) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i.val = 0 := ⟨⟨0, by have := hC.three_le; omega⟩, rfl⟩
  obtain ⟨τ, _hy1, hy2⟩ := ggFar_shape_y hC.lifts hC.y_mem hC.y_comm (i := i) hi
  have hi0 : i.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simpa using hi)
  refine ⟨τ, ?_, ?_⟩
  · intro hτ
    have he : GGVecEq (diagAt i.castSucc τ) 1 := by
      rw [hτ, diagAt_one]
      exact GGVecEq.refl 1
    exact hC.y_ne (hC.inj y hC.y_mem (GGActsVec.commute_of_vecEq_one hy2 he) hC.y_comm)
  · rw [hi0] at hy2
    exact hy2

theorem GGFarCtx.exists_x_vec (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ₂ x (diagAt (Fin.last n) τ) := by
  obtain ⟨τ, hτ, _hx1, hx2⟩ := ggFar_shape_x hC.lifts hC.x_mem hC.x_comm hC.x_ncomm
  exact ⟨τ, hτ, hx2⟩

theorem GGFarCtx.exists_vecs₁ (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ ∀ k : Fin (n + 1), ∃ z : G, z ∈ Bs ∧ GGActsVec φ₁ z (diagAt k τ) := by
  obtain ⟨τ, hτ, hy⟩ := hC.exists_y_vec
  refine ⟨τ, hτ, fun k => ?_⟩
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 k
  let P : G := φ₁ (slPerm hC.two π)
  refine ⟨P * y * P⁻¹, ?_, ?_⟩
  · have hP : P ∈ Subgroup.normalizer (Bs : Set G) := hC.perm_mem_normalizer₁ π
    exact (Subgroup.mem_normalizer_iff.mp hP y).mp hC.y_mem
  · have hp := GGActsVec.conj_perm hC.two hy π
    have hk : π 0 = k := Equiv.swap_apply_left 0 k
    rw [diagAt_comp_perm, hk] at hp
    exact hp

theorem GGFarCtx.exists_vecs₂ (hC : GGFarCtx p Bs φ₁ φ₂ x y) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ ∀ k : Fin (n + 1), ∃ z : G, z ∈ Bs ∧ GGActsVec φ₂ z (diagAt k τ) := by
  obtain ⟨τ, hτ, hx⟩ := hC.exists_x_vec
  refine ⟨τ, hτ, fun k => ?_⟩
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap (Fin.last n) k
  let P : G := φ₂ (slPerm hC.two π)
  refine ⟨P * x * P⁻¹, ?_, ?_⟩
  · have hP : P ∈ Subgroup.normalizer (Bs : Set G) := hC.perm_mem_normalizer₂ π
    exact (Subgroup.mem_normalizer_iff.mp hP x).mp hC.x_mem
  · have hp := GGActsVec.conj_perm hC.two hx π
    have hk : π (Fin.last n) = k := Equiv.swap_apply_left (Fin.last n) k
    rw [diagAt_comp_perm, hk] at hp
    exact hp

end Vec

end CFSG.StandardType

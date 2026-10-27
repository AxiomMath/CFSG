module

public import CFSG.Quasithin.Background.FLc2Real
public import CFSG.Quasithin.Background.B5FinWedge
public import CFSG.Quasithin.Background.JonesParshallWedge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mat_tv_mulVec_apply {n : ℕ} {a b : Fin n} (h : a < b) (v : Vt n) (c : Fin n) :
    (mat (tv a b h) *ᵥ v) c = v c + (if c = a then v b else 0) := by
  have hco : mat (tv a b h) = 1 + Matrix.single a b (1 : ZMod 2) :=
    SpecialLinearGroup.transvection_coe h.ne 1
  rw [hco, Matrix.add_mulVec, Pi.add_apply, Matrix.one_mulVec]
  congr 1
  by_cases hc : c = a
  · subst hc
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have : a ≠ c := Ne.symm hc
    simp [Matrix.mulVec, dotProduct, hc, this]

theorem fixed_coord_zero {n : ℕ} {v : Vt n} (hv : ∀ g ∈ Ut n, mat g *ᵥ v = v) (b : Fin n)
    (hb : 1 ≤ (b : ℕ)) : v b = 0 := by
  have hlt : (⟨0, by omega⟩ : Fin n) < b := by
    rw [Fin.lt_def]
    show 0 < (b : ℕ)
    omega
  have h := congrFun (hv (tv ⟨0, by omega⟩ b hlt) (tv_mem_Ut hlt)) ⟨0, by omega⟩
  rw [mat_tv_mulVec_apply] at h
  simpa using h

theorem refl_mulVec_of_supported {n : ℕ} {v : Vt n} (hv : ∀ b : Fin n, 1 ≤ (b : ℕ) → v b = 0)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) (hi2 : 2 ≤ i) :
    mat (reflection n (ZMod 2) i hi1 hin) *ᵥ v = v := by
  have hv' : v = Pi.single (⟨0, by omega⟩ : Fin n) (v ⟨0, by omega⟩) := by
    funext b
    by_cases hb : (b : ℕ) = 0
    · have : b = ⟨0, by omega⟩ := Fin.ext hb
      rw [this]
      simp
    · have hne : b ≠ ⟨0, by omega⟩ := fun h => hb (by rw [h])
      rw [hv b (by omega), Pi.single_eq_of_ne hne]
  have hQ : ¬ (1 = i ∨ 0 = i) := by omega
  have hcol : ∀ a : Fin n, (mat (reflection n (ZMod 2) i hi1 hin)) a ⟨0, by omega⟩ =
      if a = ⟨0, by omega⟩ then 1 else 0 := by
    intro a
    show reflectionMatrix n (ZMod 2) i a ⟨0, by omega⟩ = _
    simp [reflectionMatrix, hQ]
  funext a
  rw [hv']
  rw [Matrix.mulVec_single]
  rw [Pi.smul_apply, Matrix.col_apply, hcol a, MulOpposite.smul_eq_mul_unop]
  by_cases ha : a = ⟨0, by omega⟩
  · subst ha
    simp
  · simp [ha]

theorem fix_nat {n : ℕ} (a : Multiplicative (Vt n)) (ha : ∀ g ∈ Ut n, actM g a = a) :
    ∀ i, ∀ hi : IsNode n i, i ≠ 1 →
      actM (reflection n (ZMod 2) i hi.1 hi.2) a = a := by
  intro i hi hi1
  have hv : ∀ g ∈ Ut n, mat g *ᵥ Multiplicative.toAdd a = Multiplicative.toAdd a := by
    intro g hg
    have := congrArg Multiplicative.toAdd (ha g hg)
    rwa [toAdd_actM] at this
  apply Multiplicative.toAdd.injective
  rw [toAdd_actM]
  exact refl_mulVec_of_supported (fixed_coord_zero hv) hi.1 hi.2 (by have := hi.1; omega)

theorem coord4_actW (g : SLt 4) (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (actW g a)) =
      B5FinWedge.wedgeMat4 (mat g) *ᵥ B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) := by
  show B5FinWedge.wedgeCoord4 (exteriorPower.map 2
    (Matrix.toLin' (((specialLinearGroupEquivStatedSL 4 (ZMod 2) g : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)))) (Multiplicative.toAdd a)) = _
  rw [B5FinWedge.wedgeCoord4_map, specialLinearGroupEquivStatedSL_coe]

theorem coord5_actW (g : SLt 5) (a : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2))) :
    JonesParshall.wedgeCoord (Multiplicative.toAdd (actW g a)) =
      JonesParshall.wedgeMat (mat g) *ᵥ JonesParshall.wedgeCoord (Multiplicative.toAdd a) := by
  show JonesParshall.wedgeCoord (exteriorPower.map 2
    (Matrix.toLin' (((specialLinearGroupEquivStatedSL 5 (ZMod 2) g : GL (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)))) (Multiplicative.toAdd a)) = _
  rw [JonesParshall.wedgeCoord_map, specialLinearGroupEquivStatedSL_coe]

theorem fixW4 : ∀ v : Fin 6 → ZMod 2,
    (∀ a b : Fin 4, a < b →
      B5FinWedge.wedgeMat4 (1 + Matrix.single a b (1 : ZMod 2)) *ᵥ v = v) →
    (B5FinWedge.wedgeMat4 (reflectionMatrix 4 (ZMod 2) 1) *ᵥ v = v) ∧
    (B5FinWedge.wedgeMat4 (reflectionMatrix 4 (ZMod 2) 3) *ᵥ v = v) := by
  decide +kernel

theorem fixW5 : ∀ v : Fin 10 → ZMod 2,
    (∀ a b : Fin 5, a < b →
      JonesParshall.wedgeMat (1 + Matrix.single a b (1 : ZMod 2)) *ᵥ v = v) →
    (JonesParshall.wedgeMat (reflectionMatrix 5 (ZMod 2) 1) *ᵥ v = v) ∧
    (JonesParshall.wedgeMat (reflectionMatrix 5 (ZMod 2) 3) *ᵥ v = v) ∧
    (JonesParshall.wedgeMat (reflectionMatrix 5 (ZMod 2) 4) *ᵥ v = v) := by
  decide +kernel

theorem fix_extSq4 (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)))
    (ha : ∀ g ∈ Ut 4, actW g a = a) :
    ∀ i, ∀ hi : IsNode 4 i, i ≠ 2 → actW (reflection 4 (ZMod 2) i hi.1 hi.2) a = a := by
  intro i hi hi2
  have hfix : ∀ a' b' : Fin 4, a' < b' →
      B5FinWedge.wedgeMat4 (1 + Matrix.single a' b' (1 : ZMod 2)) *ᵥ
        B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) =
      B5FinWedge.wedgeCoord4 (Multiplicative.toAdd a) := by
    intro a' b' h
    have h2 := coord4_actW (tv a' b' h) a
    rw [ha (tv a' b' h) (tv_mem_Ut h)] at h2
    have hco : mat (tv a' b' h) = 1 + Matrix.single a' b' (1 : ZMod 2) :=
      SpecialLinearGroup.transvection_coe h.ne 1
    rw [hco] at h2
    exact h2.symm
  have hres := fixW4 _ hfix
  have hi' : i = 1 ∨ i = 3 := by have := hi.1; have := hi.2; omega
  apply Multiplicative.toAdd.injective
  apply (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).1
  rw [coord4_actW]
  rcases hi' with rfl | rfl
  · exact hres.1
  · exact hres.2

theorem fix_extSq5 (a : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)))
    (ha : ∀ g ∈ Ut 5, actW g a = a) :
    ∀ i, ∀ hi : IsNode 5 i, i ≠ 2 → actW (reflection 5 (ZMod 2) i hi.1 hi.2) a = a := by
  intro i hi hi2
  have hfix : ∀ a' b' : Fin 5, a' < b' →
      JonesParshall.wedgeMat (1 + Matrix.single a' b' (1 : ZMod 2)) *ᵥ
        JonesParshall.wedgeCoord (Multiplicative.toAdd a) =
      JonesParshall.wedgeCoord (Multiplicative.toAdd a) := by
    intro a' b' h
    have h2 := coord5_actW (tv a' b' h) a
    rw [ha (tv a' b' h) (tv_mem_Ut h)] at h2
    have hco : mat (tv a' b' h) = 1 + Matrix.single a' b' (1 : ZMod 2) :=
      SpecialLinearGroup.transvection_coe h.ne 1
    rw [hco] at h2
    exact h2.symm
  have hres := fixW5 _ hfix
  have hi' : i = 1 ∨ i = 3 ∨ i = 4 := by have := hi.1; have := hi.2; omega
  apply Multiplicative.toAdd.injective
  apply (JonesParshall.wedgeCoord_bijective (K := ZMod 2)).1
  rw [coord5_actW]
  rcases hi' with rfl | rfl | rfl
  · exact hres.1
  · exact hres.2.1
  · exact hres.2.2

end CFSG.Quasithin.FLc

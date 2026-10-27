module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldNorm

public section

namespace CFSG.StandardType

namespace LIDUF

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {d : ℕ}

@[expose] def herm (b : K →+* K) (x y : Fin d → K) : K :=
  ∑ k, b (x k) * y k

section Herm

variable (b : K →+* K)

theorem herm_add_right (x y z : Fin d → K) : herm b x (y + z) = herm b x y + herm b x z := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_add_left (x y z : Fin d → K) : herm b (x + y) z = herm b x z + herm b y z := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem herm_smul_right (c : K) (x y : Fin d → K) : herm b x (c • y) = c * herm b x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem herm_smul_left (c : K) (x y : Fin d → K) : herm b (c • x) y = b c * herm b x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem herm_sub_right (x y z : Fin d → K) : herm b x (y - z) = herm b x y - herm b x z := by
  simp only [herm, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem herm_swap (hb : ∀ x, b (b x) = x) (x y : Fin d → K) :
    herm b y x = b (herm b x y) := by
  simp only [herm, map_sum, map_mul, hb]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem herm_map (φ : K →+* K) (hφb : ∀ x, φ (b x) = b (φ x)) (x y : Fin d → K) :
    herm b (fun k => φ (x k)) (fun k => φ (y k)) = φ (herm b x y) := by
  simp only [herm, map_sum, map_mul, hφb]

theorem herm_mulVec {g : Matrix (Fin d) (Fin d) K} (hg : adjM b g * g = 1) (x y : Fin d → K) :
    herm b (g *ᵥ x) (g *ᵥ y) = herm b x y := by
  have h1 : (fun k => b ((g *ᵥ x) k)) = (g.map b) *ᵥ (fun k => b (x k)) := by
    funext k
    exact RingHom.map_mulVec b g x k
  have h2 : herm b (g *ᵥ x) (g *ᵥ y) = ((g.map b) *ᵥ (fun k => b (x k))) ⬝ᵥ (g *ᵥ y) := by
    rw [← h1]
    rfl
  rw [h2, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
  have h3 : (g.map b)ᵀ *ᵥ (g *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec]
    change (adjM b g * g) *ᵥ y = y
    rw [hg, Matrix.one_mulVec]
  rw [h3]
  rfl

end Herm

section Fixed

variable (b : K →+* K) (φ : K →+* K)

@[expose] def semF (A : Matrix (Fin d) (Fin d) K) (x : Fin d → K) : Fin d → K :=
  A *ᵥ (fun k => φ (x k))

theorem semF_add (A : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    semF φ A (x + y) = semF φ A x + semF φ A y := by
  simp only [semF, Pi.add_apply, map_add]
  rw [← Matrix.mulVec_add]
  rfl

theorem semF_smul (A : Matrix (Fin d) (Fin d) K) (c : K) (x : Fin d → K) :
    semF φ A (c • x) = φ c • semF φ A x := by
  simp only [semF, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Matrix.mulVec_smul]
  rfl

theorem semF_sub (A : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    semF φ A (x - y) = semF φ A x - semF φ A y := by
  simp only [semF, Pi.sub_apply, map_sub]
  rw [← Matrix.mulVec_sub]
  rfl

theorem herm_semF (hφb : ∀ x, φ (b x) = b (φ x)) {A : Matrix (Fin d) (Fin d) K}
    (hA : adjM b A * A = 1) (x y : Fin d → K) :
    herm b (semF φ A x) (semF φ A y) = φ (herm b x y) := by
  rw [semF, semF, herm_mulVec b hA, herm_map b φ hφb]

theorem phi_herm_self (hφb : ∀ x, φ (b x) = b (φ x)) {A : Matrix (Fin d) (Fin d) K}
    (hA : adjM b A * A = 1) {y : Fin d → K} (hy : semF φ A y = y) :
    φ (herm b y y) = herm b y y := by
  have := herm_semF b φ hφb hA y y
  rw [hy] at this
  exact this.symm

theorem phi_herm (hφb : ∀ x, φ (b x) = b (φ x)) {A : Matrix (Fin d) (Fin d) K}
    (hA : adjM b A * A = 1) {y z : Fin d → K} (hy : semF φ A y = y) (hz : semF φ A z = z) :
    φ (herm b y z) = herm b y z := by
  have := herm_semF b φ hφb hA y z
  rw [hy, hz] at this
  exact this.symm

end Fixed

theorem ne_zero_of_minor {u v : Fin d → K} {i j : Fin d} (h : u i * v j ≠ u j * v i) :
    v ≠ 0 := by
  rintro rfl
  exact h (by simp)

section Isotropic

variable [Finite K] {n : ℕ}

theorem exists_fixed_isotropic (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : orderOf φ = p)
    (hφb : ∀ x, φ (h.bar x) = h.bar (φ x)) {A : Matrix (Fin d) (Fin d) K}
    (hA : adjM h.bar A * A = 1) {u w : Fin d → K}
    (hu : semF (φ : K →+* K) A u = u) (hw : semF (φ : K →+* K) A w = w) {i j : Fin d}
    (hij : u i * w j ≠ u j * w i) :
    ∃ v : Fin d → K, v ≠ 0 ∧ semF (φ : K →+* K) A v = v ∧ herm h.bar v v = 0 ∧
      ∃ s t : K, v = s • u + t • w := by
  classical
  have := h.charP
  set b := h.bar with hbdef
  set φr : K →+* K := (φ : K →+* K) with hφr
  have hb : ∀ x, b (b x) = x := h.bar_bar
  have hφb' : ∀ x, φr (b x) = b (φr x) := hφb
  have hselfbar : ∀ y : Fin d → K, b (herm b y y) = herm b y y :=
    fun y => (herm_swap b hb y y).symm
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hij (by simp)
  by_cases ha : herm b u u = 0
  · exact ⟨u, hu0, hu, ha, 1, 0, by simp⟩
  have hφa : φr (herm b u u) = herm b u u := phi_herm_self b φr hφb' hA hu
  have hφe : φr (herm b u w) = herm b u w := phi_herm b φr hφb' hA hu hw
  set κ : K := herm b u w / herm b u u with hκ
  have hφκ : φr κ = κ := by rw [hκ, map_div₀, hφa, hφe]
  set w' : Fin d → K := w - κ • u with hw'
  have hw'F : semF φr A w' = w' := by
    rw [hw', semF_sub, semF_smul, hu, hw, hφκ]
  have hminor : u i * w' j ≠ u j * w' i := by
    have h1 : u i * w' j - u j * w' i = u i * w j - u j * w i := by
      simp only [hw', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    intro h0
    exact hij (sub_eq_zero.mp (h1.symm.trans (sub_eq_zero.mpr h0)))
  have hortho : herm b u w' = 0 := by
    have h1 : κ * herm b u u = herm b u w := by rw [hκ]; field_simp
    rw [hw', herm_sub_right, herm_smul_right, h1, sub_self]
  have hw'u : herm b w' u = 0 := by rw [herm_swap b hb u w', hortho, map_zero]
  have hφb0 : φr (herm b w' w') = herm b w' w' := phi_herm_self b φr hφb' hA hw'F
  have hbb0 : b (herm b w' w') = herm b w' w' := hselfbar w'
  have hwexp : w' = (-κ) • u + (1 : K) • w := by
    rw [hw']
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  by_cases hb0 : herm b w' w' = 0
  · exact ⟨w', ne_zero_of_minor hminor, hw'F, hb0, -κ, 1, hwexp⟩
  set z : K := herm b w' w' / herm b u u with hz
  have hz0 : z ≠ 0 := div_ne_zero hb0 ha
  have hzb : b z = z := by rw [hz, map_div₀, hbb0, hselfbar u]
  have hzφ : φr z = z := by rw [hz, map_div₀, hφb0, hφa]
  obtain ⟨s, hs0, hsφ, hs⟩ := exists_fixed_normOne h hK hn hp hφ hφb hz0 hzb hzφ
  refine ⟨s • u + w', ?_, ?_, ?_, s - κ, 1, ?_⟩
  · refine ne_zero_of_minor (i := i) (j := j) (u := u) ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    intro h0
    apply hminor
    linear_combination h0
  · rw [semF_add, semF_smul, hu, hw'F, show φr s = s from hsφ]
  · rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_right,
      herm_smul_right, herm_smul_left, hortho, hw'u]
    have h1 : s * b s = z := hs
    have h2 : z * herm b u u = herm b w' w' := by rw [hz]; field_simp
    have h3 : b s * (s * herm b u u) = herm b w' w' := by
      rw [← h2, ← h1]
      ring
    have h4 : herm b w' w' + herm b w' w' = 0 := CharTwo.add_self_eq_zero _
    calc b s * (s * herm b u u) + b s * 0 + (s * 0 + herm b w' w')
        = herm b w' w' + herm b w' w' := by rw [h3]; ring
      _ = 0 := h4
  · rw [hwexp]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

end Isotropic

end LIDUF

end CFSG.StandardType

end

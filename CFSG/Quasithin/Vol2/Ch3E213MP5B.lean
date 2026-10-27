module

public import CFSG.Quasithin.Vol2.Ch3E213MP5A
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k]

variable (k) in
@[expose] def pa1 : Subgroup (projectiveSL 3 k) := (ua1 k).map (proj 3 k)

variable (k) in
@[expose] def pa2 : Subgroup (projectiveSL 3 k) := (ua2 k).map (proj 3 k)

variable (k) in
@[expose] def pzz : Subgroup (projectiveSL 3 k) := (uzz k).map (proj 3 k)

theorem pa1_le : pa1 k ≤ projUnitriangular 3 k := Subgroup.map_mono ua1_le_unitriangular

theorem pa2_le : pa2 k ≤ projUnitriangular 3 k := Subgroup.map_mono ua2_le_unitriangular

theorem pzz_le_pa1 : pzz k ≤ pa1 k := Subgroup.map_mono (ua1_inf_ua2 (k := k) ▸ inf_le_left)

theorem pzz_le_pa2 : pzz k ≤ pa2 k := Subgroup.map_mono (ua1_inf_ua2 (k := k) ▸ inf_le_right)

theorem pa1_inf_pa2 : pa1 k ⊓ pa2 k = pzz k := by
  refine le_antisymm ?_ (le_inf pzz_le_pa1 pzz_le_pa2)
  rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyx⟩⟩
  have h := proj_injOn_unitriangular 3 (ua2_le_unitriangular hy) (ua1_le_unitriangular hx) hyx
  subst h
  exact ⟨y, ua1_inf_ua2 (k := k) ▸ ⟨hx, hy⟩, rfl⟩

theorem uu_comm (a b c c' : k) : uu 0 0 c * uu a b c' = uu a b c' * uu 0 0 c := by
  rw [uu_mul, uu_mul, zero_add, zero_add, add_zero, add_zero, zero_mul, mul_zero, add_zero,
    add_zero, add_comm]

theorem le_or_le_proj [CharP k 2] {W : Subgroup (projectiveSL 3 k)}
    (hW : W ≤ projUnitriangular 3 k) (h2 : ∀ x ∈ W, x * x = 1) : W ≤ pa1 k ∨ W ≤ pa2 k := by
  set W' := W.comap (proj 3 k) ⊓ unitriangular 3 k with hW'
  have hW'map : W'.map (proj 3 k) = W := by
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨x, hx, rfl⟩ := hy
      exact hx.1
    · obtain ⟨x, hx, rfl⟩ := hW hy
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
  have h2' : ∀ x ∈ W', x * x = 1 := by
    intro x hx
    have hm : x * x ∈ unitriangular 3 k ⊓ scalars 3 k :=
      ⟨(unitriangular 3 k).mul_mem hx.2 hx.2,
        proj_eq_one_iff.mp (by rw [map_mul]; exact h2 _ hx.1)⟩
    rwa [unitriangular_inf_scalars, Subgroup.mem_bot] at hm
  rcases le_or_le_of_mul_self (W := W') inf_le_right h2' with h | h
  · exact Or.inl (hW'map ▸ Subgroup.map_mono h)
  · exact Or.inr (hW'map ▸ Subgroup.map_mono h)

theorem mul_self_of_mem_pa1 [CharP k 2] {x : projectiveSL 3 k} (hx : x ∈ pa1 k) : x * x = 1 := by
  obtain ⟨_, ⟨a, c, rfl⟩, rfl⟩ := hx
  rw [← map_mul, uu_mul_self, mul_zero, uu_zero, map_one]

theorem mul_self_of_mem_pa2 [CharP k 2] {x : projectiveSL 3 k} (hx : x ∈ pa2 k) : x * x = 1 := by
  obtain ⟨_, ⟨b, c, rfl⟩, rfl⟩ := hx
  rw [← map_mul, uu_mul_self, zero_mul, uu_zero, map_one]

theorem not_pa1_le_pa2 : ¬ pa1 k ≤ pa2 k := by
  intro h
  obtain ⟨y, ⟨b, c, rfl⟩, hy⟩ := h ⟨uu 1 0 0, ⟨1, 0, rfl⟩, rfl⟩
  have := proj_injOn_unitriangular 3 (uu_mem_unitriangular 0 b c) (uu_mem_unitriangular 1 0 0) hy
  exact one_ne_zero (uu_injective this).1.symm

theorem mem_flagSpace_one {v : Fin 3 → k} : v ∈ flagSpace 3 k 1 ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [mem_flagSpace]
  refine ⟨fun h => ⟨h 1 (by decide), h 2 (by decide)⟩, fun ⟨h1, h2⟩ j hj => ?_⟩
  fin_cases j
  · exact absurd hj (by decide)
  · exact h1
  · exact h2

theorem eq_smul_single_of_mem {v : Fin 3 → k} (hv : v ∈ flagSpace 3 k 1) :
    v = v 0 • Pi.single 0 1 := by
  obtain ⟨h1, h2⟩ := mem_flagSpace_one.1 hv
  funext i
  fin_cases i <;> simp [h1, h2]

theorem uu_mulVec (a b c : k) (v : Fin 3 → k) :
    ((uu a b c : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v =
      ![v 0 + a * v 1 + c * v 2, v 1 + b * v 2, v 2] := by
  funext i
  fin_cases i <;> simp [coe_uu, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mem_ua1_iff {g : Matrix.SpecialLinearGroup (Fin 3) k} :
    g ∈ ua1 k ↔ (g : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧
      ∀ v, (g : Matrix (Fin 3) (Fin 3) k) *ᵥ v - v ∈ flagSpace 3 k 1 := by
  constructor
  · rintro ⟨a, c, rfl⟩
    refine ⟨?_, fun v => ?_⟩
    · rw [uu_mulVec]
      funext i
      fin_cases i <;> simp
    · rw [uu_mulVec, mem_flagSpace_one]
      simp
  · rintro ⟨h0, h⟩
    set G := (g : Matrix (Fin 3) (Fin 3) k) with hG
    have hc : ∀ i j : Fin 3, (G *ᵥ Pi.single j 1) i = G i j := fun i j => by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have h00 : G 0 0 = 1 := by simpa [hc] using congrFun h0 0
    have h10 : G 1 0 = 0 := by simpa [hc] using congrFun h0 1
    have h20 : G 2 0 = 0 := by simpa [hc] using congrFun h0 2
    obtain ⟨h11, h21⟩ := mem_flagSpace_one.1 (h (Pi.single 1 1))
    obtain ⟨h12, h22⟩ := mem_flagSpace_one.1 (h (Pi.single 2 1))
    simp only [Pi.sub_apply, hc] at h11 h21 h12 h22
    refine ⟨G 0 1, G 0 2, Subtype.ext ?_⟩
    rw [coe_uu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hG] <;>
      simp_all [sub_eq_zero]

theorem mulVec_mem_of_mem_stabilizer {g : Matrix.SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ stabilizer (flagSpace 3 k 1)) {v : Fin 3 → k} (hv : v ∈ flagSpace 3 k 1) :
    (g : Matrix (Fin 3) (Fin 3) k) *ᵥ v ∈ flagSpace 3 k 1 := by
  rw [← mem_stabilizer.1 hg]
  exact ⟨v, hv, rfl⟩

theorem coe_mul_coe_inv (g : Matrix.SpecialLinearGroup (Fin 3) k) :
    (g : Matrix (Fin 3) (Fin 3) k) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem conj_mem_ua1 {g x : Matrix.SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ stabilizer (flagSpace 3 k 1)) (hx : x ∈ ua1 k) : g * x * g⁻¹ ∈ ua1 k := by
  obtain ⟨hx0, hx1⟩ := mem_ua1_iff.1 hx
  have hgi : g⁻¹ ∈ stabilizer (flagSpace 3 k 1) := Subgroup.inv_mem _ hg
  set G := (g : Matrix (Fin 3) (Fin 3) k)
  set Gi := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
  set X := (x : Matrix (Fin 3) (Fin 3) k)
  have hGGi : G * Gi = 1 := coe_mul_coe_inv g
  have hcoe : ((g * x * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      G * X * Gi := by simp [G, X, Gi]
  rw [mem_ua1_iff, hcoe]
  refine ⟨?_, fun v => ?_⟩
  · have hw := mulVec_mem_of_mem_stabilizer hgi (v := Pi.single 0 1)
      (mem_flagSpace_one.2 (by simp))
    have hXw : X *ᵥ (Gi *ᵥ Pi.single 0 1) = Gi *ᵥ Pi.single 0 1 := by
      rw [eq_smul_single_of_mem hw, Matrix.mulVec_smul, hx0]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXw, Matrix.mulVec_mulVec, hGGi,
      Matrix.one_mulVec]
  · have h1 := mulVec_mem_of_mem_stabilizer hg (hx1 (Gi *ᵥ v))
    have h2 : G *ᵥ (X *ᵥ (Gi *ᵥ v) - Gi *ᵥ v) = (G * X * Gi) *ᵥ v - v := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hGGi, Matrix.one_mulVec, Matrix.mul_assoc]
    rwa [h2] at h1

theorem projStabilizer_le_normalizer :
    projStabilizer (flagSpace 3 k 1) ≤ Subgroup.normalizer (pa1 k : Set (projectiveSL 3 k)) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x * g⁻¹, conj_mem_ua1 hg hx, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, conj_mem_ua1 (Subgroup.inv_mem _ hg) hx, ?_⟩
    rw [inv_inv, map_mul, map_mul, map_inv, hxy]
    group

end CFSG.Quasithin.Ch3E213M.P5

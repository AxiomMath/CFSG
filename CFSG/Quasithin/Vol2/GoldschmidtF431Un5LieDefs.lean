module

public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.RankThree.PartOne.U5K.Hyp.Aut

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

section Defs

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def z5Y : hypPSU h 2 1 := hypProj h 2 1 (z₁SU h)

@[expose] def t5Y : hypPSU h 2 1 := hypProj h 2 1 (z₂SU h)

@[expose] def v5Y : Subgroup (hypPSU h 2 1) := (Vsub h).map (hypProj h 2 1)

variable {h}

theorem hypProj_eq_of_mem_U {g g' : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (hg' : g' ∈ hypUnitriangular h 2 1) (e : hypProj h 2 1 g = hypProj h 2 1 g') : g = g' := by
  have h1 : g⁻¹ * g' ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  have h3 : g⁻¹ * g' ∈ hypUnitriangular h 2 1 :=
    (hypUnitriangular h 2 1).mul_mem ((hypUnitriangular h 2 1).inv_mem hg) hg'
  have h2 : g⁻¹ * g' ∈ hypUnitriangular h 2 1 ⊓ hypScalars h 2 1 := ⟨h3, h1⟩
  rw [Usub_inf_scalars, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem card_map_hypProj {X : Subgroup (hypSU h 2 1)} (hX : X ≤ hypUnitriangular h 2 1) :
    Nat.card (X.map (hypProj h 2 1)) = Nat.card X := by
  have hinj : Function.Injective ((hypProj h 2 1).comp X.subtype) := fun a b e =>
    Subtype.ext (hypProj_eq_of_mem_U (hX a.2) (hX b.2) e)
  have e := CFSG.RankThree.PartOne.U5K.equivMapOfInjOn (hypProj h 2 1) hinj
  exact (Nat.card_congr e.toEquiv).symm

theorem z5Y_mem_U : z5Y h ∈ hypProjUnitriangular h 2 1 :=
  ⟨z₁SU h, ZPsub_le_U z₁SU_mem_ZPsub, rfl⟩

theorem t5Y_mem_U : t5Y h ∈ hypProjUnitriangular h 2 1 :=
  ⟨z₂SU h, (Z₂Psub_le_A₂sub.trans A₂sub_le_U) z₂SU_mem_Z₂Psub, rfl⟩

theorem z5Y_mem_v5Y : z5Y h ∈ v5Y h := ⟨z₁SU h, ZPsub_le_Vsub z₁SU_mem_ZPsub, rfl⟩

theorem t5Y_mem_v5Y : t5Y h ∈ v5Y h := ⟨z₂SU h, Z₂Psub_le_Vsub z₂SU_mem_Z₂Psub, rfl⟩

theorem v5Y_le_U : v5Y h ≤ hypProjUnitriangular h 2 1 :=
  Subgroup.map_mono (Vsub_le_Ssub.trans Ssub_le_Usub)

theorem v5Y_comm {a b : hypPSU h 2 1} (ha : a ∈ v5Y h) (hb : b ∈ v5Y h) : a * b = b * a := by
  obtain ⟨v, hv, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := hb
  rw [← map_mul, ← map_mul, Vsub_comm hv hw]

theorem v5Y_sq {a : hypPSU h 2 1} (ha : a ∈ v5Y h) : a ^ 2 = 1 := by
  obtain ⟨v, hv, rfl⟩ := ha
  rw [sq, ← map_mul, Vsub_sq hv, map_one]

theorem z5Y_sq : z5Y h * z5Y h = 1 := by
  rw [← sq]
  exact v5Y_sq z5Y_mem_v5Y

theorem t5Y_sq : t5Y h * t5Y h = 1 := by
  rw [← sq]
  exact v5Y_sq t5Y_mem_v5Y

theorem z5Y_ne_one : z5Y h ≠ 1 := fun e => by
  refine z₁SU_ne_one (hypProj_eq_of_mem_U (h := h) (ZPsub_le_U z₁SU_mem_ZPsub) (one_mem _) ?_)
  rw [map_one]
  exact e

theorem t5Y_ne_one : t5Y h ≠ 1 := fun e => by
  have hU : z₂SU h ∈ hypUnitriangular h 2 1 :=
    (Z₂Psub_le_A₂sub.trans A₂sub_le_U) z₂SU_mem_Z₂Psub
  refine z₂SU_ne_one (hypProj_eq_of_mem_U (h := h) hU (one_mem _) ?_)
  rw [map_one]
  exact e

theorem orderOf_z5Y : orderOf (z5Y h) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact z5Y_sq) z5Y_ne_one

theorem orderOf_t5Y : orderOf (t5Y h) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact t5Y_sq) t5Y_ne_one

theorem card_v5Y : Nat.card (v5Y h) = (2 ^ f) ^ 4 := by
  rw [v5Y, card_map_hypProj (Vsub_le_Ssub.trans Ssub_le_Usub), card_Vsub]

end Defs

end CFSG.Quasithin.H13.F431.Un

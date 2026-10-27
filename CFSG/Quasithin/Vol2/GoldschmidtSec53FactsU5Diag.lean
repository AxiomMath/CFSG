module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagBase

public section

namespace CFSG.Quasithin.H13.Sec53F.BA

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Y : Type} [Group Y]

@[expose] def trivSub (U : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {α | (∀ x, α x ∈ U ↔ x ∈ U) ∧
    ∀ b ∈ Subgroup.normalizer (U : Set Y), b⁻¹ * α b ∈ U}
  one_mem' := ⟨fun _ => Iff.rfl, fun b _ => by simp⟩
  mul_mem' {α β} hα hβ := by
    refine ⟨fun x => by rw [MulAut.mul_apply, hα.1, hβ.1], fun b hb => ?_⟩
    have hb' : β b ∈ Subgroup.normalizer (U : Set Y) :=
      (BorelBase.stab_B hβ.1 b).mpr hb
    have h := U.mul_mem (hβ.2 b hb) (hα.2 _ hb')
    simpa [mul_assoc] using h
  inv_mem' {α} hα := by
    refine ⟨fun x => ?_, fun b hb => ?_⟩
    · have h := hα.1 (α⁻¹ x)
      rw [MulAut.apply_inv_self] at h
      exact h.symm
    · have hs : ∀ x, α⁻¹ x ∈ U ↔ x ∈ U := fun x => by
        have h := hα.1 (α⁻¹ x)
        rw [MulAut.apply_inv_self] at h
        exact h.symm
      have hb' : α⁻¹ b ∈ Subgroup.normalizer (U : Set Y) := (BorelBase.stab_B hs b).mpr hb
      have h1 := hα.2 _ hb'
      rw [MulAut.apply_inv_self] at h1
      have := U.inv_mem h1
      simpa [mul_assoc] using this

theorem conj_stab {U : Subgroup Y} {y : Y} (hy : y ∈ Subgroup.normalizer (U : Set Y)) (x : Y) :
    (MulAut.conj y) x ∈ U ↔ x ∈ U := by
  rw [MulAut.conj_apply]
  exact ((Subgroup.mem_normalizer_iff.mp hy) x).symm

theorem BorelBase.comm_mem {U H : Subgroup Y} (D : BorelBase U H) {y b : Y}
    (hy : y ∈ Subgroup.normalizer (U : Set Y)) (hb : b ∈ Subgroup.normalizer (U : Set Y)) :
    b⁻¹ * (y * b * y⁻¹) ∈ U := by
  have hq := D.quot_comm (QuotientGroup.mk ⟨y⁻¹, (Subgroup.normalizer (U : Set Y)).inv_mem hy⟩)
    (QuotientGroup.mk ⟨b, hb⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hq
  convert hq using 1
  simp [mul_assoc]

theorem conj_mem_trivSub {U H : Subgroup Y} (D : BorelBase U H) {y : Y}
    (hy : y ∈ Subgroup.normalizer (U : Set Y)) : MulAut.conj y ∈ trivSub U :=
  ⟨conj_stab hy, fun b hb => by rw [MulAut.conj_apply]; exact D.comm_mem hy hb⟩

end CFSG.Quasithin.H13.Sec53F.BA

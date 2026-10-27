module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.Quasithin.RonanF57

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {K L : Type} [Field K] [Field L]

theorem unitaryFieldData_of_card (hK : Nat.card K = 4) : UnitaryFieldData 2 1 K :=
  ⟨Nat.prime_two, le_rfl, by simpa using hK⟩

theorem finite_of_card_four (hK : Nat.card K = 4) : Finite K :=
  (unitaryFieldData_of_card hK).finite

theorem mem_su4_iff (h : UnitaryFieldData 2 1 K) (A : GL (Fin 4) K) :
    A ∈ StatedSU 4 2 K ↔ (A : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      ((A : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1 :=
  mem_unitarySU_iff h (n := 4) (A := A)

abbrev NSU (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  Subgroup.normalizer ((StatedSU 4 2 K : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K))

theorem mem_NSU_iff {g : GL (Fin 4) K} :
    g ∈ NSU K ↔ ∀ s : GL (Fin 4) K, s ∈ StatedSU 4 2 K ↔ g * s * g⁻¹ ∈ StatedSU 4 2 K :=
  Subgroup.mem_normalizer_iff

theorem mem_NSU_of_map_conj_eq {g : GL (Fin 4) K}
    (hg : (StatedSU 4 2 K).map (MulAut.conj g).toMonoidHom = StatedSU 4 2 K) : g ∈ NSU K := by
  rw [mem_NSU_iff]
  intro s
  constructor
  · intro hs
    rw [← hg]
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  · intro hs
    rw [← hg] at hs
    obtain ⟨s₀, hs₀, he⟩ := hs
    have : s₀ = s := by
      have h1 : g * s₀ * g⁻¹ = g * s * g⁻¹ := by simpa [MulAut.conj_apply] using he
      exact mul_left_cancel (mul_right_cancel h1)
    rwa [← this]

@[expose] def antiDiag4 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  fun row column => if row.val + column.val + 1 = 4 then 1 else 0

end CFSG.Quasithin.RonanF57

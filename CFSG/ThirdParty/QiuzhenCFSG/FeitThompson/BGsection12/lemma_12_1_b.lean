module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_1_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(b). -/
public theorem CFSG.lemma_12_1_b
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃) :
    E₃ ≤ ambientDerivedSubgroup E ∧ section10NormalIn E₃ E := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3⟩
  rcases hE3 with ⟨hE3E, hHallE3⟩
  let π : Set Nat.Primes := section12Tau3Primes M
  let D : Subgroup E := derivedSubgroup E
  let Dπ : Subgroup E := (piCore π D).map D.subtype
  have hnilE : Group.IsNilpotent (ambientDerivedSubgroup E) :=
    lemma_12_1_a (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hM ⟨hcomp, hE12, hE1, hE2, ⟨hE3E, hHallE3⟩⟩
  have hDπHall : IsHallSubgroup π Dπ := by
    simpa [π, D, Dπ] using
      section12_tau3_piCore_hall_in_E (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM
        ⟨hcomp, hE12, hE1, hE2, ⟨hE3E, hHallE3⟩⟩ hnilE
  have hDπ_le_D : Dπ ≤ D := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  haveI : D.Normal := by
    dsimp [D]
    infer_instance
  haveI : (piCore π D).Characteristic := piCore_characteristic π
  haveI : Dπ.Normal := by
    change ((piCore π D).map D.subtype).Normal
    infer_instance
  have hE3eq : E₃.subgroupOf E = Dπ := hDπHall.eq_of_normal hHallE3
  constructor
  · intro x hxE3
    have hxDπ : (⟨x, hE3E hxE3⟩ : E) ∈ Dπ := by
      have hxE3sub : (⟨x, hE3E hxE3⟩ : E) ∈ E₃.subgroupOf E := hxE3
      simpa [hE3eq] using hxE3sub
    have hxD : (⟨x, hE3E hxE3⟩ : E) ∈ derivedSubgroup E := hDπ_le_D hxDπ
    change x ∈ ambientDerivedSubgroup E
    exact Subgroup.mem_map_of_mem E.subtype hxD
  · refine ⟨hE3E, ?_⟩
    rw [hE3eq]
    infer_instance

end Section12

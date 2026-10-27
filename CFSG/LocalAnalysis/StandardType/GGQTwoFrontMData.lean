module

public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Open.Defs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontM_exists_y {D : Subgroup G} {x : G} (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) (hx : x ∈ D) : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
  by_contra h
  push Not at h
  have hle : D ≤ Subgroup.zpowers x := fun y hy => h y hy
  have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h1
  have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 x hx)
  have h3 := Nat.le_of_dvd (by norm_num) h2
  rw [hcard] at h1
  omega

theorem qTwoFrontM_lieModel {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4)
    (e : X ≃* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) : LieModel X .PSU 4 2 1 := by
  have hadm : StatedLieAdmissible .PSU 4 2 1 := by
    refine ⟨Nat.prime_two, le_rfl, ?_⟩
    simp
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hK
  have hmodel := statedClassicalModel_unitary (K := K) 4 1 hK2 hadm
  exact Or.inl ⟨by decide, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel⟩

end CFSG.StandardType.QTwo

end

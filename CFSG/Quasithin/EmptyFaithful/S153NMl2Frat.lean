module

public import CFSG.Quasithin.EmptyFaithful.S153NBase

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]

theorem offenders_le_ffJ_of_not_strong (hW : ∀ v : W, v ^ 2 = 1) {Γ : Subgroup (MulAut W)} {w : W}
    {𝒪 : Set (Subgroup (MulAut W))} (hD : Insp67Data Γ w 𝒪) (hns : ¬ IsStrongFFModule (ffJ Γ)) :
    ∀ B ∈ 𝒪, B ≤ ffJ Γ := by
  intro B hB
  by_cases hB0 : B = ⊥
  · rw [hB0]
    exact bot_le
  · obtain ⟨hBΓ, hel, hcard⟩ := hD.offender B hB
    exact offenders_le_ffJ hW (not_isStrongFFModule_of_ffJ hW hns) hBΓ hB0 hel hcard

theorem frattini_ffJ_of_not_strong (hW : ∀ v : W, v ^ 2 = 1) {Γ : Subgroup (MulAut W)} {w : W}
    {𝒪 : Set (Subgroup (MulAut W))} (hD : Insp67Data Γ w 𝒪) (hns : ¬ IsStrongFFModule (ffJ Γ)) :
    Γ = ffJ Γ ⊔ stabAt Γ w ∧ ∃ S : Subgroup (MulAut W), IsSylowTwoOf S (ffJ Γ) ∧
      Subgroup.normalizer (S : Set (MulAut W)) ⊓ ffJ Γ ≤ stabAt Γ w :=
  hD.frattini (ffJ Γ) (B6.ffJ_le Γ) (ffJ_subgroupOf_normal Γ)
    (offenders_le_ffJ_of_not_strong hW hD hns)

end CFSG.Quasithin.S153N

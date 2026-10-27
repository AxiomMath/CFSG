module

public import CFSG.Sporadic.Co1Patterson.RigidTwist
public import CFSG.Sporadic.Co1Patterson.RigidSplit
public import CFSG.Sporadic.Co1Patterson.TwistNativeBeta
public import CFSG.Sporadic.Co1Patterson.TwistNativeNWC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.LargeExtraspecial.S14 CFSG.EvenSmallLie.OmegaEight TwistNative
open CFSG.Blueprint (NativeSporadic.Co1)


theorem exists_mulEquiv_twistModel : ∃ k : Fin 3,
    Nonempty (centralizer ({aNC} : Set NativeSporadic.Co1) ≃* TM k) := by
  obtain ⟨G⟩ := exists_glue nondeg_bil₀.exists_eq_one typeSystemC typeSystemβ
  have : Group.IsPerfect omegaT := Cover.isPerfect_omegaT
  have : Group.IsPerfect L₀ :=
    Group.IsPerfect.ofSurjective (f := iotaC.symm.toMonoidHom) iotaC.symm.surjective
  rcases split_or_perfect G.π (G.π_surj nondeg_bil₀) (fun _ => G.π_eq_one_iff) with
    ⟨K, hζK, hK⟩ | hE
  · exact absurd (exists_mulEquiv_compat_of_split nondeg_bil₀ G K hζK hK) not_exists_compat
  · obtain ⟨k, ⟨e⟩⟩ := exists_twistModel_of_perfect typeSystemC iotaC hE G.π
      (G.π_surj nondeg_bil₀) G.π_ζ G.ζ_mem_center (fun _ => G.π_eq_one_iff) G.ζ_ne_one
    obtain ⟨e'⟩ := nonempty_mulEquiv_twist nondeg_bil₀ G
    exact ⟨k, ⟨e'.trans e⟩⟩


theorem nonempty_mulEquiv_twistModel_zero :
    Nonempty (centralizer ({aNC} : Set NativeSporadic.Co1) ≃* TM 0) := by
  obtain ⟨k, ⟨e⟩⟩ := exists_mulEquiv_twistModel
  obtain rfl := eq_zero_of_mulEquiv pattersonCo1Hyp_native notWeaklyClosed_native e
  exact ⟨e⟩

theorem nonempty_mulEquiv_centralizer {X : Type} [Group X] [Finite X] {t : X}
    (h : PattersonCo1Hyp X t) (hw : NotWeaklyClosed h) :
    Nonempty (centralizer ({t} : Set X) ≃* centralizer ({aNC} : Set NativeSporadic.Co1)) := by
  rcases centralizer_cases (typeSystemOfHyp h) typeSystemC iotaC with he | ⟨k, ⟨e⟩⟩
  · exact he
  · obtain rfl := eq_zero_of_mulEquiv h hw e
    obtain ⟨e₀⟩ := nonempty_mulEquiv_twistModel_zero
    exact ⟨e.trans e₀.symm⟩

end CFSG.Sporadic.Co1Patterson

module

public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin.S1565

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Module

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem actH_trivial_of_fixed_gens (hF : HypF918 T V L V₁ Vp H K)
    (hfix : ∀ (a : G) (ha : a ∈ Vp) (x : ↥H),
      actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x
          (modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a (le_conjClosure Vp H ha)) =
        modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a (le_conjClosure Vp H ha)) :
    ∀ x : ↥H, actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) x = 1 := by
  have := factElem hF (le_conjClosure Vp H)
  set hUN := hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H) with hUN_def
  have hHU := le_normalizer_conjClosure Vp H
  have key : ∀ u (hu : u ∈ conjClosure Vp H), ∀ x : ↥H,
      actH hF.H_le_normalizer_V₁ hHU x (modMk hUN u hu) = modMk hUN u hu := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hu
      have hzU : z ∈ conjClosure Vp H := le_conjClosure Vp H hz
      have e1 : modMk hUN (k * z * k⁻¹) ((Subgroup.mem_normalizer_iff.mp (hHU hk) z).mp hzU) =
          modMk hUN z hzU :=
        (actH_modMk hF.H_le_normalizer_V₁ hUN hHU ⟨k, hk⟩ hzU).symm.trans (hfix z hz ⟨k, hk⟩)
      intro x
      rw [e1]
      exact hfix z hz x
    | one =>
      intro x
      rw [modMk_one]
      exact map_one _
    | mul u v hu hv ihu ihv =>
      intro x
      rw [modMk_mul hUN hu hv, map_mul, ihu x, ihv x]
    | inv u hu ih =>
      intro x
      rw [modMk_inv hUN hu, map_inv, ih x]
  intro x
  refine MulEquiv.ext fun w => ?_
  obtain ⟨a, haU, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hUN (a : G) haU := Subtype.ext hau.symm
  rw [hw, MulAut.one_apply]
  exact key _ haU x

theorem actH_fix_of_comm (hF : HypF918 T V L V₁ Vp H K) {a : G} (ha : a ∈ Vp) {b : ↥H}
    (hcomm : a * (b : G) * a⁻¹ * (b : G)⁻¹ ∈ V₁) :
    actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
        (modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a (le_conjClosure Vp H ha)) =
      modMk (hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)) a (le_conjClosure Vp H ha) := by
  have := factElem hF (le_conjClosure Vp H)
  set hUN := hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H) with hUN_def
  have haU : a ∈ conjClosure Vp H := le_conjClosure Vp H ha
  rw [actH_modMk hF.H_le_normalizer_V₁ hUN (le_normalizer_conjClosure Vp H) b haU]
  apply Subtype.ext
  show secMk _ _ ⟨(b : G) * a * (b : G)⁻¹, _⟩ = secMk _ _ ⟨a, _⟩
  rw [secMk_eq_secMk_iff]
  exact (comm_mem_iff_conj (hUN haU)).mp hcomm

end Module

end CFSG.Quasithin.S1565

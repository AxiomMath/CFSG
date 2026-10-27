module

public import CFSG.Quasithin.Background.SzG11SB5b
public import CFSG.Quasithin.Background.SzG11B5cConj
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin.G11.SzG11S

open CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem map_conj_subgroupOf {Γ L : Subgroup (GLV V)} (hLΓ : L ≤ Γ) (γ : ↥Γ) :
    ((L.subgroupOf Γ).map (MulAut.conj γ).toMonoidHom).map Γ.subtype =
      L.map (MulAut.conj (γ : GLV V)).toMonoidHom := by
  set A : Subgroup ↥Γ := L.subgroupOf Γ with hA
  have hAmap : A.map Γ.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLΓ
  rw [Subgroup.map_map, ← hAmap, Subgroup.map_map]
  rfl

variable [Finite V]

theorem numConjugates_le_two_of_asA21 (hA21 : AsA21SQTKSection) {Γ L : Subgroup (GLV V)}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hL : IsComponentOf L Γ) : numConjugates Γ L ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := hq
  have : Finite (GLV V) :=
    Finite.of_injective (fun e : GLV V => (e : V → V)) DFunLike.coe_injective
  have hS : {M : Subgroup (GLV V) | ∃ γ ∈ Γ, M = L.map (MulAut.conj γ).toMonoidHom}.Finite :=
    Set.toFinite _
  obtain ⟨M₁, M₂, M₃, ⟨γ₁, hγ₁, rfl⟩, ⟨γ₂, hγ₂, rfl⟩, ⟨γ₃, hγ₃, rfl⟩, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff hS).1 hcon
  have hKc : CFSG.IsComponent (L.subgroupOf Γ) :=
    (CFSG.isComponent_iff_open _).2 (isComponentOf_iff_subgroupOf.1 hL).2
  let y : Fin 3 → ↥Γ := ![⟨γ₁, hγ₁⟩, ⟨γ₂, hγ₂⟩, ⟨γ₃, hγ₃⟩]
  refine B5c.not_three_conjugates hA21 ⟨hst, hkg⟩ φ hφ hKc y ?_
  intro i j hij h
  have h' := congrArg (Subgroup.map Γ.subtype) h
  rw [map_conj_subgroupOf hL.1, map_conj_subgroupOf hL.1] at h'
  fin_cases i <;> fin_cases j <;> simp [y] at hij h' ⊢ <;>
    first
    | exact h12 h'
    | exact h13 h'
    | exact h23 h'
    | exact h12 h'.symm
    | exact h13 h'.symm
    | exact h23 h'.symm

theorem g115bPart2_of_asA21 (hA21 : AsA21SQTKSection) : G115bPart2 := by
  intro V _ _ _ B Γ v₁ W X X₀ cx _ ⟨L, hL, hx⟩
  exact ⟨L, hL, hx, numConjugates_le_two_of_asA21 hA21 cx.sqtk hL⟩

end CFSG.Quasithin.G11.SzG11S

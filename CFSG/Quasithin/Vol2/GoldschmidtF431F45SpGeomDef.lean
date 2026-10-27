module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Quad
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisDefs

public section

namespace CFSG.Quasithin.H13.F431.F45

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin

namespace SpGeom

abbrev W (F : Type) := Fin 4 → F

section Basic

variable {F : Type} [Field F]

@[expose] def actLin (g : antiSp F) : W F →ₗ[F] W F := Matrix.mulVecLin (mat g)

theorem actLin_apply (g : antiSp F) (x : W F) : actLin g x = mat g *ᵥ x := rfl

theorem actLin_mul (g h : antiSp F) : actLin (g * h) = actLin g ∘ₗ actLin h := by
  unfold actLin
  rw [mat_mul, Matrix.mulVecLin_mul]

theorem actLin_one : actLin (1 : antiSp F) = LinearMap.id := by
  unfold actLin
  rw [mat_one, Matrix.mulVecLin_one]

theorem actLin_mul_apply (g h : antiSp F) (x : W F) : actLin (g * h) x = actLin g (actLin h x) := by
  rw [actLin_mul]
  rfl

theorem actLin_one_apply (x : W F) : actLin (1 : antiSp F) x = x := by
  rw [actLin_one]
  rfl

theorem actLin_injective (g : antiSp F) : Function.Injective (actLin g) := by
  intro x y h
  have := congrArg (actLin g⁻¹) h
  rwa [← actLin_mul_apply, ← actLin_mul_apply, inv_mul_cancel, actLin_one_apply,
    actLin_one_apply] at this

theorem form_act (g : antiSp F) (x y : W F) :
    minorForm F (actLin g x) (actLin g y) = minorForm F x y := by
  have h := CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mp
    ((mem_antiSp_iff_toLin (g : GL (Fin 4) F)).mp g.2) x y
  simpa [actLin, mat] using h

theorem bf_comm (x y : W F) : minorForm F x y = minorForm F y x := by
  rw [minorForm_apply, minorForm_apply]
  ring

variable [CharP F 2]

theorem bf_self (x : W F) : minorForm F x x = 0 := minorForm_isAlt x

end Basic

section Sets

variable {F : Type} [Field F]

@[expose] def Pt (F : Type) [Field F] : Type :=
  {U : Submodule F (W F) // Module.finrank F U = 1}

@[expose] def Ln (F : Type) [Field F] : Type :=
  {U : Submodule F (W F) // Module.finrank F U = 2 ∧ ∀ x ∈ U, ∀ y ∈ U, minorForm F x y = 0}

@[expose] def mapSub (g : antiSp F) (U : Submodule F (W F)) : Submodule F (W F) :=
  U.map (actLin g)

theorem mapSub_one (U : Submodule F (W F)) : mapSub (1 : antiSp F) U = U := by
  unfold mapSub
  rw [actLin_one, Submodule.map_id]

theorem mapSub_mul (g h : antiSp F) (U : Submodule F (W F)) :
    mapSub (g * h) U = mapSub g (mapSub h U) := by
  unfold mapSub
  rw [actLin_mul, Submodule.map_comp]

theorem mem_mapSub {g : antiSp F} {U : Submodule F (W F)} {x : W F} :
    x ∈ mapSub g U ↔ ∃ y ∈ U, actLin g y = x :=
  Submodule.mem_map

theorem mapSub_le_iff {g : antiSp F} {U U' : Submodule F (W F)} :
    mapSub g U ≤ mapSub g U' ↔ U ≤ U' :=
  Submodule.map_le_map_iff_of_injective (actLin_injective g) U U'

theorem finrank_mapSub (g : antiSp F) (U : Submodule F (W F)) :
    Module.finrank F (mapSub g U) = Module.finrank F U :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (actLin g) (actLin_injective g) U)).symm

theorem isotropic_mapSub (g : antiSp F) {U : Submodule F (W F)}
    (h : ∀ x ∈ U, ∀ y ∈ U, minorForm F x y = 0) :
    ∀ x ∈ mapSub g U, ∀ y ∈ mapSub g U, minorForm F x y = 0 := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [form_act]
  exact h x hx y hy

instance : MulAction (antiSp F) (Pt F) where
  smul g p := ⟨mapSub g p.1, by rw [finrank_mapSub]; exact p.2⟩
  one_smul p := Subtype.ext (mapSub_one p.1)
  mul_smul g h p := Subtype.ext (mapSub_mul g h p.1)

instance : MulAction (antiSp F) (Ln F) where
  smul g L := ⟨mapSub g L.1, by rw [finrank_mapSub]; exact L.2.1, isotropic_mapSub g L.2.2⟩
  one_smul L := Subtype.ext (mapSub_one L.1)
  mul_smul g h L := Subtype.ext (mapSub_mul g h L.1)

@[expose] def inc (p : Pt F) (L : Ln F) : Prop := p.1 ≤ L.1

theorem inc_smul (g : antiSp F) (p : Pt F) (L : Ln F) : inc (g • p) (g • L) ↔ inc p L :=
  mapSub_le_iff

abbrev Gr (F : Type) [Field F] : SimpleGraph (Pt F ⊕ Ln F) := incGraph inc

instance : GraphAction (antiSp F) (Gr F) where
  adj_smul g a b := by
    cases a <;> cases b
    · exact Iff.rfl
    · exact inc_smul g _ _
    · exact inc_smul g _ _
    · exact Iff.rfl

end Sets

end SpGeom

end CFSG.Quasithin.H13.F431.F45

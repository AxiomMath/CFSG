module

public import CFSG.LieType.Multipliers.G24Bridge
public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalModel
public import Certificates.Data.G24IdentModel

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Fischer
open CFSG.LieType.Multipliers.G24 (adjointEquiv gen)
open CFSG.Quasithin.G2U (ix glHom)
open CFSG.Quasithin.St84.G24Ident (k1 a1 b1 k2 a2 b2 u2 xa xb E1 Z1b N2 Z2b pc1 pc2)

abbrev Y : Type := ↥(adjointGroup .G2 F4)

theorem natCard_F4 : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, F4.card]

@[expose] def toGL : Y →* GL (Fin 14) F4 :=
  (glHom (RingEquiv.refl F4)).comp (adjointGroup .G2 F4).subtype

@[expose] def omegaU : F4ˣ := ⟨F4.ω, F4.ω * F4.ω, rfl, rfl⟩

instance instFiniteY : Finite Y := by
  haveI : Finite (ModGL .G2 F4) := finite_modGL
  exact Subtype.finite

section Elements


@[expose] def xY (i : Fin 2) (c : F4) : Y :=
  ⟨xUnit .G2 F4 (ix i) c, xUnit_mem_adjointGroup _ _⟩

@[expose] def yY (i : Fin 2) (c : F4) : Y :=
  ⟨yUnit .G2 F4 (ix i) c, yUnit_mem_adjointGroup _ _⟩

@[expose] def nY (i : Fin 2) : Y :=
  ⟨weylElt .G2 F4 (ix i) 1, weylElt_mem_adjointGroup _ _⟩

@[expose] def hY (i : Fin 2) : Y :=
  ⟨torusElt .G2 F4 (ix i) omegaU, torusElt_mem_adjointGroup _ _⟩

abbrev T0 : Subgroup Y := posUnipotentSub .G2 F4

abbrev B0 : Subgroup Y := borelSub .G2 F4

abbrev M1 : Subgroup Y := g2ParA F4

abbrev M2 : Subgroup Y := g2ParB F4

end Elements

section Words


@[expose] def agY (w : List (Fin 6 × Bool)) : Y :=
  (adjointEquiv (RingEquiv.refl F4) natCard_F4).symm (FreeGroup.lift gen (FreeGroup.mk w))

@[expose] def k1Y : Y := agY k1
@[expose] def a1Y : Y := agY a1
@[expose] def b1Y : Y := agY b1
@[expose] def k2Y : Y := agY k2
@[expose] def a2Y : Y := agY a2
@[expose] def b2Y : Y := agY b2
@[expose] def xaY : Y := agY xa
@[expose] def xbY : Y := agY xb
@[expose] def pc1Y (j : Fin 10) : Y := agY (pc1.getD j.val [])
@[expose] def pc2Y (j : Fin 10) : Y := agY (pc2.getD j.val [])

@[expose] def gB0 : Fin 4 → Y := ![k1Y, k2Y, xaY, xbY]

@[expose] def A1gen : Fin 3 → Y := ![a1Y, b1Y, k1Y]
@[expose] def A2gen : Fin 3 → Y := ![a2Y, b2Y, k2Y]
@[expose] def A1img : Fin 3 → Y := ![a1Y, b1Y⁻¹, k1Y⁻¹]
@[expose] def A2img : Fin 3 → Y := ![a2Y, b2Y⁻¹, k2Y⁻¹]

abbrev Q1 : Subgroup Y := Subgroup.closure (Set.range pc1Y)
abbrev Q2 : Subgroup Y := Subgroup.closure (Set.range pc2Y)
abbrev A1 : Subgroup Y := Subgroup.closure (Set.range A1gen)
abbrev A2 : Subgroup Y := Subgroup.closure (Set.range A2gen)
abbrev Z1 : Subgroup Y := CFSG.Quasithin.centerOf Q1
abbrev Z2 : Subgroup Y := CFSG.Quasithin.centerOf Q2
abbrev H0 : Subgroup Y := Subgroup.closure {k1Y, k2Y}

@[expose] def pc1Q (j : Fin 10) : ↥Q1 := ⟨pc1Y j, Subgroup.subset_closure ⟨j, rfl⟩⟩
@[expose] def pc2Q (j : Fin 10) : ↥Q2 := ⟨pc2Y j, Subgroup.subset_closure ⟨j, rfl⟩⟩
@[expose] def A1Q (j : Fin 3) : ↥A1 := ⟨A1gen j, Subgroup.subset_closure ⟨j, rfl⟩⟩
@[expose] def A2Q (j : Fin 3) : ↥A2 := ⟨A2gen j, Subgroup.subset_closure ⟨j, rfl⟩⟩
@[expose] def A1imgQ : Fin 3 → ↥A1 := ![A1Q 0, (A1Q 1)⁻¹, (A1Q 2)⁻¹]
@[expose] def A2imgQ : Fin 3 → ↥A2 := ![A2Q 0, (A2Q 1)⁻¹, (A2Q 2)⁻¹]

end Words

end CFSG.Quasithin.F112R.St84.G24M

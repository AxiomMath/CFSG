module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public import CFSG.Sporadic.Mathieu.M22
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Quasithin.Asc94

open CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu

abbrev m22HexadF : Finset (Fin 22) := {0, 1, 2, 9, 17, 19}

abbrev m22H1F : Finset (Fin 22) := {0, 1, 3, 6, 14, 20}

@[expose] def m22F1T : CFSG.Sporadic.Th.Native.Table :=
  #[0, 1, 9, 3, 10, 15, 14, 5, 4, 19, 8, 21, 16, 11, 20, 7, 18, 17, 12, 2, 6, 13]

@[expose] def m22F2T : CFSG.Sporadic.Th.Native.Table :=
  #[0, 1, 19, 3, 5, 4, 6, 21, 16, 17, 11, 10, 15, 18, 14, 12, 8, 9, 13, 2, 20, 7]

@[expose] def m22F1 : Fin 22 → Fin 22 := tf m22F1T

@[expose] def m22F2 : Fin 22 → Fin 22 := tf m22F2T

@[expose] def m22HexadL : List (Fin 22) := [0, 1, 2, 9, 17, 19]

@[expose] def m22Tbar : M22 := m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b *
  m22a * m22b * m22a * m22b * m22a * m22b * m22a

@[expose] def m22I1 : M22 := m22a * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22a

@[expose] def m22I2 : M22 := m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b *
  m22b * m22a * m22b * m22a * m22b * m22b

@[expose] def m22Fix2 : M22 := m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b⁻¹ *
  m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a * m22b⁻¹

@[expose] def m22Fix9 : M22 := m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22a *
  m22b⁻¹ * m22a * m22b * m22a * m22b * m22a

@[expose] def m22Fix17 : M22 := m22a * m22b * m22a * m22b * m22a * m22b⁻¹ * m22a * m22b⁻¹ * m22a

@[expose] def m22Fix19 : M22 := m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b⁻¹ * m22a *
  m22b⁻¹

@[expose] def m22G : M22 := m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b * m22b *
  m22a

@[expose] def m22E1 : M22 := m22b * m22a * m22b * m22a * m22b * m22b * m22a * m22b * m22a * m22b *
  m22a * m22b * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b * m22a * m22b⁻¹ * m22a * m22b * m22b *
  m22a

@[expose] def m22E2 : M22 := m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b *
  m22a * m22b * m22a * m22b⁻¹ * m22a * m22b * m22a * m22b * m22a * m22b * m22a * m22b * m22b *
  m22a * m22b * m22a * m22b⁻¹

abbrev PresHex (σ : Equiv.Perm (Fin 22)) : Prop := ∀ p : Fin 22, σ p ∈ m22HexadF ↔ p ∈ m22HexadF

end CFSG.Quasithin.Asc94

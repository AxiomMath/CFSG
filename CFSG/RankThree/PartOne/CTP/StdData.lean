module

public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.CTP.StdTransport

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.Classical

variable {G : Type} [Group G]

structure StdData (c : G) (f₀ : ℕ) (I K BK : Subgroup G) (J : Fin 3 → Fin 3 → Subgroup G) where
  F : Type
  [fld : Field F]
  [fin : Finite F]
  hF : UnitaryFieldData 2 (5 * f₀) F
  σ : F ≃+* F
  K₀ : Subfield F
  h₀ : UnitaryFieldData 2 f₀ K₀
  Ψ : ↥I →* GL (Fin 3) F
  Ψ_inj : Function.Injective Ψ
  Ψ_range : Ψ.range = unitarySU 2 (5 * f₀) F 3
  σ_order : orderOf σ = 5
  K₀_iff : ∀ x : F, x ∈ K₀ ↔ σ x = x
  bar_eq : ∀ x : K₀, (h₀.bar x : F) = hF.bar x
  Ψ_c : ∀ (x : ↥I) (hx : c * (x : G) * c⁻¹ ∈ I), Ψ ⟨c * x * c⁻¹, hx⟩ = glAut σ (Ψ x)
  tr_K : tr I Ψ K = (unitarySU 2 f₀ K₀ 3).map (subfieldGL K₀ 3)
  tr_BK : tr I Ψ BK = Bst K₀
  tr_J : ∀ (a b : Fin 3) (hab : a ≠ b), tr I Ψ (J a b) = Jst K₀ h₀ hab

attribute [instance] StdData.fld StdData.fin

@[expose] def StdPic (c : G) (f₀ : ℕ) (I K BK : Subgroup G)
    (J : Fin 3 → Fin 3 → Subgroup G) : Prop :=
  Nonempty (StdData c f₀ I K BK J)

end CFSG.RankThree.PartOne.CTP

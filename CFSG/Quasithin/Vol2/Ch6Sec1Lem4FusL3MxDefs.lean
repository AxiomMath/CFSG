module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import CFSG.Quasithin.Vol2.Ch6SL2Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

@[expose] def sl2Of {F : Type} [Field F] (Bl : Subgroup (GL (Fin 2) F)) : Subgroup (GL (Fin 2) F) :=
  Bl ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker

@[expose] noncomputable def sl2BlockL3 {F : Type} [Field F] (Bl : Subgroup (GL (Fin 2) F)) :
    Subgroup (GL (Fin 3) F) :=
  (sl2Of Bl).map blk

structure L3ShapeBase (F : Type) [Field F] [Finite F] (S : Subgroup (GL (Fin 3) F))
    (Bl : Subgroup (GL (Fin 2) F)) (p : ℕ) : Prop where
  charP : CharP F p
  det_one : ∀ A ∈ S, (A : Matrix (Fin 3) (Fin 3) F).det = 1
  neg_mem : negDiag3 F ∈ S
  conj : ∀ s ∈ S, s * s = 1 → s ≠ 1 → ∃ g ∈ S, g⁻¹ * s * g = negDiag3 F
  cent : ∀ A ∈ S, (A * negDiag3 F = negDiag3 F * A ↔ ∃ B ∈ Bl, blk B = A)
  blk_mem : ∀ B ∈ Bl, blk B ∈ S
  derived_eq : ⁅Bl, Bl⁆ = sl2Of Bl
  sl2_perfect : Group.IsPerfect ↥(sl2Of Bl)
  sl2_center : ∀ B : ↥(sl2Of Bl), B ∈ Subgroup.center ↥(sl2Of Bl) ↔
    (blk (B : GL (Fin 2) F) = 1 ∨ blk (B : GL (Fin 2) F) = negDiag3 F)
  sl2_psl : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ∧
    Nonempty (↥(sl2Of Bl) ⧸ Subgroup.center ↥(sl2Of Bl) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)
  scalar_of_commute : ∀ B ∈ Bl, (∀ B' ∈ sl2Of Bl, B * B' = B' * B) →
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c

structure L3Shape (F : Type) [Field F] [Finite F] (S : Subgroup (GL (Fin 3) F))
    (Bl : Subgroup (GL (Fin 2) F)) (p : ℕ) : Prop extends L3ShapeBase F S Bl p where
  exists_inverter : 5 < p → ∀ B ∈ sl2Of Bl, B ^ 5 = 1 → B ≠ 1 →
    ∃ R ∈ Bl, R * R = 1 ∧ (Matrix.GeneralLinearGroup.det R : Fˣ) = -1 ∧ R * B * R⁻¹ = B⁻¹

end CFSG.Quasithin.H13

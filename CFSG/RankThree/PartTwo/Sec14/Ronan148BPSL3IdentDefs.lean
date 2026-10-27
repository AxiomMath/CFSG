module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSTrans
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13

@[expose] def autRestrict {X : Type} [Group X] (K₀ : Subgroup X) (P : Subgroup (MulAut X)) :
    Subgroup (MulAut ↥K₀) where
  carrier := {τ | ∃ σ ∈ P, ∀ z : ↥K₀, (τ z : X) = σ z}
  mul_mem' := by
    rintro τ₁ τ₂ ⟨σ₁, hσ₁, h₁⟩ ⟨σ₂, hσ₂, h₂⟩
    refine ⟨σ₁ * σ₂, P.mul_mem hσ₁ hσ₂, fun z => ?_⟩
    rw [MulAut.mul_apply, h₁, h₂, MulAut.mul_apply]
  one_mem' := ⟨1, P.one_mem, fun _ => rfl⟩
  inv_mem' := by
    rintro τ ⟨σ, hσ, h⟩
    refine ⟨σ⁻¹, P.inv_mem hσ, fun z => ?_⟩
    have hz := h (τ⁻¹ z)
    rw [MulAut.apply_inv_self] at hz
    rw [hz, MulAut.inv_apply_self]

@[expose] def L3Ident148 {X : Type} [Group X] (P : Subgroup (MulAut X)) (K₀ : Subgroup X) :
    Prop :=
  (IsLThreePi ↥K₀ ∧ ∃ E : Subgroup X, E ≤ K₀ ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ K₀, w ∈ Subgroup.normalizer (E : Set X) ∧ w * y₀ * w⁻¹ = y₁) ∧
      ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹) ∨
    PGLModel ↥K₀ (autRestrict K₀ P) ∨
    (Nonempty (↥K₀ ≃* alternatingGroup (Fin 7)) ∧ ∃ E : Subgroup X, E ≤ K₀ ∧ Nat.card E = 9 ∧
      ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹) ∨
    (Subgroup.center ↥K₀ = ⊥ ∧ ∃ E : Subgroup X, E ≤ K₀ ∧
      (∀ e ∈ E, e ≠ 1 → IsPGroup 3 ↥(K₀ ⊓ Subgroup.centralizer ({e} : Set X))) ∧
      ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹)

@[expose] def KF148SigGenL3Ident : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (A L : Subgroup Γ) (b : Γ),
    Late.IsE27 A → b ∈ A → b ≠ 1 → L ≤ Subgroup.centralizer ({b} : Set Γ) →
    A ≤ Subgroup.normalizer (L : Set Γ) →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers b : Set Γ) →
    (∀ x ∈ Subgroup.centralizer (A : Set Γ), x ^ 3 = 1 → x ∈ A) →
    ((b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × Sec12.lBar b L) ∧
        ((IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∧
            (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
              Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∧
            Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 4))) ∨
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
            Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2)))) ∨
      (b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        (Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty (lBarA b L A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
        Nonempty (Sec4.autIn L A ≃* Equiv.Perm (Fin 3))) ∨
      (b ∉ L ∧ Sec8.IsZ3PGLThreePi (lBarA b L A) ∧
        Nonempty (Sec4.autIn L A ≃* Multiplicative (ZMod 3)) ∧
        ∃ x ∈ A, Sec4.InducesTypeOn L x 3)) →
    IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    (∃ (X' : Type) (_ : Group X') (_ : Finite X'), Sec4.IsList46 X' ∧
      Nonempty (X' ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
    L3PointFacts A L b →
    ¬ Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    ∀ (K₀ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
      (Q D : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))),
      Q ≤ (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)).range →
      SigGenHyp (Sec4.autThetaQuot A L) (K₀.map (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →*
        MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L))) Q D →
      K₀ ≠ ⊤ → Group.IsPerfect ↥K₀ →
      IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) →
      Sec4.IsList46 (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) →
      L3Ident148 (Sec4.autThetaQuot A L) K₀

end CFSG.RankThree.PartTwo.Sec14.Ronan148B

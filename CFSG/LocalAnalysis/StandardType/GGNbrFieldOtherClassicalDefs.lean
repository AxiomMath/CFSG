module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGFieldClassicalTag (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def GGTorusSCRank (p k : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → GGTorusSelfCent p A →
      p ^ k ≤ Nat.card A

@[expose] def GGFixDataSC (p r : ℕ) {R : Type} [Group R] (I : Set (MulAut R)) (x : MulAut R) :
    Prop :=
  ∃ (R₀ : Type) (_ : Group R₀) (I₀ : Set (MulAut R₀)) (θ₀ : ggFixDer x ≃* R₀),
    IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ GGFixGeom I x I₀ θ₀ ∧
      GGTorusLift p r R₀ ∧ GGTorusNoLine p r R₀ I₀ ∧ GGTorusSCRank p 3 R₀ I₀

@[expose] def GGNbrWeylRowPlainSC (p r : ℕ) : LargeEvenRawCont :=
  fun R _ I F => GGNbrWeylRowPlain p r R I F ∧
    (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusSCRank p 3 R I)

theorem GGFixDataSC.fixData {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {x : MulAut R}
    (h : GGFixDataSC p r I x) : GGFixData p r I x := by
  obtain ⟨R₀, i₀, I₀, θ₀, hs, hna, hg, hl, hn, -⟩ := h
  exact ⟨R₀, i₀, I₀, θ₀, hs, hna, hg, hl, hn⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

@[expose] def ggK1CBl_Model (nf : ℕ) (K : Type) [Field K] (kind : ggK1CCo_Kind)
    (H : Type) [Group H] : Prop :=
  match kind with
  | .sp s =>
      if s = 1 then Nonempty (H ≃* StatedSp 1 K)
      else if s = 2 ∧ nf = 1 then Nonempty (H ≃* ↥(commutator (StatedSp 2 K)))
      else Nonempty (H ≃* StatedSp s K)
  | .sl m => Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin m) K)
  | .su m => ∃ (E : Type) (_ : Field E) (_ : Fintype E),
      Fintype.card E = (Nat.card K) ^ 2 ∧
        Nonempty (H ≃* ↥(StatedSU m (Nat.card K) E))

theorem ggK1CBl_model_subgroup {nf : ℕ} {K : Type} [Field K] {r : ℕ} {kind : ggK1CCo_Kind}
    (H : Subgroup (StatedSp r K)) :
    ggK1CBl_Model nf K kind ↥H → ggK1CCo_Kind.Model nf kind H := by
  intro h
  exact h

@[expose] def ggK1CBl_KindWitness (nf : ℕ) (K : Type) [Field K] (kind : ggK1CCo_Kind)
    {G : Type} [Group G] (A : Subgroup G) : Prop :=
  match kind with
  | .sl m => 1 ≤ m ∧ Nonempty (↥A ≃* Matrix.GeneralLinearGroup (Fin m) K)
  | .su m =>
      1 ≤ m ∧ ∃ (E : Type) (_ : Field E) (_ : Fintype E)
        (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf E)
        (V : Type) (_ : AddCommGroup V) (_ : Module E V) (_ : FiniteDimensional E V)
        (Hf : V →ₛₗ[hE.bar] V →ₗ[E] E),
        Hf.IsSymm ∧ Hf.SeparatingLeft ∧
          (∃ b : Module.Basis (Fin m) E V,
            ∀ i j, Hf (b i) (b j) = if i = j then 1 else 0) ∧
          Nonempty (↥A ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf)
  | .sp s =>
      1 ≤ s ∧ ∃ (W : Type) (_ : AddCommGroup W) (_ : Module K W) (_ : FiniteDimensional K W)
        (B : LinearMap.BilinForm K W),
        B.IsAlt ∧ B.Nondegenerate ∧ Module.finrank K W = 2 * s ∧
          Nonempty (↥A ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup B)

structure ggK1CBl_PreBlocks (p nf d r : ℕ) (K : Type) [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) where
  ι : Type
  [fintype : Fintype ι]
  A : ι → Subgroup (StatedSp r K)
  kind : ι → ggK1CCo_Kind
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  hjoin : ⨆ i : ι, A i = Subgroup.centralizer ({x} : Set (StatedSp r K))
  hindep : iSupIndep A
  kind_multiset : (Finset.univ : Finset ι).val.map kind = ggK1CCo_expectedKinds p nf d m
  witness : ∀ i : ι, ggK1CBl_KindWitness nf K (kind i) (A i)

end CFSG.StandardType

end

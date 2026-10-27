module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)

variable {G : Type} [Group G] [Finite G]

structure C8SetUp (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (v₀ : IntMod V hV) (T₀ K T' : Subgroup G) : Prop where
  not_le : ¬ centralizer ({v₀.val} : Set G) ≤ D.M
  ne_one : mkTil V₀ V hV v₀ ≠ 1
  e64 : IsE64L3 ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀))
  sylow : IsSylowIn 2 T₀ (D.M ⊓ centralizer ({v₀.val} : Set G))
  mem : Sp6InL D L v₀.val T₀ K
  max : ∀ K' : Subgroup G, Sp6InL D L v₀.val T₀ K' →
    padicValNat 2 (Nat.card ↥(K' ⊓ D.M)) ≤ padicValNat 2 (Nat.card ↥(K ⊓ D.M))
  min : ∀ K' : Subgroup G, Sp6InL D L v₀.val T₀ K' →
    padicValNat 2 (Nat.card ↥(K' ⊓ D.M)) = padicValNat 2 (Nat.card ↥(K ⊓ D.M)) → K' ≤ K →
      K' = K
  sylowM : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M
  sylowK : IsSylowIn 2 (T' ⊓ K) (D.M ⊓ K)

@[expose] def C8Star (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop :=
  ∃ (T' : Subgroup G) (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2))),
    CFSG.ABGLocalTools.IsSylowOf 2 T' D.M ∧
      barSub V₀ V hV T' ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) ∧
      ∀ t ∈ T', t ^ 2 = 1 → ∀ ht : t ∈ stabTil V₀ V,
        actTil V₀ V hV ⟨t, ht⟩ ∈ pullSub ψ (tauSym 3).range

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

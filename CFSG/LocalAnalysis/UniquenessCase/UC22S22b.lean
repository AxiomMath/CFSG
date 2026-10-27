module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Pointwise

section Section22b

variable {G : Type} [Group G] [Finite G]

@[expose] def ConjModule (M V : Subgroup G) {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar M V) Vmod) : Prop :=
  ∀ (m : ↥M) (v w : ↥V), (w : G) = (m : G) * (v : G) * (m : G)⁻¹ →
    e w = Multiplicative.ofAdd (ρ (QuotientGroup.mk m) (Multiplicative.toAdd (e v)))

@[expose] def S22_17 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → ∀ t ∈ D.T, t ∉ normalizer (K : Set G) →
    ∀ (Vmod : Type) [AddCommGroup Vmod] [Module (ZMod 2) Vmod] [Finite Vmod]
      (e : ↥c.V ≃* Multiplicative Vmod) (ρ : Representation (ZMod 2) (MBar D.M c.V) Vmod),
      ConjModule D.M c.V e ρ →
      NatOmegaPlus4 ρ (mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom)) ⊤ ⊥ n ∨
      (commOn ρ (mbarImage D.M c.V K) ⊤ ⊔
          commOn ρ (mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom)) ⊤ = ⊤ ∧
        commOn ρ (mbarImage D.M c.V K) ⊤ ⊓
          commOn ρ (mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom)) ⊤ = ⊥ ∧
        (NatL2 ρ (mbarImage D.M c.V K) (commOn ρ (mbarImage D.M c.V K) ⊤) ⊥ n ∨
          (∃ k : ℕ, n = 2 * k ∧
            (SecSum (fun A B => NatOmegaMinus4 ρ (mbarImage D.M c.V K) A B k) 1
                (commOn ρ (mbarImage D.M c.V K) ⊤) ⊥ ∨
              SecSum (fun A B => NatOmegaMinus4 ρ (mbarImage D.M c.V K) A B k) 2
                (commOn ρ (mbarImage D.M c.V K) ⊤) ⊥)) ∨
          (n = 3 ∧ SecIrr ρ (mbarImage D.M c.V K) (commOn ρ (mbarImage D.M c.V K) ⊤) ⊥ 8)))

@[expose] def S22_18 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → ∀ t ∈ D.T, t ∉ normalizer (K : Set G) →
      mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
        CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M c.V))

@[expose] def S22_fin (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx22b D Ch, ∀ p ∈ D.sig, ∀ (K : Subgroup G) (n : ℕ),
    K2213 D c p K n → ∀ t ∈ D.T, t ∉ normalizer (K : Set G) →
      mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
        CFSG.RankThree.PartOne.pElementSubgroup p (⊤ : Subgroup (MBar D.M c.V)) → False

end Section22b

end CFSG.LocalAnalysis.UniquenessCase.UC22

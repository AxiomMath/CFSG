module

public import CFSG.LocalAnalysis.StandardType.GGD5Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

@[expose] def GGD5LabelDataInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
    ∀ (M : GGQTwoAmbModel p Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι),
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) → M.a = e 0 → M.b ≠ e 2 →
      Submodule.span (ZMod p)
        (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      M.toLin.Basis → lup10d_LabelData p Bs x L J M

@[expose] def GGD5ForcedInput : Prop :=
  lup10fa_TwistFacts → GGLBalanceInput → GGStdSubPrimeInput → GGQTwoCentralizerInput →
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J → GGQTwoI1 Bs D J → x ∉ L →
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
      ((GGQTwoTwoNodeRowAt 3 L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt 3 K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      ¬ Nonempty (GGQTwoModel 3 Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr 3 B x D J y K →
    ∀ (M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι),
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) → M.a = e 0 →
      Submodule.span (ZMod 3)
        (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤ →
      M.toLin.Basis → lup10d_LabelData 3 Bs x L J M → lup10d_SCData Bs J →
      ∀ (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)),
        (∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1) →
        (∀ (i : Fin 5) (v : M.V),
          κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) =
            (lup10fa_s i).mulVec (κ v)) →
        (∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x) →
        ∀ {φ : MulAut ↥Bs}, φ ∈ ggAutomizer ⊤ Bs →
        ∀ (w' : MulAut ↥Bs), w' ∈ ggAutomizer L Bs →
        ∀ (b0 : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c' : ZMod 3),
          lup10fa_Adm b0 γ lam c' → e (lup10ab_tau b0.castSucc) = M.b →
          (∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
            (lup10fa_twist γ lam c').mulVec (κ v)) →
          ∃ r' : MulAut ↥Bs, r' ∈ ggAutomizer (ggG0 3 B x L D J) Bs ∧
            ggLin (p := 3) M.model r' = ggLin (p := 3) M.model (φ * M.simple M.a * φ⁻¹)

end CFSG.StandardType

end

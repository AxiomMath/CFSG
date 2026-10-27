module

public import CFSG.Milestones.ASVolI.F45.Six

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

@[expose] def burnsideF45_C8Body (κ : GLKind) {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) : Prop :=
  ι.PathTrans ι.xv κ.m ∧
    (ι.PathTrans ι.lv (κ.m - 1) ∧
      (∃ q₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, ∃ q₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m,
        GPath.nbPaths ι.graph ι.lv κ.m =
          pathOrbit (stv ι ι.lv) q₁ ∪ pathOrbit (stv ι ι.lv) q₂ ∧
        Disjoint (pathOrbit (stv ι ι.lv) q₁) (pathOrbit (stv ι ι.lv) q₂) ∧
        Nat.card ↥(pathOrbit (stv ι ι.lv) q₁) = Nat.card ↥(pathOrbit (stv ι ι.lv) q₂)) ∧
      ∀ v ∈ CosetGeom.sphere κ.m ι.lv,
        ∀ q₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, q₁ κ.m = v →
        ∀ q₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m, q₂ κ.m = v → q₁ ≠ q₂ →
        ∀ r₁ ∈ GPath.nbPaths ι.graph ι.lv κ.m, r₁ κ.m = v →
        ∀ r₂ ∈ GPath.nbPaths ι.graph ι.lv κ.m, r₂ κ.m = v → r₁ ≠ r₂ →
          ∃ g ∈ stv ι ι.lv ⊓ stv ι v, g • q₁ = r₁ ∧ g • q₂ = r₂)

@[expose] def burnsideF45_C9Body (κ : GLKind) (p : ℕ) {E : Type} [Group E] (Gp : Subgroup E)
    {M₁ M₂ : Subgroup E} (ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂)) : Prop :=
  ∀ u v : ι.Γ, ι.graph.dist u v = κ.m →
    (CosetGeom.vtype u = true →
      IsComplementIn (stv ι u ⊓ stv ι v) (Qu p Gp ι u) (stv ι u)) ∧
    (CosetGeom.vtype u = false →
      Nonempty (↥(stv ι u ⊓ stv ι v) ≃* DihedralGroup 5) ∨
        Nonempty (↥(stv ι u ⊓ stv ι v) ≃* Multiplicative (ZMod 3)))

@[expose] def burnsideF45_ExcKind (κ : GLKind) : Prop :=
  ∀ (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ p f Gp M₁ M₂ →
    (∀ u v : (incl M₁ M₂).Γ, (incl M₁ M₂).graph.Adj u v → burnsideF45_C6Body p Gp M₁ M₂ u v) ∧
    burnsideF45_C8Body κ (incl M₁ M₂) ∧ burnsideF45_C9Body κ p Gp (incl M₁ M₂)

end CFSG.ASVolI

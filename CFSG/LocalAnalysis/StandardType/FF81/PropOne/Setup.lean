module

public import CFSG.LocalAnalysis.StandardType.FF81.LocalSetup

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

structure Counterexample (G : Type) [Group G] [Finite G] (n : ℕ) (b : G) (L : Subgroup G)
    (z : Fin 3 → ↥L) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ x y : G, x * y ≠ y * x
  hypA : HypA G n b L
  model : GGFF.Model ↥L z
  facts : LocalFacts b L z
  noL : ∀ g : G, g * b * g⁻¹ ∉ L

abbrev bOne {G : Type} [Group G] {L : Subgroup G} (z : Fin 3 → ↥L) : Subgroup G :=
  GGFF.tor (GGFF.zs z)

abbrev nB {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) : Subgroup G :=
  Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G)

abbrev cB {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) : Subgroup G :=
  Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G)

abbrev dGrp {G : Type} [Group G] (b : G) {L : Subgroup G} (z : Fin 3 → ↥L) : Subgroup G :=
  Subgroup.zpowers b ⊔ (L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G))

namespace Counterexample

theorem settingCore {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) : GGFF.SettingCore b L z :=
  h.hypA.settingCore h.model

end Counterexample

end CFSG.StandardType.FF81.PropOne

end

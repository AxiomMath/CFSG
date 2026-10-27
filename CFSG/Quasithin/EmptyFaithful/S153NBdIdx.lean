module

public import CFSG.Quasithin.EmptyFaithful.S153NDef
public import CFSG.Quasithin.Background.S1567Z4

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

set_option linter.unusedVariables false in
theorem bridgeD_relIndex (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {W : Type} [CommGroup W]
    (φ : ↥(Subgroup.centralizer (E : Set G)) →* MulAut W)
    (hker : φ.ker = (S1567.K167 T M E).subgroupOf (Subgroup.centralizer (E : Set G))) (w : W)
    (hstab : ∀ c : ↥(Subgroup.centralizer (E : Set G)), φ c ∈ stabAt φ.range w ↔ (c : G) ∈ M) :
    (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) =
      (stabAt φ.range w).relIndex φ.range := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have h1 : (stabAt φ.range w).relIndex φ.range =
      (M.subgroupOf (Subgroup.centralizer (E : Set G))).index := by
    rw [← Subgroup.index_comap]
    congr 1
    ext c
    exact hstab c
  have h2 : (M ⊓ Subgroup.normalizer (E : Set G)).relIndex (Subgroup.normalizer (E : Set G)) =
      (M ⊓ Subgroup.centralizer (E : Set G)).relIndex (Subgroup.centralizer (E : Set G)) := by
    have e1 : (M ⊓ Subgroup.normalizer (E : Set G)) ⊓ Subgroup.centralizer (E : Set G) =
        M ⊓ Subgroup.centralizer (E : Set G) := by
      rw [inf_assoc, inf_eq_right.mpr hCN]
    rw [← e1, S1567.relIndex_inf_eq_relIndex_sup
      (inf_le_right.trans (S1567.normalizer_le_normalizer_CE E)), ← S1567.normalizer_eq_sup k]
  rw [h1, h2, Subgroup.inf_relIndex_right]
  rfl

end CFSG.Quasithin.S153N

module

public import CFSG.Quasithin.Vol2.Ch3T326K

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def T326ActsGlued : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ → L ≠ conjClosure L T →
    ∀ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))),
    ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G)) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) →
      (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) ⊓
        (CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
            Subgroup.centralizer (conjClosure L T : Set G))) =
        conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G) →
      ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
        Subgroup.centralizer (CFSG.conjugate L t : Set G) →
      ¬ (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
          CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t =
          conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
        ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
          CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t = ⊥) →
      ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))))
          (autOn (Subgroup.normalizer (conjClosure L T : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
        ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G))),
          (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
          ((a u : ↥(conjClosure (conjClosure V₀ T)
            (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
            ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆

namespace Ctx

variable {G : Type} [Group G] [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem qhatStar_acts (hA37 : Vol2Native.A37ForSQTKCat) (hA38 : Vol2Native.A38ForSQTKCat)
    (hG : T326ActsGlued) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    [IsMulCommutative ↥(conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)))]
    (h1 : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
        CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G)) =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
    (h2 : (⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G))) ⊓
      (CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t ⊔
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
          Subgroup.centralizer (conjClosure L T : Set G))) =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ⊓
        Subgroup.centralizer (conjClosure L T : Set G))
    (h3 : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ≤
      Subgroup.centralizer (CFSG.conjugate L t : Set G))
    (hrk : 2 < rk ↥((⁅conjClosure (conjClosure V₀ T)
      (Subgroup.normalizer (conjClosure L T : Set G)), L⁆).subgroupOf
        (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))))) :
    ∀ A ∈ QhatStar (V := ↥(conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G))))
        (autOn (Subgroup.normalizer (conjClosure L T : Set G))
          (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))),
      ∀ a ∈ A, ∀ u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G))),
        (u : G) ∈ ⁅conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ →
        ((a u : ↥(conjClosure (conjClosure V₀ T)
          (Subgroup.normalizer (conjClosure L T : Set G)))) : G) ∈
          ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ := by
  by_cases hdir : ⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊔
      CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ∧
    ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ ⊓
      CFSG.conjugate ⁅conjClosure (conjClosure V₀ T)
        (Subgroup.normalizer (conjClosure L T : Set G)), L⁆ t = ⊥
  · exact c.qhatStar_acts_of_direct hA37 hA38 ht htn hdir hrk
  · exact hG G T L V₀ c.fsu c.ne inferInstance t ht htn h1 h2 h3 hdir

end Ctx


end CFSG.Quasithin.H13.T326

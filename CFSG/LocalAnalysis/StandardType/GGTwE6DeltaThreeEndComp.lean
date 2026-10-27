module

public import CFSG.Assembly.LargeEvenDefs
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.Fischer.Classification.Defs
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Layer

variable {G : Type*} [Group G]

theorem isComponentOf_sup_of_centralizes {X D : Subgroup G}
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hD : IsQuasisimple D) :
    IsComponentOf D (X ⊔ D) := by
  have hle : X ⊔ D ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (hXD.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  refine ⟨le_sup_right, IsSubnormal.step le_sup_right ?_ (IsSubnormal.refl _), hD⟩
  rw [Subgroup.normal_subgroupOf_iff le_sup_right]
  intro d k hd hk
  exact (Subgroup.mem_normalizer_iff.1 (hle hk) d).1 hd

theorem eq_of_isComponentOf_sup {X D K : Subgroup G} (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hD : IsQuasisimple D)
    (hK : IsComponentOf K (X ⊔ D)) : K = D := by
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top X).1 hX
  subst hd
  exact CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_sup_zpowers
    (isComponentOf_iff_open.1 hK) rfl hXD hD

theorem layer_sup_eq {X D : Subgroup G} (hX : IsCyclic X)
    (hXD : X ≤ Subgroup.centralizer (D : Set G)) (hD : IsQuasisimple D) :
    LargeEvenLayer (X ⊔ D) = D ∧ IsComponentOf (LargeEvenLayer (X ⊔ D)) (X ⊔ D) := by
  have hcomp := isComponentOf_sup_of_centralizes hXD hD
  have heq : LargeEvenLayer (X ⊔ D) = D :=
    le_antisymm (sSup_le fun K hK => (eq_of_isComponentOf_sup hX hXD hD hK).le) (le_sSup hcomp)
  exact ⟨heq, by rw [heq]; exact hcomp⟩

end Layer

section Cyclic

theorem card_le_three_of_injective_cyclic {C X : Type*} [Group C] [Group X] [Finite X]
    (hX : IsCyclic X) (f : C →* X) (hf : Function.Injective f) (hC : ∀ c : C, c ^ 3 = 1) :
    Nat.card C ≤ 3 := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  have h1 : Nat.card C ≤ Nat.card {a : X // a ^ 3 = 1} :=
    Nat.card_le_card_of_injective (fun c => ⟨f c, by rw [← map_pow, hC c, map_one]⟩)
      fun a b h => hf (congrArg Subtype.val h)
  have h2 : Nat.card {a : X // a ^ 3 = 1} ≤ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  omega

end Cyclic

end CFSG.StandardType.TwE6D3

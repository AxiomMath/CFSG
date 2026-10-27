module

public import CFSG.RankThree.PartOne.FOC.Transfer
public import CFSG.RankThree.PartOne.S11d.PlaneAll
public import CFSG.RankThree.PartOne.FOC.ListBridge

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

namespace FOC

@[expose] def FieldInnerAlt : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (n p : ℕ), 5 ≤ n → p.Prime → 5 ≤ p → IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → Nonempty (T ≃* alternatingGroup (Fin n)) → FieldInnerT p T

@[expose] def FieldInnerSpor : Prop :=
  ∀ (s : TauCeti.SporadicName), s ∈ Census3.sporadicsThm3 → ∀ (T : Type) [Group T] [Finite T] (p : ℕ),
    p.Prime → 5 ≤ p → IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* NativeSporadic.Carrier s) → FieldInnerT p T

@[expose] def FieldInnerLie (t : StatedLieTag) (ℓ : ℕ) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (n f p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → StatedLieAdmissible t n ℓ f → LieModel T t n ℓ f →
    FieldInnerT p T

@[expose] def FieldInnerExc : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (p : ℕ), p.Prime → 5 ≤ p → IsSimpleGroup T →
    (∃ a b : T, a * b ≠ b * a) → ExcListed T → FieldInnerT p T

theorem fieldInnerTCat_of_cases (hAlt : FieldInnerAlt) (hSpor : FieldInnerSpor)
    (hLie : ∀ (t : StatedLieTag) (ℓ : ℕ), t ∈ classicalTags → FieldInnerLie t ℓ)
    (hExc : FieldInnerExc) : FieldInnerTCat := by
  intro T _ _ p hp hp5 hsimple hnonab hlist
  rcases listNative_cases hlist with ⟨n, h5, -, he⟩ | ⟨s, hs, he⟩ | hcl | hexc
  · exact hAlt T n p h5 hp hp5 hsimple hnonab he
  · exact hSpor s hs T p hp hp5 hsimple hnonab he
  · obtain ⟨t, n, ℓ, f, ht, hadm, hmodel⟩ := hcl
    exact hLie t ℓ ht T n f p hp hp5 hsimple hnonab hadm hmodel
  · exact hExc T p hp hp5 hsimple hnonab hexc

@[expose] def CenterCover : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop :=
  fun _ _ _ p J => p ∣ Nat.card (Subgroup.center ↥J) ∧
    p = 5 ∧ Nat.card (Subgroup.center ↥J) = 5 ∧
      ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 n

@[expose] def FieldInnerCenter : Prop := FieldInnerPlaneWith CenterCover

@[expose] def Sec68List : ∀ (H : Type) [Group H] [Finite H], ℕ → Subgroup H → Prop :=
  fun H _ _ p J => Sec68Hyp H p J ∧ ListSec H p J

theorem fieldInnerPlaneWith_sec68_of_cases (hnc : FieldInnerPlaneWith NoPCenterList)
    (hC : FieldInnerCenter) : FieldInnerPlaneWith Sec68List := by
  intro H _ _ p J A c u v E hp hp5 hrank hJq hJcat h68 hAN hAe hAcard hcA hc1 hcC huA hvA huJ hE
    huE hfl
  by_cases hZ : p ∣ Nat.card (Subgroup.center ↥J)
  · exact hC H p J A c u v E hp hp5 hrank hJq hJcat ⟨hZ, h68.1 hZ⟩ hAN hAe hAcard hcA hc1 hcC huA
      hvA huJ hE huE hfl
  · exact hnc H p J A c u v E hp hp5 hrank hJq hJcat ⟨hZ, h68.2⟩ hAN hAe hAcard hcA hc1 hcC huA hvA
      huJ hE huE hfl

end FOC

theorem fieldOnComponentOuter_of_cases
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (h68 : SectionProvider Sec68Hyp) (hlist : FOC.SectionProviderK FOC.ListSec)
    (hAlt : FOC.FieldInnerAlt) (hSpor : FOC.FieldInnerSpor)
    (hLie : ∀ (t : StatedLieTag) (ℓ : ℕ), t ∈ classicalTags → FOC.FieldInnerLie t ℓ)
    (hExc : FOC.FieldInnerExc) (hC : FOC.FieldInnerCenter) : FieldOnComponentOuter :=
  fieldOnComponentOuter_of_planeWithK FOC.Sec68List hbridge
    (FOC.sectionProviderK_and (FOC.sectionProviderK_of_sectionProvider h68) hlist)
    (FOC.fieldInnerPlaneWith_sec68_of_cases
      (FOC.fieldInnerPlaneWith_noCenter_of_T (FOC.fieldInnerTCat_of_cases hAlt hSpor hLie hExc)) hC)

end CFSG.RankThree.PartOne

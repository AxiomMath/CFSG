module

public import CFSG.RankThree.PartOne.S11d.OutTheta
public import CFSG.RankThree.PartOne.S11d.PlaneOdd
public import CFSG.RankThree.PartOne.S11c.Sec66Glue
import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo LocalRankAut innerAut PlaneT Sec66T_K2)

namespace PlaneCases

theorem planeT_of_outer_small {T : Type} [Group T] [Finite T] {p : ℕ} (hp5 : 5 ≤ p)
    (h : Nat.card (Outer T) < 25 ∨ ¬ p ∣ Nat.card (Outer T)) : PlaneT p T := by
  intro _ E _ hcard hEinn _
  let f : E →* Outer T := (QuotientGroup.mk' (inner T)).comp E.subtype
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : MulAut T) ∈ inner T := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (x : MulAut T) ∈ E ⊓ innerAut T := ⟨x.2, h1⟩
    rw [hEinn, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hdvd : Nat.card E ∣ Nat.card (Outer T) := by
    have h1 : Nat.card E = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hcard] at hdvd
  rcases h with hlt | hnd
  · have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
    have := Nat.le_of_dvd hpos hdvd
    nlinarith
  · exact hnd ((dvd_pow_self p two_ne_zero).trans hdvd)

end PlaneCases

@[expose] def SporadicOutSmall : Prop :=
  ∀ s : TauCeti.SporadicName, ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
    (∃ a b : T, a * b ≠ b * a) → Nonempty (T ≃* NativeSporadic.Carrier s) →
      Nat.card (Outer T) < 25 ∨ ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer T)

@[expose] def PlaneCenterP : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H),
    p.Prime → 5 ≤ p → localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
    Catalog (↥J ⧸ Subgroup.center ↥J) → p ∣ Nat.card (Subgroup.center ↥J) →
    A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
    (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False

@[expose] def PlaneCenterP' : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ) (J A : Subgroup H) (c : H),
    p.Prime → 5 ≤ p → localRank p H ≤ 3 → CFSG.IsQuasisimple ↥J →
    Catalog (↥J ⧸ Subgroup.center ↥J) → p ∣ Nat.card (Subgroup.center ↥J) →
    (p = 5 ∧ Nat.card (Subgroup.center ↥J) = 5 ∧
      ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 n) →
    A ≤ Subgroup.normalizer (J : Set H) → IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    c ∈ A → c ≠ 1 → c ∈ Subgroup.centralizer (J : Set H) →
    (∀ x ∈ A, x ∈ J ⊔ Subgroup.centralizer (J : Set H) → x ∈ Subgroup.zpowers c) → False

theorem planeT_of_catalog (hEven : ∀ t : StatedLieTag, Sec66T_K2 t) (hOdd : OddLiePlaneT)
    (hSpor : SporadicOutSmall) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Q : Type} [Group Q]
    [Finite Q] (hQq : CFSG.IsQuasisimple Q) (hQcat : Catalog (Q ⧸ Subgroup.center Q)) :
    PlaneT p (Q ⧸ Subgroup.center Q) := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQq.2.1
  have hnonab := hQq.2.2
  rcases PlaneCases.catalog_cases hQcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ |
    ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  · refine PlaneCases.planeT_of_outer_small hp5 (Or.inl ?_)
    have hcard : Nat.card (Outer (Q ⧸ Subgroup.center Q)) =
        Nat.card (Outer (alternatingGroup (Fin n))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    rw [hcard]
    have := card_outer_alternating_le_four hn5
    omega
  · by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact hEven t _ p hp hp5 ⟨n, f, hadm, hmodel⟩
    · exact hOdd _ t n ℓ f p hp hp5 hadm.1 hℓ2 hadm hmodel
  · rcases hSpor s _ hnonab ⟨e⟩ with hlt | hnd
    · exact PlaneCases.planeT_of_outer_small hp5 (Or.inl (by omega))
    · exact PlaneCases.planeT_of_outer_small hp5 (Or.inr (hnd p hp hp5))

@[expose] def Sec68Hyp (H : Type) [Group H] [Finite H] (p : ℕ) (J : Subgroup H) : Prop :=
  p ∣ Nat.card (Subgroup.center ↥J) →
    p = 5 ∧ Nat.card (Subgroup.center ↥J) = 5 ∧
      ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 n

theorem planeNoInnerPart'_of_cases (hEven : ∀ t : StatedLieTag, Sec66T_K2 t)
    (hOdd : OddLiePlaneT) (hSpor : SporadicOutSmall) (hCenter : PlaneCenterP') :
    PlaneNoInnerPartWith Sec68Hyp := by
  intro H _ _ p J A c hp hp5 hrank hJq hJcat h68 hAN hAe hAcard hcA hc1 hcC hmain
  by_cases hZ : p ∣ Nat.card (Subgroup.center ↥J)
  · exact hCenter H p J A c hp hp5 hrank hJq hJcat hZ (h68 hZ) hAN hAe hAcard hcA hc1 hcC hmain
  exact Sec66T.planeNoInnerPart_of_planeT H p J A c hp hp5 hrank hJq hZ
    (planeT_of_catalog hEven hOdd hSpor hp hp5 hJq hJcat) hAN hAe hAcard hcA hc1 hcC hmain

theorem outPCyclicTheta_of_cases'
    (hbridge : CFSG.Assembly.CatalogImp CFSG.Assembly.InCatalog Catalog)
    (hEven : ∀ t : StatedLieTag, Sec66T_K2 t) (hOdd : OddLiePlaneT) (hSpor : SporadicOutSmall)
    (hCenter : PlaneCenterP') (h68 : SectionProvider Sec68Hyp) : OutPCyclicTheta :=
  outPCyclicTheta_of_planeWith Sec68Hyp hbridge h68
    (planeNoInnerPart'_of_cases hEven hOdd hSpor hCenter)

end CFSG.RankThree.PartOne

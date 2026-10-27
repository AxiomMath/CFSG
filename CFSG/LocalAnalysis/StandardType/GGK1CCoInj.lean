module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (proj_bijective_of_charTwo)

theorem ggK1CCo_component_inj {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ nf) (hnf : 1 ≤ nf)
    {x : ↥(StatedSp r K)} {m : List ℕ} (F : ggK1CCo_Family p nf d r K x m)
    {i j : F.ι} (hi : CFSG.IsQuasisimple ↥⁅F.A i, F.A i⁆)
    (hj : CFSG.IsQuasisimple ↥⁅F.A j, F.A j⁆)
    (h : (⁅F.A i, F.A i⁆).map (proj r K) = (⁅F.A j, F.A j⁆).map (proj r K)) : i = j := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := nf)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  haveI : NeZero r := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · exfalso
      subst hr
      haveI : Subsingleton (StatedSp 0 K) := inferInstance
      haveI : Subsingleton ↥⁅F.A i, F.A i⁆ := inferInstance
      haveI : Nontrivial ↥⁅F.A i, F.A i⁆ := CFSG.LocalCores.isQuasisimple_nontrivial hi
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial ↥⁅F.A i, F.A i⁆).exists_pair_ne
      exact hab (Subsingleton.elim a b)
    · exact ⟨hr.ne'⟩
  have hproj : Function.Injective (proj r K) :=
    (proj_bijective_of_charTwo (r := r) (K := K)).1
  have hH : (⁅F.A i, F.A i⁆ : Subgroup (StatedSp r K)) = ⁅F.A j, F.A j⁆ :=
    (Subgroup.map_injective hproj) h
  have hHle : (⁅F.A i, F.A i⁆ : Subgroup (StatedSp r K)) ≤ F.A i :=
    Subgroup.commutator_le_self (F.A i)
  have hHlej : (⁅F.A i, F.A i⁆ : Subgroup (StatedSp r K)) ≤ F.A j := by
    rw [hH]
    exact Subgroup.commutator_le_self (F.A j)
  by_contra hij
  have hcommH : ∀ a b : ↥⁅F.A i, F.A i⁆, a * b = b * a := by
    intro a b
    refine Subtype.ext ?_
    exact F.hcomm i j hij a.1 (hHle a.2) b.1 (hHlej b.2)
  obtain ⟨a, b, hab⟩ := hi.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥⁅F.A i, F.A i⁆) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥⁅F.A i, F.A i⁆) b
  refine hab ?_
  have hxy : (QuotientGroup.mk' (Subgroup.center ↥⁅F.A i, F.A i⁆)) (x * y) =
      (QuotientGroup.mk' (Subgroup.center ↥⁅F.A i, F.A i⁆)) (y * x) := by rw [hcommH x y]
  simpa only [map_mul] using hxy

end CFSG.StandardType

end

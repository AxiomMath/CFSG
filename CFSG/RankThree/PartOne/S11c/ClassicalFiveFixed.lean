module

public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.PartOne.S11c.ProjectiveDegree
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.RankThree.SteinbergR3ECAInnerDefiningComponentFree
public import CFSG.RankThree.GroupTheory.SteinbergCEOddSymplecticRankFour
public import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S11c.HigherLinearSmall
public import CFSG.RankThree.PartOne.S11c.HigherUnitarySmall
public import CFSG.RankThree.PartOne.S11c.PlaneOrthogonal
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.RankThree.GroupTheory (odd_symplectic_actual_cover_rank_four_and_small_parameters)

@[expose] def OddSymplecticFourInnerDefiningFixedComponentFree : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → 3 < ℓ → 1 ≤ f → ∀ (T : Type) [Group T],
    StatedClassicalModel T .PSp 2 ℓ f → ∀ β : MulAut T,
      β ∈ (MulAut.conj : T →* MulAut T).range → orderOf β = ℓ →
        ∀ L : Subgroup ((β : T →* T).eqLocus (MonoidHom.id T)), ¬ CFSG.IsComponent L

@[expose] def PSU3FiveNotInPSL2Char5 : Prop :=
  ∀ (V : Type) [Group V] (K : Subgroup V) (f : ℕ), StatedClassicalModel K .PSU 3 5 1 →
    StatedClassicalModel V .PSL 2 5 f → False

@[expose] def EvenClassicalHighDimRankFour : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (X : Subgroup H) (τ : StatedLieTag) (n f : ℕ),
    StatedClassicalModel (X ⧸ Subgroup.center X) τ n 2 f → 20 ≤ naturalDim τ n →
      4 ≤ localRank 3 H

theorem localRank_le_three_of_twoLocalOddRank {H : Type} [Group H] [Finite H]
    (hrank : CFSG.twoLocalOddRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    localRank p H ≤ 3 := by
  rcases Nat.eq_zero_or_pos (localRank p H) with h0 | hpos
  · omega
  · exact (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hp hp2
      (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hp hpos)).trans hrank

theorem not_ordinaryComponent_of_eqLocus {T : Type} [Group T] (β : MulAut T) (K : Subgroup T)
    (h : ∀ L : Subgroup ((β : T →* T).eqLocus (MonoidHom.id T)), ¬ CFSG.IsComponent L)
    (hK : IsOrdinaryComponentOf K (fixedSubgroup β)) : False := by
  have heq : fixedSubgroup β = (β : T →* T).eqLocus (MonoidHom.id T) := by
    ext x
    exact Iff.rfl
  rw [heq] at hK
  exact h _ hK.2

theorem mem_range_conj_of_congr {V T : Type} [Group V] [Group T] (e : V ≃* T) {β : MulAut V}
    (h : MulAut.congr e β ∈ inner T) : β ∈ (MulAut.conj : V →* MulAut V).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  exact hy

theorem typeA_defining_absurd {V : Type} [Group V] [Finite V] {β : MulAut V} {K : Subgroup V}
    (hord : orderOf β = 5) (hcomp : IsOrdinaryComponentOf K (fixedSubgroup β))
    {τ : StatedLieTag} (hτ : τ = .PSL ∨ τ = .PSU) {n f : ℕ} (hn : n = 3 ∨ n = 4)
    (hf1 : 1 ≤ f) (hf3 : f ≤ 3) (hmod : StatedClassicalModel V τ n 5 f) : False := by
  have hn3 : 3 ≤ n := by omega
  obtain ⟨-, hinn⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    hτ hn3 Nat.prime_five hf1 hmod
  have h5 : ¬ 5 ∣ f * CFSG.RankThree.OuterOrder.determinantParameter τ n (5 ^ f) := by
    intro h
    have hdn : CFSG.RankThree.OuterOrder.determinantParameter τ n (5 ^ f) ∣ n := by
      rcases hτ with rfl | rfl <;> exact Nat.gcd_dvd_left _ _
    generalize CFSG.RankThree.OuterOrder.determinantParameter τ n (5 ^ f) = d at h hdn
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hd4 : d ≤ 4 := (Nat.le_of_dvd (by omega) hdn).trans (by omega)
    interval_cases f <;> interval_cases d <;> omega
  have hβ : β ∈ (MulAut.conj : V →* MulAut V).range := hinn β hord h5
  exact not_ordinaryComponent_of_eqLocus β K
    (CFSG.RankThree.CAInnerDefining.linear_unitary_three_four_inner_defining_fixed_component_free
      Nat.prime_five (by norm_num) hf1 hn hτ hmod β hβ hord) hcomp

theorem sp_defining_absurd (hSp4 : OddSymplecticFourInnerDefiningFixedComponentFree) {V : Type}
    [Group V] {β : MulAut V} {K : Subgroup V} (hord : orderOf β = 5)
    (hcomp : IsOrdinaryComponentOf K (fixedSubgroup β)) {f : ℕ} (hf1 : 1 ≤ f) (hf3 : f ≤ 3)
    (hmod : StatedClassicalModel V .PSp 2 5 f) : False := by
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := id hmod
  have hout := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
    Nat.prime_five (by norm_num) hf1 (le_refl 2) hk).1
  have h5 : ¬ 5 ∣ f * Nat.gcd 2 (5 ^ f - 1) := by
    intro h
    have hg2 : Nat.gcd 2 (5 ^ f - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 2 (5 ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    generalize Nat.gcd 2 (5 ^ f - 1) = g at h hg2 hg0
    interval_cases f <;> interval_cases g <;> omega
  have hβ' : MulAut.congr e β ∈ inner (StatedProj (StatedSp 2 k)) :=
    CFSG.RankThree.OuterOrder.mem_inner_of_orderOf_eq_five hout h5
      (by rw [MulEquiv.orderOf_eq]; exact hord)
  have hβ : β ∈ (MulAut.conj : V →* MulAut V).range := mem_range_conj_of_congr e hβ'
  exact not_ordinaryComponent_of_eqLocus β K
    (hSp4 5 f Nat.prime_five (by norm_num) hf1 V hmod β hβ hord) hcomp

theorem fiveFixedExcludesClassical_of_inputs
    (hSp4 : OddSymplecticFourInnerDefiningFixedComponentFree) (hL2 : PSU3FiveNotInPSL2Char5)
    (hEven : EvenClassicalHighDimRankFour) : FiveFixedExcludesClassical := by
  intro H _ _ hrank X hX β K hFive τ n ℓ f hmod
  obtain ⟨hord, hcomp, hK⟩ := hFive
  have hloc := fun {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) =>
    localRank_le_three_of_twoLocalOddRank hrank hp hp2
  have hℓ : ℓ.Prime := hmod.1.1
  have hf : 1 ≤ f := hmod.1.2.1
  have hτ : τ = .PSL ∨ τ = .PSU ∨ τ = .PSp ∨ τ = .POmegaOdd ∨ τ = .POmegaPlus ∨
      τ = .POmegaMinus := by
    have h2 := hmod.2
    cases τ <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      | exact h2.elim
  by_cases hℓ5 : ℓ = 5
  ·
    subst hℓ5
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have hadm := hmod.1.2.2
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · have hn2 : n = 2 := by have := hadm.1; omega
        subst hn2
        exact hL2 _ K f hK hmod
      · obtain ⟨hn4, hf3⟩ := linear_small_parameters h3 hℓ (by norm_num) hmod
          (hloc hℓ (by norm_num))
        have hn4' : n ≤ 4 := hn4.resolve_right (by rintro ⟨h, -⟩; omega)
        have hf3' : f ≤ 3 := hf3.resolve_right (by rintro ⟨h, -⟩; omega)
        exact typeA_defining_absurd hord hcomp (Or.inl rfl) (by omega) hf hf3' hmod
    ·
      have hn3 : 3 ≤ n := hmod.1.2.2.1
      obtain ⟨hn4, hf3⟩ := unitary_small_parameters hn3 hℓ (by norm_num) hmod
        (hloc hℓ (by norm_num))
      have hn4' : n ≤ 4 := hn4.resolve_right (by rintro ⟨h, -⟩; omega)
      have hf3' : f ≤ 3 := hf3.resolve_right (by rintro ⟨h, -⟩; omega)
      exact typeA_defining_absurd hord hcomp (Or.inr rfl) (by omega) hf hf3' hmod
    ·
      obtain ⟨hn2, hf3⟩ := (odd_symplectic_actual_cover_rank_four_and_small_parameters.{0}
        (f := f) hℓ (by norm_num)).2 H X n (Or.inl hrank) hmod
      subst hn2
      exact sp_defining_absurd hSp4 hord hcomp hf hf3 hmod
    · exact orthogonal_model_absurd (Or.inl rfl) hℓ (by norm_num) hmod (hloc hℓ (by norm_num))
    · exact orthogonal_model_absurd (Or.inr (Or.inl rfl)) hℓ (by norm_num) hmod
        (hloc hℓ (by norm_num))
    · exact orthogonal_model_absurd (Or.inr (Or.inr rfl)) hℓ (by norm_num) hmod
        (hloc hℓ (by norm_num))
  ·
    have h20 := degree_ge_twenty_of_classical_model K hK hmod hℓ5
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have h4 := hEven H X τ n f hmod h20
      have h3 := hloc Nat.prime_three (by norm_num)
      omega
    · rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
      ·
        have hn : 20 ≤ n := h20
        rcases (linear_small_parameters (by omega) hℓ hℓ2 hmod (hloc hℓ hℓ2)).1 with
          h | ⟨-, -, h | h⟩ <;> omega
      · have hn : 20 ≤ n := h20
        rcases (unitary_small_parameters (by omega) hℓ hℓ2 hmod (hloc hℓ hℓ2)).1 with
          h | ⟨-, -, h | h⟩ <;> omega
      · obtain ⟨hn2, -⟩ := (odd_symplectic_actual_cover_rank_four_and_small_parameters.{0}
          (f := f) hℓ hℓ2).2 H X n (Or.inl hrank) hmod
        simp only [naturalDim] at h20
        omega
      · exact orthogonal_model_absurd (Or.inl rfl) hℓ hℓ2 hmod (hloc hℓ hℓ2)
      · exact orthogonal_model_absurd (Or.inr (Or.inl rfl)) hℓ hℓ2 hmod (hloc hℓ hℓ2)
      · exact orthogonal_model_absurd (Or.inr (Or.inr rfl)) hℓ hℓ2 hmod (hloc hℓ hℓ2)

end CFSG.RankThree.PartOne.HNRed

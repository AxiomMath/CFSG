module

public import CFSG.OddTranspositions.SevenLocalSecond
public import CFSG.OddTranspositions.SixSevenLocalStep

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_thirdKind_of_mem_alpha (hC : HypothesisC D) (hfaith : FaithfulOnBlocks hC.alpha)
    (hfirst : ∀ x w y : G, IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)))
    {a c : G} (ha : a ∈ hC.alpha) (hc : c ∈ hC.alpha) (hac : Commute a c) (hane : a ≠ c) :
    ∃ x : G, IsTriangle D a x c ∧ IsThirdKind a x c := by
  classical
  by_contra hcon
  push Not at hcon
  have hD := hC.setup.oddT
  have hblock := hC.isBlock_alpha
  have haD : a ∈ D := hblock.subset ha
  have ha2 : a * a = 1 := hD.mul_self_eq_one haD
  have htriv : ActsTriviallyOnBlocks hC.alpha (a * c) := by
    intro γ hγ
    have hγ' : γ ∈ perp D hC.alpha ∪ Aalpha D hC.alpha := by
      rw [perp_union_Aalpha_eq_blockClass]; exact hγ
    rcases hγ' with hγp | hγA
    · rcases mem_perp_iff.mp hγp with hγD | rfl
      · ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          have h1 : Commute a z := hγD.2.2.2 a ha z hz
          have h2 : Commute c z := hγD.2.2.2 c hc z hz
          have : a * c * z * (a * c)⁻¹ = z := by
            rw [((h1.mul_left h2)).eq]; group
          change a * c * z * (a * c)⁻¹ ∈ γ
          rw [this]; exact hz
        · intro hy
          refine ⟨y, hy, ?_⟩
          have h1 : Commute a y := hγD.2.2.2 a ha y hy
          have h2 : Commute c y := hγD.2.2.2 c hc y hy
          change a * c * y * (a * c)⁻¹ = y
          rw [((h1.mul_left h2)).eq]; group
      · have hN : a * c ∈ Subgroup.normalizer hC.alpha :=
          Subgroup.mul_mem _ (mem_normalizer_of_mem_alpha hblock ha)
            (mem_normalizer_of_mem_alpha hblock hc)
        exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hN
    · obtain ⟨b, hb⟩ := blockClass_nonempty hblock.nonempty hγA.1
      have htri : IsTriangle D a b c :=
        isTriangle_of_mem_Aalpha hD hC.setup.normal hblock hγA ha hc hac hane hb
      have h4 : orderOf (a * c * b) = 4 := by
        rcases htri.orderOf_cases hD hC.setup.normal with h1 | h4 | h3
        · exact absurd h1 (hfirst a b c htri)
        · exact h4
        · exact absurd h3 (hcon b htri)
      have hy := conj_mul_mem_of_mem_Aalpha hC hγA ha hc hac hane hb h4
        (fun x _ _ hx => hcon x hx)
      exact eq_of_mem_of_mem_blockClass hblock (conj_image_mem_blockClass hγA.1 _) hγA.1
        ⟨_, ⟨b, hb, rfl⟩, hy⟩
  have h1 := hfaith _ htriv
  apply hane
  calc a = a * (a * c) := by rw [h1, mul_one]
    _ = c := by rw [← mul_assoc, ha2, one_mul]

theorem exists_thirdKind_of_commute_d (hC : HypothesisC D) (hfaith : FaithfulOnBlocks hC.alpha)
    (hfirst : ∀ x w y : G, IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)))
    {w v : G} (htri : IsTriangle D hC.d w v) (h3 : IsThirdKind hC.d w v)
    (hv : v ∈ DalphaStar D hC.alpha) {a : G} (haD : a ∈ D) (hda : Commute hC.d a)
    (hne : hC.d ≠ a) :
    ∃ c : G, IsTriangle D hC.d c a ∧ IsThirdKind hC.d c a := by
  rcases mem_alpha_or_DalphaStar_of_commute hC haD hda.symm with haα | haS
  · exact exists_thirdKind_of_mem_alpha hC hfaith hfirst hC.d_mem_alpha haα hda hne
  · obtain ⟨h, hh, rfl⟩ := hC.Halpha_transitive v hv _ haS
    have hle : Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
      refine Subgroup.closure_le _ |>.mpr ?_
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hC.DalphaStar_subset_commute hx).2.eq
    have hhd : h * hC.d * h⁻¹ = hC.d := by
      rw [(show Commute h hC.d from Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).eq,
        mul_inv_cancel_right]
    refine ⟨h * w * h⁻¹, ?_, ?_⟩
    · simpa [hhd] using isTriangle_conj hC.setup.normal (g := h) htri
    · obtain ⟨n, hn, hn1, hord⟩ := h3
      refine ⟨n, hn, hn1, ?_⟩
      have : hC.d * (h * v * h⁻¹) * (h * w * h⁻¹) = h * (hC.d * v * w) * h⁻¹ := by
        conv_lhs => rw [← hhd]
        group
      rw [this, ← (show SemiconjBy h (hC.d * v * w) (h * (hC.d * v * w) * h⁻¹) by
        unfold SemiconjBy; group).orderOf_eq, hord]

end CFSG.OddTranspositions

end


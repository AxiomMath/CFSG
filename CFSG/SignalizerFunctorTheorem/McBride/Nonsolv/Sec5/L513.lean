module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Quotient
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.Section

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

open CFSG.SignalizerFunctorTheorem.Nonsolvable

private theorem nearSimpleModel_of_isSectionOf_aux {p : ℕ} (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] (E Y : Subgroup Γ), Nat.card Y = n →
      IsElemAbelian p E → E ≤ Subgroup.normalizer (Y : Set Γ) →
      signalizerMcBrideHypothesisB p Y →
      Group.IsSolvable (Y ⊓ Subgroup.centralizer (E : Set Γ) : Subgroup Γ) →
      ∀ (S : Type u) [Group S] [IsSimpleGroup S], IsSectionOf S ↥Y →
        (∃ a b : S, a * b ≠ b * a) → signalizerNearSimpleModel p S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ E Y hn hE hEY hY hsol S _ _ hS hSnc
  have hp : p.Prime := hY.1
  classical
  let P : Subgroup Γ → Prop := fun N => N ≠ ⊥ ∧ N ≤ Y ∧ (N.subgroupOf Y).Normal ∧
    E ≤ Subgroup.normalizer (N : Set Γ)
  have hY1 : Y ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hSnc
    have : Subsingleton ↥Y := by rw [h]; infer_instance
    have := hS.subsingleton
    exact hab (Subsingleton.elim _ _)
  have hPY : P Y := ⟨hY1, le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance, hEY⟩
  have hex : ∃ k, ∃ N, P N ∧ Nat.card N = k := ⟨_, Y, hPY, rfl⟩
  obtain ⟨N, hPN, hNk⟩ := Nat.find_spec hex
  have hmin : ∀ M, P M → Nat.card N ≤ Nat.card M := fun M hM =>
    hNk ▸ Nat.find_min' hex ⟨M, hM, rfl⟩
  obtain ⟨hN1, hNY, hNn, hEN⟩ := hPN
  by_cases hNeq : N = Y
  ·
    subst hNeq
    have hnc : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a, b, hab⟩ := hSnc
      exact hab (hS.commutative (fun x y => Subtype.ext (hcon x x.2 y y.2)) a b)
    have hsimple : IsASimple E N := ⟨hEY, hnc, fun M hMY hMn hEM => by
      by_cases hM : M = ⊥
      · exact Or.inl hM
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge hMY (hmin M ⟨hM, hMY, hMn, hEM⟩))⟩
    obtain ⟨T, hT⟩ := hsimple.simpleComponents_nonempty
    have hTnear := AChief.signalizerNearPSolvable_of_isASimple hp hE hsimple hY hsol hT
    exact (signalizerNearPSolvable_iff.mp hTnear).2 S
      (AChief.isSectionOf_component hsimple hT hSnc hS) hSnc
  ·
    have hNlt : Nat.card N < Nat.card Y := by
      by_contra hge
      push Not at hge
      exact hNeq (Subgroup.eq_of_le_of_card_ge hNY hge)
    have hYN : Y ≤ AChief.nrm N := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mp hNn
    rcases AChief.isSectionOf_normal_or_qimg hNY hYN hS with hSN | hSq
    · refine ih (Nat.card N) (hn ▸ hNlt) E N rfl hE hEN ?_ ?_ S hSN hSnc
      · exact (isSigClass_hypBClass.{u} p).mono Γ hNY hEN hY
      · exact Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion (inf_le_inf_right _ hNY)) (Subgroup.inclusion_injective _)
    · obtain ⟨π, hπ⟩ := AChief.exists_surjective_fixed hp hE hEY hEN hYN hY.2.1
      refine ih (Nat.card (AChief.qimg N Y)) ?_ (AChief.qimg N E) (AChief.qimg N Y) rfl
        (AChief.isElemAbelian_qimg hE) (AChief.qimg_le_normalizer hEY)
        (AChief.hypB_qimg hYN hY) ?_ S hSq hSnc
      · have h1 := AChief.card_qimg_mul_card hNY hYN
        have h2 : 2 ≤ Nat.card N := by
          have h3 : Nat.card N ≠ 1 := fun h => hN1 (Subgroup.eq_bot_of_card_eq N h)
          have h4 : 0 < Nat.card N := Nat.card_pos
          omega
        have h5 : 0 < Nat.card (AChief.qimg N Y) := Nat.card_pos
        rw [← hn, ← h1]
        nlinarith
      · exact Group.isSolvable_of_surjective hπ

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem lemma_5_13 {p : ℕ} {A G : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (h : NearASolvableII p A G) : NearASolvable p A G := by
  obtain ⟨hA, hB, hsol⟩ := h
  refine ⟨?_, hsol⟩
  rw [signalizerNearPSolvable_iff]
  exact ⟨hB.2.1, fun S _ _ hS hnc =>
    nearSimpleModel_of_isSectionOf_aux _ A G rfl hA hAG hB hsol S hS hnc⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

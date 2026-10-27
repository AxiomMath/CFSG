module

public import CFSG.Timmesfeld.Outcome
import CFSG.Timmesfeld.Assembly
import CFSG.Timmesfeld.RootInvolutionCenter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem Outcome.lieModel_or_exception {X : Type} [Group X] (h : Outcome X) :
    (∃ (t : StatedLieTag) (n f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧
      StatedLieAdmissible t n 2 f ∧ CFSG.Blueprint.LieModel X t n 2 f) ∨
    CFSG.Blueprint.LieModel X .PSU 3 3 1 ∨ Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic X .J2 := by
  rcases h with ⟨n, f, -, -, h⟩ | ⟨n, f, -, -, h⟩ | ⟨n, f, -, -, h | h⟩ | ⟨f, -, h⟩ |
    ⟨f, -, t, ht, h⟩ | h | h | h
  · exact Or.inl ⟨.PSL, n, f, by decide, by decide, h.admissible, h⟩
  · exact Or.inl ⟨.PSp, n, f, by decide, by decide, h.admissible, h⟩
  · exact Or.inl ⟨.POmegaPlus, n, f, by decide, by decide, h.admissible, h⟩
  · exact Or.inl ⟨.POmegaMinus, n, f, by decide, by decide, h.admissible, h⟩
  · exact Or.inl ⟨.G2, 0, f, by decide, by decide, h.admissible, h⟩
  · refine Or.inl ⟨t, 0, f, ?_, ?_, h.admissible, h⟩ <;> rintro rfl <;> exact absurd ht (by decide)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem meetsSq_of_orderOf_mul_eq_four {G : Type*} [Group G] {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hroot : IsRootInvolutionSet D) {d e : G}
    (hd : d ∈ D) (he : e ∈ D) (h4 : orderOf (d * e) = 4) :
    ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D := by
  obtain ⟨hsq, hc, -, -⟩ := sq_mem_of_orderOf_eq_four hroot hd he h4
  have hmul := mul_sq_mem_of_orderOf_eq_four hcls hroot hd he h4
  refine ⟨d, hd, (d * e) ^ 2, hsq, fun h => ?_, hc, hmul⟩
  rw [← h, hroot.mul_self_eq_one hd] at hmul
  exact hroot.ne_one hmul rfl

theorem outcome_quotient_center_of_nondegenerate {Y : Type} [Group Y] [Finite Y] {D : Set Y}
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g}) (hroot : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤)
    (h2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hDZ : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    Outcome (Y ⧸ Subgroup.center Y) := by
  obtain ⟨d, hd, e, he, h4⟩ := hnondeg
  obtain ⟨u, hu, v, hv, hne, hc, huv⟩ := meetsSq_of_orderOf_mul_eq_four hcls hroot hd he h4
  exact outcome (image_hyp_center hcls hroot hgen
    (fun _ hN hs => Bridge.le_center_of_isSolvable hcls hroot hgen hu hv hne hc huv h2 hN hs)
    hDZ ⟨d, hd, e, he, h4⟩)

end CFSG.Timmesfeld

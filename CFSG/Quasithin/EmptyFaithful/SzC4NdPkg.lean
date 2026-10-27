module

public import CFSG.Quasithin.EmptyFaithful.A38c10VMain
public import CFSG.Quasithin.EmptyFaithful.SzC4NdQ
public import CFSG.Quasithin.Background.B5Statement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

theorem nd_package2 {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {Λ B : Subgroup (MulAut V)} {U : Subgroup V} (hne : Λ ≠ ⊥) (hB : IsSylowTwoOf B Λ)
    (hnd : SumNatDual Λ U 4) :
    ∃ D : BorelIso 4 Λ B,
      (∀ u ∈ U, (∀ b ∈ B, (b : MulAut V) u = u) → D.cutsOf (Λ ⊓ fixSub u) ⊆ {1, 3}) ∧
      (∀ P : Subgroup (MulAut V), B ≤ P → P ≤ Λ → D.cutsOf P = {1} →
        ∃ q ∈ U, q ≠ 1 ∧ (∀ a ∈ P, (a : MulAut V) q = q) ∧ q ∈ commV (oTwoUpper P)) ∧
      (∀ P : Subgroup (MulAut V), B ≤ P → P ≤ Λ → D.cutsOf P = {3} →
        ∃ q ∈ U, q ≠ 1 ∧ (∀ a ∈ P, (a : MulAut V) q = q) ∧ q ∈ commV (oTwoUpper P)) ∧
      fixV Λ ⊓ U = ⊥ := by
  obtain ⟨-, π, U₁, U₂, ⟨hsup, hdis⟩, h₁, h₂⟩ := hnd
  obtain ⟨D₁⟩ := vmodelNat h₁ (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨D₂⟩ := vmodelDual h₂ (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨g, D, hρDe, -, hcuts⟩ := exists_borelIso_of_rho (by norm_num : 3 ≤ 4) (rhoOf_mem π)
    (rhoOf_surj h₁.1) (fix_reflection_of_models hsup hdis D₁ D₂ hV2 (by norm_num)) hne hB
  refine ⟨D, fun u hu huB i hi => ?_, fun P hBP hPΛ hPc => ?_, fun P hBP hPΛ hPc => ?_,
    fixV_inf_eq_bot_nd hsup hdis D₁ D₂⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hcuts u hu huB hi
    have h4 : ¬ (i ≠ 1 ∧ i ≠ 4 - 1) := h3
    show i = 1 ∨ i = 3
    omega
  · have hmodel : D.model P = QI 4 {1} := model_eq_QI_of_cuts D hB.1 hBP hPc
    obtain ⟨q, hq₁, hq1, hqfix, hqcomm⟩ := exists_q_nat D₁ g (P := P)
      (fun a ha => ⟨D.e ⟨a, hPΛ ha⟩, by rw [← hmodel]; exact (D.mem_model _).2 ha,
        hρDe ⟨a, hPΛ ha⟩⟩)
      (fun t ht => by
        rw [← hmodel] at ht
        obtain ⟨x, rfl⟩ := D.e.surjective t
        rw [hρDe x]
        exact (D.mem_model x).1 ht)
    exact ⟨q, by rw [← hsup]; exact Subgroup.mem_sup_left hq₁, hq1, hqfix, hqcomm⟩
  · have hmodel : D.model P = QI 4 {3} := model_eq_QI_of_cuts D hB.1 hBP hPc
    obtain ⟨q, hq₂, hq1, hqfix, hqcomm⟩ := exists_q_dual D₂ g (P := P)
      (fun a ha => ⟨D.e ⟨a, hPΛ ha⟩, by rw [← hmodel]; exact (D.mem_model _).2 ha,
        hρDe ⟨a, hPΛ ha⟩⟩)
      (fun t ht => by
        rw [← hmodel] at ht
        obtain ⟨x, rfl⟩ := D.e.surjective t
        rw [hρDe x]
        exact (D.mem_model x).1 ht)
    exact ⟨q, by rw [← hsup]; exact Subgroup.mem_sup_right hq₂, hq1, hqfix, hqcomm⟩

end CFSG.Quasithin.A38c10

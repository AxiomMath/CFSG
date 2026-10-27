module

public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.RankThree.PartOne.S11d.OrthSplitFixed

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Group

variable {T : Type} [Group T] [Finite T]

theorem stable_other {X C₀ C₁ : Subgroup T} (α : MulAut T) (hX : X.map α.toMonoidHom = X)
    (h1 : IsComponentOf X C₁) (hne : C₀ ≠ C₁)
    (hdec : ∀ E, IsComponentOf X E → E = C₀ ∨ E = C₁) (hs : ∀ g ∈ C₀, α g ∈ C₀) :
    ∀ g ∈ C₁, α g ∈ C₁ := by
  have hle : C₀.map α.toMonoidHom ≤ C₀ := by
    rintro _ ⟨g, hg, rfl⟩
    exact hs g hg
  have hC0 : C₀.map α.toMonoidHom = C₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective α.injective]
  have hD : IsComponentOf X (C₁.map α.toMonoidHom) := by
    have := isComponentOf_map_mulEquiv α h1
    rwa [hX] at this
  rcases hdec _ hD with h | h
  · exfalso
    apply hne
    have h' : C₁.map α.toMonoidHom = C₀.map α.toMonoidHom := h.trans hC0.symm
    exact (Subgroup.map_injective α.injective h').symm
  · intro g hg
    have : α g ∈ C₁.map α.toMonoidHom := ⟨g, hg, rfl⟩
    rwa [h] at this

end Group

section Components

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem orth_components_eq (hQ : (polarBilin Q).Nondegenerate) (hK : 4 ≤ Nat.card K)
    {x : V ≃ₗ[K] V} (hxΩ : x ∈ orthDerived Q) (hx : OddOrderIsometry Q p x)
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1) (h4 : 4 ≤ finrank K (fixedSpace x))
    {ι : Type} (C : ι → Subgroup (ProjOrthDerived Q))
    (hC : ∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
      ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal)
    (hsup : (⨆ i, C i) = fixedComponentImage Q x) :
    (∀ i, IsComponentOf (Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q)))
      (C i)) ∧
    (∀ E, IsComponentOf (Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q))) E →
      ∃ i, E = C i) ∧
    inSubgroup layer (Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q))) =
      fixedComponentImage Q x := by
  have : Nontrivial V := nontrivial_of_four_le_finrank_fixed h4
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  have hXN : centralizerImage Q x =
      Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q)) :=
    centralizerImage_eq hQ ⟨x, hxΩ⟩
  have hcomp : ∀ i, IsComponentOf (Subgroup.centralizer
      ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q))) (C i) := fun i => by
    obtain ⟨hq, hle, hsub⟩ := hC i
    refine ⟨hXN ▸ hle, hq, ?_⟩
    rw [← hXN]
    exact hsub
  have hsolv := isSolvable_centralizer_fixedComponentImage hQ hK hx hmult h4
  rw [hXN, ← hsup] at hsolv
  refine ⟨hcomp, fun E hE => isComponentOf_eq_of_decomposition C hcomp hsolv hE, ?_⟩
  rw [inSubgroup_layer_eq_of_decomposition C hcomp hsolv, hsup]

end Components

section Good

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem orth_good_split4 (hσk : ∀ c, c ∈ k ↔ σ c = c) (hext : IsExtension k Q₀ Q)
    (hQS : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : (polarBilin Q).Nondegenerate)
    (hK : 4 ≤ Nat.card K) (hσ : ∃ c, σ c ≠ c) {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q (coordinateFieldMap d σ) α) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hxΩ : x ∈ orthDerived Q) (hx : OddOrderIsometry Q p x)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1)
    (hd : finrank K (fixedSpace x) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace x), finrank K S = 2 ∧
      ∀ u ∈ S, (Q.comp (fixedSpace x).subtype) u = 0)
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hcard : Nat.card K = 2 ^ (p * f₀)) :
    GoodConclusion p (ProjOrthDerived Q) α (piOrth Q ⟨x, hxΩ⟩) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h4 : 4 ≤ finrank K (fixedSpace x) := by omega
  have : Nontrivial (Fin d → K) := nontrivial_of_four_le_finrank_fixed h4
  have hp2' : 2 ≤ p * f₀ := le_trans hp.two_le (Nat.le_mul_of_pos_right p hf₀)
  have : Finite (Fin d → K) := inferInstance
  have : Finite ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    Finite.of_injective (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => (e : (Fin d → K) → (Fin d → K)))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨M⟩ := exists_splitFourModel hx hd hsplit hK
  obtain ⟨hsupC, hfam⟩ := M.family hx
  have hS : ∀ (c : K) v, coordinateFieldMap d σ (c • v) = σ c • coordinateFieldMap d σ v :=
    coordinateFieldMap_smul σ
  have hxT : α (piOrth Q ⟨x, hxΩ⟩) = piOrth Q ⟨x, hxΩ⟩ := hα.fixed ⟨x, hxΩ⟩ hSx
  obtain ⟨w, hw, hQw, t₁, ht₁, hS₁, hsq₁, hw₁, t₂, ht₂, hS₂, hsq₂, hw₂, hne⟩ :=
    exists_rational_eichler_pair_fix k hσk hext hQS hK hodd hx hx.pow_eq_one hSx h4
  obtain ⟨z₁, z₂, hf₁, hf₂, hsq₁', hsq₂', hne', hsw⟩ := M.exists_pair_of_data hx hQ hα hw hQw
    ht₁ hS₁ hsq₁ hw₁ ht₂ hS₂ hsq₂ hw₂ hne
  have hD := M.dicksonDerived hx.polarBilin_fixed_nondegenerate
  obtain ⟨hcomp, hdec, hlayer⟩ := orth_components_eq hQ hK hxΩ hx hmult h4
    (fun i => fixedFactorImage hx (splitFourFactors M.e i)) hfam hsupC
  have hdec2 : ∀ E, IsComponentOf (Subgroup.centralizer
      ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q))) E →
      E = fixedFactorImage hx (splitFourFactors M.e 0) ∨
        E = fixedFactorImage hx (splitFourFactors M.e 1) := fun E hE => by
    obtain ⟨i, rfl⟩ := hdec E hE
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hne01 : fixedFactorImage hx (splitFourFactors M.e 0) ≠
      fixedFactorImage hx (splitFourFactors M.e 1) := by
    intro h
    have : Nontrivial ↥(fixedFactorImage hx (splitFourFactors M.e 0)) :=
      CFSG.LocalCores.isQuasisimple_nontrivial (hfam 0).1
    obtain ⟨⟨g, hg⟩, hg1⟩ := exists_ne (1 : ↥(fixedFactorImage hx (splitFourFactors M.e 0)))
    obtain ⟨a, rfl⟩ := (M.mem_fixedFactorImage_left hx).mp hg
    obtain ⟨b, hb⟩ := (M.mem_fixedFactorImage_right hx).mp (h ▸ hg)
    have h2 := M.theta_injective hx hQ hb
    apply hg1
    apply Subtype.ext
    have ha : a = 1 := (Prod.mk.inj h2).1.symm
    show M.theta hx (a, 1) = 1
    rw [ha]
    exact map_one (M.theta hx)
  have hX : (Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q))).map
      α.toMonoidHom = Subgroup.centralizer ({piOrth Q ⟨x, hxΩ⟩} : Set (ProjOrthDerived Q)) := by
    rw [map_centralizer_singleton_mulEquiv_good α, hxT]
  refine ⟨⟨_, hcomp 0⟩, ?_, ?_⟩
  · intro D hD' hstab
    obtain ⟨i, rfl⟩ := hdec D hD'
    have hboth : (∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 0),
        α g ∈ fixedFactorImage hx (splitFourFactors M.e 0)) ∧
        (∀ g ∈ fixedFactorImage hx (splitFourFactors M.e 1),
        α g ∈ fixedFactorImage hx (splitFourFactors M.e 1)) := by
      fin_cases i
      · exact ⟨hstab, stable_other α hX (hcomp 1) hne01 hdec2 hstab⟩
      · exact ⟨stable_other α hX (hcomp 0) hne01.symm (fun E hE => (hdec2 E hE).symm) hstab,
          hstab⟩
    refine ⟨?_, ?_, ?_⟩
    · fin_cases i
      · exact M.not_inner_left hx hQ hS hSx hσ hα
      · exact M.not_inner_right hx hQ hS hSx hσ hα
    · fin_cases i
      · exact ⟨.PSL, 2, f₀, hf₀, lieModel_quotient_of_SL2 hcard hp2' (M.leftEquiv hx hQ).symm⟩
      · exact ⟨.PSL, 2, f₀, hf₀, lieModel_quotient_of_SL2 hcard hp2' (M.rightEquiv hx hQ).symm⟩
    · fin_cases i
      · exact M.pair_left hx hQ hboth.1 hboth.2 hf₁ hf₂ hsq₁' hsq₂' hne' hsw
      · exact M.pair_right hx hQ hboth.1 hboth.2 hf₁ hf₂ hsq₁' hsq₂' hne' hsw
  · intro g hg _ hg2
    rw [hlayer]
    exact mem_fixedComponentImage_of_two_pow hQ hx hodd hmult h4 hD
      ((centralizerImage_eq hQ ⟨x, hxΩ⟩) ▸ hg) hg2

end Good

end CFSG.RankThree.PartOne

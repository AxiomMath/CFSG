module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB6C27
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6S21
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecKGC27b
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.Walter.J1Props
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {τ : Tag}

theorem rootReflection_smul_all
    (w : WeylGroup τ) (γ : Fin τ.rank → ℤ) :
    rootReflection (w • γ) = w * rootReflection γ * w⁻¹ := by
  by_cases hγ : IsRoot τ γ
  · exact rootReflection_smul_root w hγ
  · have hwγ : ¬ IsRoot τ (w • γ) := fun hh => hγ ((isRoot_smul_iff w).1 hh)
    simp [rootReflection, hγ, hwγ]

section Ident

open Matrix

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

private theorem eqvGen_map'' {α β : Type*} {R : α → α → Prop} {R' : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → R' (f x) (f y)) {x y : α} (h : Relation.EqvGen R x y) :
    Relation.EqvGen R' (f x) (f y) := by
  induction h with
  | rel x y h => exact Relation.EqvGen.rel _ _ (hf x y h)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem componentRoots_subset_of_kernel_subset {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (hker : kernelRoots χ ⊆ kernelRoots χ') {i : KernelComponent χ} {j : KernelComponent χ'}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots χ i) (hγ' : γ ∈ componentRoots χ' j) :
    componentRoots χ i ⊆ componentRoots χ' j := by
  rintro δ ⟨hδ, hδi⟩
  obtain ⟨hγk, hγi⟩ := hγ
  obtain ⟨hγk', hγj⟩ := hγ'
  refine ⟨hker hδ, ?_⟩
  have h1 : Relation.EqvGen _ (⟨δ, hδ⟩ : kernelRoots χ) ⟨γ, hγk⟩ :=
    Quotient.exact (hδi.trans hγi.symm)
  have h2 := eqvGen_map'' (R := fun α β : kernelRoots χ =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
    (R' := fun α β : kernelRoots χ' =>
      (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0)
    (fun x : kernelRoots χ => (⟨x, hker x.2⟩ : kernelRoots χ')) (fun x y h => h) h1
  exact (Quotient.sound h2).trans hγj

private theorem notAbel_of_comp {G : Type*} [Group G] {J K : Subgroup G} (hJ : IsComponentOf J K)
    (h : ∀ y ∈ J, ∀ z ∈ J, y * z = z * y) : False := by
  obtain ⟨-, -, -, hsimp⟩ := hJ
  haveI := hsimp
  have hc : Subgroup.center ↥J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y y.2 x x.2)
  haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
    rw [hc]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (↥J ⧸ Subgroup.center ↥J) inferInstance

private theorem eq_bot_of_perfect_of_solvable {G : Type*} [Group G] [Group.IsSolvable G]
    (h : commutator G = ⊤) : (⊤ : Subgroup G) = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  have : ∀ k, derivedSeries G k = ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [derivedSeries_succ, ih]; exact h
  rw [← this n]
  exact hn

theorem kernelRoots_famChar_subset_single {ι : Type} (a : ι → Fin τ.rank → Lˣ) (u₀ : ι) :
    kernelRoots (famCharHom a) ⊆ kernelRoots (rootCharHom (a u₀)) := by
  intro γ hγ
  obtain ⟨h1, h2⟩ := (mem_kernelRoots_famChar a).1 hγ
  rw [kernelRoots_rootCharHom]
  exact ⟨h1, h2 u₀⟩

theorem exists_rationalComponent_ge
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    (hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1) (u₀ : ι)
    (h1 : rootDiagUnit τ (a u₀) ≠ 1) (iJ : KernelComponent (famCharHom a))
    {Jg Q : Subgroup (ModGL τ L)} (hJ : IsComponentOf Jg Q) (hJΓ : Jg ≤ S.Γ)
    (hJspan : Jg ≤ rootSpan τ L (famOrbit S.ρ a iJ)) :
    ∃ i : KernelComponent (rootCharHom (a u₀)),
      componentRoots (famCharHom a) iJ ⊆ componentRoots (rootCharHom (a u₀)) i ∧
      Jg ≤ rationalComponent S.ρ S.Γ (rootCharHom (a u₀)) i ∧
      IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom (a u₀)) i)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ (a u₀)}) := by
  classical
  obtain ⟨x, rfl⟩ := Quotient.exists_rep iJ
  have hker := kernelRoots_famChar_subset_single a u₀
  have hx' : (x : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom (a u₀)) := hker x.2
  have hxJ : (x : Fin τ.rank → ℤ) ∈ componentRoots (famCharHom a) ⟦x⟧ := ⟨x.2, rfl⟩
  have hxi : (x : Fin τ.rank → ℤ) ∈
      componentRoots (rootCharHom (a u₀)) (⟦⟨x, hx'⟩⟧ : KernelComponent (rootCharHom (a u₀))) :=
    ⟨hx', rfl⟩
  have hsub := componentRoots_subset_of_kernel_subset hker hxJ hxi
  refine ⟨⟦⟨x, hx'⟩⟧, hsub, ?_⟩
  have hperf : ⁅Jg, Jg⁆ = Jg := commutator_self_eq_of_commutator_top hJ.2.2.1
  have hrs : famOrbit S.ρ a ⟦x⟧ ⊆ rationalRoots S.ρ (rootCharHom (a u₀))
      (⟦⟨x, hx'⟩⟧ : KernelComponent (rootCharHom (a u₀))) := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    exact ⟨k, δ, hsub hδ, rfl⟩
  have hle : Jg ≤ rationalSpan S.ρ S.Γ (rootCharHom (a u₀))
      (⟦⟨x, hx'⟩⟧ : KernelComponent (rootCharHom (a u₀))) :=
    le_inf (hJspan.trans (rootSpan_mono hrs)) hJΓ
  have hJle : Jg ≤ rationalComponent S.ρ S.Γ (rootCharHom (a u₀))
      (⟦⟨x, hx'⟩⟧ : KernelComponent (rootCharHom (a u₀))) := by
    calc Jg = ⁅Jg, Jg⁆ := hperf.symm
      _ ≤ _ := Subgroup.commutator_mono hle hle
  refine ⟨hJle, ?_⟩
  have hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom (a u₀))
      (⟦⟨x, hx'⟩⟧ : KernelComponent (rootCharHom (a u₀)))) := by
    rcases CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp hpL
      hsmall (ha u₀) (hap u₀) h1 ⟦⟨x, hx'⟩⟧ with hq | hsol
    · exact hq
    · exfalso
      haveI := hsol
      haveI : Group.IsSolvable ↥Jg :=
        solvable_of_solvable_injective (Subgroup.inclusion_injective hJle)
      have hbot := eq_bot_of_perfect_of_solvable (G := ↥Jg) hJ.2.2.1
      have h1' : ∀ y : ↥Jg, y = 1 := fun y => by
        have hy : y ∈ (⊤ : Subgroup ↥Jg) := Subgroup.mem_top y
        rw [hbot] at hy
        exact Subgroup.mem_bot.1 hy
      exact notAbel_of_comp hJ fun y hy z hz => by
        have e1 := congrArg Subtype.val (h1' ⟨y, hy⟩)
        have e2 := congrArg Subtype.val (h1' ⟨z, hz⟩)
        simp only [OneMemClass.coe_one] at e1 e2
        rw [e1, e2]
  exact CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.isComponentOf_rationalComponent S (ha u₀) _ hq

end Ident

end CFSG.StandardType.TableCRes

end

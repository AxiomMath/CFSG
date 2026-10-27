module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5LangSet
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Lin
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5Count
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResDefs
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.Base
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.Models.Transport
public import CFSG.Quasithin.Background.A3Structure314
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
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
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
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.Walter.J1Props
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Dickson.Sec6.I1431
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.LangRat
  TableB TableBExc TableBExcTwo TableBExcTwoFusion TableBExcTwoTB

theorem fixSubgroup_conj_eq {G : Type*} [Group G] (x : G) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (· * x) h
    simpa [mul_assoc] using h'.symm
  · intro h
    rw [← h]
    group

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aux

variable {K : Type} [Field K] [CharP K 2] {ω : (AlgebraicClosure K)ˣ}

theorem omega_zpow_eq_one_of_zmod (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) {n : ℤ}
    (hn : (n : ZMod 3) = 0) : ω ^ n = 1 := by
  rw [← pow_val_intCast_eq_zpow (omega_orderOf hω), hn, ZMod.val_zero, pow_zero]

theorem omega_zpow_cube (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) (n : ℤ) :
    (ω ^ n) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, omega_cube hω, one_zpow]

theorem three_ne_zero_of_charTwo : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
  have h2 : (2 : AlgebraicClosure K) = 0 := CharTwo.two_eq_zero
  intro h
  have h' : (3 : AlgebraicClosure K) = 0 := by exact_mod_cast h
  exact one_ne_zero (show (1 : AlgebraicClosure K) = 0 by linear_combination h' - h2)

theorem inv_sq_eq_self (hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0) : ω⁻¹ ^ 2 = ω := by
  calc ω⁻¹ ^ 2 = ω⁻¹ ^ 2 * ω ^ 3 := by rw [omega_cube hω, mul_one]
    _ = ω := by group

end Aux

section Node

variable
  {τ : Tag} {d : ℕ} {K : Type} [Field K] [CharP K 2] {ω : (AlgebraicClosure K)ˣ}

theorem nodeCount_of_frameLang [Finite K] (hτ : τ = .E7 ∨ τ = .E8) {F : OrthFrame τ d}
    (hF : FrameParseval F) (hr : 6 ≤ d + 1) {hω : (ω : AlgebraicClosure K) ^ 2 + ω + 1 = 0}
    {p₀ : ℕ} {S : LangSetup τ (AlgebraicClosure K) p₀} (hS : FrameLang F hω S)
    {A : Subgroup (adjointGroup τ K)} (hA : A ≤ (tE K F).range) (hcard : 3 ^ d ≤ Nat.card A)
    {x : adjointGroup τ K} (hxA : x ∈ A) (hx1 : x ≠ 1) : NodeCount 3 A x := by
  classical
  intro hcomp hcent
  haveI : Finite (adjointGroup τ K) := inferInstance
  have hsl : SimplyLacedTag τ := by rcases hτ with rfl | rfl <;> simp [SimplyLacedTag]
  have hτG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl <;> decide
  have hι : Function.Injective (langEmb F hω) := langEmb_injective F hω
  have hιt : ∀ v : Fin (d + 1) → ZMod 3, langEmb F hω (tE K F (Multiplicative.ofAdd v)) =
      rootDiagUnit τ (Hchar (frameLift F v) ω) := fun v => langEmb_tE hτ F hω v
  obtain ⟨u, hu⟩ := hA hxA
  have hxv : x = tE K F (Multiplicative.ofAdd (Multiplicative.toAdd u)) := by
    rw [ofAdd_toAdd]; exact hu.symm
  have hιx : langEmb F hω x = rootDiagUnit τ (Hchar (frameLift F (Multiplicative.toAdd u)) ω) := by
    rw [hxv]; exact hιt _
  have ha3 : ∀ i, (Hchar (frameLift F (Multiplicative.toAdd u)) ω) i ^ 3 = 1 :=
    fun i => omega_zpow_cube hω _
  have hT := hS.torus _ ha3
  have h1 : rootDiagUnit τ (Hchar (frameLift F (Multiplicative.toAdd u)) ω) ≠ 1 :=
    fun h => hx1 (hι (by rw [hιx, h, map_one]))
  have hTame := langSetup_hTame_of_prime S Nat.prime_three three_ne_zero_of_charTwo
    (fun h => absurd h hτG2) hT ha3 h1
  have hβ : ∀ c, langEmb F hω ((MulAut.conj x) c) =
      rootDiagUnit τ (Hchar (frameLift F (Multiplicative.toAdd u)) ω) * langEmb F hω c *
        (rootDiagUnit τ (Hchar (frameLift F (Multiplicative.toAdd u)) ω))⁻¹ :=
    fun c => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hιx]
  have hcomp' : CFSG.Open.IsComponentOf
      (LargeEvenLayer (Subgroup.centralizer ({x} : Set (adjointGroup τ K))))
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) := by
    rw [fixSubgroup_conj_eq]
    exact isComponentOf_iff_open.1 hcomp
  obtain ⟨i, -, hEi⟩ := excres_component_eq_rational S Nat.prime_three (langEmb F hω) hι hS.range
    (MulAut.conj x) hβ hT ha3 hTame hcomp'
  set Gs : Submodule (ZMod 3) (Fin (d + 1) → ZMod 3) := Submodule.span (ZMod 3)
    (frameDual F '' componentRoots (rootCharHom (Hchar (frameLift F (Multiplicative.toAdd u)) ω))
      i) with hGsdef
  have hGsE : ∀ g ∈ Gs, tE K F (Multiplicative.ofAdd g) ∈
      LargeEvenLayer (Subgroup.centralizer ({x} : Set (adjointGroup τ K))) := by
    have hle : Gs ≤ subgroupModule (tE K F)
        (LargeEvenLayer (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨γ, hγ, rfl⟩
      have hroot : IsRoot τ γ := (isRootComponent_componentRoots i).isRoot γ hγ
      have hιu : langEmb F hω (tE K F (Multiplicative.ofAdd (-frameDual F γ))) =
          rootSL2 τ (AlgebraicClosure K) γ (HSL ω) := by
        rw [langEmb_tE hτ F hω, Hel_frameLift_neg_dual hF hω γ, Hel_root_eq_rootSL2 hsl hroot]
      have hmem : rootSL2 τ (AlgebraicClosure K) γ (HSL ω) ∈ S.Γ := by
        rw [← hS.range, ← hιu]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
      have hinv : rootSL2 τ (AlgebraicClosure K) γ (HSL ω⁻¹) ∈ S.Γ := by
        rw [← HSL_inv, map_inv]; exact inv_mem hmem
      have hP2 := rootSL2_HSL_sq_mem_rationalComponent S i hγ hinv (hS.weyl γ hroot)
      rw [inv_sq_eq_self hω, ← hιu, ← hEi] at hP2
      obtain ⟨e, he, hee⟩ := Subgroup.mem_map.1 hP2
      have heu := hι hee
      rw [SetLike.mem_coe, mem_subgroupModule]
      rw [show tE K F (Multiplicative.ofAdd (frameDual F γ)) =
        (tE K F (Multiplicative.ofAdd (-frameDual F γ)))⁻¹ by rw [← map_inv, ← ofAdd_neg, neg_neg],
        ← heu]
      exact inv_mem he
    exact fun g hg => hle hg
  have hperp : ∀ v : Fin (d + 1) → ZMod 3, (∀ g ∈ Gs, g ⬝ᵥ v = 0) →
      tE K F (Multiplicative.ofAdd v) ∈ A →
        tE K F (Multiplicative.ofAdd v) ∈ Subgroup.zpowers x := by
    intro v hv hvA
    refine (hcent _ hvA).1 fun j hj => ?_
    have hjR : langEmb F hω j ∈ rationalComponent S.ρ S.Γ
        (rootCharHom (Hchar (frameLift F (Multiplicative.toAdd u)) ω)) i :=
      hEi ▸ Subgroup.mem_map_of_mem _ hj
    have hb : ∀ γ ∈ rationalRoots S.ρ (rootCharHom (Hchar (frameLift F (Multiplicative.toAdd u)) ω))
        i, rootChar (Hchar (frameLift F v) ω) γ = 1 := by
      intro γ hγ
      rw [rationalRoots_eq_of_rho_neg S hS.rho i] at hγ
      rw [rootChar_Hchar]
      refine omega_zpow_eq_one_of_zmod hω ?_
      rw [iform_frameLift, dotProduct_comm]
      exact hv _ (Submodule.subset_span ⟨γ, hγ, rfl⟩)
    have hc := rationalComponent_le_centralizer S i hb hjR
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    apply hι
    rw [map_mul, map_mul, hιt v]
    exact hc.symm
  have hx3 : x ^ 3 = 1 := by
    rw [hxv, ← map_pow, ← ofAdd_nsmul]
    have h3 : (3 : ℕ) • Multiplicative.toAdd u = 0 := funext fun k => by
      have : ∀ c : ZMod 3, 3 • c = 0 := by decide
      exact this _
    rw [h3, ofAdd_zero, map_one]
  have hcard' : 3 ^ (d + 1 - 1) ≤ Nat.card A := by simpa using hcard
  exact three_cube_le_card_inf hr (tE_injective F) hA hcard' Gs hGsE hx3 hperp

end Node

end CFSG.StandardType.SmallExc

end

module

public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.LocalAnalysis.StandardType.GGLangCoroot
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

@[expose] def LangRatCompKillsP :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) →
    S.IsAlgebraic →
    ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ a b : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      (∀ j, a j ^ p = 1) → (∀ j, b j ^ p = 1) → rootDiagUnit τ a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ¬ p ∣ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1

@[expose] def LangRatCompInnerAct :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ a b : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      (∀ j, a j ^ p = 1) → ∀ i : KernelComponent (rootCharHom b),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
        ¬ p ∣ (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) ^ 2 - 1 →
        ∃ k ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i,
          ∀ l ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i,
            (rootDiagUnit τ a)⁻¹ * l * rootDiagUnit τ a = k⁻¹ * l * k

@[expose] def LangRatCompFieldLen :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus →
      (∀ j, a j ^ p = 1) → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        GGCompFieldAt (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
          (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def LangRatCompOuterDiag :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic →
    ∀ a b : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      ∀ i : KernelComponent (rootCharHom b),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
        ∃ k ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i,
          ∀ l ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i,
            (rootDiagUnit τ a ^ ((S.D.q ^ componentOrbitLength S.ρ
                (componentRoots (rootCharHom b) i)) ^ 2 - 1))⁻¹ * l *
              rootDiagUnit τ a ^ ((S.D.q ^ componentOrbitLength S.ρ
                (componentRoots (rootCharHom b) i)) ^ 2 - 1) = k⁻¹ * l * k

private theorem conj_pow_eq {G : Type} [Group G] {R : Subgroup G} {y k : G} (hk : k ∈ R)
    (hy : ∀ l ∈ R, y⁻¹ * l * y = k⁻¹ * l * k) :
    ∀ n : ℕ, ∀ l ∈ R, (y ^ n)⁻¹ * l * y ^ n = (k ^ n)⁻¹ * l * k ^ n := by
  intro n
  induction n with
  | zero => intro l _; simp
  | succ n ih =>
    intro l hl
    have hmem : (k ^ n)⁻¹ * l * k ^ n ∈ R :=
      R.mul_mem (R.mul_mem (R.inv_mem (R.pow_mem hk n)) hl) (R.pow_mem hk n)
    calc (y ^ (n + 1))⁻¹ * l * y ^ (n + 1) = y⁻¹ * ((y ^ n)⁻¹ * l * y ^ n) * y := by
          rw [pow_succ', mul_inv_rev]; group
      _ = y⁻¹ * ((k ^ n)⁻¹ * l * k ^ n) * y := by rw [ih l hl]
      _ = k⁻¹ * ((k ^ n)⁻¹ * l * k ^ n) * k := hy _ hmem
      _ = (k ^ (n + 1))⁻¹ * l * k ^ (n + 1) := by rw [pow_succ', mul_inv_rev]; group

theorem exists_conj_of_pow_conj {G : Type} [Group G] {R : Subgroup G} {x : G} {p e : ℕ}
    (hp : p.Prime) (hxp : x ^ p = 1) (he : ¬ p ∣ e)
    (h : ∃ k ∈ R, ∀ l ∈ R, (x ^ e)⁻¹ * l * x ^ e = k⁻¹ * l * k) :
    ∃ k ∈ R, ∀ l ∈ R, x⁻¹ * l * x = k⁻¹ * l * k := by
  obtain ⟨k, hkR, hk⟩ := h
  have hcop : e.Coprime p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 he))
  obtain ⟨u, hx⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxp) hcop)
  refine ⟨k ^ u, R.pow_mem hkR u, fun l hl => ?_⟩
  have := conj_pow_eq hkR hk u l hl
  rwa [hx] at this

theorem langRatCompInnerAct_of_outerDiag
    (hOD : LangRatCompOuterDiag) : LangRatCompInnerAct := by
  intro τ L _ _ _ p₀ S hτ hAlg p hp _ a b ha hb hap i hqs hQ
  have hapow : rootDiagUnit τ a ^ p = 1 := by
    have h1 : rootDiagUnit τ a ^ p = rootDiagUnit τ (a ^ p) :=
      (map_pow (rootDiagUnitHom τ L) a p).symm
    have : a ^ p = 1 := funext hap
    rw [h1, this]
    exact CFSG.LieType.Chevalley.rootDiagUnit_one
  exact exists_conj_of_pow_conj hp hapow hQ (hOD τ L p₀ S hτ hAlg a b ha hb i hqs)

open scoped commutatorElement

@[expose] def LangRatCompTorusLift :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
    (τ = .E7 ∨ τ = .E8) → S.IsAlgebraic →
    ∀ a b : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ b ∈ S.D.torus →
      ∀ i : KernelComponent (rootCharHom b),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom b) i) →
        ∃ c : Fin τ.rank → Lˣ, rootDiagUnit τ c ∈ rationalComponent S.ρ S.Γ (rootCharHom b) i ∧
          ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i,
            rootChar c γ = rootChar a γ ^ ((S.D.q ^ componentOrbitLength S.ρ
              (componentRoots (rootCharHom b) i)) ^ 2 - 1)

theorem rationalComponent_le_rootSpan_rationalRoots
    {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ) :
    rationalComponent ρ Γ χ i ≤ rootSpan τ L (rationalRoots ρ χ i) := by
  rw [rationalComponent, Subgroup.commutator_le]
  intro g hg h hh
  have hs : ⁅g, h⁆ ∈ rationalSpan ρ Γ χ i := by
    rw [commutatorElement_def]
    exact (rationalSpan ρ Γ χ i).mul_mem ((rationalSpan ρ Γ χ i).mul_mem
      ((rationalSpan ρ Γ χ i).mul_mem hg hh) ((rationalSpan ρ Γ χ i).inv_mem hg))
      ((rationalSpan ρ Γ χ i).inv_mem hh)
  exact (Subgroup.mem_inf.1 hs).1

theorem rationalComponent_le_centralizer_of_char_one
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {b c : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom b))
    (h : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, rootChar c γ = 1) :
    rationalComponent S.ρ S.Γ (rootCharHom b) i ≤
      Subgroup.centralizer ({rootDiagUnit τ c} : Set (ModGL τ L)) := by
  refine (rationalComponent_le_rootSpan_rationalRoots _ _ _ i).trans ?_
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have hcj := rootDiagUnit_conj_pinnedX c (isRoot_of_mem_rationalRoots S i hα) s
  rw [h α hα, Units.val_one, one_mul] at hcj
  exact (mul_inv_eq_iff_eq_mul.1 hcj).symm

theorem rootChar_pow_mul_inv {τ : Tag} {L : Type} [Field L] (a c : Fin τ.rank → Lˣ) (e : ℕ)
    (γ : Fin τ.rank → ℤ) : rootChar (a ^ e * c⁻¹) γ = rootChar a γ ^ e * (rootChar c γ)⁻¹ := by
  unfold rootChar
  rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  show (a j ^ e * (c j)⁻¹) ^ γ j = _
  rw [mul_zpow, inv_zpow]
  congr 1
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem langRatCompOuterDiag_of_torusLift
    (hT : LangRatCompTorusLift) : LangRatCompOuterDiag := by
  intro τ L _ _ _ p₀ S hτ hAlg a b ha hb i hqs
  obtain ⟨c, hcR, hc⟩ := hT τ L p₀ S hτ hAlg a b ha hb i hqs
  refine ⟨rootDiagUnit τ c, hcR, fun l hl => ?_⟩
  set e := (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom b) i)) ^ 2 - 1
  have hz : ∀ γ ∈ rationalRoots S.ρ (rootCharHom b) i, rootChar (a ^ e * c⁻¹) γ = 1 := by
    intro γ hγ
    rw [rootChar_pow_mul_inv, hc γ hγ, mul_inv_cancel]
  have hzl := rationalComponent_le_centralizer_of_char_one S i hz hl
  rw [Subgroup.mem_centralizer_singleton_iff] at hzl
  have hxe : rootDiagUnit τ a ^ e = rootDiagUnit τ (a ^ e * c⁻¹) * rootDiagUnit τ c := by
    rw [← rootDiagUnit_mul, inv_mul_cancel_right]
    exact (map_pow (rootDiagUnitHom τ L) a e).symm
  rw [hxe]
  calc (rootDiagUnit τ (a ^ e * c⁻¹) * rootDiagUnit τ c)⁻¹ * l *
        (rootDiagUnit τ (a ^ e * c⁻¹) * rootDiagUnit τ c)
      = (rootDiagUnit τ c)⁻¹ * ((rootDiagUnit τ (a ^ e * c⁻¹))⁻¹ *
          (l * rootDiagUnit τ (a ^ e * c⁻¹))) * rootDiagUnit τ c := by group
    _ = (rootDiagUnit τ c)⁻¹ * l * rootDiagUnit τ c := by rw [hzl]; group

theorem langRatCompInnerAct_of_torusLift
    (hT : LangRatCompTorusLift) : LangRatCompInnerAct :=
  langRatCompInnerAct_of_outerDiag (langRatCompOuterDiag_of_torusLift hT)

theorem langRatCompKillsP_of_torusLift
    (hT : LangRatCompTorusLift) (hF : LangRatCompFieldLen) :
    LangRatCompKillsP := by
  intro τ L _ _ _ p₀ S hτ hAlg p hp hp2 a b ha hb hap hbp ha1 i hqs hpR γ hγ
  have hQ : ¬ p ∣
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ^ 2 - 1 := by
    intro h
    apply hpR
    have h1 := ggCompFieldAt_sl2_dvd (hF τ L p₀ S hτ p hp hp2 a ha hap ha1 i hqs)
    exact h.trans ((dvd_mul_left _ _).trans (h1.trans (Subgroup.card_quotient_dvd_card _)))
  obtain ⟨c, hcR, hc⟩ := hT τ L p₀ S hτ hAlg b a hb ha i hqs
  have hn : ¬ p ∣ orderOf (⟨rootDiagUnit τ c, hcR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
    fun h => hpR (h.trans (orderOf_dvd_natCard _))
  have hcn : rootDiagUnit τ c ^ orderOf (⟨rootDiagUnit τ c, hcR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 1 :=
    congrArg Subtype.val (pow_orderOf_eq_one (⟨rootDiagUnit τ c, hcR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)))
  have hbpow : rootDiagUnit τ b ^ p = 1 := by
    have h1 : rootDiagUnit τ b ^ p = rootDiagUnit τ (b ^ p) :=
      (map_pow (rootDiagUnitHom τ L) b p).symm
    have : b ^ p = 1 := funext hbp
    rw [h1, this]
    exact CFSG.LieType.Chevalley.rootDiagUnit_one
  have hr : IsRoot τ γ := isRoot_of_mem_rationalRoots S i hγ
  have h1 := rootChar_pow_eq_one_of_pow hcn hr
  have h2 := rootChar_pow_eq_one_of_pow hbpow hr
  rw [hc γ hγ, ← pow_mul] at h1
  have hcop : Nat.Coprime (((S.D.q ^ componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)) ^ 2 - 1) * orderOf (⟨rootDiagUnit τ c, hcR⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) p :=
    Nat.coprime_mul_iff_left.2 ⟨((Nat.Prime.coprime_iff_not_dvd hp).2 hQ).symm,
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hn).symm⟩
  have hg := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [hcop, pow_one] at hg

end CFSG.StandardType.LangRat

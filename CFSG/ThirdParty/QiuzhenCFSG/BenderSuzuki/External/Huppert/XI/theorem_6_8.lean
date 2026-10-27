module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_6_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_2_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.SharpNearField
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement IsMulCommutative

attribute [local instance] commutatorElement

/-!
# Huppert--Blackburn XI.6.8

The abelian Frobenius-kernel recognition theorem is kept independent of the
sharp near-field branch.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u v w
private theorem huppert_XI_6_8_scalar_range_eq_squares
    {D : Type u} {K : Type w} [Group D] [Finite D] [Field K] [Finite K]
    (scalar : D →* Kˣ) (hscalar : Function.Injective scalar)
    (hhalf : 2 * Nat.card D = Nat.card K - 1)
    (hodd : Odd (Nat.card D)) :
    scalar.range = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  classical
  let Sq : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
  rcases hodd with ⟨m, hm⟩
  have hrange_le : scalar.range ≤ Sq := by
    intro x hx
    rcases hx with ⟨d, rfl⟩
    refine ⟨scalar d ^ (m + 1), ?_⟩
    change (scalar d ^ (m + 1)) ^ 2 = scalar d
    rw [← pow_mul]
    have hexp : (m + 1) * 2 = Nat.card D + 1 := by omega
    rw [hexp, pow_succ]
    have hpow : scalar d ^ Nat.card D = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [hpow, one_mul]
  have hunitCard : Nat.card Kˣ = Nat.card K - 1 :=
    Nat.card_units (α := K)
  have hevenUnits : Even (Nat.card Kˣ) := by
    rw [hunitCard, ← hhalf]
    exact even_two.mul_right _
  have hgcd : Nat.gcd (Nat.card Kˣ) 2 = 2 :=
    Nat.gcd_eq_right (even_iff_two_dvd.mp hevenUnits)
  have hSqCard : Nat.card Sq = Nat.card D := by
    calc
      Nat.card Sq = Nat.card Kˣ / Nat.gcd (Nat.card Kˣ) 2 := by
        simpa [Sq] using IsCyclic.card_powMonoidHom_range Kˣ 2
      _ = Nat.card Kˣ / 2 := by rw [hgcd]
      _ = Nat.card D := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
        rw [Nat.mul_div_cancel' (even_iff_two_dvd.mp hevenUnits)]
        simpa [hunitCard] using hhalf.symm
  apply Subgroup.eq_of_le_of_card_ge hrange_le
  rw [hSqCard]
  exact (Nat.card_congr
    (MonoidHom.ofInjective hscalar).toEquiv).le
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
private theorem huppert_XI_6_8_scalar_coordinates
    {p : ℕ} [Fact p.Prime]
    {D F : Type u} [Group D] [Group F] [Finite F]
    [Nontrivial F] [IsElementaryAbelian p F] [MulDistribMulAction D F]
    (f : ℕ) (hf : 0 < f) (hFcard : Nat.card F = p ^ f)
    (hDcomm : IsMulCommutative D)
    (rho : Representation (ZMod p) D (Additive F))
    (hrho : Function.Injective rho)
    (hirr : ∀ W : Submodule (ZMod p) (Additive F),
      (∀ d : D, ∀ x : Additive F, x ∈ W → rho d x ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ (K : Type w) (_ : Field K) (_ : Finite K),
      ∃ eAdd : Additive F ≃+ K,
        ∃ scalar : D →* Kˣ, Function.Injective scalar ∧
          ∀ d x, eAdd (rho d x) = eAdd x * (scalar d : K) := by
  classical
  let : IsMulCommutative D := hDcomm
  let : CommGroup D := IsMulCommutative.instCommGroup
  let V := Additive F
  let A : Subalgebra (ZMod p) (Module.End (ZMod p) V) :=
    Algebra.adjoin (ZMod p) (Set.range rho)
  have hgenComm : ∀ a ∈ Set.range rho, ∀ b ∈ Set.range rho, a * b = b * a := by
    rintro _ ⟨d, rfl⟩ _ ⟨e, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg rho (mul_comm d e)
  have : IsMulCommutative A := Algebra.isMulCommutative_adjoin (ZMod p) (fun a ha b hb _ => hgenComm a ha b hb)
  let : CommRing A := inferInstance
  let : Module A V := inferInstance
  let scalarA : D →* A := {
    toFun := fun d => ⟨rho d, Algebra.subset_adjoin ⟨d, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      exact map_one rho
    map_mul' := by
      intro d e
      apply Subtype.ext
      exact map_mul rho d e }
  have hscalarA_apply (d : D) (x : V) : scalarA d • x = rho d x := rfl
  have hsimple : IsSimpleModule A V := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    constructor
    · exact Additive.instNontrivial
    · intro x hx
      let L : A →ₗ[A] V := LinearMap.toSpanSingleton A V x
      let W : Submodule A V := LinearMap.range L
      let Wk : Submodule (ZMod p) V := W.restrictScalars (ZMod p)
      have hWinv : ∀ d : D, ∀ y : V, y ∈ Wk → rho d y ∈ Wk := by
        intro d y hy
        change y ∈ W at hy
        change rho d y ∈ W
        rw [← hscalarA_apply]
        exact W.smul_mem (scalarA d) hy
      have hWk : Wk = ⊤ := by
        rcases hirr Wk hWinv with hbot | htop
        · exfalso
          have hxW : x ∈ W := by
            refine ⟨1, ?_⟩
            simp [L]
          have hxbot : x ∈ (⊥ : Submodule (ZMod p) V) := by
            rw [← hbot]
            exact hxW
          exact hx (by simpa using hxbot)
        · exact htop
      intro y
      have hy : y ∈ W := by
        have : y ∈ Wk := by rw [hWk]; trivial
        exact this
      exact (LinearMap.mem_range.mp hy)
  let : IsSimpleModule A V := hsimple
  have hAnontrivial : Nontrivial A := by
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    have h' := congrArg (fun a : A => (a : Module.End (ZMod p) V)) h
    have hv : Nontrivial V := Additive.instNontrivial
    exact zero_ne_one h'
  have hnoZero : NoZeroDivisors A := by
    refine ⟨?_⟩
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    let fa : V →ₗ[A] V := {
      toFun := fun x => a • x
      map_add' := by intro x y; exact smul_add a x y
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply]
        simpa only [mul_smul] using
          congrArg (fun z : A => z • x) (mul_comm a c) }
    have hfa : fa ≠ 0 := by
      intro hzero
      apply ha
      apply Subtype.ext
      ext x
      have hx := congrArg (fun f : V →ₗ[A] V => f x) hzero
      dsimp [fa] at hx ⊢
      exact hx
    have hfainj : Function.Injective fa :=
      LinearMap.injective_of_ne_zero (R := A) (M := V) (N := V) hfa
    apply Subtype.ext
    ext x
    have hzeroAct : a • (b • x) = a • (0 : V) := by
      rw [← mul_smul, hab]
      simp
    have hbx : b • x = 0 := hfainj hzeroAct
    exact hbx
  let : NoZeroDivisors A := hnoZero
  let : IsDomain A :=
    (isDomain_iff_noZeroDivisors_and_nontrivial A).2 ⟨hnoZero, hAnontrivial⟩
  let : Finite (Module.End (ZMod p) V) :=
    Finite.of_injective
      (fun f : Module.End (ZMod p) V => (f : V → V)) LinearMap.coe_injective
  let hAfinite : Finite A := Finite.of_injective Subtype.val Subtype.val_injective
  let : Finite A := hAfinite
  let hAfield : IsField A := Finite.isField_of_domain A
  let : Field A := hAfield.toField
  have hVnontrivial : Nontrivial V := Additive.instNontrivial
  let : Nontrivial V := hVnontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let eval : A →ₗ[A] V := LinearMap.toSpanSingleton A V v
  have hevalSurj : Function.Surjective eval :=
    (isSimpleModule_iff_toSpanSingleton_surjective.mp hsimple).2 v hv
  have hevalInj : Function.Injective eval := by
    rw [← LinearMap.ker_eq_bot]
    exact LinearMap.ker_toSpanSingleton A hv
  let eLin : A ≃ₗ[A] V := LinearEquiv.ofBijective eval ⟨hevalInj, hevalSurj⟩
  let eAddA : V ≃+ A := eLin.symm.toAddEquiv
  have heAddA_scalar (d : D) (x : V) :
      eAddA (rho d x) = eAddA x * scalarA d := by
    change eLin.symm (rho d x) = eLin.symm x * scalarA d
    apply eLin.injective
    rw [eLin.apply_symm_apply]
    calc
      rho d x = scalarA d • x := (hscalarA_apply d x).symm
      _ = scalarA d • eLin (eLin.symm x) := by rw [eLin.apply_symm_apply]
      _ = eLin (scalarA d • eLin.symm x) := by rw [eLin.map_smul]
      _ = eLin (scalarA d * eLin.symm x) := by rfl
      _ = eLin (eLin.symm x * scalarA d) := by rw [mul_comm]
  have hscalarAinj : Function.Injective scalarA := by
    intro d e hde
    apply hrho
    exact congrArg Subtype.val hde
  let scalarUnitsA : D →* Aˣ := scalarA.toHomUnits
  have hscalarUnitsAinj : Function.Injective scalarUnitsA := by
    intro d e hde
    apply hscalarAinj
    exact congrArg Units.val hde
  let K0 := GaloisField p f
  let : Fintype A := Fintype.ofFinite A
  let : Fintype K0 := Fintype.ofFinite K0
  have hcardA : Fintype.card A = Fintype.card K0 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    calc
      Nat.card A = Nat.card V := Nat.card_congr eAddA.symm.toEquiv
      _ = Nat.card F := rfl
      _ = p ^ f := hFcard
      _ = Nat.card K0 := (GaloisField.card p f hf.ne').symm
  let eField : A ≃+* K0 := FiniteField.ringEquivOfCardEq hcardA
  let K : Type w := ULift K0
  let eLift : K ≃+* K0 := ULift.ringEquiv
  let eAtoK : A ≃+* K := eField.trans eLift.symm
  let eAdd : V ≃+ K := eAddA.trans eAtoK.toAddEquiv
  let scalar : D →* Kˣ :=
    (Units.mapEquiv eAtoK.toMulEquiv).toMonoidHom.comp scalarUnitsA
  refine ⟨K, inferInstance, inferInstance, eAdd, scalar, ?_, ?_⟩
  · exact (Units.mapEquiv eAtoK.toMulEquiv).injective.comp hscalarUnitsAinj
  · intro d x
    simpa [eAdd, scalar, scalarUnitsA] using
      congrArg eAtoK (heAddA_scalar d x)
private theorem xi68_actor_card_dvd_group_card_sub_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, a • v = v → v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  classical
  let V0 := {v : V // v ≠ 1}
  let : MulAction A V0 :=
    { smul := fun a v => ⟨a • (v : V), by
        intro h
        apply v.2
        have h' := congrArg (fun x : V => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : A) • (v : V) = (v : V)
        simp
      mul_smul := by
        intro a b v
        apply Subtype.ext
        change (a * b) • (v : V) = a • (b • (v : V))
        rw [mul_smul] }
  have hstab : ∀ v : V0, MulAction.stabilizer A v = ⊥ := by
    intro v
    rw [eq_bot_iff]
    intro a ha
    have hav : a • v = v := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact v.2 (hfree a hane (v : V) (congrArg Subtype.val hav))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardV0 : Nat.card V0 = Nat.card V - 1 := by
    let : Fintype V := Fintype.ofFinite V
    let : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ≠ 1} = Fintype.card V - 1
    simp
  rw [hcardV0, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A V0)), by
    rw [mul_comm]
    exact hcard⟩

/-- Under a coprime action on a finite solvable group, trivial fixed points
remain trivial after quotienting by the commutator subgroup. -/
private theorem huppert_XI_6_8_elementary_kernel
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFcomm : IsMulCommutative F)
    (hlarge : Nat.card F - 1 ≤ 2 * Nat.card D)
    (p f : ℕ) (hp : Nat.Prime p) (hf : 0 < f)
    (hFcard : Nat.card F = p ^ f) :
    IsElementaryAbelian p F := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : F.Normal := hFrob.normal
  let : IsMulCommutative F := hFcomm
  let Ω : Subgroup F := omega₁ (G := F) (p := p)
  have hΩchar : Ω.Characteristic := by
    simpa [Ω] using omega₁_characteristic (G := F) (p := p)
  let : Ω.Characteristic := hΩchar
  let Ωmap : Subgroup H := Ω.map F.subtype
  have hΩmapNormal : Ωmap.Normal := by
    simpa [Ωmap] using
      (ConjAct.normal_of_characteristic_of_normal (H := F) (K := Ω))
  let : Ωmap.Normal := hΩmapNormal
  let : MulDistribMulAction D Ωmap :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D Ωmap
      (Subgroup.le_normalizer_of_normal (H := Ωmap))
  have hfree : ∀ d : D, d ≠ 1 → ∀ x : Ωmap, d • x = x → x = 1 := by
    intro d hd x hfix
    have hconj : (d : H) * (x : H) * (d : H)⁻¹ = (x : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (x : H) = (x : H) * (d : H) := by
      have h := congrArg (fun z : H => z * (d : H)) hconj
      simpa [mul_assoc] using h
    have hxF : (x : H) ∈ F := by
      rcases x.property with ⟨y, hy, hxy⟩
      rw [← hxy]
      exact y.property
    have hxcent : (x : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨hxF, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by simpa [hcent] using hxcent
    exact Subtype.ext (by simpa using hxbot)
  have hdivMap : Nat.card D ∣ Nat.card Ωmap - 1 :=
    xi68_actor_card_dvd_group_card_sub_one hfree
  have hΩmapCard : Nat.card Ωmap = Nat.card Ω := by
    simpa [Ωmap] using
      (Subgroup.card_map_of_injective (K := Ω) (f := F.subtype)
        F.subtype_injective)
  have hpDvdF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p hf.ne'
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' (G := F) p hpDvdF
  have hzpow : z ^ p = 1 := by rw [← hzorder]; exact pow_orderOf_eq_one z
  have hzmem : z ∈ Ω := by
    change z ∈ Subgroup.closure {y : F | y ^ (p ^ 1) = 1}
    apply Subgroup.subset_closure
    simpa [pow_one] using hzpow
  have hzne : z ≠ 1 := by
    intro hz
    subst z
    simp at hzorder
    exact hp.ne_one hzorder.symm
  have hΩne : Ω ≠ ⊥ := by
    intro hbot
    have : z ∈ (⊥ : Subgroup F) := by simpa [hbot] using hzmem
    exact hzne (Subgroup.mem_bot.mp this)
  have hΩgt : 1 < Nat.card Ω := (Subgroup.one_lt_card_iff_ne_bot Ω).2 hΩne
  have hdiv : Nat.card D ∣ Nat.card Ω - 1 := by simpa [hΩmapCard] using hdivMap
  have hDle : Nat.card D ≤ Nat.card Ω - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hΩgt) hdiv
  have hFgt : 1 < Nat.card F :=
    (Subgroup.one_lt_card_iff_ne_bot F).2 hFrob.kernel_ne_bot
  have hΩlower : Nat.card F + 1 ≤ 2 * Nat.card Ω := by
    calc
      Nat.card F + 1 = (Nat.card F - 1) + 2 := by omega
      _ ≤ 2 * Nat.card D + 2 := Nat.add_le_add_right hlarge 2
      _ ≤ 2 * (Nat.card Ω - 1) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hDle) 2
      _ = 2 * Nat.card Ω := by omega
  have hΩtop : Ω = ⊤ := by
    by_contra htop
    have hindexNe : Ω.index ≠ 1 := by
      intro hi
      apply htop
      exact Subgroup.index_eq_one.mp hi
    have hindexGe : 2 ≤ Ω.index := by
      have hindexZero : Ω.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hmul := Ω.card_mul_index
    have hupper : 2 * Nat.card Ω ≤ Nat.card F := by
      calc
        2 * Nat.card Ω ≤ Nat.card Ω * Ω.index :=
          by simpa [mul_comm] using
            Nat.mul_le_mul_left (Nat.card Ω) hindexGe
        _ = Nat.card F := hmul
    omega
  refine { toIsMulCommutative := hFcomm, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  have hxΩ : x ∈ Ω := by rw [hΩtop]; trivial
  let y : Ω := ⟨x, hxΩ⟩
  have hΩelem : IsElementaryAbelian p Ω :=
    IsElementaryAbelian.omega₁_of_isMulCommutative F
  have hpow : y ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hΩelem.exponent_dvd_p y
  simpa [y] using congrArg Subtype.val hpow

private theorem huppert_XI_6_8_irreducible_complement_action
    {p : ℕ} [Fact p.Prime]
    {D F : Type*} [Group D] [Finite D] [Group F] [Finite F]
    [Nontrivial F] [IsElementaryAbelian p F] [MulDistribMulAction D F]
    (hFcard : ∃ f : ℕ, 0 < f ∧ Nat.card F = p ^ f)
    (hhalf : 2 * Nat.card D = Nat.card F - 1)
    (hfree : ∀ d : D, d ≠ 1 → ∀ x : F, d • x = x → x = 1) :
    let rho : Representation (ZMod p) D (Additive F) :=
      Theory.Representation.ofElementaryAbelianAction (A := D) (G := F) (p := p)
    ∀ W : Submodule (ZMod p) (Additive F),
      (∀ d : D, ∀ x : Additive F, x ∈ W → rho d x ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
  classical
  change ∀ W : Submodule (ZMod p) (Additive F),
    (∀ d : D, ∀ x : Additive F, x ∈ W →
      Theory.Representation.ofElementaryAbelianAction
        (A := D) (G := F) (p := p) d x ∈ W) → W = ⊥ ∨ W = ⊤
  let rho : Representation (ZMod p) D (Additive F) :=
    Theory.Representation.ofElementaryAbelianAction (A := D) (G := F) (p := p)
  obtain ⟨f, hf, hFcard⟩ := hFcard
  have hpge : 3 ≤ p := by
    have hp2 := (Fact.out : p.Prime).two_le
    rcases (Fact.out : p.Prime).eq_two_or_odd' with hpEq | hpOdd
    · subst p
      have hcardEven : Even (Nat.card F) := by
        rw [hFcard]
        exact Even.pow_of_ne_zero even_two hf.ne'
      have hsubOdd : Odd (Nat.card F - 1) :=
        Nat.Even.sub_odd Nat.card_pos hcardEven odd_one
      have hleftEven : Even (2 * Nat.card D) := even_two.mul_right _
      rw [hhalf] at hleftEven
      rcases hsubOdd with ⟨r, hr⟩
      rcases hleftEven with ⟨s, hs⟩
      omega
    · rcases hpOdd with ⟨k, hk⟩
      omega
  intro W hW
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  right
  by_contra hWtop
  let : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).2 hWbot
  let : MulDistribMulAction D (Multiplicative W) := {
    smul := fun d x => Multiplicative.ofAdd
      ⟨rho d x.toAdd.1, hW d x.toAdd.1 x.toAdd.2⟩
    one_smul := by
      intro x
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change rho 1 x.toAdd.1 = x.toAdd.1
      rw [map_one]
      rfl
    mul_smul := by
      intro d e x
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change rho (d * e) x.toAdd.1 = rho d (rho e x.toAdd.1)
      rw [map_mul]
      rfl
    smul_one := by
      intro d
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change rho d 0 = 0
      exact map_zero (rho d)
    smul_mul := by
      intro d x y
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      change rho d (x.toAdd.1 + y.toAdd.1) =
        rho d x.toAdd.1 + rho d y.toAdd.1
      exact map_add (rho d) _ _ }
  have hfreeW : ∀ d : D, d ≠ 1 → ∀ x : Multiplicative W,
      d • x = x → x = 1 := by
    intro d hd x hfix
    have hfixV : rho d x.toAdd.1 = x.toAdd.1 :=
      congrArg (fun y : Multiplicative W => y.toAdd.1) hfix
    have hfixF : d • x.toAdd.1.toMul = x.toAdd.1.toMul := by
      simpa [rho] using congrArg Additive.toMul hfixV
    have hxone := hfree d hd x.toAdd.1.toMul hfixF
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    exact hxone
  have hdiv : Nat.card D ∣ Nat.card (Multiplicative W) - 1 :=
    xi68_actor_card_dvd_group_card_sub_one hfreeW
  have hWgt : 1 < Nat.card W := Finite.one_lt_card
  have hDle : Nat.card D ≤ Nat.card W - 1 := by
    apply Nat.le_of_dvd (Nat.sub_pos_of_lt hWgt)
    have hcardEq : Nat.card (Multiplicative W) = Nat.card W :=
      Nat.card_congr (Multiplicative.toAdd)
    simpa [hcardEq] using hdiv
  let : FiniteDimensional (ZMod p) (Additive F) := Module.Finite.of_finite
  have hfinlt : Module.finrank (ZMod p) W <
      Module.finrank (ZMod p) (Additive F) := Submodule.finrank_lt hWtop
  have hcardW : Nat.card W = p ^ Module.finrank (ZMod p) W := by
    simpa [ZMod.card p] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := W))
  have hcardV : Nat.card F = p ^ Module.finrank (ZMod p) (Additive F) := by
    have hcardAdd : Nat.card (Additive F) = Nat.card F :=
      (Nat.card_congr (Additive.ofMul)).symm
    simpa [ZMod.card p, hcardAdd] using
      (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive F))
  have hpowStep : p ^ (Module.finrank (ZMod p) W + 1) ≤
      p ^ Module.finrank (ZMod p) (Additive F) :=
    Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  have htwocard : 2 * Nat.card W ≤ Nat.card F := by
    rw [hcardW, hcardV]
    calc
      2 * p ^ Module.finrank (ZMod p) W ≤
          p * p ^ Module.finrank (ZMod p) W := by
        exact Nat.mul_le_mul_right _ (by omega)
      _ = p ^ (Module.finrank (ZMod p) W + 1) := by rw [pow_succ']
      _ ≤ _ := hpowStep
  omega

set_option maxHeartbeats 800000 in
private theorem huppert_XI_6_8_field_coordinates
    {H : Type u} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFcomm : IsMulCommutative F)
    (hDcomm : IsMulCommutative D)
    (hhalf : 2 * Nat.card D = Nat.card F - 1)
    (p f : ℕ) (hp : Nat.Prime p) (hf : 0 < f)
    (hFcard : Nat.card F = p ^ f) :
    ∃ (K : Type w) (_ : Field K) (_ : Finite K),
      ∃ eAdd : Additive F ≃+ K,
        ∃ scalar : D →* Kˣ, Function.Injective scalar ∧
          ∀ (d : D) (x : F),
            eAdd (Additive.ofMul
              (⟨(d : H) * (x : H) * (d : H)⁻¹,
                hFrob.normal.conj_mem (x : H) x.property (d : H)⟩ : F)) =
              eAdd (Additive.ofMul x) * (scalar d : K) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : IsMulCommutative F := hFcomm
  let : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  have hElem : IsElementaryAbelian p F :=
    huppert_XI_6_8_elementary_kernel F D hFrob hFcomm
      (by omega) p f hp hf hFcard
  let : IsElementaryAbelian p F := hElem
  let : F.Normal := hFrob.normal
  let : MulDistribMulAction D F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D F
      (Subgroup.le_normalizer_of_normal (H := F))
  let rho : Representation (ZMod p) D (Additive F) :=
    Theory.Representation.ofElementaryAbelianAction (A := D) (G := F) (p := p)
  have hfree : ∀ d : D, d ≠ 1 → ∀ x : F, d • x = x → x = 1 := by
    intro d hd x hfix
    have hconj : (d : H) * (x : H) * (d : H)⁻¹ = (x : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg (fun y : F => (y : H)) hfix
    have hcomm : (d : H) * (x : H) = (x : H) * (d : H) := by
      have h := congrArg (fun z : H => z * (d : H)) hconj
      simpa [mul_assoc] using h
    have hxcent : (x : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hxcent
    exact Subtype.ext (by simpa using hxbot)
  have hrho : Function.Injective rho := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
    rw [eq_bot_iff]
    intro d hdFix
    by_contra hd
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
    have hdx : d • x = x :=
      (mem_fixingSubgroup_iff (M := D) (s := (Set.univ : Set F))).mp
        hdFix x (Set.mem_univ x)
    exact hx (hfree d hd x hdx)
  have hirr := huppert_XI_6_8_irreducible_complement_action
    (D := D) (F := F) ⟨f, hf, hFcard⟩ hhalf hfree
  obtain ⟨K, hKfield, hKfinite, eAdd, scalar, hscalar, haction⟩ :=
    huppert_XI_6_8_scalar_coordinates
      f hf hFcard hDcomm rho hrho hirr
  refine ⟨K, hKfield, hKfinite, eAdd, scalar, hscalar, ?_⟩
  intro d x
  have htemp := haction d (Additive.ofMul x)
  calc
    eAdd (Additive.ofMul
      (⟨(d : H) * (x : H) * (d : H)⁻¹,
        hFrob.normal.conj_mem (x : H) x.property (d : H)⟩ : F))
        = eAdd (rho d (Additive.ofMul x)) := by
          have h1 : (⟨(d : H) * (x : H) * (d : H)⁻¹,
            hFrob.normal.conj_mem (x : H) x.property (d : H)⟩ : F) = d • x :=
            Subtype.ext ((Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
              (A := D) (K := F) d x).symm)
          calc
            eAdd (Additive.ofMul
              (⟨(d : H) * (x : H) * (d : H)⁻¹,
                hFrob.normal.conj_mem (x : H) x.property (d : H)⟩ : F))
                = eAdd (Additive.ofMul (d • x)) := by rw [h1]
            _ = eAdd (rho d (Additive.ofMul x)) := by
              rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    _ = eAdd (Additive.ofMul x) * (scalar d : K) := htemp
private theorem huppert_XI_6_8_quadraticChar_div_nonsquare
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ¬ IsSquare (x / y)) :
    quadraticChar K x = -(quadraticChar K y) := by
  have hqxy : quadraticChar K (x / y) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hxy
  have hxD := quadraticChar_dichotomy (F := K) hx
  have hyD := quadraticChar_dichotomy (F := K) hy
  have hmul := congrArg (quadraticChar K)
    (show x / y = x * y⁻¹ by rw [div_eq_mul_inv])
  simp only [map_mul] at hmul
  have hinv : quadraticChar K y⁻¹ = quadraticChar K y := by
    by_cases hysq : IsSquare y
    · rw [(quadraticChar_one_iff_isSquare hy).2 hysq,
        (quadraticChar_one_iff_isSquare (inv_ne_zero hy)).2 hysq.inv]
    · have hyinv : ¬ IsSquare y⁻¹ := by
        intro h
        apply hysq
        simpa using h.inv
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr hysq,
        quadraticChar_neg_one_iff_not_isSquare.mpr hyinv]
  rw [hinv] at hmul
  rw [hmul] at hqxy
  rcases hxD with hx1 | hxn <;> rcases hyD with hy1 | hyn <;> simp_all

private theorem huppert_XI_6_8_quadraticChar_product_relation
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (r u m k : K) (hu : u ≠ 0)
    (hUsq : IsSquare u) (hneg : ¬ IsSquare (-1 : K))
    (hmsign : quadraticChar K m = -(quadraticChar K k))
    (hrel : r * u = -m) :
    quadraticChar K r = quadraticChar K k := by
  have hUchar : quadraticChar K u = 1 :=
    (quadraticChar_one_iff_isSquare hu).2 hUsq
  have hNegchar : quadraticChar K (-1 : K) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hneg
  have hchar := congrArg (quadraticChar K) hrel
  have hnegm : -m = (-1 : K) * m := by ring
  rw [hnegm] at hchar
  simp only [map_mul] at hchar
  rw [hUchar, mul_one, hNegchar, neg_one_mul, hmsign] at hchar
  simpa using hchar

private theorem huppert_XI_6_8_odd_theta_inverse
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hneg : ¬ IsSquare (-1 : K))
    (theta : Kˣ → Kˣ)
    (hInv : ∀ x : Kˣ, theta (theta x) = x)
    (hEquiv : ∀ x u : Kˣ, IsSquare (u : K) →
      theta (x * u) = theta x * u⁻¹)
    (hrel : ∀ k : Kˣ, ∃ m u : Kˣ,
      IsSquare (u : K) ∧
        (theta m : K) = -(theta k : K) ∧
        (m : K) + (theta (-k) : K) * (u : K) = 0) :
    let c := theta (1 : Kˣ)
    ¬ IsSquare (c : K) ∧
      ∀ x : Kˣ, theta x = c * x⁻¹ := by
  classical
  let c := theta (1 : Kˣ)
  have hNegChar : quadraticChar K (-1 : K) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hneg
  have hswapChar : ∀ x : Kˣ,
      quadraticChar K (theta x : K) = -(quadraticChar K (x : K)) := by
    intro x
    let k : Kˣ := -x
    obtain ⟨m, u, huSq, hthetaM, hsum⟩ := hrel k
    let v : Kˣ := m * k⁻¹
    have hvval : (v : K) = (m : K) / (k : K) := by
      simp [v, div_eq_mul_inv]
    have hvNotSq : ¬ IsSquare ((v : K)) := by
      intro hvSq
      have heq := hEquiv k v hvSq
      have hkv : k * v = m := by simp [v, mul_comm]
      rw [hkv] at heq
      have heqVal := congrArg (fun z : Kˣ => (z : K)) heq
      change (theta m : K) = (theta k : K) * ((v⁻¹ : Kˣ) : K) at heqVal
      have hvInvEq : ((v⁻¹ : Kˣ) : K) = -1 := by
        apply mul_left_cancel₀ (Units.ne_zero (theta k))
        calc
          (theta k : K) * ((v⁻¹ : Kˣ) : K) = (theta m : K) := heqVal.symm
          _ = -(theta k : K) := hthetaM
          _ = (theta k : K) * (-1 : K) := by ring
      apply hneg
      rw [← hvInvEq]
      simpa using hvSq.inv
    have hmkNotSq : ¬ IsSquare ((m : K) / (k : K)) := by
      simpa [hvval] using hvNotSq
    have hmsign : quadraticChar K (m : K) =
        -(quadraticChar K (k : K)) :=
      huppert_XI_6_8_quadraticChar_div_nonsquare (m : K) (k : K)
        (Units.ne_zero m) (Units.ne_zero k) hmkNotSq
    have hprod : (theta (-k) : K) * (u : K) = -(m : K) :=
      eq_neg_of_add_eq_zero_right hsum
    have hcharThetaNegK : quadraticChar K (theta (-k) : K) =
        quadraticChar K (k : K) :=
      huppert_XI_6_8_quadraticChar_product_relation (theta (-k) : K) (u : K) (m : K) (k : K)
        (Units.ne_zero u) huSq hneg hmsign hprod
    have hkval : (-k : Kˣ) = x := by
      dsimp [k]
      simp
    rw [hkval] at hcharThetaNegK
    have hkChar : quadraticChar K (k : K) =
        -(quadraticChar K (x : K)) := by
      dsimp [k]
      calc
        quadraticChar K (-(x : K)) =
            quadraticChar K ((-1 : K) * (x : K)) := by rw [neg_one_mul]
        _ = quadraticChar K (-1 : K) * quadraticChar K (x : K) := map_mul _ _ _
        _ = -(quadraticChar K (x : K)) := by rw [hNegChar, neg_one_mul]
    exact hcharThetaNegK.trans hkChar
  have hcNotSq : ¬ IsSquare (c : K) := by
    have hcChar := hswapChar (1 : Kˣ)
    have hcNeg : quadraticChar K (c : K) = -1 := by simpa [c] using hcChar
    exact quadraticChar_neg_one_iff_not_isSquare.mp hcNeg
  refine ⟨hcNotSq, ?_⟩
  intro x
  by_cases hxSq : IsSquare (x : K)
  · simpa [c] using hEquiv (1 : Kˣ) x hxSq
  · have hxChar : quadraticChar K (x : K) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hxSq
    have hyChar : quadraticChar K (theta x : K) = 1 := by
      rw [hswapChar x, hxChar]
      norm_num
    have hySq : IsSquare (theta x : K) :=
      (quadraticChar_one_iff_isSquare (Units.ne_zero (theta x))).mp hyChar
    have hyFormula : theta (theta x) = c * (theta x)⁻¹ := by
      simpa [c] using hEquiv (1 : Kˣ) (theta x) hySq
    have heq : x = c * (theta x)⁻¹ := (hInv x).symm.trans hyFormula
    have hxy : x * theta x = c := by
      calc
        x * theta x = (c * (theta x)⁻¹) * theta x :=
          congrArg (fun z : Kˣ => z * theta x) heq
        _ = c := by group
    calc
      theta x = x⁻¹ * (x * theta x) := by group
      _ = x⁻¹ * c := by rw [hxy]
      _ = c * x⁻¹ := mul_comm _ _
private theorem xi68_gl2_scalar_smul_onePoint
    (K : Type*) [Field K] [DecidableEq K]
    (a : Kˣ) (x : OnePoint K) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a • x = x := by
  cases x with
  | infty =>
      rw [OnePoint.smul_infty_eq_self_iff]
      simp
  | coe x =>
      rw [OnePoint.smul_some_eq_ite]
      simp [Units.ne_zero]

private theorem xi68_gl2_mem_center_of_onePoint_trivial
    (K : Type*) [Field K] [DecidableEq K]
    (g : GL (Fin 2) K) (hfix : ∀ x : OnePoint K, g • x = x) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  have h10 : g 1 0 = 0 :=
    OnePoint.smul_infty_eq_self_iff.mp (hfix (OnePoint.infty : OnePoint K))
  have hzero := hfix (↑(0 : K) : OnePoint K)
  rw [OnePoint.smul_some_eq_ite] at hzero
  have h11 : g 1 1 ≠ 0 := by
    intro h
    simp [h10, h] at hzero
  have h01 : g 0 1 = 0 := by
    simp [h10, h11] at hzero
    exact hzero
  have hone := hfix (↑(1 : K) : OnePoint K)
  rw [OnePoint.smul_some_eq_ite] at hone
  have hdiag : g 0 0 = g 1 1 := by
    simp [h10, h01, h11] at hone
    exact (div_eq_one_iff_eq h11).mp hone
  apply Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨g 0 0, ?_⟩
  symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, h10, h01, hdiag]

private theorem xi68_gl2_onePointPermHom_ker
    (K : Type*) [Field K] [DecidableEq K] :
    (MulAction.toPermHom (GL (Fin 2) K) (OnePoint K)).ker =
      Subgroup.center (GL (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply xi68_gl2_mem_center_of_onePoint_trivial K g
    intro x
    simpa using DFunLike.congr_fun hg x
  · intro hg
    rcases Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hg with
      ⟨a, ha⟩
    rw [Equiv.Perm.ext_iff]
    intro x
    have ha0 : a ≠ 0 := by
      intro ha0
      have hgzero : (g : Matrix (Fin 2) (Fin 2) K) = 0 := by
        rw [← ha]
        simp [ha0]
      exact Units.ne_zero g hgzero
    let aUnit : Kˣ := Units.mk0 a ha0
    have hu : Matrix.GeneralLinearGroup.scalar (Fin 2) aUnit = g := by
      apply Units.ext
      change Matrix.scalar (Fin 2) (aUnit : K) =
        (g : Matrix (Fin 2) (Fin 2) K)
      simpa [aUnit] using ha
    rw [← hu]
    exact xi68_gl2_scalar_smul_onePoint K aUnit x

private noncomputable def xi68_pgl2_onePointPermHom
    (K : Type*) [Field K] [DecidableEq K] :
    Matrix.ProjGenLinGroup (Fin 2) K →* Equiv.Perm (OnePoint K) :=
  Matrix.ProjGenLinGroup.lift
    (MulAction.toPermHom (GL (Fin 2) K) (OnePoint K)) (by
      ext a x
      exact xi68_gl2_scalar_smul_onePoint K a x)

private theorem xi68_pgl2_onePointPermHom_injective
    (K : Type*) [Field K] [DecidableEq K] :
    Function.Injective (xi68_pgl2_onePointPermHom K) := by
  intro q1 q2 hq
  obtain ⟨g1, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q1
  obtain ⟨g2, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective q2
  have hperm :
      MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) g1 =
        MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) g2 := by
    simpa [xi68_pgl2_onePointPermHom] using hq
  apply (inv_mul_eq_one).mp
  rw [← map_inv, ← map_mul, ← MonoidHom.mem_ker,
    Matrix.ProjGenLinGroup.ker_mk, ← xi68_gl2_onePointPermHom_ker,
    MonoidHom.mem_ker]
  change MulAction.toPermHom (GL (Fin 2) K) (OnePoint K) (g1⁻¹ * g2) = 1
  rw [map_mul, map_inv, hperm]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem huppert_XI_6_8_odd_pslRange_of_tau
    {G : Type u} {K : Type w}
    [Group G] [Field K] [Finite K] [DecidableEq K]
    (rho : G →* Equiv.Perm (Option K))
    (A : Subgroup (Equiv.Perm (Option K)))
    (tau : Equiv.Perm (Option K))
    (affinePerm : K → Kˣ → Equiv.Perm (Option K))
    (hAffinePerm : ∀ b : K, ∀ a : Kˣ, ∀ y : Option K,
      affinePerm b a y = Option.map (fun x => b + x * (a : K)) y)
    (hA : ∀ sigma : Equiv.Perm (Option K), sigma ∈ A →
      ∃ b : K, ∃ a : Kˣ,
        IsSquare (a : K) ∧ sigma = affinePerm b a)
    (c : Kˣ) (hnegc : IsSquare (-(c : K)))
    (hTau : ∀ y : Option K,
      tau y = match y with
        | none => some 0
        | some x => if x = 0 then none else some ((c : K) / x))
    (hRange :
      (rho.range : Set (Equiv.Perm (Option K))) =
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))))
    (hRangeCard : Nat.card rho.range =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :
    Nonempty (rho.range ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  classical
  let pglPerm := xi68_pgl2_onePointPermHom K
  obtain ⟨_, _, iota, _, hiota, hiotaMk, _⟩ :=
    huppert_blackburn_XI_example_1_3_a K
  let pslPerm : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →*
      Equiv.Perm (Option K) := pglPerm.comp iota
  have hpslPerm : Function.Injective pslPerm := by
    intro x y hxy
    apply hiota
    apply xi68_pgl2_onePointPermHom_injective K
    exact hxy
  let J : Subgroup (Equiv.Perm (Option K)) := pslPerm.range
  have hA_le_J : A ≤ J := by
    intro sigma hsigma
    obtain ⟨b, a, haSq, rfl⟩ := hA sigma hsigma
    rcases haSq with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hrz
      subst r
      exact Units.ne_zero a (by simpa using hr)
    let rU : Kˣ := Units.mk0 r hr0
    let M : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : K), b; 0, 1] (by
        simpa [Matrix.det_fin_two] using Units.ne_zero a)
    let S : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![r, b * r⁻¹; 0, r⁻¹], by
        simp [Matrix.det_fin_two, hr0]⟩
    have hMS : M = Matrix.GeneralLinearGroup.scalar (Fin 2) rU *
        Matrix.SpecialLinearGroup.toGL S := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [M, S, rU, Matrix.mul_apply] using hr
      · simp [M, S, rU, Matrix.mul_apply, hr0]
        field_simp
      · simp [M, S, rU, Matrix.mul_apply]
      · simp [M, S, rU, Matrix.mul_apply, hr0]
    have hmk : Matrix.ProjGenLinGroup.mk M =
        iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S) := by
      rw [hiotaMk]
      rw [hMS, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    refine ⟨QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S, ?_⟩
    change pglPerm
        (iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S)) =
      affinePerm b a
    rw [← hmk]
    apply Equiv.ext
    intro y
    cases y with
    | infty =>
        change _ = affinePerm b a none
        rw [hAffinePerm b a none]
        simp only [pglPerm, xi68_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change M • (OnePoint.infty : OnePoint K) = OnePoint.infty
        rw [OnePoint.smul_infty_eq_self_iff]
        simp [M]
    | coe x =>
        change _ = affinePerm b a (some x)
        rw [hAffinePerm b a (some x)]
        simp only [pglPerm, xi68_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change M • (x : OnePoint K) = (b + x * (a : K) : K)
        rw [OnePoint.smul_some_eq_ite]
        simp [M, add_comm, mul_comm]
  have hTau_mem_J : tau ∈ J := by
    rcases hnegc with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hrz
      subst r
      exact Units.ne_zero c (by simpa using hr)
    let rU : Kˣ := Units.mk0 r hr0
    let W : GL (Fin 2) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, (c : K); 1, 0] (by
        simpa [Matrix.det_fin_two] using Units.ne_zero c)
    let S : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![0, -r; r⁻¹, 0], by
        simp [Matrix.det_fin_two, hr0]⟩
    have hrc : (c : K) = -(r * r) := by
      calc
        (c : K) = -(-(c : K)) := by simp
        _ = -(r * r) := congrArg Neg.neg hr
    have hWS : W = Matrix.GeneralLinearGroup.scalar (Fin 2) rU *
        Matrix.SpecialLinearGroup.toGL S := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j
      · simp [W, S, rU, Matrix.mul_apply]
      · simp [W, S, rU, Matrix.mul_apply, hrc]
      · simp [W, S, rU, Matrix.mul_apply, hr0]
      · simp [W, S, rU, Matrix.mul_apply]
    have hmk : Matrix.ProjGenLinGroup.mk W =
        iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S) := by
      rw [hiotaMk]
      rw [hWS, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    refine ⟨QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S, ?_⟩
    change pglPerm
        (iota (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) S)) = tau
    rw [← hmk]
    apply Equiv.ext
    intro y
    cases y with
    | infty =>
        change _ = tau none
        rw [hTau none]
        simp only [pglPerm, xi68_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change W • (OnePoint.infty : OnePoint K) = (0 : K)
        rw [OnePoint.smul_infty_eq_ite]
        simp [W]
    | coe x =>
        change _ = tau (some x)
        rw [hTau (some x)]
        simp only [pglPerm, xi68_pgl2_onePointPermHom,
          Matrix.ProjGenLinGroup.lift_mk]
        change W • (x : OnePoint K) =
          if x = 0 then OnePoint.infty else ((c : K) / x : K)
        rw [OnePoint.smul_some_eq_ite]
        by_cases hx : x = 0 <;> simp [W, hx]
  have hRange_le_J : rho.range ≤ J := by
    intro sigma hsigma
    have hsigma' : sigma ∈
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))) := by
      rw [← hRange]
      exact hsigma
    rcases hsigma' with hsigmaA | hsigmaD
    · exact hA_le_J hsigmaA
    · rcases DoubleCoset.mem_doubleCoset.mp hsigmaD with
        ⟨a1, ha1, a2, ha2, rfl⟩
      exact J.mul_mem (J.mul_mem (hA_le_J ha1) hTau_mem_J)
        (hA_le_J ha2)
  have hJcard : Nat.card J =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    (Nat.card_congr (Equiv.ofInjective pslPerm hpslPerm)).symm
  have hRangeEq : rho.range = J := by
    apply Subgroup.eq_of_le_of_card_ge hRange_le_J
    rw [hJcard, hRangeCard]
  let pslToJ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →* J :=
    pslPerm.codRestrict J (fun x => ⟨x, rfl⟩)
  have hpslToJ : Function.Bijective pslToJ := by
    constructor
    · intro x y hxy
      apply hpslPerm
      exact congrArg Subtype.val hxy
    · intro y
      rcases y.property with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  let ePSLJ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* J :=
    MulEquiv.ofBijective pslToJ hpslToJ
  exact ⟨(MulEquiv.subgroupCongr hRangeEq).trans ePSLJ.symm⟩
private theorem huppert_XI_6_8_odd_swap_coordinates
    {G : Type u} {Omega : Type v} {K : Type w}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    [Field K] [Finite K] [DecidableEq K]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat : ∀ g : G, g ≠ 1 → ∀ a b c : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hhalf : 2 * Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) = Nat.card F - 1)
    (eAdd : Additive F ≃+ K)
    (scalar : MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) →* Kˣ)
    (hscalar : Function.Injective scalar)
    (haction : ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      ∀ x : F,
      eAdd (Additive.ofMul
        (⟨(d : MulAction.stabilizer G a) *
            (x : MulAction.stabilizer G a) *
            (d : MulAction.stabilizer G a)⁻¹,
          hFrob.normal.conj_mem
            (x : MulAction.stabilizer G a) x.property
            (d : MulAction.stabilizer G a)⟩ : F)) =
        eAdd (Additive.ofMul x) * (scalar d : K)) :
    ∃ (ePoint : Omega ≃ Option K) (s : G) (c : Kˣ),
      ePoint a = none ∧ ePoint b = some 0 ∧
      s ^ 2 = 1 ∧ s • a = b ∧ s • b = a ∧
      (¬ IsSquare (-1 : K)) ∧
      (¬ IsSquare (c : K)) ∧
      (∀ f : F,
        ePoint (((f : MulAction.stabilizer G a) : G) • b) =
          some (eAdd (Additive.ofMul f))) ∧
      (∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        ∀ y : Option K,
          ePoint ((((d : MulAction.stabilizer G a) : G)) • ePoint.symm y) =
            Option.map (fun x => x * (scalar d : K)) y) ∧
      ∀ y : Option K,
        ePoint (s • ePoint.symm y) =
          match y with
          | none => some 0
          | some x => if x = 0 then none else some ((c : K) / x) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Odd (Nat.card D) at hodd
  change 2 * Nat.card D = Nat.card F - 1 at hhalf
  change D →* Kˣ at scalar
  obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
      htwo a b hab F hFrob eAdd
  have hKernelAction :=
    huppert_blackburn_XI_projectivePointEquiv_kernel_action
      a b F eAdd ePoint hPointA hPointF
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  have hPointB_symm : ePoint.symm (some 0) = b := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointB]
  have hDAction (d : D) (y : Option K) :
      ePoint ((((d : H) : G)) • ePoint.symm y) =
        Option.map (fun x => x * (scalar d : K)) y := by
    cases y with
    | none =>
        rw [hPointA_symm, (d : H).property, hPointA]
        rfl
    | some x =>
        let r : F := (eAdd.symm x).toMul
        let q : F :=
          ⟨(d : H) * (r : H) * (d : H)⁻¹,
            hFrob.normal.conj_mem (r : H) r.property (d : H)⟩
        have hPointR : ePoint (((r : H) : G) • b) = some x := by
          rw [hPointF]
          change some (eAdd (eAdd.symm x)) = some x
          rw [eAdd.apply_symm_apply]
        have hPointR_symm : ePoint.symm (some x) = (((r : H) : G) • b) := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointR]
        have h_stab : d • (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
          MulAction.mem_stabilizer_iff.mp d.property
        have hdb : (((d : H) : G)) • b = b := by
          have h_subtype := MulAction.mem_stabilizer_iff.mp d.property
          have h_val := congrArg Subtype.val h_subtype
          simpa [MulAction.subgroup_smul_def] using h_val
        calc
          ePoint ((((d : H) : G)) • ePoint.symm (some x)) =
              ePoint ((((d : H) : G)) • (((r : H) : G) • b)) := by
                rw [hPointR_symm]
          _ = ePoint (((((d : H) : G)) * ((r : H) : G)) • b) := by rw [mul_smul]
          _ = ePoint (((((q : H) : G)) * (((d : H) : G))) • b) := by
                congr 2
                dsimp [q]
                group
          _ = ePoint (((q : H) : G) • b) := by rw [mul_smul, hdb]
          _ = some (eAdd (Additive.ofMul q)) := hPointF q
          _ = some (x * (scalar d : K)) := by
                congr 1
                simpa [q, r] using haction d r
  obtain ⟨s, hssq, hsa, hsb⟩ :=
    zassenhaus_odd_twoPointStabilizer_exists_swap_involution
      htwo hat a b hab F hFrob hodd
  have hsne : s ≠ 1 := by
    intro hs
    apply hab
    simpa [hs] using hsa
  let tau : Equiv.Perm (Option K) :=
    ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
  have hTauApply (y : Option K) : tau y = ePoint (s • ePoint.symm y) := rfl
  have hTauPoint (y : Option K) :
      ePoint.symm (tau y) = s • ePoint.symm y := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hTauApply]
  have hTauInf : tau none = some 0 := by
    rw [hTauApply, hPointA_symm, hsa, hPointB]
  have hTauZero : tau (some 0) = none := by
    rw [hTauApply, hPointB_symm, hsb, hPointA]
  have hTauSq (y : Option K) : tau (tau y) = y := by
    rw [hTauApply, hTauApply, ePoint.symm_apply_apply]
    rw [← mul_smul, ← pow_two, hssq, one_smul, ePoint.apply_symm_apply]
  have hTauSome : ∀ x : Kˣ, ∃ y : Kˣ,
      tau (some (x : K)) = some (y : K) := by
    intro x
    cases h : tau (some (x : K)) with
    | none =>
        exfalso
        have hx0 := tau.injective (h.trans hTauZero.symm)
        exact Units.ne_zero x (Option.some.inj hx0)
    | some y =>
        have hy : y ≠ 0 := by
          intro hy0
          subst y
          have hxnone := tau.injective (h.trans hTauInf.symm)
          exact (Option.some_ne_none (x : K)) hxnone
        exact ⟨Units.mk0 y hy, by simpa⟩
  choose theta hTheta using hTauSome
  have hThetaInv (x : Kˣ) : theta (theta x) = x := by
    apply Units.ext
    exact Option.some.inj (by
      have h := hTauSq (some (x : K))
      rw [hTheta x, hTheta (theta x)] at h
      exact h)
  have hKcard : Nat.card K = Nat.card F := by
    calc
      Nat.card K = Nat.card (Additive F) := Nat.card_congr eAdd.symm.toEquiv
      _ = Nat.card F := rfl
  have hhalfK : 2 * Nat.card D = Nat.card K - 1 := by
    rw [hKcard]
    exact hhalf
  have hscalarSq : scalar.range = (powMonoidHom 2 : Kˣ →* Kˣ).range :=
    huppert_XI_6_8_scalar_range_eq_squares scalar hscalar hhalfK hodd
  have hThetaEquiv (x u : Kˣ) (huSq : IsSquare (u : K)) :
      theta (x * u) = theta x * u⁻¹ := by
    have huMem : u ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
      rcases huSq with ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        intro hrz
        exact Units.ne_zero u (by simpa [hrz] using hr)
      let ru : Kˣ := Units.mk0 r hr0
      refine ⟨ru, ?_⟩
      apply Units.ext
      simpa [ru, pow_two] using hr.symm
    rw [← hscalarSq] at huMem
    rcases huMem with ⟨d, hd⟩
    have hsInv := zassenhaus_odd_twoPointStabilizer_swap_inverts
      htwo hat hsimple a b hab F hFrob hodd s hsa hsb d
    have hsinv : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hssq)
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    have hmove : s * (((d : H) : G)) =
        ((((d⁻¹ : D) : H) : G)) * s := by
      calc
        s * (((d : H) : G)) =
            (s * (((d : H) : G)) * s⁻¹) * s := by
          rw [hsinv]
          calc
            s * (((d : H) : G)) = s * (((d : H) : G)) * 1 := by simp
            _ = s * (((d : H) : G)) * (s * s) := by rw [hss]
            _ = (s * (((d : H) : G)) * s) * s := by group
        _ = ((((d⁻¹ : D) : H) : G)) * s := by rw [hsInv]
    have hDPoint (q : D) (z : Option K) :
        ePoint.symm (Option.map (fun t => t * (scalar q : K)) z) =
          (((q : H) : G)) • ePoint.symm z := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hDAction]
    apply Units.ext
    apply Option.some.inj
    calc
      some ((theta (x * u) : K)) = tau (some ((x * u : Kˣ) : K)) :=
        (hTheta (x * u)).symm
      _ = ePoint (s • ePoint.symm
          (Option.map (fun t => t * (scalar d : K)) (some (x : K)))) := by
        rw [hd]
        rfl
      _ = ePoint (s • ((((d : H) : G)) • ePoint.symm (some (x : K)))) := by
        rw [hDPoint]
      _ = ePoint (((((d⁻¹ : D) : H) : G)) •
          (s • ePoint.symm (some (x : K)))) := by
        rw [← mul_smul, ← mul_smul, hmove]
      _ = ePoint (((((d⁻¹ : D) : H) : G)) •
          ePoint.symm (tau (some (x : K)))) := by rw [hTauPoint]
      _ = some ((theta x * u⁻¹ : Kˣ) : K) := by
        rw [hDAction, hTheta]
        apply congrArg some
        change (theta x : K) * (scalar d⁻¹ : K) =
          ((theta x * u⁻¹ : Kˣ) : K)
        have hdinv : scalar d⁻¹ = u⁻¹ := by
          simpa using congrArg Inv.inv hd
        exact congrArg (fun z : Kˣ => (z : K))
          (congrArg (fun z : Kˣ => theta x * z) hdinv)
  have hThetaRel : ∀ k : Kˣ, ∃ m u : Kˣ,
      IsSquare (u : K) ∧
        (theta m : K) = -(theta k : K) ∧
        (m : K) + (theta (-k) : K) * (u : K) = 0 := by
    intro k
    let f : F := (eAdd.symm (k : K)).toMul
    have hf : f ≠ 1 := by
      intro hf1
      have hk0 : (k : K) = 0 := by
        calc
          (k : K) = eAdd (eAdd.symm (k : K)) := (eAdd.apply_symm_apply _).symm
          _ = eAdd (Additive.ofMul f) := rfl
          _ = eAdd 0 := by rw [hf1]; rfl
          _ = 0 := eAdd.map_zero
      exact Units.ne_zero k hk0
    obtain ⟨f1, f2, d, hdecomp⟩ :=
      zassenhaus_swap_kernel_bruhat_decomposition
        htwo a b hab F hFrob s hssq hsa hsb f hf
    let ell : K := eAdd (Additive.ofMul f1)
    let m0 : K := eAdd (Additive.ofMul f2)
    let u0 : Kˣ := scalar d
    have hKernelPoint (q : F) (z : Option K) :
        ePoint.symm (Option.map (fun t => eAdd (Additive.ofMul q) + t) z) =
          (((q : H) : G)) • ePoint.symm z := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply]
      simpa using (hKernelAction q z).symm
    have hDPoint (q : D) (z : Option K) :
        ePoint.symm (Option.map (fun t => t * (scalar q : K)) z) =
          (((q : H) : G)) • ePoint.symm z := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hDAction]
    have hTauPoint' (z : Option K) : ePoint.symm (tau z) =
        s • ePoint.symm z := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hTauApply]
    have hkCoord : eAdd (Additive.ofMul f) = (k : K) := by simp [f]
    have hCoord (z : Option K) :
        tau (Option.map (fun t => (k : K) + t) (tau z)) =
          Option.map (fun t => ell + t)
            (tau (Option.map (fun t => m0 + t)
              (Option.map (fun t => t * (u0 : K)) z))) := by
      apply ePoint.symm.injective
      rw [← hkCoord]
      rw [hTauPoint', hKernelPoint, hTauPoint', hKernelPoint,
        hTauPoint', hKernelPoint, hDPoint]
      simp only [← mul_smul]
      simpa [ell, m0, u0, mul_assoc] using
        congrArg (fun q : G => q • ePoint.symm z) hdecomp
    have hThetaK : (theta k : K) = ell := by
      have h := hCoord none
      exact Option.some.inj (by simpa [hTauInf, hTheta] using h)
    have hTauM : tau (some m0) = some (-ell) := by
      have h := hCoord (some 0)
      simp only [hTauZero, Option.map_none, hTauInf, Option.map_some] at h
      cases hm : tau (some m0) with
      | none => simp [hm] at h
      | some z =>
          have hz : ell + z = 0 := Option.some.inj (by simpa [hm] using h.symm)
          have hzneg : z = -ell := eq_neg_of_add_eq_zero_right hz
          simpa [hm, hzneg]
    have hm0 : m0 ≠ 0 := by
      intro hm
      rw [hm, hTauZero] at hTauM
      exact (Option.some_ne_none (-ell)) hTauM.symm
    let m : Kˣ := Units.mk0 m0 hm0
    have hThetaM : (theta m : K) = -(theta k : K) := by
      have ht : some (theta m : K) = some (-ell) :=
        (hTheta m).symm.trans (by simpa [m] using hTauM)
      simpa [hThetaK] using Option.some.inj ht
    have huSq : IsSquare (u0 : K) := by
      have huMem : u0 ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
        rw [← hscalarSq]
        exact ⟨d, rfl⟩
      rcases huMem with ⟨r, hr⟩
      refine ⟨(r : K), ?_⟩
      simpa [pow_two] using (congrArg (fun z : Kˣ => (z : K)) hr).symm
    have hsum : (m : K) + (theta (-k) : K) * (u0 : K) = 0 := by
      have h := hCoord (some (theta (-k) : K))
      have hleft :
          tau (Option.map (fun t => (k : K) + t)
            (tau (some (theta (-k) : K)))) = none := by
        rw [hTheta (theta (-k)), hThetaInv]
        simp [hTauZero]
      rw [hleft] at h
      have hinner : tau (some (m0 + (theta (-k) : K) * (u0 : K))) = none := by
        cases hh : tau (some (m0 + (theta (-k) : K) * (u0 : K))) with
        | none => rfl
        | some z => simp [hh] at h
      exact Option.some.inj (tau.injective (hinner.trans hTauZero.symm))
    exact ⟨m, u0, huSq, hThetaM, by simpa [m] using hsum⟩
  have hKodd : Odd (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, hKcard]
    rcases hodd with ⟨r, hr⟩
    rcases hhalf with hhalf
    refine ⟨2 * r + 1, ?_⟩
    omega
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have hevenMod := FiniteField.even_card_of_char_two hchar
    have heven : Even (Fintype.card K) := Nat.even_iff.mpr hevenMod
    rcases hKodd with ⟨r, hr⟩
    rcases heven with ⟨s, hs⟩
    omega
  have hnegOne : (-1 : K) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hchar
  let negOne : Kˣ := Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero)
  have hnegSq : ¬ IsSquare (-1 : K) := by
    intro hsquare
    have hmemSq : negOne ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
      rcases hsquare with ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        intro hrz
        subst r
        norm_num at hr
      let ru : Kˣ := Units.mk0 r hr0
      refine ⟨ru, ?_⟩
      apply Units.ext
      simpa [negOne, ru, pow_two] using hr.symm
    rw [← hscalarSq] at hmemSq
    rcases hmemSq with ⟨d, hd⟩
    have hdOrder : orderOf d = 2 := by
      rw [← orderOf_injective scalar hscalar d, hd, ← orderOf_units]
      change orderOf (-1 : K) = 2
      rw [orderOf_neg_one, if_neg hchar]
    have htwoDvd : 2 ∣ Nat.card D := by
      rw [← hdOrder]
      exact orderOf_dvd_natCard d
    rcases hodd with ⟨r, hr⟩
    rcases (even_iff_two_dvd.mpr htwoDvd) with ⟨s0, hs0⟩
    omega
  obtain ⟨hcSq, hThetaFormula⟩ :=
    huppert_XI_6_8_odd_theta_inverse hnegSq theta hThetaInv hThetaEquiv hThetaRel
  let c : Kˣ := theta (1 : Kˣ)
  refine ⟨ePoint, s, c, hPointA, hPointB, hssq, hsa, hsb, hnegSq, hcSq,
    hPointF, hDAction, ?_⟩
  intro y
  change tau y = _
  cases y with
  | none => exact hTauInf
  | some x =>
      by_cases hx : x = 0
      · subst x
        simpa using hTauZero
      · let xu : Kˣ := Units.mk0 x hx
        have ht : tau (some x) = some (theta xu : K) := by
          simpa [xu] using hTheta xu
        rw [ht, hThetaFormula]
        simp [c, xu, hx, div_eq_mul_inv]
private theorem huppert_XI_6_8_scalar_range_eq_squares_of_index_two
    {D : Type u} {K : Type w} [Group D] [Finite D] [Field K] [Finite K]
    (scalar : D →* Kˣ) (hscalar : Function.Injective scalar)
    (hhalf : 2 * Nat.card D = Nat.card K - 1) :
    scalar.range = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  classical
  let Sq : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hrangeCard : Nat.card scalar.range = Nat.card D :=
    (Nat.card_congr (MonoidHom.ofInjective hscalar).toEquiv).symm
  have hunitCard : Nat.card Kˣ = Nat.card K - 1 :=
    Nat.card_units (α := K)
  have hindex : scalar.range.index = 2 := by
    have hmul := scalar.range.index_mul_card
    rw [hrangeCard, hunitCard, ← hhalf] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hSqLe : Sq ≤ scalar.range := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact Subgroup.sq_mem_of_index_two hindex y
  have hevenUnits : Even (Nat.card Kˣ) := by
    rw [hunitCard, ← hhalf]
    exact even_two.mul_right _
  have hgcd : Nat.gcd (Nat.card Kˣ) 2 = 2 :=
    Nat.gcd_eq_right (even_iff_two_dvd.mp hevenUnits)
  have hSqCard : Nat.card Sq = Nat.card D := by
    calc
      Nat.card Sq = Nat.card Kˣ / Nat.gcd (Nat.card Kˣ) 2 := by
        simpa [Sq] using IsCyclic.card_powMonoidHom_range Kˣ 2
      _ = Nat.card Kˣ / 2 := by rw [hgcd]
      _ = Nat.card D := by
        apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
        rw [Nat.mul_div_cancel' (even_iff_two_dvd.mp hevenUnits)]
        simpa [hunitCard] using hhalf.symm
  symm
  apply Subgroup.eq_of_le_of_card_ge hSqLe
  rw [hrangeCard, hSqCard]
set_option maxHeartbeats 800000 in
private theorem huppert_XI_6_8_even_complement_commutative
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F)
    (heven : Even (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hhalf : 2 * Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) = Nat.card F - 1) :
    ∃ s : G, s ≠ 1 ∧ s ^ 2 = 1 ∧ s • a = b ∧ s • b = a ∧
      (∃ c : Omega, s • c = c) ∧
      (∀ q : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        s * (((q : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((q⁻¹ : MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
              MulAction.stabilizer G a) : G))) ∧
      IsMulCommutative
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Even (Nat.card D) at heven
  change 2 * Nat.card D = Nat.card F - 1 at hhalf
  let : IsMulCommutative F := hFcomm
  let : CommGroup F := IsMulCommutative.instCommGroup
  let eAdd : Additive F ≃+ Additive F := AddEquiv.refl (Additive F)
  obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
      htwo a b hab F hFrob eAdd
  have hKernelAction :=
    huppert_blackburn_XI_projectivePointEquiv_kernel_action
      a b F eAdd ePoint hPointA hPointF
  obtain ⟨s, hsne, hssq, hsa, hsb, hsfix⟩ :=
    zassenhaus_even_twoPointStabilizer_exists_swap_involution
      htwo hat_most_two_fixed_points a b hab F hFrob heven
  let tau : Equiv.Perm (Option (Additive F)) :=
    ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
  have hTau_apply (y : Option (Additive F)) :
      tau y = ePoint (s • ePoint.symm y) := rfl
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  have hPointB_symm : ePoint.symm (some 0) = b := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointB]
  have hTauInf : tau none = some 0 := by
    rw [hTau_apply, hPointA_symm, hsa, hPointB]
  have hTauZero : tau (some 0) = none := by
    rw [hTau_apply, hPointB_symm, hsb, hPointA]
  have hTauSq (y : Option (Additive F)) : tau (tau y) = y := by
    rw [hTau_apply, hTau_apply, ePoint.symm_apply_apply]
    rw [← mul_smul, ← pow_two, hssq, one_smul, ePoint.apply_symm_apply]
  let dAct (d : D) (x : Additive F) : Additive F :=
    Additive.ofMul
      (⟨(d : H) * (Additive.toMul x : F) * (d : H)⁻¹,
        hFrob.normal.conj_mem
          ((Additive.toMul x : F) : H) (Additive.toMul x : F).property
          (d : H)⟩ : F)
  have hDAction (d : D) (y : Option (Additive F)) :
      ePoint ((((d : H) : G)) • ePoint.symm y) =
        Option.map (dAct d) y := by
    cases y with
    | none =>
        rw [hPointA_symm, (d : H).property, hPointA]
        rfl
    | some x =>
        let fx : F := Additive.toMul x
        let cfx : F :=
          ⟨(d : H) * (fx : H) * (d : H)⁻¹,
            hFrob.normal.conj_mem (fx : H) fx.property (d : H)⟩
        have hPointFx :
            ePoint ((((fx : H) : G)) • b) = some x := by
          simpa [fx, eAdd] using hPointF fx
        have hPointFxSymm :
            ePoint.symm (some x) = (((fx : H) : G)) • b := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointFx]
        have h_stab_d' : d • (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
          MulAction.mem_stabilizer_iff.mp d.property
        have hdb : (((d : H) : G)) • b = b := by
          have h_val := congrArg Subtype.val h_stab_d'
          simpa [MulAction.subgroup_smul_def] using h_val
        calc
          ePoint ((((d : H) : G)) • ePoint.symm (some x)) =
              ePoint ((((d : H) : G)) • ((((fx : H) : G)) • b)) := by
                rw [hPointFxSymm]
          _ = ePoint (((((d : H) : G)) * (((fx : H) : G))) • b) := by
                rw [mul_smul]
          _ = ePoint (((((cfx : H) : G)) * (((d : H) : G))) • b) := by
                congr 2
                dsimp [cfx]
                group
          _ = ePoint ((((cfx : H) : G)) • ((((d : H) : G)) • b)) := by
                rw [mul_smul]
          _ = ePoint ((((cfx : H) : G)) • b) := by rw [hdb]
          _ = some (dAct d x) := by
                simpa [cfx, dAct, fx, eAdd] using hPointF cfx
  have hDZero (d : D) : dAct d 0 = 0 := by
    apply Additive.toMul.injective
    dsimp [dAct]
    simp
  have hDNeg (d : D) (x : Additive F) : dAct d (-x) = -(dAct d x) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    dsimp [dAct]
    group
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 (even_iff_two_dvd.mp heven)
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsqD : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  let tG : G := ((t : H) : G)
  have htsqG : tG ^ 2 = 1 := by
    simpa [tG] using congrArg (fun x : D => (((x : H) : G))) htsqD
  have hta : tG • a = a := (t : H).property
  have h_stab_t : t • (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
    MulAction.mem_stabilizer_iff.mp t.property
  have htb : tG • b = b := by
    have h_val := congrArg Subtype.val h_stab_t
    simpa [tG, MulAction.subgroup_smul_def] using h_val
  have htsa : (s * tG * s) • a = a := by
    simp [mul_smul, hsa, hsb, htb]
  have htsb : (s * tG * s) • b = b := by
    simp [mul_smul, hsa, hsb, hta]
  let tsH : H := ⟨s * tG * s, htsa⟩
  let ts : D := ⟨tsH, by
    apply MulAction.mem_stabilizer_iff.mpr
    exact Subtype.ext htsb⟩
  have htssq : ts ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (s * tG * s) ^ 2 = 1
    rw [pow_two]
    calc
      (s * tG * s) * (s * tG * s) = s * (tG ^ 2) * s := by
        have hss : s * s = 1 := by simpa [pow_two] using hssq
        rw [show (s * tG * s) * (s * tG * s) =
          s * tG * (s * s) * tG * s by group, hss]
        simp [pow_two, mul_assoc]
      _ = 1 := by rw [htsqG]; simpa [pow_two] using hssq
  have htsne : ts ≠ 1 := by
    intro hts
    apply htne
    apply Subtype.ext
    apply Subtype.ext
    have htsG := congrArg (fun x : D => (((x : H) : G))) hts
    change s * tG * s = 1 at htsG
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    change tG = 1
    have hrecover : s * (s * tG * s) * s = tG := by
      calc
        s * (s * tG * s) * s = (s * s) * tG * (s * s) := by group
        _ = tG := by rw [hss]; simp
    calc
      tG = s * (s * tG * s) * s := hrecover.symm
      _ = s * 1 * s := by rw [htsG]
      _ = 1 := by simpa [mul_assoc] using hss
  have htsorder : orderOf ts = 2 := orderOf_eq_prime htssq htsne
  have htseq : ts = t :=
    frobenius_complement_involutions_eq F D hFrob ts t htsorder htorder
  have hstcomm : s * tG = tG * s := by
    have hconj := congrArg (fun x : D => (((x : H) : G))) htseq
    change s * tG * s = tG at hconj
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    have hmove : (s * tG * s) * s = s * tG := by
      calc
        (s * tG * s) * s = s * tG * (s * s) := by group
        _ = s * tG := by rw [hss]; simp
    calc
      s * tG = (s * tG * s) * s := hmove.symm
      _ = tG * s := by rw [hconj]
  have htConjInv (x : F) :
      (t : H) * (x : H) * (t : H)⁻¹ = (x⁻¹ : F) := by
    let : F.Normal := hFrob.normal
    let phi : MulAut F := MulAut.conjNormal (H := F) (t : H)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F) (t : H)) ^ 2 = 1
      have htsqH : (t : H) ^ 2 = 1 := by
        simpa using congrArg Subtype.val htsqD
      rw [← map_pow, htsqH, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro x
      have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
      simpa [pow_two] using hx
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro x hx
      have hxconj :
          (t : H) * (x : H) * (t : H)⁻¹ = (x : H) := by
        simpa [phi] using congrArg Subtype.val hx
      have hxcomm : (t : H) * (x : H) = (x : H) * (t : H) := by
        have := congrArg (fun z : H => z * (t : H)) hxconj
        simpa [mul_assoc] using this
      have hxcent : (x : H) ∈ elementCentralizerIn F (t : H) :=
        ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hxcomm.symm⟩
      have hcent : elementCentralizerIn F (t : H) = ⊥ :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob t htne
      have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
        simpa [hcent] using hxcent
      exact Subtype.ext (by simpa using hxbot)
    have hinv := hphi_fixedPointFree.coe_eq_inv_of_involutive hphi_involutive
    simpa [phi] using congrArg Subtype.val (congrFun hinv x)
  have hDActT (x : Additive F) : dAct t x = -x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa [dAct] using htConjInv (Additive.toMul x)
  have htPoint (y : Option (Additive F)) :
      ePoint.symm (Option.map (fun x => -x) y) =
        tG • ePoint.symm y := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply]
    rw [hDAction]
    cases y <;> simp [hDActT]
  have hTauNeg (y : Option (Additive F)) :
      tau (Option.map (fun x => -x) y) =
        Option.map (fun x => -x) (tau y) := by
    have hTauPoint : ePoint.symm (tau y) = s • ePoint.symm y := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hTau_apply]
    calc
      tau (Option.map (fun x => -x) y) =
          ePoint (s • ePoint.symm (Option.map (fun x => -x) y)) :=
            hTau_apply _
      _ = ePoint (s • (tG • ePoint.symm y)) := by rw [htPoint]
      _ = ePoint ((s * tG) • ePoint.symm y) := by rw [mul_smul]
      _ = ePoint ((tG * s) • ePoint.symm y) := by rw [hstcomm]
      _ = ePoint (tG • (s • ePoint.symm y)) := by rw [mul_smul]
      _ = ePoint (tG • ePoint.symm (tau y)) := by rw [hTauPoint]
      _ = Option.map (fun x => -x) (tau y) := by
        rw [hDAction]
        cases tau y <;> simp [hDActT]
  let F0 := {f : F // f ≠ 1}
  have hBruhat : ∀ x : F0, ∃ f1 f2 : F, ∃ d : D,
      s * (((x.1 : F) : H) : G) * s =
        (((f1 : H) : G)) * s * (((f2 : H) : G)) * (((d : H) : G)) := by
    intro x
    have htemp := zassenhaus_swap_kernel_bruhat_decomposition
      htwo a b hab F hFrob s hssq hsa hsb (x.1 : F) x.2
    rcases htemp with ⟨f1, f2, d, h⟩
    refine ⟨f1, f2, d, ?_⟩
    simpa [H, D, F0] using h
  choose f1 f2 d hdecomp using hBruhat
  let k (x : F0) : Additive F := Additive.ofMul x.1
  let ell (x : F0) : Additive F := Additive.ofMul (f1 x)
  let m (x : F0) : Additive F := Additive.ofMul (f2 x)
  have hTauPoint' (z : Option (Additive F)) :
      ePoint.symm (tau z) = s • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hTau_apply]
  have hKernelPoint (f : F) (z : Option (Additive F)) :
      ePoint.symm
          (Option.map (fun w => Additive.ofMul f + w) z) =
        (((f : H) : G)) • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply]
    simpa [eAdd] using (hKernelAction f z).symm
  have hDPoint (q : D) (z : Option (Additive F)) :
      ePoint.symm (Option.map (dAct q) z) =
        (((q : H) : G)) • ePoint.symm z := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hDAction]
  have hCoordEq (x : F0) (z : Option (Additive F)) :
      tau (Option.map (fun w => k x + w) (tau z)) =
        Option.map (fun w => ell x + w)
          (tau (Option.map (fun w => m x + w)
            (Option.map (dAct (d x)) z))) := by
    apply ePoint.symm.injective
    rw [hTauPoint', hKernelPoint, hTauPoint', hKernelPoint,
      hTauPoint', hKernelPoint, hDPoint]
    simp only [← mul_smul]
    simpa [mul_assoc] using
      congrArg (fun q : G => q • ePoint.symm z) (hdecomp x)
  have hTauK (x : F0) : tau (some (k x)) = some (ell x) := by
    have hx := hCoordEq x none
    simpa [hTauInf] using hx
  have hTauM (x : F0) : tau (some (m x)) = some (-(ell x)) := by
    have hx := hCoordEq x (some 0)
    simp only [hTauZero, Option.map_none, hTauInf, Option.map_some,
      hDZero, add_zero] at hx
    cases hm : tau (some (m x)) with
    | none => simp [hm] at hx
    | some z =>
        have hz : 0 = ell x + z := Option.some.inj (by simpa [hm] using hx)
        have hzeq : z = -(ell x) := by
          exact eq_neg_of_add_eq_zero_right hz.symm
        simpa [hm, hzeq]
  have hMeq (x : F0) : m x = -(k x) := by
    have hTauNegK : tau (some (-(k x))) = some (-(ell x)) := by
      simpa [hTauK] using hTauNeg (some (k x))
    exact Option.some.inj (tau.injective ((hTauM x).trans hTauNegK.symm))
  have hFunc (x : F0) (z : Option (Additive F)) :
      tau (Option.map (fun w => k x + w) (tau z)) =
        Option.map (fun w => ell x + w)
          (tau (Option.map (fun w => -(k x) + w)
            (Option.map (dAct (d x)) z))) := by
    simpa [hMeq] using hCoordEq x z
  have hTauEll (x : F0) : tau (some (ell x)) = some (k x) := by
    calc
      tau (some (ell x)) = tau (tau (some (k x))) := by rw [hTauK]
      _ = some (k x) := hTauSq _
  have hLeadAction (x : F0) : dAct (d x) (ell x) = -(k x) := by
    have hTauNegEll : tau (some (-(ell x))) = some (-(k x)) := by
      simpa [hTauEll] using hTauNeg (some (ell x))
    have hx := hFunc x (some (-(ell x)))
    have hnone :
        Option.map (fun w => ell x + w)
            (tau (some (-(k x) + dAct (d x) (-(ell x))))) = none := by
      simpa [hTauNegEll, hTauZero] using hx.symm
    have hinner :
        tau (some (-(k x) + dAct (d x) (-(ell x)))) = none := by
      cases hopt : tau (some (-(k x) + dAct (d x) (-(ell x)))) with
      | none => rfl
      | some z => simp [hopt] at hnone
    have harg : -(k x) + dAct (d x) (-(ell x)) = 0 := by
      exact Option.some.inj
        (tau.injective (hinner.trans hTauZero.symm))
    rw [hDNeg] at harg
    have hk : k x = -(dAct (d x) (ell x)) := neg_add_eq_zero.mp harg
    simpa using (congrArg (fun z : Additive F => -z) hk).symm
  have hParamFiber : ∀ x y : F0, d x = d y →
      y.1 = x.1 ∨ y.1 = x.1⁻¹ := by
    intro x y hdxy
    have hActY : dAct (d x) (ell y) = -(k y) := by
      rw [hdxy]
      exact hLeadAction y
    have hActX : dAct (d y) (ell x) = -(k x) := by
      rw [← hdxy]
      exact hLeadAction x
    have hx := hFunc x (some (ell y))
    have hy := hFunc y (some (ell x))
    have hx' :
        tau (some (k x + k y)) =
          Option.map (fun w => ell x + w)
            (tau (some (-(k x) + -(k y)))) := by
      simpa [hTauEll, hActY] using hx
    have hy' :
        tau (some (k y + k x)) =
          Option.map (fun w => ell y + w)
            (tau (some (-(k y) + -(k x)))) := by
      simpa [hTauEll, hActX] using hy
    have hrhs :
        Option.map (fun w => ell x + w)
            (tau (some (-(k x) + -(k y)))) =
          Option.map (fun w => ell y + w)
            (tau (some (-(k x) + -(k y)))) := by
      exact hx'.symm.trans (by simpa [add_comm] using hy')
    cases hopt : tau (some (-(k x) + -(k y))) with
    | none =>
        right
        have hsum : -(k x) + -(k y) = 0 := by
          exact Option.some.inj
            (tau.injective (hopt.trans hTauZero.symm))
        have hkxy : k x = -(k y) := neg_add_eq_zero.mp hsum
        have hkyx : k y = -(k x) := by
          simpa using (congrArg (fun z : Additive F => -z) hkxy).symm
        exact congrArg Additive.toMul hkyx
    | some z =>
        left
        have hell : ell x = ell y := by
          have hadd : ell x + z = ell y + z :=
            Option.some.inj (by simpa [hopt] using hrhs)
          exact add_right_cancel hadd
        have hkxy : k x = k y := by
          have htau : tau (some (k x)) = tau (some (k y)) := by
            rw [hTauK, hTauK, hell]
          exact Option.some.inj (tau.injective htau)
        exact (congrArg Additive.toMul hkxy).symm
  let : Fintype F := Fintype.ofFinite F
  let : Fintype D := Fintype.ofFinite D
  let : Fintype F0 := Fintype.ofFinite F0
  have hFiberCard : ∀ q ∈ (Finset.univ : Finset F0).image d,
      ({x ∈ (Finset.univ : Finset F0) | d x = q}).card ≤ 2 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, _hx, hdx⟩
    let xinv : F0 := ⟨x.1⁻¹, by
      intro hinv
      apply x.2
      have := congrArg (fun z : F => z⁻¹) hinv
      simpa using this⟩
    have hsub : {y ∈ (Finset.univ : Finset F0) | d y = q} ⊆ {x, xinv} := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hdyx : d y = d x := hy.trans hdx.symm
      rcases hParamFiber x y hdyx.symm with hval | hval
      · have hyx : y = x := Subtype.ext hval
        simp [hyx]
      · have hyinv : y = xinv := Subtype.ext hval
        simp [hyinv]
    calc
      ({y ∈ (Finset.univ : Finset F0) | d y = q}).card ≤
          ({x, xinv} : Finset F0).card :=
        Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hDomainLe : Fintype.card F0 ≤ 2 * Fintype.card D := by
    calc
      Fintype.card F0 = (Finset.univ : Finset F0).card := by
        rw [Finset.card_univ]
      _ ≤ 2 * ((Finset.univ : Finset F0).image d).card :=
        Finset.card_le_mul_card_image _ 2 hFiberCard
      _ ≤ 2 * (Finset.univ : Finset D).card := by
        exact Nat.mul_le_mul_left 2
          (Finset.card_le_card (by intro q hq; simp))
      _ = 2 * Fintype.card D := by rw [Finset.card_univ]
  have hCardF0 : Nat.card F0 = Nat.card F - 1 := by
    change Nat.card {f : F // f ≠ 1} = Nat.card F - 1
    simp only [Nat.card_eq_fintype_card]
    simp only [Fintype.card_subtype_compl (p := fun f : F => f = 1)]
    simp
  have hDomainImage : Fintype.card F0 ≤
      2 * ((Finset.univ : Finset F0).image d).card := by
    calc
      Fintype.card F0 = (Finset.univ : Finset F0).card := by
        rw [Finset.card_univ]
      _ ≤ 2 * ((Finset.univ : Finset F0).image d).card :=
        Finset.card_le_mul_card_image _ 2 hFiberCard
  have hImageLe : ((Finset.univ : Finset F0).image d).card ≤
      Fintype.card D := by
    simpa using Finset.card_le_card
      (show (Finset.univ : Finset F0).image d ⊆
        (Finset.univ : Finset D) by intro q hq; simp)
  have hF0Eq : Fintype.card F0 = 2 * Fintype.card D := by
    calc
      Fintype.card F0 = Nat.card F0 := Nat.card_eq_fintype_card.symm
      _ = Nat.card F - 1 := hCardF0
      _ = 2 * Nat.card D := hhalf.symm
      _ = 2 * Fintype.card D := by rw [Nat.card_eq_fintype_card]
  have hImageCard : ((Finset.univ : Finset F0).image d).card =
      Fintype.card D := by omega
  have hImageEq : (Finset.univ : Finset F0).image d =
      (Finset.univ : Finset D) :=
    Finset.eq_univ_of_card _ (by simpa using hImageCard)
  have hdSurj : Function.Surjective d := by
    intro q
    have hq : q ∈ (Finset.univ : Finset F0).image d := by
      rw [hImageEq]
      simp
    rcases Finset.mem_image.mp hq with ⟨x, _hx, hx⟩
    exact ⟨x, hx⟩
  have hsInv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hssq)
  have hswapInv : ∀ q : D,
      s * (((q : H) : G)) * s⁻¹ = ((((q⁻¹ : D) : H) : G)) := by
    intro q
    obtain ⟨x, hx⟩ := hdSurj q
    have hellne : ell x ≠ 0 := by
      intro hell
      have hbad : some (k x) = (none : Option (Additive F)) := by
        calc
          some (k x) = tau (tau (some (k x))) := (hTauSq _).symm
          _ = tau (some 0) := by rw [hTauK, hell]
          _ = none := hTauZero
      exact (Option.some_ne_none (k x)) hbad
    have hActEll : dAct q (ell x) = -(k x) := by
      rw [← hx]
      exact hLeadAction x
    have hActNegEll : dAct q (-(ell x)) = k x := by
      rw [hDNeg, hActEll]
      simp
    have hTauNegK : tau (some (-(k x))) = some (-(ell x)) := by
      simpa [hTauK] using hTauNeg (some (k x))
    let qG : G := ((q : H) : G)
    have hsqAction (z : Option (Additive F)) :
        ePoint ((s * qG) • ePoint.symm z) =
          tau (Option.map (dAct q) z) := by
      calc
        ePoint ((s * qG) • ePoint.symm z) =
            ePoint (s • (qG • ePoint.symm z)) := by rw [mul_smul]
        _ = ePoint (s • ePoint.symm (Option.map (dAct q) z)) := by
          rw [hDPoint]
        _ = tau (Option.map (dAct q) z) := (hTau_apply _).symm
    have hmoveEll :
        (s * qG) • ePoint.symm (some (ell x)) =
          ePoint.symm (some (-(ell x))) := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hsqAction, Option.map_some, hActEll]
      exact hTauNegK
    have hmoveNegEll :
        (s * qG) • ePoint.symm (some (-(ell x))) =
          ePoint.symm (some (ell x)) := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hsqAction, Option.map_some, hActNegEll]
      exact hTauK x
    have hqa : qG • a = a := (q : H).property
    have h_stab_q : q • (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
      MulAction.mem_stabilizer_iff.mp q.property
    have hqb : qG • b = b := by
      have h_val := congrArg Subtype.val h_stab_q
      simpa [qG, MulAction.subgroup_smul_def] using h_val
    have hfixa : (s * qG) ^ 2 • a = a := by
      simp [pow_two, mul_smul, hqa, hqb, hsa, hsb]
    have hfixb : (s * qG) ^ 2 • b = b := by
      simp [pow_two, mul_smul, hqa, hqb, hsa, hsb]
    let c0 : Omega := ePoint.symm (some (ell x))
    have hfixc : (s * qG) ^ 2 • c0 = c0 := by
      dsimp [c0]
      rw [pow_two, mul_smul, hmoveEll, hmoveNegEll]
    have hac0 : a ≠ c0 := by
      intro hac
      have heq := congrArg ePoint hac
      simpa [c0, hPointA] using heq
    have hbc0 : b ≠ c0 := by
      intro hbc
      have heq := congrArg ePoint hbc
      have : (0 : Additive F) = ell x :=
        Option.some.inj (by simpa [c0, hPointB] using heq)
      exact hellne this.symm
    have hsqOne : (s * qG) ^ 2 = 1 := by
      by_contra hne
      exact hat_most_two_fixed_points ((s * qG) ^ 2) hne
        a b c0 hab hac0 hbc0 ⟨hfixa, hfixb, hfixc⟩
    have hprod : (s * qG * s) * qG = 1 := by
      simpa [pow_two, mul_assoc] using hsqOne
    have hconj : s * qG * s = qG⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    simpa [qG, hsInv] using hconj
  have hDcomm : IsMulCommutative D := by
    refine ⟨⟨fun q r => ?_⟩⟩
    have hinvEqG :
        (((((q * r)⁻¹ : D) : H) : G)) =
          ((((q⁻¹ : D) : H) : G)) * ((((r⁻¹ : D) : H) : G)) := by
      calc
        (((((q * r)⁻¹ : D) : H) : G)) =
            s * (((q * r : D) : H) : G) * s⁻¹ := (hswapInv (q * r)).symm
        _ = (s * (((q : D) : H) : G) * s⁻¹) *
            (s * (((r : D) : H) : G) * s⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
        _ = ((((q⁻¹ : D) : H) : G)) * ((((r⁻¹ : D) : H) : G)) := by
          rw [hswapInv q, hswapInv r]
    have hinvEq : (q * r)⁻¹ = q⁻¹ * r⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hinvEqG
    have h := congrArg Inv.inv hinvEq
    simpa [mul_inv_rev] using h
  exact ⟨s, hsne, hssq, hsa, hsb, hsfix, hswapInv, hDcomm⟩
set_option maxHeartbeats 800000 in
private theorem huppert_XI_6_8_even_swap_coordinates
    {G : Type u} {Omega : Type v} {K : Type w}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    [Field K] [Finite K] [DecidableEq K]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat : ∀ g : G, g ≠ 1 → ∀ a b c : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (heven : Even (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hhalf : 2 * Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) = Nat.card F - 1)
    (eAdd : Additive F ≃+ K)
    (scalar : MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) →* Kˣ)
    (hscalar : Function.Injective scalar)
    (haction : ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      ∀ x : F,
      eAdd (Additive.ofMul
        (⟨(d : MulAction.stabilizer G a) *
            (x : MulAction.stabilizer G a) *
            (d : MulAction.stabilizer G a)⁻¹,
          hFrob.normal.conj_mem
            (x : MulAction.stabilizer G a) x.property
            (d : MulAction.stabilizer G a)⟩ : F)) =
        eAdd (Additive.ofMul x) * (scalar d : K))
    (s : G) (hsne : s ≠ 1) (hssq : s ^ 2 = 1)
    (hsa : s • a = b) (hsb : s • b = a)
    (hsfix : ∃ z : Omega, s • z = z)
    (hswapInv : ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      s * (((d : MulAction.stabilizer G a) : G)) * s⁻¹ =
        ((((d⁻¹ : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G))) :
    ∃ (ePoint : Omega ≃ Option K) (s0 : G),
      ePoint a = none ∧ ePoint b = some 0 ∧
      s0 ^ 2 = 1 ∧ s0 • a = b ∧ s0 • b = a ∧
      (∀ f : F,
        ePoint (((f : MulAction.stabilizer G a) : G) • b) =
          some (eAdd (Additive.ofMul f))) ∧
      (∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        ∀ y : Option K,
          ePoint ((((d : MulAction.stabilizer G a) : G)) • ePoint.symm y) =
            Option.map (fun x => x * (scalar d : K)) y) ∧
      ∀ y : Option K,
        ePoint (s0 • ePoint.symm y) =
          match y with
          | none => some 0
          | some x => if x = 0 then none else some (-x⁻¹) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  change Even (Nat.card D) at heven
  change 2 * Nat.card D = Nat.card F - 1 at hhalf
  change D →* Kˣ at scalar
  obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
      htwo a b hab F hFrob eAdd
  have hKernelAction :=
    huppert_blackburn_XI_projectivePointEquiv_kernel_action
      a b F eAdd ePoint hPointA hPointF
  have hPointA_symm : ePoint.symm none = a := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointA]
  have hPointB_symm : ePoint.symm (some 0) = b := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hPointB]
  have hDAction (d : D) (y : Option K) :
      ePoint ((((d : H) : G)) • ePoint.symm y) =
        Option.map (fun x => x * (scalar d : K)) y := by
    cases y with
    | none =>
        rw [hPointA_symm, (d : H).property, hPointA]
        rfl
    | some x =>
        let r : F := (eAdd.symm x).toMul
        let q : F :=
          ⟨(d : H) * (r : H) * (d : H)⁻¹,
            hFrob.normal.conj_mem (r : H) r.property (d : H)⟩
        have hPointR : ePoint (((r : H) : G) • b) = some x := by
          rw [hPointF]
          change some (eAdd (eAdd.symm x)) = some x
          rw [eAdd.apply_symm_apply]
        have hPointR_symm : ePoint.symm (some x) = (((r : H) : G) • b) := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointR]
        have h_stab : d • (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) =
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
          MulAction.mem_stabilizer_iff.mp d.property
        have hdb : (((d : H) : G)) • b = b := by
          have h_subtype := MulAction.mem_stabilizer_iff.mp d.property
          have h_val := congrArg Subtype.val h_subtype
          simpa [MulAction.subgroup_smul_def] using h_val
        calc
          ePoint ((((d : H) : G)) • ePoint.symm (some x)) =
              ePoint ((((d : H) : G)) • (((r : H) : G) • b)) := by
                rw [hPointR_symm]
          _ = ePoint (((((d : H) : G)) * ((r : H) : G)) • b) := by rw [mul_smul]
          _ = ePoint (((((q : H) : G)) * (((d : H) : G))) • b) := by
                congr 2
                dsimp [q]
                group
          _ = ePoint (((q : H) : G) • b) := by rw [mul_smul, hdb]
          _ = some (eAdd (Additive.ofMul q)) := hPointF q
          _ = some (x * (scalar d : K)) := by
                congr 1
                simpa [q, r] using haction d r
  let tau : Equiv.Perm (Option K) :=
    ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
  have hTauApply (y : Option K) : tau y = ePoint (s • ePoint.symm y) := rfl
  have hTauPoint (y : Option K) :
      ePoint.symm (tau y) = s • ePoint.symm y := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hTauApply]
  have hTauInf : tau none = some 0 := by
    rw [hTauApply, hPointA_symm, hsa, hPointB]
  have hTauZero : tau (some 0) = none := by
    rw [hTauApply, hPointB_symm, hsb, hPointA]
  have hTauSq (y : Option K) : tau (tau y) = y := by
    rw [hTauApply, hTauApply, ePoint.symm_apply_apply]
    rw [← mul_smul, ← pow_two, hssq, one_smul, ePoint.apply_symm_apply]
  have hTauSome : ∀ x : Kˣ, ∃ y : Kˣ,
      tau (some (x : K)) = some (y : K) := by
    intro x
    cases h : tau (some (x : K)) with
    | none =>
        exfalso
        have hx0 := tau.injective (h.trans hTauZero.symm)
        exact Units.ne_zero x (Option.some.inj hx0)
    | some y =>
        have hy : y ≠ 0 := by
          intro hy0
          subst y
          have hxnone := tau.injective (h.trans hTauInf.symm)
          exact (Option.some_ne_none (x : K)) hxnone
        exact ⟨Units.mk0 y hy, by simpa⟩
  choose theta hTheta using hTauSome
  have hThetaInv (x : Kˣ) : theta (theta x) = x := by
    apply Units.ext
    exact Option.some.inj (by
      have h := hTauSq (some (x : K))
      rw [hTheta x, hTheta (theta x)] at h
      exact h)
  have hKcard : Nat.card K = Nat.card F := by
    calc
      Nat.card K = Nat.card (Additive F) := Nat.card_congr eAdd.symm.toEquiv
      _ = Nat.card F := rfl
  have hhalfK : 2 * Nat.card D = Nat.card K - 1 := by
    rw [hKcard]
    exact hhalf
  have hscalarSq : scalar.range = (powMonoidHom 2 : Kˣ →* Kˣ).range :=
    huppert_XI_6_8_scalar_range_eq_squares_of_index_two scalar hscalar hhalfK
  have hThetaEquiv (x u : Kˣ) (huSq : IsSquare (u : K)) :
      theta (x * u) = theta x * u⁻¹ := by
    have huMem : u ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
      rcases huSq with ⟨r, hr⟩
      have hr0 : r ≠ 0 := by
        intro hrz
        exact Units.ne_zero u (by simpa [hrz] using hr)
      let ru : Kˣ := Units.mk0 r hr0
      refine ⟨ru, ?_⟩
      apply Units.ext
      simpa [ru, pow_two] using hr.symm
    rw [← hscalarSq] at huMem
    rcases huMem with ⟨d, hd⟩
    have hsInv := hswapInv d
    have hsinv : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hssq)
    have hss : s * s = 1 := by simpa [pow_two] using hssq
    have hmove : s * (((d : H) : G)) =
        ((((d⁻¹ : D) : H) : G)) * s := by
      calc
        s * (((d : H) : G)) =
            (s * (((d : H) : G)) * s⁻¹) * s := by
          rw [hsinv]
          calc
            s * (((d : H) : G)) = s * (((d : H) : G)) * 1 := by simp
            _ = s * (((d : H) : G)) * (s * s) := by rw [hss]
            _ = (s * (((d : H) : G)) * s) * s := by group
        _ = ((((d⁻¹ : D) : H) : G)) * s := by rw [hsInv]
    have hDPoint (q : D) (z : Option K) :
        ePoint.symm (Option.map (fun t => t * (scalar q : K)) z) =
          (((q : H) : G)) • ePoint.symm z := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hDAction]
    apply Units.ext
    apply Option.some.inj
    calc
      some ((theta (x * u) : K)) = tau (some ((x * u : Kˣ) : K)) :=
        (hTheta (x * u)).symm
      _ = ePoint (s • ePoint.symm
          (Option.map (fun t => t * (scalar d : K)) (some (x : K)))) := by
        rw [hd]
        rfl
      _ = ePoint (s • ((((d : H) : G)) • ePoint.symm (some (x : K)))) := by
        rw [hDPoint]
      _ = ePoint (((((d⁻¹ : D) : H) : G)) •
          (s • ePoint.symm (some (x : K)))) := by
        rw [← mul_smul, ← mul_smul, hmove]
      _ = ePoint (((((d⁻¹ : D) : H) : G)) •
          ePoint.symm (tau (some (x : K)))) := by rw [hTauPoint]
      _ = some ((theta x * u⁻¹ : Kˣ) : K) := by
        rw [hDAction, hTheta]
        apply congrArg some
        change (theta x : K) * (scalar d⁻¹ : K) =
          ((theta x * u⁻¹ : Kˣ) : K)
        have hdinv : scalar d⁻¹ = u⁻¹ := by
          simpa using congrArg Inv.inv hd
        exact congrArg (fun z : Kˣ => (z : K))
          (congrArg (fun z : Kˣ => theta x * z) hdinv)
  have hRatioSq (x y : Kˣ)
      (hxy : IsSquare (x : K) ↔ IsSquare (y : K)) :
      IsSquare ((x * y⁻¹ : Kˣ) : K) := by
    by_contra hnot
    have hopp := huppert_XI_6_8_quadraticChar_div_nonsquare
      (x : K) (y : K) (Units.ne_zero x) (Units.ne_zero y) (by
        simpa [div_eq_mul_inv] using hnot)
    have hsame : quadraticChar K (x : K) = quadraticChar K (y : K) := by
      by_cases hxSq : IsSquare (x : K)
      · have hySq : IsSquare (y : K) := hxy.mp hxSq
        rw [(quadraticChar_one_iff_isSquare (Units.ne_zero x)).2 hxSq,
          (quadraticChar_one_iff_isSquare (Units.ne_zero y)).2 hySq]
      · have hySq : ¬ IsSquare (y : K) := by
          intro hy
          exact hxSq (hxy.mpr hy)
        rw [quadraticChar_neg_one_iff_not_isSquare.mpr hxSq,
          quadraticChar_neg_one_iff_not_isSquare.mpr hySq]
    have hyD := quadraticChar_dichotomy (F := K) (Units.ne_zero y)
    rw [hsame] at hopp
    rcases hyD with hy1 | hyn
    · rw [hy1] at hopp
      norm_num at hopp
    · rw [hyn] at hopp
      norm_num at hopp
  have hThetaClass (x y : Kˣ)
      (hxy : IsSquare (x : K) ↔ IsSquare (y : K)) :
      IsSquare (theta x : K) ↔ IsSquare (theta y : K) := by
    let u : Kˣ := x⁻¹ * y
    have huSq : IsSquare (u : K) := by
      simpa [u, mul_comm] using hRatioSq y x hxy.symm
    have hxu : x * u = y := by simp [u]
    have heq := hThetaEquiv x u huSq
    rw [hxu] at heq
    constructor
    · intro hxSq
      rw [heq]
      have huInvSq : IsSquare ((u⁻¹ : Kˣ) : K) := by
        simpa using huSq.inv
      exact hxSq.mul huInvSq
    · intro hySq
      have hxEq : theta x = theta y * u := by
        calc
          theta x = (theta x * u⁻¹) * u := by group
          _ = theta y * u := by rw [← heq]
      rw [hxEq]
      exact hySq.mul huSq
  have hfixedUnit : ∃ r : Kˣ, theta r = r := by
    obtain ⟨z, hz⟩ := hsfix
    cases hcoord : ePoint z with
    | none =>
        exfalso
        have hza : z = a := ePoint.injective (hcoord.trans hPointA.symm)
        rw [hza, hsa] at hz
        exact hab hz.symm
    | some r =>
        have hr0 : r ≠ 0 := by
          intro hr
          subst r
          have hzb : z = b := ePoint.injective (hcoord.trans hPointB.symm)
          rw [hzb, hsb] at hz
          exact hab hz
        let ru : Kˣ := Units.mk0 r hr0
        refine ⟨ru, ?_⟩
        apply Units.ext
        have hzsymm : ePoint.symm (some r) = z := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hcoord]
        have htau : tau (some r) = some r := by
          rw [hTauApply, hzsymm, hz, hcoord]
        exact Option.some.inj ((hTheta ru).symm.trans htau)
  let c0 : Kˣ := theta (1 : Kˣ)
  have hc0Sq : IsSquare (c0 : K) := by
    by_contra hc0Not
    obtain ⟨r, hr⟩ := hfixedUnit
    by_cases hrSq : IsSquare (r : K)
    · have hclass := hThetaClass (1 : Kˣ) r (by
        constructor
        · intro _
          exact hrSq
        · intro _
          exact ⟨1, by simp⟩)
      apply hc0Not
      change IsSquare (theta (1 : Kˣ) : K)
      apply hclass.mpr
      simpa [hr] using hrSq
    · have hinput : IsSquare (c0 : K) ↔ IsSquare (r : K) := by
        constructor
        · intro h
          exact False.elim (hc0Not h)
        · intro h
          exact False.elim (hrSq h)
      have hclass := hThetaClass c0 r hinput
      have hthetaC0Sq : IsSquare (theta c0 : K) := by
        have hone : theta c0 = 1 := by simpa [c0] using hThetaInv (1 : Kˣ)
        rw [hone]
        exact ⟨1, by simp⟩
      have hthetaRSq := hclass.mp hthetaC0Sq
      apply hrSq
      simpa [hr] using hthetaRSq
  have hmodFour : Fintype.card K % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card, hKcard]
    rcases heven with ⟨m, hm⟩
    omega
  have hnegOneSq : IsSquare (-1 : K) :=
    FiniteField.isSquare_neg_one_iff.mpr hmodFour
  have hchar : ringChar K ≠ 2 := by
    intro hchar
    have hevenK : Even (Fintype.card K) :=
      Nat.even_iff.mpr (FiniteField.even_card_of_char_two hchar)
    rw [← Nat.card_eq_fintype_card] at hevenK
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rcases hevenK with ⟨r, hr⟩
    omega
  let negOne : Kˣ := Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero)
  let u0 : Kˣ := negOne * c0⁻¹
  have hu0Sq : IsSquare (u0 : K) := by
    simpa [u0, negOne] using hnegOneSq.mul hc0Sq.inv
  have hu0Mem : u0 ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
    rcases hu0Sq with ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      intro hrz
      exact Units.ne_zero u0 (by simpa [hrz] using hr)
    let ru : Kˣ := Units.mk0 r hr0
    refine ⟨ru, ?_⟩
    apply Units.ext
    simpa [ru, pow_two] using hr.symm
  rw [← hscalarSq] at hu0Mem
  rcases hu0Mem with ⟨d0, hd0⟩
  let d0G : G := ((d0 : H) : G)
  have hsInv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hssq)
  have hss : s * s = 1 := by simpa [pow_two] using hssq
  have hmove0 : s * d0G = d0G⁻¹ * s := by
    calc
      s * d0G = (s * d0G * s⁻¹) * s := by
        rw [hsInv]
        calc
          s * d0G = s * d0G * 1 := by simp
          _ = s * d0G * (s * s) := by rw [hss]
          _ = (s * d0G * s) * s := by group
      _ = d0G⁻¹ * s := by
        simpa [d0G] using congrArg (fun z : G => z * s) (hswapInv d0)
  let s0 : G := d0G * s
  have hs0sq : s0 ^ 2 = 1 := by
    rw [pow_two]
    dsimp [s0]
    calc
      (d0G * s) * (d0G * s) = d0G * (s * d0G) * s := by group
      _ = d0G * (d0G⁻¹ * s) * s := by rw [hmove0]
      _ = (d0G * d0G⁻¹) * (s * s) := by group
      _ = 1 := by rw [hss]; simp
  have hs0a : s0 • a = b := by
    dsimp [s0]
    rw [mul_smul, hsa]
    have h_d0_subtype := MulAction.mem_stabilizer_iff.mp d0.property
    simpa [d0G, MulAction.subgroup_smul_def] using congrArg Subtype.val h_d0_subtype
  have hs0b : s0 • b = a := by
    dsimp [s0]
    rw [mul_smul, hsb]
    exact (d0 : H).property
  let tau0 : Equiv.Perm (Option K) :=
    ePoint.symm.trans ((MulAction.toPerm s0).trans ePoint)
  have hTau0Apply (y : Option K) :
      tau0 y = ePoint (s0 • ePoint.symm y) := rfl
  have hTau0FromTau (y : Option K) :
      tau0 y = Option.map (fun x => x * (u0 : K)) (tau y) := by
    calc
      tau0 y = ePoint (s0 • ePoint.symm y) := hTau0Apply y
      _ = ePoint ((d0G * s) • ePoint.symm y) := by rfl
      _ = ePoint (d0G • (s • ePoint.symm y)) := by rw [mul_smul]
      _ = ePoint (d0G • ePoint.symm (tau y)) := by rw [hTauPoint]
      _ = Option.map (fun x => x * (scalar d0 : K)) (tau y) := by
        simpa [d0G] using hDAction d0 (tau y)
      _ = Option.map (fun x => x * (u0 : K)) (tau y) := by rw [hd0]
  let theta0 : Kˣ → Kˣ := fun x => theta x * u0
  have hTau0Theta (x : Kˣ) :
      tau0 (some (x : K)) = some (theta0 x : K) := by
    rw [hTau0FromTau, hTheta]
    rfl
  have hmulSquareIff (x u : Kˣ) (huSq : IsSquare (u : K)) :
      IsSquare ((x * u : Kˣ) : K) ↔ IsSquare (x : K) := by
    constructor
    · intro hxu
      have huInvSq : IsSquare ((u⁻¹ : Kˣ) : K) := by
        simpa using huSq.inv
      have h := hxu.mul huInvSq
      simpa using h
    · intro hx
      exact hx.mul huSq
  have hTheta0Class (x y : Kˣ)
      (hxy : IsSquare (x : K) ↔ IsSquare (y : K)) :
      IsSquare (theta0 x : K) ↔ IsSquare (theta0 y : K) := by
    rw [hmulSquareIff (theta x) u0 hu0Sq,
      hmulSquareIff (theta y) u0 hu0Sq]
    exact hThetaClass x y hxy
  have hTheta0Square (x : Kˣ) (hxSq : IsSquare (x : K)) :
      theta0 x = negOne * x⁻¹ := by
    have heq := hThetaEquiv (1 : Kˣ) x hxSq
    have hc : theta x = c0 * x⁻¹ := by simpa [c0] using heq
    dsimp [theta0]
    rw [hc]
    simp [u0, negOne, mul_assoc, mul_comm, mul_left_comm]
  obtain ⟨nK, hnK⟩ := FiniteField.exists_nonsquare hchar
  have hn0 : nK ≠ 0 := by
    intro hn
    subst nK
    exact hnK ⟨0, by simp⟩
  let n : Kˣ := Units.mk0 nK hn0
  have hnSq : ¬ IsSquare (n : K) := by simpa [n] using hnK
  have hthetaNSq : ¬ IsSquare (theta n : K) := by
    intro htheta
    have hinput : IsSquare (1 : K) ↔ IsSquare (theta n : K) := by
      constructor
      · intro _
        exact htheta
      · intro _
        exact ⟨1, by simp⟩
    have hclass := hThetaClass (1 : Kˣ) (theta n) hinput
    have hcTheta : IsSquare (theta (1 : Kˣ) : K) := by simpa [c0] using hc0Sq
    have hnn := hclass.mp hcTheta
    apply hnSq
    simpa [hThetaInv n] using hnn
  have htheta0NSq : ¬ IsSquare (theta0 n : K) := by
    intro h
    exact hthetaNSq ((hmulSquareIff (theta n) u0 hu0Sq).mp h)
  let k0 : Kˣ := theta0 n * n
  have hk0Sq : IsSquare (k0 : K) := by
    apply (quadraticChar_one_iff_isSquare (Units.ne_zero k0)).mp
    rw [show quadraticChar K (k0 : K) =
      quadraticChar K (theta0 n : K) * quadraticChar K (n : K) by
        simp [k0, map_mul]]
    rw [quadraticChar_neg_one_iff_not_isSquare.mpr htheta0NSq,
      quadraticChar_neg_one_iff_not_isSquare.mpr hnSq]
    norm_num
  have hTheta0Nonsquare (x : Kˣ) (hxSq : ¬ IsSquare (x : K)) :
      theta0 x = k0 * x⁻¹ := by
    let u : Kˣ := n⁻¹ * x
    have huSq : IsSquare (u : K) := by
      have hsame : IsSquare (n : K) ↔ IsSquare (x : K) := by
        constructor
        · intro h
          exact False.elim (hnSq h)
        · intro h
          exact False.elim (hxSq h)
      simpa [u, mul_comm] using hRatioSq x n hsame.symm
    have hnx : n * u = x := by simp [u]
    have heq := hThetaEquiv n u huSq
    rw [hnx] at heq
    dsimp [theta0, k0]
    rw [heq]
    have hxInv : x⁻¹ = u⁻¹ * n⁻¹ := by
      rw [← hnx, mul_inv_rev]
    rw [hxInv]
    calc
      theta n * u⁻¹ * u0 = u0 * (theta n * u⁻¹) := by ac_rfl
      _ = u0 * ((n * n⁻¹) * (theta n * u⁻¹)) := by simp
      _ = u0 * (n * (theta n * (n⁻¹ * u⁻¹))) := by ac_rfl
      _ = theta n * u0 * n * (u⁻¹ * n⁻¹) := by ac_rfl
  have hTau0Inf : tau0 none = some 0 := by
    rw [hTau0FromTau, hTauInf]
    simp
  have hTau0Zero : tau0 (some 0) = none := by
    rw [hTau0FromTau, hTauZero]
    rfl
  let phi : Option K → Option K := fun y =>
    Option.map (fun x => 1 + x) (tau0 y)
  have hPhiInf : phi none = some 1 := by
    dsimp [phi]
    rw [hTau0Inf]
    simp
  have hPhiZero : phi (some 0) = none := by
    dsimp [phi]
    rw [hTau0Zero]
    rfl
  have hPhiOne : phi (some 1) = some 0 := by
    have hOneSq : IsSquare (1 : K) := ⟨1, by simp⟩
    have hThetaOne := hTheta0Square (1 : Kˣ) hOneSq
    dsimp [phi]
    change Option.map (fun x : K => 1 + x)
      (tau0 (some ((1 : Kˣ) : K))) = some 0
    rw [hTau0Theta (1 : Kˣ), hThetaOne]
    simp [negOne]
  let f : F := (eAdd.symm 1).toMul
  have hfCoord : eAdd (Additive.ofMul f) = 1 := by simp [f]
  let fG : G := ((f : H) : G)
  let gammaG : G := fG * s0
  have hGammaCoord (y : Option K) :
      ePoint (gammaG • ePoint.symm y) = phi y := by
    have hTau0Point : ePoint.symm (tau0 y) = s0 • ePoint.symm y := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hTau0Apply]
    calc
      ePoint (gammaG • ePoint.symm y) =
          ePoint (fG • (s0 • ePoint.symm y)) := by
            simp [gammaG, mul_smul]
      _ = ePoint (fG • ePoint.symm (tau0 y)) := by rw [hTau0Point]
      _ = Option.map (fun x => eAdd (Additive.ofMul f) + x) (tau0 y) := by
        simpa [fG] using hKernelAction f (tau0 y)
      _ = phi y := by simp [phi, hfCoord]
  have hGammaPoint (y : Option K) :
      ePoint.symm (phi y) = gammaG • ePoint.symm y := by
    apply ePoint.injective
    rw [ePoint.apply_symm_apply, hGammaCoord]
  have hGammaPow3Point (y : Option K) :
      (gammaG ^ 3) • ePoint.symm y =
        ePoint.symm (phi (phi (phi y))) := by
    rw [show gammaG ^ 3 = gammaG * gammaG * gammaG by simp [pow_succ, mul_assoc]]
    rw [mul_smul, mul_smul]
    rw [← hGammaPoint y, ← hGammaPoint (phi y),
      ← hGammaPoint (phi (phi y))]
  let pInf : Omega := ePoint.symm none
  let pZero : Omega := ePoint.symm (some 0)
  let pOne : Omega := ePoint.symm (some 1)
  have hInfZero : pInf ≠ pZero := by
    intro h
    have heq := congrArg ePoint h
    simpa [pInf, pZero] using heq
  have hInfOne : pInf ≠ pOne := by
    intro h
    have heq := congrArg ePoint h
    simpa [pInf, pOne] using heq
  have hZeroOne : pZero ≠ pOne := by
    intro h
    have heq := congrArg ePoint h
    simpa [pZero, pOne] using heq
  have hFixInf : (gammaG ^ 3) • pInf = pInf := by
    rw [show pInf = ePoint.symm none by rfl, hGammaPow3Point,
      hPhiInf, hPhiOne, hPhiZero]
  have hFixZero : (gammaG ^ 3) • pZero = pZero := by
    rw [show pZero = ePoint.symm (some 0) by rfl, hGammaPow3Point,
      hPhiZero, hPhiInf, hPhiOne]
  have hFixOne : (gammaG ^ 3) • pOne = pOne := by
    rw [show pOne = ePoint.symm (some 1) by rfl, hGammaPow3Point,
      hPhiOne, hPhiZero, hPhiInf]
  have hGammaCube : gammaG ^ 3 = 1 := by
    by_contra hne
    exact hat (gammaG ^ 3) hne pInf pZero pOne
      hInfZero hInfOne hZeroOne ⟨hFixInf, hFixZero, hFixOne⟩
  have hPhiCube (y : Option K) : phi (phi (phi y)) = y := by
    apply ePoint.symm.injective
    calc
      ePoint.symm (phi (phi (phi y))) =
          (gammaG ^ 3) • ePoint.symm y := (hGammaPow3Point y).symm
      _ = ePoint.symm y := by rw [hGammaCube, one_smul]
  obtain ⟨b0, hb0Sq, hb01NotSq⟩ :=
    xi26_exists_square_add_one_nonsquare hchar
  let eK : K := -b0
  have heSq : IsSquare eK := by
    have hprod : IsSquare ((-1 : K) * b0) := hnegOneSq.mul hb0Sq
    have heq : eK = (-1 : K) * b0 := by
      dsimp [eK]
      ring
    rw [heq]
    exact hprod
  have hem1NotSq : ¬ IsSquare (eK - 1) := by
    intro hsq
    apply hb01NotSq
    have hprod : IsSquare ((-1 : K) * (eK - 1)) := hnegOneSq.mul hsq
    have heq : (-1 : K) * (eK - 1) = b0 + 1 := by
      dsimp [eK]
      ring
    rw [heq] at hprod
    exact hprod
  have heNe0 : eK ≠ 0 := by
    intro he0
    apply hem1NotSq
    rw [he0]
    simpa using hnegOneSq
  have heNe1 : eK ≠ 1 := by
    intro he1
    apply hem1NotSq
    rw [he1]
    exact ⟨0, by simp⟩
  let e : Kˣ := Units.mk0 eK heNe0
  let zK : K := (eK - 1) / eK
  have hzNe0 : zK ≠ 0 := by
    dsimp [zK]
    exact div_ne_zero (sub_ne_zero.mpr heNe1) heNe0
  let z : Kˣ := Units.mk0 zK hzNe0
  have hzNotSq : ¬ IsSquare (z : K) := by
    intro hzSq
    apply hem1NotSq
    have hprod_eq : (z : K) * (eK : K) = (eK : K) - 1 := by
      calc
        (z : K) * (eK : K) = zK * (eK : K) := by simp [z]
        _ = ((eK : K) - 1) / (eK : K) * (eK : K) := by simp [zK]
        _ = (eK : K) - 1 := by field_simp [heNe0]
    have hsq_prod : IsSquare ((z : K) * (eK : K)) := hzSq.mul heSq
    rw [hprod_eq] at hsq_prod
    exact hsq_prod
  have hPhiE : phi (some eK) = some zK := by
    have hThetaEVal : (theta0 e : K) = (-1 : K) * eK⁻¹ := by
      have hval := congrArg (fun q : Kˣ => (q : K))
        (hTheta0Square e (by simpa [e] using heSq))
      simpa [negOne, e] using hval
    dsimp [phi]
    rw [show some eK = some (e : K) by rfl, hTau0Theta e, hThetaEVal]
    apply congrArg some
    dsimp [zK]
    field_simp
    ring
  let wK : K := 1 + (k0 : K) * (z : K)⁻¹
  have hPhiZ : phi (some zK) = some wK := by
    dsimp [phi]
    rw [show some zK = some (z : K) by rfl, hTau0Theta z,
      hTheta0Nonsquare z hzNotSq]
    rfl
  have hPhiW : phi (some wK) = some eK := by
    have hcycle := hPhiCube (some eK)
    rw [hPhiE, hPhiZ] at hcycle
    exact hcycle
  have hwNe0 : wK ≠ 0 := by
    intro hw0
    rw [hw0, hPhiZero] at hPhiW
    simp at hPhiW
  let w : Kˣ := Units.mk0 wK hwNe0
  have hThetaW : (theta0 w : K) = eK - 1 := by
    have h := hPhiW
    dsimp [phi] at h
    rw [show some wK = some (w : K) by rfl, hTau0Theta w] at h
    have hadd : 1 + (theta0 w : K) = eK := Option.some.inj h
    linear_combination hadd
  have hwNotSq : ¬ IsSquare (w : K) := by
    intro hwSq
    apply hem1NotSq
    rw [← hThetaW]
    have hval0 := congrArg (fun q : Kˣ => (q : K))
      (hTheta0Square w hwSq)
    have hval : (theta0 w : K) = (-1 : K) * (w : K)⁻¹ := by
      simpa [negOne] using hval0
    rw [hval]
    exact hnegOneSq.mul hwSq.inv
  have hkw : (k0 : K) * (w : K)⁻¹ = eK - 1 := by
    calc
      (k0 : K) * (w : K)⁻¹ = (theta0 w : K) := by
        exact congrArg (fun q : Kˣ => (q : K))
          (hTheta0Nonsquare w hwNotSq).symm
      _ = eK - 1 := hThetaW
  have hkField : (k0 : K) = -1 := by
    have hkEq : (k0 : K) = (eK - 1) * wK := by
      calc
        (k0 : K) = ((k0 : K) * (w : K)⁻¹) * (w : K) := by
          field_simp
        _ = (eK - 1) * wK := by rw [hkw]; rfl
    dsimp [wK, z, zK, e] at hkEq
    have hem1 : eK - 1 ≠ 0 := sub_ne_zero.mpr heNe1
    apply (mul_left_cancel₀ hem1)
    field_simp at hkEq
    linear_combination -hkEq
  have hk0 : k0 = negOne := by
    apply Units.ext
    simpa [negOne] using hkField
  have hTheta0Formula (x : Kˣ) : theta0 x = negOne * x⁻¹ := by
    by_cases hxSq : IsSquare (x : K)
    · exact hTheta0Square x hxSq
    · rw [hTheta0Nonsquare x hxSq, hk0]
  refine ⟨ePoint, s0, hPointA, hPointB, hs0sq, hs0a, hs0b,
    hPointF, hDAction, ?_⟩
  intro y
  change tau0 y = _
  cases y with
  | none => exact hTau0Inf
  | some x =>
      by_cases hx : x = 0
      · subst x
        rw [hTau0Zero]
        simp
      · let xu : Kˣ := Units.mk0 x hx
        have ht : tau0 (some x) = some (theta0 xu : K) := by
          simpa [xu] using hTau0Theta xu
        rw [ht, hTheta0Formula]
        simp only [if_neg hx]
        apply congrArg some
        dsimp [negOne]
        rw [Units.val_inv_eq_inv_val]
        change (-1 : K) * x⁻¹ = -x⁻¹
        ring
set_option backward.isDefEq.respectTransparency false in
private theorem huppert_XI_6_8_sharpTriple_of_card_eq_descFactorial
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (hcard : Nat.card G = (Fintype.card Omega).descFactorial 3)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 → ∀ a b c : Omega,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) :
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      a' ≠ b' → a' ≠ c' → b' ≠ c' →
      ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  classical
  intro a b c a' b' c' hab hac hbc ha'b' ha'c' hb'c'
  let source : Fin 3 ↪ Omega :=
    ⟨![a, b, c], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let target : Fin 3 ↪ Omega :=
    ⟨![a', b', c'], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let orbit : G → (Fin 3 ↪ Omega) := fun g =>
    source.trans (MulAction.toPermHom G Omega g).toEmbedding
  have horbit_inj : Function.Injective orbit := by
    intro g h hgh
    have hga : g • a = h • a := by
      have hx := congrArg (fun e : Fin 3 ↪ Omega => e 0) hgh
      simpa [orbit, source] using hx
    have hgb : g • b = h • b := by
      have hx := congrArg (fun e : Fin 3 ↪ Omega => e 1) hgh
      simpa [orbit, source] using hx
    have hgc : g • c = h • c := by
      have hx := congrArg (fun e : Fin 3 ↪ Omega => e 2) hgh
      simpa [orbit, source] using hx
    have hfixa : (h⁻¹ * g) • a = a := by
      rw [mul_smul, hga, inv_smul_smul]
    have hfixb : (h⁻¹ * g) • b = b := by
      rw [mul_smul, hgb, inv_smul_smul]
    have hfixc : (h⁻¹ * g) • c = c := by
      rw [mul_smul, hgc, inv_smul_smul]
    have hone : h⁻¹ * g = 1 := by
      by_contra hne
      exact hat_most_two_fixed_points (h⁻¹ * g) hne a b c hab hac hbc
        ⟨hfixa, hfixb, hfixc⟩
    exact (inv_mul_eq_one.mp hone).symm
  have horbitCard : Nat.card G = Nat.card (Fin 3 ↪ Omega) := by
    calc
      Nat.card G = (Fintype.card Omega).descFactorial 3 := hcard
      _ = Fintype.card (Fin 3 ↪ Omega) := by
        rw [Fintype.card_embedding_eq, Fintype.card_fin]
      _ = Nat.card (Fin 3 ↪ Omega) := Nat.card_eq_fintype_card.symm
  have horbitSurj : Function.Surjective orbit :=
    ((Nat.bijective_iff_injective_and_card orbit).2
      ⟨horbit_inj, horbitCard⟩).2
  obtain ⟨g, hg⟩ := horbitSurj target
  refine ⟨g, ?_, ?_⟩
  · have h0 := congrArg (fun e : Fin 3 ↪ Omega => e 0) hg
    have h1 := congrArg (fun e : Fin 3 ↪ Omega => e 1) hg
    have h2 := congrArg (fun e : Fin 3 ↪ Omega => e 2) hg
    simpa [orbit, source, target] using And.intro h0 (And.intro h1 h2)
  · intro h hh
    apply horbit_inj
    rw [hg]
    ext i
    fin_cases i <;> simp [orbit, source, target, hh]

private theorem huppert_XI_6_8_complement_card_eq_half_arithmetic
    (n d : ℕ) (hn : 1 < n) (hd : 0 < d)
    (hdiv : d ∣ n - 1) (hbound : n - 1 ≤ 2 * d)
    (hne : d ≠ n - 1) : 2 * d = n - 1 := by
  obtain ⟨k, hk⟩ := hdiv
  have hkpos : 0 < k := by
    by_contra hk0
    have : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [this, mul_zero] at hk
    omega
  have hkle : k ≤ 2 := by
    rw [hk] at hbound
    nlinarith
  have hkne : k ≠ 1 := by
    intro hk1
    apply hne
    rw [hk, hk1, mul_one]
  have hkeq : k = 2 := by omega
  rw [hk, hkeq]
  ring

/-- XI.6.8 reduction: Feit's abelian-kernel bound and the non-sharp
hypothesis force the two-point stabilizer to have order `(n-1)/2`. -/
public theorem huppert_XI_6_8_complement_card_eq_half
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 → ∀ a b c : Omega,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hnotSharp :
      ¬ ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
          ∃! g : G,
            g • a = a' ∧ g • b = b' ∧ g • c = c')
    (hbound : Nat.card F - 1 ≤
      2 * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    2 * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) =
      Nat.card F - 1 := by
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let n := Nat.card F
  let d := Nat.card D
  obtain ⟨hOmegaCard, _hstabCard, hGcard, hdiv⟩ :=
    huppert_XI_6_1_action_parameters htwo_transitive a b hab F hFrob
  have hn : 1 < n := by
    exact (Subgroup.one_lt_card_iff_ne_bot F).mpr hFrob.kernel_ne_bot
  have hd : 0 < d := Nat.card_pos
  have hne : d ≠ n - 1 := by
    intro heq
    apply hnotSharp
    apply huppert_XI_6_8_sharpTriple_of_card_eq_descFactorial
    · calc
        Nat.card G = Fintype.card Omega * n * d := hGcard
        _ = (n + 1) * n * (n - 1) := by rw [hOmegaCard, heq]
        _ = (Fintype.card Omega).descFactorial 3 := by
          rw [hOmegaCard]
          simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one]
          have hsubOne : n + 1 - 1 = n := by omega
          have hsubTwo : n + 1 - 2 = n - 1 := by omega
          rw [hsubOne, hsubTwo]
          simp only [Nat.sub_zero]
          ac_rfl
    · exact hat_most_two_fixed_points
  exact huppert_XI_6_8_complement_card_eq_half_arithmetic
    n d hn hd hdiv hbound hne

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Huppert--Blackburn XI.6.8, in the form used by XI.11.16. -/
public theorem huppert_XI_6_8_abelianKernel_psl
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hnotSharp :
      ¬ ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
          ∃! g : G,
            g • a = a' ∧ g • b = b' ∧ g • c = c')
    (hFcomm : IsMulCommutative F) :
    ∃ (K : Type w) (_ : Field K),
      Nat.card K = Nat.card F ∧
        Nonempty
          (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  have hcomplementBound :
      Nat.card F - 1 ≤ 2 * Nat.card D := by
    exact huppert_XI_6_1_abelianKernel_complement_bound
      htwo_transitive hat_most_two_fixed_points hno_regular_normal
      a b hab F hFrob hFcomm
  have hhalf : 2 * Nat.card D = Nat.card F - 1 := by
    exact huppert_XI_6_8_complement_card_eq_half
      htwo_transitive hat_most_two_fixed_points a b hab F hFrob
        hnotSharp hcomplementBound
  have hevenComplementPSL :
      2 * Nat.card D = Nat.card F - 1 →
      Even (Nat.card D) →
      ∃ (K : Type w) (_ : Field K),
        Nat.card K = Nat.card F ∧
          Nonempty
            (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    classical
    intro _hhalf heven
    let H := MulAction.stabilizer G a
    change IsFrobeniusGroupWithKernelComplement F D at hFrob
    obtain ⟨sRaw, hsRawNe, hsRawSq, hsRawA, hsRawB, hsRawFix,
        hsRawInv, hDcomm⟩ :=
      huppert_XI_6_8_even_complement_commutative
        htwo_transitive hat_most_two_fixed_points a b hab F hFrob
          hFcomm heven hhalf
    have hFnil : Group.IsNilpotent F := by
      have : IsMulCommutative F := hFcomm
      refine ⟨1, ?_⟩
      have hcenter : Subgroup.center F = ⊤ :=
        Subgroup.center_eq_top_iff.mpr hFcomm
      simpa [Subgroup.upperCentralSeries_one] using hcenter
    obtain ⟨p, f, hp, hf, hFcard⟩ :=
      huppert_XI_6_1_frobeniusKernel_card_primePower
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
          a b hab F hFrob hFnil
    obtain ⟨K, fieldInst, finiteInst, eAdd, scalar, hscalar, haction⟩ :=
      huppert_XI_6_8_field_coordinates F D hFrob hFcomm hDcomm
        hhalf p f hp hf hFcard
    let : Field K := fieldInst
    let : Finite K := finiteInst
    let : DecidableEq K := Classical.decEq K
    let : Fintype K := Fintype.ofFinite K
    have hKcard : Nat.card K = Nat.card F := by
      calc
        Nat.card K = Nat.card (Additive F) :=
          Nat.card_congr eAdd.symm.toEquiv
        _ = Nat.card F := rfl
    have hhalfK : 2 * Nat.card D = Nat.card K - 1 := by
      rw [hKcard]
      exact hhalf
    have hscalarSq : scalar.range =
        (powMonoidHom 2 : Kˣ →* Kˣ).range :=
      huppert_XI_6_8_scalar_range_eq_squares_of_index_two
        scalar hscalar hhalfK
    obtain ⟨ePoint, s, hPointA, hPointB, hssq, hsa, hsb,
        hPointF, hDAction, hTau⟩ :=
      huppert_XI_6_8_even_swap_coordinates
        htwo_transitive hat_most_two_fixed_points a b hab F hFrob
          heven hhalf eAdd scalar hscalar haction sRaw hsRawNe hsRawSq
            hsRawA hsRawB hsRawFix hsRawInv
    let c : Kˣ := Units.mk0 (-1 : K) (neg_ne_zero.mpr one_ne_zero)
    have hnegc : IsSquare (-(c : K)) := by
      simpa [c] using (show IsSquare (1 : K) from ⟨1, by simp⟩)
    have hKernelAction :=
      huppert_blackburn_XI_projectivePointEquiv_kernel_action
        a b F eAdd ePoint hPointA hPointF
    let rho : G →* Equiv.Perm (Option K) :=
      ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Omega)
    have hrhoApply (g : G) (y : Option K) :
        rho g y = ePoint (g • ePoint.symm y) := rfl
    have hrhoInjective : Function.Injective rho := by
      intro g h hgh
      apply eq_of_smul_eq_smul (α := Omega)
      intro x
      have hx := congrArg
        (fun sigma : Equiv.Perm (Option K) => sigma (ePoint x)) hgh
      simpa [hrhoApply] using hx
    let tau : Equiv.Perm (Option K) :=
      ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
    have hrhoS : rho s = tau := rfl
    have hTau' (y : Option K) :
        tau y =
          match y with
          | none => some 0
          | some x => if x = 0 then none else some ((c : K) / x) := by
      change ePoint (s • ePoint.symm y) = _
      simpa [c, div_eq_mul_inv] using hTau y
    let affinePerm (z : K) (u : Kˣ) : Equiv.Perm (Option K) :=
      Equiv.optionCongr (u.mulRight.trans (Equiv.addLeft z))
    have hAffinePerm (z : K) (u : Kˣ) (y : Option K) :
        affinePerm z u y =
          Option.map (fun x => z + x * (u : K)) y := rfl
    have hStabilizerAffine (h : H) :
        ∃ f0 : F, ∃ d0 : D,
          h = (f0 : H) * (d0 : H) ∧
            ∀ y : Option K,
              ePoint ((h : G) • ePoint.symm y) =
                Option.map
                  (fun x => eAdd (Additive.ofMul f0) +
                    x * (scalar d0 : K)) y := by
      obtain ⟨fd, hfd, _hfdUnique⟩ := hFrob.isComplement'.existsUnique h
      let f0 : F := fd.1
      let d0 : D := fd.2
      have hdecomp : h = (f0 : H) * (d0 : H) := by
        simpa [f0, d0] using hfd.symm
      refine ⟨f0, d0, hdecomp, ?_⟩
      intro y
      have hdActionPoint :
          (((d0 : H) : G)) • ePoint.symm y =
            ePoint.symm
              (Option.map (fun x => x * (scalar d0 : K)) y) := by
        apply ePoint.injective
        rw [hDAction d0 y, ePoint.apply_symm_apply]
      have hdecompG : (h : G) =
          ((f0 : H) : G) * ((d0 : H) : G) :=
        congrArg Subtype.val hdecomp
      calc
        ePoint ((h : G) • ePoint.symm y) =
            ePoint (((f0 : H) : G) •
              (((d0 : H) : G) • ePoint.symm y)) := by
          rw [hdecompG, mul_smul]
        _ = ePoint (((f0 : H) : G) •
              ePoint.symm
                (Option.map (fun x => x * (scalar d0 : K)) y)) := by
          rw [hdActionPoint]
        _ = Option.map (fun x => eAdd (Additive.ofMul f0) + x)
              (Option.map (fun x => x * (scalar d0 : K)) y) :=
          hKernelAction f0 _
        _ = Option.map
              (fun x => eAdd (Additive.ofMul f0) +
                x * (scalar d0 : K)) y := by
          cases y <;> rfl
    let stabilizerRho : H →* Equiv.Perm (Option K) :=
      rho.comp H.subtype
    let A : Subgroup (Equiv.Perm (Option K)) := stabilizerRho.range
    have hA : ∀ sigma : Equiv.Perm (Option K), sigma ∈ A →
        ∃ z : K, ∃ u : Kˣ,
          IsSquare (u : K) ∧ sigma = affinePerm z u := by
      intro sigma hsigma
      rcases hsigma with ⟨h, rfl⟩
      obtain ⟨f0, d0, _hdecomp, haction0⟩ := hStabilizerAffine h
      refine ⟨eAdd (Additive.ofMul f0), scalar d0, ?_, ?_⟩
      · have huRange : scalar d0 ∈
            (powMonoidHom 2 : Kˣ →* Kˣ).range := by
          rw [← hscalarSq]
          exact ⟨d0, rfl⟩
        rcases huRange with ⟨u, hu⟩
        refine ⟨(u : K), ?_⟩
        simpa [pow_two] using
          congrArg (fun z : Kˣ => (z : K)) hu.symm
      · apply Equiv.ext
        intro y
        change rho (h : G) y = affinePerm
          (eAdd (Additive.ofMul f0)) (scalar d0) y
        rw [hrhoApply, haction0 y, hAffinePerm]
    have hsMoves : s • a ≠ a := by
      rw [hsa]
      exact hab.symm
    have hDoubleCoset :=
      huppert_II_1_12_b_doubleCoset_decomposition
        htwo_transitive a s hsMoves
    have hRange :
        (rho.range : Set (Equiv.Perm (Option K))) =
          (A : Set (Equiv.Perm (Option K))) ∪
            DoubleCoset.doubleCoset tau
              (A : Set (Equiv.Perm (Option K)))
              (A : Set (Equiv.Perm (Option K))) := by
      ext sigma
      constructor
      · intro hsigma
        rcases hsigma with ⟨g, rfl⟩
        have hg : g ∈ (H : Set G) ∪
            DoubleCoset.doubleCoset s H H := by
          rw [hDoubleCoset]
          exact Set.mem_univ g
        rcases hg with hg | hg
        · left
          exact ⟨⟨g, hg⟩, rfl⟩
        · right
          rcases DoubleCoset.mem_doubleCoset.mp hg with
            ⟨h1, hh1, h2, hh2, heq⟩
          apply DoubleCoset.mem_doubleCoset.mpr
          refine ⟨stabilizerRho ⟨h1, hh1⟩, ⟨⟨h1, hh1⟩, rfl⟩,
            stabilizerRho ⟨h2, hh2⟩, ⟨⟨h2, hh2⟩, rfl⟩, ?_⟩
          change rho g = rho h1 * tau * rho h2
          rw [heq, map_mul, map_mul, hrhoS]
      · intro hsigma
        rcases hsigma with hsigma | hsigma
        · rcases hsigma with ⟨h, rfl⟩
          exact ⟨(h : G), rfl⟩
        · rcases DoubleCoset.mem_doubleCoset.mp hsigma with
            ⟨sigma1, hsigma1, sigma2, hsigma2, hsigma⟩
          rcases hsigma1 with ⟨h1, rfl⟩
          rcases hsigma2 with ⟨h2, rfl⟩
          refine ⟨(h1 : G) * s * (h2 : G), ?_⟩
          rw [map_mul, map_mul, hrhoS]
          exact hsigma.symm
    obtain ⟨hOmegaCard, _hHcard, hGcard, _hdiv⟩ :=
      huppert_XI_6_1_action_parameters
        htwo_transitive a b hab F hFrob
    let q := Nat.card K
    have hqpos : 0 < q := Nat.card_pos
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      let r := q - 1
      have hq : q = r + 1 := by
        dsimp [r]
        omega
      rw [hq]
      simp only [Nat.add_sub_cancel]
      apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
      ring
    have hGdouble : 2 * Nat.card G = q * (q ^ 2 - 1) := by
      calc
        2 * Nat.card G =
            (Nat.card F + 1) * Nat.card F * (2 * Nat.card D) := by
          rw [hGcard, hOmegaCard]
          ring
        _ = (Nat.card F + 1) * Nat.card F * (Nat.card F - 1) := by
          rw [hhalf]
        _ = (q + 1) * q * (q - 1) := by rw [← hKcard]
        _ = q * (q ^ 2 - 1) := by rw [hfactor]; ac_rfl
    have hchar : ringChar K ≠ 2 := by
      intro hchar
      have hevenK : Even (Fintype.card K) :=
        Nat.even_iff.mpr (FiniteField.even_card_of_char_two hchar)
      rw [← Nat.card_eq_fintype_card] at hevenK
      have hKpos : 0 < Nat.card K := Nat.card_pos
      rcases hevenK with ⟨r, hr⟩
      omega
    have hnegOne : (-1 : K) ≠ 1 :=
      Ring.neg_one_ne_one_of_char_ne_two hchar
    have hcenter : Nat.card
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 :=
      huppert614_card_center_of_neg_one_ne_one hnegOne
    have hPSLmul := huppert614_card_psl_mul_center (K := K)
    rw [hcenter] at hPSLmul
    have hGPSLcard : Nat.card G =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
      calc
        2 * Nat.card G = q * (q ^ 2 - 1) := hGdouble
        _ = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) * 2 :=
          hPSLmul.symm
        _ = 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
          ac_rfl
    have hRangeCard : Nat.card rho.range =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
      calc
        Nat.card rho.range = Nat.card G :=
          (Nat.card_congr (Equiv.ofInjective rho hrhoInjective)).symm
        _ = _ := hGPSLcard
    obtain ⟨eRangePSL⟩ :=
      huppert_XI_6_8_odd_pslRange_of_tau
        rho A tau affinePerm hAffinePerm hA c hnegc hTau' hRange hRangeCard
    let eRange : G ≃* rho.range := MonoidHom.ofInjective hrhoInjective
    exact ⟨K, fieldInst, hKcard, ⟨eRange.trans eRangePSL⟩⟩
  have hoddComplementSimple :
      2 * Nat.card D = Nat.card F - 1 →
      Odd (Nat.card D) →
      ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤ := by
    intro hhalf' _hodd
    classical
    intro N hNnormal hNne
    let H := MulAction.stabilizer G a
    change IsFrobeniusGroupWithKernelComplement F D at hFrob
    have hNtwo : MulAction.IsMultiplyPretransitive N Omega 2 :=
      zassenhaus_nontrivial_normal_is_two_pretransitive
        htwo_transitive hno_regular_normal a b hab F hFrob
          N hNnormal hNne
    have hatN : ∀ g : N, g ≠ 1 → ∀ x y z : Omega,
        x ≠ y → x ≠ z → y ≠ z →
        ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
      intro g hg x y z hxy hxz hyz hfix
      apply hat_most_two_fixed_points (g : G)
      · intro hgG
        apply hg
        apply Subtype.ext
        exact hgG
      · exact hxy
      · exact hxz
      · exact hyz
      · exact hfix
    have hnoN : ¬ ∃ R : Subgroup N, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : Omega, ∃! r : R, (r : N) • x = y :=
      zassenhaus_normal_subgroup_no_regular_normal
        N hNnormal a hNtwo hno_regular_normal
    obtain ⟨Fother, hFother⟩ :=
      huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
        hNtwo hatN hnoN a b hab
    let Na : Subgroup H := N.comap H.subtype
    let HN := MulAction.stabilizer N a
    let eNa : Na ≃* HN := normalSubgroup_pointStabilizerEquiv N a
    let DNa : Subgroup Na := D.comap Na.subtype
    let DN : Subgroup HN := MulAction.stabilizer HN
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer N a)
    have hFNa : F ≤ Na := by
      simpa [H, Na] using
        zassenhaus_normal_stabilizer_contains_frobeniusKernel
          htwo_transitive hno_regular_normal a b hab F hFrob
            N hNnormal hNne
    have hDmap : DNa.map eNa.toMonoidHom = DN := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyD, hyx⟩
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hyfix := MulAction.mem_stabilizer_iff.mp hyD
        have hyfixOmega : (((y : Na) : H) : G) • b = b := by
          have h_temp := congrArg Subtype.val hyfix
          simpa [MulAction.subgroup_smul_def] using h_temp
        calc
          ((x : HN) : G) • b = ((eNa.toMonoidHom y : HN) : G) • b := by rw [hyx]
          _ = (((y : Na) : H) : G) • b := by
            dsimp [eNa, normalSubgroup_pointStabilizerEquiv]
            rfl
          _ = b := hyfixOmega
      · intro hx
        let y : Na := eNa.symm x
        refine ⟨y, ?_, eNa.apply_symm_apply x⟩
        change ((y : Na) : H) ∈ D
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        have hxfix := MulAction.mem_stabilizer_iff.mp hx
        have hxfixOmega : (((x : HN) : N) : G) • b = b := by
          have h_temp := congrArg Subtype.val hxfix
          simpa [MulAction.subgroup_smul_def] using h_temp
        calc
          (((y : Na) : H) : G) • b = ((eNa.symm x : Na) : G) • b := rfl
          _ = (((x : HN) : N) : G) • b := by
            dsimp [eNa, normalSubgroup_pointStabilizerEquiv]
            rfl
          _ = b := hxfixOmega
    have hDNne : DN ≠ ⊥ := by
      simpa [HN, DN] using hFother.complement_ne_bot
    have hDNa_ne : DNa ≠ ⊥ := by
      intro hbot
      apply hDNne
      rw [← hDmap, hbot]
      simp
    have hFrobNa : IsFrobeniusGroupWithKernelComplement
        (F.subgroupOf Na) DNa := by
      simpa [DNa] using
        frobenius_restrict_to_subgroup_containing_kernel
          F D Na hFrob hFNa hDNa_ne
    let FN : Subgroup HN := (F.subgroupOf Na).map eNa.toMonoidHom
    have hFrobN : IsFrobeniusGroupWithKernelComplement FN DN := by
      have hmap := hFrobNa.map_mulEquiv eNa
      rw [hDmap] at hmap
      simpa [FN] using hmap
    have hFcardN : Nat.card FN = Nat.card F := by
      calc
        Nat.card FN = Nat.card ((F.subgroupOf Na).map eNa.toMonoidHom) := rfl
        _ = Nat.card (F.subgroupOf Na) :=
          Subgroup.card_map_of_injective eNa.injective
        _ = Nat.card F := natCard_subgroupOf_eq F Na hFNa
    have hDNle : Nat.card DN ≤ Nat.card D := by
      rw [← hDmap]
      calc
        Nat.card (DNa.map eNa.toMonoidHom) = Nat.card DNa := by
          rw [Subgroup.card_map_of_injective eNa.injective]
        _ ≤ Nat.card D := Nat.card_le_card_of_injective
          (fun x : DNa =>
            (⟨((x : Na) : H), x.property⟩ : D)) (by
              intro x y hxy
              apply Subtype.ext
              apply Subtype.ext
              exact congrArg (fun z : D => (z : H)) hxy)
    let : IsMulCommutative F := hFcomm
    have hFNcomm : IsMulCommutative FN := by
      simpa only [FN] using
        (inferInstance : IsMulCommutative
          ((F.subgroupOf Na).map eNa.toMonoidHom))
    have hboundN : Nat.card F - 1 ≤ 2 * Nat.card DN := by
      have hh := huppert_XI_6_1_abelianKernel_complement_bound
        hNtwo hatN hnoN a b hab FN hFrobN hFNcomm
      rw [hFcardN] at hh
      exact hh
    have hDNeq : Nat.card DN = Nat.card D := by omega
    obtain ⟨_hOmegaCard, _hHcard, hNcard, _hdiv⟩ :=
      huppert_XI_6_1_action_parameters hNtwo a b hab FN hFrobN
    have hNcardEq : Nat.card N = Nat.card G := by
      obtain ⟨_hOmega, _hH, hGcard, _hGdiv⟩ :=
        huppert_XI_6_1_action_parameters
          htwo_transitive a b hab F hFrob
      calc
        Nat.card N = Fintype.card Omega * Nat.card FN * Nat.card DN := hNcard
        _ = Fintype.card Omega * Nat.card F * Nat.card D := by
          rw [hFcardN, hDNeq]
        _ = Nat.card G := hGcard.symm
    apply Subgroup.eq_top_of_card_eq
    exact hNcardEq
  have hsimplePSL :
      2 * Nat.card D = Nat.card F - 1 →
      Odd (Nat.card D) →
      (∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤) →
      ∃ (K : Type w) (_ : Field K),
        Nat.card K = Nat.card F ∧
          Nonempty
            (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
    classical
    intro _hhalf hodd hsimple
    let H := MulAction.stabilizer G a
    change IsFrobeniusGroupWithKernelComplement F D at hFrob
    have hFnil : Group.IsNilpotent F := by
      have : IsMulCommutative F := hFcomm
      refine ⟨1, ?_⟩
      have hcenter : Subgroup.center F = ⊤ :=
        Subgroup.center_eq_top_iff.mpr hFcomm
      simpa [Subgroup.upperCentralSeries_one] using hcenter
    obtain ⟨p, f, hp, hf, hFcard⟩ :=
      huppert_XI_6_1_frobeniusKernel_card_primePower
        htwo_transitive hat_most_two_fixed_points hno_regular_normal
          a b hab F hFrob hFnil
    have hDcyclic : IsCyclic D :=
      zassenhaus_odd_twoPointStabilizer_isCyclic
        htwo_transitive hat_most_two_fixed_points hsimple
          a b hab F hFrob hodd
    have hDcomm : IsMulCommutative D := hDcyclic.isMulCommutative
    obtain ⟨K, fieldInst, finiteInst, eAdd, scalar, hscalar, haction⟩ :=
      huppert_XI_6_8_field_coordinates F D hFrob hFcomm hDcomm
        hhalf p f hp hf hFcard
    let : Field K := fieldInst
    let : Finite K := finiteInst
    let : DecidableEq K := Classical.decEq K
    let : Fintype K := Fintype.ofFinite K
    have hKcard : Nat.card K = Nat.card F := by
      calc
        Nat.card K = Nat.card (Additive F) :=
          Nat.card_congr eAdd.symm.toEquiv
        _ = Nat.card F := rfl
    have hhalfK : 2 * Nat.card D = Nat.card K - 1 := by
      rw [hKcard]
      exact hhalf
    have hscalarSq : scalar.range =
        (powMonoidHom 2 : Kˣ →* Kˣ).range :=
      huppert_XI_6_8_scalar_range_eq_squares
        scalar hscalar hhalfK hodd
    obtain ⟨ePoint, s, c, hPointA, hPointB, hssq, hsa, hsb,
        hnegSq, hcSq, hPointF, hDAction, hTau⟩ :=
      huppert_XI_6_8_odd_swap_coordinates
        htwo_transitive hat_most_two_fixed_points hsimple
          a b hab F hFrob hodd hhalf eAdd scalar hscalar haction
    have hnegc : IsSquare (-(c : K)) := by
      have hnegChar : quadraticChar K (-1 : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hnegSq
      have hcChar : quadraticChar K (c : K) = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hcSq
      apply (quadraticChar_one_iff_isSquare
        (neg_ne_zero.mpr (Units.ne_zero c))).mp
      calc
        quadraticChar K (-(c : K)) =
            quadraticChar K ((-1 : K) * (c : K)) := by rw [neg_one_mul]
        _ = quadraticChar K (-1 : K) * quadraticChar K (c : K) :=
          map_mul _ _ _
        _ = 1 := by rw [hnegChar, hcChar]; norm_num
    have hKernelAction :=
      huppert_blackburn_XI_projectivePointEquiv_kernel_action
        a b F eAdd ePoint hPointA hPointF
    let rho : G →* Equiv.Perm (Option K) :=
      ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Omega)
    have hrhoApply (g : G) (y : Option K) :
        rho g y = ePoint (g • ePoint.symm y) := rfl
    have hrhoInjective : Function.Injective rho := by
      intro g h hgh
      apply eq_of_smul_eq_smul (α := Omega)
      intro x
      have hx := congrArg
        (fun sigma : Equiv.Perm (Option K) => sigma (ePoint x)) hgh
      simpa [hrhoApply] using hx
    let tau : Equiv.Perm (Option K) :=
      ePoint.symm.trans ((MulAction.toPerm s).trans ePoint)
    have hrhoS : rho s = tau := rfl
    have hTau' (y : Option K) :
        tau y =
          match y with
          | none => some 0
          | some x => if x = 0 then none else some ((c : K) / x) := by
      change ePoint (s • ePoint.symm y) = _
      exact hTau y
    let affinePerm (z : K) (u : Kˣ) : Equiv.Perm (Option K) :=
      Equiv.optionCongr (u.mulRight.trans (Equiv.addLeft z))
    have hAffinePerm (z : K) (u : Kˣ) (y : Option K) :
        affinePerm z u y =
          Option.map (fun x => z + x * (u : K)) y := rfl
    have hStabilizerAffine (h : H) :
        ∃ f0 : F, ∃ d0 : D,
          h = (f0 : H) * (d0 : H) ∧
            ∀ y : Option K,
              ePoint ((h : G) • ePoint.symm y) =
                Option.map
                  (fun x => eAdd (Additive.ofMul f0) +
                    x * (scalar d0 : K)) y := by
      obtain ⟨fd, hfd, _hfdUnique⟩ := hFrob.isComplement'.existsUnique h
      let f0 : F := fd.1
      let d0 : D := fd.2
      have hdecomp : h = (f0 : H) * (d0 : H) := by
        simpa [f0, d0] using hfd.symm
      refine ⟨f0, d0, hdecomp, ?_⟩
      intro y
      have hdActionPoint :
          (((d0 : H) : G)) • ePoint.symm y =
            ePoint.symm
              (Option.map (fun x => x * (scalar d0 : K)) y) := by
        apply ePoint.injective
        rw [hDAction d0 y, ePoint.apply_symm_apply]
      have hdecompG : (h : G) =
          ((f0 : H) : G) * ((d0 : H) : G) :=
        congrArg Subtype.val hdecomp
      calc
        ePoint ((h : G) • ePoint.symm y) =
            ePoint (((f0 : H) : G) •
              (((d0 : H) : G) • ePoint.symm y)) := by
          rw [hdecompG, mul_smul]
        _ = ePoint (((f0 : H) : G) •
              ePoint.symm
                (Option.map (fun x => x * (scalar d0 : K)) y)) := by
          rw [hdActionPoint]
        _ = Option.map (fun x => eAdd (Additive.ofMul f0) + x)
              (Option.map (fun x => x * (scalar d0 : K)) y) :=
          hKernelAction f0 _
        _ = Option.map
              (fun x => eAdd (Additive.ofMul f0) +
                x * (scalar d0 : K)) y := by
          cases y <;> rfl
    let stabilizerRho : H →* Equiv.Perm (Option K) :=
      rho.comp H.subtype
    let A : Subgroup (Equiv.Perm (Option K)) := stabilizerRho.range
    have hA : ∀ sigma : Equiv.Perm (Option K), sigma ∈ A →
        ∃ z : K, ∃ u : Kˣ,
          IsSquare (u : K) ∧ sigma = affinePerm z u := by
      intro sigma hsigma
      rcases hsigma with ⟨h, rfl⟩
      obtain ⟨f0, d0, _hdecomp, haction0⟩ := hStabilizerAffine h
      refine ⟨eAdd (Additive.ofMul f0), scalar d0, ?_, ?_⟩
      · have huRange : scalar d0 ∈
            (powMonoidHom 2 : Kˣ →* Kˣ).range := by
          rw [← hscalarSq]
          exact ⟨d0, rfl⟩
        rcases huRange with ⟨u, hu⟩
        refine ⟨(u : K), ?_⟩
        simpa [pow_two] using
          congrArg (fun z : Kˣ => (z : K)) hu.symm
      · apply Equiv.ext
        intro y
        change rho (h : G) y = affinePerm
          (eAdd (Additive.ofMul f0)) (scalar d0) y
        rw [hrhoApply, haction0 y, hAffinePerm]
    have hsMoves : s • a ≠ a := by
      rw [hsa]
      exact hab.symm
    have hDoubleCoset :=
      huppert_II_1_12_b_doubleCoset_decomposition
        htwo_transitive a s hsMoves
    have hRange :
        (rho.range : Set (Equiv.Perm (Option K))) =
          (A : Set (Equiv.Perm (Option K))) ∪
            DoubleCoset.doubleCoset tau
              (A : Set (Equiv.Perm (Option K)))
              (A : Set (Equiv.Perm (Option K))) := by
      ext sigma
      constructor
      · intro hsigma
        rcases hsigma with ⟨g, rfl⟩
        have hg : g ∈ (H : Set G) ∪
            DoubleCoset.doubleCoset s H H := by
          rw [hDoubleCoset]
          exact Set.mem_univ g
        rcases hg with hg | hg
        · left
          exact ⟨⟨g, hg⟩, rfl⟩
        · right
          rcases DoubleCoset.mem_doubleCoset.mp hg with
            ⟨h1, hh1, h2, hh2, heq⟩
          apply DoubleCoset.mem_doubleCoset.mpr
          refine ⟨stabilizerRho ⟨h1, hh1⟩, ⟨⟨h1, hh1⟩, rfl⟩,
            stabilizerRho ⟨h2, hh2⟩, ⟨⟨h2, hh2⟩, rfl⟩, ?_⟩
          change rho g = rho h1 * tau * rho h2
          rw [heq, map_mul, map_mul, hrhoS]
      · intro hsigma
        rcases hsigma with hsigma | hsigma
        · rcases hsigma with ⟨h, rfl⟩
          exact ⟨(h : G), rfl⟩
        · rcases DoubleCoset.mem_doubleCoset.mp hsigma with
            ⟨sigma1, hsigma1, sigma2, hsigma2, hsigma⟩
          rcases hsigma1 with ⟨h1, rfl⟩
          rcases hsigma2 with ⟨h2, rfl⟩
          refine ⟨(h1 : G) * s * (h2 : G), ?_⟩
          rw [map_mul, map_mul, hrhoS]
          exact hsigma.symm
    obtain ⟨hOmegaCard, _hHcard, hGcard, _hdiv⟩ :=
      huppert_XI_6_1_action_parameters
        htwo_transitive a b hab F hFrob
    let q := Nat.card K
    have hqpos : 0 < q := Nat.card_pos
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      let r := q - 1
      have hq : q = r + 1 := by
        dsimp [r]
        omega
      rw [hq]
      simp only [Nat.add_sub_cancel]
      apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
      ring
    have hGdouble : 2 * Nat.card G = q * (q ^ 2 - 1) := by
      calc
        2 * Nat.card G =
            (Nat.card F + 1) * Nat.card F * (2 * Nat.card D) := by
          rw [hGcard, hOmegaCard]
          ring
        _ = (Nat.card F + 1) * Nat.card F * (Nat.card F - 1) := by
          rw [hhalf]
        _ = (q + 1) * q * (q - 1) := by rw [← hKcard]
        _ = q * (q ^ 2 - 1) := by rw [hfactor]; ac_rfl
    have hnegOne : (-1 : K) ≠ 1 := by
      intro h
      apply hnegSq
      rw [h]
      exact ⟨1, by simp⟩
    have hcenter : Nat.card
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 :=
      huppert614_card_center_of_neg_one_ne_one hnegOne
    have hPSLmul := huppert614_card_psl_mul_center (K := K)
    rw [hcenter] at hPSLmul
    have hGPSLcard : Nat.card G =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
      apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
      calc
        2 * Nat.card G = q * (q ^ 2 - 1) := hGdouble
        _ = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) * 2 :=
          hPSLmul.symm
        _ = 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
          ac_rfl
    have hRangeCard : Nat.card rho.range =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
      calc
        Nat.card rho.range = Nat.card G :=
          (Nat.card_congr (Equiv.ofInjective rho hrhoInjective)).symm
        _ = _ := hGPSLcard
    obtain ⟨eRangePSL⟩ :=
      huppert_XI_6_8_odd_pslRange_of_tau
        rho A tau affinePerm hAffinePerm hA c hnegc hTau' hRange hRangeCard
    let eRange : G ≃* rho.range := MonoidHom.ofInjective hrhoInjective
    exact ⟨K, fieldInst, hKcard, ⟨eRange.trans eRangePSL⟩⟩
  by_cases hDeven : Even (Nat.card D)
  · exact hevenComplementPSL hhalf hDeven
  · have hDodd : Odd (Nat.card D) := Nat.not_even_iff_odd.mp hDeven
    exact hsimplePSL hhalf hDodd (hoddComplementSimple hhalf hDodd)

end External
end CFSG.BenderSuzuki

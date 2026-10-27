module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Torus
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourWeylKernel
import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.RankThree.PartOne.SLB4A.ClassExcRest

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (e6Rho)


variable {Ω : Type} [Field Ω]

private theorem rootChar_smul_eq_of_conj {Fr : Ω →+* Ω} {w : WeylGroup Tag.E6}
    {b : Fin Tag.E6.rank → Ωˣ}
    (h : canonicalRep (coxeterSystem Tag.E6) Ω w * twistE6 Ω Fr (rootDiagUnit Tag.E6 b) *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = rootDiagUnit Tag.E6 b)
    (y : Fin Tag.E6.rank → ℤ) :
    rootChar b (w • y) = rootChar (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) y := by
  rw [twistE6_rootDiagUnit] at h
  exact (rootDiagUnit_eq_conj_canonicalRep_iff b _ w).1 h.symm y

theorem exists_typeW0_of_e6AdLangToral [IsAlgClosed Ω] [CharP Ω 2] {n : ℕ} (hn : 1 ≤ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {X : Subgroup (ModGL Tag.E6 Ω)} (hX3 : ∀ x ∈ X, x ^ 3 = 1) (hcard : 81 ≤ Nat.card X)
    (h : E6AdLangToral Fr X) :
    ∃ g1 ∈ adjointGroup Tag.E6 Ω, g1⁻¹ * twistE6 Ω Fr g1 = TwistedDiag.n0 Ω ∧
      ∀ x ∈ X, x ∈ (twistedTorusOf (TwistedDiag.n0 Ω) (twistE6 Ω Fr)).map
        (MulAut.conj g1).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, g0, hg0, hF, hX⟩ := h
  choose a ha3 hax hafix using fun x : X =>
    exists_rootDiagUnit_of_mem_langTorus (hX x x.2) (hX3 x x.2)
  have hinj : Function.Injective a := fun x y hxy => Subtype.ext (by rw [hax x, hax y, hxy])
  have hu : twE6W0 * v⁻¹ ∈ familyStabilizer a := by
    intro x y
    have h0 := rootChar_smul_eq_of_conj (conj_twistE6_rootDiagUnit_of_cube hFr h3 (a x) (ha3 x))
    show rootChar (a x) ((twE6W0 * v⁻¹) • y) = rootChar (a x) y
    rw [mul_smul, h0, ← rootChar_smul_eq_of_conj (hafix x), smul_inv_smul]
  have hw : twE6W0 * v⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α} :=
    Subgroup.closure_mono (fun s hs => by obtain ⟨α, hα, rfl⟩ := hs; exact ⟨α, hα, rfl⟩)
      (mem_closure_familyKernel_of_card
        (fun x => funext fun i => by rw [Pi.pow_apply, ha3 x i, Pi.one_apply]) hinj hcard hu)
  obtain rfl : Fr = iterateFrobenius Ω 2 n := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  obtain ⟨z, hz, hzF⟩ : ∃ z ∈ familyGroup (K := Ω) a,
      (g0 * z)⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 n) (g0 * z) = TwistedDiag.n0 Ω :=
    LangRetype.exists_lang_retype_twisted (L := Ω) 2 TwistTag.E6 n hn a (g₀ := g0) (v := v)
      (w := twE6W0) hF hafix hw
  have hzc := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hz)
  have hfix : ∀ x : X, twistE6 Ω (iterateFrobenius Ω 2 n) x = x := fun x => by
    rw [hax x, map_mul, map_mul, map_inv, hF]
    conv_rhs => rw [← hafix x]
    group
  have htor : ∀ x : X, (g0 * z)⁻¹ * x * (g0 * z) ∈ torusGroup Tag.E6 Ω := fun x => by
    have hc := mul_inv_eq_iff_eq_mul.1 (hzc.2 x)
    have e : (g0 * z)⁻¹ * (x : ModGL Tag.E6 Ω) * (g0 * z) =
        z⁻¹ * (rootDiagUnit Tag.E6 (a x) * z) := by
      rw [hax x]
      group
    rw [e, hc, inv_mul_cancel_left]
    exact rootDiagUnit_mem_torusGroup _
  exact ⟨g0 * z, mul_mem hg0 hzc.1, hzF, mem_lang_torus_of_datum _ (A := X)
    (fun x hx => hfix ⟨x, hx⟩) (inv_mul_eq_iff_eq_mul.1 hzF) fun x hx => htor ⟨x, hx⟩⟩

end CFSG.StandardType.SCFourCover

end

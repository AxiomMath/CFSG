module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeModel
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2 CFSG.Open


theorem not_twNormTwo_of_lang_inner_torus {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (hchar : ringChar K = 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ q) {v : WeylGroup TwistTag.E6.tag} (hv : IsLongest v)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAI : A ≤ twistedE6InndiagGL K σ)
    (hodd : Odd (Nat.card A))
    (hinner : ∀ x ∈ NoOffRest.hypE6, ∃ a ∈ A,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) a =
        g * rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * g⁻¹) :
    ¬ TwNormTwo K σ A := by
  intro hU
  obtain ⟨μ, hμ1, hμadj, hμF, hμA⟩ :=
    leviSplitStep_holds K σ q hK hσ hchar A hAI hodd hU Fr hFr
  let ν : (AlgebraicClosure K)ˣ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp μ
  let F : Set (Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) :=
    {a | ∃ x ∈ NoOffRest.hypE6, a = zetaVec ζ hζ x}
  have hF : famKernel F = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun α ⟨hα, hαF⟩ => ?_
    obtain ⟨x, hx, hne⟩ := E6ThreeModel.exists_mem_hypE6_rootChar_ne_one hζo hζ α hα
    exact hne (hαF _ ⟨x, hx, rfl⟩)
  have hνadj : ∀ c, ν c ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    fun c => mul_mem (mul_mem (inv_mem hg) (hμadj c)) hg
  have hcomm : ∀ a ∈ F, ∀ c,
      rootDiagUnit TwistTag.E6.tag a * ν c *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹ = ν c := by
    rintro _ ⟨x, hx, rfl⟩ c
    obtain ⟨a, ha, he⟩ := hinner x hx
    have hc : baseChangeGL (algebraMap K (AlgebraicClosure K)) a * μ c *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) a)⁻¹ = μ c := by
      rw [← hμA a ha c, mul_inv_cancel_right]
    have hd : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) =
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) a * g := by
      rw [he]
      group
    change rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) * (g⁻¹ * μ c * g) *
      (rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x))⁻¹ = g⁻¹ * μ c * g
    rw [hd]
    calc _ = g⁻¹ * (baseChangeGL (algebraMap K (AlgebraicClosure K)) a * μ c *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) a)⁻¹) * g := by group
      _ = g⁻¹ * μ c * g := by rw [hc]
  have hT : ∀ c, ν c ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    cochar_mem_torusGroup F hF ν hνadj hcomm
  have hq : 0 < q := Nat.pos_of_ne_zero fun h0 => by
    have h := Nat.card_pos (α := K)
    rw [hK, h0] at h
    norm_num at h
  have hν : ν = 1 := cochar_eq_one_of_isLongest hq hFr hv ν hT fun c => by
    change g⁻¹ * μ (c ^ q) * g = _ *
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr (g⁻¹ * μ c * g) * _
    rw [map_mul, map_mul, map_inv, hgF, hμF c]
    group
  apply hμ1
  refine MonoidHom.ext fun c => ?_
  have h := DFunLike.congr_fun hν c
  change g⁻¹ * μ c * g = 1 at h
  exact conj_eq_one_iff.mp h

theorem eq_bot_of_isPGroup_two_of_tFrame {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 (AlgebraicClosure K)} (hL : IsLang Fr g)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) (hgood : D.Good)
    {U : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hU2 : IsPGroup 2 U)
    (hAU : ∀ x ∈ NoOffRest.hypE6, ∀ u ∈ U, D.ad x u ∈ U) : U = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  let C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  let φ : ↥C →* ModGL Tag.E6 K := C.subtype
  let A : Subgroup (ModGL Tag.E6 K) := D.V0.map φ
  have hVpow : ∀ r ∈ D.V0, r ^ 3 = 1 := by
    rintro r ⟨-, v, hv, hrv⟩
    obtain ⟨t, -, ht3, htv⟩ := hgood.inner v hv
    have hrt : r = t := CFSG.mulAut_conj_injective hgood.center (hrv.trans htv.symm)
    rwa [hrt]
  have hVE : IsElemAbelian 3 D.V0 := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hgood.torus.1 a a.2.1 b b.2.1)⟩⟩, hVpow⟩
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨k, hk⟩ := (hVE.map φ).isPGroup.exists_card_eq
    rw [show A = D.V0.map φ from rfl, hk]
    exact Odd.pow ⟨1, rfl⟩
  have hAI : A ≤ twistedE6InndiagGL K σ := by
    rintro _ ⟨r, -, rfl⟩
    exact (le_sup_left : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤
      twistedE6InndiagGL K σ) r.2
  have hinner : ∀ x ∈ NoOffRest.hypE6, ∃ a ∈ A,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) a =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ := by
    intro x hx
    obtain ⟨r, hrT, -, hrx, hrmat⟩ :=
      tFrame_inner_point hn hK σ hσ Fr hFr h3 hL hζ hζo hD x hx
    exact ⟨φ r, ⟨r, ⟨hrT, x, hx, hrx⟩, rfl⟩, hrmat⟩
  have hv : IsLongest twE6W0 := by
    have hrev : ReversesSigns twE6W0 :=
      CFSG.HardMathSupport.Malle.E27Lie.ExcCross.reversesSigns_of_negPerm twE6W0_smul
    obtain ⟨w₀, hmax, -⟩ := weyl_longest_element Tag.E6
    rw [hrev.eq (reversesSigns_of_forall_length_le hmax)]
    exact hmax
  have hgF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g =
      g * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0 :=
    inv_mul_eq_iff_eq_mul.mp hL.2
  have hno := not_twNormTwo_of_lang_inner_torus σ hK hσ (ringChar.eq K 2) Fr hFr hv
    hL.1 hgF hζ hζo hAI hAodd hinner
  by_contra hU1
  apply hno
  refine ⟨U.map φ, ?_, ?_, hU2.map φ, ?_⟩
  · rintro _ ⟨r, -, rfl⟩
    exact r.2
  · exact fun h => hU1 ((Subgroup.map_eq_bot_iff_of_injective U C.subtype_injective).1 h)
  · rintro _ ⟨r, ⟨-, x, hx, hrx⟩, rfl⟩ _ ⟨u, hu, rfl⟩
    have hmem : r * u * r⁻¹ ∈ U := by
      change MulAut.conj r u ∈ U
      rw [hrx]
      exact hAU x hx u hu
    exact ⟨r * u * r⁻¹, hmem, rfl⟩

end CFSG.StandardType.TwE6RootKill

end

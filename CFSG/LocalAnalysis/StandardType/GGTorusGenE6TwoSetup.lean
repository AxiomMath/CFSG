module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoLang
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
import CFSG.LocalAnalysis.StandardType.GGLangTwoPairAux
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Frobenius
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE
open TableBExc.E6Three TableBExcTwo TableBExcTwoFusion

namespace E6TwoGen


private theorem exists_cubeRoot_units_e6Two {L : Type} [Field L] [IsAlgClosed L]
    (h2 : (2 : L) = 0) :
    ∃ ω : Lˣ, (ω : L) ^ 2 + ω + 1 = 0 ∧ ω ^ 3 = 1 ∧ orderOf ω = 3 := by
  obtain ⟨x, hx⟩ := CFSG.StandardType.LangRat.j4e_exists_cubeRoot h2
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0] at hx
    have h1 : (1 : L) = 0 := by simpa using hx
    exact one_ne_zero h1
  let ω : Lˣ := Units.mk0 x hx0
  have hω : (ω : L) ^ 2 + ω + 1 = 0 := by simpa [ω] using hx
  have hω3 : ω ^ 3 = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    simpa [ω] using TableBExcTwoFusion.pow_three_of_sq_add hx
  have hωne1 : ω ≠ 1 := by
    intro h
    have hx1 : x = 1 := by simpa [ω] using congrArg Units.val h
    have h3 : (3 : L) = 0 := by
      rw [hx1] at hx
      linear_combination hx
    have h31 : (3 : L) = 1 := by linear_combination h2
    rw [h31] at h3
    exact one_ne_zero h3
  exact ⟨ω, hω, hω3, orderOf_eq_prime hω3 hωne1⟩

theorem exists_langSetup_e6Two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ (S : LangSetup .E6 (AlgebraicClosure K) 5)
      (ι : adjointGroup .E6 K →* ModGL .E6 (AlgebraicClosure K))
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (ω : (AlgebraicClosure K)ˣ),
      S.D.Φ = Units.map (entrywiseHom Fr) ∧ S.D.q = 2 ∧
      S.D.n = canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) wE6Two ∧
      (∀ c, Fr c = c ^ S.D.q) ∧ S.IsAlgebraic ∧ Function.Injective ι ∧ ι.range = S.Γ ∧
      orderOf ω = 3 ∧ Units.map Fr.toMonoidHom ω = ω⁻¹ ∧
      (∀ i : Fin 4, ι (uE6Two i) = rootSL2 .E6 (AlgebraicClosure K) (bE6 i) (HSL ω)) ∧
      ∀ (x : adjointGroup .E6 K) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
        ι x = rootDiagUnit .E6 a → rootDiagUnit .E6 a ∈ S.D.torus := by
  classical
  let L := AlgebraicClosure K
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num)
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  obtain ⟨ω, hω, hω3, hωord⟩ := exists_cubeRoot_units_e6Two (L := L) h2
  have hω2inv : ω ^ 2 = ω⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hω3])
  let Fr : L →+* L := frobenius L 2
  have hFr : ∀ c : L, Fr c = c ^ Nat.card K := by
    intro c
    change frobenius L 2 c = c ^ Nat.card K
    rw [frobenius_def, hK]
  have hσ : Fr (ω : L) = (ω : L) ^ 2 := by
    rw [hFr (ω : L), hK]
  let g0 : ModGL .E6 L :=
    ((frameProd L frameE6Two (langP hω) : adjointGroup .E6 L) : ModGL .E6 L)
  have hg0C : g0 ∈ adjointGroup .E6 L :=
    (frameProd L frameE6Two (langP hω) : adjointGroup .E6 L).2
  have hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .E6) L wE6Two := by
    simpa only [g0] using units_map_frameProd_langP hω Fr hσ
  obtain ⟨S, hΦ, hq, hn, hg0S, hd⟩ :=
    ExcTwoGen.exists_langSetup_data_two (τ := .E6) (Or.inl rfl) hK hFr hg0C hg0
  let bc : adjointGroup .E6 K →* ModGL .E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype
  let ι : adjointGroup .E6 K →* ModGL .E6 L :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp bc
  have hι : ∀ c, ι c = g0⁻¹ * baseChangeGL (algebraMap K L) (c : ModGL .E6 K) * g0 := by
    intro c
    change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) (c : ModGL .E6 K)) = _
    rw [MulAut.conj_apply, inv_inv]
  have hrange : ι.range = S.Γ := by
    have hcomp : ι = (MulAut.conj g0⁻¹).toMonoidHom.comp bc := rfl
    rw [hcomp, MonoidHom.range_comp, show S.Γ = S.D.Γ from rfl, hd.Γ_eq, hg0S]
  have hinjι : Function.Injective ι :=
    (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective _).comp
      (Subgroup.subtype_injective _))
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 1 (by rw [hq, pow_one])
  have hFrq : ∀ c : L, Fr c = c ^ S.D.q := by
    intro c
    rw [hFr c, hq]
  have hωinv : Units.map Fr.toMonoidHom ω = ω⁻¹ := by
    rw [← hω2inv]
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    change Fr (ω : L) = (ω : L) ^ 2
    rw [hFr (ω : L), hK]
  refine ⟨S, ι, Fr, ω, hΦ, hq.trans hK, hn, hFrq, hAlg, hinjι, hrange, hωord, hωinv,
    ?_, ?_⟩
  · intro i
    rw [hι (uE6Two i)]
    simpa only [g0] using frameProd_inv_conj_uE6Two (K := K) (algebraMap K L) hω i
  · intro x a hx
    have hmem : rootDiagUnit .E6 a ∈ twistedTorusOf
        (canonicalRep (coxeterSystem .E6) L wE6Two) (Units.map (entrywiseHom Fr)) := by
      refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      rw [← hx, hι x]
      exact ExcTwoGen.frob_conj_baseChange_two hFr hg0 (x : ModGL .E6 K)
    rw [show S.D.torus = twistedTorusOf (canonicalRep (coxeterSystem .E6) L wE6Two)
        (Units.map (entrywiseHom Fr)) from by rw [LangDatum.torus, hΦ, hn]]
    exact hmem

end E6TwoGen

end CFSG.StandardType

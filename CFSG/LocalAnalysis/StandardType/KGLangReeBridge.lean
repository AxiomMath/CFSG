module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcAbs
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwF4
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.FrobTrick

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.HardMathSupport.C14Exc CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.RankThree.PartOne.TCX.Ree

private lemma kgLangReeBridgeAux_pow_apply (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    ∀ x : G, ((e ^ n : MulAut G) : G → G) x = e^[n] x := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

private lemma kgLangReeBridgeAux_endPow_toMonoidHom (G : Type*) [Group G] (e : MulAut G) (n : ℕ) :
    endPow e.toMonoidHom n = ((e ^ n).toMonoidHom : G →* G) := by
  ext x
  rw [endPow_apply]
  simpa using (kgLangReeBridgeAux_pow_apply G e n x).symm

private lemma kgLangReeBridgeAux_Fr_pow_xElement {L : Type}
    [Field L] [CharP L 2] (C : ReeClosure L) (k : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : L) :
    (C.Fr ^ k) (xElement i c) = xElement i (c ^ 2 ^ k) := by
  have hFrpow : ∀ g : adjointGroup ReeTag.F4.tag L, (C.Fr ^ k) g =
      frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 k) g := by
    intro g
    refine Subtype.ext ?_
    rw [coe_pow_apply_of_entrywise_frobenius 2 C.Fr C.fr_apply k g, coe_frobeniusTwist]
    rfl
  rw [hFrpow, frobeniusTwist_xElement, iterateFrobenius_def]
private lemma kgLangReeBridgeAux_Fr_pow_yElement {L : Type}
    [Field L] [CharP L 2] (C : ReeClosure L) (k : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : L) :
    (C.Fr ^ k) (yElement i c) = yElement i (c ^ 2 ^ k) := by
  have hFrpow : ∀ g : adjointGroup ReeTag.F4.tag L, (C.Fr ^ k) g =
      frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 k) g := by
    intro g
    refine Subtype.ext ?_
    rw [coe_pow_apply_of_entrywise_frobenius 2 C.Fr C.fr_apply k g, coe_frobeniusTwist]
    rfl
  rw [hFrpow, frobeniusTwist_yElement, iterateFrobenius_def]

theorem kgLangRee_absBridge {a p : ℕ} (ha : 1 ≤ a) (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) (C : ReeClosure L)
    (hF : ∃ f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K), orderOf f = p) :
    ∃ b : ℕ, AbsBridge p (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)))
        (C.Φ * C.Fr ^ b).toMonoidHom ∧
      Finite ↥(((C.Φ * C.Fr ^ b) ^ p).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := by
  classical
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  haveI : Algebra.IsAlgebraic (ZMod 2) L := hL
  haveI : CharP L ReeTag.F4.prime := ‹CharP L 2›
  obtain ⟨hf, a₀, hbs⟩ :=
    CFSG.HardMathSupport.C14ExcBridgeTwF4.bridge_twF4_chev ha hK L hp hp2 hF
  obtain ⟨ρ, Θ, hρinj, hρfix, hΘinj, hI, hconj, hfrob⟩ := hbs
  have hF₀S : ReeTag.F4.reeEndo L hf a₀ = (C.Φ * C.Fr ^ a₀).toMonoidHom := by
    refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · rw [ReeTag.reeEndo_xElement]
      change xElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a₀ i) =
        (C.Φ * C.Fr ^ a₀) (xElement i c)
      rw [MulAut.mul_apply, kgLangReeBridgeAux_Fr_pow_xElement,
        (C.isExc i _).1, ← pow_mul, ReeTag.relationExponent, ReeTag.relationExponent_eq]
      rfl
    · rw [ReeTag.reeEndo_yElement]
      change yElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a₀ i) =
        (C.Φ * C.Fr ^ a₀) (yElement i c)
      rw [MulAut.mul_apply, kgLangReeBridgeAux_Fr_pow_yElement,
        (C.isExc i _).2, ← pow_mul, ReeTag.relationExponent, ReeTag.relationExponent_eq]
      rfl
  have hG_eq : (endPow (ReeTag.F4.reeEndo L hf a₀) p).eqLocus (MonoidHom.id _) =
      (((C.Φ * C.Fr ^ a₀) ^ p).toMonoidHom.eqLocus (MonoidHom.id _)) := by
    rw [hF₀S]
    change (endPow ((C.Φ * C.Fr ^ a₀).toMonoidHom) p).eqLocus (MonoidHom.id _) =
      (((C.Φ * C.Fr ^ a₀) ^ p).toMonoidHom.eqLocus (MonoidHom.id _))
    rw [kgLangReeBridgeAux_endPow_toMonoidHom]
  refine ⟨a₀, ?_, ?_⟩
  · rw [← hG_eq, ← hF₀S]
    refine ⟨ρ, Θ, hρinj, fun r => hρfix r, hΘinj, hI, hconj, fun f hfF hfp => ?_⟩
    obtain ⟨j, hpj, hj⟩ := hfrob f hfF hfp
    exact ⟨j, hpj, fun r => hj r⟩
  · rw [← hG_eq]
    haveI : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
      obtain ⟨e⟩ := CFSG.StandardType.centerQuot_twF4H_equiv K a
      haveI : Finite (CFSG.Blueprint.Chevalley.ModGL .F4 K) := finite_modGL
      haveI : Finite ↥(CFSG.Blueprint.reeFixedGroup .F4 K CFSG.Blueprint.reeF4Perm
          (fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ a else 2 ^ (a + 1))) := Subtype.finite
      haveI : Finite ↥⁅CFSG.Blueprint.reeFixedGroup .F4 K CFSG.Blueprint.reeF4Perm
          (fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ a else 2 ^ (a + 1)),
          CFSG.Blueprint.reeFixedGroup .F4 K CFSG.Blueprint.reeF4Perm
          (fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆ := Subtype.finite
      haveI : Finite (CFSG.Blueprint.DerivedCentralQuotient
          (CFSG.Blueprint.reeFixedGroup .F4 K CFSG.Blueprint.reeF4Perm
            (fun i => if i ∈ CFSG.Blueprint.reeF4Long then 2 ^ a else 2 ^ (a + 1)))) :=
        Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
      exact Finite.of_equiv _ e.symm.toEquiv
    exact Finite.of_injective Θ hΘinj

end CFSG.StandardType

module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglMain

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley LangTwistedProof LangTwisted2Proof
open CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups

namespace LangTwisted3Proof

theorem projImage_glPi_true_eq_top (q : ℕ) (K : Type) [Field K] :
    projImage (Sec4.glPi true 3 q K) = ⊤ := by
  refine eq_top_iff.2 fun P _ => ?_
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective P
  exact ⟨g, Sec4.mem_glPi_true q g, rfl⟩

@[expose] def projImageGlPiTrueEquiv (q : ℕ) (K : Type) [Field K] :
    projImage (Sec4.glPi true 3 q K) ≃* PGL(3, K) :=
  (MulEquiv.subgroupCongr (projImage_glPi_true_eq_top q K)).trans Subgroup.topEquiv

end LangTwisted3Proof

open LangTwisted3Proof



theorem kF89D4SecondCentY0Even_holds : KF89D4SecondCentY0Even := by
  intro n hev hn K _ _ σ hK hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨μ, hμ⟩ := exists_cube_root_unit (L := AlgebraicClosure K)
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFrμ : Fr (μ : AlgebraicClosure K) = (μ : AlgebraicClosure K) := by
    rw [hFr]
    exact pow_two_pow_even hμ hev
  obtain ⟨e₁⟩ := nonempty_autFix_equiv_secFixE hn hK hσ hμ hFrμ
  have e₂ := secFixEEquiv hμ hFrμ
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let _ := ZMod.algebra (AlgebraicClosure K) 2
  let ι : GaloisField 2 n →+* AlgebraicClosure K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 n) (M := AlgebraicClosure K)).toRingHom
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨G₀, hG⟩ := exists_secD_fix hq hFr μ
  have e₃ := pglFixEEquiv ι hq hcard hFr μ hG
  exact ⟨GaloisField 2 n, inferInstance, inferInstance, hcard,
    ⟨e₁.trans (e₂.trans (e₃.symm.trans (projImageGlPiTrueEquiv (2 ^ n) _).symm))⟩⟩

theorem kF89D4SecondCentEven_holds :
    KF89D4SecondCentEven :=
  kF89D4SecondCentEven_of_y0 kF89D4SecondCentY0Even_holds

end CFSG.RankThree.PartTwo.Sec8

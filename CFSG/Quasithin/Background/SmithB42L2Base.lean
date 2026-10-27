module

public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B15P4Repl
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.FFC2Ident
public import CFSG.Quasithin.Background.B4HypCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B5Models
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Quasithin

namespace B42L2

open CFSG.Assembly.LowTwoRank

section Weight

variable {V : Type} [CommGroup V] [Finite V]

theorem qOf_eq_one_of_weight (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A)
    (hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V) :
    qOf G = ((1 : ℚ) : WithTop ℚ) :=
  qOf_eq_of_offenders hV le_rfl
    (fun B hB => ((rAV_eq_one_iff hV hB.isA2).2 (hw B hB).symm).ge)
    ⟨A, hA, ((rAV_eq_one_iff hV hA.isA2).2 (hw A hA).symm).le⟩

theorem weight_eq_of_quadratic (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)}
    (hq : ∀ F, IsFFStarOffender G F → IsQuadratic F →
      Nat.card F * Nat.card (fixV F) = Nat.card V)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) :
    Nat.card B * Nat.card (fixV B) = Nat.card V := by
  obtain ⟨F, -, hF, hFq, hFw, -⟩ := exists_quadratic_offender_le hV hB
  rw [← hFw]
  exact hq F hF hFq

theorem le_normalizer_of_b4HypCore {G L : Subgroup (MulAut V)} (h : B4HypCore G L) :
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
  obtain ⟨hL, -, -⟩ := h
  subst hL
  exact le_normalizer_quasithinGenFitting G

theorem le_normalizer_of_b4Hyp {G L : Subgroup (MulAut V)} (h : B4Hyp G L) :
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  le_normalizer_of_b4HypCore h.core

theorem card_le_of_offender {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have h := hA.2.2.2 ⊥ bot_le
  rwa [B1.card_bot_mul_card_fixV] at h

end Weight

theorem center_sl2_eq_bot {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem exists_sl2_of_model {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {f : ℕ}
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ f ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hcard]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hcardK
  let e₁ : X ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans QuotientGroup.quotientBot
  exact ⟨K, hK, inferInstance, hcardK,
    ⟨(e₁.trans e).trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e₂)⟩⟩

end B42L2

end CFSG.Quasithin

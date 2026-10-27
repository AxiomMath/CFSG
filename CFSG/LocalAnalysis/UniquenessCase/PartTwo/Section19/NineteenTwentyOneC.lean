module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenElevenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.CtxLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_21_borel (D : Data G) : Prop :=
  ∀ V₀ V p L A t B r Y N Dsub H S (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
    A ≤ normalizer (Dsub : Set G) → P19_16_5 D Dsub →
    R19_19At D V₀ V p L A t B r Y N Dsub H S h →
    ∀ (d : ℕ) (K J : Fin d → Subgroup G) (i : Fin d),
      IsDynkinComponentFamily D Dsub d K J → J i ≤ IOf D p L → P19_19_1 D p L (J i) →
      ∃ P₀ : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 P₀ (Dsub ⊓ D.M) ∧
        A ≤ normalizer (P₀ : Set G)

@[expose] def Gap19_21c (D : Data G) : Prop :=
  ∀ V₀ V p L A t B r Y N Dsub H S (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
    A ≤ normalizer (Dsub : Set G) → P19_16_5 D Dsub →
    R19_19At D V₀ V p L A t B r Y N Dsub H S h →
    ∀ (d : ℕ) (K J : Fin d → Subgroup G) (i : Fin d),
      IsDynkinComponentFamily D Dsub d K J → J i ≤ IOf D p L → P19_19_1 D p L (J i) →
      ∀ E : Subgroup G, E ≤ A → IsElemAbelian r E → Nat.card E = r ^ 2 →
        ∃ R P : Subgroup G, IsPGroup r R ∧ E ≤ R ∧ R ≤ D.M ∧
          CFSG.ABGLocalTools.IsSylowOf 2 P (Dsub ⊓ D.M) ∧
          Dsub ≤ P ⊔ (Dsub ⊓ normalizer (R : Set G))

theorem gap19_21c_of (D : Data G) (hK : K_19_21_BN) (hB : Gap19_21_borel D) :
    Gap19_21c D := by
  intro V₀ V p L A t B r Y N Dsub H S h h17 h5 h19 d K J i hfam hJi h191 E hEA hEel _hEcard
  exact hK G D.M Dsub A E r h.hD.1.2.2 h5.1 h5.2 h.hO2 (A_le_M_of_ctx19_10 D h.ctx) h17
    (isMulCommutative_of_isZModSq h.ctx.hAcard) (odd_card_of_ctx19_10 h.ctx)
    (hB V₀ V p L A t B r Y N Dsub H S h h17 h5 h19 d K J i hfam hJi h191) h.ctx.hr.1 hEA
    hEel.isPGroup

theorem nineteen_twentyone_at_c (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h201 : R19_20_1At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h21 : Gap19_21c D) :
    R19_21At D V₀ V p L A t B r Y N Dsub H S h := by
  intro d K J i hfam hJi h191
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    exists_isElemAbelian_card_prime_sq_of_isZModSq h.ctx.hAcard h.ctx.hr.1 h.ctx.hr.2
  obtain ⟨R, P, -, hER, hRM, hPsyl, hDsub_le⟩ :=
    h21 V₀ V p L A t B r Y N Dsub H S h h17 h201 h19 d K J i hfam hJi h191 E hEA hEel hEcard
  have hNRM : normalizer (R : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
      (CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le (h12 E hEA hEel hEcard) hER hRM)
  have hPM : P ≤ D.M := hPsyl.le.trans inf_le_right
  exact h.hD.2 (hDsub_le.trans (sup_le hPM (inf_le_right.trans hNRM)))

theorem r19_A21c (D : Data G) {V₀ V : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (h : Ctx19_10 D V₀ V p L A t B 3), R19_12At D V₀ V p L A t B 3 h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_17At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h201 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_19At D V₀ V p L A t B 3 Y N Dsub H S h)
    (h21 : Gap19_21c D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B 3 Y N Dsub H S),
      R19_21At D V₀ V p L A t B 3 Y N Dsub H S h := by
  intro p L A t B Y N Dsub H S h
  exact nineteen_twentyone_at_c D h (h12 p L A t B h.ctx) (h17 p L A t B Y N Dsub H S h)
    (h201 p L A t B Y N Dsub H S h) (h19 p L A t B Y N Dsub H S h) h21

theorem r19_C21c (D : Data G) {V₀ V : Subgroup G}
    (h12 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (h : Ctx19_10 D V₀ V p L A t B r), R19_12At D V₀ V p L A t B r h)
    (h17 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h201 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_20_1At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h21 : Gap19_21c D) :
    ∀ (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
      (Y N Dsub H S : Subgroup G)
      (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
      R19_21At D V₀ V p L A t B r Y N Dsub H S h := by
  intro p L A t B r Y N Dsub H S h
  exact nineteen_twentyone_at_c D h (h12 p L A t B r h.ctx) (h17 p L A t B r Y N Dsub H S h)
    (h201 p L A t B r Y N Dsub H S h) (h19 p L A t B r Y N Dsub H S h) h21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

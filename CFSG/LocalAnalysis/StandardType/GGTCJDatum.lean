module

public import CFSG.LocalAnalysis.StandardType.GGTCJDescent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T2
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LieType.Chevalley.NativeMonomial
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem tcjDatum_congr_refl {R : Type} [Group R] (φ : MulAut R) :
    MulAut.congr (MulEquiv.refl R) φ = φ := by
  ext x
  rw [MulAut.congr_apply]
  simp

theorem tcjDatum_innDiagKind_of_can {R : Type} [Group R] {lab : LargeEvenLabel}
    {I : Set (MulAut R)} (hlab : LargeEvenInLambda2 lab) (hsimple : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a)
    (hcan : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R' _ I' _ => ∃ e : R ≃* R', ∀ φ, φ ∈ I → MulAut.congr e φ ∈ I')) :
    ∀ φ ∈ I, InnDiagKind R lab φ := by
  intro φ hφ
  have hZ : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hperf : commutator R = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with h | h
    · exfalso
      haveI : IsMulCommutative R := (commutator_eq_bot_iff R).mp h
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mul_comm' a b)
    · exact h
  refine ⟨hperf, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono (fun R' _ I' _ he => ?_) hcan
  obtain ⟨e, he⟩ := he
  have hna' : ∃ a b : R', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun hh => hab (e.injective (by rw [map_mul, map_mul]; exact hh))⟩
  refine ⟨e.isSimpleGroup_congr.1 hsimple, hna',
    (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hZ).trans e, rfl,
    MulAut.congr e φ, he φ hφ, ?_⟩
  have happ : ∀ (α : MulAut R) (x : R), MulAut.congr e α (e x) = e (α x) := fun α x => by
    show e (α (e.symm (e x))) = e (α x)
    rw [MulEquiv.symm_apply_apply]
  have htheta : ∀ x : R, ((CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hZ).trans e)
      (QuotientGroup.mk x) = e x := fun x => by
    rw [MulEquiv.trans_apply, CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot_mk]
  intro l l' hl
  subst hl
  rw [htheta l, htheta (φ l)]
  exact happ φ l

theorem tcjDatum_prop_of_can {R : Type} [Group R] {lab : LargeEvenLabel}
    {I : Set (MulAut R)} (hlab : LargeEvenInLambda2 lab) (hfin : Finite R)
    (hsimple_of : (∃ a b : R, a * b ≠ b * a) → IsSimpleGroup R)
    (hcan : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R' _ I' _ => ∃ e : R ≃* R', ∀ φ, φ ∈ I → MulAut.congr e φ ∈ I')) :
    Finite R ∧ ((∃ a b : R, a * b ≠ b * a) →
      IsSimpleGroup R ∧ ∀ φ ∈ I, InnDiagKind R lab φ) :=
  ⟨hfin, fun hna => ⟨hsimple_of hna,
    fun φ hφ => tcjDatum_innDiagKind_of_can hlab (hsimple_of hna) hna hcan φ hφ⟩⟩

theorem tcjDatum_finite_proj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (LargeEvenProj H) := by
  haveI : Finite (GL ι K) := inferInstance
  haveI : Finite ↥H := Subtype.finite
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

theorem tcjDatum_finite_sz {a : ℕ} {K : Type} [Field K] [Finite K] :
    Finite (LargeEvenCenterQuot (LargeEvenSzGroup a K)) := by
  haveI : Finite (GL (Fin 4) K) := inferInstance
  haveI : Finite ↥(LargeEvenSzGroup a K) := Subtype.finite
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

theorem tcjDatum_finite_chevH_false
    (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] [Finite K] :
    Finite (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)) := by
  obtain ⟨e⟩ := centerQuot_chevGroup_equiv (K := K) τ
  haveI : Finite (CFSG.Blueprint.AdjointQuotient τ K) := by
    haveI : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) :=
      CFSG.LieType.Chevalley.generated_group_finite τ K
    exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact Finite.of_equiv _ e.symm.toEquiv

theorem tcjDatum_finite_chevH_true
    (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type) [Field K] [Finite K] :
    Finite (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K true)) := by
  obtain ⟨e⟩ := centerQuot_commutator_chevGroup_equiv (K := K) τ
  haveI : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup τ K) :=
    CFSG.LieType.Chevalley.generated_group_finite τ K
  haveI : Finite ↥⁅CFSG.Blueprint.Chevalley.adjointGroup τ K,
      CFSG.Blueprint.Chevalley.adjointGroup τ K⁆ := Subtype.finite
  haveI : Finite (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.Chevalley.adjointGroup τ K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact Finite.of_equiv _ e.symm.toEquiv

theorem tcjDatum_finite_twF4H (K : Type) [Field K] [Finite K]
    (a : ℕ) : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  obtain ⟨e⟩ := centerQuot_twF4H_equiv K a
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL .F4 K) := inferInstance
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

theorem tcjDatum_finite_twistedH
    (t : CFSG.Blueprint.Chevalley.TwistTag) (n : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Finite (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n)) := by
  obtain ⟨e⟩ := centerQuot_twistedH_equiv (K := K) t n σ hσ
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL t.tag K) := inferInstance
  haveI : Finite ↥(CFSG.Blueprint.twistedFixedGroup t K σ) := Subtype.finite
  haveI : Finite ↥⁅CFSG.Blueprint.twistedFixedGroup t K σ,
      CFSG.Blueprint.twistedFixedGroup t K σ⁆ := Subtype.finite
  haveI : Finite (CFSG.Blueprint.DerivedCentralQuotient
      (CFSG.Blueprint.twistedFixedGroup t K σ)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  exact Finite.of_equiv _ e.symm.toEquiv

theorem tcjDatum_charP_two_of_card {K : Type} [Field K] [Finite K] {m : ℕ}
    (h : Nat.card K = 2 ^ m) : CharP K 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have hcard : Fintype.card K = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact h
  have hdvd : p ∣ 2 ^ m := by rw [← hcard, hk]; exact dvd_pow_self p (PNat.ne_zero k)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

@[expose] def TCJSimple : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (lab : LargeEvenLabel)
    (α : MulAut S) (K : Subgroup S), LargeEvenInLambda2 lab → Subgroup.center S = ⊥ →
      InnDiagKind S lab α → α ^ p = 1 → CFSG.Assembly.IsComponentOf K (ggFixSub α) →
        ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
          GGHasLabel labJ (K ⧸ Subgroup.center K)

theorem ggTCJ_datum_marking {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      Finite R ∧ ((∃ a b : R, a * b ≠ b * a) →
        IsSimpleGroup R ∧ ∀ φ ∈ I, InnDiagKind R lab φ) := by
  intro Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case A =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab (tcjDatum_finite_proj (LargeEvenSLGroup (Fin (rank + 1)) K))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case twA =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_proj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ n)))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case B =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab (tcjDatum_finite_proj (LargeEvenSpGroup K rank))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case C =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab (tcjDatum_finite_proj (LargeEvenSpGroup K rank))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case B2der =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_proj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case D =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    by_cases h3 : rank = 3
    · simp only [if_pos h3] at hQ ⊢
      dsimp only [LargeEvenRecipeLinear] at hQ ⊢
      obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
      refine ⟨K, hf, hfin, hK, hQ, ?_⟩
      haveI : Finite K := hfin
      have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.D, rank, n⟩
          (fun R' _ I' _ => ∃ e : LargeEvenProj (LargeEvenSLGroup (Fin 4) K) ≃* R',
            ∀ φ, φ ∈ LargeEvenMatConjImage
              (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ →
              MulAut.congr e φ ∈ I') := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_pos h3]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
          rw [tcjDatum_congr_refl]; exact hφ⟩⟩
      refine tcjDatum_prop_of_can hlab
        (tcjDatum_finite_proj (LargeEvenSLGroup (Fin 4) K)) (fun hna => ?_) hcan
      have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.D, rank, n⟩
          (fun R' _ _ _ => Nonempty (LargeEvenProj (LargeEvenSLGroup (Fin 4) K) ≃* R')) := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_pos h3]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
      exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
    · simp only [if_neg h3] at hQ ⊢
      dsimp only [LargeEvenRecipeOmegaPlus] at hQ ⊢
      obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
      refine ⟨K, hf, hfin, hK, hQ, ?_⟩
      haveI : Finite K := hfin
      have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.D, rank, n⟩
          (fun R' _ I' _ => ∃ e : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K rank)) ≃* R',
            ∀ φ, φ ∈ LargeEvenInnSet _ → MulAut.congr e φ ∈ I') := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h3]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
          rw [tcjDatum_congr_refl]; exact hφ⟩⟩
      refine tcjDatum_prop_of_can hlab
        (tcjDatum_finite_proj (LargeEvenOmega (LargeEvenQPlus K rank))) (fun hna => ?_) hcan
      have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.D, rank, n⟩
          (fun R' _ _ _ =>
            Nonempty (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K rank)) ≃* R')) := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h3]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
      exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
  case twD =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    by_cases h2 : rank = 2
    · simp only [if_pos h2] at hQ ⊢
      dsimp only [LargeEvenRecipeLinear] at hQ ⊢
      obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
      refine ⟨K, hf, hfin, hK, hQ, ?_⟩
      haveI : Finite K := hfin
      have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
          (fun R' _ I' _ => ∃ e : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃* R',
            ∀ φ, φ ∈ LargeEvenMatConjImage
              (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ →
              MulAut.congr e φ ∈ I') := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_pos h2]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
          rw [tcjDatum_congr_refl]; exact hφ⟩⟩
      refine tcjDatum_prop_of_can hlab
        (tcjDatum_finite_proj (LargeEvenSLGroup (Fin 2) K)) (fun hna => ?_) hcan
      have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
          (fun R' _ _ _ => Nonempty (LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃* R')) := by
        simp only [CFSG.Assembly.LargeEvenRawDatum, if_pos h2]
        exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
      exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
    · simp only [if_neg h2] at hQ ⊢
      by_cases h3 : rank = 3
      · simp only [if_pos h3] at hQ ⊢
        dsimp only [LargeEvenRecipeUnitary] at hQ ⊢
        obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
        refine ⟨K, hf, hfin, hK, hQ, ?_⟩
        haveI : Finite K := hfin
        have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
            (fun R' _ I' _ => ∃ e : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃* R',
              ∀ φ, φ ∈ LargeEvenMatConjImage
                (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
                (LargeEvenGUSet (Fin 4) K (2 ^ n)) → MulAut.congr e φ ∈ I') := by
          simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h2, if_pos h3]
          exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
            rw [tcjDatum_congr_refl]; exact hφ⟩⟩
        refine tcjDatum_prop_of_can hlab
          (tcjDatum_finite_proj (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (fun hna => ?_) hcan
        have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
            (fun R' _ _ _ =>
              Nonempty (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃* R')) := by
          simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h2, if_pos h3]
          exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
        exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
      · simp only [if_neg h3] at hQ ⊢
        dsimp only [LargeEvenRecipeOmegaMinus] at hQ ⊢
        obtain ⟨K, hf, hfin, hK, b, c, hbc, hQ⟩ := hQ
        refine ⟨K, hf, hfin, hK, b, c, hbc, hQ, ?_⟩
        haveI : Finite K := hfin
        have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
            (fun R' _ I' _ =>
              ∃ e : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (K := K) (rank - 1) b c)) ≃* R',
              ∀ φ, φ ∈ LargeEvenInnSet _ → MulAut.congr e φ ∈ I') := by
          simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h2, if_neg h3]
          exact ⟨K, hf, hfin, hK, b, c, hbc, ⟨MulEquiv.refl _, fun φ hφ => by
            rw [tcjDatum_congr_refl]; exact hφ⟩⟩
        refine tcjDatum_prop_of_can hlab
          (tcjDatum_finite_proj (LargeEvenOmega (LargeEvenQMinus (K := K) (rank - 1) b c)))
          (fun hna => ?_) hcan
        have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.twD, rank, n⟩
            (fun R' _ _ _ =>
              Nonempty (LargeEvenProj
                (LargeEvenOmega (LargeEvenQMinus (K := K) (rank - 1) b c)) ≃* R')) := by
          simp only [CFSG.Assembly.LargeEvenRawDatum, if_neg h2, if_neg h3]
          exact ⟨K, hf, hfin, hK, b, c, hbc, ⟨MulEquiv.refl _⟩⟩
        exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
  case G2 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_false CFSG.Blueprint.Chevalley.Tag.G2 K)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case G2der =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley,
      LargeEvenRecipeG2Derived] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_true CFSG.Blueprint.Chevalley.Tag.G2 K)
      (fun hna =>
        have hC : CFSG.Open.StatedClassicalModel
            (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) .PSU 3 3 1 :=
          (CFSG.StandardType.lieModel_g2der K hK hna).statedClassicalModel (by decide)
        (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC).2)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]
        exact Subgroup.subset_closure (Set.mem_union_left _ hφ)⟩⟩
  case F4 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_false CFSG.Blueprint.Chevalley.Tag.F4 K)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case E6 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_false CFSG.Blueprint.Chevalley.Tag.E6 K)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case E7 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_false CFSG.Blueprint.Chevalley.Tag.E7 K)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case E8 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_chevH_false CFSG.Blueprint.Chevalley.Tag.E8 K)
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case twE6 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    haveI : CharP K 2 := tcjDatum_charP_two_of_card (by rw [hK, pow_mul])
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_twistedH CFSG.Blueprint.Chevalley.TwistTag.E6 n K
        (iterateFrobenius K 2 n)
        (fun c => by rw [iterateFrobenius_def]))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case triD4 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    haveI : CharP K 2 := tcjDatum_charP_two_of_card (by rw [hK, pow_mul])
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_twistedH CFSG.Blueprint.Chevalley.TwistTag.D4 n K
        (iterateFrobenius K 2 n)
        (fun c => by rw [iterateFrobenius_def]))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case twB2 =>
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeSuzuki] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    refine tcjDatum_prop_of_can hlab (tcjDatum_finite_sz (a := (n - 1) / 2))
      (fun hna => (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna
        ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩).1)
      ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
        rw [tcjDatum_congr_refl]; exact hφ⟩⟩
  case twF4 =>
    have hn3 : 3 ≤ n := hlab.2.2.2
    have ha : (n - 1) / 2 ≠ 0 := Nat.div_pos (by omega) (by norm_num) |>.ne'
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4, rank, n⟩
        (fun R' _ I' _ => ∃ e : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K
            (LargeEvenTwF4H ((n - 1) / 2) K) → MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited]
      split_ifs with h0
      · exact absurd h0 ha
      · exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
          rw [tcjDatum_congr_refl]; exact hφ⟩⟩
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_twF4H K ((n - 1) / 2)) (fun hna => ?_) hcan
    have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4, rank, n⟩
        (fun R' _ _ _ =>
          Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) ≃* R')) := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited]
      exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
    exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1
  case twF4der =>
    have hn1 : n = 1 := hlab.2.2
    have ha : (n - 1) / 2 = 0 := by rw [hn1]
    dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at ⊢
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ, ?_⟩
    haveI : Finite K := hfin
    have hcan : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4der, rank, n⟩
        (fun R' _ I' _ => ∃ e : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) ≃* R',
          ∀ φ, φ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K
            (LargeEvenTwF4H ((n - 1) / 2) K) → MulAut.congr e φ ∈ I') := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited]
      split_ifs with h0
      exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _, fun φ hφ => by
          rw [tcjDatum_congr_refl]
          exact Subgroup.subset_closure (Set.mem_union_left _ hφ)⟩⟩
    refine tcjDatum_prop_of_can hlab
      (tcjDatum_finite_twF4H K ((n - 1) / 2)) (fun hna => ?_) hcan
    have hcan_s : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4der, rank, n⟩
        (fun R' _ _ _ =>
          Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) ≃* R')) := by
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited]
      exact ⟨K, hf, hfin, hK, ⟨MulEquiv.refl _⟩⟩
    exact (CFSG.LocalAnalysis.GLTheoremA.I91T.simple_of_datum hlab (by simp) hna hcan_s).1

theorem ggTCJKnown_of_simple
    (h : TCJSimple) : GGTCJKnown := by
  intro p hp hp2 lab hlab
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hqP => ⟨hqP.1, ?_⟩) (ggTCJ_datum_marking hlab Q hQ)
  intro L' _ _ ψ hψ hker hperf e he hφe J hJ
  let φ : MulAut R := hφe.choose
  have hφI : φ ∈ I := hφe.choose_spec.1
  have hφind : ∀ l : L', φ (ψ l) = ψ (e l) := hφe.choose_spec.2
  have hna : ∃ a b : R, a * b ≠ b * a := by
    by_contra hnab
    push Not at hnab
    haveI : IsMulCommutative R := isMulCommutative_iff.mpr hnab
    have hRcomm : commutator R = ⊥ := (commutator_eq_bot_iff R).mpr inferInstance
    have hmap : (commutator L').map ψ = ⊥ := by
      have h1 : (commutator L').map ψ = commutator R := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          MonoidHom.range_eq_top_of_surjective _ hψ, commutator_def]
      rw [h1, hRcomm]
    have hle : commutator L' ≤ ψ.ker := by
      intro x hx
      have hx' : ψ x ∈ (commutator L').map ψ := ⟨x, hx, rfl⟩
      rw [hmap] at hx'
      exact hx'
    have hcenter : commutator L' ≤ Subgroup.center L' := hle.trans hker
    have hZtop : Subgroup.center L' = ⊤ := top_le_iff.mp (hperf ▸ hcenter)
    have hcommL' : commutator L' = ⊥ :=
      (commutator_eq_bot_iff L').mpr (isMulCommutative_iff.mpr fun a b =>
        (Subgroup.mem_center_iff.mp (hZtop.symm ▸ Subgroup.mem_top a) b).symm)
    have htopbot : (⊤ : Subgroup L') = ⊥ := by rw [← hperf, hcommL']
    haveI : Subsingleton L' := ⟨fun a b => by
      have ha : a = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top a)
      have hb : b = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top b)
      rw [ha, hb]⟩
    haveI : Subsingleton J := ⟨fun a b =>
      Subtype.ext (Subsingleton.elim (a : L') (b : L'))⟩
    haveI : Subsingleton (J ⧸ Subgroup.center J) := inferInstance
    haveI : Nontrivial (J ⧸ Subgroup.center J) := hJ.2.2.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (J ⧸ Subgroup.center J)
    exact hab (Subsingleton.elim a b)
  haveI : Finite R := hqP.2.1
  have hRsimple : IsSimpleGroup R := (hqP.2.2 hna).1
  have hRinn : InnDiagKind R lab φ := (hqP.2.2 hna).2 φ hφI
  have hRcenter : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hpow : ∀ n : ℕ, ∀ l : L', (φ ^ n) (ψ l) = ψ ((e ^ n) l) := by
    intro n
    induction n with
    | zero => intro l; simp
    | succ n ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφind l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφp : φ ^ p = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have hev : (e ^ p) l = l := by simpa using congrArg (fun f : MulAut L' => f l) he
    rw [hpow p l, hev]
    rfl
  obtain ⟨labJ, hlabJ, hdvd, hhas⟩ :=
    h p hp hp2 R lab φ (J.map ψ) hlab hRcenter hRinn hφp
      (ggTCJ_descent ψ hψ hker e φ hφind J hJ).1
  exact ⟨labJ, hlabJ, hdvd,
    ggHasLabel_of_mulEquiv (ggTCJ_descent ψ hψ hker e φ hφind J hJ).2.some.symm hhas⟩

theorem tcj_ggFixSub_eq_fixSubgroup {S : Type} [Group S] (α : MulAut S) :
    ggFixSub α = fixSubgroup α := by
  ext x
  rfl

end CFSG.StandardType.TCJ

end

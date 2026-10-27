module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwLat1
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGTl_normalizer_data
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ v : WeylGroup TwistTag.E6.tag, v * v = 1 ∧
      ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
        w₀ * ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
            twistedE6RootGroup K σ) * w₀⁻¹ =
          ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
            ((ggKGEl_mat v).mulVec y)) : ↥E) : twistedE6RootGroup K σ) := by
  obtain ⟨v, -, hconj⟩ :=
    ggKGTwE6_normalizer_weyl hK hσ hp hp5 F (Or.inr ⟨hpq, hv⟩) hrefl.1
  let nv : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v
  let yhat : twistedE6RootGroup K σ → ModGL TwistTag.E6.tag (AlgebraicClosure K) := fun e =>
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (e : ModGL TwistTag.E6.tag K) * F.g0
  refine ⟨v, ?_, fun y => ?_⟩
  · have hvv : ∀ e ∈ E, (nv * nv) * yhat e * (nv * nv)⁻¹ = yhat e := by
      intro e he
      have hmem : w₀ * e * w₀⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrefl.1 e).mp he
      calc (nv * nv) * yhat e * (nv * nv)⁻¹
          = nv * (nv * yhat e * nv⁻¹) * nv⁻¹ := by group
        _ = nv * yhat (w₀ * e * w₀⁻¹) * nv⁻¹ := by rw [← hconj e he]
        _ = yhat (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹) := (hconj (w₀ * e * w₀⁻¹) hmem).symm
        _ = yhat e := by rw [hrefl.2.1 e he]
    refine ggKGTwE6_normalizer_faithful hK hσ hp hp5 F (Or.inr ⟨hpq, hv⟩)
      (u := v * v) fun e he => ?_
    obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) v v
    have hT : yhat e ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      ((F.mem_iff e).1 he).2 |>.1
    have hcomm : k * yhat e = yhat e * k :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
        (torusGroup_le_diagonalGroup hT)
    have h1 := hvv e he
    rw [hk_eq] at h1
    calc canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v * v) * yhat e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v * v))⁻¹
        = k⁻¹ * ((k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v * v)) *
            yhat e *
            (k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (v * v))⁻¹) *
            k := by group
      _ = k⁻¹ * yhat e * k := by rw [h1]
      _ = yhat e := by
          change k⁻¹ * yhat e * k = yhat e
          rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · have he : ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
        twistedE6RootGroup K σ) ∈ E :=
      (Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y)).2
    have h1 := hconj _ he
    rw [ggKGTl_pi_spec hK hσ hp hp5 hpq F hv ζ hζ, canonicalRep_conj_rootDiagUnit,
      ggKGEl_weylTuple_zeta] at h1
    rw [← ggKGTl_pi_spec hK hσ hp hp5 hpq F hv ζ hζ] at h1
    exact ggKGTl_conj_injective F h1

def ggKGTl_liftZ {p : ℕ} (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    Fin TwistTag.E6.tag.rank → ℤ :=
  fun i => ((x i).val : ℤ)

noncomputable def ggKGTl_modAct {p : ℕ} (V : WeylGroup TwistTag.E6.tag)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) : Fin TwistTag.E6.tag.rank → ZMod p :=
  ((ggKGEl_mat V).map (Int.castRingHom (ZMod p))).mulVec x

theorem ggKGTl_pi_eq_one_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin TwistTag.E6.tag.rank → ℤ) :
    Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) = 1 ↔
      ∀ i, (y i : ZMod p) = 0 := by
  constructor
  · intro h
    have h1 : rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y i) = 1 := by
      have h2 : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
            twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 = 1 := by
        rw [h]
        exact ggKGTl_conj_one F
      rwa [ggKGTl_pi_spec hK hσ hp hp5 hpq F hv ζ hζ] at h2
    have h3 : (fun i => ζ ^ y i) = 1 := rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
    intro i
    have h4 : ζ ^ (y i) = 1 := by
      have := congrFun h3 i
      rwa [Pi.one_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mpr ((hζ.zpow_eq_one_iff_dvd (y i)).1 h4)
  · intro h
    apply Subtype.ext
    apply ggKGTl_conj_injective F
    dsimp only
    rw [ggKGTl_pi_spec hK hσ hp hp5 hpq F hv ζ hζ, Subgroup.coe_one, ggKGTl_conj_one]
    rw [← rootDiagUnit_one]
    congr 1
    funext i
    rw [Pi.one_apply]
    exact (hζ.zpow_eq_one_iff_dvd (y i)).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mp (h i))

theorem ggKGTl_pi_eq_zero_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y = 0 ↔ ∀ i, (y i : ZMod p) = 0 := by
  rw [show (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y = 0) ↔
      (Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) = 1) from
    ⟨fun h => by rw [h]; rfl, fun h => Additive.toMul.injective (by rw [h]; rfl)⟩]
  exact ggKGTl_pi_eq_one_iff hK hσ hp hp5 hpq F hv ζ hζ y

theorem ggKGTl_pi_eq_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y y' : Fin TwistTag.E6.tag.rank → ℤ) :
    ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y = ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y' ↔
      ∀ i, (y i : ZMod p) = (y' i : ZMod p) := by
  rw [← sub_eq_zero (a := ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y)]
  rw [show ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y -
      ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y' =
      ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ (y - y') from (map_sub _ _ _).symm]
  rw [ggKGTl_pi_eq_zero_iff hK hσ hp hp5 hpq F hv ζ hζ]
  constructor <;> intro h i
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this

theorem ggKGTl_modAct_eq {p : ℕ} [NeZero p] (V : WeylGroup TwistTag.E6.tag)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) (i : Fin TwistTag.E6.tag.rank) :
    (ggKGTl_modAct V x i : ZMod p) =
      (((ggKGEl_mat V).mulVec (ggKGTl_liftZ x)) i : ZMod p) := by
  simp only [ggKGTl_modAct, ggKGTl_liftZ, Matrix.mulVec, Matrix.map_apply, dotProduct]
  push_cast
  exact Finset.sum_congr (M := ZMod p) rfl fun j _ => by simp [ZMod.natCast_zmod_val]

noncomputable def ggKGTl_pibar
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) : ↥E :=
  Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_liftZ x))

theorem ggKGTl_pibar_bijective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Bijective (ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro x x' h
    have h' : ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_liftZ x) =
        ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_liftZ x') :=
      Additive.toMul.injective h
    have h2 := (ggKGTl_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ _ _).1 h'
    funext i
    have := h2 i
    simpa [ggKGTl_liftZ] using this
  · intro e
    obtain ⟨y, hy⟩ := ggKGTl_pi_surjective hK hσ hp hp5 hpq F hv ζ hζ (Additive.ofMul e)
    refine ⟨fun i => (y i : ZMod p), ?_⟩
    have h2 : ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
          (ggKGTl_liftZ (fun i => (y i : ZMod p))) =
        ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y := by
      rw [ggKGTl_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ]
      intro i
      simp only [ggKGTl_liftZ]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i : ZMod p)
    show Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
      (ggKGTl_liftZ (fun i => (y i : ZMod p)))) = e
    rw [h2, hy]
    rfl

theorem ggKGTl_pibar_modAct
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ}
    (hN : w₀ ∈ Subgroup.normalizer (E : Set (twistedE6RootGroup K σ)))
    (V : WeylGroup TwistTag.E6.tag)
    (hactV : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
      w₀ * ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹ =
        ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
          ((ggKGEl_mat V).mulVec y)) : ↥E) : twistedE6RootGroup K σ))
    (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_modAct V x) =
      ⟨w₀ * ((ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ x : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹,
        (Subgroup.mem_normalizer_iff.mp hN _).mp
          (ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ x).2⟩ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  dsimp only [ggKGTl_pibar]
  have h1 : ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_liftZ (ggKGTl_modAct V x)) =
      ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
        ((ggKGEl_mat V).mulVec (ggKGTl_liftZ x)) := by
    rw [ggKGTl_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ]
    intro i
    simpa [ggKGTl_liftZ] using ggKGTl_modAct_eq V x i
  rw [h1]
  exact (hactV (ggKGTl_liftZ x)).symm

theorem ggKGTl_fix_count
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀)
    (V : WeylGroup TwistTag.E6.tag)
    (hactV : ∀ y : Fin TwistTag.E6.tag.rank → ℤ,
      w₀ * ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹ =
        ((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ
          ((ggKGEl_mat V).mulVec y)) : ↥E) : twistedE6RootGroup K σ)) :
    Nat.card {x : Fin TwistTag.E6.tag.rank → ZMod p //
      ((ggKGEl_mat V).map (Int.castRingHom (ZMod p))).mulVec x = x} =
        p ^ (TwistTag.E6.tag.rank - 1) := by
  change Nat.card {x : Fin TwistTag.E6.tag.rank → ZMod p // ggKGTl_modAct V x = x} =
    p ^ (TwistTag.E6.tag.rank - 1)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm1 : 1 ≤ TwistTag.E6.tag.rank := by decide
  have hbij := ggKGTl_pibar_bijective hK hσ hp hp5 hpq F hv ζ hζ
  let eE : (Fin TwistTag.E6.tag.rank → ZMod p) ≃ ↥E := Equiv.ofBijective _ hbij
  have heE : ∀ x, eE x = ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ x := fun x => rfl
  have hcardE : Nat.card ↥E = p ^ TwistTag.E6.tag.rank := by
    rw [← Nat.card_congr eE]
    simp [Nat.card_fun, Nat.card_zmod]
  have hfixeq : Nat.card {x : Fin TwistTag.E6.tag.rank → ZMod p // ggKGTl_modAct V x = x} =
      Nat.card {e : ↥E // w₀ * ((e : ↥E) : twistedE6RootGroup K σ) * w₀⁻¹ =
        ((e : ↥E) : twistedE6RootGroup K σ)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv eE fun x => ?_)
    rw [heE x]
    have hmod := ggKGTl_pibar_modAct hK hσ hp hp5 hpq F hv ζ hζ hrefl.1 V hactV x
    constructor
    · intro hx
      rw [hx] at hmod
      exact (Subtype.ext_iff.mp hmod).symm
    · intro hx
      have h2 : ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ (ggKGTl_modAct V x) =
          ggKGTl_pibar hK hσ hp hp5 hpq F hv ζ hζ x := by
        rw [hmod]
        exact Subtype.ext hx
      exact hbij.1 h2
  have h3 := hrefl.2.2
  rw [← hfixeq, hcardE] at h3
  have h4 : p ^ TwistTag.E6.tag.rank = p ^ (TwistTag.E6.tag.rank - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hm1]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hp.pos h3

end CFSG.StandardType

end

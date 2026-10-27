module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGTl_conj_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    Function.Injective (fun x : twistedE6RootGroup K σ =>
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * F.g0) := by
  intro x y h
  have h' : baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        (y : ModGL TwistTag.E6.tag K) := by
    have := congrArg (fun z => F.g0 * z * F.g0⁻¹) h
    simpa [mul_assoc] using this
  exact Subtype.ext (baseChangeGL_injective (f := algebraMap K (AlgebraicClosure K)) h')

theorem ggKGTl_conj_mul
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (a b : twistedE6RootGroup K σ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((a * b : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (a : ModGL TwistTag.E6.tag K) * F.g0) *
        (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (b : ModGL TwistTag.E6.tag K) * F.g0) := by
  rw [Subgroup.coe_mul, map_mul]
  group

theorem ggKGTl_conj_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 = 1 := by
  rw [Subgroup.coe_one, map_one]
  group

noncomputable def ggKGTl_pick
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin TwistTag.E6.tag.rank → ℤ) : ↥E :=
  let b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := fun i => ζ ^ y i
  let hb : ∀ j, b j ^ p = 1 := fun j => ggKGEl_zetaPow_pow_eq_one ζ hζ (y j)
  let hact : weylTuple F.v
      (fun i => Units.map F.Fr.toMonoidHom (b (TwistTag.E6.perm.symm i))) = b :=
    ggKGTc_hact_w_w0 F hv hpq hb
  let h := ggKGTc_exists_conj_of_hact hK hσ hp hp5 F hb hact
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem ggKGTl_pick_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin TwistTag.E6.tag.rank → ℤ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ y : ↥E) :
          twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y i) := by
  dsimp only [ggKGTl_pick]
  exact (Classical.choose_spec (ggKGTc_exists_conj_of_hact hK hσ hp hp5 F
    (b := fun i => ζ ^ y i) (fun j => ggKGEl_zetaPow_pow_eq_one ζ hζ (y j))
    (ggKGTc_hact_w_w0 (b := fun i => ζ ^ y i) F hv hpq
      (fun j => ggKGEl_zetaPow_pow_eq_one ζ hζ (y j))))).2.symm

noncomputable def ggKGTl_pi
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    (Fin TwistTag.E6.tag.rank → ℤ) →+ Additive ↥E where
  toFun y := Additive.ofMul (ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ y)
  map_zero' := by
    change Additive.ofMul (ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ 0) =
      Additive.ofMul (1 : ↥E)
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGTl_conj_injective F
    dsimp only
    rw [ggKGTl_pick_spec, Subgroup.coe_one, ggKGTl_conj_one]
    simp only [Pi.zero_apply, zpow_zero, Pi.one_apply]
    exact rootDiagUnit_one
  map_add' y y' := by
    change Additive.ofMul (ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ (y + y')) =
      Additive.ofMul (ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ y *
        ggKGTl_pick hK hσ hp hp5 hpq F hv ζ hζ y')
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGTl_conj_injective F
    dsimp only
    rw [ggKGTl_pick_spec, Subgroup.coe_mul, ggKGTl_conj_mul, ggKGTl_pick_spec,
      ggKGTl_pick_spec]
    rw [show (fun i => ζ ^ (y + y') i) =
        (fun i => ζ ^ y i) * (fun i => ζ ^ y' i) from by
      funext i; simp [Pi.add_apply, zpow_add]]
    rw [rootDiagUnit_mul]

theorem ggKGTl_pi_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin TwistTag.E6.tag.rank → ℤ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((Additive.toMul (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y i) :=
  ggKGTl_pick_spec hK hσ hp hp5 hpq F hv ζ hζ y

theorem ggKGTl_pi_surjective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1)
    (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Surjective (ggKGTl_pi hK hσ hp hp5 hpq F hv ζ hζ) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro e
  let Ψ : ↥E →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    { toFun := fun x => F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0
      map_one' := ggKGTl_conj_one F
      map_mul' := fun a b => ggKGTl_conj_mul F (a : twistedE6RootGroup K σ)
        (b : twistedE6RootGroup K σ) }
  have he : ((Additive.toMul e : ↥E) : twistedE6RootGroup K σ) ^ p = 1 :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : twistedE6RootGroup K σ)).1
      (Additive.toMul e).2).1
  have heT : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        F.g0 ∈ twistedTorusOf
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : twistedE6RootGroup K σ)).1
      (Additive.toMul e).2).2
  have heG : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        F.g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 heT).1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heG
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : (rootDiagUnit TwistTag.E6.tag b) ^ p = 1 := by
      rw [← hb]
      change (Ψ (Additive.toMul e)) ^ p = 1
      rw [← map_pow, show (Additive.toMul e : ↥E) ^ p = 1 from Subtype.ext he, map_one]
    have hbp' : b ^ p = 1 := rootDiagUnit_injective (τ := TwistTag.E6.tag)
      (by rw [← rootDiagUnit_pow, h1, rootDiagUnit_one])
    intro i
    simpa using congrFun hbp' i
  choose y hy using fun i => ggKGEl_eq_zetaPow_of_pow_eq_one ζ hζ (hbp i)
  refine ⟨y, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply ggKGTl_conj_injective F
  dsimp only
  rw [ggKGTl_pi_spec, hb]
  congr 1
  funext i
  exact (hy i).symm

end CFSG.StandardType

end

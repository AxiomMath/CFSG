module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylReflectionOfFixedPoints
public import TauCeti.LinearAlgebra.Matrix.Echelon.KernelBasis
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

private theorem ggKGTr_card_ker_mulVec {p n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) (ZMod p)) :
    Nat.card {x : Fin n → ZMod p // B *ᵥ x = 0} = p ^ (n - B.rank) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hker : Nat.card (LinearMap.ker B.mulVecLin) =
      Nat.card ({j // TauCeti.IsFreeColumn (List.ofFn B) j} → ZMod p) :=
    Nat.card_congr (TauCeti.freeColumnBasis B).equivFun.toEquiv
  rw [show Nat.card {x : Fin n → ZMod p // B *ᵥ x = 0} =
      Nat.card (LinearMap.ker B.mulVecLin) from rfl, hker, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, ← TauCeti.card_isFreeColumn B]

private theorem ggKGTr_card_fix_transpose {p n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin n) (Fin n) (ZMod p)) :
    Nat.card {x : Fin n → ZMod p // B *ᵥ x = x} =
      Nat.card {x : Fin n → ZMod p // Bᵀ *ᵥ x = x} := by
  have h1 : Nat.card {x : Fin n → ZMod p // B *ᵥ x = x} =
      Nat.card {x : Fin n → ZMod p // (B - 1) *ᵥ x = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun x => ?_)
    simp [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have h2 : Nat.card {x : Fin n → ZMod p // Bᵀ *ᵥ x = x} =
      Nat.card {x : Fin n → ZMod p // (Bᵀ - 1) *ᵥ x = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun x => ?_)
    simp [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [h1, h2, ggKGTr_card_ker_mulVec (B - 1), ggKGTr_card_ker_mulVec (Bᵀ - 1)]
  congr 1
  rw [← Matrix.rank_transpose, Matrix.transpose_sub, Matrix.transpose_one]

private noncomputable def ggKGTr_dualMat (u : WeylGroup TwistTag.E6.tag) :
    Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
  Matrix.of fun i j => (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j

private theorem ggKGTr_dualMat_eq_transpose (u : WeylGroup TwistTag.E6.tag) (hu : u * u = 1) :
    ggKGTr_dualMat u = (weylLatticeMatrix TwistTag.E6.tag u)ᵀ := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  ext i j
  simp only [ggKGTr_dualMat, Matrix.of_apply, Matrix.transpose_apply, weylLatticeMatrix_apply,
    huinv]

private theorem ggKGTr_expTuple_injective {p : ℕ} [NeZero p] {L : Type} [Field L]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (expTuple (τ := TwistTag.E6.tag) (p := p) ζ) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simp only [expTuple] at hi
  have hlt1 := ZMod.val_lt (x i)
  have hlt2 := ZMod.val_lt (y i)
  have hval : (x i).val = (y i).val := hζ.pow_inj hlt1 hlt2 hi
  rw [← ZMod.natCast_zmod_val (x i), ← ZMod.natCast_zmod_val (y i), hval]

private theorem ggKGTr_expTuple_pow {p : ℕ} {L : Type} [Field L]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ∀ i, expTuple (τ := TwistTag.E6.tag) (p := p) ζ x i ^ p = 1 := by
  intro i
  simp only [expTuple]
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

private theorem ggKGTr_weylTuple_expTuple {p : ℕ} [NeZero p] {L : Type} [Field L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (u : WeylGroup TwistTag.E6.tag)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    weylTuple u (expTuple (τ := TwistTag.E6.tag) (p := p) ζ x) =
      expTuple (τ := TwistTag.E6.tag) (p := p) ζ
        ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x) := by
  funext i
  set M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) (ZMod p) :=
    (ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) with hM
  have hL : weylTuple u (expTuple (τ := TwistTag.E6.tag) (p := p) ζ x) i =
      ζ ^ (∑ j, ((x j).val : ℤ) * (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j) := by
    simp only [weylTuple]
    exact rootChar_expTuple x (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ))
  have hR : expTuple (τ := TwistTag.E6.tag) (p := p) ζ (M *ᵥ x) i =
      ζ ^ (((M *ᵥ x) i).val : ℤ) := by
    simp only [expTuple, zpow_natCast]
  have hmod : ((∑ j, ((x j).val : ℤ) *
      (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j : ℤ) : ZMod p) = (M *ᵥ x) i := by
    rw [Matrix.mulVec, dotProduct]
    simp only [hM, Matrix.map_apply, ggKGTr_dualMat, Matrix.of_apply, Int.cast_sum, Int.cast_mul,
      Int.cast_natCast, ZMod.natCast_zmod_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mul_comm _ _
  have hdvd : (p : ℤ) ∣ ((∑ j, ((x j).val : ℤ) *
      (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j : ℤ) - ((M *ᵥ x) i).val) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hzero : (((∑ j, ((x j).val : ℤ) *
        (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j : ℤ) -
        (((M *ᵥ x) i).val : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, Int.cast_natCast, hmod, ZMod.natCast_zmod_val, sub_self]
    exact hzero
  have hz : ζ ^ (((∑ j, ((x j).val : ℤ) *
      (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j : ℤ) - ((M *ᵥ x) i).val)) = 1 := by
    rw [IsPrimitiveRoot.zpow_eq_one_iff_dvd hζ]
    exact hdvd
  have heq : ζ ^ (∑ j, ((x j).val : ℤ) *
      (u⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) j : ℤ) =
      ζ ^ (((M *ᵥ x) i).val : ℤ) := by
    refine mul_inv_eq_one.mp ?_
    rw [← zpow_sub]
    exact hz
  rw [hL, hR]
  exact heq

private noncomputable def ggKGTr_Y
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj F.g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (twistedE6RootGroup K σ).subtype)

private theorem ggKGTr_Y_apply
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (x : twistedE6RootGroup K σ) :
    ggKGTr_Y F x = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * F.g0 := rfl

private theorem ggKGTr_Y_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    Function.Injective (ggKGTr_Y F) :=
  (MulAut.conj F.g0⁻¹).injective.comp
    ((baseChangeGL_injective (algebraMap K (AlgebraicClosure K))).comp
      (Subgroup.subtype_injective _))

private theorem ggKGTr_expTuple_surj {p : ℕ} [NeZero p] {L : Type} [Field L]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {b : Fin TwistTag.E6.tag.rank → Lˣ} (hb : ∀ i, b i ^ p = 1) :
    ∃ x : Fin TwistTag.E6.tag.rank → ZMod p,
      expTuple (τ := TwistTag.E6.tag) (p := p) ζ x = b := by
  have hζ' : IsPrimitiveRoot (ζ : L) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have h : ∀ i, ∃ j < p, (ζ : L) ^ j = (b i : L) := fun i =>
    hζ'.eq_pow_of_pow_eq_one (by
      have := congrArg (fun u : Lˣ => (u : L)) (hb i)
      simpa using this)
  choose k hk hk_eq using h
  refine ⟨fun i => (k i : ZMod p), ?_⟩
  funext i
  simp only [expTuple]
  rw [ZMod.val_cast_of_lt (hk i)]
  apply Units.ext
  simpa using hk_eq i

private noncomputable def ggKGTr_expEquiv {p : ℕ} [NeZero p] {L : Type} [Field L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) :
    (Fin TwistTag.E6.tag.rank → ZMod p) ≃
      {b : Fin TwistTag.E6.tag.rank → Lˣ // ∀ i, b i ^ p = 1} :=
  Equiv.ofBijective
    (fun x => ⟨expTuple (τ := TwistTag.E6.tag) (p := p) ζ x,
      fun i => ggKGTr_expTuple_pow hζ x i⟩)
    (by
      constructor
      · intro x y h
        exact ggKGTr_expTuple_injective hζ (Subtype.ext_iff.mp h)
      · intro b
        obtain ⟨x, hx⟩ := ggKGTr_expTuple_surj hζ b.2
        exact ⟨x, Subtype.ext hx⟩)

private theorem ggKGTr_expEquiv_apply {p : ℕ} [NeZero p] {L : Type} [Field L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    (ggKGTr_expEquiv ζ hζ x : Fin TwistTag.E6.tag.rank → Lˣ) =
      expTuple (τ := TwistTag.E6.tag) (p := p) ζ x := rfl

private theorem ggKGTr_card_multiplicative {p r : ℕ} :
    Nat.card (Multiplicative (Fin r → ZMod p)) = p ^ r := by
  change Nat.card (Fin r → ZMod p) = p ^ r
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private noncomputable def ggKGTr_PhiFun
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : IsPrimitiveRoot ζ p) (x : Fin TwistTag.E6.tag.rank → ZMod p) : E :=
  ⟨Classical.choose (ggKGTc_exists_conj_of_hact hK hσ hp hp5 F
      (fun j => ggKGTr_expTuple_pow hζ x j)
      (ggKGTc_hact_w_w0 F hv hpq (fun j => ggKGTr_expTuple_pow hζ x j))),
   (Classical.choose_spec (ggKGTc_exists_conj_of_hact hK hσ hp hp5 F
      (fun j => ggKGTr_expTuple_pow hζ x j)
      (ggKGTc_hact_w_w0 F hv hpq (fun j => ggKGTr_expTuple_pow hζ x j)))).1⟩

private theorem ggKGTr_PhiFun_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : IsPrimitiveRoot ζ p) (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ggKGTr_Y F (ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ x) =
      rootDiagUnit TwistTag.E6.tag (expTuple (τ := TwistTag.E6.tag) (p := p) ζ x) := by
  rw [ggKGTr_PhiFun, ggKGTr_Y_apply]
  exact (Classical.choose_spec (ggKGTc_exists_conj_of_hact hK hσ hp hp5 F
      (fun j => ggKGTr_expTuple_pow hζ x j)
      (ggKGTc_hact_w_w0 F hv hpq (fun j => ggKGTr_expTuple_pow hζ x j)))).2.symm

private noncomputable def ggKGTr_Phi
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    [NeZero p]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : IsPrimitiveRoot ζ p) : (Fin TwistTag.E6.tag.rank → ZMod p) ≃ E :=
  Equiv.ofBijective (ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ) (by
    constructor
    · intro x y h
      have h1 : rootDiagUnit TwistTag.E6.tag (expTuple (τ := TwistTag.E6.tag) (p := p) ζ x) =
          rootDiagUnit TwistTag.E6.tag (expTuple (τ := TwistTag.E6.tag) (p := p) ζ y) := by
        rw [← ggKGTr_PhiFun_spec hK hσ hp hp5 hpq F hv ζ hζ x,
          ← ggKGTr_PhiFun_spec hK hσ hp hp5 hpq F hv ζ hζ y, h]
      exact ggKGTr_expTuple_injective hζ (rootDiagUnit_injective h1)
    · intro e
      have heT : ggKGTr_Y F (e : twistedE6RootGroup K σ) ∈
          torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
        (mem_twistedTorusOf.1 ((F.mem_iff (e : twistedE6RootGroup K σ)).1 e.2).2).1
      obtain ⟨b, hb_eq⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heT
      have hb_pow_eq : b ^ p = 1 := by
        apply rootDiagUnit_injective
        rw [← rootDiagUnit_pow, ← hb_eq]
        have hep : (e : twistedE6RootGroup K σ) ^ p = 1 :=
          ((F.mem_iff (e : twistedE6RootGroup K σ)).1 e.2).1
        rw [← map_pow, hep, map_one, rootDiagUnit_one]
      have hb_pow : ∀ j, b j ^ p = 1 := by
        intro j
        have := congrFun hb_pow_eq j
        simpa [Pi.pow_apply] using this
      obtain ⟨x, hx⟩ := (ggKGTr_expEquiv ζ hζ).surjective ⟨b, hb_pow⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      apply ggKGTr_Y_injective F
      rw [ggKGTr_PhiFun_spec, ← ggKGTr_expEquiv_apply ζ hζ x, Subtype.ext_iff.mp hx, hb_eq])

private theorem ggKGTr_PhiFun_action
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    [NeZero p]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (ζ : (AlgebraicClosure K)ˣ)
    (hζ : IsPrimitiveRoot ζ p) {x₀ : twistedE6RootGroup K σ}
    (u : WeylGroup TwistTag.E6.tag)
    (hconj : ∀ e ∈ E, ggKGTr_Y F (x₀ * e * x₀⁻¹) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u * ggKGTr_Y F e *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹)
    (x : Fin TwistTag.E6.tag.rank → ZMod p) :
    ggKGTr_Y F (ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ
        ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x)) =
      ggKGTr_Y F (x₀ * ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ x * x₀⁻¹) := by
  have h1 := ggKGTr_PhiFun_spec hK hσ hp hp5 hpq F hv ζ hζ
      ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x)
  have h2 := ggKGTr_PhiFun_spec hK hσ hp hp5 hpq F hv ζ hζ x
  have h3 := hconj (ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ x)
      (ggKGTr_PhiFun hK hσ hp hp5 hpq F hv ζ hζ x).2
  rw [h1, h3, h2, canonicalRep_conj_rootDiagUnit]
  exact (congrArg (rootDiagUnit TwistTag.E6.tag)
    (ggKGTr_weylTuple_expTuple ζ hζ u x)).symm

private theorem ggKGTr_count
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    [NeZero p]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ u : WeylGroup TwistTag.E6.tag, u * u = 1 ∧
      (∀ e ∈ E, ggKGTr_Y F (w₀ * e * w₀⁻¹) =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u * ggKGTr_Y F e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹) ∧
      Nat.card {f : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) //
        ExcWeylOuter.torusMulAut TwistTag.E6.tag p u f = f} =
        p ^ (TwistTag.E6.tag.rank - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure K) 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
    exact charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨u, -, hconj_raw⟩ :=
    ggKGTwE6_normalizer_weyl hK hσ hp hp5 F (Or.inr ⟨hpq, hv⟩) hrefl.1
  have hconj : ∀ e ∈ E, ggKGTr_Y F (w₀ * e * w₀⁻¹) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u * ggKGTr_Y F e *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ := by
    intro e he
    rw [ggKGTr_Y_apply]
    exact hconj_raw e he
  have hu2 : u * u = 1 := by
    have hvv : ∀ e ∈ E,
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) * ggKGTr_Y F e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
            canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ =
          ggKGTr_Y F e := by
      intro e he
      have hmem : w₀ * e * w₀⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrefl.1 e).mp he
      calc (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
              canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) *
              ggKGTr_Y F e *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
                canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹
          = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u * ggKGTr_Y F e *
                (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ := by group
        _ = canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
              ggKGTr_Y F (w₀ * e * w₀⁻¹) *
              (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ := by
              rw [hconj e he]
        _ = ggKGTr_Y F (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹) :=
              (hconj (w₀ * e * w₀⁻¹) hmem).symm
        _ = ggKGTr_Y F e := by rw [hrefl.2.1 e he]
    refine ggKGTwE6_normalizer_faithful hK hσ hp hp5 F (Or.inr ⟨hpq, hv⟩)
      (u := u * u) fun e he => ?_
    obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) u u
    have hT : ggKGTr_Y F e ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      ((F.mem_iff e).1 he).2 |>.1
    have hcomm : k * ggKGTr_Y F e = ggKGTr_Y F e * k :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
        (torusGroup_le_diagonalGroup hT)
    have h1 := hvv e he
    rw [hk_eq] at h1
    calc canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u) * ggKGTr_Y F e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u))⁻¹
        = k⁻¹ * ((k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u)) *
            ggKGTr_Y F e *
            (k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u))⁻¹)
              * k := by
          group
      _ = k⁻¹ * ggKGTr_Y F e * k := by rw [h1]
      _ = ggKGTr_Y F e := by
          change k⁻¹ * ggKGTr_Y F e * k = ggKGTr_Y F e
          rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
    Nat.prime_two hp (by omega)
  let Phi := ggKGTr_Phi hK hσ hp hp5 hpq F hv ζ hζ
  have hcardE : Nat.card E = p ^ TwistTag.E6.tag.rank := by
    rw [Nat.card_congr Phi.symm, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hactPhi : ∀ x : Fin TwistTag.E6.tag.rank → ZMod p,
      (Phi ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x) :
          twistedE6RootGroup K σ) = w₀ * (Phi x : twistedE6RootGroup K σ) * w₀⁻¹ := by
    intro x
    apply ggKGTr_Y_injective F
    exact ggKGTr_PhiFun_action hK hσ hp hp5 hpq F hv ζ hζ u hconj x
  have hfixE : Nat.card {e : E // w₀ * (e : twistedE6RootGroup K σ) * w₀⁻¹ =
      (e : twistedE6RootGroup K σ)} =
      Nat.card {x : Fin TwistTag.E6.tag.rank → ZMod p //
        (ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Phi.symm fun e => ?_)
    have h := hactPhi (Phi.symm e)
    rw [Phi.apply_symm_apply] at h
    constructor
    · intro he
      apply Phi.injective
      apply Subtype.ext
      rw [h, he, Phi.apply_symm_apply]
    · intro hx
      rw [← h, hx, Phi.apply_symm_apply]
  have hcount : Nat.card {x : Fin TwistTag.E6.tag.rank → ZMod p //
        (ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)) *ᵥ x = x} =
      p ^ (TwistTag.E6.tag.rank - 1) := by
    have h3 := hrefl.2.2
    rw [hfixE, hcardE] at h3
    have hm1 : 1 ≤ TwistTag.E6.tag.rank := by decide
    have h4 : p ^ TwistTag.E6.tag.rank = p ^ (TwistTag.E6.tag.rank - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [h4] at h3
    exact Nat.eq_of_mul_eq_mul_right hp.pos h3
  have hMT : ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p)))ᵀ =
      (weylLatticeMatrix TwistTag.E6.tag u).map (Int.castRingHom (ZMod p)) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [ggKGTr_dualMat_eq_transpose u hu2, Matrix.transpose_apply]
  have hfix : Nat.card {f : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) //
      ExcWeylOuter.torusMulAut TwistTag.E6.tag p u f = f} =
      p ^ (TwistTag.E6.tag.rank - 1) := by
    rw [natCard_fix_torusMulAut_eq]
    rw [← hMT, ← ggKGTr_card_fix_transpose
      ((ggKGTr_dualMat u).map (Int.castRingHom (ZMod p))), hcount]
  exact ⟨u, hu2, hconj, hfix⟩

theorem ggKGTwE6_reflection_isRoot
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) (F : TwE6Frame K σ n p E) (hv : ExcIsLongest TwistTag.E6.tag F.v)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ ∀ e ∈ E,
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((w₀ * e * w₀⁻¹) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ) *
          (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (rootReflection γ))⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu2, hconj, hfix⟩ := ggKGTr_count hK hσ hp hp5 hpq F hv hrefl
  have hpred : ∀ f : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p),
      ExcWeylOuter.torusMulAut TwistTag.E6.tag p (1 : WeylGroup TwistTag.E6.tag) f = f := by
    intro f; simp
  have hu1 : u ≠ 1 := by
    intro h
    have hcard1 : Nat.card {f : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) //
        ExcWeylOuter.torusMulAut TwistTag.E6.tag p u f = f} =
        p ^ TwistTag.E6.tag.rank := by
      rw [h]
      have e : {f : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) //
          ExcWeylOuter.torusMulAut TwistTag.E6.tag p (1 : WeylGroup TwistTag.E6.tag) f = f} ≃
          Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) :=
        Equiv.ofBijective Subtype.val (by
          constructor
          · intro a b hab; exact Subtype.ext hab
          · intro f; exact ⟨⟨f, hpred f⟩, rfl⟩)
      rw [Nat.card_congr e, ggKGTr_card_multiplicative]
    have hpr : p ^ TwistTag.E6.tag.rank = p ^ (TwistTag.E6.tag.rank - 1) := by
      rw [← hcard1]; exact hfix
    have hlt : p ^ (TwistTag.E6.tag.rank - 1) < p ^ TwistTag.E6.tag.rank :=
      Nat.pow_lt_pow_right hp.one_lt (Nat.sub_lt (by decide) (by decide))
    exact (ne_of_lt hlt) hpr.symm
  obtain ⟨β, hβroot, hβeq⟩ :=
    exists_rootReflection_of_natCard_fix_torusMulAut (τ := TwistTag.E6.tag) (p := p)
      (hp2 := by omega) (hτ := fun i => by
        rw [show TwistTag.E6.tag.symmetrizer = 1 from rfl]; simp)
      (hr := by decide) hu2 hu1 hfix
  exact ⟨β, hβroot, fun e he => by
    rw [← ggKGTr_Y_apply F (w₀ * e * w₀⁻¹), ← ggKGTr_Y_apply F e]
    rw [hconj e he, hβeq]⟩

end CFSG.StandardType

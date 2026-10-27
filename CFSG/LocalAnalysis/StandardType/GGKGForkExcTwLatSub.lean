module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeInvol
public import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat1
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat2
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section AtFrame


private def ggKGTs_iota
    : Fin TwistTag.E6.tag.rank → Fin 4 := fun i => ggKGEp_iota i

private def ggKGTs_sec
    : Fin 4 → Fin TwistTag.E6.tag.rank := fun i => ggKGEp_sec i

private theorem ggKGTs_iota_phi
    (i : Fin TwistTag.E6.tag.rank) :
    ggKGTs_iota (TwistTag.E6.perm i) = ggKGTs_iota i := by
  fin_cases i <;> decide +kernel

private theorem ggKGTs_iota_sec
    (i : Fin 4) : ggKGTs_iota (ggKGTs_sec i) = i := by
  fin_cases i <;> decide +kernel

private theorem ggKGTs_eq_or_eq_perm_sec
    (i : Fin TwistTag.E6.tag.rank) :
    i = ggKGTs_sec (ggKGTs_iota i) ∨ i = TwistTag.E6.perm (ggKGTs_sec (ggKGTs_iota i)) := by
  fin_cases i <;> decide +kernel

private theorem ggKGTs_w0_isLongest :
    ExcIsLongest TwistTag.E6.tag (ggKGEp_w0 TwistTag.E6.tag) := by
  intro α hα hnn
  exact (IsRoot.height_neg_iff (IsRoot.smul hα (ggKGEp_w0 TwistTag.E6.tag))).1
    (ggKGEp_w0_reversesSigns_E6 α hα ((IsRoot.height_pos_iff hα).2 hnn))

private theorem ggKGTs_conj_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) :
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

private theorem ggKGTs_conj_mul
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (a b : twistedE6RootGroup K σ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((a * b : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (a : ModGL TwistTag.E6.tag K) * F.g0) *
        (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (b : ModGL TwistTag.E6.tag K) * F.g0) := by
  rw [Subgroup.coe_mul, map_mul]
  group

private theorem ggKGTs_conj_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((1 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 = 1 := by
  rw [Subgroup.coe_one, map_one]
  group

private theorem ggKGTs_hact_w_one
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (hv : F.v = 1)
    (hpq : p ∣ 2 ^ n - 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) :
    weylTuple F.v
        (fun i => Units.map F.Fr.toMonoidHom (ζ ^ y (ggKGTs_iota (TwistTag.E6.perm.symm i)))) =
      (fun j => ζ ^ y (ggKGTs_iota j)) := by
  have hb : ∀ j, (fun j => ζ ^ y (ggKGTs_iota j)) j ^ p = 1 := fun j =>
    ggKGEl_zetaPow_pow_eq_one ζ hζ (y (ggKGTs_iota j))
  exact ggKGTc_hact_w_one (b := fun j => ζ ^ y (ggKGTs_iota j)) F hv hpq hb (by rfl) (by rfl)

private noncomputable def ggKGTs_pick
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) : ↥E :=
  let b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := fun i => ζ ^ y (ggKGTs_iota i)
  let hb : ∀ i, b i ^ p = 1 := fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y (ggKGTs_iota i))
  let h := ggKGTc_exists_conj_of_hact hK hσ hp hp5 F hb (ggKGTs_hact_w_one F hv hpq ζ hζ y)
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

private theorem ggKGTs_pick_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ y : ↥E) :
          twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y (ggKGTs_iota i)) := by
  dsimp only [ggKGTs_pick]
  let b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ := fun i => ζ ^ y (ggKGTs_iota i)
  have hb : ∀ i, b i ^ p = 1 := fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y (ggKGTs_iota i))
  exact (Classical.choose_spec (ggKGTc_exists_conj_of_hact hK hσ hp hp5 F hb
    (ggKGTs_hact_w_one F hv hpq ζ hζ y))).2.symm

private noncomputable def ggKGTs_pi
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    (Fin 4 → ℤ) →+ Additive ↥E where
  toFun y := Additive.ofMul (ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ y)
  map_zero' := by
    change Additive.ofMul (ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ 0) =
      Additive.ofMul (1 : ↥E)
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGTs_conj_injective F
    dsimp only
    rw [ggKGTs_pick_spec, Subgroup.coe_one, ggKGTs_conj_one]
    simp only [Pi.zero_apply, zpow_zero, Pi.one_apply]
    exact rootDiagUnit_one
  map_add' y y' := by
    change Additive.ofMul (ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ (y + y')) =
      Additive.ofMul (ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ y *
        ggKGTs_pick hK hσ hp hp5 hpq F hv ζ hζ y')
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGTs_conj_injective F
    dsimp only
    rw [ggKGTs_pick_spec, Subgroup.coe_mul, ggKGTs_conj_mul, ggKGTs_pick_spec, ggKGTs_pick_spec]
    rw [← rootDiagUnit_mul]
    congr 1
    funext i
    simp [Pi.add_apply, zpow_add]

private theorem ggKGTs_pi_spec
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) :
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
      rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y (ggKGTs_iota i)) :=
  ggKGTs_pick_spec hK hσ hp hp5 hpq F hv ζ hζ y

private theorem ggKGTs_pi_surjective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Surjective (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro e
  let Ψ : ↥E →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    { toFun := fun x => F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0
      map_one' := ggKGTs_conj_one F
      map_mul' := fun a b => ggKGTs_conj_mul F (a : twistedE6RootGroup K σ)
        (b : twistedE6RootGroup K σ) }
  have he : (((Additive.toMul e : ↥E) : twistedE6RootGroup K σ)) ^ p = 1 :=
    ((F.mem_iff (Additive.toMul e : ↥E)).1 (Additive.toMul e).2).1
  have heT : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) :=
    ((F.mem_iff (Additive.toMul e : ↥E)).1 (Additive.toMul e).2).2
  have heG : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 ∈
      torusGroup TwistTag.E6.tag (AlgebraicClosure K) := (mem_twistedTorusOf.1 heT).1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heG
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : (rootDiagUnit TwistTag.E6.tag b) ^ p = 1 := by
      rw [← hb]
      change (Ψ (Additive.toMul e)) ^ p = 1
      rw [← map_pow, show (Additive.toMul e : ↥E) ^ p = 1 from Subtype.ext he, map_one]
    have hbp' : b ^ p = 1 := rootDiagUnit_injective
      (by rw [← rootDiagUnit_pow, h1, rootDiagUnit_one])
    intro i
    simpa using congrFun hbp' i
  have hbT : rootDiagUnit TwistTag.E6.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr) := hb ▸ heT
  have hfix_tw : twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr
        (rootDiagUnit TwistTag.E6.tag b) = rootDiagUnit TwistTag.E6.tag b := by
    have hmem := (mem_twistedTorusOf.1 hbT).2
    simpa [hv, canonicalRep_one] using hmem
  have hbfix : ∀ i : Fin TwistTag.E6.tag.rank, b (TwistTag.E6.perm i) = b i := by
    intro i
    have h := compat_of_twistHom_rootDiagUnit hfix_tw i
    rwa [ggKGTc_fr_eq_self F.Fr F.fr_eq (hbp i) hpq] at h
  choose y hy using fun i => ggKGEl_eq_zetaPow_of_pow_eq_one ζ hζ (hbp (ggKGTs_sec i))
  refine ⟨y, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply ggKGTs_conj_injective F
  dsimp only
  rw [ggKGTs_pi_spec, hb]
  congr 1
  funext i
  rcases ggKGTs_eq_or_eq_perm_sec i with h | h
  · rw [h, ggKGTs_iota_sec]
    exact (hy (ggKGTs_iota i)).symm
  · rw [h, hbfix, ggKGTs_iota_phi, ggKGTs_iota_sec]
    exact (hy (ggKGTs_iota i)).symm

private theorem ggKGTs_normalizer_data
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ v : WeylGroup TwistTag.E6.tag, v * ggKGEp_w0 TwistTag.E6.tag = ggKGEp_w0 TwistTag.E6.tag * v ∧
      v * v = 1 ∧
      ∀ y : Fin 4 → ℤ,
        w₀ * ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
            twistedE6RootGroup K σ) * w₀⁻¹ =
          ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
            ((ggKGEp_mat4 v).mulVec y)) : ↥E) : twistedE6RootGroup K σ) := by
  obtain ⟨u, hcomm, hconj⟩ :=
    ggKGTwE6_normalizer_weyl hK hσ hp hp5 F (Or.inl ⟨hpq, hv⟩) hrefl.1
  let nu : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u
  let yhat : twistedE6RootGroup K σ → ModGL TwistTag.E6.tag (AlgebraicClosure K) := fun e =>
    F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (e : ModGL TwistTag.E6.tag K) * F.g0
  have hucomm : u * ggKGEp_w0 TwistTag.E6.tag = ggKGEp_w0 TwistTag.E6.tag * u :=
    hcomm hpq (ggKGEp_w0 TwistTag.E6.tag) (ggKGTs_w0_isLongest)
  refine ⟨u, hucomm, ?_, fun y => ?_⟩
  · have hvv : ∀ e ∈ E, (nu * nu) * yhat e * (nu * nu)⁻¹ = yhat e := by
      intro e he
      have hmem : w₀ * e * w₀⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrefl.1 e).mp he
      calc (nu * nu) * yhat e * (nu * nu)⁻¹
          = nu * (nu * yhat e * nu⁻¹) * nu⁻¹ := by group
        _ = nu * yhat (w₀ * e * w₀⁻¹) * nu⁻¹ := by rw [← hconj e he]
        _ = yhat (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹) := (hconj (w₀ * e * w₀⁻¹) hmem).symm
        _ = yhat e := by rw [hrefl.2.1 e he]
    refine ggKGTwE6_normalizer_faithful hK hσ hp hp5 F (Or.inl ⟨hpq, hv⟩) fun e he => ?_
    obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) u u
    have hT : yhat e ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) :=
      ((F.mem_iff e).1 he).2 |>.1
    have hcomm' : k * yhat e = yhat e * k :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
        (torusGroup_le_diagonalGroup hT)
    have h1 := hvv e he
    rw [hk_eq] at h1
    calc canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u) * yhat e *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u))⁻¹
        = k⁻¹ * ((k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (u * u)) *
            yhat e *
            (k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
              (u * u))⁻¹) * k :=
          by group
      _ = k⁻¹ * yhat e * k := by rw [h1]
      _ = yhat e := by
          change k⁻¹ * yhat e * k = yhat e
          rw [mul_assoc, ← hcomm', ← mul_assoc, inv_mul_cancel, one_mul]
  · have he : ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
        twistedE6RootGroup K σ) ∈ E :=
      (Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y)).2
    have h1 := hconj _ he
    rw [ggKGTs_pi_spec hK hσ hp hp5 hpq F hv ζ hζ y, canonicalRep_conj_rootDiagUnit,
      ggKGEl_weylTuple_zeta] at h1
    have h2 : (ggKGEl_mat u).mulVec (fun i => y (ggKGTs_iota i)) =
        fun i => ((ggKGEp_mat4 u).mulVec y) (ggKGTs_iota i) :=
      (ggKGEp_mat4_io hucomm y).symm
    rw [h2] at h1
    change _ = rootDiagUnit TwistTag.E6.tag
      (fun i => ζ ^ ((ggKGEp_mat4 u).mulVec y) (ggKGTs_iota i)) at h1
    rw [← ggKGTs_pi_spec hK hσ hp hp5 hpq F hv ζ hζ] at h1
    exact ggKGTs_conj_injective F h1

private def ggKGTs_liftZ
    {p : ℕ} (x : Fin 4 → ZMod p) : Fin 4 → ℤ :=
  fun i => ((x i).val : ℤ)

private noncomputable def ggKGTs_modAct
    {p : ℕ} (V : WeylGroup Tag.E6) (x : Fin 4 → ZMod p) :
    Fin 4 → ZMod p :=
  ((ggKGEp_mat4 V).map (Int.castRingHom (ZMod p))).mulVec x

private theorem ggKGTs_pi_eq_one_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) :
    Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) = 1 ↔
      ∀ i, (y i : ZMod p) = 0 := by
  constructor
  · intro h
    have h1 : rootDiagUnit TwistTag.E6.tag (fun i => ζ ^ y (ggKGTs_iota i)) = 1 := by
      have h2 : F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
            twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 = 1 := by
        rw [h]
        exact ggKGTs_conj_one F
      rwa [ggKGTs_pi_spec hK hσ hp hp5 hpq F hv ζ hζ] at h2
    have h3 : (fun i => ζ ^ y (ggKGTs_iota i)) = 1 :=
      rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
    intro i
    have h4 : ζ ^ (y i) = 1 := by
      have := congrFun h3 (ggKGTs_sec i)
      simpa [ggKGTs_iota_sec] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mpr ((hζ.zpow_eq_one_iff_dvd (y i)).1 h4)
  · intro h
    apply Subtype.ext
    apply ggKGTs_conj_injective F
    dsimp only
    rw [ggKGTs_pi_spec hK hσ hp hp5 hpq F hv ζ hζ, Subgroup.coe_one, ggKGTs_conj_one]
    rw [← rootDiagUnit_one]
    congr 1
    funext i
    rw [Pi.one_apply]
    exact (hζ.zpow_eq_one_iff_dvd (y (ggKGTs_iota i))).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (y (ggKGTs_iota i)) p).mp (h (ggKGTs_iota i)))

private theorem ggKGTs_pi_eq_zero_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin 4 → ℤ) :
    ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y = 0 ↔ ∀ i, (y i : ZMod p) = 0 := by
  rw [show (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y = 0) ↔
      (Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) = 1) from
    ⟨fun h => by rw [h]; rfl, fun h => Additive.toMul.injective (by rw [h]; rfl)⟩]
  exact ggKGTs_pi_eq_one_iff hK hσ hp hp5 hpq F hv ζ hζ y

private theorem ggKGTs_pi_eq_iff
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y y' : Fin 4 → ℤ) :
    ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y =
        ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y' ↔
      ∀ i, (y i : ZMod p) = (y' i : ZMod p) := by
  rw [← sub_eq_zero (a := ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y)]
  rw [show ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y -
        ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y' =
      ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ (y - y') from (map_sub _ _ _).symm]
  rw [ggKGTs_pi_eq_zero_iff hK hσ hp hp5 hpq F hv ζ hζ]
  constructor <;> intro h i
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this

private theorem ggKGTs_modAct_eq
    {p : ℕ} [NeZero p] (V : WeylGroup Tag.E6)
    (x : Fin 4 → ZMod p) (i : Fin 4) :
    (ggKGTs_modAct V x i : ZMod p) =
      (((ggKGEp_mat4 V).mulVec (ggKGTs_liftZ x)) i : ZMod p) := by
  simp only [ggKGTs_modAct, ggKGTs_liftZ, Matrix.mulVec, Matrix.map_apply, dotProduct]
  push_cast
  exact Finset.sum_congr (M := ZMod p) rfl fun j _ => by simp [ZMod.natCast_zmod_val]

private noncomputable def ggKGTs_pibar
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (x : Fin 4 → ZMod p) : ↥E :=
  Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTs_liftZ x))

private theorem ggKGTs_pibar_bijective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Bijective (ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro x x' h
    have h' : ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTs_liftZ x) =
        ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ (ggKGTs_liftZ x') :=
      Additive.toMul.injective h
    have h2 := (ggKGTs_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ _ _).1 h'
    funext i
    have := h2 i
    simpa [ggKGTs_liftZ] using this
  · intro e
    obtain ⟨y, hy⟩ :=
      ggKGTs_pi_surjective hK hσ hp hp5 hpq F hv ζ hζ (Additive.ofMul e)
    refine ⟨fun i => (y i : ZMod p), ?_⟩
    have h2 : ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
          (ggKGTs_liftZ (fun i => (y i : ZMod p))) =
        ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y := by
      rw [ggKGTs_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ]
      intro i
      simp only [ggKGTs_liftZ]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i : ZMod p)
    show Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
      (ggKGTs_liftZ (fun i => (y i : ZMod p)))) = e
    rw [h2, hy]
    rfl

private theorem ggKGTs_pibar_modAct
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ}
    (hN : w₀ ∈ Subgroup.normalizer (E : Set (twistedE6RootGroup K σ)))
    (V : WeylGroup Tag.E6)
    (hactV : ∀ y : Fin 4 → ℤ,
      w₀ * ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹ =
        ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
          ((ggKGEp_mat4 V).mulVec y)) : ↥E) : twistedE6RootGroup K σ))
    (x : Fin 4 → ZMod p) :
    ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ (ggKGTs_modAct V x) =
      ⟨w₀ * ((ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ x : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹,
        (Subgroup.mem_normalizer_iff.mp hN _).mp
          (ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ x).2⟩ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  dsimp only [ggKGTs_pibar]
  have h1 : ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
        (ggKGTs_liftZ (ggKGTs_modAct V x)) =
      ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
        ((ggKGEp_mat4 V).mulVec (ggKGTs_liftZ x)) := by
    rw [ggKGTs_pi_eq_iff hK hσ hp hp5 hpq F hv ζ hζ]
    intro i
    simpa [ggKGTs_liftZ] using ggKGTs_modAct_eq V x i
  rw [h1]
  exact (hactV (ggKGTs_liftZ x)).symm

private theorem ggKGTs_fix_count
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    {w₀ : twistedE6RootGroup K σ} (hrefl : GGKGIsReflAt p E w₀) (V : WeylGroup Tag.E6)
    (hactV : ∀ y : Fin 4 → ℤ,
      w₀ * ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ y) : ↥E) :
          twistedE6RootGroup K σ) * w₀⁻¹ =
        ((Additive.toMul (ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ
          ((ggKGEp_mat4 V).mulVec y)) : ↥E) : twistedE6RootGroup K σ)) :
    Nat.card {x : Fin 4 → ZMod p //
      ((ggKGEp_mat4 V).map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (4 - 1) := by
  change Nat.card {x : Fin 4 → ZMod p // ggKGTs_modAct V x = x} = p ^ (4 - 1)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbij := ggKGTs_pibar_bijective hK hσ hp hp5 hpq F hv ζ hζ
  let eE : (Fin 4 → ZMod p) ≃ ↥E := Equiv.ofBijective _ hbij
  have heE : ∀ x, eE x = ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ x := fun x => rfl
  have hcardE : Nat.card ↥E = p ^ 4 := by
    rw [← Nat.card_congr eE]
    simp [Nat.card_fun, Nat.card_zmod]
  have hfixeq : Nat.card {x : Fin 4 → ZMod p // ggKGTs_modAct V x = x} =
      Nat.card {e : ↥E // w₀ * ((e : ↥E) : twistedE6RootGroup K σ) * w₀⁻¹ =
        ((e : ↥E) : twistedE6RootGroup K σ)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv eE fun x => ?_)
    rw [heE x]
    have hmod := ggKGTs_pibar_modAct hK hσ hp hp5 hpq F hv ζ hζ hrefl.1 V hactV x
    constructor
    · intro hx
      rw [hx] at hmod
      exact (Subtype.ext_iff.mp hmod).symm
    · intro hx
      have h2 : ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ (ggKGTs_modAct V x) =
          ggKGTs_pibar hK hσ hp hp5 hpq F hv ζ hζ x := by
        rw [hmod]
        exact Subtype.ext hx
      exact hbij.1 h2
  have h3 := hrefl.2.2
  rw [← hfixeq, hcardE] at h3
  have h4 : p ^ 4 = p ^ (4 - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by norm_num : 1 ≤ 4)]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hp.pos h3

theorem ggKGTwE6_latticeAt_sub
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ n - 1) (F : TwE6Frame K σ n p E)
    (hv : F.v = 1) : GGKGLatticeAt p E := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ζu, hζu⟩ :=
    CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
      (by norm_num) hp (by omega)
  let ζ : (AlgebraicClosure K)ˣ := ζu
  have hζ : IsPrimitiveRoot ζ p := hζu
  refine ⟨4, ggKGEp_Q4, ggKGTs_pi hK hσ hp hp5 hpq F hv ζ hζ, ggKGEp_Q4_form,
    ggKGTs_pi_surjective hK hσ hp hp5 hpq F hv ζ hζ, ?_⟩
  intro w₀ hrefl
  obtain ⟨v, hvcomm, hv2, hactV⟩ :=
    ggKGTs_normalizer_data hK hσ hp hp5 hpq F hv ζ hζ hrefl
  obtain ⟨w, hwroot, hwformula⟩ :=
    ggKGLat_involution_isRoot hp (by omega) ggKGEp_Q4_form (ggKGEp_mat4 v)
      (ggKGEp_mat4_invariant hvcomm) (ggKGEp_mat4_mul_self hvcomm hv2)
      (ggKGTs_fix_count hK hσ hp hp5 hpq F hv ζ hζ hrefl v hactV) (by norm_num)
  refine ⟨w, hwroot, fun y => ?_⟩
  rw [← hwformula y]
  exact hactV y

end AtFrame

end CFSG.StandardType

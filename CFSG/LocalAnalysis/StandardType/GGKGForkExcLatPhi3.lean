module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLatPhi2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGEp_normalizer_data
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    {w₀ : adjointGroup Tag.E6 K} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ v : WeylGroup Tag.E6, v ∈ Subgroup.centralizer ({F.w} : Set (WeylGroup Tag.E6)) ∧
      v * v = 1 ∧
      ∀ y : Fin 4 → ℤ,
        w₀ * ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
            adjointGroup Tag.E6 K) * w₀⁻¹ =
          ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
            ((ggKGEp_mat4 v).mulVec y)) : ↥E) : adjointGroup Tag.E6 K) := by
  obtain ⟨v, hv, hconj⟩ :=
    ggKGExc_normalizer_weyl (Or.inl rfl) hp (by omega) (fun _ => hp5) F (Or.inr ⟨hpq, hlong⟩) hrefl.1
  let nv : ModGL Tag.E6 (AlgebraicClosure K) := canonicalRep (coxeterSystem Tag.E6)
    (AlgebraicClosure K) v
  let yhat : adjointGroup Tag.E6 K → ModGL Tag.E6 (AlgebraicClosure K) := fun e =>
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.E6 K) * F.D.g0
  have hvcomm : v * ggKGEp_w0 .E6 = ggKGEp_w0 .E6 * v := by
    have h := (Subgroup.mem_centralizer_iff.mp hv) F.w (Set.mem_singleton F.w)
    rw [ggKGEp_eq_w0_of_longest hlong] at h
    exact h.symm
  refine ⟨v, hv, ?_, fun y => ?_⟩
  · have hvv : ∀ e ∈ E, (nv * nv) * yhat e * (nv * nv)⁻¹ = yhat e := by
      intro e he
      have hmem : w₀ * e * w₀⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrefl.1 e).mp he
      calc (nv * nv) * yhat e * (nv * nv)⁻¹
          = nv * (nv * yhat e * nv⁻¹) * nv⁻¹ := by group
        _ = nv * yhat (w₀ * e * w₀⁻¹) * nv⁻¹ := by rw [← hconj e he]
        _ = yhat (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹) := (hconj (w₀ * e * w₀⁻¹) hmem).symm
        _ = yhat e := by rw [hrefl.2.1 e he]
    refine ggKGExc_normalizer_faithful (Or.inl rfl) hp (by omega) (fun _ => hp5) F (Or.inr ⟨hpq, hlong⟩)
      fun e he => ?_
    obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) v v
    have hT : yhat e ∈ torusGroup Tag.E6 (AlgebraicClosure K) := ((F.mem_iff e).1 he).2 |>.1
    have hcomm : k * yhat e = yhat e * k :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
        (torusGroup_le_diagonalGroup hT)
    have h1 := hvv e he
    rw [hk_eq] at h1
    calc canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (v * v) * yhat e *
          (canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (v * v))⁻¹
        = k⁻¹ * ((k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (v * v)) *
            yhat e *
            (k * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) (v * v))⁻¹) * k :=
          by group
      _ = k⁻¹ * yhat e * k := by rw [h1]
      _ = yhat e := by
          change k⁻¹ * yhat e * k = yhat e
          rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · have he : ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
        adjointGroup Tag.E6 K) ∈ E :=
      (Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y)).2
    have h1 := hconj _ he
    rw [ggKGEp_pi_spec hp hp5 F hFr hΦ ζ hζ hlong hpq, canonicalRep_conj_rootDiagUnit,
      ggKGEl_weylTuple_zeta] at h1
    have h2 : (ggKGEl_mat v).mulVec (fun i => y (ggKGEp_iota i)) =
        fun i => ((ggKGEp_mat4 v).mulVec y) (ggKGEp_iota i) :=
      (ggKGEp_mat4_io hvcomm y).symm
    rw [h2] at h1
    change _ = rootDiagUnit Tag.E6
      (fun i => ζ ^ ((ggKGEp_mat4 v).mulVec y) (ggKGEp_iota i)) at h1
    rw [← ggKGEp_pi_spec hp hp5 F hFr hΦ ζ hζ hlong hpq] at h1
    exact ggKGEl_conj_injective F h1

def ggKGEp_liftZ {p : ℕ} (x : Fin 4 → ZMod p) : Fin 4 → ℤ :=
  fun i => ((x i).val : ℤ)

noncomputable def ggKGEp_modAct {p : ℕ} (V : WeylGroup Tag.E6) (x : Fin 4 → ZMod p) :
    Fin 4 → ZMod p :=
  ((ggKGEp_mat4 V).map (Int.castRingHom (ZMod p))).mulVec x

theorem ggKGEp_pi_eq_one_iff
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) (y : Fin 4 → ℤ) :
    Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) = 1 ↔
      ∀ i, (y i : ZMod p) = 0 := by
  constructor
  · intro h
    have h1 : rootDiagUnit Tag.E6 (fun i => ζ ^ y (ggKGEp_iota i)) = 1 := by
      have h2 : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
            adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * F.D.g0 = 1 := by
        rw [h]
        exact ggKGEl_conj_one F
      rwa [ggKGEp_pi_spec hp hp5 F hFr hΦ ζ hζ hlong hpq] at h2
    have h3 : (fun i => ζ ^ y (ggKGEp_iota i)) = 1 :=
      rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
    intro i
    have h4 : ζ ^ (y i) = 1 := by
      have := congrFun h3 (ggKGEp_sec i)
      simpa [ggKGEp_iota_sec] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mpr ((hζ.zpow_eq_one_iff_dvd (y i)).1 h4)
  · intro h
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEp_pi_spec hp hp5 F hFr hΦ ζ hζ hlong hpq, Subgroup.coe_one, ggKGEl_conj_one]
    rw [← rootDiagUnit_one]
    congr 1
    funext i
    rw [Pi.one_apply]
    exact (hζ.zpow_eq_one_iff_dvd (y (ggKGEp_iota i))).2
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (y (ggKGEp_iota i)) p).mp (h (ggKGEp_iota i)))

theorem ggKGEp_pi_eq_zero_iff
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) (y : Fin 4 → ℤ) :
    ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y = 0 ↔ ∀ i, (y i : ZMod p) = 0 := by
  rw [show (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y = 0) ↔
      (Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) = 1) from
    ⟨fun h => by rw [h]; rfl, fun h => Additive.toMul.injective (by rw [h]; rfl)⟩]
  exact ggKGEp_pi_eq_one_iff hp hp5 F hFr hΦ ζ hζ hlong hpq y

theorem ggKGEp_pi_eq_iff
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) (y y' : Fin 4 → ℤ) :
    ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y =
        ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y' ↔
      ∀ i, (y i : ZMod p) = (y' i : ZMod p) := by
  rw [← sub_eq_zero (a := ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y)]
  rw [show ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y -
        ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y' =
      ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq (y - y') from (map_sub _ _ _).symm]
  rw [ggKGEp_pi_eq_zero_iff hp hp5 F hFr hΦ ζ hζ hlong hpq]
  constructor <;> intro h i
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this

theorem ggKGEp_modAct_eq {p : ℕ} [NeZero p] (V : WeylGroup Tag.E6) (x : Fin 4 → ZMod p)
    (i : Fin 4) :
    (ggKGEp_modAct V x i : ZMod p) =
      (((ggKGEp_mat4 V).mulVec (ggKGEp_liftZ x)) i : ZMod p) := by
  simp only [ggKGEp_modAct, ggKGEp_liftZ, Matrix.mulVec, Matrix.map_apply, dotProduct]
  push_cast
  exact Finset.sum_congr (M := ZMod p) rfl fun j _ => by simp [ZMod.natCast_zmod_val]

noncomputable def ggKGEp_pibar
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    (x : Fin 4 → ZMod p) : ↥E :=
  Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_liftZ x))

theorem ggKGEp_pibar_bijective
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) :
    Function.Bijective (ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro x x' h
    have h' : ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_liftZ x) =
        ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_liftZ x') :=
      Additive.toMul.injective h
    have h2 := (ggKGEp_pi_eq_iff hp hp5 F hFr hΦ ζ hζ hlong hpq _ _).1 h'
    funext i
    have := h2 i
    simpa [ggKGEp_liftZ] using this
  · intro e
    obtain ⟨y, hy⟩ := ggKGEp_pi_surjective hp hp5 F hFr hΦ ζ hζ hlong hpq (Additive.ofMul e)
    refine ⟨fun i => (y i : ZMod p), ?_⟩
    have h2 : ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
          (ggKGEp_liftZ (fun i => (y i : ZMod p))) =
        ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y := by
      rw [ggKGEp_pi_eq_iff hp hp5 F hFr hΦ ζ hζ hlong hpq]
      intro i
      simp only [ggKGEp_liftZ]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i : ZMod p)
    show Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
      (ggKGEp_liftZ (fun i => (y i : ZMod p)))) = e
    rw [h2, hy]
    rfl

theorem ggKGEp_pibar_modAct
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    {w₀ : adjointGroup Tag.E6 K} (hN : w₀ ∈ Subgroup.normalizer (E : Set (adjointGroup Tag.E6 K)))
    (V : WeylGroup Tag.E6)
    (hactV : ∀ y : Fin 4 → ℤ,
      w₀ * ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
          adjointGroup Tag.E6 K) * w₀⁻¹ =
        ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
          ((ggKGEp_mat4 V).mulVec y)) : ↥E) : adjointGroup Tag.E6 K))
    (x : Fin 4 → ZMod p) :
    ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_modAct V x) =
      ⟨w₀ * ((ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq x : ↥E) :
          adjointGroup Tag.E6 K) * w₀⁻¹,
        (Subgroup.mem_normalizer_iff.mp hN _).mp
          (ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq x).2⟩ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  dsimp only [ggKGEp_pibar]
  have h1 : ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_liftZ (ggKGEp_modAct V x)) =
      ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
        ((ggKGEp_mat4 V).mulVec (ggKGEp_liftZ x)) := by
    rw [ggKGEp_pi_eq_iff hp hp5 F hFr hΦ ζ hζ hlong hpq]
    intro i
    simpa [ggKGEp_liftZ] using ggKGEp_modAct_eq V x i
  rw [h1]
  exact (hactV (ggKGEp_liftZ x)).symm

theorem ggKGEp_fix_count
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    {w₀ : adjointGroup Tag.E6 K} (hrefl : GGKGIsReflAt p E w₀) (V : WeylGroup Tag.E6)
    (hactV : ∀ y : Fin 4 → ℤ,
      w₀ * ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
          adjointGroup Tag.E6 K) * w₀⁻¹ =
        ((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq
          ((ggKGEp_mat4 V).mulVec y)) : ↥E) : adjointGroup Tag.E6 K)) :
    Nat.card {x : Fin 4 → ZMod p //
      ((ggKGEp_mat4 V).map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (4 - 1) := by
  change Nat.card {x : Fin 4 → ZMod p // ggKGEp_modAct V x = x} = p ^ (4 - 1)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hbij := ggKGEp_pibar_bijective hp hp5 F hFr hΦ ζ hζ hlong hpq
  let eE : (Fin 4 → ZMod p) ≃ ↥E := Equiv.ofBijective _ hbij
  have heE : ∀ x, eE x = ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq x := fun x => rfl
  have hcardE : Nat.card ↥E = p ^ 4 := by
    rw [← Nat.card_congr eE]
    simp [Nat.card_fun, Nat.card_zmod]
  have hfixeq : Nat.card {x : Fin 4 → ZMod p // ggKGEp_modAct V x = x} =
      Nat.card {e : ↥E // w₀ * ((e : ↥E) : adjointGroup Tag.E6 K) * w₀⁻¹ =
        ((e : ↥E) : adjointGroup Tag.E6 K)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv eE fun x => ?_)
    rw [heE x]
    have hmod := ggKGEp_pibar_modAct hp hp5 F hFr hΦ ζ hζ hlong hpq hrefl.1 V hactV x
    constructor
    · intro hx
      rw [hx] at hmod
      exact (Subtype.ext_iff.mp hmod).symm
    · intro hx
      have h2 : ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq (ggKGEp_modAct V x) =
          ggKGEp_pibar hp hp5 F hFr hΦ ζ hζ hlong hpq x := by
        rw [hmod]
        exact Subtype.ext hx
      exact hbij.1 h2
  have h3 := hrefl.2.2
  rw [← hfixeq, hcardE] at h3
  have h4 : p ^ 4 = p ^ (4 - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel (by norm_num : 1 ≤ 4)]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hp.pos h3

end CFSG.StandardType

end

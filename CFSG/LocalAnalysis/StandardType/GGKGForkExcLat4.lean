module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat3
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem ggKGEl_normalizer_data
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : ExcFrame τ K p E)
    (hw : (p ∣ Nat.card K - 1 ∧ F.w = 1) ∨ (p ∣ Nat.card K + 1 ∧ ExcIsLongest τ F.w))
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    {w₀ : adjointGroup τ K} (hrefl : GGKGIsReflAt p E w₀) :
    ∃ v : WeylGroup τ, v ∈ Subgroup.centralizer ({F.w} : Set (WeylGroup τ)) ∧ v * v = 1 ∧
      ∀ y : Fin τ.rank → ℤ,
        w₀ * ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) :
            adjointGroup τ K) * w₀⁻¹ =
          ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact
            ((ggKGEl_mat v).mulVec y)) : ↥E) : adjointGroup τ K) := by
  obtain ⟨v, hv, hconj⟩ := ggKGExc_normalizer_weyl hτ hp (by omega) (fun _ => hp5) F hw hrefl.1
  let nv : ModGL τ (AlgebraicClosure K) := canonicalRep (coxeterSystem τ) (AlgebraicClosure K) v
  let yhat : adjointGroup τ K → ModGL τ (AlgebraicClosure K) := fun e =>
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0
  refine ⟨v, hv, ?_, fun y => ?_⟩
  · have hvv : ∀ e ∈ E, (nv * nv) * yhat e * (nv * nv)⁻¹ = yhat e := by
      intro e he
      have hmem : w₀ * e * w₀⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hrefl.1 e).mp he
      calc (nv * nv) * yhat e * (nv * nv)⁻¹
          = nv * (nv * yhat e * nv⁻¹) * nv⁻¹ := by group
        _ = nv * yhat (w₀ * e * w₀⁻¹) * nv⁻¹ := by rw [← hconj e he]
        _ = yhat (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹) := (hconj (w₀ * e * w₀⁻¹) hmem).symm
        _ = yhat e := by rw [hrefl.2.1 e he]
    refine ggKGExc_normalizer_faithful hτ hp (by omega) (fun _ => hp5) F hw fun e he => ?_
    obtain ⟨k, hk, hk_eq⟩ := canonicalRep_mul_mem (R := AlgebraicClosure K) v v
    have hT : yhat e ∈ torusGroup τ (AlgebraicClosure K) := ((F.mem_iff e).1 he).2 |>.1
    have hcomm : k * yhat e = yhat e * k :=
      mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hk)
        (torusGroup_le_diagonalGroup hT)
    have h1 := hvv e he
    rw [hk_eq] at h1
    calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v * v) * yhat e *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v * v))⁻¹
        = k⁻¹ * ((k * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v * v)) * yhat e *
            (k * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (v * v))⁻¹) * k := by group
      _ = k⁻¹ * yhat e * k := by rw [h1]
      _ = yhat e := by
          change k⁻¹ * yhat e * k = yhat e
          rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · have he : ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) :
        adjointGroup τ K) ∈ E := (Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y)).2
    have h1 := hconj _ he
    rw [ggKGEl_pi_spec hp hp5 hτ F hΦ ζ hζ hact, canonicalRep_conj_rootDiagUnit,
      ggKGEl_weylTuple_zeta] at h1
    rw [← ggKGEl_pi_spec hp hp5 hτ F hΦ ζ hζ hact] at h1
    exact ggKGEl_conj_injective F h1

def ggKGEl_liftZ {τ : Tag} {p : ℕ} (x : Fin τ.rank → ZMod p) : Fin τ.rank → ℤ :=
  fun i => ((x i).val : ℤ)

noncomputable def ggKGEl_modAct {τ : Tag} {p : ℕ} (V : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    Fin τ.rank → ZMod p :=
  ((ggKGEl_mat V).map (Int.castRingHom (ZMod p))).mulVec x

theorem ggKGEl_pi_eq_one_iff
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y : Fin τ.rank → ℤ) :
    Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) = 1 ↔
      ∀ i, (y i : ZMod p) = 0 := by
  constructor
  · intro h
    have h1 : rootDiagUnit τ (fun i => ζ ^ y i) = 1 := by
      have h2 : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) :
            adjointGroup τ K) : ModGL τ K) * F.D.g0 = 1 := by
        rw [h]
        exact ggKGEl_conj_one F
      rwa [ggKGEl_pi_spec hp hp5 hτ F hΦ ζ hζ hact] at h2
    have h3 : (fun i => ζ ^ y i) = 1 := rootDiagUnit_injective (by rw [h1, rootDiagUnit_one])
    intro i
    have h4 : ζ ^ (y i) = 1 := by
      have := congrFun h3 i
      rwa [Pi.one_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mpr ((hζ.zpow_eq_one_iff_dvd (y i)).1 h4)
  · intro h
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEl_pi_spec hp hp5 hτ F hΦ ζ hζ hact, Subgroup.coe_one, ggKGEl_conj_one]
    rw [← rootDiagUnit_one]
    congr 1
    funext i
    rw [Pi.one_apply]
    exact (hζ.zpow_eq_one_iff_dvd (y i)).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd (y i) p).mp (h i))

theorem ggKGEl_pi_eq_zero_iff
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y : Fin τ.rank → ℤ) :
    ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y = 0 ↔ ∀ i, (y i : ZMod p) = 0 := by
  rw [show (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y = 0) ↔
      (Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) = 1) from
    ⟨fun h => by rw [h]; rfl, fun h => Additive.toMul.injective (by rw [h]; rfl)⟩]
  exact ggKGEl_pi_eq_one_iff hτ hp hp5 F hΦ ζ hζ hact y

theorem ggKGEl_pi_eq_iff
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (y y' : Fin τ.rank → ℤ) :
    ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y = ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y' ↔
      ∀ i, (y i : ZMod p) = (y' i : ZMod p) := by
  rw [← sub_eq_zero (a := ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y)]
  rw [show ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y - ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y' =
      ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (y - y') from (map_sub _ _ _).symm]
  rw [ggKGEl_pi_eq_zero_iff hp hp5 hτ F hΦ ζ hζ hact]
  constructor <;> intro h i
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this
  · have := h i
    simpa only [Pi.sub_apply, Int.cast_sub, sub_eq_zero] using this


theorem ggKGEl_modAct_eq {τ : Tag} {p : ℕ} [NeZero p] (V : WeylGroup τ) (x : Fin τ.rank → ZMod p)
    (i : Fin τ.rank) :
    (ggKGEl_modAct V x i : ZMod p) =
      (((ggKGEl_mat V).mulVec (ggKGEl_liftZ x)) i : ZMod p) := by
  simp only [ggKGEl_modAct, ggKGEl_liftZ, Matrix.mulVec, Matrix.map_apply, dotProduct]
  push_cast
  exact Finset.sum_congr (M := ZMod p) rfl fun j _ => by simp [ZMod.natCast_zmod_val]

noncomputable def ggKGEl_pibar
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    (x : Fin τ.rank → ZMod p) : ↥E :=
  Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ x))

theorem ggKGEl_pibar_bijective
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i)) :
    Function.Bijective (ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro x x' h
    have h' : ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ x) =
        ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ x') :=
      Additive.toMul.injective h
    have h2 := (ggKGEl_pi_eq_iff hτ hp hp5 F hΦ ζ hζ hact _ _).1 h'
    funext i
    have := h2 i
    simpa [ggKGEl_liftZ] using this
  · intro e
    obtain ⟨y, hy⟩ := ggKGEl_pi_surjective hp hp5 hτ F hΦ ζ hζ hact (Additive.ofMul e)
    refine ⟨fun i => (y i : ZMod p), ?_⟩
    have h2 : ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ (fun i => (y i : ZMod p))) =
        ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y := by
      rw [ggKGEl_pi_eq_iff hτ hp hp5 F hΦ ζ hζ hact]
      intro i
      simp only [ggKGEl_liftZ]
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i : ZMod p)
    show Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ (fun i => (y i : ZMod p)))) = e
    rw [h2, hy]
    rfl

theorem ggKGEl_pibar_modAct
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    {w₀ : adjointGroup τ K} (hN : w₀ ∈ Subgroup.normalizer (E : Set (adjointGroup τ K)))
    (V : WeylGroup τ)
    (hactV : ∀ y : Fin τ.rank → ℤ,
      w₀ * ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) : adjointGroup τ K) *
          w₀⁻¹ =
        ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact ((ggKGEl_mat V).mulVec y)) :
          ↥E) : adjointGroup τ K))
    (x : Fin τ.rank → ZMod p) :
    ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_modAct V x) =
      ⟨w₀ * ((ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact x : ↥E) : adjointGroup τ K) * w₀⁻¹,
        (Subgroup.mem_normalizer_iff.mp hN _).mp
          (ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact x).2⟩ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Subtype.ext
  dsimp only [ggKGEl_pibar]
  have h1 : ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_liftZ (ggKGEl_modAct V x)) =
      ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact ((ggKGEl_mat V).mulVec (ggKGEl_liftZ x)) := by
    rw [ggKGEl_pi_eq_iff hτ hp hp5 F hΦ ζ hζ hact]
    intro i
    simpa [ggKGEl_liftZ] using ggKGEl_modAct_eq V x i
  rw [h1]
  exact (hactV (ggKGEl_liftZ x)).symm


theorem ggKGEl_fix_count
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (hp : p.Prime) (hp5 : 5 ≤ p)
    (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hact : ∀ y : Fin τ.rank → ℤ,
      weylTuple F.w (fun i => Units.map Fr.toMonoidHom (ζ ^ y i)) = (fun i => ζ ^ y i))
    {w₀ : adjointGroup τ K} (hrefl : GGKGIsReflAt p E w₀) (V : WeylGroup τ)
    (hactV : ∀ y : Fin τ.rank → ℤ,
      w₀ * ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact y) : ↥E) : adjointGroup τ K) *
          w₀⁻¹ =
        ((Additive.toMul (ggKGEl_pi hp hp5 hτ F hΦ ζ hζ hact ((ggKGEl_mat V).mulVec y)) :
          ↥E) : adjointGroup τ K)) :
    Nat.card {x : Fin τ.rank → ZMod p //
      ((ggKGEl_mat V).map (Int.castRingHom (ZMod p))).mulVec x = x} = p ^ (τ.rank - 1) := by
  change Nat.card {x : Fin τ.rank → ZMod p // ggKGEl_modAct V x = x} = p ^ (τ.rank - 1)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hm1 : 1 ≤ τ.rank := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hbij := ggKGEl_pibar_bijective hp hp5 hτ F hΦ ζ hζ hact
  let eE : (Fin τ.rank → ZMod p) ≃ ↥E := Equiv.ofBijective _ hbij
  have heE : ∀ x, eE x = ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact x := fun x => rfl
  have hcardE : Nat.card ↥E = p ^ τ.rank := by
    rw [← Nat.card_congr eE]
    simp [Nat.card_fun, Nat.card_zmod]
  have hfixeq : Nat.card {x : Fin τ.rank → ZMod p // ggKGEl_modAct V x = x} =
      Nat.card {e : ↥E // w₀ * ((e : ↥E) : adjointGroup τ K) * w₀⁻¹ =
        ((e : ↥E) : adjointGroup τ K)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv eE fun x => ?_)
    rw [heE x]
    have hmod := ggKGEl_pibar_modAct hp hp5 hτ F hΦ ζ hζ hact hrefl.1 V hactV x
    constructor
    · intro hx
      rw [hx] at hmod
      exact (Subtype.ext_iff.mp hmod).symm
    · intro hx
      have h2 : ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact (ggKGEl_modAct V x) =
          ggKGEl_pibar hp hp5 hτ F hΦ ζ hζ hact x := by
        rw [hmod]
        exact Subtype.ext hx
      exact hbij.1 h2
  have h3 := hrefl.2.2
  rw [← hfixeq, hcardE] at h3
  have h4 : p ^ τ.rank = p ^ (τ.rank - 1) * p := by
    rw [← pow_succ, Nat.sub_add_cancel hm1]
  rw [h4] at h3
  exact Nat.eq_of_mul_eq_mul_right hp.pos h3

end CFSG.StandardType

end



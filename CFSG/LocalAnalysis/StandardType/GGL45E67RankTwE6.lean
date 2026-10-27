module

public import CFSG.LocalAnalysis.StandardType.GGL45E67Config
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListFrames
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralCent
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1
public import CFSG.LocalAnalysis.GL83PartI.I713.LinearDiag
public import CFSG.LieType.Chevalley.E6GraphLeviTheta
public import CFSG.RankThree.PartOne.KLAY.SL2
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate7233Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction

@[expose] def cascadeFrameRoot : Fin 4 → (Fin TwistTag.E6.tag.rank → ℤ) :=
  ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1],
    ![1, 2, 2, 3, 2, 1]]

theorem cascadeFrameRoot_mem_cascade : ∀ i : Fin 4, cascadeFrameRoot i ∈ twistedE6Cascade := by
  intro i
  fin_cases i <;> decide +kernel

theorem isRoot_cascadeFrameRoot (i : Fin 4) :
    IsRoot .E6 (cascadeFrameRoot i) :=
  isRoot_of_mem_twistedE6Cascade (cascadeFrameRoot_mem_cascade i)

theorem cascadeFrameRoot_orth :
    ∀ i j : Fin 4, i ≠ j → iform (cascadeFrameRoot i) (cascadeFrameRoot j) = 0 := by
  decide +kernel

@[expose] def cascadeFrameE6 :
    TableBExcTwo.OrthFrame .E6 3 where
  root := cascadeFrameRoot
  symm_one := fun i => by simp [Tag.symmetrizer]
  isRoot := fun i => isRoot_cascadeFrameRoot i
  orth := cascadeFrameRoot_orth

private theorem card_closure_three_pow_of_test_last {G : Type} [Group G]
    (p x : Fin 4 → G) (hp : ∀ i, p i ^ 3 = 1)
    (hcomm : Pairwise fun i j => Commute (p i) (p j))
    (hx : ∀ i j, i ≠ j → j ≠ Fin.last 3 → Commute (p i) (x j))
    (htest : ∀ i (a : ZMod 3), i ≠ Fin.last 3 →
      p i ^ a.val * x i * (p i ^ a.val)⁻¹ = x i → a = 0)
    (hlast : p (Fin.last 3) ≠ 1) :
    Nat.card (Subgroup.closure (Set.range p)) = 3 ^ 4 := by
  classical
  let coord : (i : Fin 4) → Multiplicative (ZMod 3) →* G := fun i =>
    GL83.I713.zmodPowHom 3 (p i) (hp i)
  have hcoordcomm : Pairwise fun i j => ∀ a b, Commute (coord i a) (coord j b) := by
    intro i j hij a b
    exact (hcomm hij).pow_pow _ _
  let ψ : Multiplicative (Fin 4 → ZMod 3) →* G :=
    (MonoidHom.noncommPiCoprod coord hcoordcomm).comp
      (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toMonoidHom
  have hψ_single : ∀ (i : Fin 4) (a : ZMod 3), ψ (Multiplicative.ofAdd (Pi.single i a)) =
      p i ^ a.val := by
    intro i a
    have e : (MulEquiv.funMultiplicative (Fin 4) (ZMod 3))
        (Multiplicative.ofAdd (Pi.single i a)) = Pi.mulSingle i (Multiplicative.ofAdd a) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [show ψ = (MonoidHom.noncommPiCoprod coord hcoordcomm).comp
        (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toMonoidHom from rfl,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
      MonoidHom.noncommPiCoprod_mulSingle]
    rfl
  have hψ_prod : ∀ w : Fin 4 → ZMod 3, ψ (Multiplicative.ofAdd w) =
      Finset.univ.noncommProd (fun i => p i ^ (w i).val) (fun i _ j _ hij =>
        (hcomm hij).pow_pow _ _) := by
    intro w
    rw [show ψ = (MonoidHom.noncommPiCoprod coord hcoordcomm).comp
        (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toMonoidHom from rfl,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MonoidHom.noncommPiCoprod_apply]
    refine Finset.noncommProd_congr (s₂ := Finset.univ) rfl (fun i _ => ?_)
      (fun i _ j _ hij => (hcomm hij).pow_pow _ _)
    rfl
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    set v := Multiplicative.toAdd w with hv
    have hwv : w = Multiplicative.ofAdd v := by rw [hv, ofAdd_toAdd]
    rw [hwv] at hw
    have hzero : ∀ j : Fin 4, j ≠ Fin.last 3 → v j = 0 := by
      intro j hjlast
      let rest : Fin 4 → ZMod 3 := Function.update v j 0
      have hwdecomp : Multiplicative.ofAdd v =
          Multiplicative.ofAdd (Pi.single j (v j)) * Multiplicative.ofAdd rest := by
        rw [← ofAdd_add]
        congr 1
        funext k
        by_cases hk : k = j
        · subst hk; simp [rest]
        · simp [rest, Function.update, hk]
      have hrel : ψ (Multiplicative.ofAdd (Pi.single j (v j))) *
          ψ (Multiplicative.ofAdd rest) = 1 := by
        rw [← map_mul, ← hwdecomp]
        exact hw
      have hsingle : ψ (Multiplicative.ofAdd (Pi.single j (v j))) =
          (ψ (Multiplicative.ofAdd rest))⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        exact hrel
      have hcomm_rest : Commute (ψ (Multiplicative.ofAdd rest)) (x j) := by
        rw [hψ_prod rest]
        have h := Finset.noncommProd_commute (s := Finset.univ)
          (f := fun i => p i ^ (rest i).val)
          (comm := fun a _ b _ hab => (hcomm hab).pow_pow _ _) (y := x j) (fun i _ => ?_)
        exact h.symm
        by_cases hij : i = j
        · rw [hij]
          simp [rest]
        · exact (hx i j hij hjlast).symm.pow_right (rest i).val
      have hconj : ψ (Multiplicative.ofAdd (Pi.single j (v j))) * x j *
          (ψ (Multiplicative.ofAdd (Pi.single j (v j))))⁻¹ = x j := by
        rw [hsingle]
        exact hcomm_rest.inv_left.mul_inv_cancel
      have htestj : p j ^ (v j).val * x j * (p j ^ (v j).val)⁻¹ = x j := by
        simpa [hψ_single j (v j)] using hconj
      exact htest j (v j) hjlast htestj
    funext j
    by_cases hj : j = Fin.last 3
    · let rest : Fin 4 → ZMod 3 := Function.update v j 0
      have hwdecomp : Multiplicative.ofAdd v =
          Multiplicative.ofAdd (Pi.single j (v j)) * Multiplicative.ofAdd rest := by
        rw [← ofAdd_add]
        congr 1
        funext k
        by_cases hk : k = j
        · subst hk; simp [rest]
        · simp [rest, Function.update, hk]
      have hrel : ψ (Multiplicative.ofAdd (Pi.single j (v j))) *
          ψ (Multiplicative.ofAdd rest) = 1 := by
        rw [← map_mul, ← hwdecomp]
        exact hw
      have hrest0 : rest = 0 := by
        funext k
        by_cases hk : k = j
        · subst hk; simp [rest]
        · have hkj : k ≠ Fin.last 3 := fun h => hk (h.trans hj.symm)
          simp [rest, Function.update, hk, hzero k hkj]
      have hrest1 : Multiplicative.ofAdd rest = 1 := by rw [hrest0]; rfl
      rw [hrest1, map_one, mul_one] at hrel
      have hpow : p j ^ (v j).val = 1 := by
        simpa [hψ_single j (v j)] using hrel
      have hlastj : p j ≠ 1 := by rw [hj]; exact hlast
      have hord : orderOf (p j) = 3 := orderOf_eq_prime (hp j) hlastj
      have hdvd : (3 : ℕ) ∣ (v j).val := by
        have := orderOf_dvd_of_pow_eq_one hpow
        rwa [hord] at this
      exact (ZMod.val_eq_zero (v j)).mp
        (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt (v j)))
    · exact hzero j hj
  have hcard := CFSG.StandardType.card_closure_range_basis_eq_three_pow (R := G) ψ hψ_inj
  have hset : Set.range (fun i : Fin 4 => ψ (Multiplicative.ofAdd (Pi.single i 1))) =
      Set.range p := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      dsimp only
      rw [hψ_single i 1, show ZMod.val (1 : ZMod 3) = 1 by decide, pow_one]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      dsimp only
      rw [hψ_single i 1, show ZMod.val (1 : ZMod 3) = 1 by decide, pow_one]
  rwa [hset] at hcard

private theorem cascadeFrameRoot_perm (i : Fin 4) :
    permLattice TwistTag.E6.perm (cascadeFrameRoot i) = cascadeFrameRoot i :=
  (twistedE6Cascade_facts.2.1 _ (cascadeFrameRoot_mem_cascade i)).1

private theorem rootSL2_uSL_mem_C0
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot .E6 β) (hρ : permLattice TwistTag.E6.perm β = β) {c : K}
    (hc : σ c = c) :
    rootSL2 .E6 K β (uSL c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  change rootSL2 .E6 K β (uSL c) ∈ graphFixedRootGroup TwistTag.E6 K σ
  rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two
    (τ := .E6) (E := K) (CharP.cast_eq_zero K 2) β c]
  exact pinnedX_mem_graphFixedRootGroup_of_fixed σ hβ hρ hc

private theorem rootSL2_vSL_mem_C0
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot .E6 β) (hρ : permLattice TwistTag.E6.perm β = β) {c : K}
    (hc : σ c = c) :
    rootSL2 .E6 K β (vSL c) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  change rootSL2 .E6 K β (vSL c) ∈ graphFixedRootGroup TwistTag.E6 K σ
  rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two
    (τ := .E6) (E := K) (CharP.cast_eq_zero K 2) hβ c]
  refine pinnedX_mem_graphFixedRootGroup_of_fixed σ (IsRoot.neg hβ) ?_ ?_
  · rw [permLattice_neg, hρ]
  · exact hc

private theorem commute_rootSL2_C0
    {K : Type} [Field K] {σ : K →+* K}
    (F : TableBExcTwo.OrthFrame .E6 3) {i j : Fin 4} (hij : i ≠ j)
    (A B : SL2 K)
    (hA : rootSL2 .E6 K (F.root i) A ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hB : rootSL2 .E6 K (F.root j) B ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    Commute (⟨rootSL2 .E6 K (F.root i) A, hA⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (⟨rootSL2 .E6 K (F.root j) B, hB⟩ : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
  rw [commute_iff_eq]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  have h := (TableBExcTwo.commute_rho F hij A B).map (adjointGroup .E6 K).subtype
  have h' : @Eq (ModGL .E6 K)
      ((rootSL2 .E6 K (F.root i)) A * (rootSL2 .E6 K (F.root j)) B)
      ((rootSL2 .E6 K (F.root j)) B * (rootSL2 .E6 K (F.root i)) A) := by
    simpa [TableBExcTwo.coe_rho] using h.eq
  exact h'

private theorem fieldActor_rootSL2_fixed
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {δ : K ≃+* K} (F : TableBExcTwo.OrthFrame .E6 3)
    (i : Fin 4) (A : SL2 K)
    (hA : Matrix.SpecialLinearGroup.map δ.toRingHom A = A)
    (hmem : rootSL2 .E6 K (F.root i) A ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    fieldActor σ δ (⟨rootSL2 .E6 K (F.root i) A, hmem⟩ :
        ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) =
      ⟨rootSL2 .E6 K (F.root i) A, hmem⟩ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  change Units.map (entrywiseHom δ.toRingHom) (rootSL2 .E6 K (F.root i) A) =
    rootSL2 .E6 K (F.root i) A
  rw [CFSG.RankThree.Chevalley.entrywise_rootSL2_of_field, hA]

private theorem S_coe {K : Type} [Field K] (h2 : (2 : K) = 0) :
    ((uSL 1 * vSL 1 * uSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

private theorem D_eq {K : Type} [Field K] (h2 : (2 : K) = 0) (ω : Kˣ) :
    (HSL ω : SL2 K) = uSL (ω : K) * vSL ((ω⁻¹ : Kˣ) : K) * uSL (ω : K) *
      (uSL 1 * vSL 1 * uSL 1 : SL2 K) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, S_coe h2, coe_uSL, coe_vSL, coe_HSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2, Units.val_inv_eq_inv_val]

private theorem S_sq {K : Type} [Field K] (h2 : (2 : K) = 0) :
    (uSL 1 * vSL 1 * uSL 1 : SL2 K) ^ 2 = 1 := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, S_coe h2,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

private theorem HSL_pow_three {K : Type} [Field K] (ω : Kˣ) (hω3 : ω ^ 3 = 1) :
    (HSL ω : SL2 K) ^ 3 = 1 := by
  have h : (CFSG.RankThree.PartOne.KLAY.HSLhom (k := K)) (ω ^ 3) =
      ((CFSG.RankThree.PartOne.KLAY.HSLhom (k := K)) ω) ^ 3 := map_pow _ _ _
  rw [hω3, map_one] at h
  exact h.symm

private theorem HSL_ne_one {K : Type} [Field K] (ω : Kˣ) (hω : ω ≠ 1) :
    (HSL ω : SL2 K) ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun (congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
  simp [coe_HSL] at h1
  exact hω h1

private theorem S_D_sq {K : Type} [Field K] (h2 : (2 : K) = 0) (ω : Kˣ) :
    ((uSL 1 * vSL 1 * uSL 1 : SL2 K) * HSL ω) ^ 2 = 1 := by
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    S_coe h2, coe_HSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

private theorem map_S {K : Type} [Field K] (δ : K ≃+* K) :
    Matrix.SpecialLinearGroup.map δ.toRingHom (uSL 1 * vSL 1 * uSL 1 : SL2 K) =
      (uSL 1 * vSL 1 * uSL 1 : SL2 K) := by
  rw [map_mul, map_mul, CFSG.LieType.Chevalley.E6GraphLevi.map_uSL,
    CFSG.LieType.Chevalley.E6GraphLevi.map_vSL]
  simp

private theorem map_HSL_eq {K : Type} [Field K] {δ : K ≃+* K} {ω : Kˣ}
    (hδω : Units.map δ.toMonoidHom ω = ω) :
    Matrix.SpecialLinearGroup.map δ.toRingHom (HSL ω : SL2 K) = (HSL ω : SL2 K) := by
  rw [CFSG.LieType.Chevalley.E6GraphLevi.map_HSL, hδω]

private theorem three_dvd_card_units {K : Type} {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) : 3 ∣ Nat.card K - 1 := by
  have hpow : (2 ^ n) ^ 2 = 4 ^ n := by
    calc (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [← pow_mul]
      _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ n := by rw [pow_mul]
      _ = 4 ^ n := by norm_num
  rw [hK, hpow]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 n

private theorem exists_omega {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) : ∃ ω : Kˣ, orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact three_dvd_card_units hK
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3
  exact ⟨ω, hω⟩

private theorem omega_ne_one {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) : ω ≠ 1 := by
  intro h
  rw [h, orderOf_one] at hω
  omega

private theorem omega_pow_three {K : Type} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) :
    ω ^ 3 = 1 := by
  rw [← hω]
  exact pow_orderOf_eq_one ω

private theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by
    have h := Nat.ModEq.pow k (show (4 : ℕ) ≡ 1 [MOD 3] by decide)
    simpa [Nat.ModEq] using h
  have h2 : 2 ^ (k + k) = 4 ^ k := by
    calc 2 ^ (k + k) = 2 ^ k * 2 ^ k := by rw [pow_add]
      _ = 2 ^ (2 * k) := by rw [← pow_add]; ring_nf
      _ = (2 ^ 2) ^ k := by rw [← pow_mul]
      _ = 4 ^ k := by norm_num
  rw [h2, h4]

private theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by
    have h := Nat.ModEq.pow k (show (4 : ℕ) ≡ 1 [MOD 3] by decide)
    simpa [Nat.ModEq] using h
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    calc 2 ^ (2 * k + 1) = 2 ^ (2 * k) * 2 := by rw [pow_succ]
      _ = (2 ^ 2) ^ k * 2 := by rw [← pow_mul]
      _ = 4 ^ k * 2 := by norm_num
      _ = 2 * 4 ^ k := by ring
  rw [h2, Nat.mul_mod, h4]

private theorem map_omega_of_even {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {ω : Kˣ} (hω : orderOf ω = 3) (hn : Even n) :
    Units.map σ.toMonoidHom ω = ω := by
  apply Units.ext
  change σ (ω : K) = ((ω : K))
  rw [hσ, ← Units.val_pow_eq_pow_val, ← pow_mod_orderOf ω (2 ^ n), hω,
    two_pow_mod_three_of_even hn, pow_one]

private theorem map_omega_of_odd {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {ω : Kˣ} (hω : orderOf ω = 3) (hn : Odd n) :
    Units.map σ.toMonoidHom ω = ω ^ 2 := by
  apply Units.ext
  change σ (ω : K) = ((ω ^ 2 : Kˣ) : K)
  rw [hσ, ← Units.val_pow_eq_pow_val, ← pow_mod_orderOf ω (2 ^ n), hω,
    two_pow_mod_three_of_odd hn]

private theorem delta_omega {K : Type} [Field K] [Finite K] {ω : Kˣ} (hω : orderOf ω = 3)
    {δ : K ≃+* K} (hδ : δ ^ 3 = 1) : Units.map δ.toMonoidHom ω = ω := by
  classical
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hδ3 : ∀ c : K, δ (δ (δ c)) = c := by
    intro c
    have h := congrArg (fun e : K ≃+* K => e c) hδ
    simpa [pow_succ, mul_assoc] using h
  haveI : IsCyclic Kˣ := inferInstance
  let y := Units.map δ.toMonoidHom ω
  have hy : y = Units.map δ.toMonoidHom ω := rfl
  have hmap : orderOf y = 3 := by
    rw [hy, orderOf_injective (Units.map δ.toMonoidHom)
      (fun a b h => Units.ext (δ.injective (congrArg Units.val h))) ω, hω]
  have hsub : Subgroup.zpowers y = Subgroup.zpowers ω := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hmap, hω]
  have hmem : y ∈ Subgroup.zpowers ω := hsub ▸ Subgroup.mem_zpowers y
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hδy : Units.map δ.toMonoidHom y = y ^ k := by
    conv_lhs => rw [← hk]
    rw [map_zpow]
  have hδ2 : Units.map δ.toMonoidHom (y ^ k) = y ^ (k * k) := by
    rw [map_zpow]
    nth_rewrite 1 [hδy]
    rw [← zpow_mul]
  have hcube : y ^ (k * k) = ω := by
    rw [← hδ2, ← hδy]
    ext
    change δ (δ (δ (ω : K))) = (ω : K)
    exact hδ3 (ω : K)
  have hk3 : ω ^ (k ^ 3) = ω := by
    calc ω ^ (k ^ 3) = (ω ^ k) ^ (k * k) := by
          rw [← zpow_mul]; congr 1; ring
      _ = y ^ (k * k) := by rw [hk]
      _ = ω := hcube
  have hdvd : (3 : ℤ) ∣ k ^ 3 - k := Int.prime_dvd_pow_self_sub (p := 3) (by norm_num) k
  have hdiff : ω ^ (k ^ 3 - k) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hω]
    exact hdvd
  have hk_eq : ω ^ k = ω := by
    calc ω ^ k = ω ^ (k ^ 3 - k) * ω ^ k := by rw [hdiff, one_mul]
      _ = ω ^ ((k ^ 3 - k) + k) := by rw [← zpow_add]
      _ = ω ^ (k ^ 3) := by rw [Int.sub_add_cancel]
      _ = ω := hk3
  change y = ω
  rw [← hk, hk_eq]

private theorem twE6Q_isPGroup
    {K : Type} [Field K] [CharP K 2] {C0 : Subgroup (ModGL .E6 K)} :
    IsPGroup 2
      ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf C0) := by
  refine IsPGroup.of_exponent_dvd_pow (n := 1) ?_
  rw [pow_one]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
  rintro ⟨x, hx⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk]
  apply Subtype.ext
  change ((x : ModGL .E6 K) ^ 2 = 1)
  have hxroot : (x : ModGL .E6 K) ∈
      rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3)) :=
    Subgroup.mem_subgroupOf.mp hx
  obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hxroot
  rw [pow_two, ← hc, ← pinnedX_add]
  rw [show c + c = 0 by
    rw [← two_mul, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_mul]]
  rw [pinnedX_zero]

private theorem twE6Q_ne_bot
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} :
    ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf
      (show Subgroup (ModGL .E6 K) from graphFixedRootGroup TwistTag.E6 K σ)) ≠ ⊥ := by
  let C0 : Subgroup (ModGL .E6 K) := graphFixedRootGroup TwistTag.E6 K σ
  change ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf C0) ≠ ⊥
  intro hbot
  have hmem : pinnedX .E6 K (cascadeFrameE6.root (Fin.last 3)) 1 ∈ C0 :=
    pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_cascadeFrameRoot (Fin.last 3))
      (cascadeFrameRoot_perm (Fin.last 3)) (map_one σ)
  have hx : (⟨pinnedX .E6 K (cascadeFrameE6.root (Fin.last 3)) 1, hmem⟩ : ↥C0) ∈
      (rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf C0 :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [hbot] at hx
  have hx1 : pinnedX .E6 K (cascadeFrameE6.root (Fin.last 3)) 1 = 1 := by
    have := congrArg Subtype.val (Subgroup.mem_bot.mp hx)
    simpa using this
  have hzero : pinnedX .E6 K (cascadeFrameE6.root (Fin.last 3)) 1 =
      pinnedX .E6 K (cascadeFrameE6.root (Fin.last 3)) 0 := by
    rw [hx1, pinnedX_zero]
  have h10 : (1 : K) = 0 :=
    pinnedX_injective .E6 K (cascadeFrameE6.root (Fin.last 3)) hzero
  exact one_ne_zero h10

private theorem twE6Q_stab
    {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K} :
    ∀ g ∈ ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf
      (show Subgroup (ModGL .E6 K) from graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      fieldActor (t := TwistTag.E6) σ δ g ∈
        ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf
          (show Subgroup (ModGL .E6 K) from
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  let C0 : Subgroup (ModGL .E6 K) := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  change ∀ g ∈ ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf C0),
      fieldActor (t := TwistTag.E6) σ δ g ∈
        ((rootSubgroup .E6 K (cascadeFrameE6.root (Fin.last 3))).subgroupOf C0)
  intro g hg
  let g' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    show ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) from g
  let ρ : Fin TwistTag.E6.tag.rank → ℤ := cascadeFrameE6.root (Fin.last 3)
  have hgroot : (g' : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K ρ :=
    Subgroup.mem_subgroupOf.mp hg
  obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hgroot
  refine Subgroup.mem_subgroupOf.mpr ?_
  change ((fieldActor (t := TwistTag.E6) σ δ g' :
    ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) ∈
      rootSubgroup TwistTag.E6.tag K ρ
  rw [show ((fieldActor (t := TwistTag.E6) σ δ g' :
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
      Units.map (entrywiseHom δ.toRingHom) (g' : ModGL TwistTag.E6.tag K) from
    coe_fieldActor (t := TwistTag.E6) σ δ g']
  rw [← hc, CFSG.HardMathSupport.Malle.SeitzCube.entrywiseUnits_pinnedX]
  exact Subgroup.subset_closure ⟨δ c, rfl⟩

private theorem ggL45E67Config_fieldActor_twE6_even
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {δ : K ≃+* K} (hδ : δ ^ 3 = 1) (hne : Even n) :
    GGL45E67Config (fieldActor (t := TwistTag.E6) σ δ) 4 := by
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ω, hω⟩ := exists_omega hK
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hωne : ω ≠ 1 := omega_ne_one hω
  have hσω : Units.map σ.toMonoidHom ω = ω := map_omega_of_even hσ hω hne
  have hδω : Units.map δ.toMonoidHom ω = ω := delta_omega hω hδ
  have hσωK : σ (ω : K) = (ω : K) := congrArg Units.val hσω
  have hσwinv : σ (((ω⁻¹ : Kˣ) : K)) = ((ω⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσωK]
  let F : TableBExcTwo.OrthFrame .E6 3 := cascadeFrameE6
  let S : SL2 K := uSL 1 * vSL 1 * uSL 1
  let D : SL2 K := HSL ω
  let C0 : Subgroup (ModGL .E6 K) := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  have hβroot : ∀ i : Fin 4, IsRoot .E6 (F.root i) := fun i => F.isRoot i
  have hβρ : ∀ i : Fin 4, permLattice TwistTag.E6.perm (F.root i) = F.root i := by
    intro i
    exact cascadeFrameRoot_perm i
  have hSmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) S ∈ C0 := by
    intro i
    change rootSL2 .E6 K (F.root i) (uSL 1 * vSL 1 * uSL 1) ∈ C0
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem (rootSL2_uSL_mem_C0 (hβroot i) (hβρ i) (map_one σ))
      (rootSL2_vSL_mem_C0 (hβroot i) (hβρ i) (map_one σ)))
      (rootSL2_uSL_mem_C0 (hβroot i) (hβρ i) (map_one σ))
  have hDmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) D ∈ C0 := by
    intro i
    change rootSL2 .E6 K (F.root i) (HSL ω) ∈ C0
    rw [D_eq h2 ω, map_mul, map_mul, map_mul]
    exact mul_mem (mul_mem (mul_mem (rootSL2_uSL_mem_C0 (hβroot i) (hβρ i) hσωK)
      (rootSL2_vSL_mem_C0 (hβroot i) (hβρ i) hσwinv))
      (rootSL2_uSL_mem_C0 (hβroot i) (hβρ i) hσωK)) (hSmem i)
  have hSDmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) (S * D) ∈ C0 := by
    intro i
    rw [map_mul]
    exact mul_mem (hSmem i) (hDmem i)
  let a : Fin 4 → ↥C0 := fun i => ⟨rootSL2 .E6 K (F.root i) S, hSmem i⟩
  let b : Fin 4 → ↥C0 := fun i => ⟨rootSL2 .E6 K (F.root i) (S * D), hSDmem i⟩
  let p : Fin 4 → ↥C0 := fun i => ⟨rootSL2 .E6 K (F.root i) D, hDmem i⟩
  have hprod : ∀ i : Fin 4, a i * b i = p i := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    change rootSL2 .E6 K (F.root i) S * rootSL2 .E6 K (F.root i) (S * D) =
      rootSL2 .E6 K (F.root i) D
    rw [← map_mul]
    congr 1
    change (uSL 1 * vSL 1 * uSL 1) * ((uSL 1 * vSL 1 * uSL 1) * D) = D
    rw [← mul_assoc, ← pow_two, S_sq h2, one_mul]
  have ha2 : ∀ i, a i ^ 2 = 1 := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, S_sq h2, map_one]
  have hb2 : ∀ i, b i ^ 2 = 1 := by
    intro i
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, S_D_sq h2 ω, map_one]
  have hord : ∀ i, orderOf ((a i) * (b i)) = 3 := by
    intro i
    rw [hprod i]
    rw [← Subgroup.orderOf_coe (H := C0) (p i)]
    change orderOf (rootSL2 .E6 K (F.root i) D) = 3
    rw [orderOf_injective (rootSL2 .E6 K (F.root i))
      (CFSG.RankThree.Chevalley.rootSL2_injective_of_field (F.root i)) D]
    exact orderOf_eq_prime (HSL_pow_three ω hω3) (HSL_ne_one ω hωne)
  have hfa : ∀ i, fieldActor (t := TwistTag.E6) σ δ (a i) = a i := by
    intro i
    exact fieldActor_rootSL2_fixed (σ := σ) (δ := δ) F i S (map_S δ) (hSmem i)
  have hfb : ∀ i, fieldActor (t := TwistTag.E6) σ δ (b i) = b i := by
    intro i
    exact fieldActor_rootSL2_fixed (σ := σ) (δ := δ) F i (S * D)
      (by rw [map_mul, map_S δ, map_HSL_eq hδω]) (hSDmem i)
  have hcomm : ∀ i j, j < i → Commute ((a i) * (b i)) (a j) ∧
      Commute ((a i) * (b i)) (b j) := by
    intro i j hji
    have hij : i ≠ j := by omega
    rw [hprod i]
    refine ⟨?_, ?_⟩
    · exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i) (j := j) hij D S
        (hDmem i) (hSmem j)
    · exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i) (j := j) hij D (S * D)
        (hDmem i) (hSDmem j)
  have hcommP : Pairwise fun i j : Fin 4 => Commute (p i) (p j) := by
    intro i j hij
    exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i) (j := j) hij D D
      (hDmem i) (hDmem j)
  have hxmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) (uSL 1) ∈ C0 := fun i =>
    rootSL2_uSL_mem_C0 (hβroot i) (hβρ i) (map_one σ)
  let x : Fin 4 → ↥C0 := fun i => ⟨rootSL2 .E6 K (F.root i) (uSL 1), hxmem i⟩
  have hp3 : ∀ i, p i ^ 3 = 1 := fun i => by
    rw [← hord i, hprod i]
    exact pow_orderOf_eq_one _
  have hxp : ∀ i j, i ≠ j → Commute (p i) (x j) := by
    intro i j hij
    exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i) (j := j) hij D (uSL 1)
      (hDmem i) (hxmem j)
  have hp_val : ∀ i : Fin 4, (((p i : ↥C0) : ModGL .E6 K)) =
      rootTorusSL2 .E6 K (F.root i) ω := fun i => rfl
  have hp_pow : ∀ (i : Fin 4) (k : ℕ),
      (((p i) ^ k : ↥C0) : ModGL .E6 K) =
        rootTorusSL2 .E6 K (F.root i) (ω ^ k) := by
    intro i k
    induction k with
    | zero =>
        rw [pow_zero, Subgroup.coe_one, pow_zero]
        change (1 : ModGL .E6 K) = rootSL2 .E6 K (F.root i) (HSL 1)
        rw [CFSG.RankThree.PartOne.KLAY.HSL_one', map_one]
    | succ k ih =>
        rw [pow_succ, Subgroup.coe_mul, ih, hp_val i]
        change rootSL2 .E6 K (F.root i) (HSL (ω ^ k)) *
            rootSL2 .E6 K (F.root i) (HSL ω) =
          rootSL2 .E6 K (F.root i) (HSL (ω ^ (k + 1)))
        rw [← map_mul, CFSG.RankThree.PartOne.KLAY.HSL_mul_HSL, pow_succ]
  have htest : ∀ i (v : ZMod 3), p i ^ v.val * x i * (p i ^ v.val)⁻¹ = x i → v = 0 := by
    intro i v hv
    by_contra hne
    have hcongr := congrArg (fun z : ↥C0 => (z : ModGL .E6 K)) hv
    have hconj : rootTorusSL2 .E6 K (F.root i) (ω ^ v.val) *
        rootSL2 .E6 K (F.root i) (uSL 1) *
        (rootTorusSL2 .E6 K (F.root i) (ω ^ v.val))⁻¹ =
          rootSL2 .E6 K (F.root i) (uSL 1) := by
      simpa [hp_pow i v.val] using hcongr
    rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two (τ := .E6)
      (E := K) (CharP.cast_eq_zero K 2) (F.root i) 1] at hconj
    have hroot := CFSG.LieType.Chevalley.rootTorusSL2_conj_pinnedX_of_isRoot
      (F.isRoot i) (F.isRoot i) (ω ^ v.val) 1
    rw [hroot] at hconj
    rw [TableBExcTwo.iform_self_eq_two_of_isRoot F.symm_one (F.isRoot i)] at hconj
    have hval : (((ω ^ v.val : Kˣ) : K) ^ 2 * 1) = 1 :=
      pinnedX_injective .E6 K (F.root i) hconj
    have hc2 : ((ω ^ v.val : Kˣ) ^ 2) = 1 := by
      ext
      simpa using hval
    have hpow : ω ^ (2 * v.val) = 1 := by
      rw [mul_comm]
      simpa [pow_mul] using hc2
    have hdvd : (3 : ℕ) ∣ 2 * v.val := by
      have h := orderOf_dvd_of_pow_eq_one hpow
      rwa [hω] at h
    have hv3 : (3 : ℕ) ∣ v.val := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
      · norm_num at h
      · exact h
    have hv0 : v.val = 0 := Nat.eq_zero_of_dvd_of_lt hv3 (ZMod.val_lt v)
    exact hne ((ZMod.val_eq_zero v).mp hv0)
  have hcard : Nat.card (Subgroup.closure (Set.range fun i => a i * b i)) = 3 ^ 4 := by
    have hlast : p (Fin.last 3) ≠ 1 := by
      intro h1
      have htriv : p (Fin.last 3) ^ (1 : ZMod 3).val * x (Fin.last 3) *
          (p (Fin.last 3) ^ (1 : ZMod 3).val)⁻¹ = x (Fin.last 3) := by
        rw [h1]
        group
      have hbad : (1 : ZMod 3) = 0 := htest (Fin.last 3) 1 htriv
      exact absurd hbad (by decide)
    rw [show (fun i => a i * b i) = p from funext fun i => hprod i]
    exact card_closure_three_pow_of_test_last p x hp3 hcommP
      (fun i j hij _ => hxp i j hij) (fun i v _ hv => htest i v hv) hlast
  let Q : Subgroup ↥C0 :=
    (rootSubgroup .E6 K (F.root (Fin.last 3))).subgroupOf C0
  have hQ2 : IsPGroup 2 Q := twE6Q_isPGroup (C0 := C0)
  have hQne : Q ≠ ⊥ := twE6Q_ne_bot (σ := σ.toRingHom)
  have hQstab : ∀ g ∈ Q, fieldActor (t := TwistTag.E6) σ δ g ∈ Q :=
    twE6Q_stab (σ := σ) (δ := δ)
  have hpT : ∀ i : Fin 4, ((p i : ↥C0) : ModGL .E6 K) ∈ torusGroup .E6 K := by
    intro i
    rw [hp_val i]
    exact (CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_torus_transport
      .E6 K (F.isRoot i)).2.1 ω
  have hnorm_of_torus : ∀ (u : ↥C0), ((u : ↥C0) : ModGL .E6 K) ∈ torusGroup .E6 K →
      ∀ h ∈ Q, u * h * u⁻¹ ∈ Q := by
    intro u hu h hh
    have hhroot : (h : ModGL .E6 K) ∈ rootSubgroup .E6 K (F.root (Fin.last 3)) :=
      Subgroup.mem_subgroupOf.mp hh
    obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hhroot
    refine Subgroup.mem_subgroupOf.mpr ?_
    change ((u : ↥C0) : ModGL .E6 K) * (h : ModGL .E6 K) *
        (((u⁻¹ : ↥C0) : ModGL .E6 K)) ∈
          rootSubgroup .E6 K (F.root (Fin.last 3))
    rw [← hc, Subgroup.coe_inv]
    rw [CFSG.LieType.Chevalley.conj_pinnedX_of_mem_torusGroup (τ := Tag.E6) hu
      (F.isRoot (Fin.last 3)) c]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  have hQnorm : ∀ i, p i ∈ Subgroup.normalizer (Q : Set ↥C0) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact hnorm_of_torus (p i) (hpT i) g hg
    · intro hg
      have hhQ : p i * g * (p i)⁻¹ ∈ Q := hg
      have hconj := hnorm_of_torus (p i)⁻¹ (inv_mem (hpT i))
        (p i * g * (p i)⁻¹) hhQ
      convert hconj using 2
      group
  refine ⟨a, b, Q, ha2, hb2, hord, hfa, hfb, hcomm, hcard, hQ2, hQne, hQstab, ?_⟩
  intro i
  change a i * b i ∈ Subgroup.normalizer (Q : Set ↥C0)
  rw [hprod i]
  exact hQnorm i

private def e0 : Fin TwistTag.E6.tag.rank → ℤ := Pi.single 0 1
private def e0' : Fin TwistTag.E6.tag.rank → ℤ := permLattice TwistTag.E6.perm e0

private theorem sigma_sq_eq_id {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) : ∀ c, σ (σ c) = c := by
  intro c
  haveI : Fintype K := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul]
  have hcard : 2 ^ n * 2 ^ n = Nat.card K := by
    rw [hK, pow_two]
  rw [hcard]
  simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card c

private theorem frameTorusElt_pow_three
    {K : Type} [Field K]
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (a : Kˣ) (ha : a ^ 3 = 1) :
    frameTorusElt TwistTag.E6.tag K γ a ^ 3 = 1 := by
  rw [frameTorusElt_E6_eq_rootDiagUnit, rootDiagUnit_pow, ← rootDiagUnit_one]
  congr 1
  funext l
  rw [Pi.pow_apply]
  have hc : cartanChar (fun i => a ^ γ i) l =
      a ^ (∑ j, γ j * Tag.E6.cartan j l) := by
    rw [cartanChar]
    change (∏ j, (a ^ γ j) ^ Tag.E6.cartan j l) =
      a ^ (∑ j, γ j * Tag.E6.cartan j l)
    have hz : ∀ j, (a ^ γ j) ^ Tag.E6.cartan j l =
        a ^ (γ j * Tag.E6.cartan j l) := by
      intro j
      rw [← zpow_mul]
    rw [show (∏ j, (a ^ γ j) ^ Tag.E6.cartan j l) =
        ∏ j, a ^ (γ j * Tag.E6.cartan j l) from
      Finset.prod_congr rfl fun j _ => hz j]
    have h := CFSG.LieType.Chevalley.prod_zpow_eq_zpow_sum Finset.univ
      (fun j => γ j * Tag.E6.cartan j l) a
    simpa using h
  rw [hc, ← zpow_natCast (a ^ (∑ j, γ j * Tag.E6.cartan j l)) 3,
    ← zpow_mul]
  rw [show (∑ j, γ j * Tag.E6.cartan j l) * (↑(3 : ℕ) : ℤ) =
      3 * ∑ j, γ j * Tag.E6.cartan j l by ring]
  rw [zpow_mul]
  have h3z : a ^ (3 : ℤ) = 1 := by simpa using ha
  rw [h3z, one_zpow]
  rfl

private theorem h_pair_mem
    {K : Type} [Field K]
    {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) (ω : Kˣ) :
    frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) ∈
        graphFixedRootGroup TwistTag.E6 K σ :=
  frameTorusElt_pair_mem_graphFixedRootGroup hσσ e0 ω

private theorem h_conj_pinnedX
    {K : Type} [Field K] {σ : K →+* K}
    {ω : Kˣ} (hσω : Units.map σ.toMonoidHom ω = ω ^ 2)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (c : K) :
    (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) *
      pinnedX TwistTag.E6.tag K γ c *
      (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))⁻¹ =
    pinnedX TwistTag.E6.tag K γ
      ((↑(ω ^ (iform e0 γ + 2 * iform e0' γ)) : K) * c) := by
  let A := frameTorusElt TwistTag.E6.tag K e0 ω
  let B := frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)
  have hA := frameTorusElt_conj_pinnedX e0 ω hγ
    ((↑((Units.map σ.toMonoidHom ω) ^ iform e0' γ) : K) * c)
  have hB := frameTorusElt_conj_pinnedX e0' (Units.map σ.toMonoidHom ω) hγ c
  change A * B * pinnedX TwistTag.E6.tag K γ c * (A * B)⁻¹ = _
  calc A * B * pinnedX TwistTag.E6.tag K γ c * (A * B)⁻¹ =
        A * (B * pinnedX TwistTag.E6.tag K γ c * B⁻¹) * A⁻¹ := by group
    _ = A * pinnedX TwistTag.E6.tag K γ
          ((↑((Units.map σ.toMonoidHom ω) ^ iform e0' γ) : K) * c) * A⁻¹ := by
        rw [hB]
    _ = pinnedX TwistTag.E6.tag K γ
          ((↑(ω ^ iform e0 γ) : K) *
            ((↑((Units.map σ.toMonoidHom ω) ^ iform e0' γ) : K) * c)) := by
        rw [hA]
    _ = pinnedX TwistTag.E6.tag K γ
          ((↑(ω ^ (iform e0 γ + 2 * iform e0' γ)) : K) * c) := by
        congr 1
        have hu : ω ^ iform e0 γ * (Units.map σ.toMonoidHom ω) ^ iform e0' γ =
            ω ^ (iform e0 γ + 2 * iform e0' γ) := by
          rw [hσω, ← zpow_natCast ω 2, ← zpow_mul, ← zpow_add]
          norm_num
        rw [← mul_assoc, ← Units.val_mul, hu]

private theorem h_pow_three
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hσω3 : (Units.map σ.toMonoidHom ω) ^ 3 = 1) :
    (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) ^ 3 = 1 := by
  have hA : frameTorusElt TwistTag.E6.tag K e0 ω ^ 3 = 1 :=
    frameTorusElt_pow_three e0 ω hω3
  have hB : frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) ^ 3 = 1 :=
    frameTorusElt_pow_three e0' (Units.map σ.toMonoidHom ω) hσω3
  have hAB : Commute (frameTorusElt TwistTag.E6.tag K e0 ω)
      (frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) := by
    rw [show frameTorusElt TwistTag.E6.tag K e0 ω =
        rootDiagUnit TwistTag.E6.tag (cartanChar (fun i => ω ^ e0 i)) from
      frameTorusElt_E6_eq_rootDiagUnit e0 ω,
      show frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) =
        rootDiagUnit TwistTag.E6.tag (cartanChar (fun i =>
          (Units.map σ.toMonoidHom ω) ^ e0' i)) from
      frameTorusElt_E6_eq_rootDiagUnit e0' (Units.map σ.toMonoidHom ω)]
    rw [commute_iff_eq, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hAB.mul_pow, hA, hB, mul_one]

private theorem h_ne_one
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ}
    (hω : orderOf ω = 3) (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) :
    frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) ≠ 1 := by
  intro h1
  have hroot : IsRoot TwistTag.E6.tag e0 :=
    show IsRoot TwistTag.E6.tag (Pi.single (0 : Fin TwistTag.E6.tag.rank) 1) from
      isRoot_single TwistTag.E6.tag 0
  have hact := h_conj_pinnedX (σ := σ) hσω hroot 1
  rw [h1, one_mul, inv_one, mul_one] at hact
  have hexp : iform e0 e0 + 2 * iform e0' e0 = 2 := by decide
  rw [hexp] at hact
  have hval : (1 : K) = ((ω ^ 2 : Kˣ) : K) :=
    pinnedX_injective TwistTag.E6.tag K e0 (by simpa using hact)
  have hω2 : ω ^ 2 = 1 := Units.ext (by simpa using hval.symm)
  have hdvd : 3 ∣ 2 := by
    have := orderOf_dvd_of_pow_eq_one hω2
    simpa [hω] using this
  norm_num at hdvd

private theorem twE6Odd_vSL_one_sq {K : Type} [Field K] (h2 : (2 : K) = 0) :
    (vSL 1 : SL2 K) ^ 2 = 1 := by
  ext i j
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_vSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

private theorem twE6Odd_T_conj_uSL_test {K : Type} [Field K] (h2 : (2 : K) = 0) :
    ∀ a : ZMod 3, (uSL 1 * vSL 1 : SL2 K) ^ a.val * uSL 1 *
      ((uSL 1 * vSL 1 : SL2 K) ^ a.val)⁻¹ = uSL 1 → a = 0 := by
  intro a h
  by_contra hne
  have hk0 : a.val ≠ 0 := fun h0 => hne ((ZMod.val_eq_zero a).mp h0)
  have h' : (uSL 1 * vSL 1 : SL2 K) ^ a.val * uSL 1 =
      uSL 1 * (uSL 1 * vSL 1 : SL2 K) ^ a.val := by
    rwa [mul_inv_eq_iff_eq_mul] at h
  exact TableBF4Two.S0_pow_mul_uSL_ne h2 (ZMod.val_lt a) hk0 h'

private theorem twE6Odd_orbitWord_zero :
    TwistTag.E6.orbitWord (0 : Fin TwistTag.E6.foldedTag.rank) = [0, 5] := by decide

private theorem twE6Odd_w_eq
    {K : Type} [Field K] :
    twistedE6RelWeyl K [0] =
      weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1 := by
  simp [twistedE6RelWeyl, twE6Odd_orbitWord_zero]

private theorem twE6Odd_w_sq
    {K : Type} [Field K] [CharP K 2] :
    twistedE6RelWeyl K [0] * twistedE6RelWeyl K [0] = 1 := by
  rw [twE6Odd_w_eq]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg : (-1 : Kˣ) = 1 := by
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    exact TableBF4Two.neg_one_eq_one_of_two h2
  have hmem0 : (0 : Fin TwistTag.E6.tag.rank) ∈
      TwistTag.E6.orbit (0 : Fin TwistTag.E6.foldedTag.rank) := by decide
  have hmem5 : (5 : Fin TwistTag.E6.tag.rank) ∈
      TwistTag.E6.orbit (0 : Fin TwistTag.E6.foldedTag.rank) := by decide
  have h05 : (0 : Fin TwistTag.E6.tag.rank) ≠ 5 := by decide
  have hcomm : Commute (weylElt TwistTag.E6.tag K 0 1) (weylElt TwistTag.E6.tag K 5 1) :=
    commute_weylElt_weylElt (t := TwistTag.E6) K
      (a := (0 : Fin TwistTag.E6.foldedTag.rank)) (l := 0) (j := 5) hmem0 hmem5 h05 1 1
  have h0 : weylElt TwistTag.E6.tag K 0 1 ^ 2 = 1 := by
    rw [weylElt_one_sq, hneg, torusElt_one]
  have h5 : weylElt TwistTag.E6.tag K 5 1 ^ 2 = 1 := by
    rw [weylElt_one_sq, hneg, torusElt_one]
  calc weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1 *
        (weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1)
      = weylElt TwistTag.E6.tag K 0 1 *
          (weylElt TwistTag.E6.tag K 5 1 * weylElt TwistTag.E6.tag K 0 1) *
          weylElt TwistTag.E6.tag K 5 1 := by group
    _ = weylElt TwistTag.E6.tag K 0 1 *
          (weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1) *
          weylElt TwistTag.E6.tag K 5 1 := by rw [hcomm.eq]
    _ = (weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 0 1) *
          (weylElt TwistTag.E6.tag K 5 1 * weylElt TwistTag.E6.tag K 5 1) := by group
    _ = 1 := by rw [← sq, ← sq, h0, h5, mul_one]

private theorem twE6Odd_cartanChar_e0 {K : Type} [Field K] (a : Kˣ)
    (l : Fin TwistTag.E6.tag.rank) :
    cartanChar (fun i => a ^ (e0 i)) l = a ^ Tag.E6.cartan 0 l := by
  rw [cartanChar_zpow]
  simp only [e0]
  congr 1
  rw [Finset.sum_eq_single 0]
  · rw [Pi.single_eq_same, one_mul]
    rfl
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    exact zero_mul _
  · intro h0
    exact absurd (Finset.mem_univ 0) h0

private theorem twE6Odd_e0'_eq : e0' = Pi.single (5 : Fin TwistTag.E6.tag.rank) 1 := by
  rw [e0', e0, permLattice_single]
  decide

private theorem twE6Odd_cartanChar_e0' {K : Type} [Field K] (a : Kˣ)
    (l : Fin TwistTag.E6.tag.rank) :
    cartanChar (fun i => a ^ (e0' i)) l = a ^ Tag.E6.cartan 5 l := by
  rw [twE6Odd_e0'_eq]
  rw [cartanChar_zpow]
  congr 1
  rw [Finset.sum_eq_single 5]
  · rw [Pi.single_eq_same, one_mul]
    rfl
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    exact zero_mul _
  · intro h5
    exact absurd (Finset.mem_univ 5) h5

private theorem twE6Odd_h_eq_rootDiagUnit
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ}
    (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) :
    frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) =
    rootDiagUnit TwistTag.E6.tag
      (fun l => ω ^ (Tag.E6.cartan 0 l + 2 * Tag.E6.cartan 5 l)) := by
  rw [frameTorusElt_E6_eq_rootDiagUnit, frameTorusElt_E6_eq_rootDiagUnit,
    ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, twE6Odd_cartanChar_e0 ω l,
    twE6Odd_cartanChar_e0' (Units.map σ.toMonoidHom ω) l, hσω, ← zpow_natCast ω 2,
    ← zpow_mul, ← zpow_add]
  norm_num

private theorem twE6Odd_exponent_identity (A : Fin TwistTag.E6.tag.rank → ℤ)
    (hA : ∀ j, A j = Tag.E6.cartan 0 j + 2 * Tag.E6.cartan 5 j)
    (j : Fin TwistTag.E6.tag.rank) :
    A j + A 5 * -Tag.E6.cartan 5 j +
        (A 0 + A 5 * -Tag.E6.cartan 5 0) * -Tag.E6.cartan 0 j = -A j := by
  rw [hA j, hA 0, hA 5]
  fin_cases j <;> decide

private theorem twE6Odd_w_conj_h_eq_inv
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ}
    (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) :
    twistedE6RelWeyl K [0] *
      (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) *
      (twistedE6RelWeyl K [0])⁻¹ =
    (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))⁻¹ := by
  rw [twE6Odd_w_eq, twE6Odd_h_eq_rootDiagUnit hσω, mul_inv_rev]
  let N : Fin TwistTag.E6.tag.rank → ℤ :=
    fun l => TwistTag.E6.tag.cartan 0 l + 2 * TwistTag.E6.tag.cartan 5 l
  change (weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1) *
      rootDiagUnit TwistTag.E6.tag (fun l => ω ^ N l) *
      ((weylElt TwistTag.E6.tag K 5 1)⁻¹ * (weylElt TwistTag.E6.tag K 0 1)⁻¹) =
    (rootDiagUnit TwistTag.E6.tag (fun l => ω ^ N l))⁻¹
  have hB := weylElt_conj_rootDiagUnit (τ := TwistTag.E6.tag) (fun j => ω ^ N j) 5
  have hA := weylElt_conj_rootDiagUnit (τ := TwistTag.E6.tag)
    (fun j => ω ^ N j * (ω ^ N 5) ^ (-TwistTag.E6.tag.cartan 5 j)) 0
  calc (weylElt TwistTag.E6.tag K 0 1 * weylElt TwistTag.E6.tag K 5 1) *
        rootDiagUnit TwistTag.E6.tag (fun l => ω ^ N l) *
        ((weylElt TwistTag.E6.tag K 5 1)⁻¹ * (weylElt TwistTag.E6.tag K 0 1)⁻¹)
      = weylElt TwistTag.E6.tag K 0 1 *
          (weylElt TwistTag.E6.tag K 5 1 * rootDiagUnit TwistTag.E6.tag (fun l => ω ^ N l) *
            (weylElt TwistTag.E6.tag K 5 1)⁻¹) *
          (weylElt TwistTag.E6.tag K 0 1)⁻¹ := by group
    _ = weylElt TwistTag.E6.tag K 0 1 *
          rootDiagUnit TwistTag.E6.tag
            (fun j => ω ^ N j * (ω ^ N 5) ^ (-TwistTag.E6.tag.cartan 5 j)) *
          (weylElt TwistTag.E6.tag K 0 1)⁻¹ := by rw [hB]
    _ = rootDiagUnit TwistTag.E6.tag (fun j =>
          (ω ^ N j * (ω ^ N 5) ^ (-TwistTag.E6.tag.cartan 5 j)) *
            ((ω ^ N 0 * (ω ^ N 5) ^ (-TwistTag.E6.tag.cartan 5 0)) ^
              (-TwistTag.E6.tag.cartan 0 j))) := by rw [hA]
    _ = rootDiagUnit TwistTag.E6.tag (fun j => ω ^ (-N j)) := by
        congr 1
        funext j
        simp only [← zpow_mul, ← zpow_add]
        congr 1
        exact twE6Odd_exponent_identity N (fun j => rfl) j
    _ = (rootDiagUnit TwistTag.E6.tag (fun l => ω ^ N l))⁻¹ := by
        rw [rootDiagUnit_inv]
        congr 1
        funext j
        rw [Pi.inv_apply, zpow_neg]

private theorem twE6Odd_wh_sq
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ω : Kˣ}
    (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) :
    (twistedE6RelWeyl K [0] *
      (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))) *
      (twistedE6RelWeyl K [0] *
        (frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))) = 1 := by
  have hconj := twE6Odd_w_conj_h_eq_inv (σ := σ) hσω
  have hw : twistedE6RelWeyl K [0] * twistedE6RelWeyl K [0] = 1 := twE6Odd_w_sq
  calc (twistedE6RelWeyl K [0] *
        (frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))) *
        (twistedE6RelWeyl K [0] *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)))
      = (twistedE6RelWeyl K [0] *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) *
          (twistedE6RelWeyl K [0])⁻¹) *
          (twistedE6RelWeyl K [0] * twistedE6RelWeyl K [0]) *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) := by
        group
    _ = (frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))⁻¹ * 1 *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) := by
        rw [hconj, hw]
    _ = 1 := by group

private theorem twE6Odd_w_mul_wh
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ω : Kˣ} :
    twistedE6RelWeyl K [0] *
      (twistedE6RelWeyl K [0] *
        (frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))) =
      frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω) := by
  rw [← mul_assoc, twE6Odd_w_sq (K := K), one_mul]

private theorem twE6Odd_dvd_iform :
    ∀ i : Fin 4, 3 ∣ iform e0 (cascadeFrameRoot i) + 2 * iform e0' (cascadeFrameRoot i) := by
  decide

private theorem twE6Odd_dvd_iform_neg :
    ∀ i : Fin 4, 3 ∣ iform e0 (-cascadeFrameRoot i) + 2 * iform e0' (-cascadeFrameRoot i) := by
  intro i
  have h := twE6Odd_dvd_iform i
  rw [iform_neg_right', iform_neg_right']
  have h' : -iform e0 (cascadeFrameRoot i) + 2 * -iform e0' (cascadeFrameRoot i) =
      -(iform e0 (cascadeFrameRoot i) + 2 * iform e0' (cascadeFrameRoot i)) := by ring
  rw [h']
  exact dvd_neg.mpr h

private theorem twE6Odd_h_commute_pinnedX
    {K : Type} [Field K]
    {σ : K →+* K} {ω : Kˣ} (hω : orderOf ω = 3)
    (hσω : Units.map σ.toMonoidHom ω = ω ^ 2)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (h3 : 3 ∣ iform e0 γ + 2 * iform e0' γ) (c : K) :
    Commute (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))
      (pinnedX TwistTag.E6.tag K γ c) := by
  rw [commute_iff_eq]
  have h := h_conj_pinnedX (σ := σ) hσω hγ c
  have hωm : ω ^ (iform e0 γ + 2 * iform e0' γ) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hω]
    exact h3
  rw [hωm] at h
  simp only [Units.val_one, one_mul] at h
  calc (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) *
        pinnedX TwistTag.E6.tag K γ c
      = ((frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) *
          pinnedX TwistTag.E6.tag K γ c *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))⁻¹) *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) := by
        group
    _ = pinnedX TwistTag.E6.tag K γ c *
          (frameTorusElt TwistTag.E6.tag K e0 ω *
            frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω)) := by rw [h]

private theorem twE6Odd_h_commute_root
    {K : Type} [Field K] {σ : K →+* K} {ω : Kˣ}
    (hω : orderOf ω = 3) (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) (i : Fin 4) (c : K) :
    Commute (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))
      (pinnedX TwistTag.E6.tag K (cascadeFrameRoot i) c) :=
  twE6Odd_h_commute_pinnedX hω hσω (isRoot_cascadeFrameRoot i) (twE6Odd_dvd_iform i) c

private theorem twE6Odd_h_commute_root_neg
    {K : Type} [Field K]
    {σ : K →+* K} {ω : Kˣ} (hω : orderOf ω = 3)
    (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) (i : Fin 4) (c : K) :
    Commute (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))
      (pinnedX TwistTag.E6.tag K (-cascadeFrameRoot i) c) :=
  twE6Odd_h_commute_pinnedX hω hσω (IsRoot.neg (isRoot_cascadeFrameRoot i))
    (twE6Odd_dvd_iform_neg i) c

private theorem twE6Odd_h_commute_uSL
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ω : Kˣ}
    (hω : orderOf ω = 3) (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) (i : Fin 4) (c : K) :
    Commute (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))
      (rootSL2 TwistTag.E6.tag K (cascadeFrameRoot i) (uSL c)) := by
  rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two (τ := TwistTag.E6.tag)
    (E := K) (CharP.cast_eq_zero K 2) (cascadeFrameRoot i) c]
  exact twE6Odd_h_commute_root hω hσω i c

private theorem twE6Odd_h_commute_vSL
    {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ω : Kˣ}
    (hω : orderOf ω = 3) (hσω : Units.map σ.toMonoidHom ω = ω ^ 2) (i : Fin 4) (c : K) :
    Commute (frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toMonoidHom ω))
      (rootSL2 TwistTag.E6.tag K (cascadeFrameRoot i) (vSL c)) := by
  rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two (τ := TwistTag.E6.tag)
    (E := K) (CharP.cast_eq_zero K 2) (isRoot_cascadeFrameRoot i) c]
  exact twE6Odd_h_commute_root_neg hω hσω i c

private theorem twE6Odd_fieldActor_weyl
    {K : Type} [Field K]
    {δ : K ≃+* K} :
    Units.map (entrywiseHom δ.toRingHom) (twistedE6RelWeyl K [0]) =
      twistedE6RelWeyl K [0] := by
  rw [twE6Odd_w_eq, map_mul, CFSG.LieType.Chevalley.entrywise_weylElt_one δ 0,
    CFSG.LieType.Chevalley.entrywise_weylElt_one δ 5]

private theorem twE6Odd_fieldActor_h_diag {K : Type} [Field K] {δ : K →+* K} {ω : Kˣ}
    (hδω : Units.map δ.toMonoidHom ω = ω) :
    Units.map (entrywiseHom δ)
        (rootDiagUnit TwistTag.E6.tag
          (fun l => ω ^ (Tag.E6.cartan 0 l + 2 * Tag.E6.cartan 5 l))) =
      rootDiagUnit TwistTag.E6.tag
        (fun l => ω ^ (Tag.E6.cartan 0 l + 2 * Tag.E6.cartan 5 l)) := by
  rw [units_map_entrywiseHom_rootDiagUnit]
  congr 1
  funext l
  rw [map_zpow, hδω]

private theorem ggL45E67Config_fieldActor_twE6_odd
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {δ : K ≃+* K} (hδ : δ ^ 3 = 1) (hno : Odd n) :
    GGL45E67Config (fieldActor (t := TwistTag.E6) σ δ) 4 := by
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ω, hω⟩ := exists_omega hK
  have hω3 : ω ^ 3 = 1 := omega_pow_three hω
  have hσω : Units.map σ.toRingHom.toMonoidHom ω = ω ^ 2 :=
    map_omega_of_odd hσ hω hno
  have hδω : Units.map δ.toRingHom.toMonoidHom ω = ω := delta_omega hω hδ
  have hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c := sigma_sq_eq_id hK hσ
  have hσω3 : (Units.map σ.toRingHom.toMonoidHom ω) ^ 3 = 1 := by
    rw [hσω, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  let F : TableBExcTwo.OrthFrame .E6 3 := cascadeFrameE6
  let C0 : Subgroup (ModGL .E6 K) := graphFixedRootGroup TwistTag.E6 K σ.toRingHom
  let hMod : ModGL .E6 K :=
    frameTorusElt TwistTag.E6.tag K e0 ω *
      frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toRingHom.toMonoidHom ω)
  have hmemH : hMod ∈ C0 := h_pair_mem (σ := σ.toRingHom) hσσ ω
  let hC : ↥C0 := ⟨hMod, hmemH⟩
  let wMod : ModGL .E6 K := twistedE6RelWeyl K [0]
  have hmemW : wMod ∈ C0 := twistedE6RelWeyl_mem σ.toRingHom [0]
  let wC : ↥C0 := ⟨wMod, hmemW⟩
  have hTmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) (uSL 1 * vSL 1) ∈ C0 := by
    intro i
    rw [map_mul]
    exact mul_mem (rootSL2_uSL_mem_C0 (F.isRoot i) (cascadeFrameRoot_perm i)
      (map_one σ.toRingHom)) (rootSL2_vSL_mem_C0 (F.isRoot i) (cascadeFrameRoot_perm i)
      (map_one σ.toRingHom))
  have huSLmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) (uSL 1) ∈ C0 := fun i =>
    rootSL2_uSL_mem_C0 (F.isRoot i) (cascadeFrameRoot_perm i) (map_one σ.toRingHom)
  have hvSLmem : ∀ i : Fin 4, rootSL2 .E6 K (F.root i) (vSL 1) ∈ C0 := fun i =>
    rootSL2_vSL_mem_C0 (F.isRoot i) (cascadeFrameRoot_perm i) (map_one σ.toRingHom)
  let aCast : Fin 3 → ↥C0 := fun j =>
    ⟨rootSL2 .E6 K (F.root j.castSucc) (uSL 1), huSLmem j.castSucc⟩
  let bCast : Fin 3 → ↥C0 := fun j =>
    ⟨rootSL2 .E6 K (F.root j.castSucc) (vSL 1), hvSLmem j.castSucc⟩
  let pCast : Fin 3 → ↥C0 := fun j =>
    ⟨rootSL2 .E6 K (F.root j.castSucc) (uSL 1 * vSL 1), hTmem j.castSucc⟩
  let a : Fin 4 → ↥C0 := Fin.lastCases wC aCast
  let b : Fin 4 → ↥C0 := Fin.lastCases (wC * hC) bCast
  let p : Fin 4 → ↥C0 := Fin.lastCases hC pCast
  have ha_cast : ∀ j : Fin 3, a j.castSucc = aCast j := fun j => Fin.lastCases_castSucc j
  have ha_last : a (Fin.last 3) = wC := Fin.lastCases_last
  have hb_cast : ∀ j : Fin 3, b j.castSucc = bCast j := fun j => Fin.lastCases_castSucc j
  have hb_last : b (Fin.last 3) = wC * hC := Fin.lastCases_last
  have hp_cast : ∀ j : Fin 3, p j.castSucc = pCast j := fun j => Fin.lastCases_castSucc j
  have hp_last : p (Fin.last 3) = hC := Fin.lastCases_last
  have hprod : ∀ i, a i * b i = p i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [ha_cast j, hb_cast j, hp_cast j]
      apply Subtype.ext
      change rootSL2 .E6 K (F.root j.castSucc) (uSL 1) *
          rootSL2 .E6 K (F.root j.castSucc) (vSL 1) =
        rootSL2 .E6 K (F.root j.castSucc) (uSL 1 * vSL 1)
      rw [← map_mul]
    · rw [ha_last, hb_last, hp_last]
      apply Subtype.ext
      change (wC * (wC * hC) : ↥C0).1 = hC.1
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact twE6Odd_w_mul_wh (σ := σ.toRingHom)
  have ha2 : ∀ i, a i ^ 2 = 1 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [ha_cast j]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (rootSL2 .E6 K (F.root j.castSucc) (uSL 1)) ^ 2 = 1
      rw [← map_pow, TableBF4Two.uSL_one_sq h2, map_one]
    · rw [ha_last]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact twE6Odd_w_sq (K := K)
  have hb2 : ∀ i, b i ^ 2 = 1 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hb_cast j]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (rootSL2 .E6 K (F.root j.castSucc) (vSL 1)) ^ 2 = 1
      rw [← map_pow, twE6Odd_vSL_one_sq h2, map_one]
    · rw [hb_last]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mul, pow_two]
      exact twE6Odd_wh_sq (σ := σ.toRingHom) hσω
  have hord : ∀ i, orderOf ((a i) * (b i)) = 3 := by
    intro i
    rw [hprod i]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hp_cast j]
      rw [← Subgroup.orderOf_coe (H := C0) (pCast j)]
      change orderOf (rootSL2 .E6 K (F.root j.castSucc) (uSL 1 * vSL 1)) = 3
      rw [orderOf_injective (rootSL2 .E6 K (F.root j.castSucc))
        (CFSG.RankThree.Chevalley.rootSL2_injective_of_field (F.root j.castSucc))
        (uSL 1 * vSL 1)]
      exact orderOf_eq_prime (TableBF4Two.S0_pow_three h2) (TableBF4Two.S0_ne_one h2)
    · rw [hp_last]
      rw [← Subgroup.orderOf_coe (H := C0) hC]
      change orderOf hMod = 3
      exact orderOf_eq_prime (h_pow_three (σ := σ.toRingHom) hω3 hσω3)
        (h_ne_one (σ := σ.toRingHom) hω hσω)
  have hfixW : fieldActor (t := TwistTag.E6) σ δ wC = wC := by
    apply Subtype.ext
    exact twE6Odd_fieldActor_weyl (K := K) (δ := δ)
  have hfixH : fieldActor (t := TwistTag.E6) σ δ hC = hC := by
    apply Subtype.ext
    change Units.map (entrywiseHom δ.toRingHom)
        (frameTorusElt TwistTag.E6.tag K e0 ω *
          frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toRingHom.toMonoidHom ω)) =
      frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toRingHom.toMonoidHom ω)
    rw [twE6Odd_h_eq_rootDiagUnit (σ := σ.toRingHom) hσω]
    exact twE6Odd_fieldActor_h_diag hδω
  have hfa : ∀ i, fieldActor (t := TwistTag.E6) σ δ (a i) = a i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [ha_cast j]
      exact fieldActor_rootSL2_fixed (σ := σ) (δ := δ) F j.castSucc (uSL 1)
        (by rw [CFSG.LieType.Chevalley.E6GraphLevi.map_uSL]; simp) (huSLmem j.castSucc)
    · rw [ha_last]
      exact hfixW
  have hfb : ∀ i, fieldActor (t := TwistTag.E6) σ δ (b i) = b i := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hb_cast j]
      exact fieldActor_rootSL2_fixed (σ := σ) (δ := δ) F j.castSucc (vSL 1)
        (by rw [CFSG.LieType.Chevalley.E6GraphLevi.map_vSL]; simp) (hvSLmem j.castSucc)
    · rw [hb_last]
      have hm : (fieldActor (t := TwistTag.E6) σ δ) (wC * hC) =
          (fieldActor (t := TwistTag.E6) σ δ) wC *
            (fieldActor (t := TwistTag.E6) σ δ) hC :=
        MulEquiv.map_mul (fieldActor (t := TwistTag.E6) σ δ) wC hC
      rw [hm, hfixW, hfixH]
      rfl
  have hcommT : ∀ j : Fin 3, Commute hC (pCast j) := by
    intro j
    have h1 : Commute hMod (rootSL2 .E6 K (F.root j.castSucc) (uSL 1)) :=
      twE6Odd_h_commute_uSL (σ := σ.toRingHom) hω hσω j.castSucc 1
    have h2 : Commute hMod (rootSL2 .E6 K (F.root j.castSucc) (vSL 1)) :=
      twE6Odd_h_commute_vSL (σ := σ.toRingHom) hω hσω j.castSucc 1
    have h3 : Commute hMod (rootSL2 .E6 K (F.root j.castSucc) (uSL 1 * vSL 1)) := by
      have h12 := h1.mul_right h2
      rwa [← map_mul] at h12
    rw [commute_iff_eq]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h3.eq
  have hcommP : Pairwise fun i j : Fin 4 => Commute (p i) (p j) := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [hp_cast i', hp_cast j']
        have hne : i' ≠ j' := fun h => hij (by rw [h])
        exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i'.castSucc) (j := j'.castSucc)
          (by simpa using hne) (uSL 1 * vSL 1) (uSL 1 * vSL 1) (hTmem _) (hTmem _)
      · rw [hp_cast i', hp_last]
        exact (hcommT i').symm
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [hp_last, hp_cast j']
        exact hcommT j'
      · exact absurd rfl hij
  have hp3 : ∀ i, p i ^ 3 = 1 := by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hp_cast j]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (rootSL2 .E6 K (F.root j.castSucc) (uSL 1 * vSL 1)) ^ 3 = 1
      rw [← map_pow, TableBF4Two.S0_pow_three h2, map_one]
    · rw [hp_last]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h_pow_three (σ := σ.toRingHom) hω3 hσω3
  have hx : ∀ i j, i ≠ j → j ≠ Fin.last 3 → Commute (p i) (a j) := by
    intro i j hij hjlast
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · rw [ha_cast j']
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [hp_cast i']
        exact commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i'.castSucc) (j := j'.castSucc)
          (by simpa using fun h => hij (by rw [h])) (uSL 1 * vSL 1) (uSL 1) (hTmem _)
          (huSLmem _)
      · rw [hp_last]
        have hcm := twE6Odd_h_commute_uSL (σ := σ.toRingHom) hω hσω j'.castSucc 1
        rw [commute_iff_eq] at hcm ⊢
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hcm
    · exact absurd rfl hjlast
  have htest : ∀ i (v : ZMod 3), i ≠ Fin.last 3 →
      p i ^ v.val * a i * (p i ^ v.val)⁻¹ = a i → v = 0 := by
    intro i v hi hconj
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [hp_cast i', ha_cast i'] at hconj
      have h := congrArg (fun z : ↥C0 => (z : ModGL .E6 K)) hconj
      simp only [pCast, aCast, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] at h
      have h' : rootSL2 .E6 K (F.root i'.castSucc)
          ((uSL 1 * vSL 1 : SL2 K) ^ v.val * uSL 1 *
            ((uSL 1 * vSL 1 : SL2 K) ^ v.val)⁻¹) =
          rootSL2 .E6 K (F.root i'.castSucc) (uSL 1) := by
        simpa only [map_mul, map_pow, map_inv] using h
      exact twE6Odd_T_conj_uSL_test h2 v
        (CFSG.RankThree.Chevalley.rootSL2_injective_of_field (F.root i'.castSucc) h')
    · exact absurd rfl hi
  have hlast : p (Fin.last 3) ≠ 1 := by
    rw [hp_last]
    intro h1
    have h2 : (frameTorusElt TwistTag.E6.tag K e0 ω *
        frameTorusElt TwistTag.E6.tag K e0' (Units.map σ.toRingHom.toMonoidHom ω)) = 1 := by
      have h3 : (hC : ModGL .E6 K) = 1 := by rw [h1, Subgroup.coe_one]
      exact h3
    exact h_ne_one (σ := σ.toRingHom) hω hσω h2
  have hcard : Nat.card (Subgroup.closure (Set.range fun i => a i * b i)) = 3 ^ 4 := by
    rw [show (fun i => a i * b i) = p from funext hprod]
    exact card_closure_three_pow_of_test_last p a hp3 hcommP hx htest hlast
  let Q : Subgroup ↥C0 :=
    (rootSubgroup .E6 K (F.root (Fin.last 3))).subgroupOf C0
  have hQ2 : IsPGroup 2 Q := twE6Q_isPGroup (C0 := C0)
  have hQne : Q ≠ ⊥ := twE6Q_ne_bot (σ := σ.toRingHom)
  have hQstab : ∀ g ∈ Q, fieldActor (t := TwistTag.E6) σ δ g ∈ Q :=
    twE6Q_stab (σ := σ) (δ := δ)
  have hcentQ : ∀ i, p i ∈ Subgroup.centralizer (Q : Set ↥C0) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨c, hc⟩ := mem_rootSubgroup.mp (Subgroup.mem_subgroupOf.mp hg)
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [hp_cast i']
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rw [show (g : ModGL .E6 K) = pinnedX Tag.E6 K (F.root (Fin.last 3)) c from hc.symm]
      rw [show (pCast i' : ModGL .E6 K) =
          rootSL2 .E6 K (F.root i'.castSucc) (uSL 1 * vSL 1) from rfl]
      rw [← CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two (τ := Tag.E6)
        (E := K) (CharP.cast_eq_zero K 2) (F.root (Fin.last 3)) c]
      have hine : i'.castSucc ≠ Fin.last 3 := by
        intro h
        have h' := congrArg Fin.val h
        simp at h'
        omega
      have hcomm := (TableBExcTwo.commute_rho F (i := i'.castSucc) (j := Fin.last 3)
        hine (uSL 1 * vSL 1) (uSL c)).map (adjointGroup .E6 K).subtype
      exact (by simpa [TableBExcTwo.coe_rho] using hcomm.eq.symm)
    · rw [hp_last]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      rw [show (g : ModGL .E6 K) = pinnedX Tag.E6 K (F.root (Fin.last 3)) c from hc.symm]
      have hcm := twE6Odd_h_commute_root (σ := σ.toRingHom) hω hσω (Fin.last 3) c
      rw [commute_iff_eq] at hcm
      exact hcm.symm
  have hQnorm : ∀ i, p i ∈ Subgroup.normalizer (Q : Set ↥C0) := fun i =>
    Subgroup.centralizer_le_normalizer (Q : Set ↥C0) (hcentQ i)
  have hcommAll : ∀ i j, j < i → Commute ((a i) * (b i)) (a j) ∧
      Commute ((a i) * (b i)) (b j) := by
    intro i j hji
    rw [hprod i]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · have hjlast : j ≠ Fin.last 3 := by
        intro h
        rw [h] at hji
        exact (Fin.castSucc_lt_last i').asymm hji
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hne : i' ≠ j' := by
          intro h
          rw [h] at hji
          exact (lt_irrefl _) hji
        rw [hp_cast i', ha_cast j', hb_cast j']
        exact ⟨commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i'.castSucc)
            (j := j'.castSucc) (by simpa using hne) (uSL 1 * vSL 1) (uSL 1)
            (hTmem _) (huSLmem _),
          commute_rootSL2_C0 (σ := σ.toRingHom) F (i := i'.castSucc)
            (j := j'.castSucc) (by simpa using hne) (uSL 1 * vSL 1) (vSL 1)
            (hTmem _) (hvSLmem _)⟩
      · exact absurd rfl hjlast
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [hp_last, ha_cast j', hb_cast j']
        constructor
        · have hcm := twE6Odd_h_commute_uSL (σ := σ.toRingHom) hω hσω j'.castSucc 1
          rw [commute_iff_eq] at hcm ⊢
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact hcm
        · have hcm := twE6Odd_h_commute_vSL (σ := σ.toRingHom) hω hσω j'.castSucc 1
          rw [commute_iff_eq] at hcm ⊢
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact hcm
      · exact absurd hji (lt_irrefl _)
  have hnormAll : ∀ i, a i * b i ∈ Subgroup.normalizer (Q : Set ↥C0) := by
    intro i
    rw [hprod i]
    exact hQnorm i
  exact ⟨a, b, Q, ha2, hb2, hord, hfa, hfb, hcommAll, hcard, hQ2, hQne, hQstab, hnormAll⟩
theorem ggL45E67Config_fieldActor_twE6
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {δ : K ≃+* K} (hδ : δ ^ 3 = 1) :
    GGL45E67Config (fieldActor (t := TwistTag.E6) σ δ) 4 := by
  rcases Nat.even_or_odd n with h | h
  · exact ggL45E67Config_fieldActor_twE6_even hK σ hσ hδ h
  · exact ggL45E67Config_fieldActor_twE6_odd hK σ hσ hδ h

theorem ggL45E67Config_twE6Recipe
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∀ f ∈ LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n),
      orderOf f = 3 → GGL45E67Config f 4 := by
  intro f hf hord
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨iterateFrobeniusEquiv K 2 n, fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  obtain ⟨ε, -, hfD⟩ := TwE6FieldCore.exists_recipeConj_field hn hK σ hσ
  obtain ⟨δ, rfl⟩ := hfD f hf
  have hδ : δ ^ 3 = 1 := by
    have h1 : orderOf (fieldActor (t := TwistTag.E6) σ δ) = 3 := by
      rw [← MulEquiv.orderOf_eq (MulAut.congr ε) (fieldActor (t := TwistTag.E6) σ δ)]
      exact hord
    have h2 : orderOf (fieldActor (t := TwistTag.E6) σ δ) = orderOf δ :=
      TwE6FieldCore.orderOf_fieldActor hn hK hσ δ
    have h3 : orderOf δ = 3 := by rw [← h2, h1]
    rw [← h3]
    exact pow_orderOf_eq_one δ
  refine ggL45E67Config_of_mulEquiv ε (fun x => ?_)
    (ggL45E67Config_fieldActor_twE6 hK σ hσ hδ)
  change ε ((fieldActor (t := TwistTag.E6) σ δ) (ε.symm (ε x))) =
    ε ((fieldActor (t := TwistTag.E6) σ δ) x)
  rw [MulEquiv.symm_apply_apply]

end CFSG.StandardType

end

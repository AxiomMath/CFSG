module

public import CFSG.LocalAnalysis.StandardType.GGKG87BSCBridge
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjLift
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjOrbit
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated
import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.KG87B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.AlgebraicGroups (rootCharHom kernelRoots_rootCharHom)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.SeitzReduction.F4Pilot (twistedIsogenyC)
open CFSG.HardMathSupport.Timmesfeld.Steinberg (toralCentralizer_eq_toralRootGroup_of_stabilizer_le)

private theorem e6KerCount_thirty_inner : ∀ a b c d e f : ZMod 3,
    e6KerCount (e6ConjVec a b c d e f) = 30 → a + 2 * c + e + 2 * f = 0 := by
  decide +kernel

private theorem kernelRoots_torV
    {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) (x : Fin Tag.E6.rank → ZMod 3) :
    kernelRoots (rootCharHom (SmallQ3.torV ω x)) =
      {α | IsRoot Tag.E6 α ∧ ∑ i, x i * ((α i : ℤ) : ZMod 3) = 0} := by
  have h3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have h1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  ext α
  simp only [kernelRoots_rootCharHom, Set.mem_setOf_eq]
  exact and_congr_right fun _ => rootChar_torV_eq_one_iff h3 h1 x α

private theorem ncard_kernelRoots_eq_e6KerCount
    (x : Fin Tag.E6.rank → ZMod 3) :
    {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α ∧ ∑ i, x i * ((α i : ℤ) : ZMod 3) = 0}.ncard =
      e6KerCount x := by
  rw [e6KerCount, ← Set.ncard_coe_finset]
  congr 1
  ext α
  simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_rootFinset]

private theorem exists_inner_of_ncard_thirty
    {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom a)).ncard = 30) :
    ∃ x : Fin Tag.E6.rank → ZMod 3, SmallQ3.torV ω x = a ∧ e6KerCount x = 30 ∧
      SmallQ3.subLin (τ := .E6) SmallQ3.e6InnerVec (SmallQ3.e6InnerCoords x) = x := by
  have hprim : IsPrimitiveRoot ω 3 := hω ▸ IsPrimitiveRoot.orderOf ω
  choose m hm hma using fun i =>
    hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (a i)).2 (ha i))
  set x : Fin Tag.E6.rank → ZMod 3 := fun i => (m i : ZMod 3) with hxdef
  have hxa : SmallQ3.torV ω x = a := funext fun i => by
    change ω ^ ((m i : ZMod 3)).val = a i
    rw [ZMod.val_natCast_of_lt (hm i), hma i]
  have hx : e6KerCount x = 30 := by
    rw [← ncard_kernelRoots_eq_e6KerCount, ← kernelRoots_torV hω, hxa]
    exact hk
  refine ⟨x, hxa, hx, SmallQ3.subLin_e6InnerCoords ?_⟩
  have hx' : x = e6ConjVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext i
    fin_cases i <;> rfl
  exact e6KerCount_thirty_inner _ _ _ _ _ _ (by rw [← hx']; exact hx)

private theorem exists_orderOf_eq_three {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : ∃ ω : Kˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_prime_orderOf_dvd_card' 3 ?_
  rw [Nat.card_units, hK, ← pow_mul, mul_comm, pow_mul]
  have h := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 n
  rw [one_pow] at h
  exact h

private theorem list_prod_pow_eq_one {M : Type*} [CommMonoid M] {m : ℕ} :
    ∀ l : List M, (∀ t ∈ l, t ^ m = 1) → l.prod ^ m = 1
  | [], _ => by rw [List.prod_nil, one_pow]
  | t :: l, h => by
    rw [List.prod_cons, mul_pow, h t List.mem_cons_self,
      list_prod_pow_eq_one l fun s hs => h s (List.mem_cons_of_mem _ hs), one_mul]

private theorem conj_eq_mul_of_conj {G : Type*} [Group G] {G₃ X H T z Z : G}
    (hzc : z ∈ Subgroup.center G) (hZc : Z ∈ Subgroup.center G) (hH : H = G₃ * (T * z) * G₃⁻¹)
    (hXZ : X * H * X⁻¹ = H * Z) :
    (G₃⁻¹ * X * G₃) * T * (G₃⁻¹ * X * G₃)⁻¹ = T * Z := by
  have hz := Subgroup.mem_center_iff.1 hzc
  have hZ := Subgroup.mem_center_iff.1 hZc
  have e1 : (G₃⁻¹ * X * G₃) * T * (G₃⁻¹ * X * G₃)⁻¹ * z = G₃⁻¹ * (X * H * X⁻¹) * G₃ := by
    rw [hH]
    calc (G₃⁻¹ * X * G₃) * T * (G₃⁻¹ * X * G₃)⁻¹ * z
        = (G₃⁻¹ * X * G₃) * T * ((G₃⁻¹ * X * G₃)⁻¹ * z) := by group
      _ = (G₃⁻¹ * X * G₃) * T * (z * (G₃⁻¹ * X * G₃)⁻¹) := by rw [hz (G₃⁻¹ * X * G₃)⁻¹]
      _ = G₃⁻¹ * (X * (G₃ * (T * z) * G₃⁻¹) * X⁻¹) * G₃ := by group
  have e2 : G₃⁻¹ * (H * Z) * G₃ = T * Z * z := by
    rw [hH]
    calc G₃⁻¹ * (G₃ * (T * z) * G₃⁻¹ * Z) * G₃ = T * z * (G₃⁻¹ * (Z * G₃)) := by group
      _ = T * z * (G₃⁻¹ * (G₃ * Z)) := by rw [← hZ G₃]
      _ = T * (z * Z) := by group
      _ = T * (Z * z) := by rw [← hz Z]
      _ = T * Z * z := by group
  rw [hXZ, e2] at e1
  exact mul_right_cancel e1

private theorem minEndBC_injective' {d : ℕ} {k k' : Type*} [Field k] [Field k'] (ι : k →+* k') :
    Function.Injective (minEndBC (d := d) ι) := by
  intro A B h
  refine minEnd_ext fun b => Finsupp.ext fun c => ?_
  have h1 := congrArg (fun f : Module.End k' (Fin d →₀ k') => f (Finsupp.single b 1) c) h
  simp only [minEndBC_single, Finsupp.mapRange_apply] at h1
  exact ι.injective h1

private theorem minBC_injective'
    {k k' : Type} [Field k] [Field k'] (ι : k →+* k') :
    Function.Injective (minBC e6Data_valid ι) := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  apply minEndBC_injective' ι
  exact congrArg (fun x : e6Data_valid.minGroup k' =>
    ((x : (Module.End k' (Fin e6Data.d →₀ k'))ˣ) : Module.End k' (Fin e6Data.d →₀ k'))) e


private theorem exists_conj_diag_of_fixDim_36
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {h₀ : ModGL Tag.E6 K}
    (hh₀ : h₀ ∈ twistedE6InndiagGL K σ) (h3 : h₀ ^ 3 = 1)
    (hdim : twE6MatFixDim K σ ⟨h₀, hh₀⟩ = 36) :
    ∃ (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ),
      g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧ (∀ i, a i ^ 3 = 1) ∧
      (kernelRoots (rootCharHom a)).ncard = 30 ∧
      g0 * rootDiagUnit Tag.E6 a * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K)) h₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨u, hu⟩ : ∃ u : ModGL Tag.E6 (AlgebraicClosure K),
      u = baseChangeGL (algebraMap K (AlgebraicClosure K)) h₀ := ⟨_, rfl⟩
  have hup : u ^ 3 = 1 := by rw [hu, ← map_pow, h3, map_one]
  have huG : u ∈ adjointGroup Tag.E6 (AlgebraicClosure K) := by
    rw [hu]
    exact (map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two hn hK σ hσ
      (iterateFrobenius (AlgebraicClosure K) 2 n) (fun c => iterateFrobenius_def 2 n c)
      ⟨_, hh₀, rfl⟩).1
  obtain ⟨g0, hg0C, hg0T⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_conj_torusGroup_of_pow_eq_one
      Nat.prime_three monomialToralAt_E6_three (by decide : (2 : ℕ) ≠ 3)
      (isAlgebraic_zmod_algebraicClosure_of_finite K 2) huG hup
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg0T
  have hg0 : g0 * rootDiagUnit Tag.E6 a * g0⁻¹ = u := by
    rw [← ha]
    group
  have hap : ∀ i, a i ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
      have : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
        (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).map_pow a 3
      have h := conj_pow (a := g0⁻¹) (b := u) (i := 3)
      rw [inv_inv] at h
      rw [this, ← ha, h, hup, CFSG.LieType.Chevalley.rootDiagUnit_one]
      group
    have h2 : a ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  refine ⟨g0, a, hg0C, hap, ?_, hg0.trans hu⟩
  have h1 := KSNotAll24.twE6MatFixDim_eq_of_conj σ ⟨h₀, hh₀⟩ g0 a (hg0.trans hu)
  rw [hdim] at h1
  omega

private theorem eq_one_of_conj_minTorus
    {k : Type} [Field k] [Finite k] [CharP k 2] (u : Fin Tag.E6.rank → kˣ)
    (hu3 : ∀ j, e6RootParams u j ^ 3 = 1)
    (hk : (kernelRoots (rootCharHom (e6RootParams u))).ncard = 30) {g Z : e6Data_valid.minGroup k}
    (hZ : ((e6Isogeny k Z : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) = 1)
    (hgT : g * minTorus e6Data_valid k u * g⁻¹ = minTorus e6Data_valid k u * Z) : Z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup k →* ModGL Tag.E6 k,
      π = (adjointGroup Tag.E6 k).subtype.comp (e6Isogeny k) := ⟨_, rfl⟩
  have hπ₃a : ∀ g, π₃ g = ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) :=
    fun g => by rw [hπ₃]; rfl
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid k u := ⟨_, rfl⟩
  rw [← hT] at hgT
  have hπT : π₃ T = rootDiagUnit Tag.E6 (e6RootParams u) := by
    rw [hπ₃a, hT]
    exact e6Isogeny_minTorus u
  have hcC : π₃ g ∈ toralCentralizer Tag.E6 k (e6RootParams u) := by
    refine mem_toralCentralizer.2 ⟨by rw [hπ₃a]; exact (e6Isogeny k g).2, ?_⟩
    have hZ' : π₃ Z = 1 := by rw [hπ₃a]; exact hZ
    have h1 : π₃ g * π₃ T * (π₃ g)⁻¹ = π₃ T := by
      rw [← map_inv, ← map_mul, ← map_mul, hgT, map_mul, hZ', mul_one]
    rw [← hπT]
    calc π₃ T * π₃ g * (π₃ T)⁻¹ = (π₃ g * π₃ T * (π₃ g)⁻¹) * π₃ g * (π₃ T)⁻¹ := by rw [h1]
      _ = π₃ g := by group
  have hst := KSConn.e6_stab_le_kernelReflectionGroup_of_conn (e6RootParams u) hu3
    (by rw [hk]; simp)
  have hM : π₃ g ∈ toralRootGroup Tag.E6 k (e6RootParams u) := by
    rw [← toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 k (e6RootParams u) hst]
    exact hcC
  have hcomm := commute_minTorus_of_mem_toralRootGroup_char (p := 2) (by decide) u hM
    (hπ₃a g).symm
  rw [← hT] at hcomm
  have h1 : T * Z = T * 1 := by rw [← hgT, hcomm, mul_inv_cancel_right, mul_one]
  exact mul_left_cancel h1

private theorem exists_descent
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    {a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hker30 : (kernelRoots (rootCharHom a)).ncard = 30) :
    ∃ (K₃ : Subfield (AlgebraicClosure K)) (_ : Finite K₃) (ι₃ : K →+* K₃)
      (G₃ : e6Data_valid.minGroup K₃) (u₃ : Fin Tag.E6.rank → K₃ˣ),
      K₃.subtype.comp ι₃ = algebraMap K (AlgebraicClosure K) ∧
      baseChangeGL K₃.subtype ((e6Isogeny K₃ G₃ : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = g0 ∧
      (∀ j, u₃ j ^ 3 = 1) ∧ (∀ j, e6RootParams u₃ j ^ 3 = 1) ∧
      (kernelRoots (rootCharHom (e6RootParams u₃))).ncard = 30 ∧
      (fun i => Units.map K₃.subtype.toMonoidHom (e6RootParams u₃ i)) = a := by
  classical
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_three hK
  obtain ⟨ι, hιdef⟩ : ∃ ι : K →+* AlgebraicClosure K, ι = algebraMap K (AlgebraicClosure K) :=
    ⟨_, rfl⟩
  have hωb : orderOf (Units.map ι.toMonoidHom ω) = 3 := by
    rw [orderOf_injective _ (Units.map_injective ι.injective) ω]
    exact hω
  obtain ⟨x, hx, hx30, hxy⟩ := exists_inner_of_ncard_thirty hωb hap hker30
  obtain ⟨Eg, hEg⟩ := exists_finset_descent hg0C
  obtain ⟨K₃, hK₃, hEK₃, hιK₃⟩ := exists_finite_subfield_of_finset (K := K) Eg
  have : Finite K₃ := hK₃
  obtain ⟨g₃, hg₃C, hg₃⟩ := hEg K₃ hEK₃
  obtain ⟨ι₃, hιι⟩ : ∃ ι₃ : K →+* K₃, K₃.subtype.comp ι₃ = ι :=
    ⟨ι.codRestrict K₃ fun c => by rw [hιdef]; exact hιK₃ ⟨c, rfl⟩, RingHom.ext fun _ => rfl⟩
  obtain ⟨G₃, hG₃⟩ := e6Isogeny_surjective K₃ ⟨g₃, hg₃C⟩
  obtain ⟨ω₃, hω₃def⟩ : ∃ ω₃ : K₃ˣ, ω₃ = Units.map ι₃.toMonoidHom ω := ⟨_, rfl⟩
  have hω₃ : orderOf ω₃ = 3 := by
    rw [hω₃def, orderOf_injective _ (Units.map_injective ι₃.injective) ω]
    exact hω
  have hω₃3 : ω₃ ^ 3 = 1 := hω₃ ▸ pow_orderOf_eq_one ω₃
  obtain ⟨u₃, hu₃def⟩ : ∃ u₃ : Fin Tag.E6.rank → K₃ˣ,
      u₃ = SmallQ3.e6InnerParam ω₃ (SmallQ3.e6InnerCoords x) := ⟨_, rfl⟩
  have hcu : e6RootParams u₃ = SmallQ3.torV ω₃ x := by
    rw [hu₃def, SmallQ3.e6RootParams_e6InnerParam hω₃3, hxy]
  refine ⟨K₃, hK₃, ι₃, G₃, u₃, hιι.trans hιdef, by rw [hG₃, hg₃], fun j => ?_, fun j => ?_, ?_,
    ?_⟩
  · have hpow : u₃ ^ 3 = 1 := by
      rw [hu₃def, SmallQ3.e6InnerParam]
      refine list_prod_pow_eq_one _ fun t ht => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht
      rw [← pow_mul, mul_comm, pow_mul, ← Pi.mulSingle_pow, hω₃3, Pi.mulSingle_one, one_pow]
    exact congrFun hpow j
  · rw [hcu]
    change (ω₃ ^ (x j).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, hω₃3, one_pow]
  · rw [hcu, kernelRoots_torV hω₃, ncard_kernelRoots_eq_e6KerCount, hx30]
  · rw [hcu, ← hx]
    funext i
    have e : Units.map K₃.subtype.toMonoidHom ω₃ = Units.map ι.toMonoidHom ω := Units.ext (by
      rw [hω₃def]
      change K₃.subtype (ι₃ (ω : K)) = ι (ω : K)
      rw [← hιι]
      rfl)
    change Units.map K₃.subtype.toMonoidHom (ω₃ ^ (x i).val) =
      Units.map ι.toMonoidHom ω ^ (x i).val
    rw [map_pow, e]

private theorem exists_langLift
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {hhat : ↥(fixedGroup K σ.toRingHom)}
    (h3 : twistedIsogenyC hn hK σ.toRingHom hσ hhat ^ 3 = 1)
    (hdim : twE6FixDim K σ (twistedIsogenyC hn hK σ.toRingHom hσ hhat) = 36) :
    ∃ (K₃ : Subfield (AlgebraicClosure K)) (_ : Finite K₃) (ι₃ : K →+* K₃)
      (G₃ : e6Data_valid.minGroup K₃) (w : Fin Tag.E6.rank → K₃ˣ), (∀ j, w j ^ 3 = 1) ∧
      minBC e6Data_valid ι₃ hhat = G₃ * minTorus e6Data_valid K₃ w * G₃⁻¹ ∧
      ∀ X Z : e6Data_valid.minGroup K₃,
        ((e6Isogeny K₃ Z : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = 1 →
        X * minBC e6Data_valid ι₃ hhat * X⁻¹ = minBC e6Data_valid ι₃ hhat * Z → Z = 1 := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : ↥(fixedGroup K σ.toRingHom) →* ↥(twistedE6RootGroup K σ),
      π = twistedIsogenyC hn hK σ.toRingHom hσ := ⟨_, rfl⟩
  rw [← hπ] at h3 hdim
  obtain ⟨h₀, hh₀def⟩ : ∃ h₀ : ModGL Tag.E6 K,
      h₀ = ((π hhat : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := ⟨_, rfl⟩
  have hh₀ : h₀ ∈ twistedE6InndiagGL K σ := by
    rw [hh₀def]
    exact Subgroup.mem_sup_left (π hhat).2
  have hh₀3 : h₀ ^ 3 = 1 := by
    rw [hh₀def]
    change ((π hhat ^ 3 : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = 1
    rw [h3]
    rfl
  have hdim' : twE6MatFixDim K σ ⟨h₀, hh₀⟩ = 36 := by
    subst hh₀def
    exact hdim
  obtain ⟨g0, a, hg0C, hap, hker30, hg0⟩ :=
    exists_conj_diag_of_fixDim_36 hn hK σ hσ hh₀ hh₀3 hdim'
  obtain ⟨K₃, hK₃, ι₃, G₃, u₃, hιι, hπG, hu₃3, ha₃, hker₃, hpar⟩ :=
    exists_descent hK hg0C hap hker30
  have : Finite K₃ := hK₃
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : CharP K₃ 2 := Subfield.charP K₃ 2
  obtain ⟨π₃, hπ₃⟩ : ∃ π : e6Data_valid.minGroup K₃ →* ModGL Tag.E6 K₃,
      π = (adjointGroup Tag.E6 K₃).subtype.comp (e6Isogeny K₃) := ⟨_, rfl⟩
  have hπ₃a : ∀ g, π₃ g = ((e6Isogeny K₃ g : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) :=
    fun g => by rw [hπ₃]; rfl
  rw [← hπ₃a] at hπG
  have hbcπ : baseChangeGL K₃.subtype (π₃ (minBC e6Data_valid ι₃ hhat)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) h₀ := by
    rw [hπ₃a, e6Isogeny_minBC, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hιι, hh₀def,
      hπ]
    rfl
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid K₃ u₃ := ⟨_, rfl⟩
  have hbcT : baseChangeGL K₃.subtype (π₃ T) = rootDiagUnit Tag.E6 a := by
    rw [hπ₃a, hT, e6Isogeny_minTorus, baseChangeGL_rootDiagUnit, hpar]
  obtain ⟨hl, hhl⟩ : ∃ y, y = G₃⁻¹ * minBC e6Data_valid ι₃ hhat * G₃ := ⟨_, rfl⟩
  have hbchl : baseChangeGL K₃.subtype (π₃ hl) = rootDiagUnit Tag.E6 a := by
    simp only [hhl, map_mul, map_inv, hπG, hbcπ]
    rw [← hg0]
    group
  obtain ⟨z, hz⟩ : ∃ z, z = T⁻¹ * hl := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (e6Data_valid.minGroup K₃) := by
    refine SmallQ3.mem_center_of_isogeny_eq_one ?_
    have hTl : π₃ hl = π₃ T := baseChangeGL_injective K₃.subtype (hbchl.trans hbcT.symm)
    rw [← hπ₃a, hz, map_mul, map_inv, hTl, inv_mul_cancel]
  obtain ⟨v, hzv, hv3⟩ := SmallQ3.exists_minTorus_of_mem_center_E6 hzc
  have hH : minBC e6Data_valid ι₃ hhat = G₃ * (T * z) * G₃⁻¹ := by
    rw [hz, hhl]
    group
  refine ⟨K₃, hK₃, ι₃, G₃, u₃ * v, fun j => by rw [Pi.mul_apply, mul_pow, hu₃3, hv3, one_mul],
    by rw [hH, map_mul, ← hT, ← hzv], fun X Z hZ hXZ => ?_⟩
  rw [hT] at hH
  exact eq_one_of_conj_minTorus u₃ ha₃ hker₃ hZ
    (conj_eq_mul_of_conj hzc (SmallQ3.mem_center_of_isogeny_eq_one hZ) hH hXZ)

end CFSG.StandardType.KG87B

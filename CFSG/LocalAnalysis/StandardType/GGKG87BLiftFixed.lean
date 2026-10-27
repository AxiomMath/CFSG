module

public import CFSG.LocalAnalysis.StandardType.GGKG87BSCBridge
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs

import all CFSG.LocalAnalysis.StandardType.GGKG87BLiftFixedLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjLift
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityProof
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.SeitzReduction.F4Pilot (twistedIsogenyC)

private theorem exists_frobenius_ext {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {δ : K ≃+* K} (hδ : ∀ c : K, c ^ 3 = 1 → δ c = c)
    {k : Type} [Field k] [CharP k 2] (ι₃ : K →+* k) :
    ∃ δ₃ : k →+* k, δ₃.comp ι₃ = ι₃.comp δ.toRingHom ∧
      ∀ v : kˣ, v ^ 3 = 1 → Units.map δ₃.toMonoidHom v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcomm : ∀ x : ZMod 2, δ (algebraMap (ZMod 2) K x) = algebraMap (ZMod 2) K x := fun x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((δ : K →+* K).comp (algebraMap (ZMod 2) K))
      (algebraMap (ZMod 2) K)) x
  obtain ⟨j, hj⟩ : ∃ j : ℕ, ∀ c : K, δ c = c ^ 2 ^ j := by
    obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K
      (AlgEquiv.ofRingEquiv hcomm)
    rw [Nat.card_zmod] at hj
    exact ⟨j, hj⟩
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_three hK
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  have hδω : ω ^ 2 ^ j = ω := Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← hj]
    exact hδ _ (by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]))
  rw [pow_eq_pow_mod _ hω3] at hδω
  have hj3 : 2 ^ j % 3 = 1 := by
    have hlt := Nat.mod_lt (2 ^ j) (show 3 > 0 by norm_num)
    interval_cases hm : 2 ^ j % 3
    · exact absurd (hδω.symm.trans (pow_zero ω)) hω1
    · rfl
    · exfalso
      apply hω1
      have : ω * ω = ω * 1 := by rw [mul_one, ← pow_two, hδω]
      exact mul_left_cancel this
  refine ⟨iterateFrobenius k 2 j, RingHom.ext fun c => ?_, fun v hv => Units.ext ?_⟩
  · change iterateFrobenius k 2 j (ι₃ c) = ι₃ (δ c)
    rw [iterateFrobenius_def, hj, map_pow]
  · change iterateFrobenius k 2 j (v : k) = v
    rw [iterateFrobenius_def, ← Units.val_pow_eq_pow_val, pow_eq_pow_mod _ hv, hj3, pow_one]

private theorem eq_of_inv_mul_mem_center {L G : Type} [Group L] [Group G]
    (hperf : commutator L = ⊤) (f g : L →* G) (h : ∀ l, (f l)⁻¹ * g l ∈ Subgroup.center G)
    (l : L) : f l = g l := by
  let C : L →* Subgroup.center G :=
    { toFun := fun l => ⟨(f l)⁻¹ * g l, h l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (f (x * y))⁻¹ * g (x * y) = (f x)⁻¹ * g x * ((f y)⁻¹ * g y)
        have hz := Subgroup.mem_center_iff.1 (h x) (f y)⁻¹
        rw [map_mul, map_mul]
        calc (f x * f y)⁻¹ * (g x * g y) = (f y)⁻¹ * ((f x)⁻¹ * g x) * g y := by group
          _ = (f x)⁻¹ * g x * (f y)⁻¹ * g y := by rw [hz]
          _ = (f x)⁻¹ * g x * ((f y)⁻¹ * g y) := by group) }
  have hl : l ∈ C.ker := Abelianization.commutator_subset_ker C (by rw [hperf]; trivial)
  have h1 : (f l)⁻¹ * g l = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hl)
  exact inv_mul_eq_one.1 h1

private theorem units_map_entrywiseHom_eq_baseChangeGL'
    {K : Type} [Field K] {τ : Tag}
    (δ : K →+* K) (g : ModGL τ K) : Units.map (entrywiseHom δ) g = baseChangeGL δ g :=
  Units.ext ((baseChange_entrywise δ _).unique (baseChange_baseChangeEnd δ _))

private theorem twistedIsogenyC_symm_apply
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n) {L' : Type} [Group L']
    {ψ : L' →* TwE6Delta.RecipeR K n} (α : ↥(fixedGroup K σ.toRingHom) ≃* L')
    (hα : ∀ u, ψ (α u) = ε (twistedIsogenyC hn hK σ.toRingHom hσ u)) (l : L') :
    twistedIsogenyC hn hK σ.toRingHom hσ (α.symm l) = ε.symm (ψ l) := by
  have := hα (α.symm l)
  rw [α.apply_symm_apply] at this
  rw [this, ε.symm_apply_apply]

theorem pow_three_eq_one_of_fixDim_36
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (h3 : 3 ∣ Nat.card ψ.ker) {k : L'} (hk3 : ψ k ^ 3 = 1)
    (hdim : twE6FixDim K σ (ε.symm (ψ k)) = 36) :
    k ^ 3 = 1 := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨α, hα⟩ := exists_mulEquiv_fixedGroup hn hK σ hσ ε hψ hker hperf h3
  have hπ := twistedIsogenyC_symm_apply hn1 hK σ hσ ε α hα
  obtain ⟨K₃, hK₃, ι₃, G₃, w, hw3, hH, -⟩ := exists_langLift hn1 hK σ hσ (hhat := α.symm k)
    (by rw [hπ, ← map_pow, hk3, map_one]) (by rw [hπ]; exact hdim)
  have hT3 : minTorus e6Data_valid K₃ w ^ 3 = 1 := by
    rw [← map_pow]
    have : w ^ 3 = 1 := funext fun j => hw3 j
    rw [this, map_one]
  have hB3 : minBC e6Data_valid ι₃ ((α.symm k : e6Data_valid.minGroup K) ^ 3) = 1 := by
    rw [map_pow, hH, conj_pow, hT3, mul_one, mul_inv_cancel]
  have hk' : α.symm k ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact minBC_injective' ι₃ (hB3.trans (map_one _).symm))
  calc k ^ 3 = α (α.symm k ^ 3) := by rw [map_pow, α.apply_symm_apply]
    _ = 1 := by rw [hk', map_one]

theorem commute_of_fixDim_36
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (h3 : 3 ∣ Nat.card ψ.ker) {k k' : L'} (hk3 : ψ k ^ 3 = 1)
    (hdim : twE6FixDim K σ (ε.symm (ψ k)) = 36) (hcomm : ψ k * ψ k' = ψ k' * ψ k) :
    k * k' = k' * k := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨α, hα⟩ := exists_mulEquiv_fixedGroup hn hK σ hσ ε hψ hker hperf h3
  have hπ := twistedIsogenyC_symm_apply hn1 hK σ hσ ε α hα
  obtain ⟨K₃, hK₃, ι₃, -, -, -, -, hrig⟩ := exists_langLift hn1 hK σ hσ (hhat := α.symm k)
    (by rw [hπ, ← map_pow, hk3, map_one]) (by rw [hπ]; exact hdim)
  have : Finite K₃ := hK₃
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L' →* e6Data_valid.minGroup K₃, Φ = (minBC e6Data_valid ι₃).comp
      ((fixedGroup K σ.toRingHom).subtype.comp α.symm.toMonoidHom) := ⟨_, rfl⟩
  have hΦa : ∀ l, Φ l = minBC e6Data_valid ι₃ (α.symm l) := fun l => by rw [hΦ]; rfl
  obtain ⟨c, hc⟩ : ∃ c, c = k⁻¹ * k' * k * k'⁻¹ := ⟨_, rfl⟩
  have hψc : ψ c = 1 := by
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (ψ k'), ← hcomm]
    group
  have hZ : ((e6Isogeny K₃ (Φ c) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = 1 := by
    rw [hΦa, e6Isogeny_minBC]
    have e : ((e6Isogeny K (α.symm c) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = 1 := by
      change ((twistedIsogenyC hn1 hK σ.toRingHom hσ (α.symm c) : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) = 1
      rw [hπ, hψc, map_one, OneMemClass.coe_one]
    rw [e, map_one]
  have hXZ : Φ k' * minBC e6Data_valid ι₃ (α.symm k) * (Φ k')⁻¹ =
      minBC e6Data_valid ι₃ (α.symm k) * Φ c := by
    rw [← hΦa, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hc]
    congr 1
    group
  have hc1 : Φ c = 1 := hrig _ _ hZ hXZ
  have hc1' : c = 1 := by
    rw [hΦa] at hc1
    have h1 : α.symm c = 1 :=
      Subtype.ext (minBC_injective' ι₃ (hc1.trans (map_one _).symm))
    have h2 := congrArg α h1
    rwa [α.apply_symm_apply, map_one] at h2
  rw [hc] at hc1'
  have h2 : k' * k * k'⁻¹ = k := by
    calc k' * k * k'⁻¹ = k * (k⁻¹ * k' * k * k'⁻¹) := by group
      _ = k := by rw [hc1', mul_one]
  calc k * k' = k' * k * k'⁻¹ * k' := by rw [h2]
    _ = k' * k := by group

theorem apply_eq_self_of_fixDim_36
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (h3 : 3 ∣ Nat.card ψ.ker) {δ : K ≃+* K} (hδ : ∀ c : K, c ^ 3 = 1 → δ c = c)
    {b : MulAut L'}
    (hb : ∀ l, MulAut.congr ε (fieldActor (t := TwistTag.E6) σ δ) (ψ l) = ψ (b l))
    {k₀ : L'} (hk₀3 : ψ k₀ ^ 3 = 1) (hbk₀ : ψ (b k₀) = ψ k₀)
    (hdim : twE6FixDim K σ (ε.symm (ψ k₀)) = 36) :
    b k₀ = k₀ := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨α, hα⟩ := exists_mulEquiv_fixedGroup hn hK σ hσ ε hψ hker hperf h3
  have hπ := twistedIsogenyC_symm_apply hn1 hK σ hσ ε α hα
  obtain ⟨K₃, hK₃, ι₃, G₃, w, hw3, hH, hrig⟩ := exists_langLift hn1 hK σ hσ
    (hhat := α.symm k₀) (by rw [hπ, ← map_pow, hk₀3, map_one]) (by rw [hπ]; exact hdim)
  have : Finite K₃ := hK₃
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : CharP K₃ 2 := Subfield.charP K₃ 2
  obtain ⟨δ₃, hδι, hδ₃⟩ := exists_frobenius_ext hK hδ ι₃
  obtain ⟨T, hT⟩ : ∃ T, T = minTorus e6Data_valid K₃ w := ⟨_, rfl⟩
  have hδT : minBC e6Data_valid δ₃ T = T := by
    rw [hT, SmallQ3.minBC_minTorus_E6]
    congr 1
    funext i
    exact hδ₃ _ (hw3 i)
  rw [← hT] at hH
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L' →* e6Data_valid.minGroup K₃, Φ = (minBC e6Data_valid ι₃).comp
      ((fixedGroup K σ.toRingHom).subtype.comp α.symm.toMonoidHom) := ⟨_, rfl⟩
  have hΦa : ∀ l, Φ l = minBC e6Data_valid ι₃ (α.symm l) := fun l => by rw [hΦ]; rfl
  obtain ⟨y, hy⟩ : ∃ y : L' → ModGL Tag.E6 K,
      ∀ l, y l = ((ε.symm (ψ l) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) :=
    ⟨_, fun _ => rfl⟩
  have hΦπ : ∀ l, ((e6Isogeny K₃ (Φ l) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) =
      baseChangeGL ι₃ (y l) := fun l => by
    rw [hΦa, e6Isogeny_minBC, hy, ← hπ l]
    rfl
  have hyb : ∀ l, y (b l) = baseChangeGL δ.toRingHom (y l) := fun l => by
    have hψb : ε.symm (ψ (b l)) = fieldActor (t := TwistTag.E6) σ δ (ε.symm (ψ l)) := by
      rw [← hb l, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [hy, hy, hψb]
    exact units_map_entrywiseHom_eq_baseChangeGL' δ.toRingHom _
  have hC : ∀ l, (minBC e6Data_valid δ₃ (Φ l))⁻¹ * Φ (b l) ∈
      Subgroup.center (e6Data_valid.minGroup K₃) := fun l => by
    refine SmallQ3.mem_center_of_isogeny_eq_one ?_
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e6Isogeny_minBC, hΦπ, hΦπ, hyb,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hδι, inv_mul_cancel]
  have hkey : ∀ l, minBC e6Data_valid δ₃ (Φ l) = Φ (b l) := fun l =>
    eq_of_inv_mul_mem_center hperf ((minBC e6Data_valid δ₃).comp Φ) (Φ.comp b.toMonoidHom)
      (fun l => hC l) l
  obtain ⟨z, hzdef⟩ : ∃ z, z = k₀⁻¹ * b k₀ := ⟨_, rfl⟩
  have hψz : ψ z = 1 := by rw [hzdef, map_mul, map_inv, hbk₀, inv_mul_cancel]
  have hbz : b k₀ = k₀ * z := by rw [hzdef, mul_inv_cancel_left]
  obtain ⟨G', hG'⟩ : ∃ G', G' = minBC e6Data_valid δ₃ G₃ := ⟨_, rfl⟩
  have hXH : (G' * G₃⁻¹) * minBC e6Data_valid ι₃ (α.symm k₀) * (G' * G₃⁻¹)⁻¹ =
      minBC e6Data_valid ι₃ (α.symm k₀) * Φ z := by
    have e1 : minBC e6Data_valid δ₃ (Φ k₀) = G' * T * G'⁻¹ := by
      rw [hΦa, hH, map_mul, map_mul, map_inv, hδT, hG']
    have e2 : (G' * G₃⁻¹) * minBC e6Data_valid ι₃ (α.symm k₀) * (G' * G₃⁻¹)⁻¹ =
        G' * T * G'⁻¹ := by
      rw [hH]
      group
    rw [e2, ← e1, hkey, hbz, map_mul, hΦa]
  have hZ : ((e6Isogeny K₃ (Φ z) : adjointGroup Tag.E6 K₃) : ModGL Tag.E6 K₃) = 1 := by
    rw [hΦπ, hy, hψz, map_one, OneMemClass.coe_one]
    exact map_one _
  have hz1 : Φ z = 1 := hrig _ _ hZ hXH
  have hz1' : z = 1 := by
    rw [hΦa] at hz1
    have h1 : α.symm z = 1 :=
      Subtype.ext (minBC_injective' ι₃ (hz1.trans (map_one _).symm))
    have h2 := congrArg α h1
    rwa [α.apply_symm_apply, map_one] at h2
  rw [hbz, hz1', mul_one]

end CFSG.StandardType.KG87B

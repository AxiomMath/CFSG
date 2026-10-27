module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
public import CFSG.LieType.Chevalley.GraphFixedMonomialQuotient

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace TableBExc.E6Three

section Act

variable {τ : Tag} {p : ℕ}

theorem weyl_smul_eq_sum (w : WeylGroup τ) (v : Fin τ.rank → ℤ) :
    w • v = ∑ k, v k • (w • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun j => if k = j then (1 : ℤ) else 0) = Pi.single k 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm]

variable (τ p) in
@[expose] noncomputable def adAct (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    Fin τ.rank → ZMod p :=
  fun i => ∑ j, (((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j : ℤ) : ZMod p) * x j

theorem adAct_one (x : Fin τ.rank → ZMod p) : adAct τ p 1 x = x := by
  funext i
  simp [adAct, Pi.single_apply]

theorem adAct_mul (w w' : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    adAct τ p (w * w') x = adAct τ p w (adAct τ p w' x) := by
  funext i
  simp only [adAct, mul_inv_rev, mul_smul]
  rw [weyl_smul_eq_sum w'⁻¹ (w⁻¹ • Pi.single i 1)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (τ p) in
@[expose] noncomputable def adPerm : WeylGroup τ →* Equiv.Perm (Fin τ.rank → ZMod p) where
  toFun w :=
    { toFun := adAct τ p w
      invFun := adAct τ p w⁻¹
      left_inv x := by rw [← adAct_mul, inv_mul_cancel, adAct_one]
      right_inv x := by rw [← adAct_mul, mul_inv_cancel, adAct_one] }
  map_one' := Equiv.ext fun x => adAct_one x
  map_mul' w w' := Equiv.ext fun x => adAct_mul w w' x

theorem adPerm_apply (w : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    adPerm τ p w x = adAct τ p w x :=
  rfl

variable (τ p) in
@[expose] def adRefl (i : Fin τ.rank) (x : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  x - x i • fun j => ((τ.cartan i j : ℤ) : ZMod p)

variable (τ p) in
@[expose] def adWord (ω : List (Fin τ.rank)) (x : Fin τ.rank → ZMod p) : Fin τ.rank → ZMod p :=
  ω.foldr (adRefl τ p) x

theorem adAct_simple (i : Fin τ.rank) (x : Fin τ.rank → ZMod p) :
    adAct τ p (simple τ i) x = adRefl τ p i x := by
  funext k
  rw [adAct, (coxeterSystem τ).inv_simple, simple_smul]
  simp only [reflect, adRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
    Int.cast_mul, sub_mul, Finset.sum_sub_distrib]
  simp [Pi.single_apply, mul_comm]

theorem adWord_eq_adAct (ω : List (Fin τ.rank)) (x : Fin τ.rank → ZMod p) :
    adWord τ p ω x = adAct τ p ((coxeterSystem τ).wordProd ω) x := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, adAct_one]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, adAct_mul, ← ih, adAct_simple]
    rfl

end Act

section Minor

variable {τ : Tag} {p : ℕ}

variable (τ p) in
@[expose] noncomputable def adWordLin (ω : List (Fin τ.rank)) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) :=
  ω.foldr (fun i L => (LinearMap.id - (LinearMap.proj i).smulRight
    (fun j => ((τ.cartan i j : ℤ) : ZMod p))).comp L) LinearMap.id

theorem adWordLin_apply (ω : List (Fin τ.rank)) (x : Fin τ.rank → ZMod p) :
    adWordLin τ p ω x = adWord τ p ω x := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change ((LinearMap.id - (LinearMap.proj i).smulRight
      (fun j => ((τ.cartan i j : ℤ) : ZMod p))).comp (adWordLin τ p ω)) x =
        adRefl τ p i (adWord τ p ω x)
    rw [LinearMap.comp_apply, ih, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, LinearMap.proj_apply]
    rfl

theorem card_fix_adWord_le [Fact p.Prime] (ω : List (Fin τ.rank)) {k : ℕ}
    (R C : Fin k → Fin τ.rank) (hC : Function.Injective C) (N : Fin k → Fin k → ZMod p)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (adWord τ p ω (Pi.single (C b) 1) (R c) -
      if R c = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin τ.rank → ZMod p // adWord τ p ω x = x} ≤ p ^ (τ.rank - k) := by
  have h := card_fix_le_of_leftInverse (adWordLin τ p ω) R C hC N
    (by simpa only [adWordLin_apply] using hN)
  simp only [adWordLin_apply, ZMod.card] at h
  exact h

theorem card_fixAll_adWord_le [Fact p.Prime] {ι : Type*} (ω : ι → List (Fin τ.rank)) {k : ℕ}
    (R : Fin k → ι × Fin τ.rank) (C : Fin k → Fin τ.rank) (hC : Function.Injective C)
    (N : Fin k → Fin k → ZMod p)
    (hN : ∀ a b : Fin k, ∑ c, N a c * (adWord τ p (ω (R c).1) (Pi.single (C b) 1) (R c).2 -
      if (R c).2 = C b then 1 else 0) = if a = b then 1 else 0) :
    Nat.card {x : Fin τ.rank → ZMod p // ∀ t, adWord τ p (ω t) x = x} ≤ p ^ (τ.rank - k) := by
  have h := Three.card_fixAll_le_of_leftInverse (fun t => adWordLin τ p (ω t)) R C hC N
    (by simpa only [adWordLin_apply] using hN)
  simp only [adWordLin_apply, ZMod.card] at h
  exact h

end Minor

section Zeta

variable {τ : Tag} {p : ℕ} [NeZero p] {K : Type} [Field K]

@[expose] def zetaVec (ζ : Kˣ) (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) : Fin τ.rank → Kˣ :=
  fun i => zmodPowHom ζ hζ (.ofAdd (x i))

theorem zetaVec_apply (ζ : Kˣ) (hζ : ζ ^ p = 1) (x : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    zetaVec ζ hζ x i = ζ ^ (x i).val :=
  rfl

theorem zmodPowHom_zpow (ζ : Kˣ) (hζ : ζ ^ p = 1) (n : ℤ) (y : ZMod p) :
    zmodPowHom ζ hζ (.ofAdd y) ^ n = zmodPowHom ζ hζ (.ofAdd ((n : ZMod p) * y)) := by
  rw [← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]

theorem weylTuple_zetaVec (ζ : Kˣ) (hζ : ζ ^ p = 1) (w : WeylGroup τ)
    (x : Fin τ.rank → ZMod p) : weylTuple w (zetaVec ζ hζ x) = zetaVec ζ hζ (adAct τ p w x) := by
  funext i
  simp only [weylTuple, zetaVec, adAct, rootChar]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zmodPowHom_zpow]

theorem zetaVec_injective {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) :
    Function.Injective (zetaVec (τ := τ) ζ hζ) := by
  intro x y h
  funext i
  have h1 := congrFun h i
  exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ h1)

theorem exists_zetaVec_eq {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {a : Fin τ.rank → Kˣ} (ha : a ^ p = 1) : ∃ x, zetaVec ζ hζ x = a := by
  have hai : ∀ i, a i ^ p = 1 := fun i => by simpa using congrFun ha i
  choose m hm using fun i =>
    CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo (hai i)
  exact ⟨m, funext hm⟩

end Zeta

section Monomial

variable {τ : Tag} {K : Type} [Field K]

theorem monomial_conj_rootDiagUnit_weylTuple {x : ModGL τ K} (hx : x ∈ monomialSubgroup τ K)
    {w : WeylGroup τ} (hxw : MapsRootLines x w) (b : Fin τ.rank → Kˣ) :
    x * rootDiagUnit τ b * x⁻¹ = rootDiagUnit τ (weylTuple w b) := by
  obtain ⟨w', k, hk, hxk⟩ := monomialSubgroup_le_torusWeylCosets hx
  have hw : w' = w := (mapsRootLines_mul_canonicalRep hk w').unique (hxk ▸ hxw)
  subst hw
  rw [hxk]
  have h3 := canonicalRep_conj_rootDiagUnit (K := K) w' b
  have h4 := rootDiagUnit_mul_comm_of_mem_torusGroup (weylTuple w' b) hk
  calc k * canonicalRep (coxeterSystem τ) K w' * rootDiagUnit τ b *
        (k * canonicalRep (coxeterSystem τ) K w')⁻¹ =
      k * (canonicalRep (coxeterSystem τ) K w' * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w')⁻¹) * k⁻¹ := by group
    _ = rootDiagUnit τ (weylTuple w' b) := by rw [h3, ← h4, mul_inv_cancel_right]

end Monomial

end TableBExc.E6Three

end CFSG.StandardType

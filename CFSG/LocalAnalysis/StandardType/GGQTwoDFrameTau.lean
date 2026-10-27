module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameStd
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxRefl

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

@[expose] noncomputable def dNeg (m : ℕ) (a : Fin m) : DVec m ≃ₗ[ZMod 3] DVec m :=
  ZS.diagMap 3 (dBasis m) (fun k => if k = a then -1 else 1)

theorem dNeg_basis (m : ℕ) (a i : Fin m) :
    dNeg m a (dBasis m i) = (if i = a then (-1 : ZMod 3) else 1) • dBasis m i := by
  rw [dNeg, ZS.diagMap_apply_basis]
  by_cases h : i = a <;> simp [h, Units.val_neg]

theorem dNeg_apply_vec (m : ℕ) (a : Fin m) (v : DVec m) :
    dNeg m a v = v - (2 * v a) • dBasis m a := by
  have hfx : ((2 : ZMod 3) • (LinearMap.proj a : DVec m →ₗ[ZMod 3] ZMod 3))
      (dBasis m a) = 2 := by
    simp [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
      Pi.single_eq_same]
  have hrefl : dNeg m a = Module.reflection hfx := by
    refine (dBasis m).ext' fun i => ?_
    rw [Module.reflection_apply, dNeg_basis]
    by_cases h : i = a
    · subst h
      rw [if_pos rfl]
      simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dBasis,
        Pi.basisFun_apply, Pi.single_eq_same, mul_one]
      module
    · rw [if_neg h]
      have hf : ((2 : ZMod 3) • (LinearMap.proj a : DVec m →ₗ[ZMod 3] ZMod 3))
          (dBasis m i) = 0 := by
        simp [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dBasis,
          Pi.basisFun_apply, Pi.single_apply, if_neg (Ne.symm h)]
      rw [hf, zero_smul, sub_zero, one_smul]
  rw [hrefl, Module.reflection_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem dTau_basis (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) (i : Fin m) :
    dTau m ε a b (dBasis m i) =
      (if i = a ∨ i = b then dSgn ε else 1) • dBasis m (Equiv.swap a b i) := by
  by_cases hia : i = a
  · subst hia
    rw [dTau_apply_left m ε hab, Equiv.swap_apply_left]
    simp [dSgn]
  · by_cases hib : i = b
    · subst hib
      rw [dTau_apply_right m ε hab, Equiv.swap_apply_right]
      simp [dSgn]
    · rw [dTau_apply_of_ne m ε hia hib, Equiv.swap_apply_of_ne_of_ne hia hib]
      simp [hia, hib]

section Tau

variable {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ}
  (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)

@[expose] noncomputable def tauIota : Additive ↥Bs ≃+ DVec (n + 1) where
  toFun x i := Multiplicative.toAdd (τ.symm (Additive.toMul x) i)
  invFun v := Additive.ofMul (τ fun i => Multiplicative.ofAdd (v i))
  left_inv x := by
    apply Additive.toMul.injective
    simp
  right_inv v := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, toMul_add, map_mul, Pi.mul_apply, toAdd_mul]

theorem tauIota_ofMul_tau (f : Fin (n + 1) → Multiplicative (ZMod 3)) :
    tauIota τ (Additive.ofMul (τ f)) = fun i => Multiplicative.toAdd (f i) := by
  funext i
  change Multiplicative.toAdd (τ.symm (Additive.toMul (Additive.ofMul (τ f))) i) =
    Multiplicative.toAdd (f i)
  rw [toMul_ofMul, MulEquiv.symm_apply_apply]

theorem ggLin_tauIota_basis_iff (a : MulAut ↥Bs) (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) :
    (∀ (f : Fin (n + 1) → Multiplicative (ZMod 3)) (i : Fin (n + 1)),
        Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)) ↔
      ∀ i, ggLin (p := 3) (tauIota τ) a (dBasis (n + 1) i) = c i • dBasis (n + 1) (σ i) := by
  have hpoint :
      (∀ (f : Fin (n + 1) → Multiplicative (ZMod 3)) (i : Fin (n + 1)),
          Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)) ↔
        ∀ (v : DVec (n + 1)) (i : Fin (n + 1)),
          ggLin (p := 3) (tauIota τ) a v (σ i) = c i * v i := by
    constructor
    · intro hf v i
      have hv : v = tauIota τ (Additive.ofMul (τ (fun k => Multiplicative.ofAdd (v k)))) := by
        rw [tauIota_ofMul_tau]
        rfl
      have key : ggLin (p := 3) (tauIota τ) a v =
          tauIota τ (Additive.ofMul (a (τ (fun k => Multiplicative.ofAdd (v k))))) := by
        conv_lhs => rw [hv]
        rw [ggLin_apply_ofMul]
      rw [key]
      change Multiplicative.toAdd
        (τ.symm (a (τ (fun k => Multiplicative.ofAdd (v k)))) (σ i)) = c i * v i
      rw [hf (fun k => Multiplicative.ofAdd (v k)) i]
      simp
    · intro hv f i
      have hh := hv (tauIota τ (Additive.ofMul (τ f))) i
      rw [ggLin_apply_ofMul, tauIota_ofMul_tau] at hh
      exact hh
  rw [hpoint]
  constructor
  · intro hv i
    funext j
    by_cases hj : j = σ i
    · subst hj
      rw [hv (dBasis (n + 1) i) i]
      simp only [dBasis, Pi.basisFun_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
        if_pos rfl]
    · have h0 := hv (dBasis (n + 1) i) (σ.symm j)
      rw [Equiv.apply_symm_apply] at h0
      rw [h0]
      have hne : i ≠ σ.symm j := fun hc => hj (by rw [hc, Equiv.apply_symm_apply])
      have hL : (dBasis (n + 1) i) (σ.symm j) = 0 := by
        rw [dBasis, Pi.basisFun_apply, Pi.single_apply, if_neg (Ne.symm hne)]
      have hR : (c i • dBasis (n + 1) (σ i)) j = 0 := by
        rw [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_apply, if_neg hj, smul_zero]
      rw [hL, hR, mul_zero]
  · intro hb v i
    have hv : v = ∑ k, v k • dBasis (n + 1) k := by
      conv_lhs => rw [← (dBasis (n + 1)).sum_equivFun v]
      simp only [dBasis, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
    conv_lhs => rw [hv]
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, hb, smul_eq_mul]
    rw [Finset.sum_eq_single i
      (fun k _ hki => by
        rw [dBasis, Pi.basisFun_apply, Pi.single_apply,
          if_neg (Ne.symm (fun hc => hki (σ.injective hc))), mul_zero, mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [dBasis, Pi.basisFun_apply, Pi.single_apply, if_pos rfl, mul_one]
    ring

theorem ggLinInv_mem_automizer_d {X : Subgroup G} (hmod : HdRo7D.DCoordModel 3 Bs X n τ)
    {P : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (hσ : σ 0 = 0) (hc0 : c 0 = 1) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hprod : ∏ i, c i = 1) (hP : ∀ i, P (dBasis (n + 1) i) = c i • dBasis (n + 1) (σ i)) :
    ggLinInv (p := 3) (tauIota τ) P ∈ ggAutomizer X Bs := by
  refine (hmod (ggLinInv (p := 3) (tauIota τ) P)).mpr ⟨σ, c, hσ, hc0, hc, hprod, ?_⟩
  exact (ggLin_tauIota_basis_iff τ (ggLinInv (p := 3) (tauIota τ) P) σ c).mpr
    (fun i => by rw [ggLin_ggLinInv]; exact hP i)

theorem ggLinInv_mem_automizer_c2 {X : Subgroup G} (hmod : HdRo7C.C2CoordModel 3 Bs X n τ)
    {P : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (hσ : σ 0 = 0) (hc0 : c 0 = 1) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hP : ∀ i, P (dBasis (n + 1) i) = c i • dBasis (n + 1) (σ i)) :
    ggLinInv (p := 3) (tauIota τ) P ∈ ggAutomizer X Bs := by
  refine (hmod (ggLinInv (p := 3) (tauIota τ) P)).mpr ⟨σ, c, hσ, hc0, hc, ?_⟩
  exact (ggLin_tauIota_basis_iff τ (ggLinInv (p := 3) (tauIota τ) P) σ c).mpr
    (fun i => by rw [ggLin_ggLinInv]; exact hP i)

theorem ggLinInv_dTau_mem_automizer_d {X : Subgroup G} (hmod : HdRo7D.DCoordModel 3 Bs X n τ)
    (ε : Bool) {a b : Fin (n + 1)} (ha : 0 < a.val) (hb : 0 < b.val) (hab : a ≠ b) :
    ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε a b) ∈ ggAutomizer X Bs := by
  have ha0 : (0 : Fin (n + 1)) ≠ a := by
    intro h
    rw [← h] at ha
    simp at ha
  have hb0 : (0 : Fin (n + 1)) ≠ b := by
    intro h
    rw [← h] at hb
    simp at hb
  refine ggLinInv_mem_automizer_d (n := n) (τ := τ) (X := X) (hmod := hmod)
    (P := dTau (n + 1) ε a b) (σ := Equiv.swap a b)
    (c := fun i => if i = a ∨ i = b then dSgn ε else 1)
    (Equiv.swap_apply_of_ne_of_ne ha0 hb0) ?_ ?_ ?_ (dTau_basis (n + 1) ε hab)
  · rw [if_neg (fun h => h.elim ha0 hb0)]
  · intro i
    by_cases h : i = a ∨ i = b
    · rw [if_pos h]
      cases ε <;> simp [dSgn]
    · rw [if_neg h]; exact Or.inl rfl
  · rw [Finset.prod_eq_mul_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab]
    · rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
      cases ε <;> decide
    · intro k _ hk
      rw [if_neg (fun h => h.elim hk.1 hk.2)]

theorem ggLinInv_dTau_mem_automizer_c2 {X : Subgroup G} (hmod : HdRo7C.C2CoordModel 3 Bs X n τ)
    (ε : Bool) {a b : Fin (n + 1)} (ha : 0 < a.val) (hb : 0 < b.val) (hab : a ≠ b) :
    ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε a b) ∈ ggAutomizer X Bs := by
  have ha0 : (0 : Fin (n + 1)) ≠ a := by
    intro h
    rw [← h] at ha
    simp at ha
  have hb0 : (0 : Fin (n + 1)) ≠ b := by
    intro h
    rw [← h] at hb
    simp at hb
  refine ggLinInv_mem_automizer_c2 (n := n) (τ := τ) (X := X) (hmod := hmod)
    (P := dTau (n + 1) ε a b) (σ := Equiv.swap a b)
    (c := fun i => if i = a ∨ i = b then dSgn ε else 1)
    (Equiv.swap_apply_of_ne_of_ne ha0 hb0) ?_ ?_ (dTau_basis (n + 1) ε hab)
  · rw [if_neg (fun h => h.elim ha0 hb0)]
  · intro i
    by_cases h : i = a ∨ i = b
    · rw [if_pos h]
      cases ε <;> simp [dSgn]
    · rw [if_neg h]; exact Or.inl rfl

theorem ggLinInv_dNeg_mem_automizer_c2 {X : Subgroup G} (hmod : HdRo7C.C2CoordModel 3 Bs X n τ)
    {a : Fin (n + 1)} (ha : 0 < a.val) :
    ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a) ∈ ggAutomizer X Bs := by
  have ha0 : (0 : Fin (n + 1)) ≠ a := by
    intro h
    rw [← h] at ha
    simp at ha
  refine ggLinInv_mem_automizer_c2 (n := n) (τ := τ) (X := X) (hmod := hmod)
    (P := dNeg (n + 1) a) (σ := 1) (c := fun i => if i = a then -1 else 1)
    rfl ?_ ?_ (dNeg_basis (n + 1) a)
  · rw [if_neg ha0]
  · intro i
    by_cases h : i = a
    · rw [if_pos h]; exact Or.inr rfl
    · rw [if_neg h]; exact Or.inl rfl

theorem ggIsReflection_ggLinInv_dTau (ε : Bool) {a b : Fin (n + 1)} (hab : a ≠ b) :
    GGIsReflection 3 (ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) ε a b)) := by
  refine ggIsReflection_of_eq_reflection (p := 3) (by decide) (tauIota τ)
    (x := dRootAB (n + 1) ε a b) (f := dFormAB (n + 1) ε a b)
    (dFormAB_dRootAB (n + 1) ε hab) ?_
  rw [ggLin_ggLinInv]
  refine LinearEquiv.ext fun v => ?_
  rw [dTau_apply_vec (n + 1) ε hab v, Module.reflection_apply]

theorem ggIsReflection_ggLinInv_dNeg (a : Fin (n + 1)) :
    GGIsReflection 3 (ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a)) := by
  refine ggIsReflection_of_eq_reflection (p := 3) (by decide) (tauIota τ)
    (x := dBasis (n + 1) a)
    (f := (2 : ZMod 3) • (LinearMap.proj a : DVec (n + 1) →ₗ[ZMod 3] ZMod 3)) ?_ ?_
  · simp [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
      Pi.single_eq_same]
  · rw [ggLin_ggLinInv]
    refine LinearEquiv.ext fun v => ?_
    rw [dNeg_apply_vec (n + 1) a v, Module.reflection_apply]
    simp only [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem not_pow_two_or_three_dNeg_mul_dTau {a b : Fin (n + 1)} (hab : a ≠ b) :
    ¬ ((ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a) *
          ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) false a b)) ^ 2 = 1 ∨
        (ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a) *
          ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) false a b)) ^ 3 = 1) := by
  intro h
  set φ : MulAut ↥Bs := ggLinInv (p := 3) (tauIota τ) (dNeg (n + 1) a) with hφ
  set ψ : MulAut ↥Bs := ggLinInv (p := 3) (tauIota τ) (dTau (n + 1) false a b) with hψ
  set T : DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1) :=
    dNeg (n + 1) a * dTau (n + 1) false a b with hTdef
  have hT : ggLin (p := 3) (tauIota τ) (φ * ψ) = T := by
    rw [map_mul, hφ, hψ, ggLin_ggLinInv, ggLin_ggLinInv, hTdef]
  have hTa : T (dBasis (n + 1) a) = dBasis (n + 1) b := by
    rw [hTdef, LinearEquiv.mul_apply, dTau_apply_left (n + 1) false hab,
      if_neg (by decide : ¬ (false = true)), one_smul,
      dNeg_basis, if_neg (Ne.symm hab), one_smul]
  have hTb : T (dBasis (n + 1) b) = -dBasis (n + 1) a := by
    rw [hTdef, LinearEquiv.mul_apply, dTau_apply_right (n + 1) false hab,
      if_neg (by decide : ¬ (false = true)), one_smul,
      dNeg_basis, if_pos rfl, neg_one_smul]
  have hT2 : (T ^ 2) (dBasis (n + 1) a) = -dBasis (n + 1) a := by
    rw [pow_two, LinearEquiv.mul_apply, hTa, hTb]
  have hT3 : (T ^ 3) (dBasis (n + 1) a) = -dBasis (n + 1) b := by
    change (T ^ (2 + 1)) (dBasis (n + 1) a) = -dBasis (n + 1) b
    rw [pow_succ, LinearEquiv.mul_apply, hTa, pow_two, LinearEquiv.mul_apply, hTb, map_neg,
      hTa]
  have hne_a : -dBasis (n + 1) a ≠ dBasis (n + 1) a := by
    intro heq
    have hc := congrFun heq a
    simp only [Pi.neg_apply, dBasis, Pi.basisFun_apply, Pi.single_apply, if_pos rfl] at hc
    exact (by decide : (-1 : ZMod 3) ≠ 1) hc
  have hne_b : -dBasis (n + 1) b ≠ dBasis (n + 1) a := by
    intro heq
    have hc := congrFun heq a
    simp only [Pi.neg_apply, dBasis, Pi.basisFun_apply, Pi.single_apply, if_neg hab,
      if_pos rfl] at hc
    exact (by decide : (0 : ZMod 3) ≠ 1) hc
  have hTpow : T ^ 2 = 1 ∨ T ^ 3 = 1 := by
    rcases h with h2 | h3
    · left
      have hh := congrArg (ggLin (p := 3) (tauIota τ)) h2
      rwa [map_pow, hT, map_one] at hh
    · right
      have hh := congrArg (ggLin (p := 3) (tauIota τ)) h3
      rwa [map_pow, hT, map_one] at hh
  rcases hTpow with h2 | h3
  · have hh := congrArg (fun L : (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) =>
        L (dBasis (n + 1) a)) h2
    simp only [hT2, LinearEquiv.coe_one, id_eq] at hh
    exact hne_a hh
  · have hh := congrArg (fun L : (DVec (n + 1) ≃ₗ[ZMod 3] DVec (n + 1)) =>
        L (dBasis (n + 1) a)) h3
    simp only [hT3, LinearEquiv.coe_one, id_eq] at hh
    exact hne_b hh

end Tau

end CFSG.StandardType.QTwo

end

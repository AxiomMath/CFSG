module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU44TwoNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU44TwoNatAset
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMain
public import CFSG.ClassicalGroups.Unitary.SU4FiveStab
public import CFSG.Quasithin.Background.GoldschmidtE23FourFix
public import CFSG.Quasithin.Background.SmithB51Sp4Bound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult CFSG.Quasithin.E3
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.RankThreeUC
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open scoped Matrix Kronecker

variable {K : Type} [Field K] [Finite K]

@[expose] def twoNatVec (w : Fin 2 → K) (x : Fin 4 → K) : StdMod (Fin 2 × Fin 4) K :=
  Multiplicative.ofAdd fun p => w p.1 * x p.2

theorem twoNatVec_mem_lineSub {u w : Fin 2 → K} {x : Fin 4 → K} (hx : x ≠ 0) :
    twoNatVec w x ∈ lineSub (ι := Fin 4) u ↔ w ∈ Submodule.span K {u} := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  constructor
  · rintro ⟨y, hy⟩
    have hwy : w = fun j => u j * (y i₀ / x i₀) := by
      funext j
      have h := congrFun hy (j, i₀)
      simp only [twoNatVec, toAdd_ofAdd] at h
      calc w j = (w j * x i₀) / x i₀ := (mul_div_cancel_right₀ _ hi₀).symm
        _ = (u j * y i₀) / x i₀ := by rw [h]
        _ = u j * (y i₀ / x i₀) := mul_div_assoc _ _ _
    rw [hwy]
    have hc : (fun j => u j * (y i₀ / x i₀)) = (y i₀ / x i₀) • u := by
      funext j
      simp [mul_comm]
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨fun i => c * x i, ?_⟩
    funext p
    rw [twoNatVec, toAdd_ofAdd, ← hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem exists_not_mem_span_singleton_two {u : Fin 2 → K} (hu : u ≠ 0) :
    ∃ w : Fin 2 → K, w ∉ Submodule.span K {u} ∧
      u 1 * w 0 - u 0 * w 1 ≠ 0 := by
  by_cases h0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    refine ⟨fun i : Fin 2 => if i = 0 then (1 : K) else 0, ?_, by simpa [h0] using hu1⟩
    intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    have h := congrFun hc 0
    simp [h0] at h
  · refine ⟨fun i : Fin 2 => if i = 1 then (1 : K) else 0, ?_, by simpa using h0⟩
    intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    have h0' := congrFun hc 0
    have h1' := congrFun hc 1
    simp at h0' h1'
    rcases h0' with hc0 | hu0
    · rw [hc0] at h1'
      simp at h1'
    · exact absurd hu0 h0

theorem exists_kronGL_of_fix_lineSub {A' : MulAut (StdMod (Fin 4) K)} {σ : K ≃+* K}
    {B : GL (Fin 2) K} {a : MulAut (StdMod (Fin 2 × Fin 4) K)}
    (hA' : IsSemilinear A' σ)
    (h : ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap a v p = toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
        v (j, i)) p.2)
    (ha2 : a ^ 2 = 1) {u : Fin 2 → K} (hu : u ≠ 0)
    (hfix : ∀ x, a (lineEmb (ι := Fin 4) u x) = lineEmb (ι := Fin 4) u x) :
    ∃ B' : GL (Fin 2) K, a = matAut (kronGL (ι := Fin 4) (K := K) 2 B') ∧
      (B' : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u ∧
      (B' : Matrix (Fin 2) (Fin 2) K) * B' = 1 := by
  classical
  let Bu : Fin 2 → K := (B : Matrix (Fin 2) (Fin 2) K) *ᵥ u
  have hEq : ∀ (i : Fin 4) (j : Fin 2) (k : Fin 4),
      σ (Bu j) * toAddMap A' (Pi.single i (1 : K)) k =
        u j * (Pi.single i (1 : K) : Fin 4 → K) k := by
    intro i j k
    have h1 := hfix (Multiplicative.ofAdd (Pi.single i (1 : K)))
    rw [normalForm_lineEmb hA' h u] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) (j, k)
    simpa [lineEmb_toAdd, Bu] using h2
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hu
  have hcne : ∀ i : Fin 4, toAddMap A' (Pi.single i (1 : K)) i ≠ 0 := by
    intro i h0
    have h1 := hEq i j₀ i
    rw [h0, mul_zero] at h1
    exact hj₀ (by simpa using h1.symm)
  have hsj : σ (Bu j₀) ≠ 0 := by
    intro h0
    have h1 := hEq 0 j₀ 0
    rw [h0, zero_mul] at h1
    exact hj₀ (by simpa using h1.symm)
  have hpropi : ∀ (i : Fin 4) (j : Fin 2),
      σ (Bu j) * toAddMap A' (Pi.single i (1 : K)) i = u j := by
    intro i j
    simpa using hEq i j i
  have hoff : ∀ (i k : Fin 4), k ≠ i → toAddMap A' (Pi.single i (1 : K)) k = 0 := by
    intro i k hk
    have h1 := hEq i j₀ k
    rw [Pi.single_eq_of_ne hk, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hsj
  have hscalar : ∀ i : Fin 4, toAddMap A' (Pi.single i (1 : K)) i =
      toAddMap A' (Pi.single 0 (1 : K)) 0 := by
    intro i
    apply mul_left_cancel₀ hsj
    rw [hpropi i j₀, hpropi 0 j₀]
  set c : K := toAddMap A' (Pi.single 0 (1 : K)) 0 with hcdef
  have hc0 : c ≠ 0 := hcne 0
  have hAe : ∀ i : Fin 4, toAddMap A' (Pi.single i (1 : K)) =
      c • (Pi.single i (1 : K) : Fin 4 → K) := by
    intro i
    funext k
    by_cases hk : k = i
    · rw [hk, hcdef]
      simpa using hscalar i
    · rw [hoff i k hk]
      simp [Pi.single_eq_of_ne hk]
  have hsigma : σ = RingEquiv.refl K := by
    ext t
    have h1 := hfix (Multiplicative.ofAdd (t • (Pi.single 0 (1 : K) : Fin 4 → K)))
    rw [normalForm_lineEmb hA' h u] at h1
    have hA'x : toAddMap A' (t • (Pi.single 0 (1 : K) : Fin 4 → K)) =
        (σ t * c) • (Pi.single 0 (1 : K) : Fin 4 → K) := by
      rw [hA' t, hAe 0, smul_smul]
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) (j₀, 0)
    simp only [lineEmb_toAdd, toAdd_ofAdd] at h2
    change σ (Bu j₀) * toAddMap A' (t • (Pi.single 0 (1 : K) : Fin 4 → K)) 0 =
      u j₀ * (t • (Pi.single 0 (1 : K) : Fin 4 → K)) 0 at h2
    rw [hA'x] at h2
    have h3 : (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) 0 = 1 := Pi.single_eq_same ..
    simp only [h3, mul_one, Pi.smul_apply, smul_eq_mul] at h2
    have h4 := hpropi 0 j₀
    have h5 : u j₀ * σ t = u j₀ * t := by
      calc u j₀ * σ t = (σ (Bu j₀) * c) * σ t := by rw [h4]
        _ = σ (Bu j₀) * (σ t * c) := by ring
        _ = u j₀ * t := h2
    exact mul_left_cancel₀ hj₀ h5
  have hA'lin : IsSemilinear A' (RingEquiv.refl K) := hsigma ▸ hA'
  have hAid : ∀ x : Fin 4 → K, toAddMap A' x = c • x := by
    intro x
    let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
      { toFun := toAddMap A'
        map_add' := toAddMap_add A'
        map_smul' := hA'lin }
    have hf : f = c • (LinearMap.id : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) := by
      refine (Pi.basisFun K (Fin 4)).ext fun i => ?_
      have h1 : f (Pi.basisFun K (Fin 4) i) = toAddMap A' (Pi.single i (1 : K)) := by
        rw [Pi.basisFun_apply]
        rfl
      rw [h1, hAe i]
      simp [Pi.basisFun_apply, smul_eq_mul]
    have hx := congrArg (fun g : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => g x) hf
    show toAddMap A' x = c • x
    exact hx
  set B' : GL (Fin 2) K :=
    B * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) with hB'def
  have hB'val : (B' : Matrix (Fin 2) (Fin 2) K) = c • (B : Matrix (Fin 2) (Fin 2) K) := by
    rw [hB'def, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.scalar_apply]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro b _ hb
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have haB : a = matAut (kronGL (ι := Fin 4) (K := K) 2 B') := by
    apply toAddMap_injective
    intro v
    funext p
    rw [h v p, toAddMap_matAut, kronGL_mulVec, hAid, hB'val]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply]
    simp only [smul_eq_mul]
    ring
  have hB'sq : (B' : Matrix (Fin 2) (Fin 2) K) * B' = 1 := by
    have h1 : matAut (kronGL (ι := Fin 4) (K := K) 2 (B' * B')) = 1 := by
      have h2 : a * a = matAut (kronGL (ι := Fin 4) (K := K) 2 B') *
          matAut (kronGL (ι := Fin 4) (K := K) 2 B') := by rw [← haB]
      rw [← pow_two, ha2] at h2
      change (1 : MulAut (StdMod (Fin 2 × Fin 4) K)) =
        matHom (kronGL (ι := Fin 4) (K := K) 2 B') *
          matHom (kronGL (ι := Fin 4) (K := K) 2 B') at h2
      rw [← map_mul] at h2
      change (1 : MulAut (StdMod (Fin 2 × Fin 4) K)) =
        matHom (kronGL (ι := Fin 4) (K := K) 2 B' *
          kronGL (ι := Fin 4) (K := K) 2 B') at h2
      rw [← map_mul (kronGL (ι := Fin 4) (K := K) 2)] at h2
      exact h2.symm
    have h3 : kronGL (ι := Fin 4) (K := K) 2 (B' * B') = 1 := by
      apply matHom_injective
      have h4 : matAut (1 : GL (Fin 2 × Fin 4) K) = 1 := by
        simpa [matHom_apply] using
          map_one (matHom : GL (Fin 2 × Fin 4) K →*
            MulAut (StdMod (Fin 2 × Fin 4) K))
      show matAut (kronGL (ι := Fin 4) (K := K) 2 (B' * B')) =
        matAut (1 : GL (Fin 2 × Fin 4) K)
      rw [h4]
      exact h1
    have hunit : B' * B' = 1 := kronGL_injective (ι := Fin 4) (K := K) 2 (h3.trans
      (map_one (kronGL (ι := Fin 4) (K := K) 2)).symm)
    exact congrArg Units.val hunit
  refine ⟨B', haB, ?_, hB'sq⟩
  have hformB' : ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap (matAut (kronGL (ι := Fin 4) (K := K) 2 B')) v p =
        toAddMap (1 : MulAut (StdMod (Fin 4) K))
          (fun i => ∑ j, (B' : Matrix (Fin 2) (Fin 2) K) p.1 j * v (j, i)) p.2 := by
    intro v p
    rw [toAddMap_matAut, kronGL_mulVec]
    rfl
  have h1 := hfix (Multiplicative.ofAdd (Pi.single 0 (1 : K)))
  rw [haB, normalForm_lineEmb isSemilinear_one hformB' u] at h1
  funext j
  have h3 := congrFun (congrArg Multiplicative.toAdd h1) (j, 0)
  simp only [lineEmb_toAdd, toAdd_ofAdd, Pi.single_eq_same, mul_one, toAddMap_one] at h3
  simpa using h3

theorem mem_centSub_of_trivial_quot {A' : MulAut (StdMod (Fin 4) K)} {σ : K ≃+* K}
    {B : GL (Fin 2) K} {a : MulAut (StdMod (Fin 2 × Fin 4) K)}
    (hA' : IsSemilinear A' σ)
    (h : ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap a v p = toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
        v (j, i)) p.2)
    (haσ : IsSemilinear a σ) (ha2 : a ^ 2 = 1) (hchar : CharP K 2) {u : Fin 2 → K} (hu : u ≠ 0)
    (hfixJ : ∀ x, a (lineEmb (ι := Fin 4) u x) ∈ lineSub u)
    (hquot : ∀ v, ∃ j ∈ lineSub u,
      Multiplicative.toAdd (a v) = Multiplicative.toAdd j + Multiplicative.toAdd v) :
    a ∈ centSub (lineSub u) := by
  classical
  let Bu : Fin 2 → K := (B : Matrix (Fin 2) (Fin 2) K) *ᵥ u
  obtain ⟨w, hw, hκ⟩ := exists_not_mem_span_singleton_two hu
  let Bw : Fin 2 → K := (B : Matrix (Fin 2) (Fin 2) K) *ᵥ w
  set δ : K := w 1 * u 0 - w 0 * u 1 with hδdef
  have hδ : δ ≠ 0 := by
    intro h0
    apply hκ
    have h1 : u 1 * w 0 - u 0 * w 1 = -δ := by
      rw [hδdef]
      ring
    rw [h1, h0, neg_zero]
  let ell : (Fin 2 → K) →ₗ[K] K :=
    { toFun := fun z => (z 1 * u 0 - z 0 * u 1) / δ
      map_add' := by
        intro x y
        simp only [Pi.add_apply]
        field_simp
        ring
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
        simp only [RingHom.id_apply]
        ring }
  have hellu : ell u = 0 := by
    simp only [ell, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show u 1 * u 0 - u 0 * u 1 = 0 by ring]
    exact zero_div δ
  have hellw : ell w = 1 := by
    simp only [ell, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show w 1 * u 0 - w 0 * u 1 = δ from rfl]
    exact div_self hδ
  let L : (Fin 2 × Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun v i => ell (fun j => v (j, i))
      map_add' := by
        intro x y
        funext i
        exact ell.map_add _ _
      map_smul' := by
        intro c x
        funext i
        exact ell.map_smul c _ }
  have hLJ : ∀ v : StdMod (Fin 2 × Fin 4) K, v ∈ lineSub u →
      L (Multiplicative.toAdd v) = 0 := by
    intro v hv
    obtain ⟨x, hx⟩ := hv
    funext i
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (fun j => Multiplicative.toAdd v (j, i)) = x i • u := by
      funext j
      rw [hx]
      simp [Pi.smul_apply, mul_comm]
    rw [h1, ell.map_smul, hellu, smul_eq_mul, mul_zero]
    rfl
  have hLt : ∀ x : Fin 4 → K, L (fun p => w p.1 * x p.2) = x := by
    intro x
    funext i
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (fun j => w j * x i) = x i • w := by
      funext j
      simp [Pi.smul_apply, mul_comm]
    rw [h1, ell.map_smul, hellw, smul_eq_mul, mul_one]
  have haL : ∀ x : Fin 4 → K,
      L (Multiplicative.toAdd (a (twoNatVec w x))) =
        ell (fun j => σ (Bw j)) • toAddMap A' x := by
    intro x
    funext i
    have hcol : ∀ j : Fin 2, Multiplicative.toAdd (a (twoNatVec w x)) (j, i) =
        σ (Bw j) * toAddMap A' x i := by
      intro j
      rw [show Multiplicative.toAdd (a (twoNatVec w x)) (j, i) =
        toAddMap a (Multiplicative.toAdd (twoNatVec w x)) (j, i) from rfl, h]
      have hrow : (fun i' => ∑ j', (B : Matrix (Fin 2) (Fin 2) K) j j' *
          Multiplicative.toAdd (twoNatVec w x) (j', i')) = fun i' => Bw j * x i' := by
        funext k'
        simp only [twoNatVec, toAdd_ofAdd]
        have h1 : (∑ j', (B : Matrix (Fin 2) (Fin 2) K) j j' * (w j' * x k')) =
            (∑ j', (B : Matrix (Fin 2) (Fin 2) K) j j' * w j') * x k' := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j' _ => by ring
        rw [h1]
        congr 1
      rw [hrow]
      have h2 : (fun i' => Bw j * x i') = Bw j • x := by
        funext i'
        simp [Pi.smul_apply, smul_eq_mul]
      rw [h2, hA']
      simp [Pi.smul_apply, smul_eq_mul]
    have h1 : (fun j => Multiplicative.toAdd (a (twoNatVec w x)) (j, i)) =
        (toAddMap A' x i) • (fun j => σ (Bw j)) := by
      funext j
      rw [hcol j]
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    change ell (fun j => Multiplicative.toAdd (a (twoNatVec w x)) (j, i)) = _
    rw [h1, ell.map_smul]
    simp [smul_eq_mul, mul_comm]
  have hquotL : ∀ x : Fin 4 → K,
      L (Multiplicative.toAdd (a (twoNatVec w x))) = x := by
    intro x
    obtain ⟨j, hjJ, hj⟩ := hquot (twoNatVec w x)
    rw [hj, map_add, hLJ j hjJ, zero_add]
    exact hLt x
  set lam : K := ell (fun j => σ (Bw j)) with hlamdef
  have hA'e0 : A' (Multiplicative.ofAdd (Pi.single 0 (1 : K))) ≠ 1 := by
    intro h0
    have h' : Multiplicative.ofAdd (Pi.single 0 (1 : K) : Fin 4 → K) = 1 :=
      A'.injective (by simpa using h0)
    have h2 : (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) = 0 := by
      have := congrArg Multiplicative.toAdd h'
      simpa using this
    have := congrFun h2 0
    simp at this
  have hlam : lam ≠ 0 := by
    intro h0
    have h2 := hquotL (Pi.single 0 (1 : K))
    rw [haL, h0, zero_smul] at h2
    have hne : (Pi.single (0 : Fin 4) (1 : K) : Fin 4 → K) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    exact hne h2.symm
  have hA'id : ∀ x : Fin 4 → K, toAddMap A' x = lam⁻¹ • x := by
    intro x
    have hx := hquotL x
    rw [haL, hlamdef] at hx
    by_cases h0 : x = 0
    · rw [h0]
      simp
    · calc toAddMap A' x = lam⁻¹ • (lam • toAddMap A' x) := by
            rw [smul_smul, inv_mul_cancel₀ hlam, one_smul]
        _ = lam⁻¹ • x := by rw [hx]
  have hsigma : σ = RingEquiv.refl K := by
    ext c
    change σ c = c
    have h1 := hA' c (Pi.single 0 (1 : K))
    rw [hA'id] at h1
    rw [hA'id] at h1
    have h2 : lam⁻¹ * c = σ c * lam⁻¹ := by
      have := congrFun h1 0
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have h3 : lam⁻¹ * c = c * lam⁻¹ := by ring
    rw [h3] at h2
    exact (mul_right_cancel₀ (inv_ne_zero hlam) h2).symm
  have hA'lin : IsSemilinear A' (RingEquiv.refl K) := hsigma ▸ hA'
  have hBu : Bu ∈ Submodule.span K {u} := by
    have h1 := hfixJ (Multiplicative.ofAdd (Pi.single 0 (1 : K)))
    rw [normalForm_lineEmb hA' h u] at h1
    rw [hsigma] at h1
    exact (twoNatVec_mem_lineSub (u := u) (w := Bu)
      (x := Multiplicative.toAdd (A' (Multiplicative.ofAdd (Pi.single 0 (1 : K)))))
      (by simpa [toAddMap] using hA'e0)).mp (by
        change lineEmb (ι := Fin 4) (fun j => ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) j)
          (A' (Multiplicative.ofAdd (Pi.single 0 (1 : K)))) ∈ lineSub u
        exact h1)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hBu
  have hcval : ∀ j, Bu j = c * u j := fun j => (congrFun hc j).symm
  have h3 : (fun j => Bu j) = c • u := by
    funext j
    rw [hcval j, Pi.smul_apply]
    ring
  have hline : ∀ (d : K) (y : StdMod (Fin 4) K),
      lineEmb (ι := Fin 4) (d • u) y =
        lineEmb (ι := Fin 4) u (Multiplicative.ofAdd (d • Multiplicative.toAdd y)) := by
    intro d y
    apply Multiplicative.toAdd.injective
    funext p
    simp [lineEmb_toAdd, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  have hact : ∀ x : StdMod (Fin 4) K,
      a (lineEmb (ι := Fin 4) u x) = lineEmb (ι := Fin 4) u ((c * lam⁻¹) • x) := by
    intro x
    have h1 : a (lineEmb u x) = lineEmb (fun j => σ (Bu j)) (A' x) :=
      normalForm_lineEmb hA' h u x
    rw [h1, hsigma]
    change lineEmb (ι := Fin 4) (fun j => Bu j) (A' x) =
      lineEmb (ι := Fin 4) u ((c * lam⁻¹) • x)
    rw [h3]
    have hA'x : A' x = lam⁻¹ • x := by
      change Multiplicative.ofAdd (toAddMap A' (Multiplicative.toAdd x)) = lam⁻¹ • x
      rw [hA'id]
      rfl
    rw [hA'x, hline c (lam⁻¹ • x)]
    congr 1
    simp [smul_smul]
  have ht2 : (c * lam⁻¹) ^ 2 = 1 := by
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hu
    have h1 : a (a (lineEmb u (Multiplicative.ofAdd (Pi.single 0 (1 : K))))) =
        lineEmb u (Multiplicative.ofAdd (Pi.single 0 (1 : K))) := by
      have h2 := congrArg (fun g : MulAut (StdMod (Fin 2 × Fin 4) K) =>
        g (lineEmb u (Multiplicative.ofAdd (Pi.single 0 (1 : K))))) ha2
      rwa [pow_two] at h2
    rw [hact, hact] at h1
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) (j₀, 0)
    simp only [lineEmb_toAdd, toAdd_ofAdd, Pi.single_eq_same, smul_smul] at h2
    have h3 : c * lam⁻¹ * (c * lam⁻¹) = 1 := by
      apply mul_left_cancel₀ hj₀
      simpa [mul_assoc] using h2
    simpa [pow_two] using h3
  have ht1 : c * lam⁻¹ = 1 := by
    rcases sq_eq_one_iff.mp ht2 with h | h
    · exact h
    · have hneg : (-1 : K) = 1 := by
        rw [neg_eq_iff_add_eq_zero]
        have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
        calc (1 : K) + 1 = 2 := by norm_num
          _ = 0 := h2
      rw [h, hneg]
  have htriv : ∀ x : StdMod (Fin 4) K, a (lineEmb u x) = lineEmb u x := by
    intro x
    rw [hact, ht1, one_smul]
  intro z hz
  obtain ⟨x, hx⟩ := hz
  have hz' : z = lineEmb (ι := Fin 4) u (Multiplicative.ofAdd x) := by
    apply Multiplicative.toAdd.injective
    funext p
    rw [hx]
    rfl
  rw [hz']
  exact htriv _

theorem two_mul_card_fixV_le_card_inf_mul_index {W : Type} [CommGroup W] [Finite W]
    {J : Subgroup W} {A : Subgroup (MulAut W)}
    (hAJ : ∀ a ∈ A, ∀ w ∈ J, a w ∈ J)
    (hnt : ∃ a ∈ A, ∃ v : W, a v * v⁻¹ ∉ J) :
    2 * Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV A ⊓ J) * J.index := by
  classical
  let C : Subgroup W := fixV A
  let φ : ↥C →* W ⧸ J := (QuotientGroup.mk' J).comp C.subtype
  let M : Subgroup (W ⧸ J) := φ.range
  have hker : φ.ker = (C ⊓ J).subgroupOf C := by
    ext x
    change (QuotientGroup.mk (x : W) = 1) ↔ ((x : W) ∈ C ∧ (x : W) ∈ J)
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  have hMtop : M ≠ ⊤ := by
    obtain ⟨a, ha, v, hv⟩ := hnt
    intro hM
    have hmem : QuotientGroup.mk v ∈ M := by rw [hM]; exact Subgroup.mem_top _
    obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.mp hmem
    have hxC : (x : W) ∈ C := x.2
    rw [mem_fixV] at hxC
    have hax : a (x : W) = x := hxC a ha
    have hxJ : (x : W) * v⁻¹ ∈ J := by
      have h1 : (QuotientGroup.mk' J) ((x : W) * v⁻¹) = 1 := by
        rw [map_mul, map_inv]
        have hx' : (QuotientGroup.mk' J) (x : W) = (QuotientGroup.mk' J) v := hxeq
        rw [hx', mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff (N := J) _).mp h1
    have hwell : (QuotientGroup.mk' J) (a (x : W)) = (QuotientGroup.mk' J) (a v) := by
      have h1 : (a (x : W)) * (a v)⁻¹ ∈ J := by
        have := hAJ a ha ((x : W) * v⁻¹) hxJ
        simpa [map_mul, map_inv] using this
      have h2 : (QuotientGroup.mk' J) ((a (x : W)) * (a v)⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff (N := J) _).mpr h1
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.mp h2
    have h1 : (QuotientGroup.mk' J) (a v) = (QuotientGroup.mk' J) v := by
      rw [← hwell, hax]
      exact hxeq
    apply hv
    have h2 : (QuotientGroup.mk' J) ((a v) * v⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := J) _).mp h2
  have hidx : 2 ≤ M.index := by
    have h := Subgroup.one_lt_index_of_ne_top hMtop
    omega
  have hMJ : M.index * Nat.card ↥M = Nat.card (W ⧸ J) :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup M).symm
  have hJidx : Nat.card (W ⧸ J) = J.index := by
    rw [Subgroup.index_eq_card]
  have hstep : 2 * (Nat.card ↥(C ⊓ J) * Nat.card ↥M) ≤
      Nat.card ↥(C ⊓ J) * (M.index * Nat.card ↥M) := by
    have h1 : 2 * Nat.card ↥M ≤ M.index * Nat.card ↥M := Nat.mul_le_mul_right _ hidx
    calc 2 * (Nat.card ↥(C ⊓ J) * Nat.card ↥M)
        = Nat.card ↥(C ⊓ J) * (2 * Nat.card ↥M) := by ring
      _ ≤ Nat.card ↥(C ⊓ J) * (M.index * Nat.card ↥M) :=
          Nat.mul_le_mul_left _ h1
  calc 2 * Nat.card ↥C
      = 2 * (Nat.card ↥(C ⊓ J) * Nat.card ↥M) := by rw [hcard]
    _ ≤ Nat.card ↥(C ⊓ J) * (M.index * Nat.card ↥M) := hstep
    _ = Nat.card ↥(C ⊓ J) * Nat.card (W ⧸ J) := by rw [hMJ]
    _ = Nat.card ↥(C ⊓ J) * J.index := by rw [hJidx]

theorem fixV_kronGL_involution_le_lineSub {u : Fin 2 → K} (hu : u ≠ 0)
    {B : GL (Fin 2) K} (hBu : (B : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u) (hB1 : B ≠ 1) :
    fixV (Subgroup.zpowers (matAut (kronGL (ι := Fin 4) (K := K) 2 B))) ≤
      lineSub (ι := Fin 4) u := by
  classical
  let d : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
    { toFun := fun x => (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x - x
      map_add' := by
        intro x y
        simp only [Matrix.mulVec_add, Pi.add_apply, Pi.sub_apply]
        abel
      map_smul' := by
        intro c x
        simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_sub,
          RingHom.id_apply] }
  have hd_ne : d ≠ 0 := by
    intro hd
    apply hB1
    ext i j
    have h0 : d (Pi.single j (1 : K)) = 0 := by rw [hd]; rfl
    have h1 : (B : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single j (1 : K) -
        Pi.single j (1 : K) = 0 := by
      simpa only [d, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
        LinearMap.id_apply] using h0
    have h2 := sub_eq_zero.mp h1
    have h3 := congrFun h2 i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using h3
  have hker_lt : LinearMap.ker d ≠ ⊤ := by
    intro htop
    apply hd_ne
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ LinearMap.ker d := htop ▸ Submodule.mem_top
    simpa using hx
  have hker_le_one : Module.finrank K (LinearMap.ker d) ≤ 1 := by
    have hlt := Submodule.finrank_lt (K := K) hker_lt
    have hV : Module.finrank K (Fin 2 → K) = 2 := by simp
    omega
  have hu_ker : u ∈ LinearMap.ker d := by
    show d u = 0
    simp only [d, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, LinearMap.id_apply]
    rw [hBu, sub_self]
  have hspan_le : Submodule.span K ({u} : Set (Fin 2 → K)) ≤ LinearMap.ker d := by
    rw [Submodule.span_singleton_le_iff_mem u (LinearMap.ker d)]
    exact hu_ker
  have hspan_finrank : Module.finrank K (Submodule.span K ({u} : Set (Fin 2 → K))) = 1 :=
    finrank_span_singleton (K := K) (V := Fin 2 → K) (v := u) hu
  have hker_ge_one : 1 ≤ Module.finrank K (LinearMap.ker d) := by
    rw [← hspan_finrank]
    exact Submodule.finrank_mono hspan_le
  have hker_eq : LinearMap.ker d = Submodule.span K ({u} : Set (Fin 2 → K)) := by
    exact (Submodule.eq_of_le_of_finrank_le hspan_le
      (by rw [hspan_finrank]; exact hker_le_one)).symm
  have hker : ∀ x : Fin 2 → K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = x →
      x ∈ Submodule.span K ({u} : Set (Fin 2 → K)) := by
    intro x hx
    have hxker : x ∈ LinearMap.ker d := by
      show d x = 0
      simp only [d, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply, LinearMap.id_apply]
      rw [hx, sub_self]
    rw [hker_eq] at hxker
    exact hxker
  intro v hv
  rw [mem_fixV_zpowers_iff_apply] at hv
  have hvec : (kronGL (ι := Fin 4) (K := K) 2 B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) K) *ᵥ
      Multiplicative.toAdd v = Multiplicative.toAdd v := by
    have h1 : toAddMap (matAut (kronGL (ι := Fin 4) (K := K) 2 B))
        (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
      simpa [toAddMap] using congrArg Multiplicative.toAdd hv
    simpa [toAddMap_matAut] using h1
  have hcol : ∀ i : Fin 4,
      (fun j => Multiplicative.toAdd v (j, i)) ∈
        Submodule.span K ({u} : Set (Fin 2 → K)) := by
    intro i
    apply hker
    funext j
    have h1 := congrFun hvec (j, i)
    rwa [kronGL_mulVec] at h1
  have hx : ∀ i, ∃ c : K, ∀ j, Multiplicative.toAdd v (j, i) = c * u j := by
    intro i
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcol i)
    refine ⟨c, fun j => ?_⟩
    have h1 := congrFun hc j
    simpa [Pi.smul_apply, smul_eq_mul] using h1.symm
  choose x hxval using hx
  refine ⟨x, ?_⟩
  funext p
  obtain ⟨j, i⟩ := p
  simpa [mul_comm] using hxval i j

theorem fixV_range_actOnSub {W : Type} [CommGroup W]
    {A : Subgroup (MulAut W)} {J : Subgroup W}
    (hAJ : ∀ a ∈ A, ∀ w ∈ J, a w ∈ J) :
    Nat.card ↥(fixV (actOnSub hAJ).range) = Nat.card ↥(fixV A ⊓ J) := by
  classical
  have hmap : (fixV (actOnSub hAJ).range).map J.subtype = fixV A ⊓ J := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z.2⟩
      intro a ha
      have hmem : (actOnSub hAJ) ⟨a, ha⟩ ∈ (actOnSub hAJ).range :=
        MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
      have h1 := hz _ hmem
      exact congrArg Subtype.val h1
    · rintro ⟨hwA, hwJ⟩
      refine ⟨⟨w, hwJ⟩, ?_, rfl⟩
      intro g hg
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      apply Subtype.ext
      exact hwA a a.2
  rw [← hmap, Subgroup.card_map_of_injective J.subtype_injective]

theorem card_range_mul_card_fixV_lineSub {u : Fin 2 → K} (hu : u ≠ 0) (hchar : CharP K 2)
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {X A : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))}
    (hX : X = natImage (diagSub 2 (StatedSU 4 (2 ^ 2) K)))
    (hXJ : ∀ x ∈ X, ∀ w ∈ lineSub (ι := Fin 4) u, x w ∈ lineSub (ι := Fin 4) u)
    (hAJ : ∀ a ∈ A, ∀ w ∈ lineSub (ι := Fin 4) u, a w ∈ lineSub (ι := Fin 4) u)
    (hAN : A ≤ Subgroup.normalizer (X : Set (MulAut (StdMod (Fin 2 × Fin 4) K))))
    (hAel : IsElemAbelian2 A) :
    Nat.card ↥(actOnSub hAJ).range *
      Nat.card ↥(fixV (actOnSub hAJ).range) ≤ Nat.card ↥(lineSub (ι := Fin 4) u) := by
  classical
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  let J : Subgroup (StdMod (Fin 2 × Fin 4) K) := lineSub (ι := Fin 4) u
  let XJ : Subgroup (MulAut ↥J) := (actOnSub hXJ).range
  let Ab : Subgroup (MulAut ↥J) := (actOnSub hAJ).range
  obtain ⟨eJ, heJ⟩ := exists_lineSub_equiv (k := 2) (ι := Fin 4) u hu
  have hXJmap : XJ.map (congrHom eJ) = natImage Γ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
      have hx : (x : MulAut (StdMod (Fin 2 × Fin 4) K)) ∈ natImage (diagSub 2 Γ) := by
        rw [← hX]
        exact x.2
      obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨γ₀, hγ₀Γ, hγ₀⟩ := Subgroup.mem_map.mp γ.2
      have hxval : (x : MulAut (StdMod (Fin 2 × Fin 4) K)) = matAut (diagGL 2 γ₀) := by
        rw [← hγ]
        change matAut (γ : GL (Fin 2 × Fin 4) K) = matAut (diagGL 2 γ₀)
        rw [hγ₀]
      refine ⟨⟨γ₀, hγ₀Γ⟩, ?_⟩
      apply MulEquiv.ext
      intro v
      obtain ⟨w, rfl⟩ := eJ.surjective v
      rw [congrHom_apply, eJ.symm_apply_apply]
      have hmemX : matAut (diagGL 2 γ₀) w ∈ J := by
        rw [← hxval]
        exact hXJ x x.2 w w.2
      have hsub : ((actOnSub hXJ) x) ⟨w, w.2⟩ = ⟨matAut (diagGL 2 γ₀) w, hmemX⟩ := by
        apply Subtype.ext
        change ((x : MulAut (StdMod (Fin 2 × Fin 4) K)) w : StdMod (Fin 2 × Fin 4) K) =
          (matAut (diagGL 2 γ₀) w : StdMod (Fin 2 × Fin 4) K)
        rw [hxval]
      rw [hsub]
      exact (heJ γ₀ w hmemX).symm
    · rintro ⟨γ, rfl⟩
      have hxmem : matAut (diagGL 2 (γ : GL (Fin 4) K)) ∈ natImage (diagSub 2 Γ) := by
        rw [natImage_eq_map]
        exact Subgroup.mem_map.mpr
          ⟨diagGL 2 (γ : GL (Fin 4) K),
            Subgroup.mem_map.mpr ⟨(γ : GL (Fin 4) K), γ.2, rfl⟩, rfl⟩
      have hxmemX : matAut (diagGL 2 (γ : GL (Fin 4) K)) ∈ X := hX.symm ▸ hxmem
      refine ⟨(actOnSub hXJ) ⟨matAut (diagGL 2 (γ : GL (Fin 4) K)), hxmemX⟩, ?_, ?_⟩
      · exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      · apply MulEquiv.ext
        intro v
        obtain ⟨w, rfl⟩ := eJ.surjective v
        rw [congrHom_apply, eJ.symm_apply_apply]
        have hsub : ((actOnSub hXJ) ⟨matAut (diagGL 2 (γ : GL (Fin 4) K)), hxmemX⟩) ⟨w, w.2⟩ =
            ⟨matAut (diagGL 2 (γ : GL (Fin 4) K)) w, hXJ _ hxmemX w w.2⟩ := by
          apply Subtype.ext
          rfl
        rw [hsub]
        exact heJ (γ : GL (Fin 4) K) w (hXJ _ hxmemX w w.2)
  have hAbN : Ab ≤ Subgroup.normalizer (XJ : Set (MulAut ↥J)) :=
    actOnSub_range_le_normalizer hXJ hAJ hAN
  have hAbN' : Ab.map (congrHom eJ) ≤
      Subgroup.normalizer (XJ.map (congrHom eJ) : Set (MulAut (StdMod (Fin 4) K))) := by
    have h1 := Subgroup.map_mono (f := congrHom eJ) hAbN
    rwa [Subgroup.map_equiv_normalizer_eq XJ (MulAut.congr eJ)] at h1
  have hAbel : IsElemAbelian2 Ab := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have h1 : a * b = b * a := Subtype.ext (by simpa using hAel.1 a a.2 b b.2)
      calc actOnSub hAJ a * actOnSub hAJ b = actOnSub hAJ (a * b) := by rw [map_mul]
        _ = actOnSub hAJ (b * a) := by rw [h1]
        _ = actOnSub hAJ b * actOnSub hAJ a := by rw [map_mul]
    · rintro _ ⟨a, rfl⟩
      have h1 : a ^ 2 = 1 := Subtype.ext (by simpa using hAel.2 a a.2)
      calc actOnSub hAJ a ^ 2 = actOnSub hAJ (a ^ 2) := by rw [map_pow]
        _ = 1 := by rw [h1, map_one]
  have hAb'el : IsElemAbelian2 (Ab.map (congrHom eJ)) :=
    (isElemAbelian2_map_congrHom eJ).mpr hAbel
  let ε₀ : ↥Γ ≃* ↥(natImage Γ) :=
    (Subgroup.equivMapOfInjective Γ matHom matHom_injective).trans
      (MulEquiv.subgroupCongr (natImage_eq_map Γ).symm)
  let ε : ↥(natImage Γ) ≃* ↥Γ := ε₀.symm
  have hmem_nat : ∀ γ : ↥Γ, matAut (γ : GL (Fin 4) K) ∈ natImage Γ := by
    intro γ
    rw [natImage_eq_map]
    exact Subgroup.mem_map.mpr ⟨(γ : GL (Fin 4) K), γ.2, rfl⟩
  have hε : ∀ γ : ↥Γ, ε ⟨matAut (γ : GL (Fin 4) K), hmem_nat γ⟩ = γ := by
    intro γ
    apply ε₀.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  have hcompat : ∀ (l : ↥(natImage Γ)) (s : StdMod (Fin 4) K),
      (MulEquiv.refl (StdMod (Fin 4) K)) ((l : MulAut (StdMod (Fin 4) K)) s) =
        Multiplicative.ofAdd (((ε l : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ
          Multiplicative.toAdd ((MulEquiv.refl (StdMod (Fin 4) K)) s)) := by
    intro l s
    have hl2 : (l : MulAut (StdMod (Fin 4) K)) ∈ Γ.map matHom := by
      rw [← natImage_eq_map]
      exact l.2
    obtain ⟨γ, hγ, hl⟩ := Subgroup.mem_map.mp hl2
    have hl' : l = ⟨matAut (γ : GL (Fin 4) K), hmem_nat ⟨γ, hγ⟩⟩ := Subtype.ext hl.symm
    rw [hl']
    have hεγ := hε ⟨γ, hγ⟩
    rw [hεγ]
    rfl
  have hmain := partBN_stmt (S := StdMod (Fin 4) K) (n := 2) (F := K)
    (fun s => @CFSG.Quasithin.FFC.Sp4Off.sq_eq_one_stdMod (Fin 4) K _ hchar s)
    (by norm_num) hK
    (L := natImage Γ) (A := Ab.map (congrHom eJ)) ε (MulEquiv.refl (StdMod (Fin 4) K))
    hcompat hAb'el (by rw [← hXJmap]; exact hAbN')
  have hcardJ : Nat.card ↥J = Nat.card (StdMod (Fin 4) K) := Nat.card_congr eJ.toEquiv
  calc Nat.card ↥Ab * Nat.card ↥(fixV Ab)
      = Nat.card ↥(Ab.map (congrHom eJ)) *
          Nat.card ↥(fixV (Ab.map (congrHom eJ))) := by
        rw [CFSG.Quasithin.H.card_map_congrHom, CFSG.Quasithin.H.fixV_map_congrHom,
          Subgroup.card_map_of_injective eJ.injective]
    _ ≤ Nat.card (StdMod (Fin 4) K) := hmain
    _ = Nat.card ↥J := hcardJ.symm

theorem not_isFFModule_of_sumOfNatVia_su4 {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {X Y : Subgroup (MulAut W)}
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {π : ↥(StatedSU 4 (2 ^ 2) K) →* ↥X}
    (h : SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ 2) K)) X ⊤ ⊥ 2 π) :
    ¬ IsFFModule Y := by
  classical
  intro hFF
  obtain ⟨A, hAY, hA1, hAel, hAcard⟩ := hFF
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  have hΓ : HasScalarCommutant Γ := fun f hf => commutant_statedSU (n := 2) hK f hf
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := 4)
      Nat.prime_two (by rw [hK]; norm_num)
  have hK4 : Nat.card K = 2 ^ 4 := by rw [hK]; norm_num
  obtain ⟨I, e, hreal, he, hblock⟩ := exists_coords_of_sumOfNatVia Γ h
  have hπ : Function.Surjective π := by
    obtain ⟨I₀, -, -, -, hreal₀⟩ := h
    exact (hreal₀ 0).1
  have hXmap : X.map (congrHom e) = natImage (diagSub 2 Γ) :=
    map_congrHom_eq_natImage_diag Γ hπ e he
  have hYmap : Y.map (congrHom e) ≤ natNorm (diagSub 2 Γ) := by
    have h1 : (Subgroup.normalizer (X : Set (MulAut W))).map (congrHom e) =
        Subgroup.normalizer ((X.map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))) : Set _) :=
      Subgroup.map_equiv_normalizer_eq X (MulAut.congr e)
    have h2 := Subgroup.map_mono (f := congrHom e) hYN
    rwa [h1, hXmap] at h2
  let Xm : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := X.map (congrHom e)
  let Am : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := A.map (congrHom e)
  have hAmY : Am ≤ Y.map (congrHom e) := Subgroup.map_mono hAY
  have hAm1 : Am ≠ ⊥ := by
    change A.map (congrHom e) ≠ ⊥
    rw [ne_eq, Subgroup.map_eq_bot_iff_of_injective A (f := congrHom e) (congrHom_injective e)]
    exact hA1
  have hAmel : IsElemAbelian2 Am :=
    (isElemAbelian2_map_congrHom e).mpr hAel
  have hAmcard : Nat.card (StdMod (Fin 2 × Fin 4) K) ≤
      Nat.card ↥Am * Nat.card ↥(fixV Am) := by
    have h1 : Nat.card (StdMod (Fin 2 × Fin 4) K) = Nat.card W :=
      Nat.card_congr e.toEquiv.symm
    have h2 : Nat.card ↥Am = Nat.card ↥A := card_map_congrHom e A
    have h3 : Nat.card ↥(fixV Am) = Nat.card ↥(fixV A) := by
      rw [fixV_map_congrHom, Subgroup.card_map_of_injective e.injective]
    rw [h1, h2, h3]
    exact hAcard
  have hAmN : Am ≤ Subgroup.normalizer (Xm : Set (MulAut (StdMod (Fin 2 × Fin 4) K))) := by
    rw [show Xm = natImage (diagSub 2 Γ) from hXmap]
    exact le_trans hAmY hYmap
  have hformA : ∀ a ∈ Am,
      ∃ (A' : MulAut (StdMod (Fin 4) K)) (σ : K ≃+* K) (B : GL (Fin 2) K),
        IsSemilinear A' σ ∧ IsSemilinear a σ ∧
        ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
          toAddMap a v p = toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
            v (j, i)) p.2 := by
    intro a ha
    obtain ⟨A', σ, B, -, hA'semi, haσ, hform, -⟩ :=
      exists_of_mem_normalizer_diag (k := 2) hΓ (hYmap (hAmY ha))
    exact ⟨A', σ, B, hA'semi, haσ, hform⟩
  have hAm2 : IsPGroup 2 ↥Am := E3.isPGroup_of_isElemAbelian2 hAmel
  obtain ⟨u, hu, hufix⟩ := @exists_fixed_lineSub (Fin 4) _ _ K _ _ hchar Am hAm2
    (fun a ha => by
      obtain ⟨A', σ, B, hA', -, hform⟩ := hformA a ha
      exact ⟨A', σ, B, hA', hform⟩)
  let J : Subgroup (StdMod (Fin 2 × Fin 4) K) := lineSub (ι := Fin 4) u
  have hTdiag : ∀ (γ : GL (Fin 4) K) (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
      toAddMap (matAut (diagGL 2 γ)) v p =
        toAddMap (matAut γ) (fun i => ∑ j, (1 : Matrix (Fin 2) (Fin 2) K) p.1 j *
          v (j, i)) p.2 := by
    intro γ v p
    obtain ⟨p1, p2⟩ := p
    rw [toAddMap_matAut, toAddMap_matAut, diagGL_mulVec]
    congr 1
    funext i
    rw [Finset.sum_eq_single p1]
    · simp
    · intro b _ hb
      simp [Matrix.one_apply, Ne.symm hb]
    · intro hp
      exact (hp (Finset.mem_univ _)).elim
  have hXJnat : ∀ x ∈ natImage (diagSub 2 Γ), ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    obtain ⟨y, hy⟩ := hw
    have hw_eq : w = lineEmb (ι := Fin 4) u (Multiplicative.ofAdd y) := by
      apply Multiplicative.toAdd.injective
      rw [lineEmb_toAdd]
      simpa using hy
    rw [hw_eq]
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨γ₀, -, hγ₀⟩ := Subgroup.mem_map.mp γ.2
    have hxmat : x = matAut (diagGL 2 γ₀) := by
      rw [← hγ]
      change matAut (γ : GL (Fin 2 × Fin 4) K) = matAut (diagGL 2 γ₀)
      rw [hγ₀]
    have hNF := normalForm_lineEmb (k := 2) (T := matAut (diagGL 2 γ₀))
      (A := matAut γ₀) (σ := RingEquiv.refl K) (B := 1)
      (isSemilinear_matAut γ₀) (hTdiag γ₀) u (Multiplicative.ofAdd y)
    rw [hxmat, hNF]
    have hmem : lineEmb (ι := Fin 4) u (matAut γ₀ (Multiplicative.ofAdd y)) ∈ J :=
      ⟨matAut γ₀ (Multiplicative.ofAdd y), by rw [lineEmb_toAdd]; rfl⟩
    simpa [Matrix.one_mulVec] using hmem
  have hXJ : ∀ x ∈ Xm, ∀ w ∈ J, x w ∈ J := by
    intro x hx w hw
    rw [show Xm = natImage (diagSub 2 Γ) from hXmap] at hx
    exact hXJnat x hx w hw
  have hAmJ : ∀ a ∈ Am, ∀ w ∈ J, a w ∈ J := by
    intro a ha w hw
    have h1 : J.map a.toMonoidHom = J := hufix a ha
    have hmem : a w ∈ J.map a.toMonoidHom := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    rwa [h1] at hmem
  let A₁ : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := Am ⊓ centSub J
  let Ab : Subgroup (MulAut ↥J) := (actOnSub hAmJ).range
  have hsplit : Nat.card ↥Am = Nat.card ↥A₁ * Nat.card ↥Ab := by
    have h1 := Subgroup.card_ker_mul_card_range (actOnSub hAmJ)
    have hker : (actOnSub hAmJ).ker = A₁.subgroupOf Am := by
      ext a
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centSub]
      constructor
      · intro h
        refine ⟨a.2, ?_⟩
        intro w hw
        have h2 := congrArg (fun g : MulAut ↥J => (g ⟨w, hw⟩ : StdMod (Fin 2 × Fin 4) K)) h
        simpa [actOnSub_apply] using h2
      · rintro ⟨-, h⟩
        apply MulEquiv.ext
        intro w
        exact Subtype.ext (h w w.2)
    rw [hker, Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show A₁ ≤ Am from inf_le_left)).toEquiv] at h1
    exact h1.symm
  have hfixVAb : Nat.card ↥(fixV Ab) = Nat.card ↥(fixV Am ⊓ J) :=
    fixV_range_actOnSub hAmJ
  have hpart : Nat.card ↥Ab * Nat.card ↥(fixV Ab) ≤ Nat.card ↥J :=
    card_range_mul_card_fixV_lineSub hu hchar hK hXmap hXJ hAmJ hAmN hAmel
  by_cases hA₁ : A₁ = ⊥
  · have hcardAmAb : Nat.card ↥Am = Nat.card ↥Ab := by
      rw [hsplit, hA₁, Subgroup.card_bot, one_mul]
    have hnt : ∃ a ∈ Am, ∃ v : StdMod (Fin 2 × Fin 4) K, a v * v⁻¹ ∉ J := by
      by_contra hcon
      push Not at hcon
      have hle : Am ≤ A₁ := by
        intro a ha
        have hcent : a ∈ centSub (lineSub (ι := Fin 4) u) := by
          obtain ⟨A', σ, B, hA', haσ, hform⟩ := hformA a ha
          refine mem_centSub_of_trivial_quot hA' hform haσ (hAmel.2 a ha) hchar hu
            (fun x => hAmJ a ha _ ⟨x, rfl⟩) ?_
          intro v
          refine ⟨a v * v⁻¹, hcon a ha v, ?_⟩
          rw [toAdd_mul, toAdd_inv]
          abel
        exact ⟨ha, hcent⟩
      have hbot : Am = ⊥ := by
        apply le_antisymm _ bot_le
        rwa [hA₁] at hle
      exact hAm1 hbot
    have hquot := two_mul_card_fixV_le_card_inf_mul_index (J := J) (A := Am) hAmJ hnt
    have hWJ : Nat.card (StdMod (Fin 2 × Fin 4) K) = J.index * Nat.card ↥J := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup J, ← Subgroup.index_eq_card]
    have h2 : 2 * Nat.card (StdMod (Fin 2 × Fin 4) K) ≤
        Nat.card (StdMod (Fin 2 × Fin 4) K) := by
      calc 2 * Nat.card (StdMod (Fin 2 × Fin 4) K)
          ≤ 2 * (Nat.card ↥Am * Nat.card ↥(fixV Am)) := Nat.mul_le_mul_left 2 hAmcard
        _ = Nat.card ↥Am * (2 * Nat.card ↥(fixV Am)) := by ring
        _ ≤ Nat.card ↥Am * (Nat.card ↥(fixV Am ⊓ J) * J.index) :=
            Nat.mul_le_mul_left _ hquot
        _ = (Nat.card ↥Ab * Nat.card ↥(fixV Ab)) * J.index := by
            rw [← hcardAmAb, ← hfixVAb]
            ring
        _ ≤ Nat.card ↥J * J.index := Nat.mul_le_mul_right _ hpart
        _ = Nat.card (StdMod (Fin 2 × Fin 4) K) := by
            rw [hWJ]; ring
    have hpos : 0 < Nat.card (StdMod (Fin 2 × Fin 4) K) := Nat.card_pos
    omega
  · obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA₁
    let a₀ : MulAut (StdMod (Fin 2 × Fin 4) K) := (a : MulAut (StdMod (Fin 2 × Fin 4) K))
    have haAm : a₀ ∈ Am := a.2.1
    have haCent : a₀ ∈ centSub J := a.2.2
    have ha1' : a₀ ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨A', σ, B, hA', haσ, hform⟩ := hformA a₀ haAm
    have ha2 : a₀ ^ 2 = 1 := hAmel.2 a₀ haAm
    have hfixa : ∀ x, a₀ (lineEmb (ι := Fin 4) u x) = lineEmb (ι := Fin 4) u x :=
      fun x => haCent (lineEmb (ι := Fin 4) u x) ⟨x, rfl⟩
    obtain ⟨B', haB', hBu', hBsq'⟩ := exists_kronGL_of_fix_lineSub hA' hform ha2 hu hfixa
    have hB'1 : B' ≠ 1 := by
      intro h1
      apply ha1'
      rw [haB', h1]
      have h2 : kronGL (ι := Fin 4) (K := K) 2 (1 : GL (Fin 2) K) = 1 :=
        map_one (kronGL (ι := Fin 4) (K := K) 2)
      rw [h2]
      simpa [matHom_apply] using
        map_one (matHom : GL (Fin 2 × Fin 4) K →* MulAut (StdMod (Fin 2 × Fin 4) K))
    have hfixzp_le : fixV (Subgroup.zpowers a₀) ≤ J := by
      rw [haB']
      exact fixV_kronGL_involution_le_lineSub hu hBu' hB'1
    have hJ_le : J ≤ fixV (Subgroup.zpowers a₀) := by
      intro w hw
      rw [mem_fixV_zpowers_iff_apply]
      exact haCent w hw
    have hfixzp : fixV (Subgroup.zpowers a₀) = J := le_antisymm hfixzp_le hJ_le
    have hC_le : fixV Am ≤ J := by
      intro v hv
      have hv' : a₀ v = v := (mem_fixV.mp hv) a₀ haAm
      have hmem : v ∈ fixV (Subgroup.zpowers a₀) := mem_fixV_zpowers_iff_apply.mpr hv'
      rwa [hfixzp] at hmem
    have hcardCJ : Nat.card ↥(fixV Am) ≤ Nat.card ↥J := by
      refine Nat.card_le_card_of_injective
        (fun x : ↥(fixV Am) => (⟨x.1, hC_le x.2⟩ : ↥J)) ?_
      intro x y h
      exact Subtype.ext (congrArg (fun z : ↥J => (z : StdMod (Fin 2 × Fin 4) K)) h)
    have hA₁el2 : IsElemAbelian2 A₁ := by
      refine ⟨?_, ?_⟩
      · intro x hx y hy
        exact hAmel.1 x hx.1 y hy.1
      · intro x hx
        exact hAmel.2 x hx.1
    have hA₁el : CFSG.Open.IsElemAbelian 2 A₁ := isElemAbelian2_iff.mp hA₁el2
    have hA₁c : A₁ ≤ Subgroup.centralizer
        (natImage (diagSub 2 Γ) : Set (MulAut (StdMod (Fin 2 × Fin 4) K))) := by
      intro x hx
      let x₀ : MulAut (StdMod (Fin 2 × Fin 4) K) := (x : MulAut (StdMod (Fin 2 × Fin 4) K))
      obtain ⟨A'', σ', B'', hA'', haσ', hform'⟩ := hformA x₀ hx.1
      have hx2 : x₀ ^ 2 = 1 := hAmel.2 x₀ hx.1
      have hfixx : ∀ y, x₀ (lineEmb (ι := Fin 4) u y) = lineEmb (ι := Fin 4) u y :=
        fun y => hx.2 (lineEmb (ι := Fin 4) u y) ⟨y, rfl⟩
      obtain ⟨B'', hxB'', -, -⟩ := exists_kronGL_of_fix_lineSub hA'' hform' hx2 hu hfixx
      change x₀ ∈ Subgroup.centralizer _
      rw [hxB'']
      exact (mem_centralizer_diag_iff (k := 2) hΓ).mpr ⟨B'', rfl⟩
    have hA₁K : Nat.card ↥A₁ ≤ Nat.card K :=
      @CFSG.Quasithin.H.Mult.card_le_of_isElemAbelian_two_centralizer_diag
        (Fin 4) _ _ K _ _ hchar _ Γ hΓ A₁ hA₁el hA₁c
    have hC_eq : Nat.card ↥(fixV Am) = Nat.card ↥(fixV Ab) := by
      rw [hfixVAb, inf_eq_left.mpr hC_le]
    have h2 : Nat.card ↥Am * Nat.card ↥(fixV Am) ≤ Nat.card K * Nat.card ↥J := by
      calc Nat.card ↥Am * Nat.card ↥(fixV Am)
          = Nat.card ↥A₁ * Nat.card ↥Ab * Nat.card ↥(fixV Am) := by
              rw [hsplit]
        _ = Nat.card ↥A₁ * (Nat.card ↥Ab * Nat.card ↥(fixV Ab)) := by
              rw [hC_eq]; ring
        _ ≤ Nat.card K * Nat.card ↥J := Nat.mul_le_mul hA₁K hpart
    have hKcard : Nat.card K = 16 := by rw [hK]; norm_num
    have hJcard : Nat.card ↥J = Nat.card K ^ 4 := by
      change Nat.card ↥(lineSub (ι := Fin 4) u) = Nat.card K ^ 4
      obtain ⟨eJ, -⟩ := exists_lineSub_equiv (k := 2) (ι := Fin 4) u hu
      rw [Nat.card_congr eJ.toEquiv, card_stdMod]
      norm_num
    have hWcard : Nat.card (StdMod (Fin 2 × Fin 4) K) = Nat.card K ^ 8 := by
      rw [card_stdMod]
      norm_num
    have hineq : Nat.card K * Nat.card ↥J < Nat.card (StdMod (Fin 2 × Fin 4) K) := by
      rw [hJcard, hWcard, hKcard]
      norm_num
    have hle := le_trans hAmcard h2
    exact (not_lt_of_ge hle) hineq

theorem toAddMap_diagGL_of_colSub {x : Fin 4 → K} {γ : GL (Fin 4) K} {c : K}
    (hc : (γ : Matrix (Fin 4) (Fin 4) K) *ᵥ x = c • x)
    {v : StdMod (Fin 2 × Fin 4) K} (hv : v ∈ colSub (K ∙ x)) :
    toAddMap (matAut (diagGL 2 γ)) (Multiplicative.toAdd v) =
      c • Multiplicative.toAdd v := by
  funext p
  obtain ⟨j, i⟩ := p
  rw [toAddMap_matAut, diagGL_mulVec]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv j)
  have hrow : (fun i => Multiplicative.toAdd v (j, i)) = a • x := ha.symm
  rw [hrow, Matrix.mulVec_smul, hc, smul_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show Multiplicative.toAdd v (j, i) = a * x i from congrFun hrow i]
  ring

@[expose] def twoNatKLine (v : StdMod (Fin 2 × Fin 4) K) : Subgroup (StdMod (Fin 2 × Fin 4) K) where
  carrier := {w | ∃ c : K, Multiplicative.toAdd w = c • Multiplicative.toAdd v}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, ?_⟩
    rw [toAdd_mul, hc, hd, add_smul]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    exact ⟨-c, by rw [toAdd_inv, hc, neg_smul]⟩

theorem twoNatKLine_ne_bot {v : StdMod (Fin 2 × Fin 4) K} (hv : v ≠ 1) : twoNatKLine v ≠ ⊥ := by
  intro h
  have hmem : v ∈ twoNatKLine v := ⟨1, by simp⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hv hmem

theorem exists_Z_of_sumOfNatVia_su4 {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w ^ 2 = 1) {X Y : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hK : Nat.card K = (2 ^ 2) ^ 2)
    {π : ↥(StatedSU 4 (2 ^ 2) K) →* ↥X}
    (h : SumOfNatVia (FFModel.nat (StatedSU 4 (2 ^ 2) K)) X ⊤ ⊥ 2 π)
    (S : Subgroup (MulAut W)) (hS : IsSylowIn 2 S Y) :
    ∃ Z : Subgroup W, Z ≠ ⊥ ∧
      (∀ A ∈ aSet 2 Y, A ≤ S → Z ≤ fixV A) ∧
      ∃ E : Subgroup (MulAut W), E ≤ X ⊓ stabSub Z ∧
        IsElemAbelian 5 E ∧ Nat.card E = 25 := by
  classical
  let Γ : Subgroup (GL (Fin 4) K) := StatedSU 4 (2 ^ 2) K
  have hΓ : HasScalarCommutant Γ := fun f hf => commutant_statedSU (n := 2) hK f hf
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := 4)
      Nat.prime_two (by rw [hK]; norm_num)
  have hK4 : Nat.card K = 2 ^ 4 := by rw [hK]; norm_num
  obtain ⟨I, e, hreal, he, hblock⟩ := exists_coords_of_sumOfNatVia Γ h
  have hπ : Function.Surjective π := by
    obtain ⟨I₀, -, -, -, hreal₀⟩ := h
    exact (hreal₀ 0).1
  have hXmap : X.map (congrHom e) = natImage (diagSub 2 Γ) :=
    map_congrHom_eq_natImage_diag Γ hπ e he
  have hXmap' : X.map (congrHom e) = (diagSub 2 Γ).map matHom := by
    rw [hXmap, natImage_eq_map]
  have hYmap : Y.map (congrHom e) ≤ natNorm (diagSub 2 Γ) := by
    have h1 : (Subgroup.normalizer (X : Set (MulAut W))).map (congrHom e) =
        Subgroup.normalizer ((X.map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K))) : Set _) :=
      Subgroup.map_equiv_normalizer_eq X (MulAut.congr e)
    have h2 := Subgroup.map_mono (f := congrHom e) hYN
    rwa [h1, hXmap] at h2
  let S' : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := S.map (congrHom e)
  have hS'le : S' ≤ Y.map (congrHom e) := Subgroup.map_mono hS.le
  have hS'2 : IsPGroup 2 ↥S' :=
    hS.isPGroup.of_equiv (Subgroup.equivMapOfInjective S (congrHom e) (congrHom_injective e))
  have hformS : ∀ a ∈ S',
      ∃ (A' : MulAut (StdMod (Fin 4) K)) (σ : K ≃+* K) (B : GL (Fin 2) K),
        IsSemilinear A' σ ∧ ∀ (v : Fin 2 × Fin 4 → K) (p : Fin 2 × Fin 4),
          toAddMap a v p = toAddMap A' (fun i => ∑ j, (B : Matrix (Fin 2) (Fin 2) K) p.1 j *
            v (j, i)) p.2 := by
    intro a ha
    obtain ⟨A', σ, B, -, hA'semi, -, hform, -⟩ :=
      exists_of_mem_normalizer_diag (k := 2) hΓ (hYmap (hS'le ha))
    exact ⟨A', σ, B, hA'semi, hform⟩
  obtain ⟨x, hx, hcolfix⟩ := exists_fixed_colSub_line (k := 2) (ι := Fin 4) hS'2 hformS
  let C : Subgroup (StdMod (Fin 2 × Fin 4) K) := colSub (K ∙ x)
  have hSC : ∀ a ∈ S', ∀ c ∈ C, a c ∈ C := by
    intro a ha c hc
    have hmem : a c ∈ C.map a.toMonoidHom := Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rw [hcolfix a ha] at hmem
    exact hmem
  let Slin : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := S' ⊓ linSub
  have hSlinP : IsPGroup 2 ↥Slin := hS'2.to_le inf_le_left
  have hCmem : twoNatVec (fun i : Fin 2 => if i = 0 then (1 : K) else 0) x ∈ C := by
    intro j
    fin_cases j
    · simpa [twoNatVec, C] using Submodule.subset_span (Set.mem_singleton x)
    · convert Submodule.zero_mem (K ∙ x) using 1
      funext i
      simp [twoNatVec]
  have hCeven : 2 ∣ Nat.card ↥C := by
    let v : ↥C := ⟨twoNatVec (fun i : Fin 2 => if i = 0 then (1 : K) else 0) x, hCmem⟩
    have hv2 : v ^ 2 = 1 := by
      apply Subtype.ext
      simpa using @CFSG.Quasithin.FFC.Sp4Off.sq_eq_one_stdMod (Fin 2 × Fin 4) K _ hchar
        (v : StdMod (Fin 2 × Fin 4) K)
    have hv1 : v ≠ 1 := by
      intro h
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
      have hval := congrArg (fun z : ↥C =>
        Multiplicative.toAdd (z : StdMod (Fin 2 × Fin 4) K) (0, i₀)) h
      simp [v, twoNatVec, toAdd_one] at hval
      exact hi₀ hval
    have hord : orderOf v = 2 := orderOf_eq_prime hv2 hv1
    have hzv : Nat.card ↥(Subgroup.zpowers v) = 2 := by rw [Nat.card_zpowers, hord]
    have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers v)
    rwa [hzv] at hdvd
  have hTopP : IsPGroup 2 ↥(⊤ : Subgroup ↥Slin) := hSlinP.of_equiv Subgroup.topEquiv.symm
  let φ : ↥Slin →* MulAut ↥C := (actOnSub hSC).comp (Subgroup.inclusion inf_le_left)
  obtain ⟨e₀, -, he₀ne, he₀fix⟩ :=
    CFSG.Quasithin.E2.exists_fixed_of_isPGroup φ (X := ⊤) hTopP ⊤
      (fun _ _ _ _ => trivial) (by simpa using hCeven)
  let v₀ : StdMod (Fin 2 × Fin 4) K := (e₀ : StdMod (Fin 2 × Fin 4) K)
  have hv₀ne : v₀ ≠ 1 := fun hv => he₀ne (Subtype.ext hv)
  let Z₀ : Subgroup (StdMod (Fin 2 × Fin 4) K) := twoNatKLine v₀
  have hZ₀ne : Z₀ ≠ ⊥ := twoNatKLine_ne_bot hv₀ne
  have hfixZ₀ : ∀ A ∈ aSet 2 Y, A ≤ S → Z₀ ≤ fixV (A.map (congrHom e)) := by
    intro A hA hAS
    have hA' : A.map (congrHom e) ∈ aSet 2 (Y.map (congrHom e)) :=
      (map_mem_aSet_iff e).mpr hA
    have hA'S : A.map (congrHom e) ≤ S' := Subgroup.map_mono hAS
    have hsemi : ∀ a ∈ A.map (congrHom e), ∃ σ : K ≃+* K, IsSemilinear a σ := by
      intro a ha
      obtain ⟨A', σ, B, -, hA'semi, hσ, -, -⟩ :=
        exists_of_mem_normalizer_diag (k := 2) hΓ (hYmap (hA'.1 ha))
      exact ⟨σ, hσ⟩
    have hlin := forall_linear_of_mem_aSet (κ := Fin 2 × Fin 4) (n := 4) (by norm_num) hK4
      (X := Y.map (congrHom e)) (A := A.map (congrHom e)) (k := 2) (by norm_num) hA' hsemi
    have hA'lin : A.map (congrHom e) ≤ linSub := fun a ha => (mem_linSub).mpr (hlin a ha)
    have hA'Slin : A.map (congrHom e) ≤ Slin := le_inf hA'S hA'lin
    rintro z hz
    rw [mem_fixV]
    intro a ha
    obtain ⟨t, ht⟩ := hz
    have hz' : z = Multiplicative.ofAdd (t • Multiplicative.toAdd v₀) := by
      rw [← ht]
      simp
    have hfixe : toAddMap a (Multiplicative.toAdd v₀) = Multiplicative.toAdd v₀ := by
      have h2 : (a : MulAut (StdMod (Fin 2 × Fin 4) K))
          (e₀ : StdMod (Fin 2 × Fin 4) K) = v₀ :=
        congrArg Subtype.val (he₀fix ⟨a, hA'Slin ha⟩ (Subgroup.mem_top _))
      have := congrArg Multiplicative.toAdd h2
      simpa [toAddMap, v₀] using this
    have hlin_a : IsSemilinear a (RingEquiv.refl K) := hlin a ha
    rw [hz']
    change Multiplicative.toAdd (a (Multiplicative.ofAdd (t • Multiplicative.toAdd v₀))) =
      t • Multiplicative.toAdd v₀
    rw [show Multiplicative.toAdd (a (Multiplicative.ofAdd (t • Multiplicative.toAdd v₀))) =
        toAddMap a (t • Multiplicative.toAdd v₀) from rfl, hlin_a, hfixe]
    rfl
  obtain ⟨E, hEsub, hEea, hEcard, hEline⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_elemAbelian_five_stab_line hK x hx
  let D : Subgroup (MulAut (StdMod (Fin 2 × Fin 4) K)) := (diagSub 2 E).map matHom
  have hDle : D ≤ X.map (congrHom e) := by
    rw [hXmap']
    exact Subgroup.map_mono (Subgroup.map_mono hEsub)
  have hDea : IsElemAbelian 5 D := by
    have h1 : IsElemAbelian 5 (diagSub 2 E) := hEea.map (diagGL 2)
    have h2 := h1.map (matHom : GL (Fin 2 × Fin 4) K →*
      MulAut (StdMod (Fin 2 × Fin 4) K))
    simpa [D] using h2
  have hDcard : Nat.card ↥D = 25 := by
    change Nat.card ↥(Subgroup.map matHom (Subgroup.map (diagGL 2) E)) = 25
    rw [Subgroup.card_map_of_injective matHom_injective,
      Subgroup.card_map_of_injective (diagGL_injective (ι := Fin 4) (K := K) 2)]
    exact hEcard
  have hDfixZ : ∀ g ∈ D, ∀ z ∈ Z₀, g z ∈ Z₀ := by
    intro g hg z hz
    change g ∈ Subgroup.map matHom (diagSub 2 E) at hg
    obtain ⟨γ, hγ, hgγ⟩ := Subgroup.mem_map.mp hg
    obtain ⟨γ₀, hγ₀, hγeq⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨c, hcx⟩ := hEline γ₀ hγ₀
    have hgmat : g = matAut (diagGL 2 γ₀) := by
      rw [← hgγ, ← hγeq]
      rfl
    obtain ⟨t, ht⟩ := hz
    have hz' : z = Multiplicative.ofAdd (t • Multiplicative.toAdd v₀) := by
      rw [← ht]
      simp
    have hv₀C : v₀ ∈ C := e₀.2
    have hgv : toAddMap (matAut (diagGL 2 γ₀)) (Multiplicative.toAdd v₀) =
        c • Multiplicative.toAdd v₀ :=
      toAddMap_diagGL_of_colSub hcx hv₀C
    rw [hz', hgmat]
    refine ⟨t * c, ?_⟩
    change toAddMap (matAut (diagGL 2 γ₀)) (t • Multiplicative.toAdd v₀) =
      (t * c) • Multiplicative.toAdd v₀
    rw [isSemilinear_matAut (diagGL 2 γ₀) t (Multiplicative.toAdd v₀), hgv, smul_smul]
    simp
  have hDstab : D ≤ stabSub Z₀ := by
    intro g hg
    rw [mem_stabSub]
    intro z
    constructor
    · intro hz
      have hinv : g⁻¹ ∈ D := D.inv_mem hg
      have h := hDfixZ g⁻¹ hinv (g z) hz
      simpa using h
    · intro hz
      exact hDfixZ g hg z hz
  have hcomp : (MulAut.congr e.symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom =
      MonoidHom.id (MulAut W) := by
    ext a w
    simp [congrHom_apply]
  refine ⟨Z₀.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [ne_eq, Subgroup.map_eq_bot_iff_of_injective Z₀ e.symm.injective]
    exact hZ₀ne
  · intro A hA hAS
    have h := hfixZ₀ A hA hAS
    have hmap := Subgroup.map_mono (f := e.symm.toMonoidHom) h
    rw [fixV_map_congrHom, Subgroup.map_map] at hmap
    have hcomp3 : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id W := by
      ext x
      simp
    rw [hcomp3, Subgroup.map_id] at hmap
    exact hmap
  · refine ⟨D.map (congrHom e.symm), ?_, ?_, ?_⟩
    · refine le_inf ?_ ?_
      · have hXback : (X.map (congrHom e)).map (congrHom e.symm) = X := by
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]
        rw [← hXback]
        exact Subgroup.map_mono (f := congrHom e.symm) hDle
      · have hZmap : (Z₀.map e.symm.toMonoidHom).map e.toMonoidHom = Z₀ := by
          rw [Subgroup.map_map]
          convert Subgroup.map_id Z₀ using 2
          ext x
          simp
        have hst := StabLat.stabSub_map_equiv e (Z₀.map e.symm.toMonoidHom)
        rw [hZmap] at hst
        have hmapst : (stabSub Z₀).map (congrHom e.symm) =
            stabSub (Z₀.map e.symm.toMonoidHom) := by
          rw [hst, Subgroup.map_map, hcomp, Subgroup.map_id]
        rw [← hmapst]
        exact Subgroup.map_mono (f := congrHom e.symm) hDstab
    · exact hDea.map (congrHom e.symm)
    · rw [Subgroup.card_map_of_injective (congrHom_injective e.symm)]
      exact hDcard

theorem k_SU44_TwoNat_holds : K_SU44_TwoNat := by
  intro W _ _ hsq X Y hXY hYN hSUn hsum
  obtain ⟨F, hFf, hFfin, π, hF16, hsumF⟩ := hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact @eight_le_mParam_of_sumOfNatVia_su4 F hFf hFfin W _ _ X Y hYN hF16 π hsumF
  · exact @aSet_seven_eq_empty_of_sumOfNatVia_su4 F hFf hFfin W _ _ X Y hYN hF16 π hsumF
  · exact @not_isFFModule_of_sumOfNatVia_su4 F hFf hFfin W _ _ hsq X Y hYN hF16 π hsumF
  · intro S hS
    exact @exists_Z_of_sumOfNatVia_su4 F hFf hFfin W _ _ hsq X Y hXY hYN hF16 π hsumF S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

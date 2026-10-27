module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry

public section

namespace CFSG.StandardType.LieKnownR2.Geo

open CFSG.StandardType CFSG.StandardType.LieKnownR2.Short CFSG.LieType.BorelTits Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.Timmesfeld.Transvection.Pres
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGOppRadSpU

private def geo_toStdLin (n : ℕ) : (Fin (n / 2) → ℤ) →ₗ[ℤ] (Fin (n / 2) → ℤ) where
  toFun := toStd n
  map_add' v w := by
    funext a
    by_cases h : Even n
    · simp only [toStd, h, ite_true, Symplectic.toStd, Pi.add_apply]
      split_ifs <;> ring
    · simp only [toStd, h, ite_false, Pi.add_apply]
      split_ifs <;> ring
  map_smul' c v := by
    funext a
    by_cases h : Even n
    · simp only [toStd, h, ite_true, Symplectic.toStd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      split_ifs <;> ring
    · simp only [toStd, h, ite_false, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs <;> ring

private theorem geo_toStdLin_apply (n : ℕ) (v : Fin (n / 2) → ℤ) :
    geo_toStdLin n v = toStd n v := rfl

private theorem geo_toStd_sub (n : ℕ) (v w : Fin (n / 2) → ℤ) :
    toStd n (v - w) = toStd n v - toStd n w :=
  map_sub (geo_toStdLin n) v w

private theorem geo_toStd_zsmul (n : ℕ) (c : ℤ) (v : Fin (n / 2) → ℤ) :
    toStd n (c • v) = c • toStd n v :=
  map_zsmul (geo_toStdLin n) c v

private theorem geo_toStd_apply_of_even {n : ℕ} (h : Even n) (v : Fin (n / 2) → ℤ)
    (a : Fin (n / 2)) :
    toStd n v a = (if a.val + 1 = n / 2 then 2 else 1) * v a -
      (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  simp only [toStd, h, ite_true, Symplectic.toStd]

private theorem geo_toStd_apply_of_odd {n : ℕ} (h : ¬Even n) (v : Fin (n / 2) → ℤ)
    (a : Fin (n / 2)) :
    toStd n v a = v a - (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  simp only [toStd, h, ite_false]

private theorem geo_toStd_single_of_lt (n : ℕ) {k : Fin (n / 2)} (h : k.val + 1 < n / 2) :
    toStd n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  by_cases he : Even n
  · rw [geo_toStd_apply_of_even he]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · rw [geo_toStd_apply_of_odd he]
    simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

private theorem geo_toStd_single_of_even {n : ℕ} (he : Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) : toStd n (Pi.single k 1) = 2 • Pi.single k 1 := by
  funext a
  rw [geo_toStd_apply_of_even he]
  simp only [Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

private theorem geo_toStd_single_of_odd {n : ℕ} (he : ¬Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) : toStd n (Pi.single k 1) = Pi.single k 1 := by
  funext a
  rw [geo_toStd_apply_of_odd he]
  simp only [Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem geo_coroot_cartan_of_lt (n : ℕ) {k : Fin (n / 2)} (h : k.val + 1 < n / 2)
    (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = toStd n v k - toStd n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartan n) k =
      ((LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ) -
        LinearMap.proj (⟨k.val + 1, h⟩ : Fin (n / 2))).comp (geo_toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, geo_toStdLin_apply]
    by_cases he : Even n
    · rw [geo_toStd_apply_of_even he, geo_toStd_apply_of_even he]
      simp only [cartan, he, ite_true, Symplectic.cartanC, Matrix.of_apply, Pi.single_apply,
        Fin.ext_iff]
      split_ifs <;> omega
    · rw [geo_toStd_apply_of_odd he, geo_toStd_apply_of_odd he]
      simp only [cartan, he, ite_false, Matrix.transpose_apply, Symplectic.cartanC,
        Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem geo_coroot_cartan_of_even {n : ℕ} (he : Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = toStd n v k := by
  have key : coroot (cartan n) k =
      (LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ).comp (geo_toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, coroot_single,
      geo_toStdLin_apply]
    rw [geo_toStd_apply_of_even he]
    simp only [cartan, he, ite_true, Symplectic.cartanC, Matrix.of_apply, Pi.single_apply,
      Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem geo_coroot_cartan_of_odd {n : ℕ} (he : ¬Even n) {k : Fin (n / 2)}
    (h : ¬k.val + 1 < n / 2) (v : Fin (n / 2) → ℤ) :
    coroot (cartan n) k v = 2 * toStd n v k := by
  have key : coroot (cartan n) k =
      (2 : ℤ) • (LinearMap.proj k : (Fin (n / 2) → ℤ) →ₗ[ℤ] ℤ).comp (geo_toStdLin n) := by
    ext l
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, geo_toStdLin_apply, smul_eq_mul]
    rw [geo_toStd_apply_of_odd he]
    simp only [cartan, he, ite_false, Matrix.transpose_apply, Symplectic.cartanC,
      Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  have := LinearMap.congr_fun key v
  simpa [geo_toStdLin_apply] using this

private def geo_stdRefl {m : ℕ} (k : Fin m) (e : Fin m → ℤ) : Fin m → ℤ :=
  if h : k.val + 1 < m then e ∘ Equiv.swap k ⟨k.val + 1, h⟩
  else fun a => (if a = k then -1 else 1) * e a

private theorem geo_stdRefl_of_lt {m : ℕ} {k : Fin m} (h : k.val + 1 < m) (e : Fin m → ℤ) :
    geo_stdRefl k e = e ∘ Equiv.swap k ⟨k.val + 1, h⟩ := dite_eq_left h

private theorem geo_stdRefl_of_not_lt {m : ℕ} {k : Fin m} (h : ¬k.val + 1 < m) (e : Fin m → ℤ) :
    geo_stdRefl k e = fun a => (if a = k then -1 else 1) * e a := dite_eq_right h

private theorem geo_stdRefl_nsmul {m : ℕ} (k : Fin m) (c : ℕ) (e : Fin m → ℤ) :
    geo_stdRefl k (c • e) = c • geo_stdRefl k e := by
  by_cases h : k.val + 1 < m
  · simp only [geo_stdRefl_of_lt h]
    rfl
  · simp only [geo_stdRefl_of_not_lt h]
    funext a
    simp only [Pi.smul_apply]
    ring

private theorem geo_toStd_reflection (n : ℕ) (k : Fin (n / 2)) (v : Fin (n / 2) → ℤ) :
    toStd n (reflection (cartan n) k v) = geo_stdRefl k (toStd n v) := by
  rw [reflection_apply_coroot, geo_toStd_sub, geo_toStd_zsmul]
  by_cases h : k.val + 1 < n / 2
  · rw [geo_coroot_cartan_of_lt n h, geo_toStd_single_of_lt n h, geo_stdRefl_of_lt h]
    have hne : (⟨k.val + 1, h⟩ : Fin (n / 2)) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · by_cases he : Even n
    · rw [geo_coroot_cartan_of_even he h, geo_toStd_single_of_even he h,
        geo_stdRefl_of_not_lt h]
      funext a
      by_cases ha : a = k
      · subst ha
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
        ring
      · simp [ha]
    · rw [geo_coroot_cartan_of_odd he h, geo_toStd_single_of_odd he h,
        geo_stdRefl_of_not_lt h]
      funext a
      by_cases ha : a = k
      · subst ha
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
        ring
      · simp [ha]

private theorem geo_weight_apply (n : ℕ) (i : Fin n) (a : Fin (n / 2)) :
    weight n i a = (if i.val = a.val then 1 else 0) - (if n - 1 - i.val = a.val then 1 else 0) := by
  unfold weight
  by_cases h : i.val < n / 2
  · rw [dite_eq_left h, Pi.single_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [dite_eq_right h]
    by_cases h' : n - 1 - i.val < n / 2
    · rw [dite_eq_left h', Pi.neg_apply, Pi.single_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> omega
    · rw [dite_eq_right h']
      simp only [Pi.zero_apply]
      split_ifs <;> omega

private theorem geo_weight_rev (n : ℕ) (i : Fin n) :
    weight n (Fin.rev i) = -weight n i := by
  funext a
  rw [Pi.neg_apply, geo_weight_apply, geo_weight_apply, Fin.val_rev]
  split_ifs <;> omega

private theorem geo_weight_lowIdx {n : ℕ} (a : Fin (n / 2)) :
    weight n (lowIdx a) = Pi.single a 1 := by
  funext b
  rw [geo_weight_apply, Pi.single_apply]
  simp only [lowIdx, Fin.ext_iff]
  split_ifs <;> omega

private theorem geo_weight_rev_lowIdx {n : ℕ} (a : Fin (n / 2)) :
    weight n (Fin.rev (lowIdx a)) = -Pi.single a 1 := by
  rw [geo_weight_rev, geo_weight_lowIdx]

private theorem geo_single_comp_swap {m : ℕ} (x p q : Fin m) (c : ℤ) :
    Pi.single x c ∘ Equiv.swap p q = Pi.single (Equiv.swap p q x) c := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

private theorem geo_reach_smul_single {m : ℕ} (P : (Fin m → ℤ) → Prop)
    (hP : ∀ (k : Fin m) (e : Fin m → ℤ), P e → P (geo_stdRefl k e)) (c : ℕ)
    (hlast : ∀ k : Fin m, ¬k.val + 1 < m → P (c • Pi.single k 1)) :
    ∀ d (b : Fin m), b.val + d + 1 = m → P (c • Pi.single b 1) := by
  intro d
  induction d with
  | zero =>
    intro b hb
    exact hlast b (by omega)
  | succ d ih =>
    intro b hb
    have hb1 : b.val + 1 < m := by omega
    have h := hP b _ (ih ⟨b.val + 1, hb1⟩ (by simp; omega))
    rwa [geo_stdRefl_of_lt hb1, Pi.smul_comp, geo_single_comp_swap,
      Equiv.swap_apply_right] at h

private theorem geo_gPSUr_weight_lowIdx {n : ℕ} (a : Fin (n / 2)) :
    weight n (lowIdx a) = Pi.single a 1 := by
  funext c
  rw [weight_apply', val_lowIdx, Pi.single_apply]
  by_cases h : c = a
  · subst h
    simp
  · have h' : a.val ≠ c.val := fun e => h (Fin.ext e.symm)
    have h2 : a.val + c.val + 1 ≠ n := by
      have ha := a.isLt
      have hc := c.isLt
      omega
    simp [h, h', h2]

private theorem geo_gPSUr_toStd_apply_of_even {n : ℕ} (he : Even n) (v : Fin (n / 2) → ℤ)
    (a : Fin (n / 2)) :
    toStd n v a = (if a.val + 1 = n / 2 then 2 else 1) * v a -
      (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  rw [toStd, if_pos he]
  rfl

private theorem geo_gPSUr_exists_highest {n : ℕ} (hn : 2 ≤ n) :
    ∃ θ : Fin (n / 2) → ℤ,
      toStd n θ = 2 • weight n (lowIdx (⟨0, by omega⟩ : Fin (n / 2))) := by
  have hm : 0 < n / 2 := by omega
  by_cases he : Even n
  · refine ⟨fun a => if a.val + 1 = n / 2 then 1 else 2, ?_⟩
    funext a
    rw [geo_gPSUr_toStd_apply_of_even he, geo_gPSUr_weight_lowIdx, Pi.smul_apply,
      Pi.single_apply, nsmul_eq_mul]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
      split_ifs <;> simp_all <;> omega
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]
      split_ifs <;> simp_all <;> omega
  · refine ⟨fun _ => 2, ?_⟩
    funext a
    rw [geo_gPSUr_weight_lowIdx, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
    simp only [toStd, if_neg he]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]

private theorem geo_gPSUr_toStd_neg (n : ℕ) (v : Fin (n / 2) → ℤ) :
    toStd n (-v) = -toStd n v := by
  by_cases he : Even n
  · funext a
    simp only [toStd, if_pos he, CFSG.LieType.Universal.Symplectic.toStd, Pi.neg_apply]
    split_ifs <;> ring
  · funext a
    simp only [toStd, if_neg he, Pi.neg_apply]
    split_ifs <;> ring

private theorem geo_gPSUr_vecMul_single_rev {F : Type} [Field F] {n : ℕ} (a : Fin n) :
    Matrix.vecMul (Pi.single (Fin.rev a) (1 : F)) (Unitary.antidiag n) = Pi.single a 1 := by
  funext i
  simp only [CFSG.Timmesfeld.LieEmbed.vecMul_antidiag, Pi.single_apply, Fin.rev_inj]

private theorem geo_gPSUr_mem_rootGroup_short {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {A B : Fin (n / 2) ⊕ Fin (n / 2)}
    (hAB : idx A ≠ idx B) {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt A B) (g : SU σ n) :
    g ∈ rootGroup σ hσ n γ ↔ ∃ c : F, suElt σ hσ A B c = g := by
  by_cases he : Even n
  · exact mem_rootGroup_iff_suElt (m := n) hσ he hAB hγ g
  · exact mem_rootGroup_iff_suElt_odd (m := n) hσ hAB hγ g

private theorem geo_gPSUr_pairGen_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (u : Unitary.SU σ n) (x y : Fin n → F) (c : F) :
    ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        (1 + c • Matrix.vecMulVec x
              (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
          σ.toRingHom c • Matrix.vecMulVec y
              (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n))) *
        ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 + c • Matrix.vecMulVec
            (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
            (Matrix.vecMul (fun i =>
              σ.toRingHom (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y i))
              (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec
            (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
            (Matrix.vecMul (fun i =>
              σ.toRingHom (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x i))
              (Unitary.antidiag n)) := by
  let U : Matrix (Fin n) (Fin n) F := ((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  let V : Matrix (Fin n) (Fin n) F :=
    ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  change U * (1 + c • Matrix.vecMulVec x
            (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec y
            (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n))) * V =
      1 + c • Matrix.vecMulVec (Matrix.mulVec U x)
            (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U y i)) (Unitary.antidiag n)) -
        σ.toRingHom c • Matrix.vecMulVec (Matrix.mulVec U y)
            (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U x i)) (Unitary.antidiag n))
  have hUV : U * V = 1 := by
    change (((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) *
      ((((u : GL (Fin n) F))⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiso : conjTr σ U * Unitary.antidiag n * U = Unitary.antidiag n := by
    have h := CFSG.Timmesfeld.LieEmbed.suMat_isometry σ u
    rwa [CFSG.Timmesfeld.LieEmbed.suMat_apply] at h
  have hrow : ∀ v : Fin n → F,
      Matrix.vecMul (Timmesfeld.LieEmbed.uRow σ v) V =
        Timmesfeld.LieEmbed.uRow σ (Matrix.mulVec U v) := by
    intro v
    have h := CFSG.Timmesfeld.LieEmbed.uRow_mulVec_vecMul_of_isometry hiso v
    rw [← h, Matrix.vecMul_vecMul, hUV, Matrix.vecMul_one]
  have hN1 : U * Matrix.vecMulVec x
        (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) * V =
      Matrix.vecMulVec (Matrix.mulVec U x)
        (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U y i)) (Unitary.antidiag n)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [show Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n) =
        Timmesfeld.LieEmbed.uRow σ y from rfl]
    rw [hrow y]
    rfl
  have hN2 : U * Matrix.vecMulVec y
        (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n)) * V =
      Matrix.vecMulVec (Matrix.mulVec U y)
        (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec U x i)) (Unitary.antidiag n)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [show Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n) =
        Timmesfeld.LieEmbed.uRow σ x from rfl]
    rw [hrow x]
    rfl
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mul,
    Matrix.sub_mul, Matrix.smul_mul, hUV, Matrix.one_mul, hN1, hN2]

private theorem geo_gPSUr_unitPairGroup_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (u : Unitary.SU σ n) (x y : Fin n → F) :
    (unitPairGroup σ.toRingHom (Unitary.antidiag n) x y).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom =
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) := by
  apply le_antisymm
  · show (unitPairGroup σ.toRingHom (Unitary.antidiag n) x y).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom ≤
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
        (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
    rw [Subgroup.map_le_iff_le_comap]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨c, ?_⟩)
    change ((MulAut.conj ((u : GL (Fin n) F)) g : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = _
    rw [MulAut.conj_apply]
    simp only [Units.val_mul]
    rw [show ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        1 + c • Matrix.vecMulVec x
              (Matrix.vecMul (fun i => σ.toRingHom (y i)) (Unitary.antidiag n)) -
          σ.toRingHom c • Matrix.vecMulVec y
              (Matrix.vecMul (fun i => σ.toRingHom (x i)) (Unitary.antidiag n)) from hg]
    exact geo_gPSUr_pairGen_conj σ u x y c
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_map.2 ⟨(MulAut.conj (((u : GL (Fin n) F))⁻¹)) g, ?_, ?_⟩
    · refine Subgroup.subset_closure ⟨c, ?_⟩
      show (((MulAut.conj (((u : GL (Fin n) F))⁻¹)) (g : GL (Fin n) F) :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
      rw [MulAut.conj_apply]
      simp only [Units.val_mul]
      rw [show ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          1 + c • Matrix.vecMulVec
                (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
                (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec
                    (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y i))
                  (Unitary.antidiag n)) -
            σ.toRingHom c • Matrix.vecMulVec
                (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y)
                (Matrix.vecMul (fun i => σ.toRingHom (Matrix.mulVec
                    (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x i))
                  (Unitary.antidiag n)) from hg]
      have hux : ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹ *
          (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = 1 := by
        have h : ((u : GL (Fin n) F))⁻¹ * (u : GL (Fin n) F) = 1 := inv_mul_cancel _
        simpa [Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] using
          congrArg (fun w : GL (Fin n) F => ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
      have hx : Matrix.mulVec ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹
          (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x) = x := by
        rw [Matrix.mulVec_mulVec, hux, Matrix.one_mulVec]
      have hy : Matrix.mulVec ((((u : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F))⁻¹
          (Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) = y := by
        rw [Matrix.mulVec_mulVec, hux, Matrix.one_mulVec]
      simpa [hx, hy, CFSG.Timmesfeld.LieEmbed.uRow] using
        geo_gPSUr_pairGen_conj σ u⁻¹
          (x := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
          (y := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) c
    · change ((MulAut.conj ((u : GL (Fin n) F))) *
          (MulAut.conj (((u : GL (Fin n) F))⁻¹))) g = g
      rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem geo_gPSUr_map_conj_subtype {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (u : Unitary.SU σ n) (H : Subgroup (Unitary.SU σ n)) :
    (H.map (MulAut.conj u).toMonoidHom).map (Unitary.SU σ n).subtype =
      (H.map (Unitary.SU σ n).subtype).map
        (MulAut.conj ((u : GL (Fin n) F)) : MulAut (GL (Fin n) F)).toMonoidHom := by
  apply le_antisymm
  · rintro g ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine Subgroup.mem_map.2 ⟨(x : GL (Fin n) F),
      Subgroup.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    change MulAut.conj ((u : GL (Fin n) F)) ((x : GL (Fin n) F)) =
      (Unitary.SU σ n).subtype ((MulAut.conj u) x)
    simp [MulAut.conj_apply, Units.val_mul]
  · rintro g ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine Subgroup.mem_map.2 ⟨(MulAut.conj u) x, ?_, ?_⟩
    · exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    · change (Unitary.SU σ n).subtype ((MulAut.conj u) x) =
        MulAut.conj ((u : GL (Fin n) F)) ((x : GL (Fin n) F))
      simp [MulAut.conj_apply, Units.val_mul]

private theorem su_exists_crd {n : ℕ} {i : Fin n} (hi : i ≠ Fin.rev i) :
    ∃ b : Fin (n / 2) ⊕ Fin (n / 2), crd b = i := by
  obtain ⟨a, rfl | rfl⟩ := exists_lowIdx hi
  · exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr a, rfl⟩

private theorem ht_le_of_mem_roots' {n : ℕ} {δ : Fin (n / 2) → ℤ}
    (hδ : δ ∈ roots (isFiniteType_cartan n) (divisible n)) : ht δ ≤ (n : ℤ) - 1 := by
  rw [roots_eq] at hδ
  rcases hδ with ⟨i, j, -, -, -, -, h⟩ | ⟨i, -, h⟩ | ⟨hodd, i, -, h⟩
  · rw [ht_eq_of_weight_sub h.symm]
    have := i.isLt
    have := j.isLt
    omega
  · have h' : weight n i - weight n (Fin.rev i) = toStd n δ := by
      rw [weight_rev', sub_neg_eq_add, ← two_nsmul, h]
    rw [ht_eq_of_weight_sub h']
    simp only [Fin.val_rev]
    omega
  · have hn : 0 < n := i.pos
    have hodd' : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
    have hk : Fin.rev (⟨n / 2, by omega⟩ : Fin n) = ⟨n / 2, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_rev]; omega)
    have h' : weight n i - weight n ⟨n / 2, by omega⟩ = toStd n δ := by
      rw [weight_eq_zero_of_rev_eq hk, sub_zero, h]
    rw [ht_eq_of_weight_sub h']
    have := i.isLt
    omega

private theorem geo_stdRefl_neg {m : ℕ} (k : Fin m) (e : Fin m → ℤ) :
    geo_stdRefl k (-e) = -geo_stdRefl k e := by
  by_cases h : k.val + 1 < m
  · rw [geo_stdRefl_of_lt h, geo_stdRefl_of_lt h]
    rfl
  · rw [geo_stdRefl_of_not_lt h, geo_stdRefl_of_not_lt h]
    funext a
    simp only [Pi.neg_apply]
    ring

private theorem geo_stdRefl_single_self {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) :
    geo_stdRefl k (Pi.single k 1) = Pi.single ⟨k.val + 1, hk⟩ 1 := by
  rw [geo_stdRefl_of_lt hk]
  funext a
  rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
  by_cases ha : a = ⟨k.val + 1, hk⟩
  · subst ha
    rw [if_pos rfl, Equiv.swap_apply_right, if_pos rfl]
  · rw [if_neg ha]
    have hne : Equiv.swap k ⟨k.val + 1, hk⟩ a ≠ k := by
      intro h
      have h' := congrArg (Equiv.swap k ⟨k.val + 1, hk⟩) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
      exact ha h'
    rw [if_neg hne]

private theorem geo_stdRefl_two_single_succ {m : ℕ} (k : Fin m) (hk : k.val + 1 < m) :
    geo_stdRefl k (2 • Pi.single k 1) = 2 • Pi.single ⟨k.val + 1, hk⟩ 1 := by
  rw [geo_stdRefl_nsmul, geo_stdRefl_single_self k hk]

private theorem geo_stdRefl_two_single_last {m : ℕ} (k : Fin m) (hk : ¬k.val + 1 < m) :
    geo_stdRefl k (2 • Pi.single k 1) = -(2 • Pi.single k 1) := by
  rw [geo_stdRefl_of_not_lt hk]
  funext a
  by_cases ha : a = k
  · subst ha
    simp
  · simp [Pi.smul_apply, Pi.single_apply, ha]

private def ccOrbit (n : ℕ) (θ e : Fin (n / 2) → ℤ) : Prop :=
  ∃ w : (coxeterMatrix (isFiniteType_cartan n)).Group,
    toStd n (weylAction (isFiniteType_cartan n) w θ) = e

private theorem ccOrbit_self {n : ℕ} (θ : Fin (n / 2) → ℤ) : ccOrbit n θ (toStd n θ) :=
  ⟨1, by rw [map_one, Module.End.one_apply]⟩

private theorem ccOrbit_geo_stdRefl {n : ℕ} {θ e : Fin (n / 2) → ℤ} (h : ccOrbit n θ e)
    (k : Fin (n / 2)) : ccOrbit n θ (geo_stdRefl k e) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨(coxeterMatrix (isFiniteType_cartan n)).toCoxeterSystem.simple k * w, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple, geo_toStd_reflection, hw]

private theorem ccOrbit_two_weight {n : ℕ} {θ : Fin (n / 2) → ℤ} {a₀ : Fin (n / 2)}
    (ha₀ : a₀.val = 0) (hθ : toStd n θ = 2 • Pi.single a₀ 1) {i : Fin n}
    (hi : i ≠ Fin.rev i) : ccOrbit n θ (2 • weight n i) := by
  have hm : 0 < n / 2 := by
    have := a₀.isLt
    omega
  have hpos : ∀ b : Fin (n / 2), ccOrbit n θ (2 • Pi.single b 1) := by
    intro b
    have hmain : ∀ d (hd : d < n / 2),
        ccOrbit n θ (2 • Pi.single (⟨d, hd⟩ : Fin (n / 2)) 1) := by
      intro d
      induction d with
      | zero =>
        intro hd
        have h0 : (⟨0, hd⟩ : Fin (n / 2)) = a₀ := Fin.ext (by simp [ha₀])
        rw [h0, ← hθ]
        exact ccOrbit_self θ
      | succ d ih =>
        intro hd
        have hd' : d < n / 2 := by omega
        have hstep := ccOrbit_geo_stdRefl (ih hd') (⟨d, hd'⟩ : Fin (n / 2))
        rwa [geo_stdRefl_two_single_succ (⟨d, hd'⟩ : Fin (n / 2)) hd] at hstep
    exact hmain b.val b.isLt
  have hneg : ∀ b : Fin (n / 2), ccOrbit n θ (-(2 • Pi.single b 1)) := by
    have hlast : ∀ k : Fin (n / 2), ¬k.val + 1 < n / 2 →
        ccOrbit n θ (-(2 • Pi.single k 1)) := by
      intro k hk
      have hk' : k = (⟨n / 2 - 1, by omega⟩ : Fin (n / 2)) := by
        ext
        simp only
        omega
      rw [hk']
      have hstep := ccOrbit_geo_stdRefl (hpos ⟨n / 2 - 1, by omega⟩) ⟨n / 2 - 1, by omega⟩
      rwa [geo_stdRefl_two_single_last ⟨n / 2 - 1, by omega⟩ (by omega)] at hstep
    intro b
    exact geo_reach_smul_single (fun e => ccOrbit n θ (-e))
      (fun k e he => by
        rw [← geo_stdRefl_neg]
        exact ccOrbit_geo_stdRefl he k)
      2 hlast (n / 2 - 1 - b.val) b (by omega)
  obtain ⟨p, rfl | rfl⟩ := exists_lowIdx hi
  · have h := hpos p
    rw [geo_weight_lowIdx]
    exact h
  · have h := hneg p
    rw [geo_weight_rev_lowIdx]
    simpa only [smul_neg] using h

theorem ggLongRoot_of_two_smul_weight {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {β : Fin (n / 2) → ℤ}
    (hβ : β ∈ roots (isFiniteType_cartan n) (divisible n)) {i : Fin n} (hi : i ≠ Fin.rev i)
    (h : toStd n β = 2 • weight n i) : GGLongRoot (Unitary.rootDatum hc n) β := by
  have hn : 2 ≤ n := by
    rcases hβ with ⟨_, l, _⟩ | ⟨_, l, _⟩ <;> have := l.isLt <;> omega
  have hm : 0 < n / 2 := by omega
  obtain ⟨θ, hθ⟩ := geo_gPSUr_exists_highest hn
  have hθ' : toStd n θ = 2 • Pi.single (⟨0, hm⟩ : Fin (n / 2)) 1 := by
    rw [hθ, geo_weight_lowIdx]
  have hθr : θ ∈ (Unitary.rootDatum hc n).roots := by
    change θ ∈ roots (isFiniteType_cartan n) (divisible n)
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨lowIdx ⟨0, by omega⟩, lowIdx_ne_rev _ _, hθ⟩)
  have hmax : ∀ δ ∈ (Unitary.rootDatum hc n).roots, ht δ ≤ ht θ := by
    intro δ hδ
    have hδ' : δ ∈ roots (isFiniteType_cartan n) (divisible n) := hδ
    have hδle := ht_le_of_mem_roots' hδ'
    have hθht : ht θ = (n : ℤ) - 1 := by
      have h2 := two_mul_ht θ
      rw [hθ, map_nsmul, lv_weight] at h2
      simp only [val_lowIdx, Nat.cast_zero, mul_zero, sub_zero, nsmul_eq_mul] at h2
      omega
    rw [hθht]
    exact hδle
  have hθlong : GGLongRoot (Unitary.rootDatum hc n) θ :=
    ⟨1, θ, hθr, hmax, by rw [map_one]; rfl⟩
  have horbit := ccOrbit_two_weight (θ := θ) (a₀ := ⟨0, hm⟩) rfl hθ' hi
  obtain ⟨w, hw⟩ := horbit
  have hγlong : GGLongRoot (Unitary.rootDatum hc n)
      (weylAction (isFiniteType_cartan n) w θ) :=
    ⟨w, θ, hθr, hmax, rfl⟩
  have hγeq : weylAction (isFiniteType_cartan n) w θ = β :=
    toStd_inj' (by rw [hw, h])
  rwa [hγeq] at hγlong

private theorem exists_rt_of_mem_roots_short {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {β : Fin (n / 2) → ℤ}
    (hβ : β ∈ (Unitary.rootDatum hc n).roots) (hs : ¬ GGLongRoot (Unitary.rootDatum hc n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hc n).roots) :
    ∃ a b : Fin (n / 2) ⊕ Fin (n / 2), idx a ≠ idx b ∧ toStd n β = rt a b ∧
      toStd n (-β) = rt (Sum.swap b) (Sum.swap a) := by
  have hβ' : β ∈ roots (isFiniteType_cartan n) (divisible n) := hβ
  rw [roots_eq] at hβ'
  rcases hβ' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨hodd, i, hi, h⟩
  · obtain ⟨a, ha⟩ := su_exists_crd hi
    obtain ⟨b, hb⟩ := su_exists_crd (by rw [Fin.rev_rev]; exact Ne.symm hj)
    have hrt : rt a b = weight n i - weight n j := by
      rw [rt, ← weight_crd a, ← weight_crd b, ha, hb, weight_rev', sub_eq_add_neg]
    have hab : idx a ≠ idx b := by
      intro hh
      rcases eq_or_eq_swap_of_idx_eq hh with h' | h'
      · have hrev : Fin.rev j = i := by rw [← hb, h', ha]
        exact hji (by rw [← hrev, Fin.rev_rev])
      · have hrev : Fin.rev j = Fin.rev i := by rw [← hb, h', crd_swap, ha]
        exact hij (Fin.rev_inj.mp hrev.symm)
    refine ⟨a, b, hab, h.trans hrt.symm, ?_⟩
    rw [geo_gPSUr_toStd_neg, h, rt_comm (Sum.swap b) (Sum.swap a), rt_swap_swap, ← hrt]
  · exact absurd (ggLongRoot_of_two_smul_weight hc hβ hi h) hs
  · refine absurd (?_ : 2 • β ∈ roots (isFiniteType_cartan n) (divisible n)) h2β
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨i, hi, by rw [toStd_nsmul_two, h]⟩)

private theorem su_herm_mat {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (u : SU (unitaryInvolution F 2 f) n)
    (p q : Fin n) :
    (suH hc n).β (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single p 1)
        (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single q 1) =
      if q = Fin.rev p then 1 else 0 := by
  have hσ := unitaryInvolution_involutive hc
  have h := isIsometric_natRep_SU (unitaryInvolution F 2 f) hσ n u
    (Pi.single p 1) (Pi.single q 1)
  rw [natRep_apply, natRep_apply] at h
  change (suForm (unitaryInvolution F 2 f) hσ n).β _ _ = _
  have h' : (suForm (unitaryInvolution F 2 f) hσ n).β
      (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single p 1)
      (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single q 1) =
      (suForm (unitaryInvolution F 2 f) hσ n).β (Pi.single p 1) (Pi.single q 1) := by
    simpa only [mat_apply] using h
  rw [h', suForm_β]
  rw [Finset.sum_eq_single p]
  · simp [Pi.single_apply, eq_comm]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

private theorem pairGen_eq_mat_suElt {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {a b : Fin (n / 2) ⊕ Fin (n / 2)} (hab : idx a ≠ idx b) (c : F) :
    1 + c • Matrix.vecMulVec (Pi.single (crd a) 1)
          (Matrix.vecMul (fun i => σ ((Pi.single (crd b) 1 : Fin n → F) i))
            (Unitary.antidiag n)) -
        σ c • Matrix.vecMulVec (Pi.single (crd b) 1)
          (Matrix.vecMul (fun i => σ ((Pi.single (crd a) 1 : Fin n → F) i))
            (Unitary.antidiag n)) =
      mat σ n (suElt σ hσ a b c) := by
  have hσsingle : ∀ p : Fin n, (fun i => σ ((Pi.single p 1 : Fin n → F) i)) =
      (Pi.single p 1 : Fin n → F) := by
    intro p
    funext i
    by_cases h : i = p
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hvec : ∀ p : Fin n,
      Matrix.vecMul (fun i => σ ((Pi.single p 1 : Fin n → F) i)) (Unitary.antidiag n) =
        Pi.single (Fin.rev p) 1 := by
    intro p
    rw [hσsingle p]
    have h := geo_gPSUr_vecMul_single_rev (n := n) (F := F) (Fin.rev p)
    rwa [Fin.rev_rev] at h
  have hvs : ∀ p q : Fin n, Matrix.vecMulVec (Pi.single p (1 : F)) (Pi.single q (1 : F)) =
      (Matrix.single p q 1 : Matrix (Fin n) (Fin n) F) := by
    intro p q
    ext x y
    by_cases hx : x = p
    · subst hx
      by_cases hy : y = q
      · subst hy; simp [Matrix.vecMulVec, Pi.single_apply, Matrix.single_apply]
      · simp [Matrix.vecMulVec, Pi.single_apply, Matrix.single_apply, hy, Ne.symm hy]
    · by_cases hy : y = q
      · subst hy
        simp [Matrix.vecMulVec, Pi.single_apply, Matrix.single_apply, hx, Ne.symm hx]
      · simp [Matrix.vecMulVec, Pi.single_apply, Matrix.single_apply, hx, hy,
          Ne.symm hx, Ne.symm hy]
  rw [mat_suElt hσ hab, hvec (crd b), hvec (crd a), ← crd_swap b, ← crd_swap a,
    hvs (crd a) (crd (Sum.swap b)), hvs (crd b) (crd (Sum.swap a))]
  rw [show c • (Matrix.single (crd a) (crd (Sum.swap b)) 1 : Matrix (Fin n) (Fin n) F) =
      Matrix.single (crd a) (crd (Sum.swap b)) c from by
    ext x y
    by_cases hx : x = crd a <;> by_cases hy : y = crd (Sum.swap b) <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]
  rw [show σ c • (Matrix.single (crd b) (crd (Sum.swap a)) 1 : Matrix (Fin n) (Fin n) F) =
      Matrix.single (crd b) (crd (Sum.swap a)) (σ c) from by
    ext x y
    by_cases hx : x = crd b <;> by_cases hy : y = crd (Sum.swap a) <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]

private theorem rootGroup_map_subtype_short {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {a b : Fin (n / 2) ⊕ Fin (n / 2)} (hab : idx a ≠ idx b)
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt a b) :
    (rootGroup σ hσ n γ).map (SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Pi.single (crd a) 1) (Pi.single (crd b) 1) := by
  have hmem : ∀ g : SU σ n, g ∈ rootGroup σ hσ n γ ↔ ∃ c, suElt σ hσ a b c = g :=
    fun g => geo_gPSUr_mem_rootGroup_short σ hσ hab hγ g
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hmem x).1 hx
    refine Subgroup.subset_closure ⟨c, ?_⟩
    change ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
    rw [← hc]
    exact (pairGen_eq_mat_suElt σ hσ hab c).symm
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_map.2 ⟨suElt σ hσ a b c, (hmem _).2 ⟨c, rfl⟩, ?_⟩
    apply Units.ext
    change (((suElt σ hσ a b c : SU σ n) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F)
    exact (pairGen_eq_mat_suElt σ hσ hab c).symm.trans hg.symm

private theorem eq_comap_of_map_subtype_eq {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    {G : Subgroup (SU σ n)} {C : Subgroup (GL (Fin n) F)}
    (h : G.map (SU σ n).subtype = C) : G = C.comap (SU σ n).subtype := by
  have h' := Subgroup.comap_map_eq_self_of_injective
    (f := (SU σ n).subtype) (SU σ n).subtype_injective G
  rw [h] at h'
  exact h'.symm

private theorem map_conj_rootGroup_eq_suPair {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {a b : Fin (n / 2) ⊕ Fin (n / 2)} (hab : idx a ≠ idx b)
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt a b) (u : SU σ n) :
    (rootGroup σ hσ n γ).map (MulAut.conj u).toMonoidHom =
      (unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (mat σ n u *ᵥ Pi.single (crd a) 1)
        (mat σ n u *ᵥ Pi.single (crd b) 1)).comap (SU σ n).subtype := by
  refine eq_comap_of_map_subtype_eq σ ?_
  rw [geo_gPSUr_map_conj_subtype σ u (rootGroup σ hσ n γ),
    rootGroup_map_subtype_short σ hσ hab hγ,
    geo_gPSUr_unitPairGroup_conj σ u (Pi.single (crd a) 1) (Pi.single (crd b) 1)]
  rfl

private theorem suFrame_conj {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} {a b : Fin (n / 2) ⊕ Fin (n / 2)}
    (hab : idx a ≠ idx b) (u : SU (unitaryInvolution F 2 f) n) :
    SUFrame hc n (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd a) 1)
      (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd b) 1)
      (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd (Sum.swap b)) 1)
      (mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd (Sum.swap a)) 1) := by
  unfold SUFrame
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [su_herm_mat hc u (crd a) (crd (Sum.swap a)), if_pos (crd_swap a)]
  · rw [su_herm_mat hc u (crd b) (crd (Sum.swap b)), if_pos (crd_swap b)]
  · rw [su_herm_mat hc u (crd a) (crd a), if_neg (crd_ne_rev a)]
  · rw [su_herm_mat hc u (crd b) (crd b), if_neg (crd_ne_rev b)]
  · rw [su_herm_mat hc u (crd (Sum.swap b)) (crd (Sum.swap b)), if_neg (crd_ne_rev _)]
  · rw [su_herm_mat hc u (crd (Sum.swap a)) (crd (Sum.swap a)), if_neg (crd_ne_rev _)]
  · rw [su_herm_mat hc u (crd a) (crd b), if_neg]
    intro h
    exact ne_swap_of_idx_ne hab (crd_injective (by rwa [← crd_swap a] at h))
  · rw [su_herm_mat hc u (crd a) (crd (Sum.swap b)), if_neg]
    intro h
    have h1 : Fin.rev (crd b) = Fin.rev (crd a) := (crd_swap b).symm.trans h
    exact (ne_of_idx_ne hab) (crd_injective (Fin.rev_inj.mp h1))
  · rw [su_herm_mat hc u (crd b) (crd (Sum.swap a)), if_neg]
    intro h
    have h1 : Fin.rev (crd a) = Fin.rev (crd b) := (crd_swap a).symm.trans h
    exact (ne_of_idx_ne (Ne.symm hab)) (crd_injective (Fin.rev_inj.mp h1))
  · rw [su_herm_mat hc u (crd (Sum.swap b)) (crd (Sum.swap a)), if_neg]
    intro h
    have h1 : Fin.rev (crd a) = crd b := by
      rw [← crd_swap a, h, crd_swap b, Fin.rev_rev]
    have h2 : a = Sum.swap b := by
      refine crd_injective ?_
      rw [crd_swap b, ← h1, Fin.rev_rev]
    exact ne_swap_of_idx_ne hab (by rw [h2, Sum.swap_swap])

theorem exists_unitPairGroup_eq_conj_rootGroup_SU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ)
    {β : Fin (Unitary.rootDatum hc n).rank → ℤ}
    (hβ : β ∈ (Unitary.rootDatum hc n).roots) (hs : ¬ GGLongRoot (Unitary.rootDatum hc n) β)
    (h2β : 2 • β ∉ (Unitary.rootDatum hc n).roots)
    (u : ↥(SU (unitaryInvolution F 2 f) n)) :
    ∃ v w v' w' : Fin n → F, SUFrame hc n v w v' w' ∧
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom) =
        suPair (unitaryInvolution F 2 f) n v w ∧
      (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom) =
        suPair (unitaryInvolution F 2 f) n v' w' := by
  obtain ⟨a, b, hab, hγ, hγ'⟩ := exists_rt_of_mem_roots_short hc hβ hs h2β
  have hσ := unitaryInvolution_involutive hc
  refine ⟨mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd a) 1,
    mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd b) 1,
    mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd (Sum.swap b)) 1,
    mat (unitaryInvolution F 2 f) n u *ᵥ Pi.single (crd (Sum.swap a)) 1,
    suFrame_conj hc hab u, ?_, ?_⟩
  · have hmem := map_conj_rootGroup_eq_suPair (unitaryInvolution F 2 f) hσ hab hγ u
    exact hmem
  · have hab' : idx (Sum.swap b) ≠ idx (Sum.swap a) := by
      simpa only [idx_swap] using Ne.symm hab
    have hmem := map_conj_rootGroup_eq_suPair (unitaryInvolution F 2 f) hσ hab' hγ' u
    exact hmem

end CFSG.StandardType.LieKnownR2.Geo

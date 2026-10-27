module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms
public import CFSG.Timmesfeld.Transvection.ModelRankSU
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoWittSU
public import CFSG.Timmesfeld.Transvection.PresSUModel
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.LieEmbed.UnitaryIsometry
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.Timmesfeld.Transvection.Pres

private theorem gPSUr_traceZero_iff {F : Type} [Field F] [CharP F 2] (σ : F →+* F)
    (c : F) : c + σ c = 0 ↔ σ c = c := by
  constructor
  · intro h
    have h2 : σ c = -c := eq_neg_of_add_eq_zero_right h
    rw [h2, CharTwo.neg_eq]
  · intro h
    rw [h, ← two_mul]
    exact mul_eq_zero_of_left (CharP.cast_eq_zero F 2) c

theorem isUTransGroup_map_subtype_eq_unitTransvGroup {F : Type} [Field F] [CharP F 2]
    {n : ℕ} (σ : F ≃+* F) {v : Fin n → F} {X : Subgroup (Unitary.SU σ n)}
    (hX : CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ v X) :
    X.map (Unitary.SU σ n).subtype =
      unitTransvGroup σ.toRingHom (Unitary.antidiag n) v := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨c, hc, hx'⟩ := (hX.1 x).1 hx
    have hc' : σ c = c := (gPSUr_traceZero_iff σ.toRingHom c).1 hc
    refine Subgroup.subset_closure ⟨c, hc', ?_⟩
    change CFSG.Timmesfeld.LieEmbed.suMat σ n x = _
    rw [hx']
    simp only [CFSG.Timmesfeld.LieEmbed.uTrans, CFSG.Timmesfeld.LieEmbed.uNil,
      CFSG.Timmesfeld.LieEmbed.uRow]
    rfl
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hc, hg⟩
    have hc' : c + σ c = 0 := (gPSUr_traceZero_iff σ.toRingHom c).2 hc
    obtain ⟨x, hx⟩ := hX.2 c hc'
    refine Subgroup.mem_map.2 ⟨x, ?_, ?_⟩
    · rw [hX.1 x]
      exact ⟨c, hc', hx⟩
    · apply Units.ext
      change CFSG.Timmesfeld.LieEmbed.suMat σ n x =
        ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [hx, hg]
      simp only [CFSG.Timmesfeld.LieEmbed.uTrans, CFSG.Timmesfeld.LieEmbed.uNil,
        CFSG.Timmesfeld.LieEmbed.uRow]
      rfl

private theorem gPSUr_weight_lowIdx {n : ℕ} (a : Fin (n / 2)) :
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

private theorem gPSUr_toStd_apply_of_even {n : ℕ} (he : Even n) (v : Fin (n / 2) → ℤ)
    (a : Fin (n / 2)) :
    toStd n v a = (if a.val + 1 = n / 2 then 2 else 1) * v a -
      (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) := by
  rw [toStd, if_pos he]
  rfl

private theorem gPSUr_exists_highest {n : ℕ} (hn : 2 ≤ n) :
    ∃ θ : Fin (n / 2) → ℤ,
      toStd n θ = 2 • weight n (lowIdx (⟨0, by omega⟩ : Fin (n / 2))) := by
  have hm : 0 < n / 2 := by omega
  by_cases he : Even n
  · refine ⟨fun a => if a.val + 1 = n / 2 then 1 else 2, ?_⟩
    funext a
    rw [gPSUr_toStd_apply_of_even he, gPSUr_weight_lowIdx, Pi.smul_apply,
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
    rw [gPSUr_weight_lowIdx, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
    simp only [toStd, if_neg he]
    by_cases h0 : a.val = 0
    · have : a = ⟨0, hm⟩ := Fin.ext h0
      subst this
      simp
    · have h1 : 0 < a.val := Nat.pos_of_ne_zero h0
      have hne : ¬ (a = ⟨0, hm⟩) := fun e => h0 (by rw [e])
      simp [h1, hne]

private theorem gPSUr_toStd_maxHeight {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n)
    {γ : Fin (n / 2) → ℤ} (hγ : γ ∈ (Unitary.rootDatum hc n).roots)
    (hmax : ∀ δ ∈ (Unitary.rootDatum hc n).roots, ht δ ≤ ht γ) :
    ∃ i : Fin n, i ≠ Fin.rev i ∧ toStd n γ = 2 • weight n i := by
  obtain ⟨θ, hθ⟩ := gPSUr_exists_highest hn
  have hm : 0 < n / 2 := by omega
  have hθr : θ ∈ (Unitary.rootDatum hc n).roots := by
    show θ ∈ roots (isFiniteType_cartan n) (divisible n)
    rw [roots_eq]
    exact Or.inr (Or.inl ⟨lowIdx ⟨0, hm⟩, lowIdx_ne_rev _ _, hθ⟩)
  have hle : ht θ ≤ ht γ := hmax θ hθr
  have hθ2 : ht θ = (n : ℤ) - 1 := by
    have h := two_mul_ht θ
    have h0 : (lowIdx (⟨0, hm⟩ : Fin (n / 2))).val = 0 := val_lowIdx _
    rw [hθ, map_nsmul, lv_weight, h0] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_zero, mul_zero, sub_zero] at h
    omega
  have h2 := two_mul_ht γ
  have hγ'' : γ ∈ roots (isFiniteType_cartan n) (divisible n) := hγ
  rw [roots_eq] at hγ''
  rcases hγ'' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exfalso
    rw [h, map_sub, lv_weight, lv_weight] at h2
    have hi' := i.isLt
    have hj' := j.isLt
    exact hji (Fin.ext (by rw [Fin.val_rev]; omega))
  · exact ⟨i, hi, h⟩
  · exfalso
    rw [h, lv_weight] at h2
    have hi' := i.isLt
    omega

private theorem gPSUr_vecMul_smul {F : Type} [CommSemiring F] {n : ℕ} (c : F) (v : Fin n → F)
    (M : Matrix (Fin n) (Fin n) F) :
    Matrix.vecMul (fun i => c * v i) M = c • Matrix.vecMul v M := by
  funext b
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

private theorem gPSUr_unitTransvGroup_smul {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (hσ : ∀ c, σ (σ c) = c) {α : F} (hα : α ≠ 0) (x : Fin n → F) :
    unitTransvGroup σ (Unitary.antidiag n) (α • x) =
      unitTransvGroup σ (Unitary.antidiag n) x := by
  have hvec : ∀ β : F,
      Matrix.vecMulVec (β • x) (Matrix.vecMul (fun i => σ ((β • x) i)) (Unitary.antidiag n)) =
        (β * σ β) • Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n)) := by
    intro β
    have hrow : Matrix.vecMul (fun i => σ ((β • x) i)) (Unitary.antidiag n) =
        σ β • Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n) := by
      rw [show (fun i => σ ((β • x) i)) = (fun i => σ β * σ (x i)) by
        funext i
        simp [Pi.smul_apply, map_mul]]
      exact gPSUr_vecMul_smul (σ β) (fun i => σ (x i)) (Unitary.antidiag n)
    rw [hrow]
    ext a b
    show (β * x a) * (σ β * Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n) b) =
      (β * σ β) * (x a * Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n) b)
    ring
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hc, hg⟩
    refine Subgroup.subset_closure ⟨c * α * σ α, ?_, ?_⟩
    · rw [map_mul, map_mul, hσ, hc]
      ring
    · rw [hg, hvec α, smul_smul, mul_assoc]
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hc, hg⟩
    have hmem : α * σ α ≠ 0 := mul_ne_zero hα ((map_ne_zero σ).2 hα)
    have hx : Matrix.vecMulVec x (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n)) =
        (α * σ α)⁻¹ • Matrix.vecMulVec (α • x)
          (Matrix.vecMul (fun i => σ ((α • x) i)) (Unitary.antidiag n)) := by
      rw [hvec α, smul_smul, inv_mul_cancel₀ hmem, one_smul]
    refine Subgroup.subset_closure ⟨c * (α * σ α)⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv₀, map_mul, hσ, hc, mul_comm (σ α) α]
    · rw [hg, hx, smul_smul]

private theorem gPSUr_toStd_neg (n : ℕ) (v : Fin (n / 2) → ℤ) :
    toStd n (-v) = -toStd n v := by
  by_cases he : Even n
  · funext a
    simp only [toStd, if_pos he, CFSG.LieType.Universal.Symplectic.toStd, Pi.neg_apply]
    split_ifs <;> ring
  · funext a
    simp only [toStd, if_neg he, Pi.neg_apply]
    split_ifs <;> ring

theorem toStd_neg_eq_two_weight_rev {n : ℕ} {γ : Fin (n / 2) → ℤ} {i : Fin n}
    (hγ : toStd n γ = 2 • weight n i) :
    toStd n (-γ) = 2 • weight n (Fin.rev i) := by
  rw [gPSUr_toStd_neg, hγ, CFSG.LieType.Universal.Unitary.SUExtras.weight_rev', smul_neg]

theorem exists_conj_rootGroup_eq_unitTransvGroup_PSU_of_toStd
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n)
    (i : Fin n) (hi : i ≠ Fin.rev i) (γ : Fin (n / 2) → ℤ)
    (hβi : toStd n γ = 2 • weight n i) (v w : Fin n → F)
    (hv : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1) :
    ∃ u : ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      (((Unitary.rootDatum hc n).rootGroup γ).map (MulAut.conj u).toMonoidHom).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) v ∧
      (((Unitary.rootDatum hc n).rootGroup (-γ)).map (MulAut.conj u).toMonoidHom).map
          (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
        unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
          (Unitary.antidiag n) w := by
  classical
  set σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 f with hσdef
  have hσ : ∀ c, σ (σ c) = c := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  have hIγ : CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ (Pi.single i 1)
      (Unitary.rootGroup σ hσ n γ) :=
    CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hi hβi
  have hβineg : toStd n (-γ) = 2 • weight n (Fin.rev i) :=
    toStd_neg_eq_two_weight_rev hβi
  have hineg : Fin.rev i ≠ Fin.rev (Fin.rev i) := by
    rw [Fin.rev_rev]
    exact hi.symm
  have hIneg : CFSG.Timmesfeld.LieEmbed.IsUTransGroup σ (Pi.single (Fin.rev i) 1)
      (Unitary.rootGroup σ hσ n (-γ)) :=
    CFSG.Timmesfeld.Transvection.ModelRank.isUTransGroup_rootGroup_long' hσ hineg hβineg
  obtain ⟨u, α, β, hα, hβ, hu1, hu2⟩ :=
    Geo.exists_su_mulVec_single_eq_smul hc hi v w hv hw hvw
  refine ⟨u, ?_, ?_⟩
  · have hmap := isUTransGroup_map_subtype_eq_unitTransvGroup σ (hIγ.conjSub u)
    rw [CFSG.Timmesfeld.LieEmbed.suMat_apply, hu1] at hmap
    rw [gPSUr_unitTransvGroup_smul σ.toRingHom hσ hα v] at hmap
    exact hmap
  · have hmap := isUTransGroup_map_subtype_eq_unitTransvGroup σ (hIneg.conjSub u)
    rw [CFSG.Timmesfeld.LieEmbed.suMat_apply, hu2] at hmap
    rw [gPSUr_unitTransvGroup_smul σ.toRingHom hσ hβ w] at hmap
    exact hmap


private theorem gPSUr_long {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n) (v w : Fin n → F)
    (hv : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1) :
    ∃ β, β ∈ (Unitary.rootDatum hc n).roots ∧ GGLongRoot (Unitary.rootDatum hc n) β ∧ ∃ u :
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v ∧
        (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) w := by
  classical
  obtain ⟨γ₀, hγ₀, hmax₀⟩ :=
    exists_maxHeight (D := Unitary.rootDatum hc n) (show 0 < n / 2 by omega)
  let γ : Fin (n / 2) → ℤ := γ₀
  have hγ : γ ∈ (Unitary.rootDatum hc n).roots := hγ₀
  have hmax : ∀ δ ∈ (Unitary.rootDatum hc n).roots, ht δ ≤ ht γ := hmax₀
  have hlong : GGLongRoot (Unitary.rootDatum hc n) γ :=
    ⟨1, γ, hγ, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨i, hi, hβi⟩ := gPSUr_toStd_maxHeight hc hn hγ hmax
  obtain ⟨u, hpos, hneg⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU_of_toStd hc n hn i hi γ hβi v w hv hw hvw
  exact ⟨γ, hγ, hlong, u, hpos, hneg⟩

theorem exists_conj_rootGroup_eq_unitTransvGroup_PSU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 2 ≤ n) (v w : Fin n → F)
    (hv : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1) :
    ∃ β, β ∈ (Unitary.rootDatum hc n).roots ∧ GGLongRoot (Unitary.rootDatum hc n) β ∧ ∃ u :
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v ∧
        (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) w := by
  exact gPSUr_long hc n hn v w hv hw hvw

private theorem gPSUr_mem_rootGroup_short {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {A B : Fin (n / 2) ⊕ Fin (n / 2)}
    (hAB : idx A ≠ idx B) {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt A B) (g : SU σ n) :
    g ∈ rootGroup σ hσ n γ ↔ ∃ c : F, suElt σ hσ A B c = g := by
  by_cases he : Even n
  · exact mem_rootGroup_iff_suElt (m := n) hσ he hAB hγ g
  · exact mem_rootGroup_iff_suElt_odd (m := n) hσ hAB hγ g

private theorem gPSUr_vecMul_single_rev {F : Type} [Field F] {n : ℕ} (a : Fin n) :
    Matrix.vecMul (Pi.single (Fin.rev a) (1 : F)) (Unitary.antidiag n) = Pi.single a 1 := by
  funext i
  simp only [CFSG.Timmesfeld.LieEmbed.vecMul_antidiag, Pi.single_apply, Fin.rev_inj]

private theorem gPSUr_pairGen {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F) (a b : Fin n) (c : F) :
    1 + c • Matrix.vecMulVec (Pi.single a 1)
          (Matrix.vecMul (fun i => σ.toRingHom ((Pi.single (Fin.rev b) 1 : Fin n → F) i))
            (Unitary.antidiag n)) -
      σ.toRingHom c • Matrix.vecMulVec (Pi.single (Fin.rev b) 1)
          (Matrix.vecMul (fun i => σ.toRingHom ((Pi.single a 1 : Fin n → F) i))
            (Unitary.antidiag n))
    = rootMatrix σ a b c := by
  have hσsingle : ∀ p : Fin n,
      (fun i => σ.toRingHom (((Pi.single p (1 : F)) : Fin n → F) i)) =
        ((Pi.single p (1 : F)) : Fin n → F) := by
    intro p
    funext i
    by_cases h : i = p
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have h3 : Matrix.vecMul (Pi.single a (1 : F)) (Unitary.antidiag n) =
      Pi.single (Fin.rev a) 1 := by
    have h := gPSUr_vecMul_single_rev (F := F) (n := n) (Fin.rev a)
    rw [Fin.rev_rev] at h
    exact h
  rw [hσsingle (Fin.rev b), hσsingle a, gPSUr_vecMul_single_rev b, h3]
  have hvs : ∀ p q : Fin n,
      Matrix.vecMulVec (Pi.single p (1 : F)) (Pi.single q (1 : F)) =
        (Matrix.single p q 1 : Matrix (Fin n) (Fin n) F) := by
    intro p q
    ext x y
    by_cases hx : x = p <;> by_cases hy : y = q <;>
      simp_all [Matrix.vecMulVec, Pi.single_apply, Matrix.single_apply, eq_comm]
  rw [hvs a b, hvs (Fin.rev b) (Fin.rev a)]
  rw [show c • (Matrix.single a b 1 : Matrix (Fin n) (Fin n) F) = Matrix.single a b c from by
    ext x y
    by_cases hx : x = a <;> by_cases hy : y = b <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]
  rw [show σ.toRingHom c • (Matrix.single (Fin.rev b) (Fin.rev a) 1 :
        Matrix (Fin n) (Fin n) F) =
      Matrix.single (Fin.rev b) (Fin.rev a) (σ.toRingHom c) from by
    ext x y
    by_cases hx : x = Fin.rev b <;> by_cases hy : y = Fin.rev a <;>
      simp [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, hx, hy, eq_comm]]
  rw [rootMatrix]
  rfl

private theorem gPSUr_suElt_matrix {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (hσ : ∀ c, σ (σ c) = c) {k j : Fin (n / 2)} (hkj : k ≠ j) (c : F) :
    (((suElt σ hσ (Sum.inl k) (Sum.inr j) c : SU σ n) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      rootMatrix σ (lowIdx k) (lowIdx j) c := by
  unfold suElt
  rw [dif_pos (by simpa [idx] using hkj)]
  rfl

private theorem gPSUr_rootGroup_map_subtype_short {F : Type} [Field F] {n : ℕ}
    (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c) {k j : Fin (n / 2)} (hkj : k ≠ j)
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt (Sum.inl k) (Sum.inr j)) :
    (rootGroup σ hσ n γ).map (SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (Pi.single (lowIdx k) 1)
        (Pi.single (Fin.rev (lowIdx j)) 1) := by
  have hAB : idx (Sum.inl k) ≠ idx (Sum.inr j) := by simpa [idx] using hkj
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (gPSUr_mem_rootGroup_short σ hσ hAB hγ x).1 hx
    refine Subgroup.subset_closure ⟨c, ?_⟩
    change ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = _
    rw [← hc, gPSUr_suElt_matrix σ hσ hkj c]
    exact (gPSUr_pairGen σ (lowIdx k) (lowIdx j) c).symm
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.mem_map.2 ⟨suElt σ hσ (Sum.inl k) (Sum.inr j) c,
      (gPSUr_mem_rootGroup_short σ hσ hAB hγ _).2 ⟨c, rfl⟩, ?_⟩
    apply Units.ext
    change (((suElt σ hσ (Sum.inl k) (Sum.inr j) c : SU σ n) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F)
    rw [gPSUr_suElt_matrix σ hσ hkj c]
    exact (hg.trans (gPSUr_pairGen σ (lowIdx k) (lowIdx j) c)).symm

private theorem gPSUr_two_nsmul_single_notMem_roots {n : ℕ} {k : Fin (n / 2)}
    (hk : k.val + 1 < n / 2) :
    2 • (Pi.single k 1 : Fin (n / 2) → ℤ) ∉ roots (isFiniteType_cartan n) (divisible n) := by
  have hstd : toStd n (2 • (Pi.single k 1 : Fin (n / 2) → ℤ)) =
      2 • (weight n (lowIdx k) - weight n (lowIdx ⟨k.val + 1, hk⟩)) := by
    rw [toStd_nsmul_two, toStd_short]
  have hne : k ≠ (⟨k.val + 1, hk⟩ : Fin (n / 2)) := by
    intro e
    have h : k.val = k.val + 1 := by simpa using congrArg Fin.val e
    omega
  have ha1 : weight n (lowIdx k) k = 1 := by
    rw [gPSUr_weight_lowIdx]
    simp
  have ha2 : weight n (lowIdx k) ⟨k.val + 1, hk⟩ = 0 := by
    rw [gPSUr_weight_lowIdx, Pi.single_apply, if_neg (Ne.symm hne)]
  have hb1 : weight n (lowIdx ⟨k.val + 1, hk⟩) k = 0 := by
    rw [gPSUr_weight_lowIdx, Pi.single_apply, if_neg hne]
  have hb2 : weight n (lowIdx ⟨k.val + 1, hk⟩) ⟨k.val + 1, hk⟩ = 1 := by
    rw [gPSUr_weight_lowIdx]
    simp
  rw [roots_eq]
  rintro (⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩)
  · rw [hstd] at h
    have hev : weight n (lowIdx k) - weight n (lowIdx ⟨k.val + 1, hk⟩) ≠ 0 := by
      intro h0
      have := congrFun h0 k
      rw [Pi.sub_apply, ha1, hb1, sub_zero] at this
      exact one_ne_zero this
    have hw : weight n i = weight n (lowIdx k) - weight n (lowIdx ⟨k.val + 1, hk⟩) :=
      (eq_rev_of_weight_sub_eq_two_smul h.symm hev).2
    have hik : i.val = k.val := by
      have hc := congrFun hw k
      rw [Pi.sub_apply, ha1, hb1, sub_zero] at hc
      rw [weight_apply'] at hc
      split_ifs at hc <;> omega
    have hik1 : i.val + (k.val + 1) + 1 = n := by
      have hc := congrFun hw ⟨k.val + 1, hk⟩
      rw [Pi.sub_apply, ha2, hb2, zero_sub] at hc
      rw [weight_apply'] at hc
      split_ifs at hc <;> omega
    omega
  · rw [hstd] at h
    have h1 : weight n i k = 1 := by
      have hc := congrFun h k
      rw [Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, ha1, hb1, sub_zero] at hc
      norm_num at hc
      omega
    have h2 : weight n i ⟨k.val + 1, hk⟩ = -1 := by
      have hc := congrFun h ⟨k.val + 1, hk⟩
      rw [Pi.smul_apply, Pi.smul_apply, Pi.sub_apply, ha2, hb2, zero_sub] at hc
      norm_num at hc
      omega
    have hik : i.val = k.val := by
      rw [weight_apply'] at h1
      split_ifs at h1 <;> omega
    have hik1 : i.val + (k.val + 1) + 1 = n := by
      rw [weight_apply'] at h2
      split_ifs at h2 <;> omega
    omega
  · rw [hstd] at h
    have h1 : weight n i k = 2 := by
      have hc := congrFun h k
      rw [Pi.smul_apply, Pi.sub_apply, ha1, hb1, sub_zero] at hc
      norm_num at hc
      omega
    have hb := (weight_apply_bounds i k).2
    omega

private theorem gPSUr_vecMulVec_smul_left {F : Type} [CommSemiring F] {n : ℕ} (α : F)
    (x φ : Fin n → F) :
    Matrix.vecMulVec (α • x) φ = α • Matrix.vecMulVec x φ := by
  ext i j
  simp [Matrix.vecMulVec, Pi.smul_apply, smul_eq_mul]
  ring

private theorem gPSUr_vecMulVec_smul_right {F : Type} [CommSemiring F] {n : ℕ} (α : F)
    (x φ : Fin n → F) :
    Matrix.vecMulVec x (α • φ) = α • Matrix.vecMulVec x φ := by
  ext i j
  simp [Matrix.vecMulVec, Pi.smul_apply, smul_eq_mul]
  ring

private theorem gPSUr_pairGen_smul {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (hσ : ∀ c, σ (σ c) = c) (α β : F) (x y : Fin n → F) (c : F) :
    1 + c • Matrix.vecMulVec (α • x)
          (Matrix.vecMul (fun i => σ ((β • y) i)) (Unitary.antidiag n)) -
      σ c • Matrix.vecMulVec (β • y)
          (Matrix.vecMul (fun i => σ ((α • x) i)) (Unitary.antidiag n)) =
    1 + (c * α * σ β) • Matrix.vecMulVec x
          (Matrix.vecMul (fun i => σ (y i)) (Unitary.antidiag n)) -
      σ (c * α * σ β) • Matrix.vecMulVec y
          (Matrix.vecMul (fun i => σ (x i)) (Unitary.antidiag n)) := by
  have hfun1 : (fun i => σ ((β • y) i)) = (fun i => σ β * σ (y i)) := by
    funext i
    simp [Pi.smul_apply, map_mul]
  have hfun2 : (fun i => σ ((α • x) i)) = (fun i => σ α * σ (x i)) := by
    funext i
    simp [Pi.smul_apply, map_mul]
  rw [hfun1, hfun2, gPSUr_vecMul_smul, gPSUr_vecMul_smul,
    gPSUr_vecMulVec_smul_left, gPSUr_vecMulVec_smul_right,
    gPSUr_vecMulVec_smul_left, gPSUr_vecMulVec_smul_right,
    smul_smul, smul_smul]
  rw [show σ (c * α * σ β) = σ c * (β * σ α) from by
    rw [map_mul, map_mul, hσ]
    ring]
  simp only [smul_smul, mul_assoc]

private theorem gPSUr_unitPairGroup_smul {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    (hσ : ∀ c, σ (σ c) = c) {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) (x y : Fin n → F) :
    unitPairGroup σ (Unitary.antidiag n) (α • x) (β • y) =
      unitPairGroup σ (Unitary.antidiag n) x y := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    refine Subgroup.subset_closure ⟨c * α * σ β, ?_⟩
    rw [hg, gPSUr_pairGen_smul σ hσ α β x y c]
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro g ⟨c, hg⟩
    have hαβ : α * σ β ≠ 0 := mul_ne_zero hα ((map_ne_zero σ).2 hβ)
    refine Subgroup.subset_closure ⟨c * (α * σ β)⁻¹, ?_⟩
    have h1 : c * (α * σ β)⁻¹ * α * σ β = c := by
      have hσβ : σ β ≠ 0 := (map_ne_zero σ).2 hβ
      field_simp [hσβ]
    rw [hg, gPSUr_pairGen_smul σ hσ α β x y (c * (α * σ β)⁻¹), h1]

private theorem gPSUr_pairGen_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
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

private theorem gPSUr_unitPairGroup_conj {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
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
    exact gPSUr_pairGen_conj σ u x y c
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
        gPSUr_pairGen_conj σ u⁻¹
          (x := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) x)
          (y := Matrix.mulVec (((u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) y) c
    · change ((MulAut.conj ((u : GL (Fin n) F))) *
          (MulAut.conj (((u : GL (Fin n) F))⁻¹))) g = g
      rw [← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

private theorem gPSUr_map_conj_subtype {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
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

private theorem gPSUr_short {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) (v₁ w₁ v₂ w₂ : Fin n → F)
    (h₁ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ w₂ = 1)
      (h₂ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₂ = 1)
    (h₀ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0) :
    ∃ β ∈ (Unitary.rootDatum hc n).roots, 2 • β ∉ (Unitary.rootDatum hc n).roots ∧ ∃ u :
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v₁ w₁ ∧
        (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v₂ w₂ := by
  classical
  set σ := CFSG.LieType.BorelTits.unitaryInvolution F 2 f with hσdef
  have hσ : ∀ c, σ (σ c) = c := CFSG.LieType.BorelTits.unitaryInvolution_involutive hc
  let k : Fin (n / 2) := ⟨0, by omega⟩
  let β : Fin (n / 2) → ℤ := Pi.single k 1
  have hkval : k.val = 0 := rfl
  have hk : k.val + 1 < n / 2 := by omega
  let j : Fin (n / 2) := ⟨k.val + 1, hk⟩
  let a : Fin n := lowIdx k
  let b : Fin n := lowIdx j
  have ha : a ≠ Fin.rev a := lowIdx_ne_rev k k
  have hb : b ≠ Fin.rev b := lowIdx_ne_rev j j
  have hab : a ≠ b := by
    dsimp only [a, b, j]
    exact lowIdx_ne_succ hk
  have hab' : a ≠ Fin.rev b := lowIdx_ne_rev k j
  have hba : b ≠ Fin.rev a := lowIdx_ne_rev j k
  obtain ⟨u, α₁, β₁, α₂, β₂, hα₁, hβ₁, hα₂, hβ₂, hu1, hu2, hu3, hu4⟩ :=
    Geo.exists_su_mulVec_single_eq_smul_quad hc ha hb hab hab' v₁ w₁ v₂ w₂ h₁ h₂ h₀
  have hkj : k ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    have hjval : j.val = k.val + 1 := rfl
    omega
  have hγ : toStd n β =
      rt (Sum.inl k) (Sum.inr j) := by
    rw [toStd_short (k := k) hk,
      gPSUr_weight_lowIdx (n := n) (a := k),
      gPSUr_weight_lowIdx (n := n) (a := j), rt_inl_inr]
  have hγ' : toStd n (-β) =
      rt (Sum.inl j) (Sum.inr k) := by
    rw [toStd_short_neg (k := k) hk,
      gPSUr_weight_lowIdx (n := n) (a := j),
      gPSUr_weight_lowIdx (n := n) (a := k), rt_inl_inr]
  have hroot : (rootGroup σ hσ n β).map (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (Pi.single a 1)
        (Pi.single (Fin.rev b) 1) := by
    change (rootGroup σ hσ n β).map (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Pi.single (lowIdx k) 1)
        (Pi.single (Fin.rev (lowIdx j)) 1)
    exact gPSUr_rootGroup_map_subtype_short σ hσ (k := k)
      (j := j) hkj hγ
  have hrootneg : (rootGroup σ hσ n (-β)).map
        (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) (Pi.single b 1)
        (Pi.single (Fin.rev a) 1) := by
    change (rootGroup σ hσ n (-β)).map
        (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n)
        (Pi.single (lowIdx j) 1)
        (Pi.single (Fin.rev (lowIdx k)) 1)
    exact gPSUr_rootGroup_map_subtype_short σ hσ (k := j)
      (j := k) hkj.symm hγ'
  refine ⟨β, ?_, ?_, u, ?_, ?_⟩
  · change β ∈ roots (isFiniteType_cartan n) (divisible n)
    rw [roots_eq]
    left
    refine ⟨a, b, hab, ha, hb, hba, ?_⟩
    rw [hγ, rt_inl_inr, gPSUr_weight_lowIdx, gPSUr_weight_lowIdx]
  · change 2 • β ∉ roots (isFiniteType_cartan n) (divisible n)
    exact gPSUr_two_nsmul_single_notMem_roots hk
  · change ((rootGroup σ hσ n β).map
        (MulAut.conj u).toMonoidHom).map (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) v₁ w₁
    rw [gPSUr_map_conj_subtype σ u (rootGroup σ hσ n β), hroot]
    rw [gPSUr_unitPairGroup_conj σ u (Pi.single a 1) (Pi.single (Fin.rev b) 1)]
    rw [hu1, hu2]
    exact gPSUr_unitPairGroup_smul σ.toRingHom hσ hα₁ hβ₁ v₁ w₁
  · change ((rootGroup σ hσ n (-β)).map
        (MulAut.conj u).toMonoidHom).map (Unitary.SU σ n).subtype =
      unitPairGroup σ.toRingHom (Unitary.antidiag n) v₂ w₂
    rw [gPSUr_map_conj_subtype σ u (rootGroup σ hσ n (-β)), hrootneg]
    rw [gPSUr_unitPairGroup_conj σ u (Pi.single b 1) (Pi.single (Fin.rev a) 1)]
    rw [hu3, hu4]
    exact gPSUr_unitPairGroup_smul σ.toRingHom hσ hα₂ hβ₂ v₂ w₂

theorem exists_conj_rootGroup_eq_unitPairGroup_PSU {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (hn : 4 ≤ n) (v₁ w₁ v₂ w₂ : Fin n → F)
    (h₁ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ w₂ = 1)
      (h₂ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₂ = 1)
    (h₀ : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
      (Unitary.antidiag n) ⬝ᵥ v₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₁ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₁ i))
        (Unitary.antidiag n) ⬝ᵥ v₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (w₁ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0 ∧
      Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) (v₂ i))
        (Unitary.antidiag n) ⬝ᵥ w₂ = 0) :
    ∃ β ∈ (Unitary.rootDatum hc n).roots, 2 • β ∉ (Unitary.rootDatum hc n).roots ∧ ∃ u :
      ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n),
      (((Unitary.rootDatum hc n).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v₁ w₁ ∧
        (((Unitary.rootDatum hc n).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n).subtype =
          unitPairGroup (CFSG.LieType.BorelTits.unitaryInvolution F 2 f).toRingHom
            (Unitary.antidiag n) v₂ w₂ := by
  exact gPSUr_short hc n hn v₁ w₁ v₂ w₂ h₁ h₂ h₀

end CFSG.StandardType.ClassicalPosition

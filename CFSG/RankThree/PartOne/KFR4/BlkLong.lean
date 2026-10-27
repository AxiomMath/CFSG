module

public import CFSG.RankThree.PartOne.KFR4.Defs
public import CFSG.RankThree.CentralLiftU.BlockMat
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.RankThree.PartOne.KFR4.Blk

open Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary
  CFSG.RankThree.CentralLiftU

section Mat

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

omit [Finite K] [CharP K 2] in
theorem matToG_apply (M : GL (Fin 3) E) (v : Vs K E) :
    matToG K M v = ((M : Matrix (Fin 3) (Fin 3) E) *ᵥ v.1, v.2) := rfl

omit [Finite K] [CharP K 2] in
theorem matToG_injective : Function.Injective (matToG (E := E) K) := by
  intro M N h
  refine Matrix.GeneralLinearGroup.ext fun x y => ?_
  have := congrArg (fun g : Vs K E ≃ₗ[K] Vs K E => (g ((Pi.single y 1 : Fin 3 → E), 0)).1 x) h
  simpa [matToG_apply, Matrix.mulVec_single_one] using this

theorem sum_N_mulVec (D : EvenNormPlane K E) {M : Matrix (Fin 3) (Fin 3) E}
    (hM : conjTr D.σ.toRingEquiv M * M = 1) (w : Fin 3 → E) :
    ∑ l, D.N ((M *ᵥ w) l) = ∑ l, D.N (w l) := by
  apply (algebraMap K E).injective
  simp only [map_sum, D.algebraMap_N]
  have h1 : (fun l => D.σ ((M *ᵥ w) l)) = (M.map D.σ.toRingEquiv) *ᵥ (fun l => D.σ (w l)) := by
    funext l
    exact RingHom.map_mulVec D.σ.toRingEquiv.toRingHom M w l
  calc ∑ l, (M *ᵥ w) l * D.σ ((M *ᵥ w) l)
      = (fun l => D.σ ((M *ᵥ w) l)) ⬝ᵥ (M *ᵥ w) := by
        simp only [dotProduct]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    _ = ((M.map D.σ.toRingEquiv) *ᵥ (fun l => D.σ (w l))) ⬝ᵥ (M *ᵥ w) := by rw [h1]
    _ = (fun l => D.σ (w l)) ⬝ᵥ ((conjTr D.σ.toRingEquiv M) *ᵥ (M *ᵥ w)) := by
        rw [conjTr, Matrix.dotProduct_mulVec (fun l => D.σ (w l)), Matrix.vecMul_transpose]
    _ = (fun l => D.σ (w l)) ⬝ᵥ w := by rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
    _ = ∑ l, w l * D.σ (w l) := by
        simp only [dotProduct]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem matToG_mem_O (D : EvenNormPlane K E) {M : GL (Fin 3) E}
    (hM : conjTr D.σ.toRingEquiv (M : Matrix (Fin 3) (Fin 3) E) *
      (M : Matrix (Fin 3) (Fin 3) E) = 1) :
    matToG K M ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [Qs_apply, Qs_apply, matToG_apply, sum_N_mulVec D hM]

theorem N_sigma (D : EvenNormPlane K E) (z : E) : D.N (D.σ z) = D.N z := by
  apply (algebraMap K E).injective
  rw [D.algebraMap_N, D.algebraMap_N, D.sigma_sigma, mul_comm]

theorem conjCoord_mem_O (D : EvenNormPlane K E) (k : Fin 3) :
    conjCoord D k ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [Qs_apply, Qs_apply, conjCoord_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = k
  · simp only [hl, ↓reduceIte, N_sigma]
  · simp only [hl, ↓reduceIte]

end Mat

section BlockEmb

variable {E : Type} [Field E]

@[expose] def pairE (i j : Fin 3) : Fin 2 → Fin 3 := ![i, j]

theorem pairE_injective {i j : Fin 3} (hij : i ≠ j) : Function.Injective (pairE i j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [pairE]

theorem pairE_ne {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (a : Fin 2) : pairE i j a ≠ k := by
  fin_cases a
  · exact Ne.symm hki
  · exact Ne.symm hkj

theorem blockMat_injective' {e : Fin 2 → Fin 3} (he : Function.Injective e) :
    Function.Injective (blockMat (R := E) e) := by
  intro M N h
  ext a b
  rw [← blockMat_apply_e he M a b, ← blockMat_apply_e he N a b, h]

theorem conjTr_blockMat (σ : E ≃+* E) {e : Fin 2 → Fin 3} (he : Function.Injective e)
    (M : Matrix (Fin 2) (Fin 2) E) : conjTr σ (blockMat e M) = blockMat e (conjTr σ M) := by
  ext x y
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  by_cases hx : ∃ a, e a = x
  · by_cases hy : ∃ b, e b = y
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [blockMat_apply_e he, blockMat_apply_e he]
      rfl
    · push Not at hy
      rw [blockMat_apply_of_notMem_left _ hy, blockMat_apply_of_notMem_right _ hy]
      by_cases hxy : x = y
      · subst hxy
        simp
      · rw [Matrix.one_apply_ne (Ne.symm hxy), Matrix.one_apply_ne hxy, map_zero]
  · push Not at hx
    rw [blockMat_apply_of_notMem_right _ hx, blockMat_apply_of_notMem_left _ hx]
    by_cases hxy : x = y
    · subst hxy
      simp
    · rw [Matrix.one_apply_ne (Ne.symm hxy), Matrix.one_apply_ne hxy, map_zero]

theorem blockMat_mulVec_single {e : Fin 2 → Fin 3} (M : Matrix (Fin 2) (Fin 2) E) {k : Fin 3}
    (hk : ∀ a, e a ≠ k) : blockMat e M *ᵥ Pi.single k 1 = Pi.single k 1 := by
  funext x
  rw [Matrix.mulVec_single_one, Matrix.col_apply, blockMat_apply_of_notMem_right _ hk,
    Matrix.one_apply, Pi.single_apply]

@[expose] noncomputable def blkHom {i j : Fin 3} (hij : i ≠ j) : GL (Fin 2) E →* GL (Fin 3) E :=
  Units.map
    { toFun := blockMat (pairE i j)
      map_one' := blockMat_one _
      map_mul' := blockMat_mul (pairE_injective hij) }

theorem coe_blkHom {i j : Fin 3} (hij : i ≠ j) (A : GL (Fin 2) E) :
    ((blkHom hij A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      blockMat (pairE i j) (A : Matrix (Fin 2) (Fin 2) E) := rfl

theorem blkHom_injective {i j : Fin 3} (hij : i ≠ j) : Function.Injective (blkHom (E := E) hij) :=
  fun _ _ h => Units.ext (blockMat_injective' (pairE_injective hij) (congrArg Units.val h))

end BlockEmb

section SuSupp

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem suSupp_col {i j : Fin 3} {M : GL (Fin 3) E} (hM : M ∈ suSupp D i j) {k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j) (x : Fin 3) :
    (M : Matrix (Fin 3) (Fin 3) E) x k = (1 : Matrix (Fin 3) (Fin 3) E) x k := by
  have := congrFun (hM.2 k hki hkj) x
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

theorem suSupp_row {i j : Fin 3} {M : GL (Fin 3) E} (hM : M ∈ suSupp D i j) {k : Fin 3}
    (hki : k ≠ i) (hkj : k ≠ j) (y : Fin 3) :
    (M : Matrix (Fin 3) (Fin 3) E) k y = (1 : Matrix (Fin 3) (Fin 3) E) k y := by
  obtain ⟨⟨-, hiso⟩, hfix⟩ := hM
  have h1 : conjTr D.σ.toRingEquiv (M : Matrix (Fin 3) (Fin 3) E) *ᵥ Pi.single k 1 =
      Pi.single k 1 := by
    conv_lhs => rw [← hfix k hki hkj]
    rw [Matrix.mulVec_mulVec, hiso, Matrix.one_mulVec]
  have h2 := congrFun h1 y
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply] at h2
  apply D.σ.toRingEquiv.injective
  rw [h2, Matrix.one_apply, Pi.single_apply]
  by_cases hky : k = y
  · subst hky
    simp
  · rw [ite_eq_right (Ne.symm hky), ite_eq_right hky, map_zero]

theorem blkHom_mem_suSupp {i j : Fin 3} (hij : i ≠ j) {A : GL (Fin 2) E}
    (hA : A ∈ SUid D.σ.toRingEquiv 2) : blkHom hij A ∈ suSupp D i j := by
  obtain ⟨hdet, hiso⟩ := hA
  refine ⟨⟨?_, ?_⟩, fun k hki hkj => ?_⟩
  · rw [coe_blkHom, det_blockMat (pairE_injective hij), hdet]
  · rw [coe_blkHom, conjTr_blockMat _ (pairE_injective hij),
      ← blockMat_mul (pairE_injective hij), hiso, blockMat_one]
  · rw [coe_blkHom]
    exact blockMat_mulVec_single _ (pairE_ne hki hkj)

theorem exists_blkHom_of_mem_suSupp {i j : Fin 3} (hij : i ≠ j) {M : GL (Fin 3) E}
    (hM : M ∈ suSupp D i j) : ∃ A ∈ SUid D.σ.toRingEquiv 2, blkHom hij A = M := by
  obtain ⟨⟨hdet, hiso⟩, -⟩ := id hM
  set A₀ : Matrix (Fin 2) (Fin 2) E :=
    Matrix.of fun a b => (M : Matrix (Fin 3) (Fin 3) E) (pairE i j a) (pairE i j b) with hA₀
  have hmA : blockMat (pairE i j) A₀ = (M : Matrix (Fin 3) (Fin 3) E) := by
    ext x y
    by_cases hx : ∃ a, pairE i j a = x
    · by_cases hy : ∃ b, pairE i j b = y
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [blockMat_apply_e (pairE_injective hij)]
        rfl
      · push Not at hy
        rw [blockMat_apply_of_notMem_right _ hy, suSupp_col D hM (Ne.symm (hy 0)) (Ne.symm (hy 1))]
    · push Not at hx
      rw [blockMat_apply_of_notMem_left _ hx, suSupp_row D hM (Ne.symm (hx 0)) (Ne.symm (hx 1))]
  have hdetA : A₀.det = 1 := by rw [← det_blockMat (pairE_injective hij), hmA, hdet]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A₀ (by rw [hdetA]; exact one_ne_zero),
    ⟨hdetA, ?_⟩, Units.ext hmA⟩
  apply blockMat_injective' (pairE_injective hij)
  show blockMat (pairE i j) (conjTr D.σ.toRingEquiv A₀ * A₀) = blockMat (pairE i j) 1
  rw [blockMat_mul (pairE_injective hij), ← conjTr_blockMat _ (pairE_injective hij), hmA, hiso,
    blockMat_one]

theorem map_SUid_eq_suSupp {i j : Fin 3} (hij : i ≠ j) :
    (SUid D.σ.toRingEquiv 2).map (blkHom hij) = suSupp D i j := by
  ext M
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact blkHom_mem_suSupp D hij hA
  · intro hM
    obtain ⟨A, hA, rfl⟩ := exists_blkHom_of_mem_suSupp D hij hM
    exact ⟨A, hA, rfl⟩

theorem longBlock_le_O (i j : Fin 3) :
    longBlock D i j ≤ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  rintro _ ⟨M, hM, rfl⟩
  exact matToG_mem_O D hM.1.2

end SuSupp

section Model

open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem exists_card_eq_two_pow : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem unitaryInvolution_eq (D : EvenNormPlane K E) {f : ℕ} (hf : Nat.card K = 2 ^ f) [Finite E]
    [CharP E 2] : unitaryInvolution E 2 f = D.σ.toRingEquiv := by
  ext c
  rw [unitaryInvolution_apply]
  show c ^ 2 ^ f = D.σ c
  rw [D.sigma_eq_pow, hf]

theorem nonempty_sl2_mulEquiv_SUid (D : EvenNormPlane K E) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    [Finite E] [CharP E 2] :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield E 2 f) ≃*
      SUid D.σ.toRingEquiv 2) := by
  have hE : Nat.card E = (2 ^ f) ^ 2 := by rw [D.card_E, hf]
  rw [← unitaryInvolution_eq D hf]
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hE
  obtain ⟨P, hP⟩ := exists_wittMatrix hE 2
  exact ⟨(hypEquiv hζ0 hζ).trans (conjEquiv P hP)⟩

@[expose] noncomputable def longHom (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) {F : Type}
    [Group F] (ψ : F ≃* SUid D.σ.toRingEquiv 2) : F →* (Vs K E ≃ₗ[K] Vs K E) :=
  (matToG K).comp ((blkHom hij).comp ((SUid D.σ.toRingEquiv 2).subtype.comp ψ.toMonoidHom))

theorem longHom_injective (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) {F : Type}
    [Group F] (ψ : F ≃* SUid D.σ.toRingEquiv 2) : Function.Injective (longHom D hij ψ) :=
  (matToG_injective (K := K) (E := E)).comp ((blkHom_injective hij).comp
    ((SUid D.σ.toRingEquiv 2).subtype_injective.comp ψ.injective))

theorem longBlock_eq_range (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) {F : Type}
    [Group F] (ψ : F ≃* SUid D.σ.toRingEquiv 2) : longBlock D i j = (longHom D hij ψ).range := by
  have h1 : ((SUid D.σ.toRingEquiv 2).subtype.comp ψ.toMonoidHom).range =
      SUid D.σ.toRingEquiv 2 := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [longHom, MonoidHom.range_comp, MonoidHom.range_comp, h1, map_SUid_eq_suSupp D hij]
  rfl

end Model

section Torus

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p)

theorem fin3_eq_of_ne {i j k x : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hxi : x ≠ i)
    (hxj : x ≠ j) : x = k := by
  rw [Ne, Fin.ext_iff] at hij hik hjk hxi hxj
  have := i.isLt
  have := j.isLt
  have := k.isLt
  have := x.isLt
  exact Fin.ext (by omega)

theorem matToG_commute_tor {i j : Fin 3} {M : GL (Fin 3) E} (hM : M ∈ suSupp S.D i j)
    {a : Fin 3 → ZMod p} (ha : a i = a j) : matToG K M * tor S a = tor S a * matToG K M := by
  have key : ∀ x y, (M : Matrix (Fin 3) (Fin 3) E) x y = 0 ∨ a x = a y := by
    intro x y
    by_cases hx : x = i ∨ x = j
    · by_cases hy : y = i ∨ y = j
      · right
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · exact ha
        · exact ha.symm
        · rfl
      · push Not at hy
        rw [suSupp_col S.D hM hy.1 hy.2]
        by_cases hxy : x = y
        · exact Or.inr (by rw [hxy])
        · exact Or.inl (Matrix.one_apply_ne hxy)
    · push Not at hx
      rw [suSupp_row S.D hM hx.1 hx.2]
      by_cases hxy : x = y
      · exact Or.inr (by rw [hxy])
      · exact Or.inl (Matrix.one_apply_ne hxy)
  refine LinearEquiv.ext fun v => Prod.ext (funext fun x => ?_) rfl
  simp only [LinearEquiv.mul_apply, matToG_apply, tor_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases key x y with h | h
  · simp [h]
  · rw [h]
    ring

@[expose] noncomputable def torMat (a : Fin 3 → ZMod p) : GL (Fin 3) E :=
  ⟨Matrix.diagonal fun l => S.rot (a l), Matrix.diagonal fun l => S.rot (-a l),
    by rw [Matrix.diagonal_mul_diagonal]; simp [S.rot_mul_neg],
    by rw [Matrix.diagonal_mul_diagonal]; simp [S.rot_neg]⟩

theorem matToG_torMat (a : Fin 3 → ZMod p) : matToG K (torMat S a) = tor S a :=
  LinearEquiv.ext fun v => Prod.ext (funext fun x => by
    simp [matToG_apply, tor_apply, torMat, Matrix.mulVec_diagonal]) rfl

theorem sum_fin3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a : Fin 3 → ZMod p) :
    ∑ l, a l = a i + a j + a k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_three] <;> ring

theorem prod_rot (a : Fin 3 → ZMod p) : ∏ l, S.rot (a l) = S.rot (∑ l, a l) := by
  rw [Fin.prod_univ_three, Fin.sum_univ_three, S.rot_add, S.rot_add]

theorem torMat_mem_suSupp_iff {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ZMod p) : torMat S a ∈ suSupp S.D i j ↔ a k = 0 ∧ a i + a j = 0 := by
  have hdet : ((torMat S a : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det =
      S.rot (a i + a j + a k) := by
    show (Matrix.diagonal fun l => S.rot (a l)).det = _
    rw [Matrix.det_diagonal, prod_rot, sum_fin3 hij hik hjk]
  have hcol : ∀ k', ((torMat S a : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ Pi.single k' 1 =
      S.rot (a k') • Pi.single k' 1 := by
    intro k'
    funext x
    change ((Matrix.diagonal fun l => S.rot (a l)) *ᵥ Pi.single k' 1) x = _
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x = k'
    · subst hx
      simp
    · simp [hx]
  constructor
  · rintro ⟨⟨hd, -⟩, hfix⟩
    have h1 := congrFun (hfix k (Ne.symm hik) (Ne.symm hjk)) k
    rw [hcol, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
    have hk : a k = 0 := S.rot_injective (h1.trans S.rot_zero.symm)
    rw [hdet, hk, add_zero] at hd
    exact ⟨hk, S.rot_injective (hd.trans S.rot_zero.symm)⟩
  · rintro ⟨hk, hij'⟩
    refine ⟨⟨?_, ?_⟩, fun k' hk'i hk'j => ?_⟩
    · rw [hdet, hk, add_zero, hij', S.rot_zero]
    · show conjTr S.D.σ.toRingEquiv (Matrix.diagonal fun l => S.rot (a l)) *
        Matrix.diagonal (fun l => S.rot (a l)) = 1
      rw [conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext l
      show S.D.σ (S.rot (a l)) * S.rot (a l) = 1
      rw [S.sigma_rot, S.rot_neg]
    · rw [fin3_eq_of_ne hij hik hjk hk'i hk'j, hcol, hk, S.rot_zero, one_smul]

theorem tor_mem_longBlock_iff {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : Fin 3 → ZMod p) : tor S a ∈ longBlock S.D i j ↔ a k = 0 ∧ a i + a j = 0 := by
  rw [← torMat_mem_suSupp_iff S hij hik hjk, ← matToG_torMat S a]
  constructor
  · rintro ⟨M, hM, hMt⟩
    rwa [← matToG_injective hMt]
  · intro h
    exact ⟨torMat S a, h, rfl⟩

end Torus

end CFSG.RankThree.PartOne.KFR4.Blk

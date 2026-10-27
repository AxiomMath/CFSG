module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailRot
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.OmegaPilot
open scoped commutatorElement

namespace OrthRestTail

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

section Prod

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_prod {p : ℕ} {A : Subgroup G} {B : Subgroup H} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) : IsElemAbelian p (A.prod B) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hx := Subgroup.mem_prod.mp x.2
    have hy := Subgroup.mem_prod.mp y.2
    exact Prod.ext (TableB.IsElemAbelian.comm hA hx.1 hy.1)
      (TableB.IsElemAbelian.comm hB hx.2 hy.2)
  · have hx' := Subgroup.mem_prod.mp hx
    exact Prod.ext (hA.2 _ hx'.1) (hB.2 _ hx'.2)

theorem card_prod_subgroup (A : Subgroup G) (B : Subgroup H) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

theorem isElemAbelian_bot' {p : ℕ} : IsElemAbelian p (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2])⟩⟩,
    fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩

theorem zpow_conj_of_conj_inv {M σ : G} (hσ : σ * M * σ⁻¹ = M⁻¹) {x : G}
    (hx : x ∈ Subgroup.zpowers M) : σ * x * σ⁻¹ = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow, hσ, _root_.inv_zpow]

theorem pow_eq_one_of_mem_zpowers' {M : G} {p : ℕ} (hMp : M ^ p = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers M) : x ^ p = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hMp,
    _root_.one_zpow]

theorem isElemAbelian_zpowers' {M : G} {p : ℕ} (hMp : M ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers M) := CFSG.Open.isElemAbelian_zpowers hMp

end Prod

section Blocks

variable [CharP K 2] {Q : QuadraticForm K (ι → K)}

@[expose] noncomputable def blkTorus (B : HypBlock Q)
    (H₁ H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) : Subgroup (GL ι K) :=
  (H₁.prod H₂).map B.blkGL

omit [CharP K 2] in
theorem blkTorus_le_suppSub (B : HypBlock Q)
    (H₁ H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :
    blkTorus B H₁ H₂ ≤ suppSub K (Set.range B.pos) := by
  rintro _ ⟨x, -, rfl⟩
  exact B.blkGL_mem_suppSub x

theorem card_blkTorus (B : HypBlock Q) (H₁ H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :
    Nat.card (blkTorus B H₁ H₂) = Nat.card H₁ * Nat.card H₂ := by
  rw [blkTorus, Subgroup.card_map_of_injective B.blkGL_injective, card_prod_subgroup]

omit [CharP K 2] in
theorem isElemAbelian_blkTorus {p : ℕ} (B : HypBlock Q)
    {H₁ H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (h₁ : IsElemAbelian p H₁)
    (h₂ : IsElemAbelian p H₂) : IsElemAbelian p (blkTorus B H₁ H₂) :=
  TableB.isElemAbelian_map (isElemAbelian_prod h₁ h₂) _

theorem blkTorus_le_omega {p : ℕ} (hp : Odd p) {M σ : Matrix.SpecialLinearGroup (Fin 2) K}
    (hMp : M ^ p = 1) (hσ : σ * M * σ⁻¹ = M⁻¹) (B : HypBlock Q)
    {H₁ H₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (h₁ : H₁ ≤ Subgroup.zpowers M)
    (h₂ : H₂ ≤ Subgroup.zpowers M) : blkTorus B H₁ H₂ ≤ LargeEvenOmega ⇑Q := by
  rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
  have hx := h₁ (Subgroup.mem_prod.mp hxy).1
  have hy := h₂ (Subgroup.mem_prod.mp hxy).2
  refine mem_omega_of_conj_inv (B.blkGL_mem_orth _) (B.blkGL_mem_orth (σ, σ)) ?_ hp ?_
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Prod.ext (zpow_conj_of_conj_inv hσ hx) (zpow_conj_of_conj_inv hσ hy)
  · rw [← map_pow, show (x, y) ^ p = 1 from
      Prod.ext (pow_eq_one_of_mem_zpowers' hMp hx) (pow_eq_one_of_mem_zpowers' hMp hy), map_one]

variable {m : ℕ} (F : HypFrame Q m)

omit [Fintype ι] [CharP K 2] in
@[expose] def HypFrame.pairSet (lo hi : ℕ) : Set ι :=
  {x | ∃ i : Fin m, lo ≤ i.val ∧ i.val < hi ∧ (x = F.X i ∨ x = F.Y i)}

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.pairSet_mono {lo hi lo' hi' : ℕ} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    F.pairSet lo hi ⊆ F.pairSet lo' hi' := by
  rintro x ⟨i, hi1, hi2, hx⟩
  exact ⟨i, by omega, by omega, hx⟩

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.pairSet_disjoint {lo hi lo' hi' : ℕ} (h : hi ≤ lo') :
    Disjoint (F.pairSet lo hi) (F.pairSet lo' hi') := by
  rw [Set.disjoint_left]
  rintro x ⟨i, -, hi2, hx⟩ ⟨j, hj1, -, hy⟩
  have hij : i ≠ j := fun e => by rw [e] at hi2; omega
  rcases hx with rfl | rfl <;> rcases hy with h' | h'
  · exact hij (F.X.injective h')
  · exact F.X_ne_Y i j h'
  · exact F.Y_ne_X i j h'
  · exact hij (F.Y.injective h')

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.X_not_mem_pairSet {lo hi : ℕ} {k : Fin m} (hk : k.val < lo ∨ hi ≤ k.val) :
    F.X k ∉ F.pairSet lo hi := by
  rintro ⟨i, hi1, hi2, h | h⟩
  · have := F.X.injective h
    subst this
    omega
  · exact F.X_ne_Y k i h

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.Y_not_mem_pairSet {lo hi : ℕ} {k : Fin m} (hk : k.val < lo ∨ hi ≤ k.val) :
    F.Y k ∉ F.pairSet lo hi := by
  rintro ⟨i, hi1, hi2, h | h⟩
  · exact F.Y_ne_X k i h
  · have := F.Y.injective h
    subst this
    omega

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.range_block_subset {i j : Fin m} (hij : i ≠ j) {lo hi : ℕ} (hi1 : lo ≤ i.val)
    (hi2 : i.val < hi) (hj1 : lo ≤ j.val) (hj2 : j.val < hi) :
    Set.range (F.block hij).pos ⊆ F.pairSet lo hi := by
  rw [F.range_block hij]
  rintro x (rfl | rfl | rfl | rfl)
  · exact ⟨i, hi1, hi2, Or.inl rfl⟩
  · exact ⟨j, hj1, hj2, Or.inl rfl⟩
  · exact ⟨i, hi1, hi2, Or.inr rfl⟩
  · exact ⟨j, hj1, hj2, Or.inr rfl⟩

@[expose] noncomputable def fullTorus (M : Matrix.SpecialLinearGroup (Fin 2) K) (o : ℕ) :
    (k : ℕ) → o + 2 * k ≤ m → Subgroup (GL ι K)
  | 0, _ => ⊥
  | k + 1, h => fullTorus M o k (by omega) ⊔
      blkTorus (F.block (i := ⟨o + 2 * k, by omega⟩) (j := ⟨o + 2 * k + 1, by omega⟩)
        (by simp [Fin.ext_iff])) (Subgroup.zpowers M) (Subgroup.zpowers M)

omit [CharP K 2] in
theorem fullTorus_le_suppSub (M : Matrix.SpecialLinearGroup (Fin 2) K) (o : ℕ) :
    ∀ (k : ℕ) (h : o + 2 * k ≤ m), fullTorus F M o k h ≤ suppSub K (F.pairSet o (o + 2 * k))
  | 0, _ => bot_le
  | k + 1, h => sup_le ((fullTorus_le_suppSub M o k (by omega)).trans
      (suppSub_mono (F.pairSet_mono le_rfl (by omega))))
    ((blkTorus_le_suppSub _ _ _).trans (suppSub_mono
      (F.range_block_subset _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
        (by dsimp only; omega))))

omit [Fintype ι] [CharP K 2] in
theorem fullTorus_succ_disjoint (o k : ℕ) {i j : Fin m} (hij : i ≠ j) (hi : i.val = o + 2 * k)
    (hj : j.val = o + 2 * k + 1) :
    Disjoint (F.pairSet o (o + 2 * k)) (Set.range (F.block hij).pos) :=
  Set.disjoint_of_subset_right (F.range_block_subset hij (by omega) (by omega) (by omega)
    (by omega)) (F.pairSet_disjoint (lo' := o + 2 * k) (hi' := o + 2 * k + 2) le_rfl)

theorem card_fullTorus {p : ℕ} {M : Matrix.SpecialLinearGroup (Fin 2) K} (hM : orderOf M = p)
    (o : ℕ) : ∀ (k : ℕ) (h : o + 2 * k ≤ m), Nat.card (fullTorus F M o k h) = p ^ (2 * k)
  | 0, _ => by rw [fullTorus, Subgroup.card_bot, mul_zero, pow_zero]
  | k + 1, _ => by
    rw [fullTorus, card_sup_of_suppSub (fullTorus_succ_disjoint F o k _ rfl rfl)
      (fullTorus_le_suppSub F M o k _) (blkTorus_le_suppSub _ _ _), card_fullTorus hM o k _,
      card_blkTorus, Nat.card_zpowers, hM]
    ring

omit [CharP K 2] in
theorem isElemAbelian_fullTorus {p : ℕ} {M : Matrix.SpecialLinearGroup (Fin 2) K}
    (hMp : M ^ p = 1) (o : ℕ) :
    ∀ (k : ℕ) (h : o + 2 * k ≤ m), IsElemAbelian p (fullTorus F M o k h)
  | 0, _ => isElemAbelian_bot'
  | k + 1, _ => TableB.isElemAbelian_sup (isElemAbelian_fullTorus hMp o k _)
      (isElemAbelian_blkTorus _ (isElemAbelian_zpowers' hMp) (isElemAbelian_zpowers' hMp))
      fun _ ha _ hc => commute_of_mem_suppSub (fullTorus_succ_disjoint F o k _ rfl rfl)
        (fullTorus_le_suppSub F M o k _ ha) (blkTorus_le_suppSub _ _ _ hc)

theorem fullTorus_le_omega {p : ℕ} (hp : Odd p) {M σ : Matrix.SpecialLinearGroup (Fin 2) K}
    (hMp : M ^ p = 1) (hσ : σ * M * σ⁻¹ = M⁻¹) (o : ℕ) :
    ∀ (k : ℕ) (h : o + 2 * k ≤ m), fullTorus F M o k h ≤ LargeEvenOmega ⇑Q
  | 0, _ => bot_le
  | k + 1, _ => sup_le (fullTorus_le_omega hp hMp hσ o k _)
      (blkTorus_le_omega hp hMp hσ _ le_rfl le_rfl)

end Blocks

section Elements

variable {Q : QuadraticForm K (ι → K)} (B : HypBlock Q)

theorem HypBlock.blkGL_mulVec_pos
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : ι → K) (r s : Fin 2) :
    (((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v) (B.pos (r, s)) =
      ((AB.1 : Matrix (Fin 2) (Fin 2) K) * toMat2 (v ∘ B.pos) *
        (AB.2 : Matrix (Fin 2) (Fin 2) K)ᵀ) r s :=
  congrFun (congrFun (B.toMat2_blkGL AB v) r) s

theorem HypBlock.blkGL_mulVec_of_not_mem
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : ι → K) {k : ι} (hk : k ∉ Set.range B.pos) :
    (((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v) k = v k := by
  rw [blkGL_mulVec, posLin_apply_of_not_mem _ _ _ hk]

@[expose] def unipSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_unipSL : ((unipSL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 1; 0, 1] :=
  rfl

variable [CharP K 2]

@[expose] def nSL : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

theorem coe_nSL : ((nSL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![0, 1; 1, 1] :=
  rfl

omit [CharP K 2] in
theorem HypBlock.blkGL_unip_mulVec (v : ι → K) :
    ((B.blkGL (unipSL, 1) : GL ι K) : Matrix ι ι K) *ᵥ v =
      eichLin Q (B.pos (0, 0)) (B.pos (1, 1)) (Pi.single (B.pos (0, 1)) 1) v := by
  have hp : QuadraticMap.polar Q v (Pi.single (B.pos (0, 1)) 1) = v (B.pos (1, 0)) := by
    rw [QuadraticMap.polar_comm, B.hyp₁.polar_left]
  funext k
  rw [eichLin_apply, hp, B.hyp₁.map_left, zero_mul, add_zero]
  by_cases hk : k ∈ Set.range B.pos
  · obtain ⟨⟨r, s⟩, rfl⟩ := hk
    rw [B.blkGL_mulVec_pos, coe_unipSL, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
      Matrix.mul_one]
    fin_cases r <;> fin_cases s <;>
      simp [toMat2, Matrix.mul_apply, Fin.sum_univ_two, B.pos.injective.eq_iff,
        Function.comp_apply, Matrix.of_apply]
  · have hne : ∀ rs, k ≠ B.pos rs := fun rs h => hk ⟨rs, h.symm⟩
    rw [B.blkGL_mulVec_of_not_mem _ _ hk]
    simp [hne]

theorem HypBlock.blkGL_nSL_single_01 :
    ((B.blkGL (1, nSL) : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (B.pos (0, 1)) 1 =
      Pi.single (B.pos (0, 0)) 1 + Pi.single (B.pos (0, 1)) 1 := by
  funext k
  by_cases hk : k ∈ Set.range B.pos
  · obtain ⟨⟨r, s⟩, rfl⟩ := hk
    rw [B.blkGL_mulVec_pos, coe_nSL, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    fin_cases r <;> fin_cases s <;>
      simp [toMat2, Matrix.mul_apply, Fin.sum_univ_two, B.pos.injective.eq_iff,
        Function.comp_apply, Matrix.of_apply]
  · have hne : ∀ rs, k ≠ B.pos rs := fun rs h => hk ⟨rs, h.symm⟩
    rw [B.blkGL_mulVec_of_not_mem _ _ hk]
    simp [hne]

theorem HypBlock.blkGL_nSL_single_00 :
    ((B.blkGL (1, nSL) : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (B.pos (0, 0)) 1 =
      Pi.single (B.pos (0, 1)) 1 := by
  funext k
  by_cases hk : k ∈ Set.range B.pos
  · obtain ⟨⟨r, s⟩, rfl⟩ := hk
    rw [B.blkGL_mulVec_pos, coe_nSL, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
    fin_cases r <;> fin_cases s <;>
      simp [toMat2, Matrix.mul_apply, Fin.sum_univ_two, B.pos.injective.eq_iff,
        Function.comp_apply, Matrix.of_apply]
  · have hne : ∀ rs, k ≠ B.pos rs := fun rs h => hk ⟨rs, h.symm⟩
    rw [B.blkGL_mulVec_of_not_mem _ _ hk]
    simp [hne]

theorem unipSL_sq : (unipSL : Matrix.SpecialLinearGroup (Fin 2) K) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_unipSL, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two,
    CharTwo.add_self_eq_zero]

omit [CharP K 2] in
theorem unipSL_ne_one : (unipSL : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [coe_unipSL] at this

end Elements

section FrameElements

variable [CharP K 2] {Q : QuadraticForm K (ι → K)} {m : ℕ} (F : HypFrame Q m)

@[expose] def HypFrame.block01 (hm : 2 ≤ m) : HypBlock Q :=
  F.block (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff])

omit [Fintype ι] [CharP K 2] in
theorem HypFrame.range_block01_subset (hm : 2 ≤ m) :
    Set.range (F.block01 hm).pos ⊆ F.pairSet 0 2 :=
  F.range_block_subset _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega)

theorem HypFrame.siegel_mem_omega (hm : 3 ≤ m) :
    (F.block01 (by omega)).blkGL (unipSL, 1) ∈ LargeEvenOmega ⇑Q := by
  set B := F.block01 (by omega)
  set B' := F.block (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩) (by simp [Fin.ext_iff])
  have hst := F.hyp ⟨0, by omega⟩
  have hsub : Set.range B'.pos ⊆ F.pairSet 1 3 :=
    F.range_block_subset _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega)
  have hs : F.X ⟨0, by omega⟩ ∉ Set.range B'.pos := fun h =>
    F.X_not_mem_pairSet (lo := 1) (hi := 3) (k := ⟨0, by omega⟩) (Or.inl (by dsimp only; omega))
      (hsub h)
  have ht : F.Y ⟨0, by omega⟩ ∉ Set.range B'.pos := fun h =>
    F.Y_not_mem_pairSet (lo := 1) (hi := 3) (k := ⟨0, by omega⟩) (Or.inl (by dsimp only; omega))
      (hsub h)
  have hw : (Pi.single (F.X ⟨2, by omega⟩) (1 : K) : ι → K) (F.Y ⟨0, by omega⟩) = 0 :=
    Pi.single_eq_of_ne (F.Y_ne_X _ _) 1
  have hc := eichGL_commutator hst hs ht (B'.blkGL_mem_suppSub (1, nSL)) (B'.map_blkGL (1, nSL)) hw
  have hmem : ⁅B'.blkGL (1, nSL), eichGL hst _ hw⁆ ∈ LargeEvenOmega ⇑Q :=
    Subgroup.commutator_mem_commutator (B'.blkGL_mem_orth _) (eichGL_mem_orth hst hw)
  rw [hc] at hmem
  convert hmem using 1
  refine gl_ext fun v => ?_
  rw [B.blkGL_unip_mulVec, eichGL_mulVec]
  have h1 := B'.blkGL_nSL_single_01
  change ((B'.blkGL (1, nSL) : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (F.X ⟨2, by omega⟩) 1 =
    Pi.single (F.X ⟨1, by omega⟩) 1 + Pi.single (F.X ⟨2, by omega⟩) 1 at h1
  change eichLin Q (F.X ⟨0, by omega⟩) (F.Y ⟨0, by omega⟩) (Pi.single (F.X ⟨1, by omega⟩) 1) v = _
  rw [h1, add_assoc, show (Pi.single (F.X ⟨2, by omega⟩) (1 : K) : ι → K) +
    Pi.single (F.X ⟨2, by omega⟩) 1 = 0 from funext fun k => CharTwo.add_self_eq_zero _, add_zero]

theorem HypFrame.exists_eich_ne_one (hm : 3 ≤ m) :
    ∃ g ∈ eichSub (F.hyp ⟨m - 1, by omega⟩) (F.pairSet 0 (m - 1)) ⊓ LargeEvenOmega ⇑Q,
      g ≠ 1 := by
  set B := F.block01 (by omega)
  have hst := F.hyp ⟨m - 1, by omega⟩
  have hsub := F.range_block01_subset (by omega)
  have hs : F.X ⟨m - 1, by omega⟩ ∉ Set.range B.pos := fun h =>
    F.X_not_mem_pairSet (lo := 0) (hi := 2) (k := ⟨m - 1, by omega⟩) (Or.inr (by dsimp only; omega))
      (hsub h)
  have ht : F.Y ⟨m - 1, by omega⟩ ∉ Set.range B.pos := fun h =>
    F.Y_not_mem_pairSet (lo := 0) (hi := 2) (k := ⟨m - 1, by omega⟩) (Or.inr (by dsimp only; omega))
      (hsub h)
  have hw : (Pi.single (F.X ⟨0, by omega⟩) (1 : K) : ι → K) (F.Y ⟨m - 1, by omega⟩) = 0 :=
    Pi.single_eq_of_ne (F.Y_ne_X _ _) 1
  have hc := eichGL_commutator hst hs ht (B.blkGL_mem_suppSub (1, nSL)) (B.map_blkGL (1, nSL)) hw
  have h0 := B.blkGL_nSL_single_00
  change ((B.blkGL (1, nSL) : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (F.X ⟨0, by omega⟩) 1 =
    Pi.single (F.X ⟨1, by omega⟩) 1 at h0
  refine ⟨⁅B.blkGL (1, nSL), eichGL hst _ hw⁆, ⟨?_, ?_⟩, ?_⟩
  · rw [hc]
    refine eichGL_mem_eichSub hst _ fun k hk => ?_
    have hk0 : k ≠ F.X ⟨0, by omega⟩ := by
      rintro rfl
      exact hk ⟨⟨0, by omega⟩, le_rfl, by dsimp only; omega, Or.inl rfl⟩
    have hk1 : k ≠ F.X ⟨1, by omega⟩ := by
      rintro rfl
      exact hk ⟨⟨1, by omega⟩, by dsimp only; omega, by dsimp only; omega, Or.inl rfl⟩
    rw [h0, Pi.add_apply, Pi.single_eq_of_ne hk1, Pi.single_eq_of_ne hk0, add_zero]
  · exact Subgroup.commutator_mem_commutator (B.blkGL_mem_orth _) (eichGL_mem_orth hst hw)
  · rw [hc]
    intro h1
    have h2 := congrFun (congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ
      Pi.single (F.Y ⟨m - 1, by omega⟩) 1) h1) (F.X ⟨0, by omega⟩)
    simp only [eichGL_mulVec, Units.val_one, one_mulVec, eichLin_apply, h0] at h2
    have hne1 : F.X ⟨0, by omega⟩ ≠ F.X ⟨1, by omega⟩ := fun e => by
      have := F.X.injective e
      simp [Fin.ext_iff] at this
    have hne2 : F.X ⟨0, by omega⟩ ≠ F.X ⟨m - 1, by omega⟩ := fun e => by
      have := F.X.injective e
      simp [Fin.ext_iff] at this
      omega
    simp [hne1, hne2, F.X_ne_Y] at h2

theorem le_normalizer_eichSub {s t : ι} (hst : IsHypCoord Q s t) {S T : Set ι} (hs : s ∉ T)
    (ht : t ∉ T) {H : Subgroup (GL ι K)} (hHT : H ≤ suppSub K T) (hHQ : H ≤ LargeEvenOrthGroup ⇑Q)
    (hHS : ∀ h ∈ H, ∀ w : ι → K, (∀ k ∉ S, w k = 0) → ∀ k ∉ S,
      ((h : Matrix ι ι K) *ᵥ w) k = 0) :
    H ≤ Subgroup.normalizer (eichSub hst S : Set (GL ι K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_eichSub hst hs ht (hHT hh)
    (TableBOrth.isometry_of_mem_orthGroup (hHQ hh)) (hHS h hh) hg, fun hg => ?_⟩
  have hh' := Subgroup.inv_mem H hh
  have := conj_mem_eichSub hst hs ht (hHT hh') (TableBOrth.isometry_of_mem_orthGroup (hHQ hh'))
    (hHS _ hh') hg
  convert this using 1
  group

theorem le_normalizer_inf {G : Type*} [Group G] {A B H : Subgroup G}
    (hA : H ≤ Subgroup.normalizer (A : Set G)) (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hA hh) g),
    (Subgroup.mem_normalizer_iff.mp (hB hh) g)]

theorem le_normalizer_self {G : Type*} [Group G] (A : Subgroup G) :
    A ≤ Subgroup.normalizer (A : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => A.mul_mem (A.mul_mem hh hg) (A.inv_mem hh), fun hg => ?_⟩
  have := A.mul_mem (A.mul_mem (A.inv_mem hh) hg) hh
  convert this using 1
  group

end FrameElements

end OrthRestTail

end CFSG.StandardType

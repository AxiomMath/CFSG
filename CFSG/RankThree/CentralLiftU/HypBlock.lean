module

public import CFSG.RankThree.CentralLiftU.BlockMat
public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def restrGram (K : Type) [Field K] (e : κ → HypIndex r ε) : Matrix κ κ K :=
  (embMat e : Matrix (HypIndex r ε) κ K)ᵀ * hypGram r ε K * (embMat e : Matrix (HypIndex r ε) κ K)

@[expose] def PartnerClosed (e : κ → HypIndex r ε) : Prop :=
  ∀ a, ∃ b, hypPartner (e a) = e b

omit [Fintype κ] [DecidableEq κ] in
theorem restrGram_apply (e : κ → HypIndex r ε) (a b : κ) :
    restrGram K e a b = if e b = hypPartner (e a) then 1 else 0 := by
  have h1 : ∀ x : HypIndex r ε, ((embMat e : Matrix (HypIndex r ε) κ K)ᵀ * hypGram r ε K) a x =
      hypGram r ε K (e a) x := by
    intro x
    rw [mul_apply, Finset.sum_eq_single (e a)]
    · simp [transpose_apply, embMat_apply]
    · intro y _ hy
      simp [transpose_apply, embMat_apply, Ne.symm hy]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [restrGram, mul_apply, Finset.sum_eq_single (e b)]
  · rw [h1, hypGram_apply, embMat_apply, ite_eq_left rfl, mul_one]
  · intro y _ hy
    rw [embMat_apply, ite_eq_right (fun h => hy h.symm), mul_zero]
  · intro h0; exact absurd (Finset.mem_univ _) h0

omit [DecidableEq κ] in
theorem hypGram_mul_embMat {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) :
    hypGram r ε K * (embMat e : Matrix (HypIndex r ε) κ K) =
      (embMat e : Matrix (HypIndex r ε) κ K) * restrGram K e := by
  ext x a
  have hL : (hypGram r ε K * (embMat e : Matrix (HypIndex r ε) κ K)) x a =
      hypGram r ε K x (e a) := by
    rw [mul_apply, Finset.sum_eq_single (e a)]
    · rw [embMat_apply, ite_eq_left rfl, mul_one]
    · intro y _ hy
      rw [embMat_apply, ite_eq_right (fun h => hy h.symm), mul_zero]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [hL, hypGram_apply, mul_apply]
  by_cases hx : ∃ b, e b = x
  · obtain ⟨b, rfl⟩ := hx
    rw [Finset.sum_eq_single b]
    · rw [embMat_apply, ite_eq_left rfl, one_mul, restrGram_apply]
    · intro c _ hcb
      rw [embMat_apply, ite_eq_right (fun h => hcb (he h)), zero_mul]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · push Not at hx
    rw [Finset.sum_eq_zero (fun c _ => by rw [embMat_apply, ite_eq_right (hx c), zero_mul])]
    rw [ite_eq_right]
    intro hxa
    obtain ⟨b, hb⟩ := hc a
    exact hx b (by rw [← hb, hxa, hypPartner_hypPartner])

omit [DecidableEq κ] in
theorem transpose_embMat_mul_hypGram {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) :
    (embMat e : Matrix (HypIndex r ε) κ K)ᵀ * hypGram r ε K =
      restrGram K e * (embMat e : Matrix (HypIndex r ε) κ K)ᵀ := by
  have h := congrArg Matrix.transpose (hypGram_mul_embMat (K := K) he hc)
  rw [transpose_mul, transpose_mul, hypGram_transpose] at h
  have hG : (restrGram K e)ᵀ = restrGram K e := by
    rw [restrGram, transpose_mul, transpose_mul, hypGram_transpose, transpose_transpose,
      Matrix.mul_assoc]
  rw [hG] at h
  exact h

variable (h : UnitaryFieldData p f K)

omit [Fintype κ] [DecidableEq κ] in
theorem map_bar_embMat (e : κ → HypIndex r ε) :
    (embMat e : Matrix (HypIndex r ε) κ K).map h.bar = embMat e := by
  ext x a
  simp only [map_apply, embMat_apply]
  split_ifs <;> simp

theorem conjTranspose_blockMat (e : κ → HypIndex r ε) (M : Matrix κ κ K) :
    ((blockMat e M).map h.bar)ᵀ = blockMat e ((M.map h.bar)ᵀ) := by
  have hm : (blockMat e M).map h.bar = blockMat e (M.map h.bar) := by
    rw [blockMat, blockMat, Matrix.map_add _ (map_add h.bar), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_sub _ (map_sub h.bar), Matrix.map_one _ (map_zero h.bar) (map_one h.bar),
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), map_bar_embMat, transpose_map,
      map_bar_embMat]
  rw [hm, blockMat, blockMat, transpose_add, transpose_one, transpose_mul, transpose_mul,
    transpose_transpose, transpose_sub, transpose_one, Matrix.mul_assoc]

theorem blockMat_isometry {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) {M : Matrix κ κ K}
    (hM : (M.map h.bar)ᵀ * restrGram K e * M = restrGram K e) :
    ((blockMat e M).map h.bar)ᵀ * hypGram r ε K * blockMat e M = hypGram r ε K := by
  rw [conjTranspose_blockMat]
  set P : Matrix (HypIndex r ε) κ K := embMat e
  set G' : Matrix κ κ K := restrGram K e
  set Mh := (M.map h.bar)ᵀ
  have hJP : hypGram r ε K * P = P * G' := hypGram_mul_embMat he hc
  have hPJ : Pᵀ * hypGram r ε K = G' * Pᵀ := transpose_embMat_mul_hypGram he hc
  have hPJP : Pᵀ * hypGram r ε K * P = G' := rfl
  simp only [blockMat]
  have e1 : (1 + P * (Mh - 1) * Pᵀ) * hypGram r ε K * (1 + P * (M - 1) * Pᵀ) =
      hypGram r ε K + P * ((Mh - 1) * G' + G' * (M - 1) + (Mh - 1) * G' * (M - 1)) * Pᵀ := by
    have k1 : P * (Mh - 1) * Pᵀ * hypGram r ε K = P * ((Mh - 1) * G') * Pᵀ := by
      rw [Matrix.mul_assoc, hPJ]; simp only [Matrix.mul_assoc]
    have k2 : hypGram r ε K * (P * (M - 1) * Pᵀ) = P * (G' * (M - 1)) * Pᵀ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJP]; simp only [Matrix.mul_assoc]
    have k3 : P * (Mh - 1) * Pᵀ * hypGram r ε K * (P * (M - 1) * Pᵀ) =
        P * ((Mh - 1) * G' * (M - 1)) * Pᵀ := by
      calc P * (Mh - 1) * Pᵀ * hypGram r ε K * (P * (M - 1) * Pᵀ)
          = P * (Mh - 1) * (Pᵀ * hypGram r ε K * P) * (M - 1) * Pᵀ := by
            simp only [Matrix.mul_assoc]
        _ = P * ((Mh - 1) * G' * (M - 1)) * Pᵀ := by rw [hPJP]; simp only [Matrix.mul_assoc]
    have e0 : (1 + P * (Mh - 1) * Pᵀ) * hypGram r ε K * (1 + P * (M - 1) * Pᵀ) =
        hypGram r ε K + hypGram r ε K * (P * (M - 1) * Pᵀ) + P * (Mh - 1) * Pᵀ * hypGram r ε K +
          P * (Mh - 1) * Pᵀ * hypGram r ε K * (P * (M - 1) * Pᵀ) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [e0, k3, k1, k2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
    abel
  rw [e1]
  have e2 : (Mh - 1) * G' + G' * (M - 1) + (Mh - 1) * G' * (M - 1) = Mh * G' * M - G' := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e2, hM, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem blockMat_mem_hypSU {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) {G' : Matrix κ κ K} (hG' : restrGram K e = G') (g : gramSU h G') :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (blockMat e ((g : GL κ K) : Matrix κ κ K))
      (by rw [det_blockMat he, g.2.2]; exact one_ne_zero) ∈ hypSU h r ε := by
  rw [mem_hypSU, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  refine ⟨blockMat_isometry h he hc ?_, by rw [det_blockMat he, g.2.2]⟩
  rw [hG']
  exact g.2.1

@[expose] noncomputable def blockHom {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) {G' : Matrix κ κ K} (hG' : restrGram K e = G') :
    gramSU h G' →* hypSU h r ε where
  toFun g := ⟨_, blockMat_mem_hypSU h he hc hG' g⟩
  map_one' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Subgroup.coe_one, Units.val_one,
      Subgroup.coe_one, Units.val_one, blockMat_one]))
  map_mul' g g' := Subtype.ext (Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Subgroup.coe_mul, Units.val_mul,
      Subgroup.coe_mul, Units.val_mul, blockMat_mul he]
    rfl))

theorem coe_blockHom {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) {G' : Matrix κ κ K} (hG' : restrGram K e = G') (g : gramSU h G') :
    ((blockHom h he hc hG' g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blockMat e ((g : GL κ K) : Matrix κ κ K) :=
  rfl

theorem blockHom_injective {e : κ → HypIndex r ε} (he : Function.Injective e)
    (hc : PartnerClosed e) {G' : Matrix κ κ K} (hG' : restrGram K e = G') :
    Function.Injective (blockHom h he hc hG') := by
  intro g g' hgg'
  apply Subtype.ext
  apply Units.ext
  ext a b
  have := congrArg (fun x : hypSU h r ε =>
    ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (e a) (e b)) hgg'
  change blockMat e ((g : GL κ K) : Matrix κ κ K) (e a) (e b) =
    blockMat e ((g' : GL κ K) : Matrix κ κ K) (e a) (e b) at this
  rwa [blockMat_apply_e he, blockMat_apply_e he] at this

end CFSG.RankThree.CentralLiftU

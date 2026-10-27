module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfSp4
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotAutUCenter
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent proj projUnipotent)
open CFSG.SeitzReduction.SymplecticPilot (twoCentralElt twoCentralMat twoCentralMat_apply
  twoCentralMat_transpose mat_twoCentralElt twoCentralElt_zero centralizer_unipotent_le
  spHighRootCenter_le_unipotent)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open Matrix

section Block

variable {F : Type} [Field F]

local notation "M₂" => Matrix (Fin 2) (Fin 2) F
local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

structure SpPair (E Q Q' : M₂) : Prop where
  ee : E * E = E
  eq : E * Q = Q
  qe : Q * E = Q
  eq' : E * Q' = Q'
  q'e : Q' * E = Q'
  qq' : Q * Q' = E
  q'q : Q' * Q = E
  et : Eᵀ = E
  qt : Qᵀ = Q
  q't : Q'ᵀ = Q'

@[expose] def spBlockMat (E Q Q' A : M₂) : M₄ :=
  fromBlocks (A 0 0 • E + (1 - E)) (A 0 1 • Q) (A 1 0 • Q') (A 1 1 • E + (1 - E))

variable {E Q Q' : Matrix (Fin 2) (Fin 2) F}

theorem SpPair.e_one_sub (h : SpPair E Q Q') : E * (1 - E) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.ee, sub_self]

theorem SpPair.one_sub_e (h : SpPair E Q Q') : (1 - E) * E = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.ee, sub_self]

theorem SpPair.one_sub_sq (h : SpPair E Q Q') : (1 - E) * (1 - E) = 1 - E := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.e_one_sub, sub_zero]

theorem SpPair.one_sub_q (h : SpPair E Q Q') : (1 - E) * Q = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.eq, sub_self]

theorem SpPair.q_one_sub (h : SpPair E Q Q') : Q * (1 - E) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.qe, sub_self]

theorem SpPair.one_sub_q' (h : SpPair E Q Q') : (1 - E) * Q' = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.eq', sub_self]

theorem SpPair.q'_one_sub (h : SpPair E Q Q') : Q' * (1 - E) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, h.q'e, sub_self]

theorem spBlockMat_one : spBlockMat E Q Q' 1 = 1 := by
  simp [spBlockMat]

theorem spBlockMat_mul (h : SpPair E Q Q') (A B : M₂) :
    spBlockMat E Q Q' (A * B) = spBlockMat E Q Q' A * spBlockMat E Q Q' B := by
  rw [spBlockMat, spBlockMat, spBlockMat, fromBlocks_multiply]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.ee,
    h.e_one_sub, h.one_sub_e, h.one_sub_sq, h.one_sub_q, h.q_one_sub, h.one_sub_q',
    h.q'_one_sub, h.eq, h.qe, h.eq', h.q'e, h.qq', h.q'q, smul_zero, add_zero, zero_add,
    Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> module

theorem spBlockMat_sp (h : SpPair E Q Q') {A : M₂} (hA : A.det = 1) :
    (spBlockMat E Q Q' A)ᵀ * (fromBlocks 0 1 (-1) 0 : M₄) * spBlockMat E Q Q' A =
      fromBlocks 0 1 (-1) 0 := by
  have hd : A 0 0 * A 1 1 = 1 + A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two] at hA
    linear_combination hA
  rw [spBlockMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, h.et, h.qt, h.q't, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, h.ee, h.e_one_sub, h.one_sub_e,
    h.one_sub_sq, h.one_sub_q, h.q_one_sub, h.one_sub_q', h.q'_one_sub, h.eq, h.qe, h.eq',
    h.q'e, h.qq', h.q'q, smul_zero, neg_zero, add_zero, zero_add]
  congr 1
  · module
  · linear_combination (norm := module) hd • E
  · linear_combination (norm := module) -(hd • E)
  · module

@[expose] noncomputable def spBlock (h : SpPair E Q Q') :
    Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 2 F where
  toFun A := ⟨⟨spBlockMat E Q Q' (A : M₂),
      spBlockMat E Q Q' ((A⁻¹ : Matrix.SpecialLinearGroup _ F) : M₂),
      by rw [← spBlockMat_mul h, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, spBlockMat_one],
      by rw [← spBlockMat_mul h, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, spBlockMat_one]⟩,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
      (spBlockMat_sp h A.2)⟩
  map_one' := Subtype.ext (Units.ext spBlockMat_one)
  map_mul' A B := Subtype.ext (Units.ext (spBlockMat_mul h (A : M₂) (B : M₂)))

theorem mat_spBlock (h : SpPair E Q Q') (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    mat 2 F (spBlock h A) = spBlockMat E Q Q' (A : M₂) :=
  rfl

theorem spBlock_injective (h : SpPair E Q Q') (hE : E 0 0 = 1) {i j k l : Fin 2}
    (hQ : Q i j ≠ 0) (hQ' : Q' k l ≠ 0) : Function.Injective (spBlock h) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hm : spBlockMat E Q Q' (A : M₂) = 1 := by
    rw [← mat_spBlock h, hA, map_one]
  have e1 := congrFun (congrFun hm (.inl 0)) (.inl 0)
  have e2 := congrFun (congrFun hm (.inr 0)) (.inr 0)
  have e3 := congrFun (congrFun hm (.inl i)) (.inr j)
  have e4 := congrFun (congrFun hm (.inr k)) (.inl l)
  simp [spBlockMat, hE] at e1 e2 e3 e4
  have h01 : (A : M₂) 0 1 = 0 := by
    rcases e3 with h3 | h3
    · exact h3
    · exact absurd h3 hQ
  have h10 : (A : M₂) 1 0 = 0 := by
    rcases e4 with h4 | h4
    · exact h4
    · exact absurd h4 hQ'
  refine Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_
  fin_cases x <;> fin_cases y <;> simp [e1, e2, h01, h10]

theorem mat_spBlock_xT (h : SpPair E Q Q') :
    mat 2 F (spBlock h (xT 1)) = fromBlocks 1 Q 0 1 := by
  rw [mat_spBlock, spBlockMat, coe_xT]
  simp

end Block

section Pairs

variable {F : Type} [Field F]

@[expose] def qInv (a b : F) : Matrix (Fin 2) (Fin 2) F :=
  !![0, b⁻¹; b⁻¹, -(a * b⁻¹ * b⁻¹)]

theorem spPair_inv (a : F) {b : F} (hb : b ≠ 0) :
    SpPair 1 (twoCentralMat 0 1 a b) (qInv a b) where
  ee := Matrix.mul_one 1
  eq := Matrix.one_mul _
  qe := Matrix.mul_one _
  eq' := Matrix.one_mul _
  q'e := Matrix.mul_one _
  qq' := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [twoCentralMat_apply, qInv, Matrix.mul_apply, Fin.sum_univ_two, hb]
    field_simp
    ring
  q'q := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [twoCentralMat_apply, qInv, Matrix.mul_apply, Fin.sum_univ_two, hb]
    field_simp
    ring
  et := Matrix.transpose_one
  qt := twoCentralMat_transpose 0 1 a b
  q't := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [qInv]

theorem spPair_long {a : F} (ha : a ≠ 0) :
    SpPair (twoCentralMat 0 1 1 0) (twoCentralMat 0 1 a 0) (twoCentralMat 0 1 a⁻¹ 0) where
  ee := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [twoCentralMat_apply, Matrix.mul_apply]
  eq := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [twoCentralMat_apply, Matrix.mul_apply]
  qe := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [twoCentralMat_apply, Matrix.mul_apply]
  eq' := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [twoCentralMat_apply, Matrix.mul_apply]
  q'e := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [twoCentralMat_apply, Matrix.mul_apply]
  qq' := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [twoCentralMat_apply, Matrix.mul_apply, ha]
  q'q := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [twoCentralMat_apply, Matrix.mul_apply, ha]
  et := twoCentralMat_transpose 0 1 1 0
  qt := twoCentralMat_transpose 0 1 a 0
  q't := twoCentralMat_transpose 0 1 a⁻¹ 0

end Pairs

section Sp4

variable {F : Type} [Field F]

theorem cbAt_sp4 [CharP F 2] : CBAt (StatedSp 2 F) (unipotent 2 F) := fun _ _ hc =>
  spHighRootCenter_le_unipotent (m := 0)
    (centralizer_unipotent_le (m := 0)
      (Subgroup.mem_centralizer_iff.mpr fun u hu => (hc u hu).symm))

theorem invAt_sp4 [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 3 ≤ f) :
    InvAt (StatedSp 2 F) (unipotent 2 F) := by
  intro z _ hz1 hzc
  obtain ⟨a, b, rfl⟩ := centralizer_unipotent_le (m := 0)
    (Subgroup.mem_centralizer_iff.mpr fun u hu => (hzc u hu).symm)
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      exact hz1 (twoCentralElt_zero 0 1)
    have hP := spPair_long ha
    have hz : spBlock hP (xT 1) = twoCentralElt 2 0 1 a 0 := by
      apply mat_injective
      rw [mat_spBlock_xT, mat_twoCentralElt]
    obtain ⟨y, h1, h2, h3⟩ := exists_inv_of_hom hF hf (spBlock hP)
      (spBlock_injective hP (by simp [twoCentralMat_apply]) (i := 0) (j := 0) (k := 0) (l := 0)
        (by simpa [twoCentralMat_apply] using ha) (by simpa [twoCentralMat_apply] using ha))
      one_ne_zero
    rw [hz] at h2
    exact ⟨y, h1, h2, h3⟩
  · have hP := spPair_inv a hb
    have hz : spBlock hP (xT 1) = twoCentralElt 2 0 1 a b := by
      apply mat_injective
      rw [mat_spBlock_xT, mat_twoCentralElt]
    obtain ⟨y, h1, h2, h3⟩ := exists_inv_of_hom hF hf (spBlock hP)
      (spBlock_injective hP (by simp) (i := 0) (j := 1) (k := 0) (l := 1)
        (by simpa [twoCentralMat_apply] using hb) (by simpa [qInv] using hb))
      one_ne_zero
    rw [hz] at h2
    exact ⟨y, h1, h2, h3⟩

@[expose] noncomputable def spProjEquiv [CharP F 2] : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
  MulEquiv.ofBijective (proj 2 F)
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
      exact CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot 2,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩

end Sp4

theorem ordBC_two_ne {q : ℕ} (hq : 8 ≤ q) : CFSG.Open.ordBC 2 q ≠ 20160 := by
  intro h
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have a1 : 4096 ≤ q ^ 4 := by
    calc 4096 = 8 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have a2 : 64 ≤ q ^ 2 := by
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hN : 4096 * (63 * 4095) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Nat.mul_le_mul a1 (Nat.mul_le_mul (by omega) (by omega))
  unfold CFSG.Open.ordBC at h
  rw [show 2 * 2 = 4 from rfl, show Finset.Icc 1 2 = {1, 2} from rfl,
    Finset.prod_pair (by norm_num)] at h
  have h3 := Nat.div_le_div_left hg hg0 (a := q ^ 4 * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)))
  rw [h] at h3
  have h4 := Nat.div_le_div_right (c := 2) hN
  norm_num at h3
  omega

theorem false_of_autConf_psp4 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel M .PSp 2 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).2.2.1 rfl
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hF4 : 4 ≤ Nat.card F := by omega
  have hU : (unipotent 2 F).map (spProjEquiv (F := F)).toMonoidHom = projUnipotent 2 F := rfl
  have hCB : CBAt (StatedProj (StatedSp 2 F)) (projUnipotent 2 F) := hU ▸ cbAt_sp4.map _
  have hInv : InvAt (StatedProj (StatedSp 2 F)) (projUnipotent 2 F) :=
    hU ▸ (invAt_sp4 hF hf).map _
  have h34 : ¬ IsPSL 3 2 2 (StatedProj (StatedSp 2 F)) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e.toEquiv, hcard] at h1
    exact ordBC_two_ne h8 h1
  exact not_autConf_of_at isSylowTwoOf_projUnipotent_two (n4At_sp4 hF4) h34 hCB hInv (h.map e)

end CFSG.Quasithin.H13.S126C

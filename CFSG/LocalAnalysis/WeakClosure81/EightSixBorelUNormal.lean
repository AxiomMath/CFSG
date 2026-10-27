module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofHermitian
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM
import CFSG.Quasithin.Vol2.Ch8Sec2L829NKLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.RankTwoClassical (hform)
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.ComponentClassification.RankTwoClassical.URigid

variable {m n : ℕ} {F : Type} [Field F] [Finite F]

private lemma borel86_un_one_le_of_ne_zero {u : Fin m → F} (hu : u ≠ 0) : 1 ≤ m := by
  obtain ⟨j, _⟩ := Function.ne_iff.mp hu
  exact Fin.pos_iff_nonempty.mpr ⟨j⟩

private lemma borel86_un_W_ne_zero (h : UnitaryFieldData 2 n F) {u : Fin m → F}
    (hu : u ≠ 0) : vecMulVec u (h.bar ∘ u) ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu
  simp only [Pi.zero_apply] at hj
  intro h0
  have hentry := congrFun (congrFun h0 j) j
  simp only [vecMulVec_apply, Function.comp_apply, Pi.zero_apply] at hentry
  exact mul_ne_zero hj (fun hb0 => hj (h.bar_eq_zero_iff.mp hb0)) hentry

private lemma borel86_un_one_add_smul_sq [CharP F 2] (b : F) {W : Matrix (Fin n) (Fin n) F}
    (hW2 : W * W = 0) : (1 + b • W) * (1 + b • W) = 1 := by
  have h1 : (1 + b • W) * (1 + b • W) =
      1 + b • W + (b • W + (b • W) * (b • W)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  have hbb : (b • W) * (b • W) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hW2, smul_zero, smul_zero]
  rw [h1, hbb, add_zero, add_assoc, ← two_smul F (b • W), CharTwo.two_eq_zero,
    zero_smul, add_zero]

private lemma borel86_un_inv_val (h : UnitaryFieldData 2 n F) (S : StatedSU m (2 ^ n) F) :
    (S⁻¹ : GL (Fin m) F).val = adjM h.bar (S : GL (Fin m) F).val :=
  Units.inv_eq_of_mul_eq_one_right
    (mul_eq_one_comm.mp (adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply S.2))

private lemma borel86_un_conj_W (h : UnitaryFieldData 2 n F) (S : StatedSU m (2 ^ n) F)
    (a : Fin m → F) :
    (S : GL (Fin m) F).val * vecMulVec a (h.bar ∘ a) * adjM h.bar (S : GL (Fin m) F).val =
      vecMulVec ((S : GL (Fin m) F).val *ᵥ a) (h.bar ∘ ((S : GL (Fin m) F).val *ᵥ a)) := by
  calc (S : GL (Fin m) F).val * vecMulVec a (h.bar ∘ a) * adjM h.bar (S : GL (Fin m) F).val
      = vecMulVec ((S : GL (Fin m) F).val *ᵥ a) (h.bar ∘ a) *
          adjM h.bar (S : GL (Fin m) F).val := by
        rw [Matrix.mul_vecMulVec]
    _ = vecMulVec ((S : GL (Fin m) F).val *ᵥ a)
          ((h.bar ∘ a) ᵥ* adjM h.bar (S : GL (Fin m) F).val) := by
        rw [Matrix.vecMulVec_mul]
    _ = vecMulVec ((S : GL (Fin m) F).val *ᵥ a)
          (h.bar ∘ ((S : GL (Fin m) F).val *ᵥ a)) := by
        apply congrArg (fun w => vecMulVec ((S : GL (Fin m) F).val *ᵥ a) w)
        rw [adjM, Matrix.vecMul_transpose]
        funext i
        exact (RingHom.map_mulVec h.bar (S : GL (Fin m) F).val a i).symm

private lemma borel86_un_commute_SU_iff (h : UnitaryFieldData 2 n F) {u : Fin m → F}
    {b : F} (hb0 : b ≠ 0) {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u))
    (Y : StatedSU m (2 ^ n) F) :
    Y * N = N * Y ↔ (Y : GL (Fin m) F).val * vecMulVec u (h.bar ∘ u) =
      vecMulVec u (h.bar ∘ u) * (Y : GL (Fin m) F).val := by
  have hcoe : (Y * N = N * Y : Prop) ↔
      (Y : GL (Fin m) F) * (N : GL (Fin m) F) =
        (N : GL (Fin m) F) * (Y : GL (Fin m) F) := by
    rw [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  rw [hcoe]
  constructor
  · intro hc
    have hmat := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, hN] at hmat
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul] at hmat
    exact smul_right_injective (Matrix (Fin m) (Fin m) F) hb0 (add_left_cancel hmat)
  · intro hW
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hN]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, hW]

private lemma borel86_un_mk_commute_iff (h : UnitaryFieldData 2 n F) {u : Fin m → F}
    (hu : u ≠ 0) (huu : hform h.bar u u = 0) {b : F} (hb0 : b ≠ 0)
    {N : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u))
    (Y : StatedSU m (2 ^ n) F) :
    (QuotientGroup.mk Y : StatedProj (StatedSU m (2 ^ n) F)) * QuotientGroup.mk N =
        QuotientGroup.mk N * QuotientGroup.mk Y ↔ Y * N = N * Y := by
  haveI := h.charP
  have hm1 : 1 ≤ m := borel86_un_one_le_of_ne_zero hu
  have hNN : N * N = 1 :=
    mul_self_eq_one_of_val hN (borel86_un_one_add_smul_sq b (vecMulVec_mul_self h huu))
  constructor
  · intro hq
    exact commute_of_uProj_commute hm1 hNN hq
  · intro hY
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hY]

theorem borel86_un_exists_eq_mk (h : UnitaryFieldData 2 n F)
    {t₀ : StatedProj (StatedSU m (2 ^ n) F)} (ht : IsUnitaryTransvectionIn m n t₀) :
    ∃ (a : Fin m → F) (c : F) (N₀ : StatedSU m (2 ^ n) F), a ≠ 0 ∧ hform h.bar a a = 0 ∧
      c ≠ 0 ∧ h.bar c = c ∧ (N₀ : GL (Fin m) F).val = 1 + c • vecMulVec a (h.bar ∘ a) ∧
      (QuotientGroup.mk N₀ : StatedProj (StatedSU m (2 ^ n) F)) = t₀ := by
  haveI := h.charP
  obtain ⟨g, hgt, hr⟩ := ht
  let M : GL (Fin m) F := (g : GL (Fin m) F)
  obtain ⟨p, φ, hpφ⟩ :=
    CFSG.Quasithin.H13.L829NK.exists_vecMulVec_of_rank_le_one (M.val - 1) hr.le
  have hdet : M.val.det = 1 := CFSG.Open.StatedAPI.det_of_mem_statedSU g.2
  have hMval : M.val = 1 + vecMulVec p φ := by rw [← hpφ, add_comm, sub_add_cancel]
  have hdetvec : (1 + vecMulVec p φ).det = 1 + φ ⬝ᵥ p := by
    rw [Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : φ ⬝ᵥ p = 0 := by
    have h1 := hdet
    rw [hMval, hdetvec] at h1
    exact add_left_cancel (by rw [h1, add_zero])
  have hW2 : (M.val - 1) * (M.val - 1) = 0 := by
    rw [hpφ, Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul]
    simp
  have hM1 : M.val = 1 + (M.val - 1) := by rw [add_comm, sub_add_cancel]
  have hMmat : M.val * M.val = 1 := by
    rw [hM1]
    simpa using borel86_un_one_add_smul_sq (1 : F) hW2
  have hMM : M * M = 1 := Units.ext (by rw [Units.val_mul, hMmat, Units.val_one])
  have hMne : M ≠ 1 := by
    intro hM1'
    have hrank : (M.val - 1).rank = 0 := by rw [hM1']; simp
    rw [hr] at hrank
    exact one_ne_zero hrank
  have hord : orderOf M = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hMM) hMne
  obtain ⟨a, c, ha, hc0, hc, haa, hac⟩ := exists_transvection_eq h g.2 hord hr
  refine ⟨a, c, g, ha, haa, hc0, hc, ?_, hgt⟩
  rw [← hac, add_comm, sub_add_cancel]

theorem borel86_un_ne_one (h : UnitaryFieldData 2 n F) {t₀ : StatedProj (StatedSU m (2 ^ n) F)}
    (ht : IsUnitaryTransvectionIn m n t₀) : t₀ ≠ 1 := by
  intro ht1
  obtain ⟨a, c, N₀, ha, haa, hc0, hc, hN₀, hmk⟩ := borel86_un_exists_eq_mk h ht
  have hπ : (QuotientGroup.mk N₀ : StatedProj (StatedSU m (2 ^ n) F)) =
      (1 : StatedProj (StatedSU m (2 ^ n) F)) := by rw [hmk, ht1]
  have hπ' : uProj F m n (1 : StatedSU m (2 ^ n) F) = uProj F m n N₀ := hπ.symm
  obtain ⟨c', hc'⟩ := uProj_eq_uProj_iff.mp hπ'
  have hN₀scalar : (N₀ : GL (Fin m) F).val = Matrix.scalar (Fin m) (c' : F) := by
    rw [hc', Units.val_mul, Subgroup.coe_one, Units.val_one, mul_one,
      GeneralLinearGroup.coe_scalar]
  have hsc : (1 : Matrix (Fin m) (Fin m) F) + c • vecMulVec a (h.bar ∘ a) =
      Matrix.scalar (Fin m) (c' : F) := by rw [← hN₀, hN₀scalar]
  have hscalar : Matrix.scalar (Fin m) (c' : F) =
      (c' : F) • (1 : Matrix (Fin m) (Fin m) F) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hzero : (1 - (c' : F)) • (1 : Matrix (Fin m) (Fin m) F) +
      c • vecMulVec a (h.bar ∘ a) = 0 := by
    rw [sub_smul, one_smul, ← hscalar, ← hsc]
    abel
  obtain ⟨_, hcW⟩ := eq_zero_of_smul_one_add_smul (borel86_un_W_ne_zero h ha)
    (vecMulVec_mul_self h haa) hzero
  exact hc0 hcW

theorem borel86_un_exists_conj (h : UnitaryFieldData 2 n F) (hm : 3 ≤ m) {a u : Fin m → F}
    (ha : a ≠ 0) (haa : hform h.bar a a = 0) (hu : u ≠ 0) (huu : hform h.bar u u = 0)
    {c b : F} (hc0 : c ≠ 0) (hc : h.bar c = c) (hb0 : b ≠ 0) (hb : h.bar b = b)
    {N₀ N : StatedSU m (2 ^ n) F}
    (hN₀ : (N₀ : GL (Fin m) F).val = 1 + c • vecMulVec a (h.bar ∘ a))
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u)) :
    ∃ S : StatedSU m (2 ^ n) F, S * N₀ * S⁻¹ = N := by
  haveI := h.charP
  have hbc : h.bar (b / c) = b / c := by rw [map_div₀, hb, hc]
  obtain ⟨μ, hμ⟩ := h.normHom_surjective ⟨b / c, h.mem_fixedField.2 hbc⟩
  have hμ' : μ * h.bar μ = b / c := by
    have := congrArg Subtype.val hμ
    simpa [UnitaryFieldData.norm] using this
  have hμ0 : μ ≠ 0 := by
    intro h0
    exact (div_ne_zero hb0 hc0) (by rw [← hμ', h0, zero_mul])
  have hμu : μ • u ≠ 0 := smul_ne_zero hμ0 hu
  have hμuu : hform h.bar (μ • u) (μ • u) = 0 := by
    rw [hform_smul_left, hform_smul_right, huu, mul_zero, mul_zero]
  obtain ⟨S, hS⟩ := exists_statedSU_mulVec_eq h hm ha haa hμu hμuu
  have hvec : vecMulVec (μ • u) (h.bar ∘ (μ • u)) =
      (μ * h.bar μ) • vecMulVec u (h.bar ∘ u) := by
    rw [show h.bar ∘ (μ • u) = h.bar μ • (h.bar ∘ u) from by
      funext j; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul],
      Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]
  have hSadj : (S : GL (Fin m) F).val * adjM h.bar (S : GL (Fin m) F).val = 1 :=
    mul_eq_one_comm.mp (adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply S.2)
  have hmain : (S : GL (Fin m) F).val * (1 + c • vecMulVec a (h.bar ∘ a)) *
      (S⁻¹ : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u) := by
    rw [borel86_un_inv_val h S]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      borel86_un_conj_W h S a, hS]
    rw [hSadj, hvec, smul_smul, hμ', mul_div_cancel₀ b hc0]
  refine ⟨S, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hN₀, hN]
  exact hmain

theorem borel86_un_commute_mk_iff (h : UnitaryFieldData 2 n F) {u : Fin m → F} (hu : u ≠ 0)
    (huu : hform h.bar u u = 0) {b b' : F} (hb0 : b ≠ 0) (hb0' : b' ≠ 0)
    {N N' : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u))
    (hN' : (N' : GL (Fin m) F).val = 1 + b' • vecMulVec u (h.bar ∘ u))
    (y : StatedProj (StatedSU m (2 ^ n) F)) :
    y * QuotientGroup.mk N = QuotientGroup.mk N * y ↔
      y * QuotientGroup.mk N' = QuotientGroup.mk N' * y := by
  obtain ⟨Y, hY⟩ := QuotientGroup.mk_surjective y
  rw [← hY, borel86_un_mk_commute_iff h hu huu hb0 hN Y,
    borel86_un_mk_commute_iff h hu huu hb0' hN' Y]
  rw [borel86_un_commute_SU_iff h hb0 hN Y, borel86_un_commute_SU_iff h hb0' hN' Y]

theorem borel86_un_mk_ne_mk (h : UnitaryFieldData 2 n F) {u : Fin m → F} (hu : u ≠ 0)
    (huu : hform h.bar u u = 0) {b b' : F} (hbb : b ≠ b') {N N' : StatedSU m (2 ^ n) F}
    (hN : (N : GL (Fin m) F).val = 1 + b • vecMulVec u (h.bar ∘ u))
    (hN' : (N' : GL (Fin m) F).val = 1 + b' • vecMulVec u (h.bar ∘ u)) :
    (QuotientGroup.mk N : StatedProj (StatedSU m (2 ^ n) F)) ≠ QuotientGroup.mk N' := by
  haveI := h.charP
  have hm1 : 1 ≤ m := borel86_un_one_le_of_ne_zero hu
  have hNN : N * N = 1 :=
    mul_self_eq_one_of_val hN (borel86_un_one_add_smul_sq b (vecMulVec_mul_self h huu))
  have hN'N' : N' * N' = 1 :=
    mul_self_eq_one_of_val hN' (borel86_un_one_add_smul_sq b' (vecMulVec_mul_self h huu))
  intro hπ
  have hNeq : N = N' := eq_of_uProj_eq_of_mul_self hm1 hπ hNN hN'N'
  have hmat : (N : GL (Fin m) F).val = (N' : GL (Fin m) F).val := by rw [hNeq]
  rw [hN, hN'] at hmat
  have hcancel : b • vecMulVec u (h.bar ∘ u) = b' • vecMulVec u (h.bar ∘ u) :=
    add_left_cancel hmat
  have hsub : (b - b') • vecMulVec u (h.bar ∘ u) = 0 := by rw [sub_smul, hcancel, sub_self]
  have hW0 : vecMulVec u (h.bar ∘ u) = 0 :=
    smul_right_injective (Matrix (Fin m) (Fin m) F) (sub_ne_zero.mpr hbb)
      (hsub.trans (smul_zero (b - b')).symm)
  exact absurd hW0 (borel86_un_W_ne_zero h hu)

theorem borel86_un_exists_fixed_ne (h : UnitaryFieldData 2 n F) (hn : 1 < n) :
    ∃ d : F, d ≠ 0 ∧ d ≠ 1 ∧ h.bar d = d := by
  have hn2 : 2 ≤ n := hn
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hcard : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    exact lt_of_lt_of_le (by norm_num) hpow
  have hne : ∃ d : h.fixedField, d ≠ 0 ∧ d ≠ 1 := by
    by_contra hc
    rw [not_exists] at hc
    have hsurj : Function.Surjective (fun b : Bool => if b then (1 : h.fixedField) else 0) := by
      intro d
      by_cases hd0 : d = 0
      · exact ⟨false, by simp [hd0]⟩
      · by_cases hd1 : d = 1
        · exact ⟨true, by simp [hd1]⟩
        · exact absurd ⟨hd0, hd1⟩ (hc d)
    have hle := Nat.card_le_card_of_surjective _ hsurj
    have hBool : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    omega
  obtain ⟨d, hd0, hd1⟩ := hne
  exact ⟨(d : F), fun hd => hd0 (Subtype.ext hd), fun hd => hd1 (Subtype.ext hd),
    h.mem_fixedField.mp d.2⟩

theorem borel86_un_exists_conj_ne (h : UnitaryFieldData 2 n F) (hn : 1 < n) (hm : 3 ≤ m)
    {t₀ : StatedProj (StatedSU m (2 ^ n) F)} (ht : IsUnitaryTransvectionIn m n t₀) :
    ∃ d₀ t₁ : StatedProj (StatedSU m (2 ^ n) F), d₀ * t₀ * d₀⁻¹ = t₁ ∧ t₁ ≠ t₀ ∧
      ∀ y : StatedProj (StatedSU m (2 ^ n) F), y * t₀ = t₀ * y ↔ y * t₁ = t₁ * y := by
  haveI := h.charP
  obtain ⟨a, c, N₀, ha, haa, hc0, hc, hN₀, hmk⟩ := borel86_un_exists_eq_mk h ht
  obtain ⟨d, hd0, hd1, hd⟩ := borel86_un_exists_fixed_ne h hn
  have hb0 : c * d ≠ 0 := mul_ne_zero hc0 hd0
  have hb : h.bar (c * d) = c * d := by rw [map_mul, hc, hd]
  obtain ⟨N, hN⟩ := exists_one_add_mem h haa hb
  obtain ⟨S, hS⟩ := borel86_un_exists_conj h hm ha haa ha haa hc0 hc hb0 hb hN₀ hN
  refine ⟨QuotientGroup.mk S, QuotientGroup.mk N, ?_, ?_, ?_⟩
  · rw [← hmk]
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    rw [hS]
  · rw [← hmk]
    exact borel86_un_mk_ne_mk h ha haa (fun hcd => hd1 ((mul_eq_left₀ hc0).mp hcd)) hN hN₀
  · intro y
    rw [← hmk]
    exact borel86_un_commute_mk_iff h ha haa hc0 hb0 hN₀ hN y

end CFSG.LocalAnalysis.WeakClosure81

end

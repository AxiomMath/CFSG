module

public import CFSG.RankThree.PartTwo.KFacts.KS21U34Check
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.CurtisTits.Conclusion

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U34

open CFSG.GH74.KGroups Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

instance : CharP GF16 2 := CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)

instance : CharP GF4 2 := CharTwo.of_one_ne_zero_of_two_eq_zero (by decide) (by decide)

theorem card_GF16 : Nat.card GF16 = (2 ^ 2) ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_GF4 : Nat.card GF4 = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

@[expose] def emb4 : GF4 →+* GF16 where
  toFun := emb4Fun
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem emb4_apply (a : GF4) : emb4 a = emb4Fun a := rfl

theorem emb4_injective : Function.Injective emb4 := emb4.injective

theorem emb4_pre4 (c : GF16) (hc : frob4 c = c) : emb4Fun (pre4 c) = c := by
  revert c
  decide

abbrev σ16 : GF16 ≃+* GF16 := unitaryInvolution GF16 2 2

theorem σ16_apply (c : GF16) : σ16 c = frob4 c := by
  rw [σ16, unitaryInvolution_apply, frob4]
  ring

abbrev Y : Subgroup (GL (Fin 3) GF16) := SU σ16 3

abbrev mat (y : Y) : Mat3 := ((y : GL (Fin 3) GF16) : Mat3)

theorem mat_mul (a b : Y) : mat (a * b) = mat a * mat b := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem antidiag_three_eq : (antidiag 3 : Mat3) = J3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem conjTr_eq_ct3 (A : Mat3) : conjTr σ16 A = ct3 A := by
  ext i j
  simp only [conjTr, ct3, Matrix.transpose_apply, Matrix.map_apply]
  exact σ16_apply _

theorem det_eq_det3 (A : Mat3) : A.det = det3 A := by
  rw [Matrix.det_fin_three, det3]

theorem mem_Y_iff (g : GL (Fin 3) GF16) : g ∈ Y ↔ det3 (g : Mat3) = 1 ∧ IsGU3 (g : Mat3) := by
  rw [mem_SU, conjTr_eq_ct3, antidiag_three_eq, det_eq_det3]
  rfl

theorem isGU3_mat (y : Y) : IsGU3 (mat y) := ((mem_Y_iff _).mp y.2).2

@[expose] def t0GL : GL (Fin 3) GF16 :=
  ⟨t0Mat, t0Mat * t0Mat, by rw [← Matrix.mul_assoc]; exact u34Facts.1.1, u34Facts.1.1⟩

@[expose] def t0 : Y := ⟨t0GL, by
  rw [mem_Y_iff]
  exact ⟨u34Facts.1.2.2.2, u34Facts.1.2.2.1⟩⟩

theorem mat_t0 : mat t0 = t0Mat := rfl

theorem t0_pow_three : t0 ^ 3 = 1 := by
  apply mat_injective
  rw [pow_succ, pow_succ, pow_one, mat_mul, mat_mul, mat_t0, mat_one]
  exact u34Facts.1.1

theorem t0_ne_one : t0 ≠ 1 := fun h => u34Facts.1.2.1 (by rw [← mat_t0, h, mat_one])

theorem orderOf_t0 : orderOf t0 = 3 :=
  orderOf_eq_prime t0_pow_three t0_ne_one

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) GF4) :
    blockMat (A * B) = blockMat A * blockMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, ← emb4_apply]

theorem blockMat_one : blockMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat, ← emb4_apply]

theorem coe_mul_SL24 (M N : SL24) :
    ((M * N : SL24) : Matrix (Fin 2) (Fin 2) GF4) =
      (M : Matrix (Fin 2) (Fin 2) GF4) * (N : Matrix (Fin 2) (Fin 2) GF4) := rfl

theorem coe_one_SL24 : ((1 : SL24) : Matrix (Fin 2) (Fin 2) GF4) = 1 := rfl

@[expose] def blockGL (M : SL24) : GL (Fin 3) GF16 :=
  ⟨blockMat (M : Matrix (Fin 2) (Fin 2) GF4), blockMat ((M⁻¹ : SL24) : Matrix (Fin 2) (Fin 2) GF4),
    by rw [← blockMat_mul, ← coe_mul_SL24, mul_inv_cancel, coe_one_SL24, blockMat_one],
    by rw [← blockMat_mul, ← coe_mul_SL24, inv_mul_cancel, coe_one_SL24, blockMat_one]⟩

theorem coe_blockGL (M : SL24) :
    ((blockGL M : GL (Fin 3) GF16) : Mat3) = blockMat (M : Matrix (Fin 2) (Fin 2) GF4) := rfl

theorem blockGL_mem (M : SL24) : blockGL M ∈ Y := by
  rw [mem_Y_iff, coe_blockGL]
  exact ⟨(u34Facts.2.2.2.2.2 M).2, (u34Facts.2.2.2.2.2 M).1⟩

@[expose] def iota : SL24 →* Y where
  toFun M := ⟨blockGL M, blockGL_mem M⟩
  map_one' := mat_injective (by
    change blockMat ((1 : SL24) : Matrix (Fin 2) (Fin 2) GF4) = 1
    rw [coe_one_SL24, blockMat_one])
  map_mul' M N := mat_injective (by
    change blockMat ((M * N : SL24) : Matrix (Fin 2) (Fin 2) GF4) =
      blockMat (M : Matrix (Fin 2) (Fin 2) GF4) * blockMat (N : Matrix (Fin 2) (Fin 2) GF4)
    rw [coe_mul_SL24, blockMat_mul])

theorem mat_iota (M : SL24) : mat (iota M) = blockMat (M : Matrix (Fin 2) (Fin 2) GF4) := rfl

theorem iota_injective : Function.Injective iota := by
  intro M N h
  have h' := congrArg mat h
  rw [mat_iota, mat_iota] at h'
  ext i j
  apply emb4_injective
  rw [emb4_apply, emb4_apply]
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h' 0) 0
  · exact congrFun (congrFun h' 0) 2
  · exact congrFun (congrFun h' 2) 0
  · exact congrFun (congrFun h' 2) 2

@[expose] def K0 : Subgroup Y := iota.range

@[expose] def K0Equiv : SL24 ≃* K0 := MonoidHom.ofInjective iota_injective

theorem card_SL24 : Nat.card SL24 = 60 := by
  rw [Nat.card_eq_fintype_card]
  exact u34Facts.2.2.2.2.1.1

theorem card_K0 : Nat.card K0 = 60 := by
  rw [← Nat.card_congr K0Equiv.toEquiv, card_SL24]

theorem mem_K0_of_inK0 (g : Y) (hg : InK0 (mat g)) : g ∈ K0 := by
  obtain ⟨h01, h10, h12, h21, h11, f00, f02, f20, f22, hdet⟩ := hg
  let A : Matrix (Fin 2) (Fin 2) GF4 :=
    !![pre4 (mat g 0 0), pre4 (mat g 0 2); pre4 (mat g 2 0), pre4 (mat g 2 2)]
  have hA : A.det = 1 := by
    apply emb4_injective
    rw [Matrix.det_fin_two, map_one, map_sub, map_mul, map_mul]
    simp only [A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, emb4_apply, emb4_pre4 _ f00, emb4_pre4 _ f02,
      emb4_pre4 _ f20, emb4_pre4 _ f22]
    exact hdet
  refine ⟨(⟨A, hA⟩ : SL24), mat_injective ?_⟩
  change blockMat A = mat g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat, A, emb4_pre4 _ f00, emb4_pre4 _ f02, emb4_pre4 _ f20, emb4_pre4 _ f22,
      h01, h10, h12, h21, h11]

theorem t0_mem_K0 : t0 ∈ K0 := mem_K0_of_inK0 t0 (by rw [mat_t0]; decide)

theorem center_SL24 : Subgroup.center SL24 = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have key : ∀ r : GF4, r ^ 2 = 1 → r = 1 := by decide
  have hr1 : r = 1 := key r hr
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

@[expose] def pslEquivSL24 : ProjectiveSpecialLinearGroup (Fin 2) GF4 ≃* SL24 :=
  (QuotientGroup.quotientMulEquivOfEq center_SL24).trans QuotientGroup.quotientBot

theorem nonempty_equiv_SL24 {K : Type} [Group K] (hK : StatedClassicalModel K .PSL 2 2 2) :
    Nonempty (K ≃* SL24) := by
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := hK
  let _ : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card GF4 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_GF4]
  exact ⟨φ.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
    ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans pslEquivSL24))⟩

theorem statedClassicalModel_SL24 : StatedClassicalModel SL24 .PSL 2 2 2 :=
  ⟨⟨Nat.prime_two, by norm_num, by decide⟩, GF4, inferInstance, inferInstance, card_GF4,
    ⟨pslEquivSL24.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 GF4)⟩⟩

theorem statedClassicalModel_K0 : StatedClassicalModel K0 .PSL 2 2 2 :=
  CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv K0Equiv statedClassicalModel_SL24

theorem eq_top_of_orderOf {H : Subgroup SL24} {a b : SL24} (ha : a ∈ H) (hb : b ∈ H)
    (ha3 : orderOf a = 3) (hb2 : orderOf b = 2) (hab : orderOf (a * b) = 5) : H = ⊤ := by
  classical
  have h3 : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H ha
    rwa [ha3] at this
  have h2 : 2 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hb
    rwa [hb2] at this
  have h5 : 5 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H (H.mul_mem ha hb)
    rwa [hab] at this
  have h30 : 30 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 5)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3) h5
  have h60 : Nat.card H ∣ 60 := card_SL24 ▸ Subgroup.card_subgroup_dvd_card H
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hcases : Nat.card H = 30 ∨ Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h30
    obtain ⟨m, hm⟩ := h60
    rw [hk] at hm hpos
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have : 30 * k * m ≥ 30 * 3 * 1 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega))
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm; omega
        · exact h0
      omega
    interval_cases k <;> omega
  rcases hcases with h | h
  · exfalso
    have hidx : H.index = 2 := by
      have := H.card_mul_index
      rw [h, card_SL24] at this
      omega
    have hsq : ((Finset.univ.image fun g : SL24 => g ^ 2 : Finset SL24) : Set SL24) ⊆ H := by
      intro x hx
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact Subgroup.sq_mem_of_index_two hidx g
    have hle := Set.ncard_le_ncard hsq (Set.toFinite _)
    rw [Set.ncard_coe_finset, u34Facts.2.2.2.2.1.2, ← Nat.card_coe_set_eq] at hle
    have hH : Nat.card (H : Set SL24) = Nat.card H := rfl
    omega
  · exact Subgroup.eq_top_of_card_eq H (by rw [h, card_SL24])

theorem eq_zero_of_mul_eq {x c c' : GF16} (h : x * c = c' * x) (hc : c ≠ c') : x = 0 := by
  have : x * (c - c') = 0 := by rw [mul_sub, h, mul_comm]; ring
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hc

theorem t0Mat_eq_diagonal : t0Mat = Matrix.diagonal ![om, 1, om * om] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_monMat_of_mul_t0 (S : Mat3) (h : S * t0Mat = t0Mat * t0Mat * S) :
    S = monMat (S 0 2) (S 1 1) (S 2 0) := by
  rw [t0Mat_eq_diagonal, Matrix.diagonal_mul_diagonal] at h
  have key : ∀ i j, S i j * ![om, 1, om * om] j =
      (![om, 1, om * om] i * ![om, 1, om * om] i) * S i j := by
    intro i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  ext i j
  fin_cases i <;> fin_cases j
  · exact eq_zero_of_mul_eq (key 0 0) (by decide)
  · exact eq_zero_of_mul_eq (key 0 1) (by decide)
  · rfl
  · exact eq_zero_of_mul_eq (key 1 0) (by decide)
  · rfl
  · exact eq_zero_of_mul_eq (key 1 2) (by decide)
  · rfl
  · exact eq_zero_of_mul_eq (key 2 1) (by decide)
  · exact eq_zero_of_mul_eq (key 2 2) (by decide)

theorem mul_sMat (x : Mat3) (a : GF16) : x * sMat a =
    !![x 0 2 * (a * a), x 0 1, x 0 0 * a; x 1 2 * (a * a), x 1 1, x 1 0 * a;
      x 2 2 * (a * a), x 2 1, x 2 0 * a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem sMat_mul (x : Mat3) (a : GF16) : sMat a * x =
    !![a * x 2 0, a * x 2 1, a * x 2 2; x 1 0, x 1 1, x 1 2;
      a * a * x 0 0, a * a * x 0 1, a * a * x 0 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_commMat_of_comm (x : Mat3) {a : GF16} (ha : a * a * a = 1)
    (h : x * sMat a = sMat a * x) :
    x = commMat a (x 0 0) (x 0 1) (x 0 2) (x 1 0) (x 1 1) := by
  rw [mul_sMat, sMat_mul] at h
  have e : ∀ i j, (!![x 0 2 * (a * a), x 0 1, x 0 0 * a; x 1 2 * (a * a), x 1 1, x 1 0 * a;
      x 2 2 * (a * a), x 2 1, x 2 0 * a] : Mat3) i j =
      (!![a * x 2 0, a * x 2 1, a * x 2 2; x 1 0, x 1 1, x 1 2;
        a * a * x 0 0, a * a * x 0 1, a * a * x 0 2] : Mat3) i j := fun i j => by rw [h]
  have h00 : x 0 2 * (a * a) = a * x 2 0 := by simpa using e 0 0
  have h01 : x 0 1 = a * x 2 1 := by simpa using e 0 1
  have h02 : x 0 0 * a = a * x 2 2 := by simpa using e 0 2
  have h10 : x 1 2 * (a * a) = x 1 0 := by simpa using e 1 0
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change x 1 2 = a * x 1 0
    linear_combination a * h10 - x 1 2 * ha
  · change x 2 0 = a * x 0 2
    linear_combination (-(a * a)) * h00 + (a * x 0 2 - x 2 0) * ha
  · change x 2 1 = a * a * x 0 1
    linear_combination (-(a * a)) * h01 - x 2 1 * ha
  · change x 2 2 = x 0 0
    linear_combination (-(a * a)) * h02 + (x 0 0 - x 2 2) * ha

theorem sq_commMat_11 (a u v w y z : GF16) :
    (commMat a u v w y z * commMat a u v w y z) 1 1 = e11 a z v y := by
  simp [commMat, e11, Matrix.mul_apply, Fin.sum_univ_three]

theorem sq_commMat_02 (a u v w y z : GF16) :
    (commMat a u v w y z * commMat a u v w y z) 0 2 = e02 a u v w y := by
  simp [commMat, e02, Matrix.mul_apply, Fin.sum_univ_three]

theorem sq_commMat_00 (a u v w y z : GF16) :
    (commMat a u v w y z * commMat a u v w y z) 0 0 = e00 a u v w y := by
  simp [commMat, e00, Matrix.mul_apply, Fin.sum_univ_three]

theorem sMat_of_inverts {s : Y} (hss : s * s = 1) (hst : s * t0 = t0 * t0 * s) :
    ∃ a : GF16, a * a * a = 1 ∧ mat s = sMat a ∧ s ∈ K0 := by
  have hm : mat s * t0Mat = t0Mat * t0Mat * mat s := by
    rw [← mat_t0, ← mat_mul, ← mat_mul, ← mat_mul, hst]
  have hmon := eq_monMat_of_mul_t0 _ hm
  have hsq : mat s * mat s = 1 := by rw [← mat_mul, hss, mat_one]
  have hgu := isGU3_mat s
  rw [hmon] at hsq hgu
  obtain ⟨hK0, ha, hs⟩ := u34Facts.2.1 _ _ _ hsq hgu
  rw [← hmon] at hK0 hs
  exact ⟨_, ha, hs, mem_K0_of_inK0 s hK0⟩

theorem mem_K0_of_comm {a : GF16} (ha : a * a * a = 1) {x s : Y} (hs : mat s = sMat a)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hxs : x * s = s * x) : x ∈ K0 := by
  have hm : mat x * sMat a = sMat a * mat x := by rw [← hs, ← mat_mul, ← mat_mul, hxs]
  have hc := eq_commMat_of_comm _ ha hm
  have hsq : mat x * mat x = 1 := by rw [← mat_mul, hxx, mat_one]
  have hne : mat x ≠ 1 := fun h => hx1 (mat_injective (by rw [h, mat_one]))
  have hgu := isGU3_mat x
  rw [hc] at hsq hne hgu
  have h11 := sq_commMat_11 a (mat x 0 0) (mat x 0 1) (mat x 0 2) (mat x 1 0) (mat x 1 1)
  have h02 := sq_commMat_02 a (mat x 0 0) (mat x 0 1) (mat x 0 2) (mat x 1 0) (mat x 1 1)
  have h00 := sq_commMat_00 a (mat x 0 0) (mat x 0 1) (mat x 0 2) (mat x 1 0) (mat x 1 1)
  rw [hsq] at h11 h02 h00
  have hK0 := u34Facts.2.2.1 a ha _ _ _ (by rw [← h11]; rfl) _ _ (by rw [← h02]; rfl)
    (by rw [← h00]; rfl) hsq hne hgu
  rw [← hc] at hK0
  exact mem_K0_of_inK0 x hK0

theorem eq_K0_of_mem {K : Subgroup Y} (hK : StatedClassicalModel K .PSL 2 2 2) (ht : t0 ∈ K) :
    K = K0 := by
  obtain ⟨e⟩ := nonempty_equiv_SL24 hK
  set τ := e ⟨t0, ht⟩ with hτ
  have hτ1 : τ ≠ 1 := by
    rw [hτ, Ne, MulEquiv.map_eq_one_iff]
    intro h
    exact t0_ne_one (congrArg Subtype.val h)
  have hτ3 : τ ^ 3 = 1 := by
    have : (⟨t0, ht⟩ : K) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, t0_pow_three]; rfl)
    rw [hτ, ← map_pow, this, map_one]
  obtain ⟨σ, hσσ, hσ1, hστ, ξ, hξξ, hξ1, hξσ, hτξ5, hτξ1⟩ := u34Facts.2.2.2.1 τ hτ1 hτ3
  let f : SL24 →* Y := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hft : f τ = t0 := by
    change ((e.symm τ : K) : Y) = t0
    rw [hτ, e.symm_apply_apply]
  have hfne : ∀ g : SL24, g ≠ 1 → f g ≠ 1 := fun g hg h => hg (hf (by rw [h, map_one]))
  have hss : f σ * f σ = 1 := by rw [← map_mul, hσσ, map_one]
  have hst : f σ * t0 = t0 * t0 * f σ := by
    have h1 : f σ * t0 * f σ * t0 = 1 := by rw [← hft, ← map_mul, ← map_mul, ← map_mul, hστ,
      map_one]
    have hsinv : (f σ)⁻¹ = f σ := inv_eq_of_mul_eq_one_right hss
    have htinv : t0⁻¹ = t0 * t0 := inv_eq_of_mul_eq_one_right (by
      rw [← mul_assoc, ← pow_two, ← pow_succ, t0_pow_three])
    have h2 : (f σ * t0)⁻¹ = f σ * t0 := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h1)
    rw [← h2, _root_.mul_inv_rev, hsinv, htinv]
  obtain ⟨a, ha, hsa, hsK0⟩ := sMat_of_inverts hss hst
  have hxx : f ξ * f ξ = 1 := by rw [← map_mul, hξξ, map_one]
  have hxs : f ξ * f σ = f σ * f ξ := by rw [← map_mul, ← map_mul, hξσ]
  have hxK0 := mem_K0_of_comm ha hsa hxx (hfne ξ hξ1) hxs
  let H : Subgroup SL24 := (K0.subgroupOf K).map e.toMonoidHom
  have hτH : τ ∈ H := ⟨⟨t0, ht⟩, Subgroup.mem_subgroupOf.mpr t0_mem_K0, rfl⟩
  have hξH : ξ ∈ H := ⟨e.symm ξ, Subgroup.mem_subgroupOf.mpr hxK0, e.apply_symm_apply ξ⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHtop : H = ⊤ := eq_top_of_orderOf hτH hξH (orderOf_eq_prime hτ3 hτ1)
    (orderOf_eq_prime (by rw [pow_two]; exact hξξ) hξ1) (orderOf_eq_prime hτξ5 hτξ1)
  have hle : K ≤ K0 := by
    intro k hk
    have hkH : e ⟨k, hk⟩ ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
    obtain ⟨k', hk', hk'e⟩ := hkH
    have : k' = ⟨k, hk⟩ := e.injective hk'e
    rw [this] at hk'
    exact Subgroup.mem_subgroupOf.mp hk'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_K0, Nat.card_congr e.toEquiv, card_SL24]

theorem statedScalars_subgroupOf_eq_bot :
    (StatedScalars (Fin 3) GF16).subgroupOf (StatedSU 3 (2 ^ 2) GF16) = ⊥ := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 GF16 :=
    ⟨Nat.prime_two, by norm_num, by rw [Nat.card_eq_fintype_card]; rfl⟩
  rw [← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq h (by norm_num)]
  apply Subgroup.eq_bot_of_card_eq
  rw [CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars h (by norm_num)]
  rfl

@[expose] def statedProjEquiv :
    StatedProj (StatedSU 3 (2 ^ 2) GF16) ≃* StatedSU 3 (2 ^ 2) GF16 :=
  (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_eq_bot).trans
    QuotientGroup.quotientBot

theorem card_Y : Nat.card Y = 62400 := by
  rw [Nat.card_congr (equivStatedSU card_GF16 3).toEquiv,
    ← Nat.card_congr statedProjEquiv.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num)
      card_GF16 (by norm_num)]
  decide

theorem factorization_card_Y : (Nat.card Y).factorization 3 = 1 := by
  rw [card_Y, Nat.factorization_def _ Nat.prime_three,
    show (62400 : ℕ) = 3 * 20800 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_eq_map_conj (T : Subgroup Y) (hT : Nat.card T = 3) :
    ∃ g : Y, T = (Subgroup.zpowers t0).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 Y := Sylow.ofCard T (by rw [hT, factorization_card_Y, pow_one])
  let P0 : Sylow 3 Y := Sylow.ofCard (Subgroup.zpowers t0)
    (by rw [Nat.card_zpowers, orderOf_t0, factorization_card_Y, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y P0 P
  refine ⟨g, ?_⟩
  have h1 : ((g • P0 : Sylow 3 Y) : Subgroup Y) = (P : Subgroup Y) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
  exact h1.symm

theorem existsUnique_Y (T : Subgroup Y) (hT : Nat.card T = 3) :
    ∃! K : Subgroup Y, StatedClassicalModel K .PSL 2 2 2 ∧ T ≤ K := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj T hT
  let c := MulAut.conj g
  have hmodel : ∀ L : Subgroup Y, StatedClassicalModel L .PSL 2 2 2 →
      StatedClassicalModel (L.map c.toMonoidHom) .PSL 2 2 2 := fun L hL =>
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (L.equivMapOfInjective c.toMonoidHom c.injective) hL
  refine ⟨K0.map c.toMonoidHom, ⟨hmodel K0 statedClassicalModel_K0, Subgroup.map_mono
    ((Subgroup.zpowers_le).mpr t0_mem_K0)⟩, ?_⟩
  rintro K ⟨hK, hTK⟩
  have hK' : StatedClassicalModel (K.map c.symm.toMonoidHom) .PSL 2 2 2 :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (K.equivMapOfInjective c.symm.toMonoidHom c.symm.injective) hK
  have ht : t0 ∈ K.map c.symm.toMonoidHom := by
    refine ⟨c t0, hTK ⟨t0, Subgroup.mem_zpowers t0, rfl⟩, ?_⟩
    exact c.symm_apply_apply t0
  have h := eq_K0_of_mem hK' ht
  rw [← h, Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id K]
  congr 1
  exact MonoidHom.ext fun y => (c.apply_symm_apply y).symm

theorem nonempty_equiv_Y {X : Type} [Group X] (hX : StatedClassicalModel X .PSU 3 2 2) :
    Nonempty (X ≃* Y) := by
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := hX
  let _ : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card GF16 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_GF16]
  let ρ : F ≃+* GF16 := FiniteField.ringEquivOfCardEq hcard
  exact ⟨φ.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr ρ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU ρ 3 (2 ^ 2))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars ρ)).trans
    (statedProjEquiv.trans (equivStatedSU card_GF16 3).symm))⟩

theorem existsUnique_psl24_of_card_three {X : Type} [Group X]
    (hX : StatedClassicalModel X .PSU 3 2 2) (T : Subgroup X) (hT : Nat.card T = 3) :
    ∃! K : Subgroup X, StatedClassicalModel K .PSL 2 2 2 ∧ T ≤ K := by
  obtain ⟨φ⟩ := nonempty_equiv_Y hX
  have hT' : Nat.card (T.map φ.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective φ.injective, hT]
  obtain ⟨K, ⟨hK, hTK⟩, huniq⟩ := existsUnique_Y _ hT'
  have hmodel : ∀ {A B : Type} [Group A] [Group B] (ψ : A ≃* B) (L : Subgroup A),
      StatedClassicalModel L .PSL 2 2 2 →
        StatedClassicalModel (L.map ψ.toMonoidHom) .PSL 2 2 2 := fun ψ L hL =>
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (L.equivMapOfInjective ψ.toMonoidHom ψ.injective) hL
  have hback : ∀ L : Subgroup X, (L.map φ.toMonoidHom).map φ.symm.toMonoidHom = L := by
    intro L
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id L]
    congr 1
    exact MonoidHom.ext fun x => φ.symm_apply_apply x
  refine ⟨K.map φ.symm.toMonoidHom, ⟨hmodel φ.symm K hK, ?_⟩, ?_⟩
  · rw [← hback T]
    exact Subgroup.map_mono hTK
  · rintro L ⟨hL, hTL⟩
    have := huniq (L.map φ.toMonoidHom) ⟨hmodel φ L hL, Subgroup.map_mono hTL⟩
    rw [← this, hback]

end CFSG.RankThree.PartTwo.KFacts.KS21.U34

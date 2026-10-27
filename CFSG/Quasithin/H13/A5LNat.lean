module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.Background.G64Realize

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open Matrix

section Uni

variable {n : ℕ}

@[expose] def IsUni (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  (∀ i, M i i = 1) ∧ ∀ i j, j < i → M i j = 0

theorem IsUni.one : IsUni (1 : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨fun i => Matrix.one_apply_eq i, fun _ _ h => Matrix.one_apply_ne (ne_of_lt h).symm⟩

theorem IsUni.mul {M N : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : IsUni M) (hN : IsUni N) :
    IsUni (M * N) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.1, hN.1, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hM.2 i k h, zero_mul]
      · rw [hN.2 k i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM.2 i k h, zero_mul]
    · rw [hN.2 k j (lt_of_lt_of_le hij h), mul_zero]

theorem IsUni.det_eq_one {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : IsUni M) : M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => hM.2 i j h)]
  exact Finset.prod_eq_one fun i _ => hM.1 i

@[expose] noncomputable def uniGL (n : ℕ) : Subgroup (GL (Fin n) (ZMod 2)) where
  carrier := {g | IsUni (g : Matrix (Fin n) (Fin n) (ZMod 2))}
  mul_mem' {a b} ha hb := by
    show IsUni ((a * b : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [Units.val_mul]
    exact IsUni.mul ha hb
  one_mem' := by
    show IsUni ((1 : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [Units.val_one]
    exact IsUni.one
  inv_mem' {a} ha := by
    have hpow : ∀ k : ℕ,
        IsUni ((a ^ k : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      intro k
      induction k with
      | zero => rw [pow_zero, Units.val_one]; exact IsUni.one
      | succ k ih => rw [pow_succ, Units.val_mul]; exact IsUni.mul ih ha
    have hpos : 0 < orderOf a := orderOf_pos a
    have h1 : a ^ (orderOf a - 1) = a⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one])
    show IsUni ((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
    rw [← h1]
    exact hpow _

theorem mem_uniGL {g : GL (Fin n) (ZMod 2)} :
    g ∈ uniGL n ↔ IsUni (g : Matrix (Fin n) (Fin n) (ZMod 2)) := Iff.rfl

@[expose] noncomputable def uniUnit {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : IsUni M) :
    GL (Fin n) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM.det_eq_one]; exact one_ne_zero)

theorem coe_uniUnit {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : IsUni M) :
    (uniUnit hM : Matrix (Fin n) (Fin n) (ZMod 2)) = M := rfl

theorem exists_conj_of_comm_sylow [NeZero n] (hU : IsPGroup 2 (uniGL n))
    (hUi : ¬ 2 ∣ (uniGL n).index) {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hZ : ∀ m ∈ uniGL n, (∀ u ∈ uniGL n, m * u = u * m) → m ≠ 1 →
      (m : Matrix (Fin n) (Fin n) (ZMod 2)) = t)
    (P : Sylow 2 (GL (Fin n) (ZMod 2))) {M : GL (Fin n) (ZMod 2)} (hM2 : M * M = 1)
    (hM1 : M ≠ 1) (hc : ∀ g ∈ P, M * g = g * M) :
    ∃ g : GL (Fin n) (ZMod 2),
      ((g⁻¹ * M * g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMP : M ∈ P := by
    have hord : orderOf M = 2 := orderOf_eq_prime (by rw [pow_two]; exact hM2) hM1
    have h2 : IsPGroup 2 (Subgroup.zpowers M) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    have hN : M ∈ Subgroup.normalizer (P : Set (GL (Fin n) (ZMod 2))) := by
      refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
      · have : M * h * M⁻¹ = h := by rw [hc h hh, mul_assoc, mul_inv_cancel, mul_one]
        rwa [this]
      · have h' := hc _ hh
        have : h = M * h * M⁻¹ := by
          calc h = M⁻¹ * (M * h * M⁻¹ * M) := by group
            _ = M⁻¹ * (M * (M * h * M⁻¹)) := by rw [h']
            _ = M * h * M⁻¹ := by group
        rwa [this]
    have hm : M ∈ Subgroup.zpowers M ⊓ Subgroup.normalizer (P : Set (GL (Fin n) (ZMod 2))) :=
      ⟨Subgroup.mem_zpowers M, hN⟩
    rw [h2.inf_normalizer_sylow P] at hm
    exact hm.2
  let U : Sylow 2 (GL (Fin n) (ZMod 2)) := hU.toSylow hUi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin n) (ZMod 2)) U P
  have hmem : ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ uniGL n := by
    intro x
    rw [← hg]
    show x ∈ ((g • U : Sylow 2 (GL (Fin n) (ZMod 2))) : Subgroup (GL (Fin n) (ZMod 2))) ↔ _
    rw [Sylow.coe_subgroup_smul,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
      inv_inv, IsPGroup.toSylow_coe]
  refine ⟨g, hZ _ ((hmem M).mp hMP) (fun u hu => ?_) fun h => hM1 ?_⟩
  · have hgu : g * u * g⁻¹ ∈ P := (hmem _).mpr (by simpa [mul_assoc] using hu)
    have h1 := hc _ hgu
    calc g⁻¹ * M * g * u = g⁻¹ * (M * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * M) * g := by rw [h1]
      _ = u * (g⁻¹ * M * g) := by group
  · calc M = g * (g⁻¹ * M * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group

theorem card_fix_of_conj {M g : GL (Fin n) (ZMod 2)} {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : ((g⁻¹ * M * g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = t) :
    Nat.card {x : Fin n → ZMod 2 // (M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x} =
      Nat.card {x : Fin n → ZMod 2 // t *ᵥ x = x} := by
  set m := g⁻¹ * M * g with hm_def
  rw [← hg]
  have hMm : (M : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * (m : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← Units.val_mul, ← Units.val_mul, hm_def]
    congr 1
    group
  have hgg : ∀ x, (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgg' : ∀ x, ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  refine Nat.card_congr
    { toFun := fun x => ⟨((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x.1, ?_⟩
      invFun := fun y => ⟨(g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y.1, ?_⟩
      left_inv := fun x => Subtype.ext (hgg x.1)
      right_inv := fun y => Subtype.ext (hgg' y.1) }
  · obtain ⟨x, hx⟩ := x
    show (m : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
        ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x
    rw [hMm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hx
    have := congrArg
      (fun z => ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) hx
    simpa only [hgg'] using this
  · obtain ⟨y, hy⟩ := y
    show (M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y
    rw [hMm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg', hy]

theorem card_fix_of_comm_sylow [NeZero n] (hU : IsPGroup 2 (uniGL n))
    (hUi : ¬ 2 ∣ (uniGL n).index) {t : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hZ : ∀ m ∈ uniGL n, (∀ u ∈ uniGL n, m * u = u * m) → m ≠ 1 →
      (m : Matrix (Fin n) (Fin n) (ZMod 2)) = t)
    (P : Sylow 2 (GL (Fin n) (ZMod 2))) {M : GL (Fin n) (ZMod 2)} (hM2 : M * M = 1)
    (hM1 : M ≠ 1) (hc : ∀ g ∈ P, M * g = g * M) :
    Nat.card {x : Fin n → ZMod 2 // (M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x} =
      Nat.card {x : Fin n → ZMod 2 // t *ᵥ x = x} := by
  obtain ⟨g, hg⟩ := exists_conj_of_comm_sylow hU hUi hZ P hM2 hM1 hc
  exact card_fix_of_conj hg

end Uni

section Five

@[expose] def mk5 (p : Fin 10 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, p 0, p 1, p 2, p 3; 0, 1, p 4, p 5, p 6; 0, 0, 1, p 7, p 8; 0, 0, 0, 1, p 9;
    0, 0, 0, 0, 1]

@[expose] def ext5 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Fin 10 → ZMod 2 :=
  ![M 0 1, M 0 2, M 0 3, M 0 4, M 1 2, M 1 3, M 1 4, M 2 3, M 2 4, M 3 4]

theorem isUni_mk5 (p : Fin 10 → ZMod 2) : IsUni (mk5 p) := by
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

theorem ext5_mk5 (p : Fin 10 → ZMod 2) : ext5 (mk5 p) = p := by
  funext k
  fin_cases k <;> rfl

theorem mk5_ext5 {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hM : IsUni M) : mk5 (ext5 M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (hM.1 _).symm | exact (hM.2 _ _ (by decide)).symm

@[expose] def t5 : Matrix (Fin 5) (Fin 5) (ZMod 2) := mk5 (Pi.single 3 1)

@[expose] def T5 : Fin 4 → Fin 10 → ZMod 2 :=
  ![Pi.single 0 1, Pi.single 4 1, Pi.single 7 1, Pi.single 9 1]

theorem center5 : ∀ p : Fin 10 → ZMod 2, (∀ i : Fin 4, mk5 p * mk5 (T5 i) = mk5 (T5 i) * mk5 p) →
    mk5 p = 1 ∨ mk5 p = t5 := by
  decide +kernel

theorem card_fix_t5 : Nat.card {x : Fin 5 → ZMod 2 // t5 *ᵥ x = x} = 2 ^ 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_uniGL5 : Nat.card (uniGL 5) = 2 ^ 10 := by
  have e : ↥(uniGL 5) ≃ (Fin 10 → ZMod 2) :=
    { toFun := fun g => ext5 ((g : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      invFun := fun p => ⟨uniUnit (isUni_mk5 p), isUni_mk5 p⟩
      left_inv := fun g => Subtype.ext (Units.ext (mk5_ext5 g.2))
      right_inv := fun p => ext5_mk5 p }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_GL5 : Nat.card (GL (Fin 5) (ZMod 2)) = 9999360 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  norm_num

theorem uniGL5_isPGroup : IsPGroup 2 (uniGL 5) := IsPGroup.of_card card_uniGL5

theorem uniGL5_index : ¬ 2 ∣ (uniGL 5).index := by
  have h := (uniGL 5).card_mul_index
  rw [card_uniGL5, card_GL5] at h
  have : (uniGL 5).index = 9765 := by omega
  rw [this]
  decide

theorem uniGL5_center (m : GL (Fin 5) (ZMod 2)) (hm : m ∈ uniGL 5)
    (hc : ∀ u ∈ uniGL 5, m * u = u * m) (h1 : m ≠ 1) :
    (m : Matrix (Fin 5) (Fin 5) (ZMod 2)) = t5 := by
  have hmk := mk5_ext5 (mem_uniGL.mp hm)
  set p := ext5 ((m : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
  have hcomm : ∀ i : Fin 4, mk5 p * mk5 (T5 i) = mk5 (T5 i) * mk5 p := by
    intro i
    have := congrArg (fun g : GL (Fin 5) (ZMod 2) => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)))
      (hc (uniUnit (isUni_mk5 (T5 i))) (isUni_mk5 (T5 i)))
    simp only [Units.val_mul, coe_uniUnit] at this
    rw [hmk]
    exact this
  rcases center5 p hcomm with h | h
  · exact absurd (Units.ext (hmk.symm.trans h)) h1
  · exact hmk.symm.trans h

end Five

section Four

@[expose] def mk4 (p : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, p 0, p 1, p 2; 0, 1, p 3, p 4; 0, 0, 1, p 5; 0, 0, 0, 1]

@[expose] def ext4 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Fin 6 → ZMod 2 :=
  ![M 0 1, M 0 2, M 0 3, M 1 2, M 1 3, M 2 3]

theorem isUni_mk4 (p : Fin 6 → ZMod 2) : IsUni (mk4 p) := by
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · fin_cases i <;> rfl
  · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

theorem ext4_mk4 (p : Fin 6 → ZMod 2) : ext4 (mk4 p) = p := by
  funext k
  fin_cases k <;> rfl

theorem mk4_ext4 {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : IsUni M) : mk4 (ext4 M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (hM.1 _).symm | exact (hM.2 _ _ (by decide)).symm

@[expose] def t4 : Matrix (Fin 4) (Fin 4) (ZMod 2) := mk4 (Pi.single 2 1)

@[expose] def T4 : Fin 3 → Fin 6 → ZMod 2 := ![Pi.single 0 1, Pi.single 3 1, Pi.single 5 1]

theorem center4 : ∀ p : Fin 6 → ZMod 2, (∀ i : Fin 3, mk4 p * mk4 (T4 i) = mk4 (T4 i) * mk4 p) →
    mk4 p = 1 ∨ mk4 p = t4 := by
  decide +kernel

theorem card_fix_t4 : Nat.card {x : Fin 4 → ZMod 2 // t4 *ᵥ x = x} = 2 ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_uniGL4 : Nat.card (uniGL 4) = 2 ^ 6 := by
  have e : ↥(uniGL 4) ≃ (Fin 6 → ZMod 2) :=
    { toFun := fun g => ext4 ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
      invFun := fun p => ⟨uniUnit (isUni_mk4 p), isUni_mk4 p⟩
      left_inv := fun g => Subtype.ext (Units.ext (mk4_ext4 g.2))
      right_inv := fun p => ext4_mk4 p }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_GL4 : Nat.card (GL (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem uniGL4_isPGroup : IsPGroup 2 (uniGL 4) := IsPGroup.of_card card_uniGL4

theorem uniGL4_index : ¬ 2 ∣ (uniGL 4).index := by
  have h := (uniGL 4).card_mul_index
  rw [card_uniGL4, card_GL4] at h
  have : (uniGL 4).index = 315 := by omega
  rw [this]
  decide

theorem uniGL4_center (m : GL (Fin 4) (ZMod 2)) (hm : m ∈ uniGL 4)
    (hc : ∀ u ∈ uniGL 4, m * u = u * m) (h1 : m ≠ 1) :
    (m : Matrix (Fin 4) (Fin 4) (ZMod 2)) = t4 := by
  have hmk := mk4_ext4 (mem_uniGL.mp hm)
  set p := ext4 ((m : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hcomm : ∀ i : Fin 3, mk4 p * mk4 (T4 i) = mk4 (T4 i) * mk4 p := by
    intro i
    have := congrArg (fun g : GL (Fin 4) (ZMod 2) => (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
      (hc (uniUnit (isUni_mk4 (T4 i))) (isUni_mk4 (T4 i)))
    simp only [Units.val_mul, coe_uniUnit] at this
    rw [hmk]
    exact this
  rcases center4 p hcomm with h | h
  · exact absurd (Units.ext (hmk.symm.trans h)) h1
  · exact hmk.symm.trans h

end Four

section Fact

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_fixV_zpowers_iff {c : MulAut V} {w : V} :
    w ∈ fixV (Subgroup.zpowers c) ↔ c w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem factLNatRow1321 : FactLNatRow1321 := by
  intro V _ _ hV G L v hB4 hc h9
  obtain ⟨-, n, hn, hnat, -⟩ := h9
  have hL : L = ⊤ := G64.BinaryNaturalSL.eq_top hnat
  have hcardV : Nat.card V = 2 ^ n := G64.BinaryNaturalSL.card_eq hnat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (W := V) (p := 2)
    (fun a b => mul_comm a b) hV hcardV
  set Φ := CFSG.SectionRank.Ccomm.elemAutEquivGL e with hΦ
  obtain ⟨S, hS, hSv⟩ := hc.sylow
  subst hL
  have hSp : IsPGroup 2 S := hS.2.1
  have hSi : ¬ 2 ∣ S.index := by
    have h := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h
  have hPp : IsPGroup 2 (S.map Φ.toMonoidHom) := hSp.map _
  have hPi : ¬ 2 ∣ (S.map Φ.toMonoidHom).index := by
    rwa [show Φ.toMonoidHom = (Φ : MulAut V →* GL (Fin n) (ZMod 2)) from rfl,
      Subgroup.index_map_equiv]
  let P : Sylow 2 (GL (Fin n) (ZMod 2)) := hPp.toSylow hPi
  have hM2 : Φ v * Φ v = 1 := by rw [← map_mul, hc.sq, map_one]
  have hM1 : Φ v ≠ 1 := fun h => hc.ne_one (Φ.injective (h.trans (map_one Φ).symm))
  have hcomm : ∀ g ∈ P, Φ v * g = g * Φ v := by
    intro g hg
    rw [IsPGroup.mem_toSylow] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hSv hs)
    show Φ v * Φ s = Φ s * Φ v
    rw [← map_mul, ← map_mul, h1]
  have hfix : Nat.card {x : Fin n → ZMod 2 //
      ((Φ v : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x} = 2 ^ (n - 1) := by
    rcases hn with rfl | rfl
    · rw [card_fix_of_comm_sylow uniGL4_isPGroup uniGL4_index uniGL4_center P hM2 hM1 hcomm]
      exact card_fix_t4
    · rw [card_fix_of_comm_sylow uniGL5_isPGroup uniGL5_index uniGL5_center P hM2 hM1 hcomm]
      exact card_fix_t5
  have hfixV : Nat.card (fixV (Subgroup.zpowers v)) = 2 ^ (n - 1) := by
    rw [← hfix]
    refine Nat.card_congr
      { toFun := fun w => ⟨Multiplicative.toAdd (e w), ?_⟩
        invFun := fun x => ⟨e.symm (Multiplicative.ofAdd x.1), ?_⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    · obtain ⟨w, hw⟩ := w
      show ((Φ v : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (e w) = Multiplicative.toAdd (e w)
      rw [hΦ, CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec, mem_fixV_zpowers_iff.mp hw]
    · obtain ⟨x, hx⟩ := x
      rw [mem_fixV_zpowers_iff]
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec, ← hΦ, MulEquiv.apply_symm_apply]
      exact hx
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hidx := (fixV (Subgroup.zpowers v)).card_mul_index
  rw [hfixV, hcardV] at hidx
  have h2 : (fixV (Subgroup.zpowers v)).index = 2 := by
    have h3 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hn1]
    rw [h3] at hidx
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hidx
  unfold rkIdx
  rw [h2]
  simp

end Fact

end CFSG.Quasithin.H13.A5

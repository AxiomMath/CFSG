module

public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.Open

instance s1422FactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem center_sl_two_gf2 (f : ℕ) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hchar : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hchar
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  subst h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz]
  simp

private theorem s1422_nat_aux (q : ℕ) (hq : 2 ≤ q) :
    (q ^ 2 - 1) * (q ^ 2 - q) / (q - 1) = q * (q ^ 2 - 1) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    zify [h1, h2, (by omega : 1 ≤ q)]
    ring
  exact Nat.div_eq_of_eq_mul_left (by omega) h3

theorem card_sl_two_gf2 (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = 2 ^ f * (4 ^ f - 1) := by
  classical
  let _ : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 f (by omega)
  rw [Matrix.card_SL_field 2, hq]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [s1422_nat_aux _ h2f]
  have : (4 : ℕ) ^ f = (2 ^ f) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]

noncomputable def pslTwoGf2EquivSl (f : ℕ) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) :=
  (QuotientGroup.quotientMulEquivOfEq (center_sl_two_gf2 f)).trans QuotientGroup.quotientBot

theorem card_psl_two_gf2 (f : ℕ) (hf : 1 ≤ f) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) =
      2 ^ f * (4 ^ f - 1) :=
  (Nat.card_congr (pslTwoGf2EquivSl f).toEquiv).trans (card_sl_two_gf2 f hf)

theorem IsL2Quot.card {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X] (h : IsL2Quot f X) :
    Nat.card X = 2 ^ f * (4 ^ f - 1) := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans (card_psl_two_gf2 f hf)

theorem two_pow_mul_four_pow_sub_one_ge (f : ℕ) (hf : 2 ≤ f) : 60 ≤ 2 ^ f * (4 ^ f - 1) := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h16 : 16 ≤ 4 ^ f := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  calc 60 = 4 * 15 := by norm_num
    _ ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h4 (by omega)

theorem IsL2Quot.eq_one_of_card_lt {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X] (h : IsL2Quot f X)
    (hX : Nat.card X < 60) : f = 1 := by
  by_contra hne
  have := two_pow_mul_four_pow_sub_one_ge f (by omega)
  have := h.card hf
  omega

theorem IsL2Quot.eq_one_of_card_eq_six {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X]
    (h : IsL2Quot f X) (hX : Nat.card X = 6) : f = 1 :=
  h.eq_one_of_card_lt hf (by omega)

theorem card_psl_two_gf2_one :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  rw [card_psl_two_gf2 1 le_rfl]
  norm_num

@[expose] noncomputable def slNonzeroPerm (F : Type) [Field F] :
    SL(2, F) →* Equiv.Perm {v : Fin 2 → F // v ≠ 0} where
  toFun A := Equiv.Perm.subtypePerm (MulAction.toPermHom SL(2, F) (Fin 2 → F) A) (by
    intro v
    simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, ne_eq]
    constructor
    · intro h h0
      apply h
      rw [h0, smul_zero]
    · intro h h0
      apply h
      have := congrArg (fun w => A⁻¹ • w) h0
      simpa [smul_smul] using this)
  map_one' := by
    ext v
    simp
  map_mul' A B := by
    ext v : 1
    apply Subtype.ext
    change (A * B) • (v : Fin 2 → F) = A • B • (v : Fin 2 → F)
    rw [mul_smul]

theorem slNonzeroPerm_apply (F : Type) [Field F] (A : SL(2, F))
    (v : {v : Fin 2 → F // v ≠ 0}) :
    ((slNonzeroPerm F A v : {v : Fin 2 → F // v ≠ 0}) : Fin 2 → F) = A • (v : Fin 2 → F) := rfl

theorem slNonzeroPerm_injective (F : Type) [Field F] : Function.Injective (slNonzeroPerm F) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have key : ∀ v : Fin 2 → F, v ≠ 0 → A • v = v := by
    intro v hv
    have := congrArg (fun σ : Equiv.Perm {v : Fin 2 → F // v ≠ 0} => (σ ⟨v, hv⟩ : Fin 2 → F)) hA
    simpa [slNonzeroPerm_apply] using this
  have e0 := key (Pi.single 0 1) (by
    intro h; have := congrFun h 0; simp at this)
  have e1 := key (Pi.single 1 1) (by
    intro h; have := congrFun h 1; simp at this)
  rw [Matrix.SpecialLinearGroup.smul_def] at e0 e1
  have a00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using congrFun e0 0
  have a10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using congrFun e0 1
  have a01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simpa using congrFun e1 0
  have a11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by simpa using congrFun e1 1
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a10, a01, a11]

theorem card_gf2_one : Nat.card (GaloisField 2 1) = 2 := by
  simpa using GaloisField.card 2 1 one_ne_zero

theorem card_nonzero_vectors_gf2 :
    Nat.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} = 3 := by
  classical
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact card_gf2_one
  rw [Nat.card_eq_fintype_card]
  have h1 : Fintype.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} =
      Fintype.card (Fin 2 → GaloisField 2 1) - Fintype.card {v : Fin 2 → GaloisField 2 1 // v = 0} :=
    Fintype.card_subtype_compl (fun v : Fin 2 → GaloisField 2 1 => v = 0)
  rw [h1, Fintype.card_subtype_eq, Fintype.card_fun, hq, Fintype.card_fin]
  norm_num

noncomputable def slTwoEquivPermThree : SL(2, GaloisField 2 1) ≃* Equiv.Perm (Fin 3) := by
  classical
  have hcardN : Nat.card {v : Fin 2 → GaloisField 2 1 // v ≠ 0} = 3 := card_nonzero_vectors_gf2
  have hbij : Function.Bijective (slNonzeroPerm (GaloisField 2 1)) := by
    refine ⟨slNonzeroPerm_injective _, ?_⟩
    have : Finite (Equiv.Perm {v : Fin 2 → GaloisField 2 1 // v ≠ 0}) := inferInstance
    have h1 : Nat.card (Equiv.Perm {v : Fin 2 → GaloisField 2 1 // v ≠ 0}) = 6 := by
      rw [Nat.card_perm, hcardN]; rfl
    have h2 : Nat.card (SL(2, GaloisField 2 1)) = 6 := by
      rw [card_sl_two_gf2 1 le_rfl]
      norm_num
    exact (Function.Injective.bijective_of_nat_card_le (slNonzeroPerm_injective _)
      (by rw [h1, h2])).2
  exact (MulEquiv.ofBijective (slNonzeroPerm (GaloisField 2 1)) hbij).trans
    (Equiv.permCongrHom ((Finite.equivFin _).trans (finCongr hcardN)))

noncomputable def permThreeEquivPSL :
    Equiv.Perm (Fin 3) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1) :=
  slTwoEquivPermThree.symm.trans (pslTwoGf2EquivSl 1).symm

theorem isL2Quot_one_perm_three : IsL2Quot 1 (Equiv.Perm (Fin 3)) := ⟨permThreeEquivPSL⟩

theorem IsL2Quot.of_perm_three {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    IsL2Quot 1 X := ⟨e.trans permThreeEquivPSL⟩

theorem IsL2Quot.perm_three {X : Type*} [Group X] (h : IsL2Quot 1 X) :
    Nonempty (X ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans permThreeEquivPSL.symm⟩

theorem isRankOneListed_perm_three {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 3)) :
    IsRankOneListed X :=
  Or.inl ⟨1, le_rfl, ⟨e.trans permThreeEquivPSL⟩⟩

end CFSG.Quasithin

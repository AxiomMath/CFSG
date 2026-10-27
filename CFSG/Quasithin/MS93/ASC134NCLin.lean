module

public import CFSG.Quasithin.MS93.ML3Facts

public section

namespace CFSG.Quasithin.MS93

open Matrix
open scoped Pointwise

variable {F : Type} [Field F]

theorem sl3_mulVec_mul (g h : SL3 F) (v : Fin 3 → F) :
    ((g * h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
  change ((g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = _
  rw [Matrix.mulVec_mulVec]

theorem sl3_one_mulVec (v : Fin 3 → F) : ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v :=
  Matrix.one_mulVec v

@[expose] def lnStab : Subgroup (SL3 F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0}
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    change ((g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F)) 2 0 = 0 ∧
      ((g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F)) 2 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hh0, hh1]
  one_mem' := by
    change (1 : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (1 : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
    simp
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    change (Matrix.adjugate (g : Matrix (Fin 3) (Fin 3) F)) 2 0 = 0 ∧
      (Matrix.adjugate (g : Matrix (Fin 3) (Fin 3) F)) 2 1 = 0
    rw [Matrix.adjugate_fin_three]
    simp [hg0, hg1]

theorem mem_lnStab_iff {g : SL3 F} :
    g ∈ lnStab ↔ ∀ x ∈ (ln01 : Submodule F (Fin 3 → F)),
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ ln01 := by
  constructor
  · rintro ⟨h0, h1⟩ x hx
    rw [mem_ln01] at hx ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0, h1, hx]
  · intro h
    have e0 := h (Pi.single 0 1) (by simp [mem_ln01])
    have e1 := h (Pi.single 1 1) (by simp [mem_ln01])
    rw [mem_ln01] at e0 e1
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e0 e1
    exact ⟨e0, e1⟩

theorem mem_qLn_iff_fix {g : SL3 F} :
    g ∈ qLn ↔ ∀ x ∈ (ln01 : Submodule F (Fin 3 → F)),
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  constructor
  · intro hg x hx
    rw [← fixN_qLn] at hx
    exact hx g hg
  · intro h
    have e0 := h (Pi.single 0 1) (by simp [mem_ln01])
    have e1 := h (Pi.single 1 1) (by simp [mem_ln01])
    have c00 := congrFun e0 0
    have c10 := congrFun e0 1
    have c20 := congrFun e0 2
    have c01 := congrFun e1 0
    have c11 := congrFun e1 1
    have c21 := congrFun e1 2
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at c00 c10 c20
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at c01 c11 c21
    have hdet : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := g.2
    rw [Matrix.det_fin_three] at hdet
    simp [c00, c10, c20, c01, c11, c21] at hdet
    rw [mem_qLn_iff]
    refine ⟨(g : Matrix (Fin 3) (Fin 3) F) 0 2, (g : Matrix (Fin 3) (Fin 3) F) 1 2, ?_⟩
    rw [rootElt02_eq_uniTri, rootElt12_eq_uniTri, uniTri_mul]
    apply Subtype.ext
    change ((uniTri _ _ _ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [coe_uniTri]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c00, c10, c20, c01, c11, c21, hdet]

theorem qLn_le_lnStab : (qLn : Subgroup (SL3 F)) ≤ lnStab := fun g hg =>
  mem_lnStab_iff.mpr fun x hx => by rw [mem_qLn_iff_fix.mp hg x hx]; exact hx

theorem conj_mem_qLn {h g : SL3 F} (hh : h ∈ lnStab) (hg : g ∈ qLn) : h * g * h⁻¹ ∈ qLn := by
  rw [mem_qLn_iff_fix] at hg ⊢
  intro x hx
  have hx' : ((h⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ ln01 :=
    mem_lnStab_iff.mp (lnStab.inv_mem hh) x hx
  rw [sl3_mulVec_mul, sl3_mulVec_mul, hg _ hx', ← sl3_mulVec_mul, mul_inv_cancel, sl3_one_mulVec]

theorem rootElt_two_one_not_mem_lnStab : rootElt 2 1 (1 : F) ∉ lnStab := by
  rintro ⟨-, h⟩
  rw [coe_rootElt (by decide)] at h
  simp at h

theorem rootElt_two_one_mulVec {c : F} {x : Fin 3 → F}
    (hx : x ∈ (pt0 : Submodule F (Fin 3 → F))) :
    ((rootElt 2 1 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x := by
  rw [coe_rootElt (by decide), Matrix.add_mulVec, Matrix.one_mulVec]
  have h1 : x 1 = 0 := hx.1
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h1]

theorem rootElt_one_two_mem_qLn (c : F) : rootElt 1 2 c ∈ (qLn : Subgroup (SL3 F)) :=
  mem_qLn_iff.mpr ⟨0, c, by rw [rootElt_zero, one_mul]⟩

theorem coe_threeElt [CharP F 2] :
    ((rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 1; 0, 1, 0] := by
  have hinv : (rootElt 2 1 (1 : F))⁻¹ = rootElt 2 1 1 := by rw [← rootElt_neg, CharTwo.neg_eq]
  rw [hinv]
  change ((rootElt 1 2 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
      (((rootElt 2 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
        ((rootElt 1 2 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *
        ((rootElt 2 1 (1 : F) : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = _
  rw [coe_rootElt (by decide), coe_rootElt (by decide)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

theorem threeElt_pow_three [CharP F 2] :
    (rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹)) ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  apply Subtype.ext
  change ((rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) *
    ((rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) *
    ((rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹) : SL3 F) :
      Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_threeElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem threeElt_ne_one [CharP F 2] :
    rootElt 1 2 (1 : F) * (rootElt 2 1 1 * rootElt 1 2 1 * (rootElt 2 1 1)⁻¹) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL3 F => (g : Matrix (Fin 3) (Fin 3) F) 1 2) h
  simp only [coe_threeElt] at this
  simp at this

theorem eq_one_of_pow_two_pow_of_pow_three {H : Type*} [Monoid H] {x : H} {k : ℕ}
    (h1 : x ^ 2 ^ k = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  have hd1 := orderOf_dvd_of_pow_eq_one h1
  have hd3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd3))

theorem charP_two_of_card_eq [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  have hn : n ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := F)
    rw [hF] at this
    simp at this
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, hF]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp [pow_succ]

theorem isPGroup_qLn [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsPGroup 2 (qLn : Subgroup (SL3 F)) :=
  (isPGroup_sStar hF).to_le qLn_le_sStar

theorem exists_map_conj_eq_sStar [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {U : Subgroup (SL3 F)} (hU : IsPGroup 2 U) (hodd : ¬ 2 ∣ U.index) :
    ∃ γ : SL3 F, U.map (MulAut.conj γ).toMonoidHom = sStar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (SL3 F) (hU.toSylow hodd)
    ((isPGroup_sStar hF).toSylow (not_two_dvd_index_sStar hF))
  refine ⟨γ, ?_⟩
  have := congrArg (fun P : Sylow 2 (SL3 F) => (P : Subgroup (SL3 F))) hγ
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [Subgroup.pointwise_smul_def] at this
  exact this

theorem card_pt0 [Finite F] : Nat.card (pt0 : Submodule F (Fin 3 → F)) = Nat.card F := by
  let e : F ≃ (pt0 : Submodule F (Fin 3 → F)) :=
    { toFun := fun c => ⟨![c, 0, 0], ⟨rfl, rfl⟩⟩
      invFun := fun x => (x : Fin 3 → F) 0
      left_inv := fun c => rfl
      right_inv := fun x => by
        apply Subtype.ext
        funext k
        fin_cases k
        · rfl
        · exact x.2.1.symm
        · exact x.2.2.symm }
  rw [← Nat.card_congr e]

theorem card_top_vec [Finite F] :
    Nat.card (⊤ : Submodule F (Fin 3 → F)) = Nat.card F ^ 3 := by
  rw [Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule F (Fin 3 → F)) ≃ₗ[F] _).toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end CFSG.Quasithin.MS93

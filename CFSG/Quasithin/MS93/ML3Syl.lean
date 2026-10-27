module

public import CFSG.Quasithin.MS93.ML3Basic

public section

namespace CFSG.Quasithin.MS93

open Matrix

variable {F : Type} [Field F]

@[expose] def uniTri (a b c : F) : SL3 F :=
  ⟨!![1, a, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uniTri (a b c : F) :
    ((uniTri a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, a, b; 0, 1, c; 0, 0, 1] :=
  rfl

theorem uniTri_mul (a b c a' b' c' : F) :
    uniTri a b c * uniTri a' b' c' = uniTri (a + a') (b + a * c' + b') (c + c') := by
  apply Subtype.ext
  change ((uniTri a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((uniTri a' b' c' : SL3 F) :
      Matrix _ _ F) = ((uniTri (a + a') (b + a * c' + b') (c + c') : SL3 F) : Matrix _ _ F)
  rw [coe_uniTri, coe_uniTri, coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uniTri_zero : uniTri (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  change ((uniTri (0 : F) 0 0 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem uniTri_inv (a b c : F) : (uniTri a b c)⁻¹ = uniTri (-a) (a * c - b) (-c) := by
  rw [inv_eq_iff_mul_eq_one, uniTri_mul, uniTri_zero.symm]
  congr 1 <;> ring

theorem rootElt01_eq_uniTri (a : F) : rootElt 0 1 a = uniTri a 0 0 := by
  apply Subtype.ext
  change ((rootElt 0 1 a : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((uniTri a 0 0 : SL3 F) :
    Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rootElt02_eq_uniTri (b : F) : rootElt 0 2 b = uniTri 0 b 0 := by
  apply Subtype.ext
  change ((rootElt 0 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((uniTri 0 b 0 : SL3 F) :
    Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem rootElt12_eq_uniTri (c : F) : rootElt 1 2 c = uniTri 0 0 c := by
  apply Subtype.ext
  change ((rootElt 1 2 c : SL3 F) : Matrix (Fin 3) (Fin 3) F) = ((uniTri 0 0 c : SL3 F) :
    Matrix _ _ F)
  rw [coe_rootElt (by decide), coe_uniTri]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uniTri_eq_prod (a b c : F) :
    uniTri a b c = rootElt 0 1 a * rootElt 0 2 (b - a * c) * rootElt 1 2 c := by
  rw [rootElt01_eq_uniTri, rootElt02_eq_uniTri, rootElt12_eq_uniTri, uniTri_mul, uniTri_mul]
  congr 1 <;> ring

theorem mem_sStar_iff {g : SL3 F} : g ∈ sStar ↔ ∃ a b c : F, uniTri a b c = g := by
  let U : Subgroup (SL3 F) :=
    { carrier := {g | ∃ a b c : F, uniTri a b c = g}
      mul_mem' := by
        rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
        exact ⟨_, _, _, (uniTri_mul a b c a' b' c').symm⟩
      one_mem' := ⟨0, 0, 0, uniTri_zero⟩
      inv_mem' := by
        rintro _ ⟨a, b, c, rfl⟩
        exact ⟨_, _, _, (uniTri_inv a b c).symm⟩ }
  constructor
  · intro hg
    have hle : (sStar : Subgroup (SL3 F)) ≤ U := by
      rw [sStar]
      refine sup_le (sup_le ?_ ?_) ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨a, 0, 0, (rootElt01_eq_uniTri a).symm⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨0, b, 0, (rootElt02_eq_uniTri b).symm⟩
      · rintro _ ⟨c, rfl⟩
        exact ⟨0, 0, c, (rootElt12_eq_uniTri c).symm⟩
    exact hle hg
  · rintro ⟨a, b, c, rfl⟩
    rw [uniTri_eq_prod, sStar]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (rootElt_mem_rootGroup _ _ _)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (rootElt_mem_rootGroup _ _ _))))
      (Subgroup.mem_sup_right (rootElt_mem_rootGroup _ _ _))

theorem uniTri_injective : Function.Injective fun p : F × F × F => uniTri p.1 p.2.1 p.2.2 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' := congrArg (fun g : SL3 F => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_uniTri] at h'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  have h3 := congrFun (congrFun h' 1) 2
  simp at h1 h2 h3
  rw [h1, h2, h3]

theorem card_sStar [Finite F] : Nat.card (sStar : Subgroup (SL3 F)) = Nat.card F ^ 3 := by
  have e : F × F × F ≃ (sStar : Subgroup (SL3 F)) :=
    Equiv.ofBijective (fun p => ⟨uniTri p.1 p.2.1 p.2.2, mem_sStar_iff.mpr ⟨_, _, _, rfl⟩⟩)
      ⟨fun p p' h => uniTri_injective (congrArg Subtype.val h), by
        rintro ⟨g, hg⟩
        obtain ⟨a, b, c, rfl⟩ := mem_sStar_iff.mp hg
        exact ⟨(a, b, c), rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_prod]
  ring

theorem card_SL3 [Finite F] :
    Nat.card (SL3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
  set q := Nat.card F with hq
  have hq2 : 1 < q := Finite.one_lt_card
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  rw [e1, e2]
  have hq1 : 0 < q - 1 := by omega
  rw [show (q ^ 3 - 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
      q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) by ring, Nat.mul_div_cancel _ hq1]

theorem index_sStar [Finite F] :
    (sStar : Subgroup (SL3 F)).index = (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  have h := (sStar : Subgroup (SL3 F)).index_mul_card
  rw [card_sStar, card_SL3, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 3) h

theorem not_two_dvd_index_sStar [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    ¬ 2 ∣ (sStar : Subgroup (SL3 F)).index := by
  rw [index_sStar, hF]
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : (1 : ℕ) < Nat.card F := Finite.one_lt_card
      rw [hF] at this
      simp at this
    · exact h
  have hodd : ∀ k, 1 ≤ k → Odd ((2 ^ n) ^ k - 1) := fun k hk => by
    rw [← pow_mul]
    have hnk : n * k ≠ 0 := by positivity
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, hnk⟩) odd_one
  rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact Nat.odd_mul.mpr ⟨hodd 3 (by norm_num), hodd 2 (by norm_num)⟩

theorem isPGroup_sStar [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    IsPGroup 2 (sStar : Subgroup (SL3 F)) :=
  IsPGroup.of_card (n := 3 * n) (by rw [card_sStar, hF, ← pow_mul, mul_comm])

end CFSG.Quasithin.MS93

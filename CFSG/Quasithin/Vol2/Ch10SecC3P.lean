module

public import CFSG.Quasithin.Vol2.Ch10SecC3O

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] [Finite K]

omit [CharP K 2] in
theorem card_SL : Nat.card (SL K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have hpos : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have h1 : Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (Nat.card K ^ 2 - 1) * (Nat.card K * (Nat.card K - 1)) =
    Nat.card K * (Nat.card K ^ 2 - 1) * (Nat.card K - 1) by ring, Nat.mul_div_cancel _ hpos]

theorem two_dvd_card : 2 ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card] at h
  exact (CharP.cast_eq_zero_iff K 2 _).mp h

theorem card_le_of_sq_eq_one {P : Subgroup (SL K)} (h2 : ∀ x ∈ P, x * x = 1) :
    Nat.card P ≤ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (h2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hdvd : Nat.card P ∣ Nat.card (SL K) := Subgroup.card_subgroup_dvd_card P
  rw [card_SL, hk] at hdvd
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    have hq := two_dvd_card (K := K)
    have hq1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have he : Even (Nat.card K ^ 2) :=
      (Nat.even_pow' (by norm_num)).mpr (even_iff_two_dvd.mpr hq)
    exact Nat.Even.sub_odd hq1 he odd_one
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  rw [hk]
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)

@[expose] def fixMat (B : Subgroup (MulAut (WM K))) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {X | Multiplicative.ofAdd X ∈ fixV B}

omit [CharP K 2] [Finite K] in
theorem card_fixMat (B : Subgroup (MulAut (WM K))) :
    Nat.card (fixMat B) = Nat.card ↥(fixV B) :=
  Nat.card_congr
    { toFun := fun X => ⟨Multiplicative.ofAdd X.1, X.2⟩
      invFun := fun v => ⟨Multiplicative.toAdd v.1, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [CharP K 2] [Finite K] in
theorem sub_mem_fixMat {B : Subgroup (MulAut (WM K))} {X Y : Matrix (Fin 2) (Fin 2) K}
    (hX : X ∈ fixMat B) (hY : Y ∈ fixMat B) : X - Y ∈ fixMat B := by
  have h := (fixV B).div_mem hX hY
  exact h

omit [CharP K 2] [Finite K] in
theorem fix_of_mem_fixMat {B : Subgroup (MulAut (WM K))} {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X ∈ fixMat B) {g : SL K × SL K} (hg : rho K g ∈ B) :
    (g.1 : Matrix (Fin 2) (Fin 2) K) * X * (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
  have h := congrArg Multiplicative.toAdd (hX _ hg)
  rw [toAdd_rho] at h
  exact h

theorem card_fixV_le_sq_left {B : Subgroup (MulAut (WM K))} {c d : SL K}
    (hB : rho K (c, d) ∈ B) (hc : c ≠ 1) (hd : d * d = 1) :
    Nat.card ↥(fixV B) ≤ Nat.card K ^ 2 := by
  rw [← card_fixMat]
  exact card_fixSet_le hc hd _ (fun X hX => fix_of_mem_fixMat hX hB)
    (fun X hX Y hY => sub_mem_fixMat hX hY)

theorem card_fixV_le_sq_right {B : Subgroup (MulAut (WM K))} {c d : SL K}
    (hB : rho K (c, d) ∈ B) (hd : d ≠ 1) (hc : c * c = 1) :
    Nat.card ↥(fixV B) ≤ Nat.card K ^ 2 := by
  rw [← card_fixMat]
  set S : Set (Matrix (Fin 2) (Fin 2) K) := {Y | Yᵀ ∈ fixMat B} with hSdef
  have hcard : Nat.card (fixMat B) = Nat.card S :=
    Nat.card_congr
      { toFun := fun X => ⟨X.1ᵀ, by
          change X.1ᵀᵀ ∈ fixMat B
          rw [Matrix.transpose_transpose]
          exact X.2⟩
        invFun := fun Y => ⟨Y.1ᵀ, Y.2⟩
        left_inv := fun X => Subtype.ext (Matrix.transpose_transpose _)
        right_inv := fun Y => Subtype.ext (Matrix.transpose_transpose _) }
  rw [hcard]
  refine card_fixSet_le hd hc S (fun Y hY => ?_) (fun X hX Y hY => ?_)
  · have h : (c : Matrix (Fin 2) (Fin 2) K) * Yᵀ * (d : Matrix (Fin 2) (Fin 2) K)ᵀ = Yᵀ :=
      fix_of_mem_fixMat (g := (c, d)) hY hB
    have h' := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
    exact h'
  · change (X - Y)ᵀ ∈ fixMat B
    rw [Matrix.transpose_sub]
    exact sub_mem_fixMat hX hY

end CFSG.Quasithin.Vol2.Ch10.C3.Om

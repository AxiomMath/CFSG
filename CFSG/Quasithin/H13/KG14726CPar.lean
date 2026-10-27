module

public import CFSG.Quasithin.H13.KG14726COrd
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Par

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem exists_prime_dvd_two_pow_sub_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ 2 ^ n - 1 := by
  have h8 : 8 ∣ 2 ^ n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 hn
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hmod : (2 ^ n - 1) % 8 = 7 := by omega
  by_contra hcon
  push Not at hcon
  have h3 : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
    intro d hd hdn
    have hd2 : d ≠ 2 := by
      rintro rfl
      omega
    by_contra hd3
    have hd4 : d ≠ 4 := by
      rintro rfl
      exact absurd hd (by decide)
    have := hd.two_le
    exact hcon d hd (by omega) hdn
  have hne : 2 ^ n - 1 ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hne h3
  have := three_pow_mod_eight (2 ^ n - 1).primeFactorsList.length
  rw [← hpow] at this
  omega

theorem exists_prime_orderOf_sl2 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ A : SpecialLinearGroup (Fin 2) F, orderOf A = p := by
  obtain ⟨p, hp, hp5, hpd⟩ := exists_prime_dvd_two_pow_sub_one (n := 2 * n) (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (SpecialLinearGroup (Fin 2) F) := by
    rw [card_specialLinear_two, hF, ← pow_mul, mul_comm n 2]
    exact Dvd.dvd.mul_left hpd _
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨p, hp, hp5, A, hA⟩

theorem exists_orderOf_mem_of_mem_map {G H : Type*} [Group G] [Group H] {W P : Subgroup G}
    (e : ↥W ≃* H) {y' : H} (hy' : y' ∈ (P.subgroupOf W).map e.toMonoidHom) :
    ∃ y ∈ P, orderOf y = orderOf y' := by
  obtain ⟨w, hw, rfl⟩ := hy'
  refine ⟨w, mem_subgroupOf.mp hw, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]

section SL2

variable {F : Type} [Field F]

@[expose] noncomputable def torusSL2 : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun a := ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩
  map_one' := Subtype.ext (by
    show !![((1 : Fˣ) : F), 0; 0, (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp)
  map_mul' a b := Subtype.ext (by
    show !![((a * b : Fˣ) : F), 0; 0, (((a * b)⁻¹ : Fˣ) : F)] =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm])

theorem torusSL2_apply (a : Fˣ) :
    ((torusSL2 a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] := rfl

theorem torusSL2_injective : Function.Injective (torusSL2 (F := F)) := by
  intro a b h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [torusSL2_apply] at this
  exact Units.ext (by simpa using this)

theorem torusSL2_mem_upperTriangular (a : Fˣ) : torusSL2 a ∈ upperTriangular 2 F := by
  intro i j hij
  rw [torusSL2_apply]
  fin_cases i <;> fin_cases j <;> simp_all

variable [Finite F] [CharP F 2]

theorem exists_prime_orderOf_mem_normalizer_sl2 {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n)
    {S : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧
      ∃ y ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 2) F)), orderOf y = p := by
  obtain ⟨g, hg⟩ := CFSG.Quasithin.QP.exists_conj_normalizer_of_isSylowTwoOf (n := 2)
    (by norm_num) hS
  obtain ⟨p, hp, hp5, hpd⟩ := exists_prime_dvd_two_pow_sub_one hn
  have : Fact p.Prime := ⟨hp⟩
  have hU : Nat.card Fˣ = 2 ^ n - 1 := by rw [Nat.card_units, hF]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [hU]; exact hpd)
  refine ⟨p, hp, hp5, MulAut.conj g (torusSL2 a), ?_, ?_⟩
  · rw [hg]
    exact ⟨torusSL2 a, torusSL2_mem_upperTriangular a, rfl⟩
  · rw [MulEquiv.orderOf_eq, orderOf_injective _ torusSL2_injective, ha]

end SL2

section SL3

variable {F : Type} [Field F]

@[expose] def lowerMatrix (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

@[expose] def upperMatrix (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem lowerMatrix_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    lowerMatrix A * lowerMatrix B = lowerMatrix (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem upperMatrix_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    upperMatrix A * upperMatrix B = upperMatrix (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem det_lowerMatrix (A : Matrix (Fin 2) (Fin 2) F) : (lowerMatrix A).det = A.det := by
  simp [lowerMatrix, Matrix.det_fin_three, Matrix.det_fin_two]

theorem det_upperMatrix (A : Matrix (Fin 2) (Fin 2) F) : (upperMatrix A).det = A.det := by
  simp [upperMatrix, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] noncomputable def sl3Lower : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F
    where
  toFun A := ⟨lowerMatrix A, by rw [det_lowerMatrix]; exact A.2⟩
  map_one' := Subtype.ext (by
    show lowerMatrix 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerMatrix])
  map_mul' A B := Subtype.ext (by
    show lowerMatrix ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      lowerMatrix (A : Matrix (Fin 2) (Fin 2) F) * lowerMatrix (B : Matrix (Fin 2) (Fin 2) F)
    rw [lowerMatrix_mul, Matrix.SpecialLinearGroup.coe_mul])

@[expose] noncomputable def sl3Upper : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F
    where
  toFun A := ⟨upperMatrix A, by rw [det_upperMatrix]; exact A.2⟩
  map_one' := Subtype.ext (by
    show upperMatrix 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperMatrix])
  map_mul' A B := Subtype.ext (by
    show upperMatrix ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      upperMatrix (A : Matrix (Fin 2) (Fin 2) F) * upperMatrix (B : Matrix (Fin 2) (Fin 2) F)
    rw [upperMatrix_mul, Matrix.SpecialLinearGroup.coe_mul])

theorem sl3Lower_apply (A : SpecialLinearGroup (Fin 2) F) :
    ((sl3Lower A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      lowerMatrix A := rfl

theorem sl3Upper_apply (A : SpecialLinearGroup (Fin 2) F) :
    ((sl3Upper A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      upperMatrix A := rfl

theorem sl3Lower_injective : Function.Injective (sl3Lower (F := F)) := by
  intro A B h
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrArg (fun X : SpecialLinearGroup (Fin 3) F =>
    (X : Matrix (Fin 3) (Fin 3) F) i.succ j.succ) h
  simp only [sl3Lower_apply] at this
  fin_cases i <;> fin_cases j <;> simpa [lowerMatrix] using this

theorem sl3Upper_injective : Function.Injective (sl3Upper (F := F)) := by
  intro A B h
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have := congrArg (fun X : SpecialLinearGroup (Fin 3) F =>
    (X : Matrix (Fin 3) (Fin 3) F) i.castSucc j.castSucc) h
  simp only [sl3Upper_apply] at this
  fin_cases i <;> fin_cases j <;> simpa [upperMatrix] using this

theorem sl3Lower_mem (A : SpecialLinearGroup (Fin 2) F) :
    sl3Lower A ∈ stabilizer (flagSpace 3 F 1) := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_stabilizer_flagSpace_of_entries ?_
  intro k l hl hk
  rw [sl3Lower_apply]
  fin_cases k <;> fin_cases l <;> simp_all [lowerMatrix]

theorem sl3Upper_mem (A : SpecialLinearGroup (Fin 2) F) :
    sl3Upper A ∈ stabilizer (flagSpace 3 F 2) := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_stabilizer_flagSpace_of_entries ?_
  intro k l hl hk
  rw [sl3Upper_apply]
  fin_cases k <;> fin_cases l <;> simp_all [upperMatrix]

variable [Finite F] [CharP F 2]

theorem exists_prime_orderOf_mem_of_isMaxParabolic2_sl3 {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) {P : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) P) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ y ∈ P, orderOf y = p := by
  obtain ⟨g, d, hd1, hd3, rfl⟩ :=
    CFSG.Quasithin.QP.exists_conj_stabilizer_of_isMaxParabolic2 (n := 3) (by norm_num) hP
  obtain ⟨p, hp, hp5, A, hA⟩ := exists_prime_orderOf_sl2 hF hn
  refine ⟨p, hp, hp5, ?_⟩
  rcases (by omega : d = 1 ∨ d = 2) with rfl | rfl
  · refine ⟨MulAut.conj g (sl3Lower A), ⟨_, sl3Lower_mem A, rfl⟩, ?_⟩
    rw [MulEquiv.orderOf_eq, orderOf_injective _ sl3Lower_injective, hA]
  · refine ⟨MulAut.conj g (sl3Upper A), ⟨_, sl3Upper_mem A, rfl⟩, ?_⟩
    rw [MulEquiv.orderOf_eq, orderOf_injective _ sl3Upper_injective, hA]

end SL3

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.Lie2Parabolic
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_orderOf_five_mem_of_isMaxParabolic2_sp4 (hF : Nat.card F = 4)
    {P : Subgroup (StatedSp 2 F)} (hP : IsMaxParabolic2 (⊤ : Subgroup (StatedSp 2 F)) P) :
    ∃ y ∈ P, orderOf y = 5 := by
  obtain ⟨S₁, hS₁, hNS₁, hcov⟩ := exists_sylow_of_isMaxParabolic2 hP
  have hS₁P : S₁ ≤ P := Subgroup.le_normalizer.trans hNS₁
  obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.NQCat.exists_conj_map_eq hS₁
    CFSG.Quasithin.F134.Sp4.isSylowTwoOf_unipotent
  have hUP : unipotent 2 F ≤ P.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono hS₁P
  have hcov' : P.map (MulAut.conj g).toMonoidHom ⋖ ⊤ := by
    rw [← Subgroup.map_top_of_surjective (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective]
    exact (apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))).mpr hcov
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, P.map (MulAut.conj g).toMonoidHom = Q2 F j := by
    have hle : ∃ j : Fin 2, P.map (MulAut.conj g).toMonoidHom ≤ Q2 F j := by
      rcases contained_in_Q2 hUP hcov'.lt.ne with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨j, hj⟩ := hle
    refine ⟨j, ?_⟩
    rcases hcov'.eq_or_eq hj le_top with h | h
    · exact h.symm
    · exact absurd h (CFSG.Quasithin.H13.Ch4.Sp4M.Q2_ne_top j)
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    exact ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨A, hA⟩ := exists_prime_orderOf_dvd_card' (G := SpecialLinearGroup (Fin 2) F) 5
    (by rw [card_specialLinear_two, hF]; norm_num)
  have hz : spLevi j A ∈ P.map (MulAut.conj g).toMonoidHom := hj ▸ spLevi_mem j A
  have hz5 : orderOf (spLevi j A) = 5 := by
    have h5 : spLevi j A ^ 5 = 1 := by rw [← map_pow, ← hA, pow_orderOf_eq_one, map_one]
    have hne : spLevi j A ≠ 1 := by
      intro h1
      have h2 := blkN_spLevi hK4 j A
      have h3 : (⟨spLevi j A, spLevi_mem_perfectCore hK4 j A⟩ : ↥(perfectCore (Q2 F j))) = 1 :=
        Subtype.ext h1
      rw [h3, map_one] at h2
      rw [← h2, orderOf_one] at hA
      norm_num at hA
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ (orderOf_dvd_of_pow_eq_one h5)) with
      h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  obtain ⟨y, hyP, hyz⟩ := hz
  refine ⟨y, hyP, ?_⟩
  rw [← hz5, ← hyz, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]

end Sp4

end CFSG.Quasithin.H13.KG14726

end

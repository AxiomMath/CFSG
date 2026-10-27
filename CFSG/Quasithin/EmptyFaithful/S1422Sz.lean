module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open scoped MatrixGroups

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def szList : List (Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  [!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
   !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 1],
   !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0; 1, 1, 1, 1],
   !![0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 1, 1; 1, 1, 0, 1],
   !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
   !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 1, 0, 1],
   !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 1],
   !![1, 0, 0, 0; 1, 1, 0, 0; 1, 1, 1, 0; 1, 0, 1, 1],
   !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1],
   !![1, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1],
   !![1, 0, 1, 1; 1, 1, 1, 0; 0, 1, 1, 1; 1, 1, 0, 1],
   !![1, 0, 1, 1; 1, 1, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0],
   !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1],
   !![1, 1, 0, 1; 0, 1, 1, 1; 1, 1, 1, 0; 1, 0, 1, 1],
   !![1, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
   !![1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1; 1, 1, 1, 1],
   !![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1],
   !![1, 1, 1, 1; 0, 1, 1, 0; 1, 1, 0, 0; 1, 0, 0, 0],
   !![1, 1, 1, 1; 1, 0, 0, 1; 0, 1, 0, 1; 1, 0, 1, 1],
   !![1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 1, 0; 1, 1, 0, 1]]

theorem szList_length : szList.length = 20 := by decide +kernel

theorem szList_nodup : szList.Nodup := by decide +kernel

theorem szList_one : (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList := by decide +kernel

theorem szList_mul : ∀ x ∈ szList, ∀ y ∈ szList, x * y ∈ szList := by
  intro x hx y hy
  simp only [szList, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  decide +kernel

@[expose] def szMon : Submonoid (GL (Fin 4) (ZMod 2)) where
  carrier := {A | (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList}
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList
    rw [Units.val_mul]
    exact szList_mul _ ha _ hb
  one_mem' := by
    show ((1 : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList
    rw [Units.val_one]
    exact szList_one

@[expose] def szSub : Subgroup (GL (Fin 4) (ZMod 2)) :=
  { szMon with
    inv_mem' := fun {a} ha => by
      have hn : 0 < orderOf a := orderOf_pos a
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      rw [hinv]
      exact szMon.pow_mem ha _ }

theorem card_szSub_le : Nat.card szSub ≤ 20 := by
  have h : Nat.card szSub ≤ Nat.card {M : Matrix (Fin 4) (Fin 4) (ZMod 2) // M ∈ szList} :=
    Nat.card_le_card_of_injective
      (fun A => ⟨((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)), A.2⟩)
      (fun A B hAB => Subtype.ext (Units.ext (congrArg Subtype.val hAB)))
  have h2 : Nat.card {M : Matrix (Fin 4) (Fin 4) (ZMod 2) // M ∈ szList} = 20 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun M => (List.mem_toFinset (l := szList)).symm)),
      Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup szList_nodup,
      szList_length]
  omega

@[expose] noncomputable def phiGF : GaloisField 2 (2 * 0 + 1) ≃+* ZMod 2 := by
  haveI : Fintype (GaloisField 2 (2 * 0 + 1)) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * 0 + 1) (by norm_num), ZMod.card]
    norm_num)

@[expose] noncomputable def szPsi :
    GL (Fin 4) (GaloisField 2 (2 * 0 + 1)) ≃* GL (Fin 4) (ZMod 2) :=
  Units.mapEquiv (phiGF.mapMatrix (m := Fin 4)).toMulEquiv

theorem szPsi_val (A : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
    ((szPsi A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))).map phiGF := rfl

theorem szPsi_symm_val (B : GL (Fin 4) (ZMod 2)) :
    ((szPsi.symm B : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) =
      (B : Matrix (Fin 4) (Fin 4) (ZMod 2)).map phiGF.symm := rfl

theorem szRoot_mem (a' b' : ZMod 2) :
    (!![1, a', b', a' ^ 4 + a' * b' + b' ^ 2; 0, 1, a' ^ 2, a' ^ 3 + b'; 0, 0, 1, a'; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList := by
  revert a' b'
  decide +kernel

theorem szWeyl_mem :
    (!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈
      szList := by
  decide +kernel

theorem szPsi_mem_szSub (A : GL (Fin 4) (GaloisField 2 (2 * 0 + 1)))
    (hA : (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) ∈ SzGenerators 0) :
    szPsi A ∈ szSub := by
  show ((szPsi A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ szList
  rw [szPsi_val]
  rcases hA with ⟨a, b, h⟩ | ⟨x, h⟩ | h
  · rw [h]
    have key := szRoot_mem (phiGF a) (phiGF b)
    convert key using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_add, map_mul, map_pow]
  · rw [h]
    have hx0 : phiGF (x : GaloisField 2 (2 * 0 + 1)) ≠ 0 := by
      simp
    have hx1 : phiGF (x : GaloisField 2 (2 * 0 + 1)) = 1 := by
      revert hx0
      generalize phiGF (x : GaloisField 2 (2 * 0 + 1)) = y
      revert y
      decide +kernel
    convert szList_one using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx1, map_pow, map_inv₀]
  · rw [h]
    convert szWeyl_mem using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem Sz_zero_le_comap : Sz 0 ≤ szSub.comap szPsi.toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  intro A hA
  exact szPsi_mem_szSub A hA

theorem card_Sz_zero_le : Nat.card ↥(Sz 0) ≤ 20 := by
  have hle : ∀ A : ↥(Sz 0), szPsi (A : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) ∈ szSub :=
    fun A => Sz_zero_le_comap A.2
  have : Nat.card ↥(Sz 0) ≤ Nat.card szSub :=
    Nat.card_le_card_of_injective (fun A => ⟨szPsi (A : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))),
      hle A⟩) (fun A B h => Subtype.ext (szPsi.injective (congrArg Subtype.val h)))
  exact this.trans card_szSub_le

@[expose] def uS10 : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1],
    !![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def uS01 : GL (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1],
    !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1], by decide +kernel, by decide +kernel⟩

@[expose] def uW : GL (Fin 4) (ZMod 2) :=
  ⟨!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0], by decide +kernel, by decide +kernel⟩

theorem mem_Sz_of_gen (B : GL (Fin 4) (ZMod 2))
    (hB : (B : Matrix (Fin 4) (Fin 4) (ZMod 2)).map phiGF.symm ∈ SzGenerators 0) :
    szPsi.symm B ∈ Sz 0 := by
  apply Subgroup.subset_closure
  show ((szPsi.symm B : GL (Fin 4) (GaloisField 2 (2 * 0 + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * 0 + 1))) ∈ SzGenerators 0
  rw [szPsi_symm_val]
  exact hB

theorem uS10_mem : szPsi.symm uS10 ∈ Sz 0 :=
  mem_Sz_of_gen _ (Or.inl ⟨1, 0, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uS10]⟩)

theorem uS01_mem : szPsi.symm uS01 ∈ Sz 0 :=
  mem_Sz_of_gen _ (Or.inl ⟨0, 1, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uS01]⟩)

theorem uW_mem : szPsi.symm uW ∈ Sz 0 :=
  mem_Sz_of_gen _ (Or.inr (Or.inr (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uW])))

theorem orderOf_uS10 : orderOf uS10 = 4 := by
  have h2 : uS10 ^ 2 ≠ 1 := by
    intro h
    have h' := congrArg (fun u : GL (Fin 4) (ZMod 2) => (u : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h'
    revert h'
    show ¬ (!![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 2 = 1
    decide +kernel
  have h4 : uS10 ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (!![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) ^ 4 = 1
    decide +kernel
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := uS10) (by simpa using h2)
    (by simpa using h4)
  simpa using this

theorem orderOf_uW_uS01 : orderOf (uW * uS01) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : (uW * uS01) ^ 5 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mul]
    show ((!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]) ^ 5 = 1
    decide +kernel
  have h1 : uW * uS01 ≠ 1 := by
    intro h
    have h' := congrArg (fun u : GL (Fin 4) (ZMod 2) => (u : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    simp only [Units.val_mul, Units.val_one] at h'
    revert h'
    show ¬ ((!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]) = 1
    decide +kernel
  exact orderOf_eq_prime h5 h1

theorem card_Sz_zero : Nat.card ↥(Sz 0) = 20 := by
  have h4 : 4 ∣ Nat.card ↥(Sz 0) := by
    have := orderOf_dvd_natCard (⟨szPsi.symm uS10, uS10_mem⟩ : ↥(Sz 0))
    rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_uS10] at this
  have h5 : 5 ∣ Nat.card ↥(Sz 0) := by
    have hmem : szPsi.symm (uW * uS01) ∈ Sz 0 := by
      rw [map_mul]
      exact Subgroup.mul_mem _ uW_mem uS01_mem
    have := orderOf_dvd_natCard (⟨szPsi.symm (uW * uS01), hmem⟩ : ↥(Sz 0))
    rwa [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_uW_uS01] at this
  have h20 : 20 ∣ Nat.card ↥(Sz 0) := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 4 5) h4 h5
    simpa using this
  have hpos : 0 < Nat.card ↥(Sz 0) := Nat.card_pos
  have hle := card_Sz_zero_le
  have := Nat.le_of_dvd hpos h20
  omega

end CFSG.Quasithin

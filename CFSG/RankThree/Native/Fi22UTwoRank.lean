module

public import CFSG.RankThree.Native.Fi22UAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Fischer CFSG.Assembly.LowTwoRank Matrix

theorem range_isElementaryAbelian_of_injective_pi {S : Type*} [Group S] {p m : ℕ}
    [Fact p.Prime] (Ψ : Multiplicative (Fin m → ZMod p) →* S) (hΨ : Function.Injective Ψ) :
    CFSG.IsElementaryAbelian p Ψ.range ∧ Nat.card Ψ.range = p ^ m := by
  have hcomm : ∀ x y : Ψ.range, x * y = y * x := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    change Ψ a * Ψ b = Ψ b * Ψ a
    rw [← map_mul, ← map_mul, mul_comm]
  have hsq : ∀ x : Ψ.range, x ^ p = 1 := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    change Ψ a ^ p = 1
    have ha : a ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    rw [← map_pow, ha, map_one]
  refine ⟨{ toIsMulCommutative := ⟨⟨hcomm⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin m → ZMod p) ≃ _), Nat.card_fun,
    Nat.card_zmod, Nat.card_fin]

@[expose] def fi22Half (k : Fin 6) : Fin 3 := ⟨k / 2, by omega⟩

@[expose] def fi22NMat (A : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun k l => A (fi22Half k) (fi22Half l)

@[expose] def fi22GMat (A : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  1 + fi22NMat A

theorem fi22F4_two : (2 : F4) = 0 := F4.two_eq_zero

theorem fi22NMat_mul (A B : Matrix (Fin 3) (Fin 3) F4) : fi22NMat A * fi22NMat B = 0 := by
  ext k m
  simp only [Matrix.mul_apply, fi22NMat, Matrix.of_apply, Fin.sum_univ_six, Matrix.zero_apply]
  have h0 : fi22Half 0 = 0 := rfl
  have h1 : fi22Half 1 = 0 := rfl
  have h2 : fi22Half 2 = 1 := rfl
  have h3 : fi22Half 3 = 1 := rfl
  have h4 : fi22Half 4 = 2 := rfl
  have h5 : fi22Half 5 = 2 := rfl
  rw [h0, h1, h2, h3, h4, h5]
  linear_combination (A (fi22Half k) 0 * B 0 (fi22Half m) + A (fi22Half k) 1 * B 1 (fi22Half m) +
    A (fi22Half k) 2 * B 2 (fi22Half m)) * fi22F4_two

theorem fi22NMat_add (A B : Matrix (Fin 3) (Fin 3) F4) :
    fi22NMat (A + B) = fi22NMat A + fi22NMat B := by
  ext k l
  simp [fi22NMat]

theorem fi22GMat_mul (A B : Matrix (Fin 3) (Fin 3) F4) :
    fi22GMat A * fi22GMat B = fi22GMat (A + B) := by
  simp only [fi22GMat, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, fi22NMat_mul,
    fi22NMat_add, add_zero]
  abel

theorem fi22GMat_zero : fi22GMat 0 = 1 := by
  rw [fi22GMat, add_eq_left]
  ext k l
  simp [fi22NMat]

theorem fi22Mat3_add_self (A : Matrix (Fin 3) (Fin 3) F4) : A + A = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (A i j)

theorem fi22GMat_mul_self (A : Matrix (Fin 3) (Fin 3) F4) : fi22GMat A * fi22GMat A = 1 := by
  rw [fi22GMat_mul, fi22Mat3_add_self, fi22GMat_zero]

@[expose] def fi22GGL (A : Matrix (Fin 3) (Fin 3) F4) : GL (Fin 6) F4 :=
  ⟨fi22GMat A, fi22GMat A, fi22GMat_mul_self A, fi22GMat_mul_self A⟩

theorem fi22GGL_mul (A B : Matrix (Fin 3) (Fin 3) F4) :
    fi22GGL A * fi22GGL B = fi22GGL (A + B) :=
  Units.ext (fi22GMat_mul A B)

theorem fi22GGL_zero : fi22GGL 0 = 1 := Units.ext fi22GMat_zero

@[expose] def Fi22IsHerm (A : Matrix (Fin 3) (Fin 3) F4) : Prop := ∀ i j, A j i = A i j ^ 2

theorem fi22_add_sq (x y : F4) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := CharTwo.add_sq x y

theorem fi22GMat_conjTranspose {A : Matrix (Fin 3) (Fin 3) F4} (hA : Fi22IsHerm A) :
    ((fi22GMat A).map (· ^ 2))ᵀ = fi22GMat A := by
  ext k l
  simp only [Matrix.transpose_apply, Matrix.map_apply, fi22GMat, fi22NMat, Matrix.add_apply,
    Matrix.of_apply, Matrix.one_apply, fi22_add_sq]
  rw [← hA]
  congr 1
  · by_cases h : k = l
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem fi22_sq_eq_one {d : F4} (hd : d ^ 2 = 1) : d = 1 := by
  have h : (d + 1) ^ 2 = 0 := by
    rw [fi22_add_sq, hd, one_pow]
    exact CharTwo.add_self_eq_zero 1
  have h' : d + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h
  calc d = d + 1 + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h', zero_add]

theorem fi22GGL_mem {A : Matrix (Fin 3) (Fin 3) F4} (hA : Fi22IsHerm A) :
    fi22GGL A ∈ StatedSU 6 (2 ^ 1) F4 := by
  rw [mem_fi22S_iff]
  refine ⟨fi22_sq_eq_one ?_, ?_⟩
  · change (fi22GMat A).det ^ 2 = 1
    rw [pow_two, ← Matrix.det_mul, fi22GMat_mul_self, Matrix.det_one]
  · change ((fi22GMat A).map (· ^ 2))ᵀ * fi22GMat A = 1
    rw [fi22GMat_conjTranspose hA, fi22GMat_mul_self]

theorem eq_zero_of_fi22GGL_eq_scalar {A : Matrix (Fin 3) (Fin 3) F4} {c : F4ˣ}
    (h : fi22GGL A = Matrix.GeneralLinearGroup.scalar (Fin 6) c) : A = 0 := by
  ext i j
  have h' := congrArg (fun g : GL (Fin 6) F4 =>
    (g : Matrix (Fin 6) (Fin 6) F4) ⟨2 * i, by omega⟩ ⟨2 * j + 1, by omega⟩) h
  have hne : (⟨2 * i, by omega⟩ : Fin 6) ≠ ⟨2 * j + 1, by omega⟩ := by
    intro he
    have := congrArg Fin.val he
    simp only at this
    omega
  have hi : fi22Half ⟨2 * i, by omega⟩ = i := Fin.ext (by simp [fi22Half])
  have hj : fi22Half ⟨2 * j + 1, by omega⟩ = j := Fin.ext (by simp [fi22Half]; omega)
  simp only [fi22GGL, fi22GMat, fi22NMat, Matrix.add_apply, Matrix.one_apply_ne hne,
    Matrix.of_apply, zero_add, hi, hj, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hne] at h'
  simpa using h'

@[expose] def fi22Cast : ZMod 2 →+* F4 := ZMod.castHom (dvd_refl 2) F4

theorem fi22Cast_sq (x : ZMod 2) : fi22Cast x ^ 2 = fi22Cast x := by
  rw [← map_pow, ZMod.pow_card]

theorem fi22Cast_injective : Function.Injective fi22Cast := fi22Cast.injective

@[expose] def fi22HermOf (a : Fin 9 → ZMod 2) : Matrix (Fin 3) (Fin 3) F4 :=
  !![fi22Cast (a 0), fi22Cast (a 3) + fi22Cast (a 4) * F4.ω,
      fi22Cast (a 5) + fi22Cast (a 6) * F4.ω;
    fi22Cast (a 3) + fi22Cast (a 4) * F4.ω ^ 2, fi22Cast (a 1),
      fi22Cast (a 7) + fi22Cast (a 8) * F4.ω;
    fi22Cast (a 5) + fi22Cast (a 6) * F4.ω ^ 2, fi22Cast (a 7) + fi22Cast (a 8) * F4.ω ^ 2,
      fi22Cast (a 2)]

theorem fi22_omega_four : F4.ω ^ 4 = F4.ω := by decide

theorem fi22_omega_sq_add : F4.ω ^ 2 + F4.ω = 1 := by decide

theorem fi22HermOf_isHerm (a : Fin 9 → ZMod 2) : Fi22IsHerm (fi22HermOf a) := by
  have hpair : ∀ x y : ZMod 2, (fi22Cast x + fi22Cast y * F4.ω) ^ 2 =
      fi22Cast x + fi22Cast y * F4.ω ^ 2 := fun x y => by
    rw [fi22_add_sq, mul_pow, fi22Cast_sq, fi22Cast_sq]
  have hpair' : ∀ x y : ZMod 2, (fi22Cast x + fi22Cast y * F4.ω ^ 2) ^ 2 =
      fi22Cast x + fi22Cast y * F4.ω := fun x y => by
    rw [fi22_add_sq, mul_pow, fi22Cast_sq, fi22Cast_sq, ← pow_mul, fi22_omega_four]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [fi22HermOf, fi22Cast_sq, hpair, hpair']

theorem fi22HermOf_add (a b : Fin 9 → ZMod 2) :
    fi22HermOf (a + b) = fi22HermOf a + fi22HermOf b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fi22HermOf, map_add] <;> ring

theorem fi22HermOf_zero : fi22HermOf 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fi22HermOf]

theorem fi22HermOf_eq_zero {a : Fin 9 → ZMod 2} (h : fi22HermOf a = 0) : a = 0 := by
  have e : ∀ i j, fi22HermOf a i j = 0 := fun i j => by rw [h]; rfl
  have hc : ∀ x : ZMod 2, fi22Cast x = 0 → x = 0 := fun x hx =>
    fi22Cast_injective (by rw [hx, map_zero])
  have hpair : ∀ x y : ZMod 2, fi22Cast x + fi22Cast y * F4.ω = 0 →
      fi22Cast x + fi22Cast y * F4.ω ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y h1 h2
    have hy : fi22Cast y = 0 := by
      have := congrArg₂ (· + ·) h1 h2
      simp only [add_zero] at this
      calc fi22Cast y = fi22Cast y * (F4.ω ^ 2 + F4.ω) := by rw [fi22_omega_sq_add, mul_one]
        _ = 0 := by linear_combination this - (fi22Cast x) * fi22F4_two
    refine ⟨hc x ?_, hc y hy⟩
    rw [hy, zero_mul, add_zero] at h1
    exact h1
  have h00 := e 0 0
  have h11 := e 1 1
  have h22 := e 2 2
  have h01 := e 0 1
  have h10 := e 1 0
  have h02 := e 0 2
  have h20 := e 2 0
  have h12 := e 1 2
  have h21 := e 2 1
  simp only [fi22HermOf, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one]
    at h00 h11 h22 h01 h10 h02 h20 h12 h21
  obtain ⟨h3, h4⟩ := hpair _ _ h01 h10
  obtain ⟨h5, h6⟩ := hpair _ _ h02 h20
  obtain ⟨h7, h8⟩ := hpair _ _ h12 h21
  funext k
  fin_cases k
  · exact hc _ h00
  · exact hc _ h11
  · exact hc _ h22
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

@[expose] def fi22EtwoHom : Multiplicative (Fin 9 → ZMod 2) →* StatedSU 6 (2 ^ 1) F4 where
  toFun a := ⟨fi22GGL (fi22HermOf (Multiplicative.toAdd a)),
    fi22GGL_mem (fi22HermOf_isHerm _)⟩
  map_one' := Subtype.ext (by
    change fi22GGL (fi22HermOf 0) = 1
    rw [fi22HermOf_zero, fi22GGL_zero])
  map_mul' a b := Subtype.ext (by
    change fi22GGL (fi22HermOf (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      fi22GGL (fi22HermOf (Multiplicative.toAdd a)) * fi22GGL (fi22HermOf (Multiplicative.toAdd b))
    rw [fi22GGL_mul, fi22HermOf_add])

@[expose] def fi22EtwoX : Multiplicative (Fin 9 → ZMod 2) →* fi22OuterX :=
  fi22UnitaryEquiv.toMonoidHom.comp ((QuotientGroup.mk' _).comp fi22EtwoHom)

theorem fi22EtwoX_injective : Function.Injective fi22EtwoX := by
  refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
  have h1 : (QuotientGroup.mk' _ (fi22EtwoHom a) :
      StatedProj (StatedSU 6 (2 ^ 1) F4)) = 1 :=
    fi22UnitaryEquiv.injective (by rw [map_one]; exact ha)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have hA := eq_zero_of_fi22GGL_eq_scalar hc.symm
  exact Multiplicative.toAdd.injective (fi22HermOf_eq_zero hA)

theorem R3E_Fi22_unitary_quotient_elementary_two_rank_nine :
    ∃ E : Subgroup fi22OuterX, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨_, range_isElementaryAbelian_of_injective_pi fi22EtwoX fi22EtwoX_injective⟩

end CFSG.RankThree.Native.Fi22U

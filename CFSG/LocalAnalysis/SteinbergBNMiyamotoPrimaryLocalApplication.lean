module

public import CFSG.LocalAnalysis.SteinbergBNGMSLinearLocalApplication
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public noncomputable section

namespace CFSG.LocalAnalysis

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

@[expose] def miyamotoJ4 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

section Matrices

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def miyamotoX (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; a, 1, 0, 0; c, b, 1, 0; d, h.bar c + h.bar a * b, h.bar a, 1]

theorem miyamotoX_zero : miyamotoX h 0 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoX]

theorem miyamotoX_mul [CharP K 2] {a b c d a' b' c' d' : K} (hb : h.bar b = b) :
    miyamotoX h a b c d * miyamotoX h a' b' c' d' =
      miyamotoX h (a + a') (b + b') (c + c' + b * a')
        (d + d' + (h.bar c + h.bar a * b) * a' + h.bar a * c') := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoX, Matrix.mul_apply, Fin.sum_univ_four, map_add, map_mul, hb]
  all_goals first | ring1 | linear_combination (-(b * h.bar a')) * h2

@[expose] def miyamotoUnipotent (za zb : Bool) : Subgroup (GL (Fin 4) K) where
  carrier := {g | ∃ a b c d : K, (za = true → a = 0) ∧ (zb = true → b = 0) ∧ h.bar b = b ∧
    d + h.bar d + a * h.bar c + h.bar a * c = 0 ∧
    (g : Matrix (Fin 4) (Fin 4) K) = miyamotoX h a b c d}
  mul_mem' := by
    have : CharP K 2 := h.charP
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rintro g g' ⟨a, b, c, d, ha, hb0, hb, hd, hg⟩ ⟨a', b', c', d', ha', hb0', hb', hd', hg'⟩
    refine ⟨a + a', b + b', c + c' + b * a', d + d' + (h.bar c + h.bar a * b) * a' + h.bar a * c',
      fun hz => by rw [ha hz, ha' hz, add_zero], fun hz => by rw [hb0 hz, hb0' hz, add_zero],
      by rw [map_add, hb, hb'], ?_, by rw [Units.val_mul, hg, hg', miyamotoX_mul h hb]⟩
    simp only [map_add, map_mul, h.bar_bar, hb]
    linear_combination hd + hd' + (a' * h.bar c + h.bar a * b * a' + h.bar a * c' +
      h.bar a' * c + a * b * h.bar a' + a * h.bar c' + a' * b * h.bar a') * h2
  one_mem' := ⟨0, 0, 0, 0, fun _ => rfl, fun _ => rfl, map_zero _, by simp,
    by rw [Units.val_one, miyamotoX_zero]⟩
  inv_mem' := by
    have : CharP K 2 := h.charP
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rintro g ⟨a, b, c, d, ha, hb0, hb, hd, hg⟩
    refine ⟨a, b, c + b * a, d + a * h.bar c + h.bar a * c, ha, hb0, hb, ?_, ?_⟩
    · simp only [map_add, map_mul, h.bar_bar, hb]
      linear_combination hd + (a * h.bar c + h.bar a * c + a * b * h.bar a) * h2
    · have hmul : (g : Matrix (Fin 4) (Fin 4) K) *
          miyamotoX h a b (c + b * a) (d + a * h.bar c + h.bar a * c) = 1 := by
        rw [hg, miyamotoX_mul h hb, ← miyamotoX_zero h]
        congr 1
        · linear_combination a * h2
        · linear_combination b * h2
        · linear_combination (c + b * a) * h2
        · linear_combination (d + a * h.bar c + h.bar a * c + h.bar a * b * a) * h2
      calc ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
          = ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((g : Matrix (Fin 4) (Fin 4) K) *
            miyamotoX h a b (c + b * a) (d + a * h.bar c + h.bar a * c)) := by rw [hmul, mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]

@[expose] def miyamotoDiag (a b c d : Kˣ) : GL (Fin 4) K where
  val := diagonal ![(a : K), b, c, d]
  inv := diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K), ((c⁻¹ : Kˣ) : K), ((d⁻¹ : Kˣ) : K)]
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp

theorem coe_miyamotoDiag (a b c d : Kˣ) :
    ((miyamotoDiag a b c d : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![(a : K), b, c, d] :=
  rfl

theorem miyamotoDiag_mul (a b c d a' b' c' d' : Kˣ) :
    (miyamotoDiag a b c d : GL (Fin 4) K) * miyamotoDiag a' b' c' d' =
      miyamotoDiag (a * a') (b * b') (c * c') (d * d') := by
  apply Units.ext
  rw [Units.val_mul, coe_miyamotoDiag, coe_miyamotoDiag, coe_miyamotoDiag, diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem miyamotoDiag_one : (miyamotoDiag 1 1 1 1 : GL (Fin 4) K) = 1 := by
  apply Units.ext
  change diagonal _ = (1 : Matrix (Fin 4) (Fin 4) K)
  rw [← diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def miyamotoIParam : Kˣ × Kˣ →* Kˣ :=
  MonoidHom.fst Kˣ Kˣ * MonoidHom.snd Kˣ Kˣ *
    ((Units.map h.bar.toMonoidHom).comp (MonoidHom.fst Kˣ Kˣ))⁻¹ *
    ((Units.map h.bar.toMonoidHom).comp (MonoidHom.snd Kˣ Kˣ))⁻¹

@[expose] def miyamotoIHom : Kˣ × Kˣ →* GL (Fin 4) K where
  toFun x := miyamotoDiag x.1 x.2 (Units.map h.bar.toMonoidHom x.2)⁻¹
    (Units.map h.bar.toMonoidHom x.1)⁻¹
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, inv_one, miyamotoDiag_one]
  map_mul' x y := by
    rw [miyamotoDiag_mul]
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_inv]

@[expose] def miyamotoI : Subgroup (GL (Fin 4) K) :=
  (miyamotoIParam h).ker.map (miyamotoIHom h)

@[expose] def miyamotoI1Hom : Kˣ →* GL (Fin 4) K where
  toFun a := miyamotoDiag a a a⁻¹ a⁻¹
  map_one' := by simp only [inv_one, miyamotoDiag_one]
  map_mul' a b := by
    rw [miyamotoDiag_mul]
    simp only [mul_inv]

@[expose] def miyamotoI1 : Subgroup (GL (Fin 4) K) :=
  ((miyamotoI1Hom (K := K)).comp (Units.map h.fixedField.subtype.toMonoidHom)).range

@[expose] def miyamotoI2Hom : Kˣ →* GL (Fin 4) K where
  toFun a := miyamotoDiag (a ^ 2) (a ^ (2 ^ f - 1)) (a ^ (2 ^ f - 1))
    (Units.map h.bar.toMonoidHom a ^ 2)⁻¹
  map_one' := by simp only [one_pow, map_one, inv_one, miyamotoDiag_one]
  map_mul' a b := by
    rw [miyamotoDiag_mul]
    simp only [mul_pow, map_mul, mul_inv]

@[expose] def miyamotoI2 : Subgroup (GL (Fin 4) K) :=
  (miyamotoI2Hom h).range

@[expose] def miyamotoN1Mat : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 4) (Fin 4) K where
  toFun m := !![m 0 0, m 0 1, 0, 0; m 1 0, m 1 1, 0, 0; 0, 0, h.bar (m 0 0), h.bar (m 0 1);
    0, 0, h.bar (m 1 0), h.bar (m 1 1)]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' m n := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, map_add, map_mul]

@[expose] def miyamotoN1 : Subgroup (GL (Fin 4) K) :=
  ((Units.map (miyamotoN1Mat h)).comp SpecialLinearGroup.toGL).range

@[expose] def miyamotoN2Mat (K : Type) [Field K] :
    Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 4) (Fin 4) K where
  toFun m := !![1, 0, 0, 0; 0, m 0 0, m 0 1, 0; 0, m 1 0, m 1 1, 0; 0, 0, 0, 1]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' m n := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

@[expose] def miyamotoN2 : Subgroup (GL (Fin 4) K) :=
  ((Units.map (miyamotoN2Mat K)).comp (SpecialLinearGroup.toGL.comp
    (SpecialLinearGroup.map (h.fixedField.subtype : h.fixedField →+* K)))).range

@[expose] def miyamotoR1 (K : Type) [Field K] : GL (Fin 4) K where
  val := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  inv := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def miyamotoR2 (K : Type) [Field K] : GL (Fin 4) K where
  val := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
  inv := !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def miyamotoZ1 (K : Type) [Field K] : GL (Fin 4) K where
  val := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1]
  inv := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; -1, 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def miyamotoZ2 (K : Type) [Field K] : GL (Fin 4) K where
  val := !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1]
  inv := !![1, 0, 0, 0; 0, 1, 0, 0; -1, 0, 1, 0; 0, -1, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def miyamotoI2r1 : Subgroup (GL (Fin 4) K) :=
  (miyamotoI2 h).map (MulAut.conj (miyamotoR1 K)⁻¹).toMonoidHom

theorem miyamotoUnipotent_le_SU (za zb : Bool) :
    miyamotoUnipotent h za zb ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rintro g ⟨a, b, c, d, -, -, hb, hd, hg⟩
  refine mem_gramSU.mpr ⟨?_, ?_⟩
  · rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [miyamotoX, miyamotoJ4, Matrix.mul_apply, Fin.sum_univ_four, map_add, map_mul,
        h.bar_bar, hb]
    all_goals first
      | linear_combination hd
      | linear_combination (h.bar c + h.bar a * b) * h2
      | linear_combination h.bar a * h2
      | linear_combination (c + a * b) * h2
      | linear_combination b * h2
      | linear_combination a * h2
  · rw [hg]
    simp [miyamotoX, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

end Matrices

section Ambient

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G) (Q T : Subgroup G)

@[expose] def miyamotoPull (M : Subgroup (GL (Fin 4) K)) : Subgroup G :=
  ((M.subgroupOf (gramSU h (miyamotoJ4 K))).map η.symm.toMonoidHom).map L.subtype

abbrev miyamotoPG : Subgroup G := miyamotoPull h L η (miyamotoUnipotent h false false)

abbrev miyamotoA1G : Subgroup G := miyamotoPull h L η (miyamotoUnipotent h true false)

abbrev miyamotoA2G : Subgroup G := miyamotoPull h L η (miyamotoUnipotent h false true)

abbrev miyamotoIG : Subgroup G := miyamotoPull h L η (miyamotoI h)

abbrev miyamotoI1G : Subgroup G := miyamotoPull h L η (miyamotoI1 h)

abbrev miyamotoI2G : Subgroup G := miyamotoPull h L η (miyamotoI2 h)

abbrev miyamotoI2r1G : Subgroup G := miyamotoPull h L η (miyamotoI2r1 h)

abbrev miyamotoN1G : Subgroup G := miyamotoPull h L η (miyamotoN1 h)

abbrev miyamotoN2G : Subgroup G := miyamotoPull h L η (miyamotoN2 h)

@[expose] def miyamotoB1 : Subgroup G := zpowers t ⊔ miyamotoA1G h L η

@[expose] def miyamotoB2 : Subgroup G := zpowers t ⊔ miyamotoA2G h L η

@[expose] def miyamotoM0 : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer (CFSG.centerIn Q : Set G))

@[expose] def miyamotoE : Subgroup G :=
  let X := miyamotoM0 Q ⊓ centralizer (miyamotoI2r1G h L η : Set G) ⊔ miyamotoIG h L η
  ⁅X, X⁆

@[expose] def miyamotoD1 : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer (miyamotoB1 h L η t : Set G))

@[expose] def miyamotoF1 : Subgroup G :=
  let X := miyamotoD1 h L η t ⊔ miyamotoI1G h L η
  ⁅X, X⁆

@[expose] def miyamotoQ1 : Subgroup G := miyamotoF1 h L η t ⊔ Q

@[expose] def miyamotoS1 : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer (miyamotoQ1 h L η t Q : Set G))

@[expose] def miyamotoR : Subgroup G :=
  let X := miyamotoS1 h L η t Q ⊔ miyamotoIG h L η
  ⁅X, X⁆

@[expose] def miyamotoY2 : Subgroup G := miyamotoE h L η Q ⊔ miyamotoA2G h L η

@[expose] def miyamotoY3 : Subgroup G := miyamotoE h L η Q ⊔ miyamotoB2 h L η t

@[expose] def miyamotoD2 : Subgroup G where
  carrier := {s | s ∈ miyamotoS1 h L η t Q ⊓ normalizer (miyamotoE h L η Q : Set G) ⊓
    normalizer (miyamotoY2 h L η Q : Set G) ⊓ normalizer (miyamotoY3 h L η t Q : Set G) ∧
    ∀ y ∈ miyamotoY2 h L η Q, y⁻¹ * (s⁻¹ * y * s) ∈ miyamotoE h L η Q}
  mul_mem' := by
    rintro s s' ⟨hs, hsy⟩ ⟨hs', hsy'⟩
    refine ⟨mul_mem hs hs', fun y hy => ?_⟩
    have hE : s'⁻¹ ∈ normalizer (miyamotoE h L η Q : Set G) :=
      inv_mem (mem_inf.mp (mem_inf.mp (mem_inf.mp hs').1).1).2
    have h1 := (mem_normalizer_iff.mp hE _).mp (hsy y hy)
    have h2 := mul_mem (hsy' y hy) h1
    rw [inv_inv] at h2
    have e : y⁻¹ * ((s * s')⁻¹ * y * (s * s')) =
        y⁻¹ * (s'⁻¹ * y * s') * (s'⁻¹ * (y⁻¹ * (s⁻¹ * y * s)) * s') := by group
    rw [e]
    exact h2
  one_mem' := ⟨one_mem _, fun y _ => by
    rw [inv_one, one_mul, mul_one, inv_mul_cancel]
    exact one_mem _⟩
  inv_mem' := by
    rintro s ⟨hs, hsy⟩
    refine ⟨inv_mem hs, fun y hy => ?_⟩
    have hY : s ∈ normalizer (miyamotoY2 h L η Q : Set G) := (mem_inf.mp (mem_inf.mp hs).1).2
    have hy' : s * y * s⁻¹ ∈ miyamotoY2 h L η Q := (mem_normalizer_iff.mp hY y).mp hy
    have h1 := inv_mem (hsy _ hy')
    have e : y⁻¹ * (s⁻¹⁻¹ * y * s⁻¹) = ((s * y * s⁻¹)⁻¹ * (s⁻¹ * (s * y * s⁻¹) * s))⁻¹ := by
      group
    rw [e]
    exact h1

@[expose] def miyamotoF2 : Subgroup G := miyamotoD2 h L η t Q ⊓ miyamotoR h L η t Q

@[expose] def MiyamotoSetup : Prop :=
  2 ≤ f ∧ CFSG.Assembly.ComponentType.IsStandardSubgroup L ∧ ¬L.Normal ∧
    CFSG.pPrimeCore 2 G = ⊥ ∧
    (∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G)))) ∧
    t ∈ centralizer (L : Set G) ∧ orderOf t = 2 ∧
    Q ≤ L ⊔ centralizer (L : Set G) ∧
    (∃ S : Sylow 2 (L ⊔ centralizer (L : Set G) : Subgroup G),
      (S : Subgroup (L ⊔ centralizer (L : Set G) : Subgroup G)) =
        Q.subgroupOf (L ⊔ centralizer (L : Set G))) ∧
    t ∈ Q ∧ miyamotoPG h L η ≤ Q ∧
    T ≤ centralizer ({t} : Set G) ∧
    (∃ S : Sylow 2 (centralizer ({t} : Set G)),
      (S : Subgroup (centralizer ({t} : Set G))) = T.subgroupOf (centralizer ({t} : Set G))) ∧
    Q ≤ T

@[expose] def MiyamotoTupleOne {H : Type*} [Group H] (A : Subgroup H) (tH : H)
    (U V D : Subgroup H) (n : ℕ) : Prop :=
  n = 2 * f ∧
    ∃ e : H ≃* (normalizer (miyamotoF1 h L η t : Set G) ⊓
        centralizer (miyamotoI1G h L η : Set G) : Subgroup G),
      (A.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoN1G h L η ∧
      ((e tH : _) : G) = t ∧
      (U.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoN1G h L η ⊓ miyamotoPG h L η ∧
      (V.map e.toMonoidHom).map (Subgroup.subtype _) =
        miyamotoR h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ∧
      (D.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoIG h L η ⊓ miyamotoN1G h L η

@[expose] def MiyamotoTupleTwo {H : Type*} [Group H] (A : Subgroup H) (tH : H)
    (U V D : Subgroup H) (n : ℕ) : Prop :=
  n = f ∧
    ∃ e : H ≃* (normalizer (miyamotoF2 h L η t Q : Set G) ⊓
        centralizer (miyamotoI2G h L η : Set G) : Subgroup G),
      (A.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoN2G h L η ∧
      ((e tH : _) : G) = t ∧
      (U.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoN2G h L η ⊓ miyamotoPG h L η ∧
      (V.map e.toMonoidHom).map (Subgroup.subtype _) =
        miyamotoR h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ∧
      (D.map e.toMonoidHom).map (Subgroup.subtype _) = miyamotoIG h L η ⊓ miyamotoN2G h L η

@[expose] def MiyamotoTupleThree {H : Type*} [Group H] (A : Subgroup H) (tH : H)
    (U V D : Subgroup H) (n : ℕ) : Prop :=
  n = 2 * f ∧
    let N := normalizer (miyamotoF1 h L η t : Set G)
    let π := QuotientGroup.mk' ((miyamotoF1 h L η t).subgroupOf N)
    miyamotoN1G h L η ≤ N ∧ miyamotoN1G h L η ⊓ miyamotoPG h L η ≤ N ∧
      miyamotoR h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ N ∧
      miyamotoIG h L η ⊓ miyamotoN1G h L η ≤ N ∧
      ∃ (ht : t ∈ N) (e : H ≃* N ⧸ (miyamotoF1 h L η t).subgroupOf N),
        A.map e.toMonoidHom = ((miyamotoN1G h L η).subgroupOf N).map π ∧
        e tH = π ⟨t, ht⟩ ∧
        U.map e.toMonoidHom = ((miyamotoN1G h L η ⊓ miyamotoPG h L η).subgroupOf N).map π ∧
        V.map e.toMonoidHom = ((miyamotoR h L η t Q ⊓
          centralizer (miyamotoI1G h L η : Set G)).subgroupOf N).map π ∧
        D.map e.toMonoidHom = ((miyamotoIG h L η ⊓ miyamotoN1G h L η).subgroupOf N).map π

end Ambient

@[expose] def MiyamotoPrimaryLinearApplication {H : Type*} [Group H] (A : Subgroup H) (tH : H)
    (U V D : Subgroup H) (n : ℕ) : Prop :=
  GMSLinearLocalApplication A tH U V D n ∧
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (f : ℕ) (K : Type) (_ : Field K)
      (h : UnitaryFieldData 2 f K) (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
      (Q T : Subgroup G), MiyamotoSetup h L η t Q T ∧
        (MiyamotoTupleOne h L η t Q A tH U V D n ∨ MiyamotoTupleTwo h L η t Q A tH U V D n ∨
          MiyamotoTupleThree h L η t Q A tH U V D n)

end CFSG.LocalAnalysis

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Elt

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

theorem matU_inv_eq (hF : Nat.card F = p ^ 2) (g : SU3F p F) :
    matU g⁻¹ = ((matU g).map (uniData hF).bar)ᵀ := by
  show (((g⁻¹ : SU3F p F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv ((mem_unitarySU_iff (uniData hF)).mp g.2).2

@[expose] def diagU (hF : Nat.card F = p ^ 2) : Subgroup (SU3F p F) where
  carrier := {g | matU g 0 1 = 0 ∧ matU g 0 2 = 0 ∧ matU g 1 0 = 0 ∧ matU g 1 2 = 0 ∧
    matU g 2 0 = 0 ∧ matU g 2 1 = 0}
  one_mem' := by simp [matU_one]
  mul_mem' := by
    rintro a b ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    simp [matU_mul, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3,
      b4, b5, b6]
  inv_mem' := by
    rintro a ⟨a1, a2, a3, a4, a5, a6⟩
    simp [matU_inv_eq hF, a1, a2, a3, a4, a5, a6]

theorem mem_diagU_iff (hF : Nat.card F = p ^ 2) {g : SU3F p F} : g ∈ diagU hF ↔
    matU g 0 1 = 0 ∧ matU g 0 2 = 0 ∧ matU g 1 0 = 0 ∧ matU g 1 2 = 0 ∧ matU g 2 0 = 0 ∧
      matU g 2 1 = 0 := Iff.rfl

@[expose] def monoU (hF : Nat.card F = p ^ 2) : Subgroup (SU3F p F) where
  carrier := {g | matU g 0 2 = 0 ∧ matU g 1 2 = 0 ∧ matU g 2 0 = 0 ∧ matU g 2 1 = 0 ∧
    ((matU g 0 1 = 0 ∧ matU g 1 0 = 0) ∨ (matU g 0 0 = 0 ∧ matU g 1 1 = 0))}
  one_mem' := by simp [matU_one]
  mul_mem' := by
    rintro a b ⟨a1, a2, a3, a4, ⟨a5, a6⟩ | ⟨a5, a6⟩⟩ ⟨b1, b2, b3, b4, ⟨b5, b6⟩ | ⟨b5, b6⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [matU_mul, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3,
          b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [matU_mul, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3,
          b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [matU_mul, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3,
          b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [matU_mul, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3,
          b4, b5, b6]
  inv_mem' := by
    rintro a ⟨a1, a2, a3, a4, ⟨a5, a6⟩ | ⟨a5, a6⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [matU_inv_eq hF, a1, a2, a3, a4, a5, a6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [matU_inv_eq hF, a1, a2, a3, a4, a5, a6]

theorem mem_monoU_iff (hF : Nat.card F = p ^ 2) {g : SU3F p F} : g ∈ monoU hF ↔
    matU g 0 2 = 0 ∧ matU g 1 2 = 0 ∧ matU g 2 0 = 0 ∧ matU g 2 1 = 0 ∧
      ((matU g 0 1 = 0 ∧ matU g 1 0 = 0) ∨ (matU g 0 0 = 0 ∧ matU g 1 1 = 0)) := Iff.rfl

theorem diagU_le_monoU (hF : Nat.card F = p ^ 2) : diagU hF ≤ monoU hF :=
  fun _ ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h4, h5, h6, Or.inl ⟨h1, h3⟩⟩

theorem monoU_le_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : monoU hF ≤ leviU hF :=
  fun _ ⟨h1, h2, h3, h4, _⟩ => (mem_leviU_iff hp2 hF).mpr ⟨h1, h2, h3, h4⟩

@[expose] noncomputable def muU (hF : Nat.card F = p ^ 2) : Subgroup Fˣ :=
  (Units.map (uniData hF).normHom).ker

theorem bar_mul_self_of_mem_muU (hF : Nat.card F = p ^ 2) {u : Fˣ} (hu : u ∈ muU hF) :
    (uniData hF).bar (u : F) * (u : F) = 1 := by
  have h := (UnitaryFieldData.mem_ker_normUnits (uniData hF)).mp hu
  rw [UnitaryFieldData.norm] at h
  rw [mul_comm]
  exact h

theorem mem_muU_of_bar_mul_self (hF : Nat.card F = p ^ 2) {u : Fˣ}
    (h : (uniData hF).bar (u : F) * (u : F) = 1) : u ∈ muU hF := by
  refine (UnitaryFieldData.mem_ker_normUnits (uniData hF)).mpr ?_
  rw [UnitaryFieldData.norm, mul_comm]
  exact h

theorem card_muU [Finite F] (hF : Nat.card F = p ^ 2) : Nat.card (muU hF) = p + 1 := by
  have h := (uniData hF).card_ker_normUnits_and_surjective.1
  show Nat.card ↥(Units.map (uniData hF).normHom).ker = p + 1
  rw [h, pow_one]

@[expose] noncomputable def diagSU (hF : Nat.card F = p ^ 2) (x y z : F) (hxyz : x * y * z = 1)
    (hx : (uniData hF).bar x * x = 1) (hy : (uniData hF).bar y * y = 1)
    (hz : (uniData hF).bar z * z = 1) : SU3F p F :=
  mkSU3 hF (Matrix.diagonal ![x, y, z])
    (by simpa [Matrix.det_diagonal, Fin.prod_univ_three] using hxyz)
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.diagonal_apply, hx, hy, hz])

theorem matU_diagSU (hF : Nat.card F = p ^ 2) (x y z : F) (hxyz : x * y * z = 1)
    (hx : (uniData hF).bar x * x = 1) (hy : (uniData hF).bar y * y = 1)
    (hz : (uniData hF).bar z * z = 1) :
    matU (diagSU hF x y z hxyz hx hy hz) = Matrix.diagonal ![x, y, z] := rfl

@[expose] noncomputable def diagHomU (hF : Nat.card F = p ^ 2) :
    ↥(muU hF) × ↥(muU hF) →* SU3F p F where
  toFun ab := diagSU hF ((ab.1 : Fˣ) : F) ((ab.2 : Fˣ) : F) (((ab.1 * ab.2)⁻¹ : ↥(muU hF)) : Fˣ)
    (congrArg Units.val (by simp : (ab.1 : Fˣ) * ab.2 * ((ab.1 * ab.2)⁻¹ : ↥(muU hF)) = 1))
    (bar_mul_self_of_mem_muU hF ab.1.2) (bar_mul_self_of_mem_muU hF ab.2.2)
    (bar_mul_self_of_mem_muU hF ((ab.1 * ab.2)⁻¹ : ↥(muU hF)).2)
  map_one' := by
    apply ext_matU
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matU_diagSU, matU_one]
  map_mul' a b := by
    apply ext_matU
    rw [matU_mul, matU_diagSU, matU_diagSU, matU_diagSU, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · rfl
    · rfl
    · show ((((a * b).1 * (a * b).2)⁻¹ : ↥(muU hF)) : Fˣ).val = _
      have : (((a * b).1 * (a * b).2)⁻¹ : ↥(muU hF)) = (a.1 * a.2)⁻¹ * (b.1 * b.2)⁻¹ := by
        rw [Prod.fst_mul, Prod.snd_mul, mul_mul_mul_comm, mul_inv]
      rw [this]
      rfl

theorem matU_diagHomU (hF : Nat.card F = p ^ 2) (ab : ↥(muU hF) × ↥(muU hF)) :
    matU (diagHomU hF ab) = Matrix.diagonal ![((ab.1 : Fˣ) : F), ((ab.2 : Fˣ) : F),
      (((ab.1 * ab.2)⁻¹ : ↥(muU hF)) : Fˣ)] := rfl

theorem diagHomU_mem (hF : Nat.card F = p ^ 2) (ab : ↥(muU hF) × ↥(muU hF)) :
    diagHomU hF ab ∈ diagU hF := by
  rw [mem_diagU_iff, matU_diagHomU]
  simp

theorem diagU_det (hF : Nat.card F = p ^ 2) {g : SU3F p F} (hg : g ∈ diagU hF) :
    matU g 0 0 * matU g 1 1 * matU g 2 2 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  have hd : (matU g).det = 1 := ((mem_unitarySU_iff (uniData hF)).mp g.2).1
  rw [Matrix.det_fin_three] at hd
  simpa [h1, h2, h3, h4, h5, h6] using hd

theorem bar_mul_self_of_mem_diagU (hF : Nat.card F = p ^ 2) {g : SU3F p F} (hg : g ∈ diagU hF)
    (j : Fin 3) : (uniData hF).bar (matU g j j) * matU g j j = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  have := unitary_cols hF g j j
  fin_cases j <;> simpa [Fin.sum_univ_three, h1, h2, h3, h4, h5, h6] using this

theorem diagHomU_injective (hF : Nat.card F = p ^ 2) : Function.Injective (diagHomU hF) :=
  fun a b h => by
    have h1 := congrArg (fun g => matU g 0 0) h
    have h2 := congrArg (fun g => matU g 1 1) h
    simp only [matU_diagHomU, Matrix.diagonal_apply_eq] at h1 h2
    exact Prod.ext (Subtype.ext (Units.ext h1)) (Subtype.ext (Units.ext h2))

theorem range_diagHomU (hF : Nat.card F = p ^ 2) : (diagHomU hF).range = diagU hF := by
  ext g
  constructor
  · rintro ⟨ab, rfl⟩
    exact diagHomU_mem hF ab
  · intro hg
    have hdet := diagU_det hF hg
    have h0 : matU g 0 0 ≠ 0 := fun h => by
      rw [h] at hdet
      simp at hdet
    have h1 : matU g 1 1 ≠ 0 := fun h => by
      rw [h] at hdet
      simp at hdet
    have ha : Units.mk0 (matU g 0 0) h0 ∈ muU hF :=
      mem_muU_of_bar_mul_self hF (bar_mul_self_of_mem_diagU hF hg 0)
    have hb : Units.mk0 (matU g 1 1) h1 ∈ muU hF :=
      mem_muU_of_bar_mul_self hF (bar_mul_self_of_mem_diagU hF hg 1)
    refine ⟨(⟨_, ha⟩, ⟨_, hb⟩), ?_⟩
    apply ext_matU
    rw [matU_diagHomU]
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hg
    have h22 : matU g 2 2 = (matU g 0 0 * matU g 1 1)⁻¹ := eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4, e5, e6, h22]

theorem card_diagU [Finite F] (hF : Nat.card F = p ^ 2) : Nat.card (diagU hF) = (p + 1) ^ 2 := by
  have h1 : Nat.card (diagU hF) = Nat.card (↥(muU hF) × ↥(muU hF)) := by
    rw [← range_diagHomU hF]
    exact (Nat.card_congr (Equiv.ofInjective _ (diagHomU_injective hF))).symm
  rw [h1, Nat.card_prod, card_muU hF, sq]

theorem swapU_mem_monoU (hF : Nat.card F = p ^ 2) : swapU hF ∈ monoU hF := by
  rw [mem_monoU_iff]
  simp [matU_swapU, swapMat]

theorem relIndex_diagU_monoU (hF : Nat.card F = p ^ 2) : (diagU hF).relIndex (monoU hF) = 2 := by
  have : ((diagU hF).subgroupOf (monoU hF)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨swapU hF, swapU_mem_monoU hF⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    obtain ⟨h02, h12, h20, h21, ⟨h01, h10⟩ | ⟨h00, h11⟩⟩ := hb
    · have hbD : b ∈ diagU hF := ⟨h01, h02, h10, h12, h20, h21⟩
      have hd := diagU_det hF hbD
      have h00 : matU b 0 0 ≠ 0 := fun h => by
        rw [h] at hd
        simp at hd
      refine Or.inr ⟨hbD, fun h => ?_⟩
      have h' : (b * swapU hF : SU3F p F) ∈ diagU hF := h
      have := h'.1
      simp [matU_mul, matU_swapU, swapMat, Matrix.mul_apply, Fin.sum_univ_three, h01, h02] at this
      exact h00 this
    · have hbD : b ∉ diagU hF := fun h => by
        have hd := diagU_det hF h
        rw [h00] at hd
        simp at hd
      refine Or.inl ⟨?_, hbD⟩
      show b * swapU hF ∈ diagU hF
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [matU_mul, matU_swapU, swapMat, Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h02,
          h12, h20, h21]
  exact this

theorem index_diagU [Finite F] (hF : Nat.card F = p ^ 2) :
    (diagU hF).index * (p + 1) ^ 2 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
  have h := (diagU hF).index_mul_card
  rw [card_diagU hF, card_su3F hF] at h
  exact h

theorem odd_index_monoU [Finite F] (hF : Nat.card F = p ^ 2) (hp : p % 4 = 3) :
    Odd (monoU hF).index := by
  have h1 := Subgroup.relIndex_mul_index (diagU_le_monoU hF)
  rw [relIndex_diagU_monoU hF] at h1
  have hi := index_diagU hF
  have hpp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := ⟨p / 4, by omega⟩
  have hp1 : 1 ≤ p := by omega
  have hpos : 0 < (p + 1) ^ 2 := by positivity
  have hp2' : p ≤ p ^ 2 := by nlinarith
  have hp1' : 1 ≤ p ^ 2 := by nlinarith
  have hp3' : 1 ≤ p ^ 3 := Nat.one_le_pow _ _ (by omega)
  have key : (diagU hF).index = p ^ 3 * ((p - 1) * (p ^ 2 - p + 1)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hi]
    zify [hp1, hp2', hp1', hp3']
    ring
  have h2 : 2 * (monoU hF).index = p ^ 3 * ((p - 1) * (p ^ 2 - p + 1)) := by
    rw [← key, ← h1]
  have h3 : (monoU hF).index = p ^ 3 * ((2 * k + 1) * (p ^ 2 - p + 1)) := by
    have : p - 1 = 2 * (2 * k + 1) := by omega
    rw [this] at h2
    linarith
  rw [h3]
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  refine hodd.pow.mul (Odd.mul ⟨k, rfl⟩ ?_)
  have hp' : p ^ 2 - p = p * (p - 1) := by rw [sq, Nat.mul_sub_one]
  rw [hp']
  exact (Nat.even_mul_pred_self p).add_one

end CFSG.Quasithin.E2P.Asc80

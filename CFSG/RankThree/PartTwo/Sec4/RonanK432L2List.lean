module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432PRank
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.KFacts.K72List
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts

theorem pRank_psl2_le_one {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3)
    (h4 : 4 ≤ Nat.card F) : CFSG.Open.pRank 3 (⊤ : Subgroup (PSL2 F)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have := card_le_of_isCyclic_sylow (X := PSL2 F) (p := 3) (isCyclic_sylow_three_psl2 h3 h4) hE.2
  simpa using this

theorem listRow_psl2_of_char_ne_three {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3)
    (h4 : 4 ≤ Nat.card F) : ListRow (PSL2 F) :=
  listRow_of_pRank_le_one (pRank_psl2_le_one h3 h4)

section CharThree

variable {F : Type} [Field F]

@[expose] def uSL (x : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def tSL (s : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem uSL_mul (x y : F) : uSL x * uSL y = uSL (x + y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uSL_zero : uSL (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem tSL_mul_uSL (s : Fˣ) (x : F) : tSL s * uSL x = uSL ((s : F) ^ 2 * x) * tSL s := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, tSL, Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_comm, mul_left_comm,
      mul_assoc]

@[expose] def uP (x : F) : PSL2 F := QuotientGroup.mk (uSL x)

@[expose] def tP (s : Fˣ) : PSL2 F := QuotientGroup.mk (tSL s)

theorem uP_add (x y : F) : uP (x + y) = uP x * uP y := by
  simp only [uP, ← QuotientGroup.mk_mul, uSL_mul]

theorem uP_zero : uP (0 : F) = 1 := by
  simp [uP, uSL_zero]

theorem tP_mul_uP (s : Fˣ) (x : F) : tP s * uP x * (tP s)⁻¹ = uP ((s : F) ^ 2 * x) := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [tP, uP, ← QuotientGroup.mk_mul, tSL_mul_uSL]

theorem uP_injective : Function.Injective (uP : F → PSL2 F) := by
  intro x y h
  have h1 : (uSL x)⁻¹ * uSL y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    QuotientGroup.eq.mp h
  have hx : (uSL x)⁻¹ = uSL (-x) :=
    inv_eq_of_mul_eq_one_right (by rw [uSL_mul, add_neg_cancel, uSL_zero])
  rw [hx, uSL_mul] at h1
  obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp h1
  have e00 := congrFun (congrFun hr 0) 0
  have e01 := congrFun (congrFun hr 0) 1
  simp [uSL] at e00 e01
  linear_combination e01

@[expose] def uHom (F : Type) [Field F] : Multiplicative F →* PSL2 F where
  toFun x := uP (Multiplicative.toAdd x)
  map_one' := uP_zero
  map_mul' x y := uP_add (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem uP_zsmul (x : F) (k : ℤ) : (uP x) ^ k = uP (k • x) := by
  have := map_zpow (uHom F) (Multiplicative.ofAdd x) k
  simpa [uHom, ofAdd_zsmul] using this.symm

variable [Finite F]

theorem listRow_psl2_of_char_three [CharP F 3] (h9 : 9 ≤ Nat.card F) : ListRow (PSL2 F) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨e, he⟩ := FiniteField.card F 3
  have hcard : Nat.card F = 3 ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, he.2]
  set P : Subgroup (PSL2 F) := (uHom F).range with hPdef
  have hinj : Function.Injective (uHom F) := fun x y h => by
    have := uP_injective h
    exact Multiplicative.toAdd.injective this
  have hP : Nat.card P = 3 ^ (e : ℕ) := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  have hS : ¬ 3 ^ ((e : ℕ) + 1) ∣ Nat.card (PSL2 F) := by
    have hodd : IsOddPrimePower (Nat.card F) := ⟨3, e, Nat.prime_three, by decide, e.pos, hcard⟩
    have hform := psl2_card_formula F hodd
    rw [hform, hcard]
    set q : ℕ := 3 ^ (e : ℕ) with hq
    have hq3 : 3 ∣ q := dvd_pow_self 3 e.ne_zero
    have hqodd : Odd q := Odd.pow (by decide)
    have hq2 : 2 ∣ q ^ 2 - 1 := by
      have : Odd (q ^ 2) := hqodd.pow
      obtain ⟨m, hm⟩ := this
      exact ⟨m, by omega⟩
    rw [Nat.mul_div_assoc q hq2]
    intro hdvd
    have hM : 3 ∣ (q ^ 2 - 1) / 2 := by
      rw [pow_succ] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) _) hdvd
    have h2M : q ^ 2 - 1 = 2 * ((q ^ 2 - 1) / 2) := (Nat.mul_div_cancel' hq2).symm
    have h3sq : 3 ∣ q ^ 2 := dvd_pow hq3 (by norm_num)
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    obtain ⟨t, ht⟩ := hM
    omega
  obtain ⟨s, hs⟩ : ∃ s : Fˣ, s ^ 4 ≠ 1 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    refine ⟨g, fun h4 => ?_⟩
    have h1 : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    rw [Nat.card_units] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h4
    have h3 : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    omega
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  refine not_weaklyClosed_of_sylow_witness (e : ℕ) P hP hS (fun q hq hqo => ?_) hz
  obtain ⟨x, rfl⟩ := hq
  have hx : Multiplicative.toAdd x ≠ 0 := by
    intro h0
    have : uHom F x = 1 := by simp [uHom, h0, uP_zero]
    rw [this, orderOf_one] at hqo
    omega
  refine ⟨tP s, ?_, ?_⟩
  · have : tP s * uHom F x * (tP s)⁻¹ = uP ((s : F) ^ 2 * Multiplicative.toAdd x) := tP_mul_uP s _
    rw [this]
    show uP _ * uP _ = uP _ * uP _
    rw [← uP_add, ← uP_add, add_comm]
  · intro hmem
    have : tP s * uHom F x * (tP s)⁻¹ = uP ((s : F) ^ 2 * Multiplicative.toAdd x) := tP_mul_uP s _
    rw [this] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (uHom F x) ^ k = uP ((k : F) * Multiplicative.toAdd x) := by
      show (uP (Multiplicative.toAdd x)) ^ k = _
      rw [uP_zsmul]
      simp [zsmul_eq_mul]
    rw [hk'] at hk
    have h2 := uP_injective hk
    have h3 : (k : F) = (s : F) ^ 2 := mul_right_cancel₀ hx h2
    have h4 : (s : F) ^ 4 = 1 := by
      have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
      have hkF : (k : F) = ((k % 3 : ℤ) : F) := by
        have := Int.emod_add_mul_ediv k 3
        calc (k : F) = ((k % 3 + 3 * (k / 3) : ℤ) : F) := by rw [this]
          _ = ((k % 3 : ℤ) : F) := by push_cast; rw [h3F]; ring
      have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hsne : (s : F) ≠ 0 := s.ne_zero
      rcases hr with hr | hr | hr
      · rw [hr] at hkF
        have : (s : F) ^ 2 = 0 := by rw [← h3, hkF]; simp
        exact absurd (pow_eq_zero_iff (by norm_num) |>.mp this) hsne
      · rw [hr] at hkF
        have : (s : F) ^ 2 = 1 := by rw [← h3, hkF]; simp
        calc (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
          _ = 1 := by rw [this]; norm_num
      · rw [hr] at hkF
        have h2 : ((2 : ℤ) : F) = -1 := by
          push_cast
          linear_combination h3F
        have : (s : F) ^ 2 = -1 := by rw [← h3, hkF, h2]
        calc (s : F) ^ 4 = ((s : F) ^ 2) ^ 2 := by ring
          _ = 1 := by rw [this]; norm_num
    exact hs (Units.ext (by simpa using h4))

end CharThree

end CFSG.RankThree.PartTwo.Sec4.RonanK432

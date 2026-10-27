module

public import CFSG.Dihedral.Glauberman.DicksonMaxExist
public import CFSG.Quasithin.H13.QRCPairedBorel
public import CFSG.Quasithin.H13.QRCPairedRank

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.ShultStronglyClosedTI
  CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped MatrixGroups

section Matrices

variable {k : Type} [Field k]

@[expose] def sl2LowerUnipotent (s : k) : SL(2, k) :=
  ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_sl2LowerUnipotent (s : k) :
    ((sl2LowerUnipotent s : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; s, 1] := rfl

theorem coe_sl2UpperUnipotent' (x : k) :
    ((sl2UpperUnipotent x : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![1, x; 0, 1] := rfl

variable [CharP k 2]

theorem sl2LowerUnipotent_sq (s : k) : sl2LowerUnipotent s * sl2LowerUnipotent s = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2LowerUnipotent, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem coe_upper_mul_lower {t : k} (ht : t ≠ 0) :
    ((sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) =
      !![0, t; t⁻¹, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2LowerUnipotent, coe_sl2UpperUnipotent',
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_inv_cancel₀ ht, CharTwo.add_self_eq_zero]

theorem upper_mul_lower_pow_three {t : k} (ht : t ≠ 0) :
    (sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ : SL(2, k)) ^ 3 = 1 := by
  ext i j
  rw [pow_succ, pow_succ, pow_one, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_upper_mul_lower ht, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [mul_inv_cancel₀ ht, inv_mul_cancel₀ ht, CharTwo.add_self_eq_zero]

theorem upper_mul_lower_ne_one {t : k} (ht : t ≠ 0) :
    (sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ : SL(2, k)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  simp only [coe_upper_mul_lower ht] at h1
  simp at h1

theorem upper_mul_lower_not_mem_borel {t : k} (ht : t ≠ 0) :
    (sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ : SL(2, k)) ∉ sl2Borel k := by
  intro h
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff] at h
  change ((sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ : SL(2, k)) :
    Matrix (Fin 2) (Fin 2) k) 1 0 = 0 at h
  rw [coe_upper_mul_lower ht] at h
  simp [ht] at h

end Matrices

section Groups

variable {G : Type*} [Group G]

theorem eq_of_mem_zpowers_of_orderOf_two {e y : G} (he : orderOf e = 2)
    (hy : y ∈ zpowers e) (hy1 : y ≠ 1) : y = e := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, he] at hy1 ⊢
  have h1 : j % (2 : ℕ) = 0 ∨ j % (2 : ℕ) = 1 := by omega
  rcases h1 with h | h
  · rw [h, zpow_zero] at hy1
    exact absurd rfl hy1
  · rw [h, zpow_one]

end Groups

section Dihedral

variable {A : Type*} [Group A] [Finite A] {k : Type} [Field k] [CharP k 2] {K₁ : Subgroup A}

theorem paired_dihedral {θ₁ : K₁ ≃* SL(2, k)} {S B E₁ : Subgroup A}
    (hSK₁ : S ⊓ K₁ = stdSub θ₁ (sl2UpperUnipotentSubgroup k))
    (hBK₁ : B ⊓ K₁ = stdSub θ₁ (sl2Borel k))
    (hE₁U : E₁ ≤ stdSub θ₁ (sl2UpperUnipotentSubgroup k)) (hE₁2 : Nat.card E₁ = 2) :
    ∃ (x₁ : A) (L₁ : Subgroup A), x₁ ∈ K₁ ∧ L₁ = E₁ ⊔ conjugate E₁ x₁ ∧ x₁ ∈ L₁ ∧ L₁ ≤ K₁ ∧
      Nonempty (L₁ ≃* DihedralGroup 3) ∧ B ⊓ L₁ = E₁ ∧ S ⊓ L₁ = E₁ ∧
      IsSylowOf 2 (S ⊓ L₁) L₁ ∧ kerIn (B ⊓ L₁) L₁ = ⊥ ∧ inSubgroup (pCore 2) L₁ = ⊥ ∧
      inSubgroup (pCore 2) (B ⊓ L₁) = S ⊓ L₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ū := sl2UpperUnipotentSubgroup k with hŪ
  have : Nontrivial E₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE₁2]; norm_num)
  obtain ⟨⟨e, heE⟩, he1⟩ := exists_ne (1 : E₁)
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  have heU : e ∈ stdSub θ₁ Ū := hE₁U heE
  obtain ⟨heK, heU'⟩ := mem_stdSub.1 heU
  obtain ⟨t, ht⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).1 heU'
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply he1'
    have h1 : θ₁ ⟨e, heK⟩ = 1 := by rw [ht, sl2UpperUnipotent_zero]
    exact congrArg Subtype.val (θ₁.map_eq_one_iff.1 h1)
  have hee : e * e = 1 := stdSub_upperUnipotent_sq θ₁ heU
  have hoe : orderOf e = 2 := orderOf_eq_prime (by rw [sq, hee]) he1'
  have hE₁z : E₁ = zpowers e := by
    symm
    refine eq_of_le_of_card_ge (zpowers_le.2 heE) ?_
    rw [hE₁2, Nat.card_zpowers, hoe]
  set f : A := ((θ₁.symm (sl2LowerUnipotent t⁻¹) : K₁) : A) with hfdef
  have hfK : f ∈ K₁ := (θ₁.symm _).2
  have hff : f * f = 1 := by
    have h1 := congrArg (fun g => ((θ₁.symm g : K₁) : A)) (sl2LowerUnipotent_sq (k := k) t⁻¹)
    simp only [map_mul, map_one, coe_mul, OneMemClass.coe_one] at h1
    exact h1
  set x₁ := e * f with hx₁
  have hx₁K : x₁ ∈ K₁ := K₁.mul_mem heK hfK
  have hθx : θ₁ ⟨x₁, hx₁K⟩ = sl2UpperUnipotent t * sl2LowerUnipotent t⁻¹ := by
    have h1 : (⟨x₁, hx₁K⟩ : K₁) = ⟨e, heK⟩ * θ₁.symm (sl2LowerUnipotent t⁻¹) := rfl
    rw [h1, map_mul, ht, MulEquiv.apply_symm_apply]
  have hx₁3 : x₁ ^ 3 = 1 := by
    have h1 : θ₁ (⟨x₁, hx₁K⟩ ^ 3) = 1 := by rw [map_pow, hθx, upper_mul_lower_pow_three ht0]
    have h2 := congrArg Subtype.val (θ₁.map_eq_one_iff.1 h1)
    simpa using h2
  have hx₁1 : x₁ ≠ 1 := by
    intro h
    apply upper_mul_lower_ne_one ht0
    rw [← hθx]
    have h1 : (⟨x₁, hx₁K⟩ : K₁) = 1 := Subtype.ext h
    rw [h1, map_one]
  have hox : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1
  have hx₁B : x₁ ∉ stdSub θ₁ (sl2Borel k) := by
    intro h
    obtain ⟨hK', hB'⟩ := mem_stdSub.1 h
    exact upper_mul_lower_not_mem_borel ht0 (hθx ▸ hB')
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hex : e * x₁ * e⁻¹ = x₁⁻¹ := by
    rw [hx₁, heinv, mul_inv_rev, heinv, hfinv]
    calc e * (e * f) * e = (e * e) * f * e := by group
      _ = f * e := by rw [hee, one_mul]
  have hex' : e * x₁⁻¹ * e⁻¹ = x₁ := by
    have h1 : e * x₁⁻¹ * e⁻¹ = (e * x₁ * e⁻¹)⁻¹ := by group
    rw [h1, hex, inv_inv]
  set L₁ := E₁ ⊔ conjugate E₁ x₁ with hL₁
  have hconj_e : x₁⁻¹ * e * x₁ ∈ conjugate E₁ x₁ := by
    rw [mem_conjugate_iff, show x₁ * (x₁⁻¹ * e * x₁) * x₁⁻¹ = e by group]
    exact heE
  have hx₁sq : e * (x₁⁻¹ * e * x₁) = x₁ ^ 2 := by
    calc e * (x₁⁻¹ * e * x₁) = (e * x₁⁻¹ * e⁻¹) * x₁ := by rw [heinv]; group
      _ = x₁ ^ 2 := by rw [hex', sq]
  have hx₁L : x₁ ∈ L₁ := by
    have h2 : x₁ ^ 2 ∈ L₁ := hx₁sq ▸ L₁.mul_mem (mem_sup_left heE) (mem_sup_right hconj_e)
    have h3 : x₁ = (x₁ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hx₁3, one_mul]
    rw [h3]
    exact L₁.pow_mem h2 2
  have heN : zpowers e ≤ normalizer ((zpowers x₁ : Subgroup A) : Set A) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      have h1 : e * x₁ ^ j * e⁻¹ = (e * x₁ * e⁻¹) ^ j := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      rw [h1, hex]
      exact zpow_mem (inv_mem (mem_zpowers x₁)) j
    · obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hy
      have h1 : y = e⁻¹ * (e * y * e⁻¹) * e := by group
      have h2 : e * x₁ ^ j * e⁻¹ = (e * x₁ * e⁻¹) ^ j := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      have h3 : e⁻¹ * x₁ ^ j * e = e * x₁ ^ j * e⁻¹ := by rw [heinv]
      rw [h1, ← hj, h3, h2, hex]
      exact zpow_mem (inv_mem (mem_zpowers x₁)) j
  have hLz : L₁ = zpowers x₁ ⊔ zpowers e := by
    apply le_antisymm
    · refine sup_le (by rw [hE₁z]; exact le_sup_right) fun y hy => ?_
      rw [mem_conjugate_iff] at hy
      have h1 : y = x₁⁻¹ * (x₁ * y * x₁⁻¹) * x₁ := by group
      rw [h1]
      exact mul_mem (mul_mem (mem_sup_left (inv_mem (mem_zpowers x₁)))
        (mem_sup_right (hE₁z ▸ hy))) (mem_sup_left (mem_zpowers x₁))
    · exact sup_le (zpowers_le.2 hx₁L) (zpowers_le.2 (mem_sup_left heE))
  have hinv : ∀ c ∈ zpowers x₁, e * c * e⁻¹ = c⁻¹ := by
    intro c hc
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
    have h1 : e * x₁ ^ j * e⁻¹ = (e * x₁ * e⁻¹) ^ j := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [h1, hex, inv_zpow]
  have heC : e ∉ zpowers x₁ := by
    intro h
    have h1 := orderOf_dvd_of_mem_zpowers h
    rw [hoe, hox] at h1
    norm_num at h1
  obtain ⟨φ⟩ := CFSG.Glauberman.Dickson.nonempty_sup_zpowers_mulEquiv_dihedral (zpowers x₁)
    inferInstance e heC hee hinv
  have hC3 : Nat.card (zpowers x₁) = 3 := by rw [Nat.card_zpowers, hox]
  rw [hC3] at φ
  have hD : Nonempty (L₁ ≃* DihedralGroup 3) := ⟨(MulEquiv.subgroupCongr hLz).trans φ⟩
  have hcardL : Nat.card L₁ = 6 := by
    rw [Nat.card_congr ((MulEquiv.subgroupCongr hLz).trans φ).toEquiv, DihedralGroup.nat_card]
  have hE₁K : E₁ ≤ K₁ := hE₁U.trans (stdSub_le _ _)
  have hL₁K : L₁ ≤ K₁ := by
    refine sup_le hE₁K fun y hy => ?_
    rw [mem_conjugate_iff] at hy
    have h1 : y = x₁⁻¹ * (x₁ * y * x₁⁻¹) * x₁ := by group
    rw [h1]
    exact K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hx₁K) (hE₁K hy)) hx₁K
  have hE₁B : E₁ ≤ B :=
    (hE₁U.trans (stdSub_mono θ₁ upperUnipotent_le_borel)).trans (hBK₁ ▸ inf_le_left)
  have hBL : B ⊓ L₁ = E₁ := by
    refine le_antisymm (fun y hy => ?_) (le_inf hE₁B le_sup_left)
    obtain ⟨hyB, hyL⟩ := mem_inf.1 hy
    rw [hLz, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left (zpowers x₁) (zpowers e)
      heN] at hyL
    obtain ⟨c, hc, d, hd, rfl⟩ := hyL
    have hdE : d ∈ E₁ := hE₁z ▸ hd
    have hcB : c ∈ B := by
      have := B.mul_mem hyB (B.inv_mem (hE₁B hdE))
      rwa [mul_inv_cancel_right] at this
    have hcK : c ∈ K₁ := (zpowers_le.2 hx₁K) hc
    have hcB₁ : c ∈ stdSub θ₁ (sl2Borel k) := hBK₁ ▸ ⟨hcB, hcK⟩
    have hc1 : c = 1 := by
      by_contra hc1
      apply hx₁B
      have h1 : zpowers c = zpowers x₁ := by
        refine eq_of_le_of_card_ge (zpowers_le.2 hc) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hox]
        have h2 : orderOf c ∣ 3 := hox ▸ orderOf_dvd_of_mem_zpowers hc
        rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hc1
        · rw [h]
      have h3 := mem_zpowers x₁
      rw [← h1] at h3
      exact (zpowers_le.2 hcB₁) h3
    show c * d ∈ E₁
    rw [hc1, one_mul]
    exact hdE
  have hSL : S ⊓ L₁ = E₁ := by
    refine le_antisymm ?_ (le_inf (hE₁U.trans (hSK₁ ▸ inf_le_left)) le_sup_left)
    rw [← hBL]
    refine le_inf ?_ inf_le_right
    intro y hy
    have h1 : y ∈ S ⊓ K₁ := ⟨hy.1, hL₁K hy.2⟩
    rw [hSK₁] at h1
    exact (hBK₁ ▸ stdSub_mono θ₁ upperUnipotent_le_borel h1 : y ∈ B ⊓ K₁).1
  have hE₁2' : IsPGroup 2 E₁ := IsPGroup.of_card (n := 1) (by rw [hE₁2, pow_one])
  have hsyl : IsSylowOf 2 E₁ L₁ := by
    refine isSylowOf_iff.2 ⟨le_sup_left, hE₁2', ?_⟩
    have h1 := relIndex_mul_card E₁ L₁
    rw [inf_eq_left.2 (le_sup_left : E₁ ≤ L₁), hE₁2, hcardL] at h1
    have h2 : E₁.relIndex L₁ = 3 := by omega
    rw [h2]
    norm_num
  have hker : kerIn E₁ L₁ = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    by_contra hy1
    have hyE : y ∈ E₁ := by simpa using hy 1 (one_mem L₁)
    have hye : y = e := eq_of_mem_zpowers_of_orderOf_two hoe (hE₁z ▸ hyE) hy1
    have h1 : x₁ * y * x₁⁻¹ ∈ E₁ := hy x₁ hx₁L
    rw [hye] at h1
    have h2 : x₁ * e * x₁⁻¹ = e := by
      refine eq_of_mem_zpowers_of_orderOf_two hoe (hE₁z ▸ h1) fun h => he1' ?_
      have h3 : e = x₁⁻¹ * (x₁ * e * x₁⁻¹) * x₁ := by group
      rw [h3, h, mul_one, inv_mul_cancel]
    have h4 : x₁ * e = e * x₁ := by
      calc x₁ * e = x₁ * e * x₁⁻¹ * x₁ := by group
        _ = e * x₁ := by rw [h2]
    have h5 : e * x₁ * e⁻¹ = x₁ := by rw [← h4, mul_inv_cancel_right]
    rw [hex] at h5
    have h6 : x₁ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [← h5]
      exact inv_mul_cancel x₁
    have h7 := orderOf_dvd_of_pow_eq_one h6
    rw [hox] at h7
    norm_num at h7
  refine ⟨x₁, L₁, hx₁K, rfl, hx₁L, hL₁K, hD, hBL, hSL, hSL ▸ hsyl, hBL ▸ hker,
    inSubgroup_pCore_eq_bot_of_kerIn hsyl le_rfl hker, ?_⟩
  rw [hBL, hSL]
  exact inSubgroup_pCore_eq_of_isSylowOf hsyl le_rfl le_sup_left le_normalizer

end Dihedral

end CFSG.Quasithin.H13.QRC

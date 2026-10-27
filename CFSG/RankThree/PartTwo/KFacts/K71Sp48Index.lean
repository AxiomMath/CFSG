module

public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.Assembly.LowTwoRank
open Matrix
open scoped MatrixGroups

section Unit

variable (F : Type) [Field F]

@[expose] noncomputable def ordThreeUnit : (Matrix (Fin 2) (Fin 2) F)ˣ :=
  SpecialLinearGroup.toGL (ordThreeSL F)

theorem coe_ordThreeUnit : (ordThreeUnit F : Matrix (Fin 2) (Fin 2) F) = ordThreeMat F :=
  rfl

theorem orderOf_ordThreeUnit : orderOf (ordThreeUnit F) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [ordThreeUnit, ← map_pow, ordThreeSL_pow_three, map_one]
  · intro h
    have h1 := congrArg
      (fun u : (Matrix (Fin 2) (Fin 2) F)ˣ => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [coe_ordThreeUnit, Units.val_one] at h1
    simp [ordThreeMat] at h1

end Unit

section Block

variable {F : Type} [Field F] [CharP F 2]

theorem eq_one_or_eq_or_eq_of_commute_ordThreeMat {B : Matrix (Fin 2) (Fin 2) F}
    (hB : B * ordThreeMat F = ordThreeMat F * B) (hdet : B.det = 1) (h3 : B ^ 3 = 1) :
    B = 1 ∨ B = ordThreeMat F ∨ B = ordThreeMat F * ordThreeMat F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e00 := congrFun (congrFun hB 0) 0
  have e01 := congrFun (congrFun hB 0) 1
  simp [ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hc : B 1 0 = -B 0 1 := by
    first
    | linear_combination e00
    | linear_combination -e00
  have he : B 1 1 = B 0 0 - B 0 1 := by
    first
    | linear_combination e01
    | linear_combination -e01
  have hBeq : B = !![B 0 0, B 0 1; -B 0 1, B 0 0 - B 0 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, he]
  generalize B 0 0 = a at hBeq
  generalize B 0 1 = b at hBeq
  subst hBeq
  have hd : a ^ 2 - a * b + b ^ 2 = 1 := by
    rw [Matrix.det_fin_two_of] at hdet
    linear_combination hdet
  have h01 := congrFun (congrFun h3 0) 1
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at h01
  have hab : a * b * (a - b) = 0 := by linear_combination h01 - a * b * (a - b) * h2
  have hsq : ∀ u : F, u ^ 2 = 1 → u = 1 := fun u hu => by
    have h := sub_pow_char (p := 2) u 1
    rw [hu, one_pow, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  rcases mul_eq_zero.mp hab with h | h
  · rcases mul_eq_zero.mp h with ha | hb
    · subst ha
      have hb1 : b = 1 := hsq b (by linear_combination hd)
      subst hb1
      right; left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ordThreeMat]
    · subst hb
      have ha1 : a = 1 := hsq a (by linear_combination hd)
      subst ha1
      left
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · have hab' : a = b := sub_eq_zero.mp h
    subst hab'
    have ha1 : a = 1 := hsq a (by linear_combination hd)
    subst ha1
    right; right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ordThreeMat, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | linear_combination h2
      | linear_combination (-1 : F) * h2

theorem det_block0_of_mem_centralizer {x : StatedSp 2 F}
    (hx : x ∈ Subgroup.centralizer {sp4T F}) :
    (block0 (((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))).det =
      1 := by
  have h3 : (3 : F) ≠ 0 := by
    have h31 : (3 : F) = 1 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h31]
    exact one_ne_zero
  obtain ⟨⟨y1, y2, y3, y4⟩, -⟩ :=
    planeEntries_eq_zero h3 (mul_planeBlock_eq_of_mem_centralizer hx)
  have hsp := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp x.2
  have hd := congrFun (congrFun hsp (.inl 0)) (.inr 0)
  generalize ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = X
    at y1 y2 y3 y4 hd ⊢
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, y1, y2, y3, y4] at hd
  rw [block0, Matrix.det_fin_two_of]
  linear_combination hd

end Block

section Index

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
theorem three_ne_zero_of_charTwo : (3 : F) ≠ 0 := by
  have h31 : (3 : F) = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h2
  rw [h31]
  exact one_ne_zero

theorem card_le_three_mul_card_inf_sp4T (hF : 4 ≤ Nat.card F)
    {E : Subgroup (StatedSp 2 F)} (hE : E ≤ Subgroup.centralizer {sp4T F})
    (hE3 : ∀ y ∈ E, y ^ 3 = 1) :
    Nat.card E ≤
      3 * Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) :
        Subgroup (StatedSp 2 F)) := by
  have h3 : (3 : F) ≠ 0 := three_ne_zero_of_charTwo
  set f : E →* (Matrix (Fin 2) (Fin 2) F)ˣ :=
    (block0Hom F h3).toHomUnits.comp (Subgroup.inclusion hE) with hf
  have hfval : ∀ y : E, ((f y : (Matrix (Fin 2) (Fin 2) F)ˣ) : Matrix (Fin 2) (Fin 2) F) =
      block0 ((((y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) := fun y => rfl
  have hrange : f.range ≤ Subgroup.zpowers (ordThreeUnit F) := by
    rintro _ ⟨y, rfl⟩
    have hy3 : (f y) ^ 3 = 1 := by
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (by simpa using hE3 y y.2)
      rw [this, map_one]
    have hB : ((f y : (Matrix (Fin 2) (Fin 2) F)ˣ) : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
    rw [hfval] at hB
    rcases eq_one_or_eq_or_eq_of_commute_ordThreeMat
        (block0_mul_ordThreeMat h3 (mul_planeBlock_eq_of_mem_centralizer (hE y.2)))
        (det_block0_of_mem_centralizer (hE y.2)) hB with h | h | h
    · have : f y = 1 := Units.ext (by rw [hfval, h, Units.val_one])
      rw [this]
      exact Subgroup.one_mem _
    · have : f y = ordThreeUnit F := Units.ext (by rw [hfval, h, coe_ordThreeUnit F])
      rw [this]
      exact Subgroup.mem_zpowers _
    · have : f y = ordThreeUnit F ^ 2 := Units.ext (by
        rw [hfval, h, Units.val_pow_eq_pow_val, coe_ordThreeUnit F, pow_two])
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  have hcardR : Nat.card f.range ≤ 3 := by
    have h1 := Subgroup.card_le_of_le hrange
    rwa [Nat.card_zpowers, orderOf_ordThreeUnit F] at h1
  have hker : ∀ y : E, f y = 1 →
      (y : StatedSp 2 F) ∈ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) := by
    intro y hy
    have h1 : block0 ((((y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = 1 := by
      rw [← hfval, hy, Units.val_one]
    rw [inSubgroup_perfectResidual_centralizer_sp4T_eq h3 hF]
    exact mem_range_planeSp_one h3 (hE y.2) h1
  have hcardK : Nat.card f.ker ≤
      Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) :
        Subgroup (StatedSp 2 F)) := by
    refine Nat.card_le_card_of_injective
      (fun y : f.ker => (⟨((y : E) : StatedSp 2 F), (y : E).2, hker y y.2⟩ :
        (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) :
          Subgroup (StatedSp 2 F)))) ?_
    intro y z hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) :
      Subgroup (StatedSp 2 F)) => (w : StatedSp 2 F)) hyz
  have hE' : Nat.card E = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hE']
  calc Nat.card f.ker * Nat.card f.range ≤ Nat.card (E ⊓ inSubgroup perfectResidual
        (Subgroup.centralizer {sp4T F}) : Subgroup (StatedSp 2 F)) * 3 :=
      Nat.mul_le_mul hcardK hcardR
    _ = _ := mul_comm _ _

theorem sp4T_not_mem_perfectResidual (hF : 4 ≤ Nat.card F) :
    sp4T F ∉ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) := by
  rw [inSubgroup_perfectResidual_centralizer_sp4T_eq three_ne_zero_of_charTwo hF]
  rintro ⟨B, hB⟩
  have h1 := congrArg (fun g : StatedSp 2 F =>
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inl 0) (.inl 0)) hB
  simp only [coe_planeSp, coe_sp4T] at h1
  simp [planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat] at h1

omit [CharP F 2] [Finite F] in
theorem centralizer_map_mulEquiv {M : Type*} [Group M] (φ : StatedSp 2 F ≃* M) :
    Subgroup.centralizer {φ (sp4T F)} =
      (Subgroup.centralizer {sp4T F}).map φ.toMonoidHom := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact h
  · intro h
    have := congrArg φ h
    rwa [map_mul, map_mul, φ.apply_symm_apply] at this

theorem card_le_three_mul_card_inf_perfectResidual (hF : 4 ≤ Nat.card F) {M : Type*} [Group M]
    (ψ : StatedSp 2 F ≃* M) {x : M} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {E : Subgroup M}
    (hE : E ≤ Subgroup.centralizer {x}) (hE3 : ∀ y ∈ E, y ^ 3 = 1) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) :
      Subgroup M) := by
  obtain ⟨φ, hφ⟩ := exists_mulAut_apply_sp4T_eq (x := ψ.symm x)
    (by rw [← map_pow, hx3, map_one]) (ψ.symm.map_ne_one_iff.mpr hx1)
  set φ' : StatedSp 2 F ≃* M := φ.trans ψ with hφ'
  have hx : φ' (sp4T F) = x := by rw [hφ', MulEquiv.trans_apply, hφ, MulEquiv.apply_symm_apply]
  subst hx
  set E' := E.map φ'.symm.toMonoidHom with hE'
  have hE'C : E' ≤ Subgroup.centralizer {sp4T F} := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hE hy
    rw [centralizer_map_mulEquiv φ', Subgroup.mem_map_equiv] at h1
    exact h1
  have hE'3 : ∀ y ∈ E', y ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    change φ'.symm y ^ 3 = 1
    rw [← map_pow, hE3 y hy, map_one]
  have hmain := card_le_three_mul_card_inf_sp4T hF hE'C hE'3
  have hcE : Nat.card E' = Nat.card E := by
    rw [hE']
    exact Nat.card_congr (E.equivMapOfInjective _ φ'.symm.injective).toEquiv.symm
  have hcI : Nat.card (E' ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) :
      Subgroup (StatedSp 2 F)) =
      Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {φ' (sp4T F)}) :
        Subgroup M) := by
    have h2 : (inSubgroup perfectResidual (Subgroup.centralizer {φ' (sp4T F)})).map
        φ'.symm.toMonoidHom = inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) := by
      rw [centralizer_map_mulEquiv φ', ← map_inSubgroup_perfectResidual, Subgroup.map_map]
      have hid : φ'.symm.toMonoidHom.comp φ'.toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun z => φ'.symm_apply_apply z
      rw [hid, Subgroup.map_id]
    have hmap : (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {φ' (sp4T F)})).map
        φ'.symm.toMonoidHom =
        E' ⊓ inSubgroup perfectResidual (Subgroup.centralizer {sp4T F}) := by
      rw [Subgroup.map_inf_eq _ _ _ φ'.symm.injective, h2]
    rw [← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ φ'.symm.injective).toEquiv.symm
  rw [← hcE, ← hcI]
  exact hmain

theorem not_mem_perfectResidual_centralizer (hF : 4 ≤ Nat.card F) {M : Type*} [Group M]
    (ψ : StatedSp 2 F ≃* M) {x : M} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x ∉ inSubgroup perfectResidual (Subgroup.centralizer {x}) := by
  obtain ⟨φ, hφ⟩ := exists_mulAut_apply_sp4T_eq (x := ψ.symm x)
    (by rw [← map_pow, hx3, map_one]) (ψ.symm.map_ne_one_iff.mpr hx1)
  set φ' : StatedSp 2 F ≃* M := φ.trans ψ with hφ'
  have hx : φ' (sp4T F) = x := by rw [hφ', MulEquiv.trans_apply, hφ, MulEquiv.apply_symm_apply]
  subst hx
  rw [centralizer_map_mulEquiv φ', ← map_inSubgroup_perfectResidual]
  rintro ⟨y, hy, hyx⟩
  have : y = sp4T F := φ'.injective hyx
  subst this
  exact sp4T_not_mem_perfectResidual hF hy

theorem card_inf_perfectResidual_eq_three (hF : 4 ≤ Nat.card F) {M : Type*} [Group M]
    (ψ : StatedSp 2 F ≃* M) {x : M} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {E : Subgroup M}
    (hE : E ≤ Subgroup.centralizer {x}) (hE3 : ∀ y ∈ E, y ^ 3 = 1) (hE9 : Nat.card E = 9)
    (hxE : x ∈ E) :
    Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) : Subgroup M) = 3 := by
  have hle := card_le_three_mul_card_inf_perfectResidual hF ψ hx3 hx1 hE hE3
  have hdvd : Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) :
      Subgroup M) ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) :
      Subgroup M) ≠ 9 := by
    intro h9
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
    have heq : E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h9, hE9])
    have hx' : x ∈ E ⊓ inSubgroup perfectResidual (Subgroup.centralizer {x}) := by
      rw [heq]
      exact hxE
    exact not_mem_perfectResidual_centralizer hF ψ hx3 hx1 hx'.2
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hk'] at hle hne ⊢
  rw [hE9] at hle
  interval_cases k
  · norm_num at hle
  · norm_num
  · norm_num at hne

end Index

end CFSG.RankThree.PartTwo.KFacts

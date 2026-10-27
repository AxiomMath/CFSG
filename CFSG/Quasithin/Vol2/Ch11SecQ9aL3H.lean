module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
  CFSG.ClassicalInvolution.ModelFacts.OddCover

variable {F : Type} [Field F]

@[expose] noncomputable def repP (x : PGL3 F) : GL (Fin 3) F :=
  (ProjGenLinGroup.mk_surjective x).choose

theorem mk_repP (x : PGL3 F) : ProjGenLinGroup.mk (repP x) = x :=
  (ProjGenLinGroup.mk_surjective x).choose_spec

@[expose] noncomputable def ratioP (i i' : Fin 3) (x : PGL3 F) : F :=
  (repP x : Matrix (Fin 3) (Fin 3) F) i i * ((repP x : Matrix (Fin 3) (Fin 3) F) i' i')⁻¹

theorem ratioP_mk (i i' : Fin 3) (g : GL (Fin 3) F) :
    ratioP i i' (ProjGenLinGroup.mk g) =
      (g : Matrix (Fin 3) (Fin 3) F) i i * ((g : Matrix (Fin 3) (Fin 3) F) i' i')⁻¹ := by
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp (mk_repP (ProjGenLinGroup.mk g))
  have e := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at e
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [ratioP, ← e, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.mul_diagonal, mul_inv,
    show ∀ x y z : F, x * z * (y * z⁻¹) = x * y * (z * z⁻¹) from fun x y z => by ring,
    mul_inv_cancel₀ hc0, mul_one]

theorem ratioP_one (i i' : Fin 3) : ratioP i i' (1 : PGL3 F) = 1 := by
  rw [← map_one ProjGenLinGroup.mk, ratioP_mk]
  simp

theorem ratioP_mul [CharP F 2] (i i' : Fin 3) {x y : PGL3 F}
    (hx : x ∈ Subgroup.normalizer (S0P F : Set (PGL3 F)))
    (hy : y ∈ Subgroup.normalizer (S0P F : Set (PGL3 F))) :
    ratioP i i' (x * y) = ratioP i i' x * ratioP i i' y := by
  have hgx := isUpperTriangular_of_mem_normalizer (g := repP x) (by rw [mk_repP]; exact hx)
  have hgy := isUpperTriangular_of_mem_normalizer (g := repP y) (by rw [mk_repP]; exact hy)
  have hxy : x * y = ProjGenLinGroup.mk (repP x * repP y) := by
    rw [map_mul, mk_repP, mk_repP]
  rw [hxy, ratioP_mk, Units.val_mul, mul_apply_self_of_isUpperTriangular hgx hgy i,
    mul_apply_self_of_isUpperTriangular hgx hgy i', ratioP, ratioP, mul_inv]
  ring

variable [Finite F]

theorem exists_ratioP_eq_one [CharP F 2] (hF : Nat.card F = 4) (i i' : Fin 3)
    {E : Subgroup (PGL3 F)} (hE : E ≤ Subgroup.normalizer (S0P F : Set (PGL3 F)))
    (hE9 : Nat.card ↥E = 9) : ∃ e ∈ E, e ≠ 1 ∧ ratioP i i' e = 1 := by
  by_contra hcon
  push Not at hcon
  have hinv : ∀ e ∈ E, ratioP i i' e * ratioP i i' e⁻¹ = 1 := fun e he => by
    rw [← ratioP_mul i i' (hE he) (hE (E.inv_mem he)), mul_inv_cancel, ratioP_one]
  have hinj : Function.Injective (fun e : E => ratioP i i' (e : PGL3 F)) := by
    intro e e' h
    by_contra hne
    have hne' : (e : PGL3 F) * (e' : PGL3 F)⁻¹ ≠ 1 := fun h' =>
      hne (Subtype.ext (mul_inv_eq_one.mp h'))
    apply hcon _ (E.mul_mem e.2 (E.inv_mem e'.2)) hne'
    rw [ratioP_mul i i' (hE e.2) (hE (E.inv_mem e'.2))]
    simp only at h
    rw [h]
    exact hinv _ e'.2
  have := Nat.card_le_card_of_injective _ hinj
  rw [hE9, hF] at this
  omega

omit [Finite F] in
theorem pow_three_mem_S0P (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular) :
    ProjGenLinGroup.mk g ^ 3 ∈ S0P F := by
  rw [← map_pow]
  have hg3 : ((g ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
    rw [pow_three', Units.val_mul, Units.val_mul]
    exact (hg.mul hg).mul hg
  have hd : ∀ i, ((g ^ 3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    intro i
    rw [pow_three', Units.val_mul, Units.val_mul,
      mul_apply_self_of_isUpperTriangular (hg.mul hg) hg,
      mul_apply_self_of_isUpperTriangular hg hg]
    have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
    have hu := pow_card_eq_one' (x := Units.mk0 _ (diag_ne_zero hg i))
    rw [h3] at hu
    have := congrArg Units.val hu
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this
    linear_combination this
  exact mk_mem_S0P hg3 ((hd 0).trans (hd 1).symm) ((hd 1).trans (hd 2).symm)

theorem eq_one_of_mem_S0P_of_mem {E : Subgroup (PGL3 F)} (hE9 : Nat.card ↥E = 9) [CharP F 2]
    {y : PGL3 F} (hyS : y ∈ S0P F) (hyE : y ∈ E) : y = 1 := by
  have hp : IsPGroup 2 (S0P F) := (isSylowTwoOf_projU (K := F)).2.1.map (thetaP F)
  obtain ⟨k, hk⟩ := hp ⟨y, hyS⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  have h9 : orderOf y ∣ 9 := by
    rw [← hE9, ← Subgroup.orderOf_mk y hyE]
    exact orderOf_dvd_natCard _
  rw [hm] at h9
  have hm0 : m = 0 := by
    by_contra h0
    have : 2 ∣ 9 := (dvd_pow_self 2 h0).trans h9
    omega
  rw [hm0, pow_zero] at hm
  exact orderOf_eq_one_iff.mp hm

theorem exists_mem_sc_zero [CharP F 2] (hF : Nat.card F = 4) {E : Subgroup (PGL3 F)}
    (hE : E ≤ Subgroup.normalizer (S0P F : Set (PGL3 F))) (hE9 : Nat.card ↥E = 9) :
    E ⊓ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0)) ≠ ⊥ := by
  obtain ⟨e, heE, he1, hr⟩ := exists_ratioP_eq_one hF 1 2 hE hE9
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective e
  have hN := hE heE
  have hg := isUpperTriangular_of_mem_normalizer hN
  rw [ratioP_mk] at hr
  have h11 := diag_ne_zero hg 1
  have h22 := diag_ne_zero hg 2
  have e12 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    field_simp at hr
    exact hr
  have g10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hg (by decide)
  have g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hg (by decide)
  have g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hg (by decide)
  have he3 : ProjGenLinGroup.mk g ^ 3 = 1 :=
    eq_one_of_mem_S0P_of_mem hE9 (pow_three_mem_S0P hF hg) (E.pow_mem heE 3)
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he3
  obtain ⟨c, hc⟩ := he3
  have e := congrFun (congrFun
    (congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc) 1) 2
  simp [pow_three', Matrix.mul_apply, Fin.sum_univ_three, g10, g20, g21,
    GeneralLinearGroup.coe_scalar, ← e12] at e
  have g12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
    have h3 := three_eq_one (F := F)
    have hX : (g : Matrix (Fin 3) (Fin 3) F) 1 1 ^ 2 * (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
      linear_combination -e - ((g : Matrix (Fin 3) (Fin 3) F) 1 1 ^ 2 *
        (g : Matrix (Fin 3) (Fin 3) F) 1 2) * h3
    exact (mul_eq_zero.mp hX).resolve_left (pow_ne_zero 2 h11)
  intro hbot
  apply he1
  have hmem : ProjGenLinGroup.mk g ∈
      E ⊓ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0)) := by
    refine ⟨heE, mk_mem_sectionCentralizer hF 0 hN (diag_ne_zero hg 0) h11 ?_ ?_⟩
    · intro w hw
      rw [mem_flagSpace] at hw
      have w1 := hw 1 (by simp)
      have w2 := hw 2 (by simp)
      ext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, w1, w2, g10, g20, g21]
    · intro v
      rw [mem_flagSpace]
      intro k hk
      fin_cases k
      · simp at hk
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, g10, g12]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, g20, g21, e12]
  rw [hbot] at hmem
  exact hmem

theorem exists_mem_sc_one [CharP F 2] (hF : Nat.card F = 4) {E : Subgroup (PGL3 F)}
    (hE : E ≤ Subgroup.normalizer (S0P F : Set (PGL3 F))) (hE9 : Nat.card ↥E = 9) :
    E ⊓ sectionCentralizer (Ptheta F 1) (pCoreOf 2 (Ptheta F 1)) ≠ ⊥ := by
  obtain ⟨e, heE, he1, hr⟩ := exists_ratioP_eq_one hF 0 1 hE hE9
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective e
  have hN := hE heE
  have hg := isUpperTriangular_of_mem_normalizer hN
  rw [ratioP_mk] at hr
  have h00 := diag_ne_zero hg 0
  have h11 := diag_ne_zero hg 1
  have e01 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1 := by
    field_simp at hr
    exact hr
  have g10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hg (by decide)
  have g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hg (by decide)
  have g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hg (by decide)
  have he3 : ProjGenLinGroup.mk g ^ 3 = 1 :=
    eq_one_of_mem_S0P_of_mem hE9 (pow_three_mem_S0P hF hg) (E.pow_mem heE 3)
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he3
  obtain ⟨c, hc⟩ := he3
  have e := congrFun (congrFun
    (congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc) 0) 1
  simp [pow_three', Matrix.mul_apply, Fin.sum_univ_three, g10, g20, g21,
    GeneralLinearGroup.coe_scalar, ← e01] at e
  have g01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
    have h3 := three_eq_one (F := F)
    have hX : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 2 * (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by
      linear_combination -e - ((g : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 2 *
        (g : Matrix (Fin 3) (Fin 3) F) 0 1) * h3
    exact (mul_eq_zero.mp hX).resolve_left (pow_ne_zero 2 h00)
  intro hbot
  apply he1
  have hmem : ProjGenLinGroup.mk g ∈
      E ⊓ sectionCentralizer (Ptheta F 1) (pCoreOf 2 (Ptheta F 1)) := by
    refine ⟨heE, mk_mem_sectionCentralizer hF 1 hN h00 (diag_ne_zero hg 2) ?_ ?_⟩
    · intro w hw
      rw [mem_flagSpace] at hw
      have w2 := hw 2 (by simp)
      ext k
      fin_cases k <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, w2, g10, g20, g21, g01, e01]
    · intro v
      rw [mem_flagSpace]
      intro k hk
      fin_cases k
      · simp at hk
      · simp at hk
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, g20, g21]
  rw [hbot] at hmem
  exact hmem

theorem exists_mem_sc [CharP F 2] (hF : Nat.card F = 4) (j : Fin 2) {E : Subgroup (PGL3 F)}
    (hE : E ≤ Subgroup.normalizer (S0P F : Set (PGL3 F))) (hE9 : Nat.card ↥E = 9) :
    E ⊓ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)) ≠ ⊥ := by
  fin_cases j
  · exact exists_mem_sc_zero hF hE hE9
  · exact exists_mem_sc_one hF hE hE9

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

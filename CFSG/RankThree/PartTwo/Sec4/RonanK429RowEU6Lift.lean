module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowEU6Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Model
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace U6

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open Matrix
open scoped Matrix

@[expose, reducible] noncomputable def S6 : Subgroup (GL (Fin 6) F4) := gramSU uData M6

@[expose] noncomputable def eK : F4c ≃+* F4 := F4c.equivGF

@[expose] noncomputable def Φ : Matrix (Fin 6) (Fin 6) F4 ≃+* Matrix (Fin 6) (Fin 6) F4c :=
  eK.symm.mapMatrix

theorem Φ_apply (A : Matrix (Fin 6) (Fin 6) F4) : Φ A = A.map eK.symm := rfl

theorem Φ_symm_apply (Y : Matrix (Fin 6) (Fin 6) F4c) : Φ.symm Y = Y.map eK := rfl

theorem bar_eq (c : F4) : uData.bar c = c * c := by
  rw [UnitaryFieldData.bar_apply, pow_one, sq]

theorem Φ_transpose (A : Matrix (Fin 6) (Fin 6) F4) : Φ Aᵀ = (Φ A)ᵀ := by
  rw [Φ_apply, Φ_apply, Matrix.transpose_map]

theorem Φ_map_bar (A : Matrix (Fin 6) (Fin 6) F4) :
    Φ (A.map uData.bar) = (Φ A).map (fun c => c * c) := by
  ext i j
  simp only [Φ_apply, Matrix.map_apply, bar_eq, map_mul]

theorem uni_of_mem_GU6 {A : GL (Fin 6) F4} (hA : A ∈ GU6) :
    Uni (Φ (A : Matrix (Fin 6) (Fin 6) F4)) := by
  have h := mem_primeFormUnitary.mp hA
  rw [M6_eq_one, Matrix.mul_one] at h
  unfold Uni
  rw [← Φ_map_bar, ← Φ_transpose, ← map_mul, h, map_one]

theorem Φ_scalar (c : F4) : Φ (Matrix.scalar (Fin 6) c) = Matrix.scalar (Fin 6) (eK.symm c) := by
  ext i j
  simp only [Φ_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

@[expose] noncomputable def toGL (Y Yi : Matrix (Fin 6) (Fin 6) F4c) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1) :
    GL (Fin 6) F4 :=
  ⟨Φ.symm Y, Φ.symm Yi, by rw [← map_mul, h1, map_one], by rw [← map_mul, h2, map_one]⟩

theorem Φ_toGL (Y Yi : Matrix (Fin 6) (Fin 6) F4c) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1) :
    Φ ((toGL Y Yi h1 h2 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Y :=
  Φ.apply_symm_apply Y

theorem toGL_mem (Y Yi : Matrix (Fin 6) (Fin 6) F4c) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hU : Uni Y) (hd : Y.det = 1) : toGL Y Yi h1 h2 ∈ S6 := by
  rw [mem_gramSU, M6_eq_one, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · apply Φ.injective
    rw [map_mul, Φ_transpose, Φ_map_bar, Φ_toGL, map_one]
    exact hU
  · show (Φ.symm Y).det = 1
    rw [Φ_symm_apply, show Y.map eK = (eK : F4c →+* F4).mapMatrix Y from rfl,
      ← RingHom.map_det, hd, map_one]

noncomputable def y7G : GL (Fin 6) F4 := toGL y7C y7Ci y7C_mul_y7Ci y7Ci_mul_y7C

noncomputable def y11G : GL (Fin 6) F4 := toGL y11C y11Ci y11C_mul_y11Ci y11Ci_mul_y11C

noncomputable def y5G : GL (Fin 6) F4 := toGL y5C y5Ci y5C_mul_y5Ci y5Ci_mul_y5C

theorem det_eq_one_of_pow {Y : Matrix (Fin 6) (Fin 6) F4c} {r : ℕ} (hY : Y ^ r = 1)
    (hr : ∀ c : F4c, c ^ r = 1 → c = 1) : Y.det = 1 :=
  hr _ (by rw [← Matrix.det_pow, hY, Matrix.det_one])

theorem y7G_mem : y7G ∈ S6 :=
  toGL_mem _ _ _ _ y7C_uni (det_eq_one_of_pow y7C_pow f4c_pow_seven)

theorem y11G_mem : y11G ∈ S6 :=
  toGL_mem _ _ _ _ y11C_uni (det_eq_one_of_pow y11C_pow f4c_pow_eleven)

theorem y5G_mem : y5G ∈ S6 :=
  toGL_mem _ _ _ _ y5C_uni (det_eq_one_of_pow y5C_pow f4c_pow_five)

@[expose] noncomputable def matC : GL (Fin 6) F4 →* Matrix (Fin 6) (Fin 6) F4c :=
  (Φ.toMonoidHom).comp (Units.coeHom (Matrix (Fin 6) (Fin 6) F4))

theorem matC_apply (g : GL (Fin 6) F4) : matC g = Φ (g : Matrix (Fin 6) (Fin 6) F4) := rfl

theorem matC_injective : Function.Injective matC := by
  intro g h e
  exact Units.ext (Φ.injective e)

theorem matC_y7G : matC y7G = y7C := by
  rw [matC_apply]
  exact Φ_toGL _ _ _ _

theorem matC_y11G : matC y11G = y11C := by
  rw [matC_apply]
  exact Φ_toGL _ _ _ _

theorem matC_y5G : matC y5G = y5C := by
  rw [matC_apply]
  exact Φ_toGL _ _ _ _

theorem orderOf_toGL {Y Yi : Matrix (Fin 6) (Fin 6) F4c} {h1 : Y * Yi = 1} {h2 : Yi * Y = 1}
    {r : ℕ} [hr : Fact r.Prime] (hY : Y ^ r = 1) (hY1 : Y ≠ 1) : orderOf (toGL Y Yi h1 h2) = r := by
  refine orderOf_eq_prime (matC_injective ?_) fun h => hY1 ?_
  · rw [map_pow, matC_apply, Φ_toGL, hY, map_one]
  · rw [← Φ_toGL Y Yi h1 h2, ← matC_apply, h, map_one]

theorem orderOf_y7G : orderOf y7G = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_toGL y7C_pow y7C_ne_one

theorem orderOf_y11G : orderOf y11G = 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_toGL y11C_pow y11C_ne_one

theorem orderOf_y5G : orderOf y5G = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_toGL y5C_pow y5C_ne_one

theorem card_S6 : Nat.card S6 = 27590492160 := by
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int uData (n := 6) (by norm_num)
  have hp : ∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 841995 := by decide
  rw [hp] at hc
  have heq : CFSG.Open.StatedSU 6 (2 ^ 1) F4 = S6 := by
    rw [show CFSG.Open.StatedSU 6 (2 ^ 1) F4 = unitarySU 2 1 F4 6 from rfl,
      unitarySU_eq_gramSU uData 6]
    show gramSU uData 1 = gramSU uData M6
    rw [M6_eq_one]
  rw [heq] at hc
  norm_num at hc
  exact_mod_cast hc

instance : Finite S6 := Nat.finite_of_card_ne_zero (by rw [card_S6]; norm_num)

theorem exists_conj_pow_eq {r : ℕ} (hr : r.Prime) (hr2 : ¬ r ^ 2 ∣ Nat.card S6)
    {y h : GL (Fin 6) F4} (hy : y ∈ S6) (hh : h ∈ S6) (hyo : orderOf y = r)
    (hho : orderOf h = r) : ∃ t ∈ S6, ∃ m : ℤ, (t⁻¹ * h * t) ^ m = y := by
  haveI : Fact r.Prime := ⟨hr⟩
  set y' : S6 := ⟨y, hy⟩
  set h' : S6 := ⟨h, hh⟩
  have hy'o : orderOf y' = r := by rw [← Subgroup.orderOf_coe]; exact hyo
  have hh'o : orderOf h' = r := by rw [← Subgroup.orderOf_coe]; exact hho
  have hsyl : ∀ z : S6, orderOf z = r →
      IsPGroup r (Subgroup.zpowers z) ∧ ¬ r ∣ (Subgroup.zpowers z).index := by
    intro z hz
    refine ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), fun hi => ?_⟩
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers z)
    rw [Nat.card_zpowers, hz] at hmul
    apply hr2
    rw [← hmul, pow_two]
    exact Nat.mul_dvd_mul_left r hi
  obtain ⟨hPy, hPyi⟩ := hsyl y' hy'o
  obtain ⟨hPh, hPhi⟩ := hsyl h' hh'o
  let SY : Sylow r S6 := hPy.toSylow hPyi
  let SH : Sylow r S6 := hPh.toSylow hPhi
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq S6 SY SH
  have hmap : Subgroup.zpowers h' = (Subgroup.zpowers y').map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • SY : Sylow r S6) : Subgroup S6) = (SH : Subgroup S6) := by rw [hx]
    rw [Sylow.coe_subgroup_smul] at h1
    exact h1.symm
  have hmem : h' ∈ (Subgroup.zpowers y').map (MulAut.conj x).toMonoidHom :=
    hmap ▸ Subgroup.mem_zpowers h'
  obtain ⟨u, hu, hhu⟩ := hmem
  have hhu' : h' = x * u * x⁻¹ := by rw [← hhu]; rfl
  have hu_ord : orderOf u = r := by
    have : orderOf h' = orderOf u := by
      rw [hhu']
      exact orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective u
    rw [← this, hh'o]
  have hyu : y' ∈ Subgroup.zpowers u := by
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers y' := (Subgroup.zpowers_le).mpr hu
    have hc : Nat.card (Subgroup.zpowers y') ≤ Nat.card (Subgroup.zpowers u) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hy'o, hu_ord]
    rw [Subgroup.eq_of_le_of_card_ge hle hc]
    exact Subgroup.mem_zpowers y'
  obtain ⟨m, hm⟩ := hyu
  refine ⟨x, x.2, m, ?_⟩
  have hux : u = x⁻¹ * h' * x := by rw [hhu']; group
  have h2 : (x⁻¹ * h' * x) ^ m = y' := by rw [← hux]; exact hm
  have h3 := congrArg Subtype.val h2
  rwa [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h3

theorem units_pow_three (c : F4ˣ) : c ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact pow_three_F4 c.ne_zero

theorem scalar_comm (c : F4ˣ) (x : GL (Fin 6) F4) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin 6) c :=
  (commute_scalar c x).eq.symm

theorem exists_lift_commute (A : GU6) {g : P6} (hg : conj6 A g = g) {m : ℕ} (hm : g ^ m = 1) :
    ∃ h : gramSU uData M6, (QuotientGroup.mk h : P6) = g ^ 3 ∧ h ^ m = 1 ∧
      (A : GL (Fin 6) F4) * h = h * A := by
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  have h1 := hg
  rw [primeFormConjHom_mk] at h1
  obtain ⟨c, -, -, hc⟩ := QuotientGroup.eq.mp h1
  have h3 : (QuotientGroup.mk (g' ^ m) : P6) = 1 := by rw [QuotientGroup.mk_pow, hm]
  rw [QuotientGroup.eq_one_iff] at h3
  obtain ⟨d, -, -, hd⟩ := h3
  set G := (g' : GL (Fin 6) F4) with hG
  set Ag := (A : GL (Fin 6) F4) with hAgdef
  have hc' : (Ag * G * Ag⁻¹)⁻¹ * G = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← hc]
    rfl
  have hAG : Ag * G * Ag⁻¹ = G * (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by
    calc Ag * G * Ag⁻¹ = G * ((Ag * G * Ag⁻¹)⁻¹ * G)⁻¹ := by group
      _ = G * (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by rw [hc']
  have hcs : Commute G (Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹ :=
    ((show Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) c) G from scalar_comm c G).inv_left).symm
  have hs3 : ((Matrix.GeneralLinearGroup.scalar (Fin 6) c)⁻¹) ^ 3 = 1 := by
    rw [inv_pow, ← map_pow, units_pow_three, map_one, inv_one]
  have hA3 : Ag * G ^ 3 * Ag⁻¹ = G ^ 3 := by
    rw [← conj_pow, hAG, hcs.mul_pow, hs3]
    exact mul_one _
  refine ⟨g' ^ 3, by rw [QuotientGroup.mk_pow], ?_, ?_⟩
  · apply Subtype.ext
    have hpow : ((g' ^ 3) ^ m : gramSU uData M6) = (g' ^ m) ^ 3 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 3 m]
    rw [hpow, Subgroup.coe_pow, hd, ← map_pow, units_pow_three, map_one, Subgroup.coe_one]
  · rw [Subgroup.coe_pow]
    calc Ag * G ^ 3 = Ag * G ^ 3 * Ag⁻¹ * Ag := by group
      _ = G ^ 3 * Ag := by rw [hA3]

end U6

end CFSG.RankThree.PartTwo.Sec4.RonanK429E

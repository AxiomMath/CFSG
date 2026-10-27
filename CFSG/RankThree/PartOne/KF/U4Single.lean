module

public import CFSG.RankThree.PartOne.KF.U4Act
public import CFSG.RankThree.PartOne.KF.U4Ambient
public import CFSG.RankThree.PartOne.KF.U4Group

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec12Three
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
open scoped commutatorElement

namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

@[expose] noncomputable def blkG {a b : Fin 4} (hab : a ≠ b) : Subgroup G :=
  ((blk C.hU hab).subgroupOf (unitarySU 2 f K 4)).map C.phi

theorem blkG_le_L {a b : Fin 4} (hab : a ≠ b) : C.blkG hab ≤ L := by
  rintro _ ⟨g, -, rfl⟩
  exact C.phi_mem_L g

noncomputable def blkGEquiv {a b : Fin 4} (hab : a ≠ b) : ↥(C.blkG hab) ≃* ↥(blk C.hU hab) :=
  (Subgroup.equivMapOfInjective _ C.phi C.phi_injective).symm.trans
    (Subgroup.subgroupOfEquivOfLe (blk_le_unitarySU hab))

structure Refl (C : U4Ctx p A c L E f K) extends C.PermData where
  a : Fin 4
  b : Fin 4
  hab : a ≠ b
  hτ' : τ = Equiv.swap a b

namespace Refl

variable {C} (R : C.Refl)

abbrev w : G := C.phi R.g

theorem hg : C.phi R.g = R.w := rfl

theorem hτ : NormPerm p (R.g : GL (Fin 4) K) (Equiv.swap R.a R.b) := R.hτ' ▸ R.hperm

@[expose] def t : MulAut E := R.toPermData.t

theorem w_mem_L : R.w ∈ L := C.phi_mem_L R.g

theorem conj_phi (x : unitarySU 2 f K 4) (i : ℤ) :
    R.w * (C.phi x * c ^ i) * R.w⁻¹ = C.phi (R.g * x * R.g⁻¹) * c ^ i := by
  rw [← R.hg]
  exact C.conj_phi_mul_zpow R.g x i

theorem coe_t_apply (e : E) : ((R.t e : E) : G) = R.w * e * R.w⁻¹ := rfl

theorem mem_fixed_iff {e : G} : e ∈ autFixedInG E R.t ↔ ∃ _ : e ∈ E, R.w * e * R.w⁻¹ = e := by
  unfold autFixedInG autFixed
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨e', he', rfl⟩
    refine ⟨e'.2, ?_⟩
    have hfix : R.t e' = e' := he'
    exact congrArg Subtype.val hfix
  · rintro ⟨he, h⟩
    exact ⟨⟨e, he⟩, Subtype.ext h, rfl⟩

theorem phi_mul_zpow_mem_fixed_iff {x : unitarySU 2 f K 4}
    (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K) (i : ℤ) :
    C.phi x * c ^ i ∈ autFixedInG E R.t ↔ ent (x : GL (Fin 4) K) R.a R.a =
      ent (x : GL (Fin 4) K) R.b R.b := by
  rw [mem_fixed_iff]
  constructor
  · rintro ⟨-, h⟩
    rw [R.conj_phi] at h
    have h1 : C.phi (R.g * x * R.g⁻¹) = C.phi x := mul_right_cancel h
    have h2 : R.g * x * R.g⁻¹ = x := C.phi_injective h1
    have h3 := R.hτ.2 (x : GL (Fin 4) K) hx R.a
    have h4 : ((R.g * x * R.g⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) = (x : GL (Fin 4) K) :=
      congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
    rw [h4, Equiv.swap_apply_left] at h3
    exact h3.symm
  · intro h
    refine ⟨C.phi_mul_zpow_mem hx i, ?_⟩
    rw [R.conj_phi]
    have h2 : R.g * x * R.g⁻¹ = x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine R.hτ.conj_eq hx hx fun m => ?_
      by_cases hma : m = R.a
      · subst hma
        rw [Equiv.symm_swap, Equiv.swap_apply_left]
        exact h
      · by_cases hmb : m = R.b
        · subst hmb
          rw [Equiv.symm_swap, Equiv.swap_apply_right]
          exact h.symm
        · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hma hmb]
    rw [h2]

theorem exists_diag_of_fixed {x : unitarySU 2 f K 4} (hx : (x : GL (Fin 4) K) ∈ torusSU p 4 K)
    (hxab : ent (x : GL (Fin 4) K) R.a R.a = ent (x : GL (Fin 4) K) R.b R.b) :
    ∃ v : Fin 4 → Kˣ, (x : GL (Fin 4) K) = diagU v ∧ v R.a = v R.b := by
  obtain ⟨v, -, -, hv⟩ := mem_torusSU_iff.mp hx
  refine ⟨v, hv.symm, ?_⟩
  rw [← hv] at hxab
  simp only [ent, diagU_val, Matrix.diagonal_apply_eq] at hxab
  exact Units.ext hxab

theorem blkG_le_centralizer :
    C.blkG R.hab ≤ Subgroup.centralizer (autFixedInG E R.t : Set G) := by
  rintro _ ⟨h', hh', rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨huE, -⟩ := R.mem_fixed_iff.mp hu
  obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp huE
  have hxab := (R.phi_mul_zpow_mem_fixed_iff hx i).mp hu
  obtain ⟨v, hvx, hvab⟩ := R.exists_diag_of_fixed hx hxab
  have hh'b : (h' : GL (Fin 4) K) ∈ blk C.hU R.hab := hh'
  have hcomm : x * h' = h' * x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hvx]
    exact (blk_comm_diagU R.hab hvab hh'b).symm
  have h1 : C.phi x * C.phi h' = C.phi h' * C.phi x := by
    rw [← map_mul, ← map_mul, hcomm]
  have h2 : c ^ i * C.phi h' = C.phi h' * c ^ i :=
    (Commute.zpow_left (C.c_comm_phi h') i).eq
  calc C.phi x * c ^ i * C.phi h' = C.phi x * (c ^ i * C.phi h') := by rw [mul_assoc]
    _ = C.phi x * (C.phi h' * c ^ i) := by rw [h2]
    _ = (C.phi x * C.phi h') * c ^ i := by rw [mul_assoc]
    _ = (C.phi h' * C.phi x) * c ^ i := by rw [h1]
    _ = C.phi h' * (C.phi x * c ^ i) := by rw [mul_assoc]

theorem blkG_normalized :
    ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E R.t : Set G), ∀ b' ∈ C.blkG R.hab,
      y * b' * y⁻¹ ∈ C.blkG R.hab := by
  rintro y ⟨hyL, hyC⟩ _ ⟨h', hh', rfl⟩
  obtain ⟨gy, rfl⟩ := C.exists_phi_eq hyL
  have hh'b : (h' : GL (Fin 4) K) ∈ blk C.hU R.hab := hh'
  have hcomm : ∀ x ∈ torusSU p 4 K, ent x R.a R.a = ent x R.b R.b →
      (gy : GL (Fin 4) K) * x = x * (gy : GL (Fin 4) K) := by
    intro x hx hxab
    have hxΓ := C.torus_le x hx
    have hu : C.phi ⟨x, hxΓ⟩ * c ^ (0 : ℤ) ∈ autFixedInG E R.t :=
      (R.phi_mul_zpow_mem_fixed_iff (x := ⟨x, hxΓ⟩) hx 0).mpr hxab
    rw [zpow_zero, mul_one] at hu
    have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hu
    have h2 : C.phi (⟨x, hxΓ⟩ * gy) = C.phi (gy * ⟨x, hxΓ⟩) := by
      rw [map_mul, map_mul]
      exact h1
    exact (congrArg Subtype.val (C.phi_injective h2)).symm
  have hU : (gy : GL (Fin 4) K) ∈ primeFormUnitary C.hU (idGram K 4) :=
    unitarySU_le_primeFormUnitary (n := 4) C.hU gy.2
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have h3 := C.h.three_lt
  have hmem := conj_mem_blk_of_centralizes (h := C.hU) (by omega) hζ R.hab hU hcomm hh'b
  exact ⟨gy * h' * gy⁻¹, hmem, by simp [map_mul, map_inv]⟩

noncomputable def zElt {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) : unitarySU 2 f K 4 :=
  ⟨diagU (torusElt R.a R.b ζ), C.torus_le _ (mem_torusSU_iff.mpr
    ⟨_, (torusElt_mem R.hab hζ.pow_eq_one : torusElt R.a R.b ζ ∈ torusVec p 4 K).1,
      (torusElt_mem R.hab hζ.pow_eq_one : torusElt R.a R.b ζ ∈ torusVec p 4 K).2, rfl⟩)⟩

theorem zElt_mem_torus {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    ((R.zElt hζ : unitarySU 2 f K 4) : GL (Fin 4) K) ∈ torusSU p 4 K :=
  mem_torusSU_iff.mpr ⟨_, (torusElt_mem R.hab hζ.pow_eq_one : torusElt R.a R.b ζ ∈
    torusVec p 4 K).1, (torusElt_mem R.hab hζ.pow_eq_one : torusElt R.a R.b ζ ∈
    torusVec p 4 K).2, rfl⟩

theorem zElt_mem_blk {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    ((R.zElt hζ : unitarySU 2 f K 4) : GL (Fin 4) K) ∈ blk C.hU R.hab := by
  refine diagU_torusElt_mem_blk R.hab ?_
  have : (ζ : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  exact bar_eq_inv_of_pow_eq_one C.hU C.hpq this

theorem phi_zElt_mem_blkG {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) :
    C.phi (R.zElt hζ) ∈ C.blkG R.hab := ⟨R.zElt hζ, R.zElt_mem_blk hζ, rfl⟩

theorem phi_zElt_mem_E {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) : C.phi (R.zElt hζ) ∈ E :=
  (C.phi_mem_E_iff _).mpr (R.zElt_mem_torus hζ)

theorem phi_zElt_ne_one {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) : C.phi (R.zElt hζ) ≠ 1 := by
  intro h1
  have h2 : R.zElt hζ = 1 := C.phi_injective (by rw [h1, map_one])
  have h3 := congrArg (fun y : unitarySU 2 f K 4 => ent (y : GL (Fin 4) K) R.a R.a) h2
  simp only [zElt, ent, diagU_val, Matrix.diagonal_apply_eq, torusElt_apply_left R.hab,
    Subgroup.coe_one, Units.val_one, Matrix.one_apply_eq] at h3
  have h4 : ζ = 1 := Units.ext h3
  have h5 := hζ.pow_ne_one_of_pos_of_lt (l := 1) (by norm_num)
    (by have := C.h.three_lt; omega)
  exact h5 (by rw [h4, one_pow])

theorem exists_decomp_fixed {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {e : G} (he : e ∈ E) :
    ∃ u ∈ autFixedInG E R.t, ∃ i : ℤ, e = u * C.phi (R.zElt hζ) ^ i := by
  obtain ⟨x, hx, m, rfl⟩ := C.exists_decomp he
  obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
  have hodd : Odd p := C.h.prime.eq_two_or_odd'.resolve_left (by have := C.h.three_lt; omega)
  obtain ⟨u', s, hu', hu'ab, hvu⟩ := exists_vec_decomp hodd hζ R.hab (v := v) ⟨hv1, hv2⟩
  have hu'T : diagU u' ∈ torusSU p 4 K := mem_torusSU_iff.mpr ⟨u', hu'.1, hu'.2, rfl⟩
  set u₀ : unitarySU 2 f K 4 := ⟨diagU u', C.torus_le _ hu'T⟩ with hu₀
  have hxu : x = u₀ * R.zElt hζ ^ s := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hu₀]
    rw [← hvx, hvu, ← diagU_mul, ← diagU_pow]
    rfl
  have hu₀ab : ent (u₀ : GL (Fin 4) K) R.a R.a = ent (u₀ : GL (Fin 4) K) R.b R.b := by
    simp only [hu₀, ent, diagU_val, Matrix.diagonal_apply_eq]
    rw [hu'ab]
  refine ⟨C.phi u₀ * c ^ m, (R.phi_mul_zpow_mem_fixed_iff hu'T m).mpr hu₀ab, s, ?_⟩
  have h1 : c ^ m * C.phi (R.zElt hζ) ^ (s : ℤ) = C.phi (R.zElt hζ) ^ (s : ℤ) * c ^ m :=
    (Commute.zpow_zpow (C.c_comm_phi (R.zElt hζ)) m (s : ℤ)).eq
  calc C.phi x * c ^ m = C.phi (u₀ * R.zElt hζ ^ s) * c ^ m := by rw [hxu]
    _ = C.phi u₀ * C.phi (R.zElt hζ) ^ (s : ℤ) * c ^ m := by
      rw [map_mul, map_pow, zpow_natCast]
    _ = C.phi u₀ * (C.phi (R.zElt hζ) ^ (s : ℤ) * c ^ m) := by rw [mul_assoc]
    _ = C.phi u₀ * (c ^ m * C.phi (R.zElt hζ) ^ (s : ℤ)) := by rw [h1]
    _ = (C.phi u₀ * c ^ m) * C.phi (R.zElt hζ) ^ (s : ℤ) := by rw [← mul_assoc]

theorem exists_swap_elt :
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ C.blkG R.hab ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = R.t := by
  obtain ⟨k₀, hk₀, hk₀v⟩ := exists_swap (h := C.hU) R.hab
  set kΓ : unitarySU 2 f K 4 := ⟨k₀, blk_le_unitarySU R.hab hk₀⟩ with hkΓ
  have hzc : ∀ x : unitarySU 2 f K 4, (x : GL (Fin 4) K) ∈ torusSU p 4 K →
      kΓ⁻¹ * R.g * x * (kΓ⁻¹ * R.g)⁻¹ = x := by
    intro x hx
    apply Subtype.ext
    obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
    have hv : v ∈ torusVec p 4 K := ⟨hv1, hv2⟩
    have h1 := R.hτ.conj_diagU hv
    have h2 : k₀ * diagU v * k₀⁻¹ = diagU (v ∘ Equiv.swap R.a R.b) := by
      rw [hk₀v v, mul_inv_cancel_right]
    rw [Equiv.symm_swap, ← h2] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hvx]
    have h3 : (kΓ : GL (Fin 4) K) = k₀ := rfl
    rw [h3]
    calc k₀⁻¹ * (R.g : GL (Fin 4) K) * diagU v * ((R.g : GL (Fin 4) K)⁻¹ * k₀)
        = k₀⁻¹ * ((R.g : GL (Fin 4) K) * diagU v * (R.g : GL (Fin 4) K)⁻¹) * k₀ := by group
      _ = diagU v := by rw [h1]; group
  set zc : G := C.phi (kΓ⁻¹ * R.g) with hzc_def
  have hzcE : ∀ e ∈ E, zc * e * zc⁻¹ = e := by
    intro e he
    obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp he
    rw [hzc_def, C.conj_phi_mul_zpow, hzc x hx]
  have hzcC : zc ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 := hzcE e he
    calc e * zc = (zc * e * zc⁻¹) * zc := by rw [h1]
      _ = zc * e := by group
  have hzcN : zc ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hzcC
  have hkw : C.phi kΓ = R.w * zc⁻¹ := by
    rw [← R.hg, hzc_def]
    simp [map_mul, map_inv]
  have hk : C.phi kΓ ∈ Subgroup.normalizer (E : Set G) := by
    rw [hkw]
    exact Subgroup.mul_mem _ R.hwE (Subgroup.inv_mem _ hzcN)
  have hact : ∀ e ∈ E, C.phi kΓ * e * (C.phi kΓ)⁻¹ = R.w * e * R.w⁻¹ := by
    intro e he
    have hcomm : zc * e = e * zc := (Subgroup.mem_centralizer_iff.mp hzcC e he).symm
    have h2 : zc⁻¹ * e * zc = e := by rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
    calc C.phi kΓ * e * (C.phi kΓ)⁻¹ = R.w * (zc⁻¹ * e * zc) * R.w⁻¹ := by rw [hkw]; group
      _ = R.w * e * R.w⁻¹ := by rw [h2]
  refine ⟨C.phi kΓ, hk, ⟨kΓ, hk₀, rfl⟩, ?_⟩
  refine MulEquiv.ext fun e => Subtype.ext ?_
  exact hact e e.2

theorem autMovedInG_le_blkG : autMovedInG E R.t ≤ C.blkG R.hab := by
  rw [autMovedInG_eq_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨e, rfl⟩
  obtain ⟨x, hx, i, hei⟩ := C.exists_decomp e.2
  obtain ⟨v, hv1, hv2, hvx⟩ := mem_torusSU_iff.mp hx
  have hv : v ∈ torusVec p 4 K := ⟨hv1, hv2⟩
  set η : Kˣ := v R.b * (v R.a)⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, inv_pow, hv1 R.b, hv1 R.a]
    simp
  have hvec : (v ∘ Equiv.swap R.a R.b) * v⁻¹ = torusElt R.a R.b η := by
    funext m
    by_cases hma : m = R.a
    · subst hma
      simp [torusElt_apply_left R.hab, hη]
    · by_cases hmb : m = R.b
      · subst hmb
        simp [torusElt_apply_right R.hab, hη]
      · simp [torusElt_apply_other hma hmb, Equiv.swap_apply_of_ne_of_ne hma hmb]
  have hgen : ((R.t e : E) : G) * (e : G)⁻¹ = C.phi (R.g * x * R.g⁻¹ * x⁻¹) := by
    rw [R.coe_t_apply, hei, R.conj_phi]
    simp only [map_mul, map_inv, mul_inv_rev]
    group
  show ((R.t e : E) : G) * (e : G)⁻¹ ∈ C.blkG R.hab
  rw [hgen]
  refine ⟨R.g * x * R.g⁻¹ * x⁻¹, ?_, rfl⟩
  show (((R.g * x * R.g⁻¹ * x⁻¹ : unitarySU 2 f K 4)) : GL (Fin 4) K) ∈ blk C.hU R.hab
  have hcoe : ((R.g * x * R.g⁻¹ * x⁻¹ : unitarySU 2 f K 4) : GL (Fin 4) K) =
      diagU (torusElt R.a R.b η) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hvx, R.hτ.conj_diagU hv, Equiv.symm_swap, ← diagU_inv, diagU_mul, hvec]
  rw [hcoe]
  refine diagU_torusElt_mem_blk R.hab ?_
  have : (η : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηp, Units.val_one]
  exact bar_eq_inv_of_pow_eq_one C.hU C.hpq this

theorem inf_centralizer_eq (hK : kZero p E R.t = C.blkG R.hab) :
    E ⊓ Subgroup.centralizer (kZero p E R.t : Set G) = autFixedInG E R.t := by
  rw [hK]
  obtain ⟨k, hk, hkB, hkt⟩ := R.exists_swap_elt
  ext e
  constructor
  · rintro ⟨heE, heC⟩
    have h1 : k * e = e * k := Subgroup.mem_centralizer_iff.mp heC k hkB
    have h2 : k * e * k⁻¹ = R.w * e * R.w⁻¹ :=
      congrArg (fun φ : MulAut E => ((φ ⟨e, heE⟩ : E) : G)) hkt
    refine R.mem_fixed_iff.mpr ⟨heE, ?_⟩
    rw [← h2, h1]
    group
  · intro he
    refine Subgroup.mem_inf.mpr ⟨(R.mem_fixed_iff.mp he).1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_
    exact (Subgroup.mem_centralizer_iff.mp (R.blkG_le_centralizer hb') e he).symm

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  have h1 : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
    Subgroup.map_center_eq e
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center B := by
    rw [← h1]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (hx'.trans (map_one e).symm))

theorem kZero_eq_blkG (hqs : IsQuasisimple ↥(blk C.hU R.hab))
    (hzc : Subgroup.center ↥(blk C.hU R.hab) = ⊥) : kZero p E R.t = C.blkG R.hab := by
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hct : c ∈ autFixedInG E R.t := by
    refine R.mem_fixed_iff.mpr ⟨C.R.c_mem, ?_⟩
    have := C.R.comm R.w R.w_mem_L
    rw [← this]
    group
  refine kZero_eq_of_block C.h C.hE4 R.t hct (C.blkG_le_L R.hab) R.blkG_le_centralizer
    R.blkG_normalized ?_ ?_ (R.phi_zElt_mem_blkG hζ) (R.phi_zElt_mem_E hζ) (R.phi_zElt_ne_one hζ)
    (fun e he => R.exists_decomp_fixed hζ he)
  · exact LocalCores.isQuasisimple_of_mulEquiv (C.blkGEquiv R.hab).symm hqs
  · exact center_eq_bot_of_mulEquiv (C.blkGEquiv R.hab) hzc

end Refl

end U4Ctx

end CFSG.RankThree.PartOne.KFU

module

public import CFSG.Quasithin.H13.ZCentLieCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.ZCentLie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

section Unitriangular

@[expose] def rootSL3 {a b : Fin 3} (hab : a ≠ b) (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨transvection a b t, det_transvection_of_ne a b hab t⟩

theorem rootSL3_mem {a b : Fin 3} (hab : a < b) (t : K) : rootSL3 hab.ne t ∈ unitriangular 3 K := by
  refine ⟨fun i k hki => ?_, fun i => ?_⟩
  · change transvection a b t i k = 0
    rw [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hki), single_apply, zero_add,
      ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd (hki.trans hab) (lt_irrefl _)
  · change transvection a b t i i = 1
    rw [transvection, Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hab (lt_irrefl _)

theorem eq_one_of_unitriangular_of_scalar {n : ℕ} {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ unitriangular n K) (hs : u ∈ scalars n K) : u = 1 := by
  obtain ⟨c, -, hc⟩ := hs
  apply Subtype.ext
  ext i j
  have h0 := hu.2 i
  rw [hc, scalar_apply, diagonal_apply_eq] at h0
  rw [hc, scalar_apply, h0]
  simp [diagonal_apply, Matrix.one_apply]

theorem entry_one_two_eq_zero {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (h : rootSL3 (show (0 : Fin 3) ≠ 1 by decide) 1 * u =
      u * rootSL3 (show (0 : Fin 3) ≠ 1 by decide) 1) :
    (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  have hm := congrArg Subtype.val h
  change (transvection 0 1 1 : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
    (u : Matrix (Fin 3) (Fin 3) K) * transvection 0 1 1 at hm
  have e := congrFun (congrFun hm 0) 2
  have e22 := hu.2 2
  simpa [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, Matrix.one_apply,
    e22] using e

theorem entry_zero_one_eq_zero {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (h : rootSL3 (show (1 : Fin 3) ≠ 2 by decide) 1 * u =
      u * rootSL3 (show (1 : Fin 3) ≠ 2 by decide) 1) :
    (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
  have hm := congrArg Subtype.val h
  change (transvection 1 2 1 : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K) =
    (u : Matrix (Fin 3) (Fin 3) K) * transvection 1 2 1 at hm
  have e := congrFun (congrFun hm 0) 2
  have e00 := hu.2 0
  simpa [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, Matrix.one_apply,
    e00] using e.symm

theorem coe_eq_one_add_of_entries {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (h01 : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h12 : (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    (u : Matrix (Fin 3) (Fin 3) K) = 1 + (u : Matrix (Fin 3) (Fin 3) K) 0 2 • single 0 2 1 := by
  have h10 := hu.1 1 0 (by decide)
  have h20 := hu.1 2 0 (by decide)
  have h21 := hu.1 2 1 (by decide)
  have h0 := hu.2 0
  have h1 := hu.2 1
  have h2 := hu.2 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, h0, h1, h2, h01, h12]

theorem coe_eq_one_add_two {u : SpecialLinearGroup (Fin 2) K} (hu : u ∈ unitriangular 2 K) :
    (u : Matrix (Fin 2) (Fin 2) K) = 1 + (u : Matrix (Fin 2) (Fin 2) K) 0 1 • single 0 1 1 := by
  have h10 := hu.1 1 0 (by decide)
  have h0 := hu.2 0
  have h1 := hu.2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h0, h1]

theorem commute_of_proj {n : ℕ} {u v : SpecialLinearGroup (Fin n) K} (hu : u ∈ unitriangular n K)
    (hv : v ∈ unitriangular n K) (h : proj n K v * proj n K u = proj n K u * proj n K v) :
    v * u = u * v := by
  have h1 : proj n K (v * u * v⁻¹ * u⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 := eq_one_of_unitriangular_of_scalar
    (mul_mem (mul_mem (mul_mem hv hu) (inv_mem hv)) (inv_mem hu)) (proj_eq_one_iff.1 h1)
  calc v * u = (v * u * v⁻¹ * u⁻¹) * (u * v) := by group
    _ = u * v := by rw [h2, one_mul]

end Unitriangular

section Projective

variable [CharP K 2]

omit [CharP K 2] in
theorem exists_smul_of_proj_eq_one {n : ℕ} (A : SpecialLinearGroup (Fin n) K)
    (hA : proj n K A = 1) :
    ∃ ζ : K, ((SpecialLinearGroup.toGL A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ζ • 1 := by
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hA
  refine ⟨c, ?_⟩
  rw [SpecialLinearGroup.coe_GL_coe_matrix, hc, scalar_apply, smul_one_eq_diagonal]

theorem zCentAt_projUnitriangular_two : ZCentAt (projUnitriangular 2 K) := by
  refine zCentAt_of_scalar (n := Fin 2) CharTwo.two_eq_zero SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective (proj 2 K) (proj_surjective 2 K)
    exists_smul_of_proj_eq_one (N := single 0 1 1) (by simp) ?_
  rintro _ ⟨u, hu, rfl⟩ -
  exact ⟨u, _, rfl, by rw [SpecialLinearGroup.coe_GL_coe_matrix]; exact coe_eq_one_add_two hu⟩

theorem zCentAt_projUnitriangular_three : ZCentAt (projUnitriangular 3 K) := by
  refine zCentAt_of_scalar (n := Fin 3) CharTwo.two_eq_zero SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective (proj 3 K) (proj_surjective 3 K)
    exists_smul_of_proj_eq_one (N := single 0 2 1) (by simp) ?_
  rintro _ ⟨u, hu, rfl⟩ hcen
  have h01 : rootSL3 (show (0 : Fin 3) ≠ 1 by decide) (1 : K) * u =
      u * rootSL3 (show (0 : Fin 3) ≠ 1 by decide) 1 :=
    commute_of_proj hu (rootSL3_mem (show (0 : Fin 3) < 1 by decide) 1)
      (hcen _ ⟨_, rootSL3_mem (show (0 : Fin 3) < 1 by decide) 1, rfl⟩).symm
  have h12 : rootSL3 (show (1 : Fin 3) ≠ 2 by decide) (1 : K) * u =
      u * rootSL3 (show (1 : Fin 3) ≠ 2 by decide) 1 :=
    commute_of_proj hu (rootSL3_mem (show (1 : Fin 3) < 2 by decide) 1)
      (hcen _ ⟨_, rootSL3_mem (show (1 : Fin 3) < 2 by decide) 1, rfl⟩).symm
  exact ⟨u, _, rfl, by
    rw [SpecialLinearGroup.coe_GL_coe_matrix]
    exact coe_eq_one_add_of_entries hu (entry_zero_one_eq_zero hu h12)
      (entry_one_two_eq_zero hu h01)⟩

theorem zCentAt_sylow_of_psl {X : Type} [Group X] [Finite X] {n f : ℕ} (hn : n = 2 ∨ n = 3)
    (hf : 1 ≤ f) (h : StatedClassicalModel X .PSL n 2 f) (P : Sylow 2 X) :
    ZCentAt (P : Subgroup X) := by
  obtain ⟨-, L, _, _, hL, ⟨eT⟩⟩ := h
  have : CharP L 2 := finite_field_prime_power_characteristic Nat.prime_two hf hL
  let e : X ≃* projectiveSL n L :=
    eT.trans ((projectiveSpecialLinearGroupEquivStatedProj n L).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n L))
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  have : Finite (projectiveSL n L) := Finite.of_equiv X e.toEquiv
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_projUnitriangular (K := L) 2 (n := n) (by omega)
  refine zCentAt_sylow (P₀ := Q₀) ?_ Q
  rw [hQ₀]
  rcases hn with rfl | rfl
  · exact zCentAt_projUnitriangular_two
  · exact zCentAt_projUnitriangular_three

end Projective

section PGL

variable [CharP K 2]

omit [CharP K 2] in
theorem scalar_injective_three :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) (R := K)) := by
  intro a b hab
  apply Units.ext
  have h := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hab
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h

abbrev pglKer (K : Type) [Field K] : Subgroup ↥(⊤ : Subgroup (GL (Fin 3) K)) :=
  (StatedScalars (Fin 3) K).subgroupOf ⊤

omit [CharP K 2] in
theorem card_pgl3 [Finite K] :
    Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) =
      Nat.card K ^ 3 * (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 3 - 1)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pglKer K)
  have h2 : Nat.card ↥(⊤ : Subgroup (GL (Fin 3) K)) = Nat.card (GL (Fin 3) K) := Subgroup.card_top
  have h3 : Nat.card ↥(pglKer K) = Nat.card Kˣ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_top : StatedScalars (Fin 3) K ≤ ⊤)).toEquiv]
    exact Nat.card_congr
      (MonoidHom.ofInjective (scalar_injective_three (K := K))).toEquiv.symm
  have h4 := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  have h5 : Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have : Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) * Nat.card Kˣ =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) * Nat.card Kˣ := by
      rw [h4, ← h2, h1, h3]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [h5, card_SL_eq (by norm_num : 1 ≤ 3)]
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]

@[expose] def unipGL (K : Type) [Field K] : Subgroup ↥(⊤ : Subgroup (GL (Fin 3) K)) :=
  ((unitriangular 3 K).map SpecialLinearGroup.toGL).subgroupOf ⊤

@[expose] def projUnipGL (K : Type) [Field K] :
    Subgroup (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) :=
  (unipGL K).map (QuotientGroup.mk' (pglKer K))

omit [CharP K 2] in
theorem eq_one_of_mem_unipGL_of_mem_ker {x : ↥(⊤ : Subgroup (GL (Fin 3) K))} (hx : x ∈ unipGL K)
    (hk : x ∈ pglKer K) : x = 1 := by
  obtain ⟨u, hu, hux₀⟩ := hx
  have hux : SpecialLinearGroup.toGL u = (x : GL (Fin 3) K) := hux₀
  obtain ⟨c, hc₀⟩ := hk
  have hc : GeneralLinearGroup.scalar (Fin 3) c = (x : GL (Fin 3) K) := hc₀
  have hs : u ∈ scalars 3 K := by
    refine ⟨c, ?_, ?_⟩
    · have hdet := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
        (A : Matrix (Fin 3) (Fin 3) K).det) (rfl : u = u)
      have h1 : (u : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := by
        have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K))
          (hux.trans hc.symm)
        simpa [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar] using this
      have h2 := u.2
      rw [h1, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at h2
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
    · have := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) (hux.trans hc.symm)
      simpa [SpecialLinearGroup.coe_GL_coe_matrix, GeneralLinearGroup.coe_scalar] using this
  have hu1 := eq_one_of_unitriangular_of_scalar hu hs
  apply Subtype.ext
  rw [← hux, hu1, map_one]
  rfl

omit [CharP K 2] in
theorem exists_sylow_projUnipGL [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    ∃ P : Sylow 2 (StatedProj (⊤ : Subgroup (GL (Fin 3) K))), (P : Subgroup _) = projUnipGL K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pglKer K) with hπ
  have hinj : Function.Injective (π.comp (unipGL K).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π x = 1 := hx
    exact Subtype.ext (eq_one_of_mem_unipGL_of_mem_ker x.2
      ((QuotientGroup.eq_one_iff (N := pglKer K) _).1 h1))
  have hcardU : Nat.card (projUnipGL K) = Nat.card K ^ 3 := by
    have e1 : (π.comp (unipGL K).subtype).range = projUnipGL K := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    have e2 : Nat.card ↥(unipGL K) = Nat.card ↥((unitriangular 3 K).map SpecialLinearGroup.toGL) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
    rw [e2, Nat.card_congr (Subgroup.equivMapOfInjective _ _
      SpecialLinearGroup.toGL_injective).toEquiv.symm, card_unitriangular]
  have hp : IsPGroup 2 (projUnipGL K) := IsPGroup.of_card (n := f * 3) (by
    rw [hcardU, hK, ← pow_mul])
  refine ⟨hp.toSylow fun h2 => ?_, rfl⟩
  have hidx := (projUnipGL K).index_mul_card
  rw [hcardU, card_pgl3] at hidx
  have hq : Nat.card K ^ 3 ≠ 0 := pow_ne_zero _ (Nat.card_pos (α := K)).ne'
  have hidx' : (projUnipGL K).index = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1) := by
    rw [mul_comm] at hidx
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) hidx
  rw [hidx'] at h2
  have hf : f ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := K)
    have h1 : Nat.card K = 1 := by rw [hK, pow_zero]
    exact absurd (Finite.one_lt_card (α := K)) (by rw [h1]; exact lt_irrefl 1)
  have hev : Even (Nat.card K) := by
    rw [hK]
    exact (Nat.even_pow.2 ⟨even_two, hf⟩)
  have ho2 : Odd (Nat.card K ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (Nat.card_pos (α := K)).ne'))
      (hev.pow_of_ne_zero two_ne_zero) odd_one
  have ho3 : Odd (Nat.card K ^ 3 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 hq) (hev.pow_of_ne_zero three_ne_zero) odd_one
  exact (Nat.not_even_iff_odd.2 (ho2.mul ho3)) (even_iff_two_dvd.2 h2)

theorem zCentAt_pgl3 : ZCentAt (projUnipGL K) := by
  refine zCentAt_of_scalar (n := Fin 3) CharTwo.two_eq_zero (⊤ : Subgroup (GL (Fin 3) K)).subtype
    (Subgroup.subtype_injective _) (QuotientGroup.mk' (pglKer K)) (QuotientGroup.mk'_surjective _)
    (fun h hh => ?_) (N := single 0 2 1) (by simp) ?_
  · obtain ⟨c, hc₀⟩ := (QuotientGroup.eq_one_iff (N := pglKer K) h).1 hh
    have hc : GeneralLinearGroup.scalar (Fin 3) c = (h : GL (Fin 3) K) := hc₀
    refine ⟨c, ?_⟩
    change ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [← hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]
  · rintro _ ⟨x, hx, rfl⟩ hcen
    obtain ⟨u, hu, hux₀⟩ := hx
    have hux : SpecialLinearGroup.toGL u = (x : GL (Fin 3) K) := hux₀
    have hroot : ∀ {a b : Fin 3} (hab : a < b),
        rootSL3 hab.ne (1 : K) * u = u * rootSL3 hab.ne 1 := by
      intro a b hab
      set r : ↥(⊤ : Subgroup (GL (Fin 3) K)) :=
        ⟨SpecialLinearGroup.toGL (rootSL3 hab.ne (1 : K)), trivial⟩ with hr
      have hrU : r ∈ unipGL K := ⟨_, rootSL3_mem hab 1, rfl⟩
      have h1 := hcen _ ⟨r, hrU, rfl⟩
      have h2 : r * x * r⁻¹ * x⁻¹ ∈ pglKer K := by
        rw [← QuotientGroup.eq_one_iff (N := pglKer K)]
        simp only [QuotientGroup.mk'_apply] at h1
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, ← h1]
        group
      have hxU : x ∈ unipGL K := ⟨u, hu, hux⟩
      have h3 : r * x * r⁻¹ * x⁻¹ ∈ unipGL K :=
        mul_mem (mul_mem (mul_mem hrU hxU) (inv_mem hrU)) (inv_mem hxU)
      have h4 := eq_one_of_mem_unipGL_of_mem_ker h3 h2
      have h5 : r * x = x * r := by
        calc r * x = (r * x * r⁻¹ * x⁻¹) * (x * r) := by group
          _ = x * r := by rw [h4, one_mul]
      apply SpecialLinearGroup.toGL_injective
      rw [map_mul, map_mul, hux]
      exact congrArg Subtype.val h5
    refine ⟨x, (u : Matrix (Fin 3) (Fin 3) K) 0 2, rfl, ?_⟩
    change ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [← hux, SpecialLinearGroup.coe_GL_coe_matrix]
    exact coe_eq_one_add_of_entries hu
      (entry_zero_one_eq_zero hu (hroot (show (1 : Fin 3) < 2 by decide)))
      (entry_one_two_eq_zero hu (hroot (show (0 : Fin 3) < 1 by decide)))

theorem zCentAt_sylow_of_pgl3 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (h : IsPGLEps3 true (2 ^ f) X) (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨L, _, _, hL, ⟨e⟩⟩ := h
  have : CharP L 2 := finite_field_prime_power_characteristic Nat.prime_two hf hL
  refine zCentAt_sylow_of_mulEquiv e (fun Q => ?_) P
  have : Finite (StatedProj (⊤ : Subgroup (GL (Fin 3) L))) := Finite.of_equiv X e.toEquiv
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_projUnipGL (K := L) hL
  refine zCentAt_sylow (P₀ := Q₀) ?_ Q
  rw [hQ₀]
  exact zCentAt_pgl3

end PGL

end CFSG.Quasithin.H13.ZCentLie

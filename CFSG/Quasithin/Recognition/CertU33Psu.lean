module

public import CFSG.Quasithin.Recognition.CertU33Faithful
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.Open.Catalog

public section

open scoped MatrixGroups Matrix

namespace CFSG.Quasithin

open CFSG.CosetTable CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups

abbrev F9Field : Type := GaloisField 3 (2 * 1)

theorem unitaryFieldData_F9 : UnitaryFieldData 3 1 F9Field :=
  ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩

@[expose] noncomputable def antidiagF : Matrix (Fin 3) (Fin 3) F9Field := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem antidiagF_hermitian :
    (antidiagF.map unitaryFieldData_F9.bar)ᵀ = antidiagF := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagF]

theorem antidiagF_det : antidiagF.det ≠ 0 := by
  simp [antidiagF, Matrix.det_fin_three]

theorem card_gramSU_antidiag : Nat.card (gramSU unitaryFieldData_F9 antidiagF) = 6048 := by
  have h := unitaryFieldData_F9
  have := h.finite
  have := Fintype.ofFinite F9Field
  have hSU := (unitary_full_group_order h (gramForm_isSymm h antidiagF_hermitian)
    (gramForm_separatingLeft h antidiagF_det) (Module.finrank_fin_fun F9Field)
    (by norm_num)).2.1
  rw [card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 224 := by decide
  rw [hprod] at hSU
  norm_num at hSU
  exact_mod_cast hSU

theorem psu3_three_one_eq_map_gramSU :
    CFSG.Open.PSU3 3 1 = (gramSU unitaryFieldData_F9 antidiagF).map Matrix.ProjGenLinGroup.mk := by
  unfold CFSG.Open.PSU3
  congr 1
  rw [← Subgroup.closure_eq (gramSU unitaryFieldData_F9 antidiagF)]
  congr 1
  ext A
  rw [Set.mem_ofPred_eq, SetLike.mem_coe, mem_gramSU]
  have hbar : ∀ c : F9Field, unitaryFieldData_F9.bar c = c ^ 3 ^ 1 := fun c =>
    unitaryFieldData_F9.bar_apply c
  have hdet : Matrix.GeneralLinearGroup.det A = 1 ↔ (A : Matrix (Fin 3) (Fin 3) F9Field).det = 1 := by
    rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  rw [hdet]
  have hmat : (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) F9Field) j i ^ 3 ^ 1) =
      ((A : Matrix (Fin 3) (Fin 3) F9Field).map unitaryFieldData_F9.bar)ᵀ := by
    ext i j
    simp [hbar]
  rw [hmat]
  rfl

theorem card_psu3_three_one_le : Nat.card (CFSG.Open.PSU3 3 1) ≤ 6048 := by
  rw [psu3_three_one_eq_map_gramSU, ← card_gramSU_antidiag]
  have hfin : Finite (gramSU unitaryFieldData_F9 antidiagF) := inferInstance
  exact Nat.card_le_card_of_surjective _
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective (gramSU unitaryFieldData_F9 antidiagF))

noncomputable def gf9Equiv : GF9 ≃+* F9Field :=
  haveI : Fintype F9Field := Fintype.ofFinite _
  FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card 3 (2 * 1) (by norm_num), Nat.card_eq_fintype_card]
    decide)

noncomputable def u33Map : GL (Fin 3) GF9 →* GL (Fin 3) F9Field :=
  Matrix.GeneralLinearGroup.map gf9Equiv.toRingHom

theorem coe_u33Map (A : GL (Fin 3) GF9) :
    ((u33Map A : GL (Fin 3) F9Field) : Matrix (Fin 3) (Fin 3) F9Field) =
      (A : Matrix (Fin 3) (Fin 3) GF9).map gf9Equiv := by
  simp [u33Map, Matrix.GeneralLinearGroup.map]

theorem u33Map_injective : Function.Injective u33Map := by
  refine Units.map_injective (f := (gf9Equiv.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) GF9 →+*
    Matrix (Fin 3) (Fin 3) F9Field).toMonoidHom) ?_
  intro M N h
  exact Matrix.map_injective gf9Equiv.injective h

theorem u33Map_mem_gramSU (i : Fin 5) :
    u33Map (u33GL i) ∈ gramSU unitaryFieldData_F9 antidiagF := by
  have hv : ((u33GL i : GL (Fin 3) GF9) : Matrix (Fin 3) (Fin 3) GF9) = u33M i := rfl
  rw [mem_gramSU, coe_u33Map, hv]
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) GF9 => A.map gf9Equiv) (u33M_unitary i)
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
    have hJ : antidiag3.map gf9Equiv = antidiagF := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [antidiag3, antidiagF]
    have hbar : (gf9Equiv ∘ fun x : GF9 => x ^ 3) = unitaryFieldData_F9.bar ∘ gf9Equiv := by
      funext x
      simp [unitaryFieldData_F9.bar_apply]
    rw [hJ, hbar] at h
    simpa [Matrix.map_map, Function.comp_def] using h
  · have h2 : gf9Equiv (u33M i).det = 1 := by rw [u33M_det i, map_one]
    calc ((u33M i).map gf9Equiv).det
        = gf9Equiv (u33M i).det := (RingHom.map_det gf9Equiv.toRingHom (u33M i)).symm
      _ = 1 := h2

theorem map_u33Group9_le : u33Group9.map u33Map ≤ gramSU unitaryFieldData_F9 antidiagF := by
  rw [u33Group9, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact u33Map_mem_gramSU i

theorem map_u33Group9_eq
    : u33Group9.map u33Map = gramSU unitaryFieldData_F9 antidiagF := by
  have hcard : Nat.card (u33Group9.map u33Map) = 6048 := by
    rw [Subgroup.card_map_of_injective u33Map_injective, card_u33Group9]
  refine Subgroup.eq_of_le_of_card_ge map_u33Group9_le ?_
  rw [hcard, card_gramSU_antidiag]

theorem eq_one_of_mem_center_gramSU {g : GL (Fin 3) F9Field}
    (hg : g ∈ gramSU unitaryFieldData_F9 antidiagF)
    (hc : g ∈ Subgroup.center (GL (Fin 3) F9Field)) : g = 1 := by
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hc
  have hdet : a ^ 3 = 1 := by
    have h2 := hg.2
    rw [← ha] at h2
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using h2
  have : Fintype F9Field := Fintype.ofFinite _
  have hq : Fintype.card F9Field = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have h9 : a ^ 9 = a := by
    have := FiniteField.pow_card a
    rwa [hq] at this
  have ha1 : a = 1 := by
    calc a = a ^ 9 := h9.symm
      _ = (a ^ 3) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [hdet, one_pow]
  apply Units.ext
  rw [← ha, ha1]
  simp

noncomputable def u33Psu : PG 5 u33PresRels →* Matrix.ProjGenLinGroup (Fin 3) F9Field :=
  Matrix.ProjGenLinGroup.mk.comp (u33Map.comp u33GLHom)

theorem range_u33GLHom : u33GLHom.range = u33Group9 := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 5) | r ∈ u33PresRels.map FreeGroup.mk}, MonoidHom.map_closure, u33Group9]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (u33GLHom_of i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, u33GLHom_of i⟩

theorem u33GLHom_injective
    : Function.Injective u33GLHom := by
  obtain ⟨hfin, hle⟩ := u33Pres_finite_card_le
  have hbij : Function.Bijective u33GLHom.rangeRestrict :=
    u33GLHom.rangeRestrict_surjective.bijective_of_nat_card_le (by
      rw [range_u33GLHom, card_u33Group9]; exact hle)
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem range_u33Psu : u33Psu.range = CFSG.Open.PSU3 3 1 := by
  rw [psu3_three_one_eq_map_gramSU, ← map_u33Group9_eq, ← range_u33GLHom, u33Psu,
    MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_map]

theorem u33Psu_injective
    : Function.Injective u33Psu := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [MonoidHom.mem_ker, u33Psu, MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one] at hx
  have hmem : u33Map (u33GLHom x) ∈ gramSU unitaryFieldData_F9 antidiagF := by
    rw [← map_u33Group9_eq, ← range_u33GLHom]
    exact ⟨u33GLHom x, ⟨x, rfl⟩, rfl⟩
  have h1 := eq_one_of_mem_center_gramSU hmem hx
  rw [← map_one u33Map] at h1
  have h2 := u33Map_injective h1
  rw [← map_one u33GLHom] at h2
  exact u33GLHom_injective h2

theorem u33Pres_mulEquiv_PSU3
    : Nonempty (PG 5 u33PresRels ≃* CFSG.Open.PSU3 3 1) := by
  have hmem : ∀ g : PG 5 u33PresRels, u33Psu g ∈ CFSG.Open.PSU3 3 1 := fun g => by
    rw [← range_u33Psu]
    exact ⟨g, rfl⟩
  exact ⟨MulEquiv.ofBijective (u33Psu.codRestrict _ hmem)
    ⟨fun x y hxy => u33Psu_injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Matrix.ProjGenLinGroup (Fin 3) F9Field) ∈ u33Psu.range := by
        rw [range_u33Psu]
        exact y.2
      obtain ⟨g, hg⟩ := hy
      exact ⟨g, Subtype.ext hg⟩⟩⟩

end CFSG.Quasithin

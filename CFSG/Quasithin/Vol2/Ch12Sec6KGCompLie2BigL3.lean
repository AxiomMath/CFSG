module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfL3
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular upperTriangular proj
  projectiveSL projUnitriangular scalars mem_scalars proj_eq_one_iff proj_injOn_unitriangular
  normalizer_projUnitriangular)
open Matrix

section SL3

variable {F : Type} [Field F]

local notation "SL₃" => SpecialLinearGroup (Fin 3) F

@[expose] def x12 : SL₃ :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def x23 : SL₃ :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_x12 : ((x12 : SL₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 1, 0; 0, 1, 0; 0, 0, 1] :=
  rfl

theorem coe_x23 : ((x23 : SL₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 1; 0, 0, 1] :=
  rfl

theorem x12_mem : (x12 : SL₃) ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [coe_x12]
  · fin_cases i <;> simp [coe_x12]

theorem x23_mem : (x23 : SL₃) ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [coe_x23]
  · fin_cases i <;> simp [coe_x23]

@[expose] def ebd13 (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 0 0, 0, A 0 1; 0, 1, 0; A 1 0, 0, A 1 1]

theorem ebd13_mul (A B : Matrix (Fin 2) (Fin 2) F) : ebd13 (A * B) = ebd13 A * ebd13 B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ebd13, Matrix.mul_apply, Fin.sum_univ_succ]

theorem ebd13_one : ebd13 (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ebd13]

theorem det_ebd13 (A : Matrix (Fin 2) (Fin 2) F) : (ebd13 A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [ebd13]

@[expose] def iota13 : SpecialLinearGroup (Fin 2) F →* SL₃ where
  toFun A := ⟨ebd13 (A : Matrix (Fin 2) (Fin 2) F), (det_ebd13 _).trans A.2⟩
  map_one' := Subtype.ext ebd13_one
  map_mul' A B := Subtype.ext (ebd13_mul (A : Matrix (Fin 2) (Fin 2) F) B)

theorem coe_iota13 (A : SpecialLinearGroup (Fin 2) F) :
    ((iota13 A : SL₃) : Matrix (Fin 3) (Fin 3) F) = ebd13 (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem proj_iota13_injective : Function.Injective ((proj 3 F).comp (iota13 (F := F))) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hA
  obtain ⟨c, -, hc⟩ := hA
  have e : ∀ i j, ebd13 (A : Matrix (Fin 2) (Fin 2) F) i j = scalar (Fin 3) (c : F) i j :=
    fun i j => by rw [← coe_iota13, hc]
  have h11 := e 1 1
  have h00 := e 0 0
  have h02 := e 0 2
  have h20 := e 2 0
  have h22 := e 2 2
  simp [ebd13] at h11 h00 h02 h20 h22
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h00, h02, h20, h22, ← h11]

omit [Field F] in
theorem upper_of_mem {F : Type} [Field F] {x : SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ unitriangular 3 F) : x ∈ upperTriangular 3 F :=
  hx.1

theorem commute_of_proj {b x : SL₃} (hb : b ∈ upperTriangular 3 F) (hx : x ∈ unitriangular 3 F)
    (h : proj 3 F b * proj 3 F x = proj 3 F x * proj 3 F b) : b * x = x * b := by
  have hc : b * x * b⁻¹ * x⁻¹ ∈ unitriangular 3 F := comm_mem_unitriangular hb (upper_of_mem hx)
  have h1 : proj 3 F (b * x * b⁻¹ * x⁻¹) = proj 3 F 1 := by
    rw [map_one, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 := proj_injOn_unitriangular 3 hc (one_mem _) h1
  calc b * x = (b * x * b⁻¹ * x⁻¹) * (x * b) := by group
    _ = x * b := by rw [h2, one_mul]

theorem cbAt_psl3 [Finite F] [CharP F 2] : CBAt (projectiveSL 3 F) (projUnitriangular 3 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro b' hb hc
  rw [normalizer_projUnitriangular 2] at hb
  obtain ⟨b, hbB, rfl⟩ := hb
  have h1 : b * x12 = x12 * b := commute_of_proj hbB x12_mem (hc _ ⟨x12, x12_mem, rfl⟩)
  have h2 : b * x23 = x23 * b := commute_of_proj hbB x23_mem (hc _ ⟨x23, x23_mem, rfl⟩)
  set B := (b : Matrix (Fin 3) (Fin 3) F) with hBdef
  have hb10 : B 1 0 = 0 := hbB 1 0 (by decide)
  have hb20 : B 2 0 = 0 := hbB 2 0 (by decide)
  have hb21 : B 2 1 = 0 := hbB 2 1 (by decide)
  have e : ∀ (g g' : SL₃), g = g' → ∀ i j, (g : Matrix (Fin 3) (Fin 3) F) i j =
      (g' : Matrix (Fin 3) (Fin 3) F) i j := fun g g' h i j => by rw [h]
  have e1 := e _ _ h1 0 1
  have e2 := e _ _ h1 0 2
  have e3 := e _ _ h2 1 2
  have e4 := e _ _ h2 0 2
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_x12, coe_x23, Matrix.mul_apply,
    Fin.sum_univ_three] at e1 e2 e3 e4
  simp [← hBdef, hb10, hb21] at e1 e2 e3 e4
  have hdet := b.2
  rw [Matrix.det_fin_three, ← hBdef, hb10, hb20, hb21] at hdet
  have d1 : B 1 1 = B 0 0 := by linear_combination -e1
  have d2 : B 2 2 = B 0 0 := by
    have : B 2 2 = B 1 1 := by linear_combination -e3
    rw [this, d1]
  set a := B 0 0 with ha
  have ha3 : a * a * a = 1 := by
    rw [d1, d2] at hdet
    linear_combination hdet
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0, zero_mul, zero_mul] at ha3
    exact zero_ne_one ha3
  set u : SL₃ := ⟨a⁻¹ • B, by
    rw [Matrix.det_smul, b.2, Fintype.card_fin, mul_one, inv_pow]
    rw [show a ^ 3 = a * a * a by ring, ha3, inv_one]⟩ with hu
  have huU : u ∈ unitriangular 3 F := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change (a⁻¹ • B) i j = 0
      rw [Matrix.smul_apply, show B i j = 0 from hbB i j hij, smul_zero]
    · change (a⁻¹ • B) i i = 1
      rw [Matrix.smul_apply, smul_eq_mul]
      fin_cases i
      · exact inv_mul_cancel₀ ha0
      · change a⁻¹ * B 1 1 = 1
        rw [d1]
        exact inv_mul_cancel₀ ha0
      · change a⁻¹ * B 2 2 = 1
        rw [d2]
        exact inv_mul_cancel₀ ha0
  have hs : u⁻¹ * b ∈ scalars 3 F := by
    rw [mem_scalars]
    refine ⟨Units.mk0 a ha0, ?_, ?_⟩
    · ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [show a ^ 3 = a * a * a by ring, ha3]
    · set s : SL₃ := ⟨scalar (Fin 3) a, by
        rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, ha3]⟩ with hsdef
      have hb' : b = u * s := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        change B i j = (a⁻¹ • B * scalar (Fin 3) a) i j
        rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
        field_simp
      rw [hb', inv_mul_cancel_left]
      rfl
  refine ⟨u, huU, ?_⟩
  exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff.mpr hs)

theorem invAt_psl3 [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 3 ≤ f) :
    InvAt (projectiveSL 3 F) (projUnitriangular 3 F) := by
  intro z' hz hz1 hzc
  obtain ⟨u, hu, rfl⟩ := hz
  have h1 : u * x12 = x12 * u :=
    commute_of_proj (upper_of_mem hu) x12_mem (hzc _ ⟨x12, x12_mem, rfl⟩).symm.symm
  have h2 : u * x23 = x23 * u :=
    commute_of_proj (upper_of_mem hu) x23_mem (hzc _ ⟨x23, x23_mem, rfl⟩)
  set V := (u : Matrix (Fin 3) (Fin 3) F) with hVdef
  have e : ∀ (g g' : SL₃), g = g' → ∀ i j, (g : Matrix (Fin 3) (Fin 3) F) i j =
      (g' : Matrix (Fin 3) (Fin 3) F) i j := fun g g' h i j => by rw [h]
  have v10 : V 1 0 = 0 := hu.1 1 0 (by decide)
  have v20 : V 2 0 = 0 := hu.1 2 0 (by decide)
  have v21 : V 2 1 = 0 := hu.1 2 1 (by decide)
  have v00 : V 0 0 = 1 := hu.2 0
  have v11 : V 1 1 = 1 := hu.2 1
  have v22 : V 2 2 = 1 := hu.2 2
  have e2 := e _ _ h1 0 2
  have e4 := e _ _ h2 0 2
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_x12, coe_x23, Matrix.mul_apply,
    Fin.sum_univ_three] at e2 e4
  simp [← hVdef, v00, v22] at e2 e4
  have hu' : u = iota13 (xT (V 0 2)) := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [coe_iota13, coe_xT]
    fin_cases i <;> fin_cases j <;> simp [ebd13, ← hVdef, v10, v20, v21, v00, v11, v22, e2, e4]
  have hs : V 0 2 ≠ 0 := by
    intro h0
    apply hz1
    rw [hu', h0, xT_zero, map_one, map_one]
  obtain ⟨y, hy1, hy2, hy3⟩ :=
    exists_inv_of_hom hF hf ((proj 3 F).comp iota13) proj_iota13_injective hs
  refine ⟨y, hy1, ?_, hy3⟩
  rw [hu']
  exact hy2

end SL3

theorem ordA_two_ne {q : ℕ} (hq : 8 ≤ q) : ordA 2 q ≠ 20160 := by
  intro h
  have hg : Nat.gcd (2 + 1) (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have a1 : 512 ≤ q ^ 3 := by
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have a2 : 64 ≤ q ^ 2 := by
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hN : 512 * (63 * 511) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
    Nat.mul_le_mul a1 (Nat.mul_le_mul (by omega) (by omega))
  unfold ordA at h
  rw [show 2 * (2 + 1) / 2 = 3 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} from rfl,
    Finset.prod_pair (by norm_num)] at h
  have h3 := Nat.div_le_div_left hg hg0 (a := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
  rw [h] at h3
  have h4 := Nat.div_le_div_right (c := 3) hN
  omega

theorem false_of_autConf_psl3 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel M .PSL 3 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).1 rfl
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hF4 : 4 ≤ Nat.card F := by omega
  let e' : M ≃* projectiveSL 3 F := e.trans (K1.statedProjEquivProjectiveSL 3 F)
  have h34 : ¬ IsPSL 3 2 2 (projectiveSL 3 F) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e'.toEquiv, hcard] at h1
    exact ordA_two_ne h8 h1
  exact not_autConf_of_at isSylowTwoOf_projUnitriangular_three (n4At_psl3 hF4) h34 cbAt_psl3
    (invAt_psl3 hF hf) (h.map e')

end CFSG.Quasithin.H13.S126C

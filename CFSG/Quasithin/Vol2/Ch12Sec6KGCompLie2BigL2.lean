module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2Big
public import CFSG.Quasithin.H13.L32ACSkPfL2
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular upperTriangular
  normalizer_unitriangular)
open Matrix

section SL2

variable {F : Type} [Field F]

local notation "SL₂" => SpecialLinearGroup (Fin 2) F

@[expose] def xT (s : F) : SL₂ :=
  ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_xT (s : F) : ((xT s : SL₂) : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] :=
  rfl

theorem xT_zero : xT (0 : F) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_xT]

theorem xT_mem_unitriangular (s : F) : xT s ∈ unitriangular 2 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [coe_xT]
  · fin_cases i <;> simp [coe_xT]

theorem eq_xT_of_mem_unitriangular {u : SL₂} (hu : u ∈ unitriangular 2 F) :
    u = xT ((u : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h00 := hu.2 0
  have h11 := hu.2 1
  have h10 := hu.1 1 0 (by decide)
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [coe_xT, h00, h11, h10]

@[expose] noncomputable def gT (c : F) (hc : c ≠ 0) : SL₂ :=
  ⟨!![c, 0; c⁻¹, c⁻¹], by simp [Matrix.det_fin_two_of, hc]⟩

theorem coe_gT (c : F) (hc : c ≠ 0) :
    ((gT c hc : SL₂) : Matrix (Fin 2) (Fin 2) F) = !![c, 0; c⁻¹, c⁻¹] :=
  rfl

theorem gT_mul_w2 [CharP F 2] (c : F) (hc : c ≠ 0) :
    gT c hc * KG22.w2 = xT (c ^ 2) * gT c hc := by
  have hcc : c ^ 2 * c⁻¹ = c := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, KG22.coe_w2, coe_xT, coe_gT, hcc,
      CharTwo.add_self_eq_zero]

theorem exists_inv_xT [Finite F] [CharP F 2] {s : F} (hs : s ≠ 0) :
    ∃ y : SL₂, orderOf y = Nat.card F - 1 ∧ xT s * y * (xT s)⁻¹ = y⁻¹ := by
  obtain ⟨c, hcs⟩ := isSquare_of_charTwo' s
  have hc : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcs
    exact hs hcs
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  refine ⟨gT c hc * KG22.tT l * (gT c hc)⁻¹, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_injective KG22.tT KG22.tT_injective, hl,
      Nat.card_units]
  · have hx : xT s = gT c hc * KG22.w2 * (gT c hc)⁻¹ := by
      rw [gT_mul_w2, mul_inv_cancel_right, hcs, pow_two]
    rw [hx]
    calc gT c hc * KG22.w2 * (gT c hc)⁻¹ * (gT c hc * KG22.tT l * (gT c hc)⁻¹) *
          (gT c hc * KG22.w2 * (gT c hc)⁻¹)⁻¹ =
          gT c hc * (KG22.w2 * KG22.tT l * KG22.w2⁻¹) * (gT c hc)⁻¹ := by group
      _ = (gT c hc * KG22.tT l * (gT c hc)⁻¹)⁻¹ := by rw [KG22.w2_conj_tT]; group

theorem exists_inv_of_hom [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 3 ≤ f)
    {M : Type} [Group M] (φ : SL₂ →* M) (hφ : Function.Injective φ) {s : F} (hs : s ≠ 0) :
    ∃ y : M, Odd (orderOf y) ∧ φ (xT s) * y * (φ (xT s))⁻¹ = y⁻¹ ∧
      ¬ (y ^ 3 = 1 ∨ y ^ 5 = 1) := by
  obtain ⟨y, hy, hinv⟩ := exists_inv_xT hs
  have hord : orderOf (φ y) = 2 ^ f - 1 := by rw [orderOf_injective φ hφ, hy, hF]
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h8 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  norm_num at h8
  refine ⟨φ y, ?_, ?_, ?_⟩
  · rw [hord, Nat.odd_iff]
    omega
  · rw [← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  · rintro (h3 | h5)
    · have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h3)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h5)
      omega

theorem cbAt_sl2 [CharP F 2] : CBAt SL₂ (unitriangular 2 F) := by
  intro b hb hc
  rw [normalizer_unitriangular] at hb
  have h10 : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb 1 0 (by decide)
  have h01 : ((b * xT 1 : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      ((xT 1 * b : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    rw [hc (xT 1) (xT_mem_unitriangular 1)]
  have e1 : ((b * xT 1 : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (b : Matrix (Fin 2) (Fin 2) F) 0 0 + (b : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_xT]
  have e2 : ((xT 1 * b : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (b : Matrix (Fin 2) (Fin 2) F) 0 1 + (b : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_xT]
  rw [e1, e2] at h01
  have hdet := b.2
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hd : (b : Matrix (Fin 2) (Fin 2) F) 1 1 = (b : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -h01
  rw [hd] at hdet
  have hsq : ((b : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) ^ 2 = 0 := by
    linear_combination hdet + ((b : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * h2
  have h0 : (b : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination this - h2
  refine ⟨fun i j hij => hb i j hij, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact hd.trans h0

theorem invAt_sl2 [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 3 ≤ f) :
    InvAt SL₂ (unitriangular 2 F) := by
  intro z hz hz1 _
  obtain ⟨s, rfl⟩ : ∃ s, z = xT s := ⟨_, eq_xT_of_mem_unitriangular hz⟩
  have hs : s ≠ 0 := by
    rintro rfl
    exact hz1 xT_zero
  exact exists_inv_of_hom hF hf (MonoidHom.id _) Function.injective_id hs

end SL2

theorem mul_sq_sub_one_ne (q : ℕ) : q * (q ^ 2 - 1) ≠ 20160 := by
  intro h
  rcases Nat.lt_or_ge q 28 with hq | hq
  · interval_cases q <;> omega
  · have h1 : 28 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h2 := Nat.mul_le_mul hq h1
    norm_num at h2
    omega

theorem false_of_autConf_psl2 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : CFSG.Assembly.LowTwoRank.StatedClassicalModel M .PSL 2 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) : False := by
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two hM).1 rfl
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hM
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  let e' : M ≃* SpecialLinearGroup (Fin 2) F := e.trans ((K1.statedProjEquivProjectiveSL 2 F).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F))
  have h34 : ¬ IsPSL 3 2 2 (SpecialLinearGroup (Fin 2) F) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e'.toEquiv, hcard] at h1
    have hg : Nat.gcd (1 + 1) (2 ^ f - 1) = 1 := by
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h3 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega))
    simp only [ordA, Finset.Icc_self, Finset.prod_singleton] at h1
    norm_num [hg] at h1
    exact mul_sq_sub_one_ne (2 ^ f) h1
  exact not_autConf_of_at isSylowTwoOf_unitriangular_two n4At_sl2 h34 cbAt_sl2
    (invAt_sl2 hF hf) (h.map e')

end CFSG.Quasithin.H13.S126C

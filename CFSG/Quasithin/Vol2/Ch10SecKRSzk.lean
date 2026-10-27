module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzj
public import CFSG.Quasithin.Vol2.Ch10SecKRSu

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

theorem trvE_mem_X3' (a b : Fin 5) (ha : (a : ℕ) < 3) (hb : 3 ≤ (b : ℕ)) (h : a ≠ b) :
    trvE a b h ∈ X3 := by
  fin_cases a <;> fin_cases b <;> simp at ha hb <;>
    exact ⟨by unfold PresStd; decide +revert, by decide +revert⟩

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_alt_E3_five (c : Conf T L I t w J) (h1011 : Stmt10_1_1)
    (h5 : Case10_1_1Five T L I) (C : AltCoord J (VI T L I J w))
    (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h3 : InvStd (piL C.ρ c.le).range 3) (hX : (piL C.ρ c.le).range = X3) : False := by
  have hrow : ∀ v ∈ fsuUL T L I, ∀ b : Fin 5, 3 ≤ (b : ℕ) → ∀ c', C.E v b c' = 0 := by
    intro v hv b hb c'
    have hb0 : (0 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    have hb1 : (1 : Fin 5) ≠ b := fun h => by rw [← h] at hb; simp at hb
    obtain ⟨l₀, hl₀ρ, hl₀C⟩ := Conf.lift_trvE c h1011 C.ρ hker h3 hb0 (by norm_num) hb
      (by rw [hX]; exact trvE_mem_X3' 0 b (by norm_num) hb hb0)
    obtain ⟨l₁, hl₁ρ, hl₁C⟩ := Conf.lift_trvE c h1011 C.ρ hker h3 hb1 (by norm_num) hb
      (by rw [hX]; exact trvE_mem_X3' 1 b (by norm_num) hb hb1)
    have e0 := Conf.alt_fix_of_lift c C hV1W hl₀C hv
    have e1 := Conf.alt_fix_of_lift c C hV1W hl₁C hv
    rw [show C.ρ ⟨l₀, c.le l₀.2⟩ = trvE 0 b hb0 from hl₀ρ] at e0
    rw [show C.ρ ⟨l₁, c.le l₁.2⟩ = trvE 1 b hb1 from hl₁ρ] at e1
    exact row_eq_zero_of_two hb0 hb1 e0 e1 c'
  refine Conf.false_of_alt_five c h5 C hV1W fun v hv a b ha hb hab => ?_
  obtain ⟨hs, hd⟩ := mem_altMat.mp (C.mem v)
  by_cases ha3 : 3 ≤ (a : ℕ)
  · exact hrow v hv a ha3 b
  by_cases hb3 : 3 ≤ (b : ℕ)
  · have := congrFun (congrFun hs a) b
    rw [Matrix.transpose_apply] at this
    rw [← this]
    exact hrow v hv b hb3 a
  · have hab' : a = b := Fin.ext (by omega)
    rw [hab']
    exact hd b

theorem Conf.false_of_alt_flag_five (c : Conf T L I t w J) (h1011 : Stmt10_1_1)
    (h5 : Case10_1_1Five T L I) (C : AltCoord J (VI T L I J w))
    (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (h1 : InvStd (piL C.ρ c.le).range 1) (h4 : InvStd (piL C.ρ c.le).range 4)
    (hX : (piL C.ρ c.le).range = X14) : False := by
  refine Conf.false_of_alt_five c h5 C hV1W fun v hv a b ha hb _ => ?_
  have ha0 : (0 : Fin 5) ≠ a := fun h => by rw [← h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  obtain ⟨l, hlρ, hlC⟩ := Conf.lift_trvE14 c h1011 C.ρ hker h1 h4 (trvE_mem_rad14_left ha0)
    (by rw [hX]; exact trvE_mem_X14_left a ha0)
  have e := Conf.alt_fix_of_lift c C hV1W hlC hv
  rw [show C.ρ ⟨l, c.le l.2⟩ = trvE 0 a ha0 from hlρ] at e
  exact row_eq_zero_of_trvE ha0 e hb0

theorem Conf.false_of_y_X14 (c : Conf T L I t w J) (h37 : Vol2Native.A37ForSQTKCat)
    (ρ : ↥J →* SL5) (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (hX : (piL ρ c.le).range = X14)
    (hqX : Nonempty (↥(piL ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL ρ c.le).range ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {y : G} (hyLt : y ∈ CFSG.conjugate L t) (hy3 : orderOf y = 3) (hyJ : y ∈ J) : False := by
  obtain ⟨e⟩ := hqX
  have hyN := rho_mem_normalizer ρ c.le hyJ (conjugate_le_normalizer c.hyp c.ht hyLt)
  have hyc := rho_comm_mem_pCoreOf ρ c.le hyJ (Conf.comm_mem_of_conjugate c h37 hyLt)
  have hyX : ρ ⟨y, hyJ⟩ ∈ (piL ρ c.le).range := by
    rw [hX, ← normalizer_X14, ← hX]
    exact hyN
  have hcomm : ∀ z : ↥(piL ρ c.le).range,
      (⟨ρ ⟨y, hyJ⟩, hyX⟩ : ↥(piL ρ c.le).range) * z * (⟨ρ ⟨y, hyJ⟩, hyX⟩)⁻¹ * z⁻¹ ∈
        CFSG.pCore 2 ↥(piL ρ c.le).range := fun z => by
    obtain ⟨w', hw', hw'eq⟩ := hyc (z : SL5) z.2
    have : w' = (⟨ρ ⟨y, hyJ⟩, hyX⟩ : ↥(piL ρ c.le).range) * z * (⟨ρ ⟨y, hyJ⟩, hyX⟩)⁻¹ * z⁻¹ :=
      Subtype.ext hw'eq
    rwa [← this]
  set q : ↥(piL ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL ρ c.le).range :=
    QuotientGroup.mk ⟨ρ ⟨y, hyJ⟩, hyX⟩ with hq
  have hqc : ∀ z, z * q = q * z := fun z => by
    induction z using QuotientGroup.induction_on with
    | H z =>
      have h1 := (QuotientGroup.eq_one_iff _).mpr (hcomm z)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h1
      rw [hq]
      have h2 := congrArg (· * (QuotientGroup.mk z : ↥(piL ρ c.le).range ⧸
        CFSG.pCore 2 ↥(piL ρ c.le).range)) h1
      simp only [inv_mul_cancel_right, one_mul] at h2
      have h3 := congrArg (· * (QuotientGroup.mk ⟨ρ ⟨y, hyJ⟩, hyX⟩ : ↥(piL ρ c.le).range ⧸
        CFSG.pCore 2 ↥(piL ρ c.le).range)) h2
      simp only [inv_mul_cancel_right] at h3
      exact h3.symm
  have heq : e q = 1 := by
    have hz : e q ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
      Subgroup.mem_center_iff.mpr fun g => by
        obtain ⟨z, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hqc z]
    rwa [center_SL_eq_bot 3, Subgroup.mem_bot] at hz
  have hq1 : q = 1 := e.injective (heq.trans (map_one e).symm)
  have hO := (QuotientGroup.eq_one_iff _).mp hq1
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(piL ρ c.le).range)) ⟨_, hO⟩
  have hm' : ρ (⟨y, hyJ⟩ ^ 2 ^ m) = 1 := by
    rw [map_pow]
    exact congrArg (fun z : ↥(CFSG.pCore 2 ↥(piL ρ c.le).range) => ((z : ↥(piL ρ c.le).range) :
      SL5)) hm
  obtain ⟨m', hm''⟩ := hker _ hm'
  have hy2 : y ^ 2 ^ (m + m') = 1 := by
    rw [pow_add, pow_mul]
    simpa using hm''
  have hy3' : y ^ 3 ^ 1 = 1 := by rw [pow_one, ← hy3, pow_orderOf_eq_one]
  have hy1 := eq_one_of_two_three hy2 hy3'
  rw [hy1, orderOf_one] at hy3
  norm_num at hy3

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

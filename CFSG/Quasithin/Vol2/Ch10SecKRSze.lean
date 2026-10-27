module

public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecKRSa
public import CFSG.Quasithin.Vol2.Ch10SecQ9G17
public import CFSG.Quasithin.Vol2.Ch10SecQ9H24

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F

theorem add_split (a b c : Fin 5 → ZMod 2) : a + c = (a + b) + (b + c) := by
  rw [add_assoc, ← add_assoc b b c, add_self_vec, zero_add]

@[expose] def radE (m : ℕ) : Subgroup SL5 where
  carrier := {g | (∀ v, g • v + v ∈ stdE 5 m) ∧ ∀ v ∈ stdE 5 m, g • v = v}
  one_mem' := ⟨fun v => by rw [one_smul, add_self_vec]; exact zero_mem _,
    fun v _ => one_smul _ v⟩
  mul_mem' := fun {g h} hg hh => ⟨fun v => by
      rw [mul_smul, add_split (g • h • v) (h • v) v]
      exact add_mem (hg.1 _) (hh.1 v),
    fun v hv => by rw [mul_smul, hh.2 v hv, hg.2 v hv]⟩
  inv_mem' := fun {x} hx => inv_mem_of_mul_closed
    (S := {g : SL5 | (∀ v, g • v + v ∈ stdE 5 m) ∧ ∀ v ∈ stdE 5 m, g • v = v})
    ⟨fun v => by rw [one_smul, add_self_vec]; exact zero_mem _, fun v _ => one_smul _ v⟩
    (fun g h hg hh => ⟨fun v => by
      rw [mul_smul, add_split (g • h • v) (h • v) v]
      exact add_mem (hg.1 _) (hh.1 v),
    fun v hv => by rw [mul_smul, hh.2 v hv, hg.2 v hv]⟩) hx

theorem smul_eq_add (g : SL5) (v : Fin 5 → ZMod 2) : g • v = (g • v + v) + v := by
  rw [add_assoc, add_self_vec, add_zero]

theorem mul_self_of_mem_radE {m : ℕ} {g : SL5} (hg : g ∈ radE m) : g * g = 1 := by
  refine ext_mulVec fun v => ?_
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← smul_eq_mulVec', ← smul_eq_mulVec']
  rw [smul_eq_add g v, smul_add, hg.2 _ (hg.1 v), add_comm (g • v + v), ← add_assoc, add_self_vec,
    zero_add]

theorem conj_mem_radE {m : ℕ} {X : Subgroup SL5} (hX : InvStd X m) {x g : SL5} (hx : x ∈ X)
    (hg : g ∈ radE m) : x * g * x⁻¹ ∈ radE m := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · have h1 : (x * g * x⁻¹) • v + v = x • (g • (x⁻¹ • v) + x⁻¹ • v) := by
      rw [smul_add, mul_smul, mul_smul, smul_inv_smul]
    rw [h1]
    exact hX x hx _ (hg.1 _)
  · have hw : x⁻¹ • v ∈ stdE 5 m := hX _ (X.inv_mem hx) v hv
    rw [mul_smul, mul_smul, hg.2 _ hw, smul_inv_smul]

theorem trvE_mem_radE {m : ℕ} {a b : Fin 5} (hab : a ≠ b) (ha : (a : ℕ) < m) (hb : m ≤ (b : ℕ)) :
    trvE a b hab ∈ radE m := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [trvE_mulVec, add_comm v, add_assoc, add_self_vec, add_zero]
    rcases zmod2_cases (v b) with h | h
    · rw [h, zero_smul]
      exact zero_mem _
    · rw [h, one_smul]
      exact single_mem_stdE ha
  · rw [trvE_mulVec, hv b hb, zero_smul, add_zero]

@[expose] def P14 (g : SL5) : Prop :=
  (∀ v, g • v + v ∈ stdE 5 4) ∧ (∀ v ∈ stdE 5 4, g • v + v ∈ stdE 5 1) ∧
    ∀ v ∈ stdE 5 1, g • v = v

theorem P14_one : P14 1 :=
  ⟨fun v => by rw [one_smul, add_self_vec]; exact zero_mem _,
    fun v _ => by rw [one_smul, add_self_vec]; exact zero_mem _, fun v _ => one_smul _ v⟩

theorem P14_mul {g h : SL5} (hg : P14 g) (hh : P14 h) : P14 (g * h) := by
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [mul_smul, add_split (g • h • v) (h • v) v]
    exact add_mem (hg.1 _) (hh.1 v)
  · have hhv : h • v ∈ stdE 5 4 := by
      rw [smul_eq_add h v]
      exact add_mem (stdE_mono (by norm_num) (hh.2.1 v hv)) hv
    rw [mul_smul, add_split (g • h • v) (h • v) v]
    exact add_mem (hg.2.1 _ hhv) (hh.2.1 v hv)
  · rw [mul_smul, hh.2.2 v hv, hg.2.2 v hv]

@[expose] def rad14 : Subgroup SL5 where
  carrier := {g | P14 g}
  one_mem' := P14_one
  mul_mem' := P14_mul
  inv_mem' := fun hx => inv_mem_of_mul_closed (S := {g | P14 g}) P14_one
    (fun _ _ => P14_mul) hx

theorem pow_four_of_mem_rad14 {g : SL5} (hg : g ∈ rad14) : g ^ 4 = 1 := by
  refine ext_mulVec fun v => ?_
  obtain ⟨b, hbdef⟩ : ∃ b, g • v + v = b := ⟨_, rfl⟩
  have hbm : b ∈ stdE 5 4 := hbdef ▸ hg.1 v
  have hgv : g • v = b + v := by rw [← hbdef, add_assoc, add_self_vec, add_zero]
  obtain ⟨c, hcdef⟩ : ∃ c, g • b + b = c := ⟨_, rfl⟩
  have hcm : c ∈ stdE 5 1 := hcdef ▸ hg.2.1 b hbm
  have hgb : g • b = c + b := by rw [← hcdef, add_assoc, add_self_vec, add_zero]
  have hgc : g • c = c := hg.2.2 c hcm
  have h2 : g • g • v = c + v := by
    rw [hgv, smul_add, hgb, hgv, add_assoc, ← add_assoc b b v, add_self_vec, zero_add]
  have h3 : g • g • g • v = c + b + v := by
    rw [h2, smul_add, hgc, hgv, add_assoc]
  have h4 : g • g • g • g • v = v := by
    rw [h3, smul_add, smul_add, hgc, hgb, hgv, ← add_assoc c c b, add_self_vec, zero_add,
      ← add_assoc, add_self_vec, zero_add]
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, ← smul_eq_mulVec',
    show g ^ 4 = g * (g * (g * g)) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
    mul_smul, mul_smul, mul_smul, h4]

theorem conj_mem_rad14 {X : Subgroup SL5} (hX1 : InvStd X 1) (hX4 : InvStd X 4) {x g : SL5}
    (hx : x ∈ X) (hg : g ∈ rad14) : x * g * x⁻¹ ∈ rad14 := by
  have h1 : ∀ v : Fin 5 → ZMod 2, (x * g * x⁻¹) • v + v = x • (g • (x⁻¹ • v) + x⁻¹ • v) :=
    fun v => by
    rw [smul_add, mul_smul, mul_smul, smul_inv_smul]
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [h1]
    exact hX4 x hx _ (hg.1 _)
  · rw [h1]
    exact hX1 x hx _ (hg.2.1 _ (hX4 _ (X.inv_mem hx) v hv))
  · have hw : x⁻¹ • v ∈ stdE 5 1 := hX1 _ (X.inv_mem hx) v hv
    rw [mul_smul, mul_smul, hg.2.2 _ hw, smul_inv_smul]

theorem trvE_mem_rad14_left {b : Fin 5} (hb : (0 : Fin 5) ≠ b) : trvE 0 b hb ∈ rad14 := by
  have hs : ∀ v : Fin 5 → ZMod 2, trvE 0 b hb • v + v ∈ stdE 5 1 := fun v => by
    rw [trvE_mulVec, add_comm v, add_assoc, add_self_vec, add_zero]
    rcases zmod2_cases (v b) with h | h
    · rw [h, zero_smul]
      exact zero_mem _
    · rw [h, one_smul]
      exact single_mem_stdE (by simp)
  refine ⟨fun v => stdE_mono (by norm_num) (hs v), fun v _ => hs v, fun v hv => ?_⟩
  have hb1 : 1 ≤ (b : ℕ) := by
    rcases Nat.eq_zero_or_pos (b : ℕ) with h | h
    · exact absurd (Fin.ext h).symm hb
    · exact h
  rw [trvE_mulVec, hv b hb1, zero_smul, add_zero]

theorem trvE_mem_rad14_right {a : Fin 5} (ha : a ≠ 4) : trvE a 4 ha ∈ rad14 := by
  have ha4 : (a : ℕ) < 4 := by
    have := a.2
    have : (a : ℕ) ≠ 4 := fun h => ha (Fin.ext h)
    omega
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [trvE_mulVec, add_comm v, add_assoc, add_self_vec, add_zero]
    rcases zmod2_cases (v 4) with h | h
    · rw [h, zero_smul]
      exact zero_mem _
    · rw [h, one_smul]
      exact single_mem_stdE ha4
  · rw [trvE_mulVec, hv 4 (by simp), zero_smul, add_zero, add_self_vec]
    exact zero_mem _
  · rw [trvE_mulVec, hv 4 (by simp), zero_smul, add_zero]

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.exists_lift_of_rad (c : Conf T L I t w J) (h1011 : Stmt10_1_1)
    (ρ : ↥J →* SL5) (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    {N : Subgroup SL5} (hNX : N ≤ (piL ρ c.le).range)
    (hXN : (piL ρ c.le).range ≤ Subgroup.normalizer (N : Set SL5)) (hN2 : IsPGroup 2 N)
    {g : SL5} (hg : g ∈ N) :
    ∃ l : ↥L, piL ρ c.le l = g ∧ (l : G) ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  obtain ⟨x, hx, rfl⟩ := le_o2G _ hNX hXN hN2 hg
  have hf : Function.Surjective (piL ρ c.le).rangeRestrict :=
    (piL ρ c.le).rangeRestrict_surjective
  have hk : IsPGroup 2 (piL ρ c.le).rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact isPGroup_ker_piL ρ c.le hker
  have hcomap := comap_pCore_eq' _ hf hk
  obtain ⟨l, hl⟩ := hf x
  have hlO : l ∈ CFSG.pCore 2 ↥L := by
    rw [← hcomap]
    show (piL ρ c.le).rangeRestrict l ∈ CFSG.pCore 2 ↥(piL ρ c.le).range
    rw [hl]
    exact hx
  refine ⟨l, by rw [← hl]; rfl, ?_⟩
  have hlO' : (l : G) ∈ pCoreOf 2 L := ⟨l, by exact hlO, rfl⟩
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hV1V)
    (pCoreOf_L_le_centralizer c.hyp h1011 hlO')

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

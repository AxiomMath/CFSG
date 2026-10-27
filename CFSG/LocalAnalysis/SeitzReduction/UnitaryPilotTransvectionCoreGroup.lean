module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotTransvectionCoreBasic
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ} {i j : Fin n}

theorem barTranspose_mul_self_of_mem (g : unitarySU 2 f K n) :
    (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  ((mem_unitarySU_iff h).1 g.2).2

include h in
theorem det_coe_of_mem (g : unitarySU 2 f K n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  ((mem_unitarySU_iff h).1 g.2).1

theorem coe_inv_mul_coe (g : unitarySU 2 f K n) :
    (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]

theorem coe_mul_coe_inv (g : unitarySU 2 f K n) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]

theorem eq_of_coe_eq {g g' : unitarySU 2 f K n}
    (hgg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : g = g' :=
  Subtype.ext (Units.ext hgg)

theorem inv_mulVec_tvVec (hij : i ≠ j) {g : unitarySU 2 f K n} {μ : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = μ • tvVec i j) :
    μ ≠ 0 ∧ (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      tvVec i j = μ⁻¹ • tvVec i j := by
  have e1 : (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (μ • tvVec i j) = tvVec i j := by
    rw [← hg, mulVec_mulVec, coe_inv_mul_coe, one_mulVec]
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul, mulVec_zero] at e1
    have := congrFun e1 i
    rw [tvVec_left hij, Pi.zero_apply] at this
    exact zero_ne_one this
  refine ⟨hμ, ?_⟩
  rw [mulVec_smul] at e1
  calc (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j
      = μ⁻¹ • (μ • (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          tvVec i j) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • tvVec i j := by rw [e1]

theorem vecMul_inv_tvVec {g : unitarySU 2 f K n} {μ : K} (hμ : μ ≠ 0)
    (hg : tvVec i j ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = μ • tvVec i j) :
    tvVec i j ᵥ* (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      μ⁻¹ • tvVec i j := by
  have e1 : (μ • tvVec i j) ᵥ* (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = tvVec i j := by
    rw [← hg, vecMul_vecMul, coe_mul_coe_inv, vecMul_one]
  rw [smul_vecMul] at e1
  calc tvVec i j ᵥ* (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = μ⁻¹ • (μ • tvVec i j ᵥ* (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
    _ = μ⁻¹ • tvVec i j := by rw [e1]

variable (i j) in
@[expose] def TvAdm (x : Fin n → K) (s : K) : Prop :=
  x i = 0 ∧ x j = 0 ∧ s + h.bar s = tvBar h x ⬝ᵥ x

@[expose] noncomputable def tvESU (hij : i ≠ j) (x : Fin n → K) (s : K) (hxs : TvAdm h i j x s) :
    unitarySU 2 f K n :=
  ofSL h ⟨tvE h i j x s, det_tvE h hij hxs.1 hxs.2.1 s⟩
    (barTranspose_tvE_mul_self h hij hxs.1 hxs.2.1 hxs.2.2)

@[simp]
theorem coe_tvESU (hij : i ≠ j) (x : Fin n → K) (s : K) (hxs : TvAdm h i j x s) :
    (((tvESU h hij x s hxs : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tvE h i j x s :=
  rfl

theorem tvESU_congr (hij : i ≠ j) {x x' : Fin n → K} {s s' : K} (hx : x = x') (hs : s = s')
    (hxs : TvAdm h i j x s) (hxs' : TvAdm h i j x' s') :
    tvESU h hij x s hxs = tvESU h hij x' s' hxs' := by
  subst hx hs
  rfl

theorem TvAdm.mul {x x' : Fin n → K} {s s' : K} (hxs : TvAdm h i j x s)
    (hxs' : TvAdm h i j x' s') : TvAdm h i j (x + x') (s + s' + tvBar h x ⬝ᵥ x') := by
  obtain ⟨hxi, hxj, hs⟩ := hxs
  obtain ⟨hx'i, hx'j, hs'⟩ := hxs'
  refine ⟨by simp [hxi, hx'i], by simp [hxj, hx'j], ?_⟩
  have hbar : h.bar (tvBar h x ⬝ᵥ x') = tvBar h x' ⬝ᵥ x := by
    simp only [dotProduct, map_sum, map_mul, tvBar_apply, h.bar_bar]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [map_add, map_add, hbar, tvBar_add, add_dotProduct, dotProduct_add, dotProduct_add]
  linear_combination hs + hs'

theorem TvAdm.bar {x : Fin n → K} {s : K} (hxs : TvAdm h i j x s) :
    TvAdm h i j x (h.bar s) := by
  obtain ⟨hxi, hxj, hs⟩ := hxs
  exact ⟨hxi, hxj, by rw [h.bar_bar, add_comm, hs]⟩

theorem TvAdm.zero_zero : TvAdm h i j (0 : Fin n → K) 0 :=
  ⟨rfl, rfl, by simp [tvBar_zero]⟩

theorem tvESU_mul (hij : i ≠ j) {x x' : Fin n → K} {s s' : K} (hxs : TvAdm h i j x s)
    (hxs' : TvAdm h i j x' s') :
    tvESU h hij x s hxs * tvESU h hij x' s' hxs' =
      tvESU h hij (x + x') (s + s' + tvBar h x ⬝ᵥ x') (hxs.mul h hxs') :=
  eq_of_coe_eq (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_tvESU, coe_tvESU, coe_tvESU,
      tvE_mul h hij hxs.1 hxs.2.1 hxs'.1 hxs'.2.1])

theorem tvESU_zero_zero (hij : i ≠ j) : tvESU h hij 0 0 (TvAdm.zero_zero h) = 1 :=
  eq_of_coe_eq (by rw [coe_tvESU, tvE_zero_zero]; rfl)

theorem tvESU_inv (hij : i ≠ j) {x : Fin n → K} {s : K} (hxs : TvAdm h i j x s) :
    (tvESU h hij x s hxs)⁻¹ = tvESU h hij x (h.bar s) (hxs.bar h) := by
  have := h.charP
  rw [inv_eq_iff_mul_eq_one, tvESU_mul]
  have hx : x + x = 0 := by
    ext k
    exact CharTwo.add_self_eq_zero _
  have hs : s + h.bar s + tvBar h x ⬝ᵥ x = 0 := by
    rw [hxs.2.2, CharTwo.add_self_eq_zero]
  rw [tvESU_congr h hij hx hs _ (TvAdm.zero_zero h), tvESU_zero_zero]

variable (i j) in
theorem tvAdm_one : TvAdm h i j (0 : Fin n → K) 1 := by
  have := h.charP
  exact ⟨rfl, rfl, by rw [map_one, CharTwo.add_self_eq_zero, tvBar_zero, zero_dotProduct]⟩

@[expose] noncomputable def tvTransSU (hij : i ≠ j) : unitarySU 2 f K n :=
  tvESU h hij 0 1 (tvAdm_one h i j)

theorem coe_tvTransSU (hij : i ≠ j) :
    (((tvTransSU h hij : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + tvNil i j := by
  rw [tvTransSU, coe_tvESU]
  simp [tvE, tvBar_zero]

theorem mem_centralizer_tvTransSU_iff (hij : i ≠ j) {g : unitarySU 2 f K n} :
    g ∈ centralizer {tvTransSU h hij} ↔
      ∃ μ : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = μ • tvVec i j ∧
        tvVec i j ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = μ • tvVec i j := by
  rw [mem_centralizer_singleton_iff, ← commute_tvNil_iff hij]
  constructor
  · intro hc
    have h1 := congrArg
      (fun x : unitarySU 2 f K n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hc
    simp only [Subgroup.coe_mul, Units.val_mul, coe_tvTransSU, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul] at h1
    exact add_left_cancel h1
  · intro hc
    refine eq_of_coe_eq ?_
    simp only [Subgroup.coe_mul, Units.val_mul, coe_tvTransSU, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, hc]

theorem eq_of_mem_centralizer_tvTransSU (hij : i ≠ j) {g : unitarySU 2 f K n}
    (hg : g ∈ centralizer {tvTransSU h hij}) :
    (∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k i =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k j) ∧
    (∀ l ∈ ({i, j}ᶜ : Finset (Fin n)), ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i l =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j l) := by
  have := h.charP
  obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff h hij).1 hg
  exact ⟨fun k hk => eq_of_mulVec_tvVec h1 hk, fun l hl => eq_of_vecMul_tvVec h2 hl⟩

theorem tvBlock_mul_of_mem_centralizer (hij : i ≠ j) {g g' : unitarySU 2 f K n}
    (hg : g ∈ centralizer {tvTransSU h hij}) (hg' : g' ∈ centralizer {tvTransSU h hij}) :
    tvBlock i j (((g * g' : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        tvBlock i j ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have := h.charP
  rw [Subgroup.coe_mul, Units.val_mul]
  exact tvBlock_mul hij (eq_of_mem_centralizer_tvTransSU h hij hg).1
    (eq_of_mem_centralizer_tvTransSU h hij hg').2

@[expose] def tvRadical (hij : i ≠ j) : Subgroup (unitarySU 2 f K n) where
  carrier := {g | ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = tvVec i j ∧
    tvVec i j ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvVec i j ∧
    tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1}
  one_mem' := ⟨one_mulVec _, vecMul_one _, tvBlock_one i j⟩
  mul_mem' {g g'} hg hg' := by
    have := h.charP
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, hg'.1, hg.1]
    · rw [Subgroup.coe_mul, Units.val_mul, ← vecMul_vecMul, hg.2.1, hg'.2.1]
    · rw [Subgroup.coe_mul, Units.val_mul,
        tvBlock_mul hij (fun k hk => eq_of_mulVec_tvVec (μ := 1) (by rw [one_smul]; exact hg.1) hk)
          (fun l hl => eq_of_vecMul_tvVec (μ := 1) (by rw [one_smul]; exact hg'.2.1) hl),
        hg.2.2, hg'.2.2, Matrix.one_mul]
  inv_mem' {g} hg := by
    have := h.charP
    have h1 : (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        tvVec i j = tvVec i j := by
      have := (inv_mulVec_tvVec hij (μ := 1) (g := g) (by rw [one_smul]; exact hg.1)).2
      rwa [inv_one, one_smul] at this
    have h2 : tvVec i j ᵥ* (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = tvVec i j := by
      have := vecMul_inv_tvVec (μ := 1) (g := g) one_ne_zero (by rw [one_smul]; exact hg.2.1)
      rwa [inv_one, one_smul] at this
    refine ⟨h1, h2, ?_⟩
    have e := tvBlock_mul hij (M := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (M' := (((g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (fun k hk => eq_of_mulVec_tvVec (μ := 1) (by rw [one_smul]; exact hg.1) hk)
      (fun l hl => eq_of_vecMul_tvVec (μ := 1) (by rw [one_smul]; exact h2) hl)
    rw [coe_mul_coe_inv, tvBlock_one, hg.2.2, Matrix.one_mul] at e
    exact e.symm

theorem mem_tvRadical {hij : i ≠ j} {g : unitarySU 2 f K n} :
    g ∈ tvRadical h hij ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = tvVec i j ∧
      tvVec i j ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvVec i j ∧
      tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
  Iff.rfl

theorem tvRadical_le_centralizer (hij : i ≠ j) :
    tvRadical h hij ≤ centralizer {tvTransSU h hij} := fun g hg =>
  (mem_centralizer_tvTransSU_iff h hij).2 ⟨1, by rw [one_smul]; exact hg.1,
    by rw [one_smul]; exact hg.2.1⟩

theorem isPGroup_tvRadical (hij : i ≠ j) : IsPGroup 2 (tvRadical h hij) := by
  have := h.charP
  intro g
  refine ⟨2, Subtype.ext (Subtype.ext (Units.ext ?_))⟩
  obtain ⟨h1, h2, h3⟩ := g.2
  rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
    OneMemClass.coe_one, Units.val_one]
  exact UnitaryHigher.pow_four_eq_one_of_sub_one_pow_three
    (sub_one_pow_three_eq_zero_of_tvVec hij h1 h2 h3)

theorem centralizer_le_normalizer_tvRadical (hij : i ≠ j) :
    centralizer {tvTransSU h hij} ≤ normalizer (tvRadical h hij : Set (unitarySU 2 f K n)) := by
  have key : ∀ c ∈ centralizer {tvTransSU h hij}, ∀ r ∈ tvRadical h hij,
      c * r * c⁻¹ ∈ tvRadical h hij := by
    intro c hc r hr
    obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff h hij).1 hc
    obtain ⟨hμ, h1'⟩ := inv_mulVec_tvVec hij h1
    have h2' := vecMul_inv_tvVec hμ h2
    have hrC := tvRadical_le_centralizer h hij hr
    have hcinv : c⁻¹ ∈ centralizer {tvTransSU h hij} := inv_mem hc
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec,
        ← mulVec_mulVec, h1', mulVec_smul, hr.1, mulVec_smul, h1, smul_smul,
        inv_mul_cancel₀ hμ, one_smul]
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ← vecMul_vecMul,
        ← vecMul_vecMul, h2, smul_vecMul, hr.2.1, smul_vecMul, h2', smul_smul,
        mul_inv_cancel₀ hμ, one_smul]
    · rw [tvBlock_mul_of_mem_centralizer h hij (mul_mem hc hrC) hcinv,
        tvBlock_mul_of_mem_centralizer h hij hc hrC, hr.2.2, Matrix.mul_one,
        ← tvBlock_mul_of_mem_centralizer h hij hc hcinv, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one, tvBlock_one]
  intro c hc
  rw [mem_normalizer_iff]
  intro r
  refine ⟨fun hr => key c hc r hr, fun hr => ?_⟩
  have := key c⁻¹ (inv_mem hc) _ hr
  simpa [mul_assoc] using this

theorem exists_eq_tvESU_of_mem_tvRadical (hij : i ≠ j) {r : unitarySU 2 f K n}
    (hr : r ∈ tvRadical h hij) :
    ∃ (x : Fin n → K) (s : K) (hxs : TvAdm h i j x s), r = tvESU h hij x s hxs := by
  obtain ⟨x, hxi, hxj, s, hs, hrx⟩ :=
    eq_tvE_of_unitary h hij (barTranspose_mul_self_of_mem h r) hr.1 hr.2.1 hr.2.2
  have hxs : TvAdm h i j x s := ⟨hxi, hxj, hs⟩
  exact ⟨x, s, hxs, eq_of_coe_eq (by rw [coe_tvESU, hrx])⟩

theorem tvESU_mem_tvRadical (hij : i ≠ j) {x : Fin n → K} {s : K} (hxs : TvAdm h i j x s) :
    tvESU h hij x s hxs ∈ tvRadical h hij := by
  have := h.charP
  exact ⟨by rw [coe_tvESU]; exact tvE_mulVec_tvVec h hij hxs.1 hxs.2.1 s,
    by rw [coe_tvESU]; exact vecMul_tvE h hij hxs.1 hxs.2.1 s,
    by rw [coe_tvESU]; exact tvBlock_tvE h x s⟩

theorem tvTransSU_mem_tvRadical (hij : i ≠ j) : tvTransSU h hij ∈ tvRadical h hij :=
  tvESU_mem_tvRadical h hij _

theorem mulVec_tvVec_of_mem_unitaryBlock {m : unitarySU 2 f K n}
    (hm : m ∈ unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) :
    ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ tvVec i j = tvVec i j ∧
      tvVec i j ᵥ* ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvVec i j := by
  have hi : i ∉ ({i, j}ᶜ : Finset (Fin n)) := by simp
  have hj : j ∉ ({i, j}ᶜ : Finset (Fin n)) := by simp
  refine ⟨funext fun a => ?_, funext fun b => ?_⟩
  · rw [mulVec_tvVec_apply, (mem_unitaryBlock h).1 hm a i (Or.inr hi),
      (mem_unitaryBlock h).1 hm a j (Or.inr hj), tvVec_apply, one_apply, one_apply]
  · rw [vecMul_tvVec_apply, (mem_unitaryBlock h).1 hm i b (Or.inl hi),
      (mem_unitaryBlock h).1 hm j b (Or.inl hj), tvVec_apply, one_apply, one_apply]
    simp only [eq_comm]

theorem unitaryBlock_le_centralizer_tvTransSU (hij : i ≠ j) :
    unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ≤ centralizer {tvTransSU h hij} := fun m hm =>
  (mem_centralizer_tvTransSU_iff h hij).2 ⟨1,
    by rw [one_smul]; exact (mulVec_tvVec_of_mem_unitaryBlock h hm).1,
    by rw [one_smul]; exact (mulVec_tvVec_of_mem_unitaryBlock h hm).2⟩

theorem tvRadical_inf_unitaryBlock (hij : i ≠ j) :
    tvRadical h hij ⊓ unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hR, hB⟩
  rw [Subgroup.mem_bot]
  refine eq_of_coe_eq (Matrix.ext fun a b => ?_)
  by_cases hab : a ∈ ({i, j}ᶜ : Finset (Fin n)) ∧ b ∈ ({i, j}ᶜ : Finset (Fin n))
  · exact apply_eq_one_apply_of_tvBlock_eq_one hR.2.2 hab.1 hab.2
  · rw [not_and_or] at hab
    exact (mem_unitaryBlock h).1 hB a b hab

theorem conj_tvESU (hij : i ≠ j) {m : unitarySU 2 f K n}
    (hm : m ∈ unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) {x : Fin n → K} {s : K}
    (hxs : TvAdm h i j x s) :
    ∃ hxs' : TvAdm h i j (((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) s,
      m * tvESU h hij x s hxs * m⁻¹ =
        tvESU h hij (((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) s hxs' := by
  have hu := barTranspose_mul_self_of_mem h m
  have hmB := (mem_unitaryBlock h).1 hm
  set M := ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  have hi : i ∉ ({i, j}ᶜ : Finset (Fin n)) := by simp
  have hj : j ∉ ({i, j}ᶜ : Finset (Fin n)) := by simp
  have hMx : ∀ a ∉ ({i, j}ᶜ : Finset (Fin n)), (M *ᵥ x) a = x a := by
    intro a ha
    change ∑ b, M a b * x b = x a
    rw [Finset.sum_eq_single a]
    · rw [hmB a a (Or.inl ha), one_apply_eq, one_mul]
    · intro b _ hba
      rw [hmB a b (Or.inl ha), one_apply_ne (Ne.symm hba), zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ a) h'
  have hnorm : tvBar h (M *ᵥ x) ⬝ᵥ (M *ᵥ x) = tvBar h x ⬝ᵥ x := by
    have e1 : tvBar h (M *ᵥ x) = M.map h.bar *ᵥ tvBar h x :=
      funext fun k => RingHom.map_mulVec h.bar M x k
    rw [e1, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hu, vecMul_one]
  have hxs' : TvAdm h i j (M *ᵥ x) s :=
    ⟨by rw [hMx i hi, hxs.1], by rw [hMx j hj, hxs.2.1], by rw [hnorm]; exact hxs.2.2⟩
  refine ⟨hxs', ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine eq_of_coe_eq ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_tvESU, coe_tvESU]
  exact mul_tvE h (mulVec_tvVec_of_mem_unitaryBlock h hm).1
    (mulVec_tvVec_of_mem_unitaryBlock h hm).2 hu x s

theorem barTranspose_tvBlock_mul_self (hij : i ≠ j) {g : unitarySU 2 f K n}
    (hg : g ∈ centralizer {tvTransSU h hij}) :
    ((tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ *
      tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have := h.charP
  have hrow := (eq_of_mem_centralizer_tvTransSU h hij hg).2
  have hu := barTranspose_mul_self_of_mem h g
  ext k l
  have h1 := congrFun (congrFun hu k) l
  rw [mul_apply, sum_eq_sum_compl_add hij] at h1
  simp only [transpose_apply, map_apply] at h1
  rw [hrow k k.2, hrow l l.2, CharTwo.add_self_eq_zero, add_zero] at h1
  rw [mul_apply]
  simp only [transpose_apply, map_apply, tvBlock_apply]
  rw [h1]
  by_cases hkl : k = l
  · subst hkl
    rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne (fun h' => hkl (Subtype.ext h')), one_apply_ne hkl]

theorem mem_sup_of_det_tvBlock_eq_one (hij : i ≠ j) {g : unitarySU 2 f K n}
    (hg : g ∈ centralizer {tvTransSU h hij})
    (hdet : (tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1) :
    g ∈ unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij := by
  have := h.charP
  set A := tvBlock i j ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hA
  have hAu : (A.map h.bar)ᵀ * A = 1 := barTranspose_tvBlock_mul_self h hij hg
  let A₁ : SpecialLinearGroup ({i, j}ᶜ : Finset (Fin n)) K := ⟨A, hdet⟩
  have hmu : (((LinearPilot.blockEmbed ({i, j}ᶜ : Finset (Fin n)) A₁ :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((LinearPilot.blockEmbed ({i, j}ᶜ : Finset (Fin n)) A₁ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 := by
    rw [LinearPilot.coe_blockEmbed]
    exact blockMatrix_unitary h _ hAu
  obtain ⟨m, hm⟩ : ∃ m : unitarySU 2 f K n,
      toSL h n m = LinearPilot.blockEmbed ({i, j}ᶜ : Finset (Fin n)) A₁ := ⟨ofSL h _ hmu, rfl⟩
  have hmB : m ∈ unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) := by
    rw [mem_unitaryBlock_iff_toSL, hm, ← LinearPilot.range_blockEmbed]
    exact ⟨A₁, rfl⟩
  have hmA : tvBlock i j ((m : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = A := by
    ext k l
    rw [tvBlock_apply, ← coe_toSL h, hm, LinearPilot.coe_blockEmbed, LinearPilot.blockMatrix_apply,
      dite_eq_left ⟨k.2, l.2⟩]
  have hmC := unitaryBlock_le_centralizer_tvTransSU h hij hmB
  set r := m⁻¹ * g with hr
  have hrC : r ∈ centralizer {tvTransSU h hij} := mul_mem (inv_mem hmC) hg
  have hgmr : g = m * r := by rw [hr, mul_inv_cancel_left]
  have hrJ : tvBlock i j ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have e := tvBlock_mul_of_mem_centralizer h hij hmC hrC
    rw [← hgmr, hmA] at e
    have hAdet : IsUnit A.det := by rw [hdet]; exact isUnit_one
    calc tvBlock i j ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = A⁻¹ * (A * tvBlock i j ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAdet, Matrix.one_mul]
      _ = A⁻¹ * A := by rw [← e]
      _ = 1 := Matrix.nonsing_inv_mul _ hAdet
  obtain ⟨μ, h1, h2⟩ := (mem_centralizer_tvTransSU_iff h hij).1 hrC
  have hμ := (inv_mulVec_tvVec hij h1).1
  have hdetr := det_eq_sq hij hμ h1 h2 hrJ
  rw [det_coe_of_mem h r] at hdetr
  have hμ1 : μ = 1 := by
    have h3 : μ ^ 2 = 1 ^ 2 := by rw [one_pow, ← hdetr]
    exact CharTwo.sq_inj.1 h3
  subst hμ1
  have hrR : r ∈ tvRadical h hij := ⟨by rw [h1, one_smul], by rw [h2, one_smul], hrJ⟩
  rw [hgmr]
  exact mul_mem_sup hmB hrR

theorem commutator_centralizer_le (hij : i ≠ j) :
    ⁅centralizer {tvTransSU h hij}, centralizer {tvTransSU h hij}⁆ ≤
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hdet : ∀ x ∈ centralizer {tvTransSU h hij}, ∀ y ∈ centralizer {tvTransSU h hij},
      (tvBlock i j (((x * y : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det =
        (tvBlock i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det *
          (tvBlock i j ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det := fun x hx y hy => by
    rw [tvBlock_mul_of_mem_centralizer h hij hx hy, det_mul]
  have hinv : ∀ x ∈ centralizer {tvTransSU h hij},
      (tvBlock i j ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det *
        (tvBlock i j (((x⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)).det = 1 := fun x hx => by
    rw [← hdet x hx _ (inv_mem hx), mul_inv_cancel, Subgroup.coe_one, Units.val_one, tvBlock_one,
      det_one]
  have hc : ⁅g, g'⁆ ∈ centralizer {tvTransSU h hij} := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
  refine mem_sup_of_det_tvBlock_eq_one h hij hc ?_
  rw [commutatorElement_def, hdet _ (mul_mem (mul_mem hg hg') (inv_mem hg)) _ (inv_mem hg'),
    hdet _ (mul_mem hg hg') _ (inv_mem hg), hdet _ hg _ hg']
  have e1 := hinv g hg
  have e2 := hinv g' hg'
  linear_combination
    (tvBlock i j ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det *
      (tvBlock i j (((g'⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)).det * e1 + e2

theorem commutator_unitaryBlock_eq {I : Finset (Fin n)} (hI3 : 3 ≤ I.card)
    (hIq : (I.card, 2 ^ f) ≠ (3, 2)) : ⁅unitaryBlock h I, unitaryBlock h I⁆ = unitaryBlock h I := by
  have : Group.IsPerfect (unitarySU 2 f K I.card) := (isQuasisimple_unitarySU h hI3 hIq).1
  have : Group.IsPerfect (unitaryBlockEmbed h I).range := Group.IsPerfect.range _
  rw [← range_unitaryBlockEmbed h I]
  exact Subgroup.isPerfect_iff.1 this

theorem commutatorElement_eq_of_mul_eq {G : Type*} [Group G] {a b c : G}
    (hab : a * b = c * (b * a)) : ⁅a, b⁆ = c := by
  rw [commutatorElement_def, hab]
  group

theorem tvBar_single (k : Fin n) (c : K) :
    tvBar h (Pi.single k c) = Pi.single k (h.bar c) := by
  ext a
  rw [tvBar_apply, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

theorem tvAdm_single {k : Fin n} (hk : k ∈ ({i, j}ᶜ : Finset (Fin n))) {c s : K}
    (hs : s + h.bar s = h.bar c * c) : TvAdm h i j (Pi.single k c) s :=
  ⟨Pi.single_eq_of_ne (ne_left_of_mem_compl hk).symm _,
    Pi.single_eq_of_ne (ne_right_of_mem_compl hk).symm _,
    by rw [tvBar_single, single_dotProduct, Pi.single_eq_same, hs]⟩

theorem exists_add_bar_eq {t : K} (ht : h.bar t = t) : ∃ s : K, s + h.bar s = t := by
  obtain ⟨s, hs⟩ := h.traceLin_surjective ⟨t, h.mem_fixedField.mpr ht⟩
  exact ⟨s, congrArg Subtype.val hs⟩

theorem bar_norm (c : K) : h.bar (h.bar c * c) = h.bar c * c := by
  rw [map_mul, h.bar_bar, mul_comm]

theorem commutator_sup_eq (hij : i ≠ j) (hJ : 2 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    (hperf : ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)),
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n))⁆ = unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) :
    ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij,
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij⁆ =
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij := by
  have := h.charP
  set U := unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) with hU
  set X := U ⊔ tvRadical h hij with hX
  set D := ⁅X, X⁆ with hD
  have hRX : tvRadical h hij ≤ X := le_sup_right
  have hUX : U ≤ X := le_sup_left
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc U = ⁅U, U⁆ := hperf.symm
      _ ≤ D := Subgroup.commutator_mono hUX hUX
  obtain ⟨k₀, hk₀⟩ : ({i, j}ᶜ : Finset (Fin n)).Nonempty := Finset.card_pos.1 (by omega)
  have hA : ∀ (t : K) (ht : TvAdm h i j 0 t), tvESU h hij 0 t ht ∈ D := by
    intro t ht
    have hbt : h.bar t = t := by
      have h1 := ht.2.2
      rw [tvBar_zero, zero_dotProduct] at h1
      exact (CharTwo.add_eq_zero.1 h1).symm
    obtain ⟨l, hl⟩ := exists_add_bar_eq h hbt
    obtain ⟨s₁, hs₁⟩ := exists_add_bar_eq h (bar_norm h 1)
    obtain ⟨s₂, hs₂⟩ := exists_add_bar_eq h (bar_norm h l)
    have hx := tvAdm_single h hk₀ hs₁
    have hx' := tvAdm_single h hk₀ hs₂
    have e : ⁅tvESU h hij _ _ hx, tvESU h hij _ _ hx'⁆ = tvESU h hij 0 t ht := by
      refine commutatorElement_eq_of_mul_eq ?_
      rw [tvESU_mul, tvESU_mul, tvESU_mul]
      refine tvESU_congr h hij (by rw [zero_add, add_comm]) ?_ _ _
      rw [tvBar_zero, zero_dotProduct, add_zero, tvBar_single, tvBar_single, single_dotProduct,
        single_dotProduct, Pi.single_eq_same, Pi.single_eq_same, map_one, one_mul, mul_one, ← hl]
      linear_combination (-(h.bar l)) * CharTwo.two_eq_zero (R := K)
    rw [← e]
    exact Subgroup.commutator_mem_commutator (hRX (tvESU_mem_tvRadical h hij hx))
      (hRX (tvESU_mem_tvRadical h hij hx'))
  have hB : ∀ k ∈ ({i, j}ᶜ : Finset (Fin n)), ∀ c : K,
      ∃ (s : K) (hcs : TvAdm h i j (Pi.single k c) s), tvESU h hij (Pi.single k c) s hcs ∈ D := by
    intro k hk c
    obtain ⟨l, hl, hlk⟩ := Finset.exists_mem_ne (by omega : 1 < ({i, j}ᶜ : Finset (Fin n)).card) k
    obtain ⟨κ, hκN, hκ1⟩ := exists_norm_eq_one_ne_one h
    have hκN' : h.norm ((κ⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hκN, inv_one]
    set d : Fin n → K := Pi.mulSingle k (κ : K) * Pi.mulSingle l ((κ⁻¹ : Kˣ) : K) with hd
    have h1N : h.norm 1 = 1 := by simp [UnitaryFieldData.norm]
    have hdN : ∀ a, h.norm (d a) = 1 := by
      intro a
      rw [hd, Pi.mul_apply, norm_mul_eq h, Pi.mulSingle_apply, Pi.mulSingle_apply]
      split_ifs
      · rw [hκN, hκN', one_mul]
      · rw [hκN, h1N, one_mul]
      · rw [h1N, hκN', one_mul]
      · rw [h1N, one_mul]
    have hdprod : ∏ a, d a = 1 := by
      rw [hd]
      simp only [Pi.mul_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
        ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), Units.mul_inv]
    have hdk : d k = κ := by
      rw [hd, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hlk.symm, mul_one]
    have hmB : diagSU h d hdN hdprod ∈ U := by
      refine diagSU_mem_unitaryBlock h d hdN hdprod fun a ha => ?_
      have hak : a ≠ k := fun e => ha (e ▸ hk)
      have hal : a ≠ l := fun e => ha (e ▸ hl)
      rw [hd, Pi.mul_apply, Pi.mulSingle_eq_of_ne hak, Pi.mulSingle_eq_of_ne hal, mul_one]
    have hκ1' : (κ : K) + 1 ≠ 0 := by
      intro h0
      exact hκ1 (Units.ext (by rw [Units.val_one]; exact CharTwo.add_eq_zero.1 h0))
    set y : Fin n → K := Pi.single k (c * ((κ : K) + 1)⁻¹) with hy
    obtain ⟨s₁, hs₁⟩ := exists_add_bar_eq h (bar_norm h (c * ((κ : K) + 1)⁻¹))
    have hys := tvAdm_single h hk hs₁
    obtain ⟨hys', hconj⟩ := conj_tvESU h hij hmB hys
    have hxy : ((diagSU h d hdN hdprod : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y + y =
        Pi.single k c := by
      ext a
      rw [Pi.add_apply, coe_diagSU, mulVec_diagonal, hy, Pi.single_apply, Pi.single_apply]
      split_ifs with hak
      · subst hak
        rw [hdk]
        field_simp
      · rw [mul_zero, add_zero]
    have P := hys'.mul h hys.bar
    rw [hxy] at P
    refine ⟨_, P, ?_⟩
    have e : ⁅diagSU h d hdN hdprod, tvESU h hij y s₁ hys⁆ =
        tvESU h hij (Pi.single k c) _ P := by
      rw [commutatorElement_def, hconj, tvESU_inv, tvESU_mul]
      exact tvESU_congr h hij hxy rfl _ _
    rw [← e]
    exact Subgroup.commutator_mem_commutator (hUX hmB) (hRX (tvESU_mem_tvRadical h hij hys))
  have hC : ∀ x : Fin n → K, x i = 0 → x j = 0 →
      ∃ (s : K) (hxs : TvAdm h i j x s), tvESU h hij x s hxs ∈ D := by
    intro x hxi hxj
    have hsum : x = ∑ k ∈ ({i, j}ᶜ : Finset (Fin n)), Pi.single k (x k) := by
      ext a
      rw [Finset.sum_apply]
      simp only [Pi.single_apply]
      rw [Finset.sum_ite_eq]
      split_ifs with ha
      · rfl
      · rcases eq_or_eq_or_mem_compl i j a with h' | h' | h'
        · rw [h', hxi]
        · rw [h', hxj]
        · exact absurd h' ha
    have key := Finset.sum_induction (s := ({i, j}ᶜ : Finset (Fin n)))
      (fun k => Pi.single k (x k))
      (fun y => y i = 0 ∧ y j = 0 ∧ ∃ (s : K) (hys : TvAdm h i j y s), tvESU h hij y s hys ∈ D)
      (fun a b ha hb => by
        obtain ⟨-, -, s, hs, hsD⟩ := ha
        obtain ⟨-, -, s', hs', hs'D⟩ := hb
        refine ⟨(hs.mul h hs').1, (hs.mul h hs').2.1, _, hs.mul h hs', ?_⟩
        rw [← tvESU_mul h hij hs hs']
        exact mul_mem hsD hs'D)
      ⟨rfl, rfl, 0, TvAdm.zero_zero h, by rw [tvESU_zero_zero]; exact one_mem _⟩
      (fun k hk => by
        obtain ⟨s, hs, hsD⟩ := hB k hk (x k)
        exact ⟨hs.1, hs.2.1, s, hs, hsD⟩)
    rw [← hsum] at key
    exact key.2.2
  intro r hr
  obtain ⟨x, s, hxs, rfl⟩ := exists_eq_tvESU_of_mem_tvRadical h hij hr
  obtain ⟨s', hxs', hD'⟩ := hC x hxs.1 hxs.2.1
  have ht : TvAdm h i j 0 (s' + s) := by
    refine ⟨rfl, rfl, ?_⟩
    rw [tvBar_zero, zero_dotProduct, map_add]
    linear_combination hxs'.2.2 + hxs.2.2 + (tvBar h x ⬝ᵥ x) * CharTwo.two_eq_zero (R := K)
  have e : tvESU h hij x s hxs = tvESU h hij x s' hxs' * tvESU h hij 0 (s' + s) ht := by
    rw [tvESU_mul]
    refine tvESU_congr h hij (by rw [add_zero]) ?_ _ _
    rw [dotProduct_zero, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [e]
  exact mul_mem hD' (hA _ ht)

theorem perfectCore_centralizer_tvTransSU (hij : i ≠ j)
    (hJ : 2 ≤ ({i, j}ᶜ : Finset (Fin n)).card)
    (hperf : ⁅unitaryBlock h ({i, j}ᶜ : Finset (Fin n)),
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n))⁆ = unitaryBlock h ({i, j}ᶜ : Finset (Fin n))) :
    CFSG.Quasithin.perfectCore (centralizer {tvTransSU h hij}) =
      unitaryBlock h ({i, j}ᶜ : Finset (Fin n)) ⊔ tvRadical h hij := by
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect
    (sup_le (unitaryBlock_le_centralizer_tvTransSU h hij) (tvRadical_le_centralizer h hij))
    (commutator_sup_eq h hij hJ hperf))
  calc CFSG.Quasithin.perfectCore (centralizer {tvTransSU h hij})
      ≤ CFSG.Quasithin.derivedSeriesOf (centralizer {tvTransSU h hij}) 1 :=
        CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1
    _ = ⁅centralizer {tvTransSU h hij}, centralizer {tvTransSU h hij}⁆ := by
        rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero]
    _ ≤ _ := commutator_centralizer_le h hij

end CFSG.SeitzReduction.UnitaryPilot

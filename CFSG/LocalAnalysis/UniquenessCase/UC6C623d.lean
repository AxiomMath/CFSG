module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open scoped Matrix

theorem card_gl3 : Nat.card (GL (Fin 3) (ZMod 3)) = 11232 := by
  have := Matrix.card_GL_field (n := 3) (𝔽 := ZMod 3)
  simpa [Fin.prod_univ_three] using this

def fixAddSubgroup (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) : AddSubgroup (Fin 3 → ZMod 3) where
  carrier := {v | M *ᵥ v = v}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.mulVec_add, ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.mulVec_neg, ha]

theorem eq_zero_of_fixed_of_orderOf_thirteen {s : GL (Fin 3) (ZMod 3)} (hs : orderOf s = 13)
    {v : Fin 3 → ZMod 3} (hv : (s : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v) : v = 0 := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 3), M = (s : Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
    ⟨_, rfl⟩
  rw [← hM] at hv
  have hM13 : M ^ 13 = 1 := by
    rw [hM, ← Units.val_pow_eq_pow_val, ← hs, pow_orderOf_eq_one, Units.val_one]
  have hMne : M ≠ 1 := by
    intro h1
    have : s = 1 := Units.ext (by rw [← hM, h1]; rfl)
    rw [this, orderOf_one] at hs
    omega
  let f : Function.End (Fin 3 → ZMod 3) := fun w => M *ᵥ w
  have hf : ∀ n : ℕ, ∀ w, (f ^ n) w = (M ^ n) *ᵥ w := by
    intro n
    induction n with
    | zero => intro w; simp [Matrix.one_mulVec]; rfl
    | succ n ih =>
      intro w
      rw [pow_succ]
      show (f ^ n) (f w) = _
      rw [ih, pow_succ, ← Matrix.mulVec_mulVec]
  have hf13 : f ^ 13 ^ 1 = 1 := by
    funext w
    rw [pow_one, hf, hM13, Matrix.one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := Fin 3 → ZMod 3) (p := 13) hf13
  have hset : f.fixedPoints = (fixAddSubgroup M : Set (Fin 3 → ZMod 3)) := rfl
  have hcardV : Fintype.card (Fin 3 → ZMod 3) = 27 := by
    simp [Fintype.card_fun, ZMod.card]
  have hcardF : Fintype.card f.fixedPoints = Nat.card (fixAddSubgroup M) := by
    rw [← Nat.card_eq_fintype_card, hset]
    rfl
  rw [hcardV, hcardF] at hmod
  have hdvd : Nat.card (fixAddSubgroup M) ∣ 27 := by
    have := AddSubgroup.card_addSubgroup_dvd_card (fixAddSubgroup M)
    rwa [show Nat.card (Fin 3 → ZMod 3) = 27 by
      rw [Nat.card_eq_fintype_card, hcardV]] at this
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (by simpa using hdvd : Nat.card (fixAddSubgroup M) ∣ 3 ^ 3)
  rw [hk] at hmod
  have hk' : k = 0 ∨ k = 3 := by
    interval_cases k <;> simp [Nat.ModEq] at hmod ⊢
  rcases hk' with rfl | rfl
  ·
    have h1 : Nat.card (fixAddSubgroup M) = 1 := by rw [hk]; rfl
    have hbot : fixAddSubgroup M = ⊥ := (AddSubgroup.eq_bot_of_card_eq _ h1)
    have hmem : v ∈ fixAddSubgroup M := hv
    rw [hbot] at hmem
    exact (AddSubgroup.mem_bot).1 hmem
  · exfalso
    have htop : fixAddSubgroup M = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      rw [hk, show Nat.card (Fin 3 → ZMod 3) = 27 by rw [Nat.card_eq_fintype_card, hcardV]]
      norm_num
    apply hMne
    ext i j
    have h2 : M *ᵥ Pi.single j 1 = Pi.single j 1 := by
      have : Pi.single j (1 : ZMod 3) ∈ fixAddSubgroup M := by rw [htop]; trivial
      exact this
    have h3 := congrFun h2 i
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using h3

theorem exists_invariant_line_of_isPGroup_two {G : Subgroup (GL (Fin 3) (ZMod 3))}
    (hG : IsPGroup 2 G) : ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ ∀ g ∈ G,
      ∃ c : ZMod 3, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = c • v := by
  classical
  let ψ : G →* LinearMap.GeneralLinearGroup (ZMod 3) (Fin 3 → ZMod 3) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) (ZMod 3) ≃* _).toMonoidHom.comp G.subtype
  letI : MulAction G (Projectivization (ZMod 3) (Fin 3 → ZMod 3)) := MulAction.compHom _ ψ
  have hmod := hG.card_modEq_card_fixedPoints (α := Projectivization (ZMod 3) (Fin 3 → ZMod 3))
  have hcard : Nat.card (Projectivization (ZMod 3) (Fin 3 → ZMod 3)) = 13 := by
    have h := Projectivization.card' (k := ZMod 3) (V := Fin 3 → ZMod 3)
    have hV : Nat.card (Fin 3 → ZMod 3) = 27 := by
      rw [Nat.card_eq_fintype_card]; simp [Fintype.card_fun, ZMod.card]
    rw [hV, Nat.card_zmod] at h
    omega
  rw [hcard] at hmod
  have hne : Nat.card (MulAction.fixedPoints G (Projectivization (ZMod 3) (Fin 3 → ZMod 3))) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    revert hmod
    decide
  obtain ⟨x, hx⟩ : Nonempty (MulAction.fixedPoints G (Projectivization (ZMod 3) (Fin 3 → ZMod 3))) :=
    (Nat.card_pos_iff.1 (Nat.pos_of_ne_zero hne)).1
  refine ⟨x.rep, x.rep_nonzero, fun g hg => ?_⟩
  have h1 : (ψ ⟨g, hg⟩) • x = x := hx ⟨g, hg⟩
  rw [Projectivization.generalLinearGroup_smul_def] at h1
  have h3 := h1
  conv_lhs at h3 => rw [← Projectivization.mk_rep x, Projectivization.map_mk]
  conv_rhs at h3 => rw [← Projectivization.mk_rep x]
  rw [Projectivization.mk_eq_mk_iff'] at h3
  obtain ⟨a, ha⟩ := h3
  refine ⟨a, ?_⟩
  exact ha.symm

theorem exists_normal_cyclic_thirteen {G : Subgroup (GL (Fin 3) (ZMod 3))} (h3 : ¬ 3 ∣ Nat.card G)
    (h13 : 13 ∣ Nat.card G) :
    ∃ s : GL (Fin 3) (ZMod 3), s ∈ G ∧ orderOf s = 13 ∧
      ∀ g ∈ G, ∃ k : ℤ, g * s * g⁻¹ = s ^ k := by
  classical
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hdvd : Nat.card G ∣ 416 * 27 := by
    have := Subgroup.card_subgroup_dvd_card G
    rwa [card_gl3] at this
  have hcop : Nat.Coprime (Nat.card G) 27 := by
    have : Nat.Coprime (Nat.card G) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    simpa using Nat.Coprime.pow_right 3 this
  have hdvd416 : Nat.card G ∣ 416 := hcop.dvd_of_dvd_mul_right hdvd
  obtain ⟨m, hm⟩ := h13
  have hm32 : m ∣ 32 := by
    have h1 : 13 * m ∣ 13 * 32 := by rw [← hm]; simpa using hdvd416
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  obtain ⟨P⟩ : Nonempty (Sylow 13 G) := inferInstance
  have h13m : ¬ 13 ∣ m := by
    intro h
    have : 13 ∣ 32 := h.trans hm32
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm32
  have hPcard : Nat.card P = 13 := by
    rw [Sylow.card_eq_multiplicity, hm, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self (Fact.out), Nat.factorization_eq_zero_of_not_dvd h13m]
    simp
  have hindex : P.index = m := by
    have := Subgroup.card_mul_index (P : Subgroup G)
    rw [hPcard, hm] at this
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  have hn : Nat.card (Sylow 13 G) = 1 := by
    have hmod := card_sylow_modEq_one 13 G
    have hd : Nat.card (Sylow 13 G) ∣ 32 := (P.card_dvd_index).trans (hindex ▸ hm32)
    have hd' : Nat.card (Sylow 13 G) ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num]
      exact hd
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd'
    rw [hj'] at hmod ⊢
    interval_cases j <;> simp_all [Nat.ModEq]
  haveI : Subsingleton (Sylow 13 G) := (Nat.card_eq_one_iff_unique.1 hn).1
  have hnorm : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  haveI : IsCyclic P := isCyclic_of_prime_card hPcard
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := (P : Subgroup G))
  have hord : orderOf (t : G) = 13 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ht]
    exact hPcard
  refine ⟨((t : G) : GL (Fin 3) (ZMod 3)), (t : G).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hord
  · intro g hg
    have hmem : (⟨g, hg⟩ : G) * (t : G) * (⟨g, hg⟩ : G)⁻¹ ∈ (P : Subgroup G) := hnorm.conj_mem _ t.2 _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ht ⟨_, hmem⟩)
    refine ⟨k, ?_⟩
    have := congrArg (fun z : (P : Subgroup G) => ((z : G) : GL (Fin 3) (ZMod 3))) hk
    simpa using this.symm

theorem conj_eq_self_or_inv_of_order_thirteen {G : Type*} [Group G] {s y : G} (hs : orderOf s = 13)
    (hy2 : y * y = 1) {m : ℤ} (hm : y * s * y⁻¹ = s ^ m) :
    y * s * y⁻¹ = s ∨ y * s * y⁻¹ = s⁻¹ := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hss : s = s ^ (m * m) := by
    calc s = y * (y * s * y⁻¹) * y⁻¹ := by rw [hyinv, ← mul_assoc, ← mul_assoc, hy2, one_mul, mul_assoc, hy2, mul_one]
      _ = y * s ^ m * y⁻¹ := by rw [hm]
      _ = (y * s * y⁻¹) ^ m := (conj_zpow).symm
      _ = (s ^ m) ^ m := by rw [hm]
      _ = s ^ (m * m) := by rw [← zpow_mul]
  have h1 : s ^ (m * m - 1) = 1 := by
    rw [zpow_sub_one, ← hss, mul_inv_cancel]
  have h2 : (13 : ℤ) ∣ m * m - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hs] at this
  have hp : Prime (13 : ℤ) := by
    have := Nat.prime_iff_prime_int.1 (by decide : Nat.Prime 13)
    simpa using this
  have h3 : (13 : ℤ) ∣ (m - 1) * (m + 1) := by
    have : (m - 1) * (m + 1) = m * m - 1 := by ring
    rwa [this]
  rcases hp.dvd_or_dvd h3 with h4 | h4
  · left
    have : s ^ (m - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rwa [hs])
    rw [hm]
    have h5 : s ^ m = s := by
      rw [← mul_inv_eq_one, ← zpow_sub_one]
      exact this
    exact h5
  · right
    have : s ^ (m + 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rwa [hs])
    rw [hm]
    have h5 : s ^ m = s⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
      exact this
    exact h5

theorem exists_fixed_of_inverted {s y : GL (Fin 3) (ZMod 3)} (hs : orderOf s = 13)
    (hinv : y * s * y⁻¹ = s⁻¹) :
    ∃ v : Fin 3 → ZMod 3, v ≠ 0 ∧ (s : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v := by
  classical
  have hs13 : s ^ 13 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hdet : (s : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 := by
    have h1 : ((s : Matrix (Fin 3) (Fin 3) (ZMod 3)).det) ^ 13 = 1 := by
      rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hs13, Units.val_one, Matrix.det_one]
    revert h1
    generalize (s : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = d
    revert d
    decide
  have hconj : (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) * (s : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
      ((y⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
        ((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [← Units.val_mul, ← Units.val_mul, hinv]
  have h1 : (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) -
      ((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) * (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3))) *
        ((y⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, hconj, Units.mul_inv]
  have h2 : (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) -
      ((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      -(((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3)))) := by
    rw [Matrix.mul_sub, mul_one, Units.inv_mul, neg_sub]
  have hdN : (((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3))).det = 1 := by
    have := Matrix.det_mul (((s⁻¹ : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)))
      (s : Matrix (Fin 3) (Fin 3) (ZMod 3))
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, hdet, mul_one] at this
    exact this.symm
  have h3 : (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3))).det =
      - (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3))).det := by
    have e1 := congrArg Matrix.det h1
    have e2 := congrArg Matrix.det h2
    rw [Matrix.det_units_conj] at e1
    rw [Matrix.det_neg, Matrix.det_mul, hdN, one_mul] at e2
    rw [e1, Fintype.card_fin] at e2
    linear_combination e2
  have h4 : (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3))).det = 0 := by
    revert h3
    generalize (1 - (s : Matrix (Fin 3) (Fin 3) (ZMod 3))).det = d
    revert d
    decide
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h4
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

theorem false_of_commuting_line {s y : GL (Fin 3) (ZMod 3)} (hs : orderOf s = 13)
    (hcomm : y * s = s * y) {v₀ : Fin 3 → ZMod 3} (hv₀ : v₀ ≠ 0)
    (hfix : ∀ w : Fin 3 → ZMod 3, (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w ↔
      ∃ c : ZMod 3, w = c • v₀) : False := by
  classical
  have hs13 : s ^ 13 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hyv : (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v₀ = v₀ := (hfix v₀).2 ⟨1, by simp⟩
  have hsv : (y : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ((s : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v₀) =
      (s : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v₀ := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hcomm, Units.val_mul, ← Matrix.mulVec_mulVec, hyv]
  obtain ⟨c, hc⟩ := (hfix _).1 hsv
  have hpow : ∀ n : ℕ, ((s ^ n : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v₀ =
      c ^ n • v₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Units.val_mul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hc, smul_smul,
        pow_succ]
  have h13 : c ^ 13 • v₀ = v₀ := by
    have := hpow 13
    rwa [hs13, Units.val_one, Matrix.one_mulVec, eq_comm] at this
  have hc13 : c ^ 13 = 1 := by
    have h0 : (c ^ 13 - 1) • v₀ = 0 := by rw [sub_smul, h13, one_smul, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv₀
  have key : ∀ d : ZMod 3, d ^ 13 = 1 → d = 1 := by decide
  have hc1 : c = 1 := key c hc13
  rw [hc1, one_smul] at hc
  exact hv₀ (eq_zero_of_fixed_of_orderOf_thirteen hs hc)

theorem false_of_threePrime_noLine {G : Subgroup (GL (Fin 3) (ZMod 3))} (h3 : ¬ 3 ∣ Nat.card G)
    (hline : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ g ∈ G, ∀ c : ZMod 3,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ≠ c • v)
    {x : GL (Fin 3) (ZMod 3)} (hxG : x ∈ G) (hx4 : x ^ 4 = 1) {v₀ : Fin 3 → ZMod 3} (hv₀ : v₀ ≠ 0)
    (hfix : ∀ w : Fin 3 → ZMod 3, ((x ^ 2 : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w ↔ ∃ c : ZMod 3, w = c • v₀) : False := by
  classical
  have h13 : 13 ∣ Nat.card G := by
    by_contra h13
    have hdvd : Nat.card G ∣ 32 * (13 * 27) := by
      have := Subgroup.card_subgroup_dvd_card G
      rwa [card_gl3] at this
    have hc : Nat.Coprime (Nat.card G) (13 * 27) := by
      refine Nat.Coprime.mul_right ?_ ?_
      · exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 13)).2 h13).symm
      · have := Nat.Coprime.pow_right 3
          (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm)
        simpa using this
    have h32 : Nat.card G ∣ 2 ^ 5 := hc.dvd_of_dvd_mul_right hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h32
    obtain ⟨v, hv0, hv⟩ := exists_invariant_line_of_isPGroup_two (IsPGroup.of_card hk)
    obtain ⟨g, hg, hgv⟩ := hline v hv0
    obtain ⟨c, hc⟩ := hv g hg
    exact hgv c hc
  obtain ⟨s, hsG, hs13, hconj⟩ := exists_normal_cyclic_thirteen h3 h13
  have hyG : x ^ 2 ∈ G := G.pow_mem hxG 2
  have hy2 : x ^ 2 * x ^ 2 = 1 := by rw [← pow_add]; exact hx4
  obtain ⟨m, hm⟩ := hconj (x ^ 2) hyG
  rcases conj_eq_self_or_inv_of_order_thirteen hs13 hy2 hm with h | h
  · refine false_of_commuting_line hs13 ?_ hv₀ hfix
    exact (mul_inv_eq_iff_eq_mul.1 h)
  · obtain ⟨v, hv0, hv⟩ := exists_fixed_of_inverted hs13 h
    exact hv0 (eq_zero_of_fixed_of_orderOf_thirteen hs13 hv)

theorem false_of_irreducible_threePrime {G : Subgroup (GL (Fin 3) (ZMod 3))}
    (hirr : ∀ W : Submodule (ZMod 3) (Fin 3 → ZMod 3),
      (∀ g ∈ G, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h3 : ¬ 3 ∣ Nat.card G) {x : GL (Fin 3) (ZMod 3)} (hxG : x ∈ G) (hord : orderOf x = 4)
    {Z : Submodule (ZMod 3) (Fin 3 → ZMod 3)} (hZ : Module.finrank (ZMod 3) Z = 1)
    (hfix : {v : Fin 3 → ZMod 3 | ((x ^ 2 : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = v} = (Z : Set (Fin 3 → ZMod 3))) : False := by
  classical
  have hx4 : x ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  obtain ⟨v₀, hv₀⟩ : ∃ v : ↥Z, v ≠ 0 := Module.finrank_pos_iff_exists_ne_zero.1 (by rw [hZ]; exact Nat.one_pos)
  have hgen := (finrank_eq_one_iff_of_nonzero' v₀ hv₀).1 hZ
  have hv₀' : (v₀ : Fin 3 → ZMod 3) ≠ 0 := fun h => hv₀ (Subtype.ext h)
  have hline : ∀ v : Fin 3 → ZMod 3, v ≠ 0 → ∃ g ∈ G, ∀ c : ZMod 3,
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ≠ c • v := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    have hinv : ∀ g ∈ G, ∀ w ∈ Submodule.span (ZMod 3) {v},
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ Submodule.span (ZMod 3) {v} := by
      intro g hg w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      obtain ⟨c, hc⟩ := hcon g hg
      rw [Matrix.mulVec_smul, hc, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    rcases hirr _ hinv with h | h
    · apply hv
      have : v ∈ Submodule.span (ZMod 3) {v} := Submodule.mem_span_singleton_self v
      rw [h] at this
      simpa using this
    · have h1 : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {v}) = 1 := finrank_span_singleton hv
      rw [h, finrank_top] at h1
      simp at h1
  have hfix' : ∀ w : Fin 3 → ZMod 3, ((x ^ 2 : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w ↔ ∃ c : ZMod 3, w = c • (v₀ : Fin 3 → ZMod 3) := by
    intro w
    have h1 : (((x ^ 2 : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w = w) ↔
        w ∈ Z := by
      have := Set.ext_iff.1 hfix w
      simpa using this
    rw [h1]
    constructor
    · intro hw
      obtain ⟨c, hc⟩ := hgen ⟨w, hw⟩
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
    · rintro ⟨c, rfl⟩
      exact Z.smul_mem c v₀.2
  exact false_of_threePrime_noLine h3 hline hxG hx4 hv₀' hfix'

end CFSG.LocalAnalysis.UniquenessCase.UC6

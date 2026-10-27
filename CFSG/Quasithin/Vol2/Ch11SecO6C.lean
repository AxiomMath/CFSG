module

public import CFSG.LocalAnalysis.SignalizerFunctor.FrattiniAutomorphismKernel
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

open scoped IsMulCommutative

section LinAlg

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_smul_of_commute [FiniteDimensional k V] (hV : Module.finrank k V ≤ 2)
    {T A B : Module.End k V} (hA : T * A = A * T) (hB : T * B = B * T) (hAB : A * B ≠ B * A) :
    ∃ c : k, T = c • 1 := by
  by_contra hT
  obtain ⟨v, hv⟩ : ∃ v, LinearIndependent k ![v, T v] := by
    by_contra h
    push Not at h
    exact hT (LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent h)
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by
    have := hv.fintype_card_le_finrank
    rw [Fintype.card_fin] at this ⊢
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hv hcard
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = T v := by simp [b]
  have key : ∀ S : Module.End k V, T * S = S * T → ∃ a c : k, S = a • 1 + c • T := by
    intro S hS
    obtain ⟨a, c, hSv⟩ : ∃ a c : k, S v = a • v + c • T v := by
      have h := b.sum_repr (S v)
      rw [Fin.sum_univ_two, hb0, hb1] at h
      exact ⟨_, _, h.symm⟩
    have hST : S (T v) = T (S v) := by
      have := congrArg (fun f : Module.End k V => f v) hS
      simpa [Module.End.mul_apply] using this.symm
    refine ⟨a, c, b.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · rw [hb0, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        Module.End.one_apply]
      exact hSv
    · rw [hb1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        Module.End.one_apply, hST, hSv, map_add, map_smul, map_smul]
  obtain ⟨a₁, c₁, rfl⟩ := key A hA
  obtain ⟨a₂, c₂, rfl⟩ := key B hB
  apply hAB
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
    smul_smul]
  rw [mul_comm a₂ a₁, mul_comm a₂ c₁, mul_comm c₂ a₁, mul_comm c₂ c₁]
  abel

end LinAlg

variable {X : Type} [Group X]

@[expose] noncomputable def autP (r : ℕ) (β : MulAut X) : MulAut ↥(CFSG.pCore r X) :=
  (β.subgroupMap (CFSG.pCore r X)).trans (MulEquiv.subgroupCongr (CFSG.pCore_map_iso r β))

theorem autP_coe (r : ℕ) (β : MulAut X) (d : ↥(CFSG.pCore r X)) :
    ((autP r β d : ↥(CFSG.pCore r X)) : X) = β d := rfl

@[expose] noncomputable def autV (r : ℕ) (β : MulAut X) :
    MulAut (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) :=
  QuotientGroup.congr _ _ (autP r β) (Subgroup.characteristic_iff_map_eq.mp inferInstance _)

theorem autV_mk (r : ℕ) (β : MulAut X) (d : ↥(CFSG.pCore r X)) :
    autV r β (d : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) =
      ((autP r β d : ↥(CFSG.pCore r X)) : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) :=
  QuotientGroup.congr_mk _ _ _ _ d

theorem autV_mul (r : ℕ) (β γ : MulAut X) : autV r (β * γ) = autV r β * autV r γ := by
  ext v
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
  rw [MulAut.mul_apply, autV_mk, autV_mk, autV_mk]
  rfl

theorem autV_one (r : ℕ) : autV r (1 : MulAut X) = 1 := by
  ext v
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective v
  rw [autV_mk]
  rfl

@[expose] def ActsScalar (r : ℕ) (β : MulAut X) (k : ℕ) : Prop :=
  ∀ d ∈ CFSG.pCore r X, (d ^ k)⁻¹ * β d ∈ frattiniIn (CFSG.pCore r X)

theorem actsScalar_iff (r : ℕ) (β : MulAut X) (k : ℕ) :
    ActsScalar r β k ↔ ∀ d : ↥(CFSG.pCore r X),
      autV r β (d : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) = (d : _ ⧸ _) ^ k := by
  constructor
  · intro h d
    rw [autV_mk, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]
    obtain ⟨y, hy, hyd⟩ := h d d.2
    have hyd' : (y : X) = ((d : X) ^ k)⁻¹ * β d := hyd
    have e : (d ^ k)⁻¹ * autP r β d = y := Subtype.ext (by rw [hyd']; simp [autP_coe])
    rw [e]
    exact hy
  · intro h d hd
    have h1 := h ⟨d, hd⟩
    rw [autV_mk, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq] at h1
    exact ⟨_, h1, by simp [autP_coe]⟩

theorem actsTrivially_iff (r : ℕ) (x : X) :
    ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) x ↔ ActsScalar r (MulAut.conj x) 1 := by
  simp only [ActsTriviallyOnFrattiniQuotient, ActsScalar, pow_one, MulAut.conj_apply]

theorem autP_mul (r : ℕ) (β γ : MulAut X) : autP r (β * γ) = autP r β * autP r γ := by
  ext d
  rfl

theorem autP_one (r : ℕ) : autP r (1 : MulAut X) = 1 := by
  ext d
  rfl

theorem autP_pow (r : ℕ) (β : MulAut X) (n : ℕ) : autP r (β ^ n) = autP r β ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, autP_one]
  | succ n ih => rw [pow_succ, autP_mul, ih, pow_succ]

theorem pow_mem_frattiniIn [Finite X] {r : ℕ} [Fact r.Prime] {d : X} (hd : d ∈ CFSG.pCore r X) :
    d ^ r ∈ frattiniIn (CFSG.pCore r X) := by
  have : Fact (IsPGroup r ↥(CFSG.pCore r X)) := ⟨CFSG.pCore_isPGroup⟩
  exact ⟨_, CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥(CFSG.pCore r X)) (p := r) ⟨d, hd⟩,
    rfl⟩

section Lin

variable [Finite X] (r : ℕ) [Fact r.Prime]

instance fact_isPGroup_pCore : Fact (IsPGroup r ↥(CFSG.pCore r X)) := ⟨CFSG.pCore_isPGroup⟩

instance isElementaryAbelian_frattiniQuot :
    IsElementaryAbelian r (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) :=
  CFSG.isElementaryAbelian_quotient_frattini

@[expose] noncomputable def linV (β : MulAut X) :
    Module.End (ZMod r) (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) :=
  (MulEquiv.toAdditive (autV r β)).toAddMonoidHom.toZModLinearMap r

theorem linV_ofMul (β : MulAut X) (v : ↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) :
    linV r β (Additive.ofMul v) = Additive.ofMul (autV r β v) := rfl

theorem linV_mul (β γ : MulAut X) : linV r (β * γ) = linV r β * linV r γ := by
  ext w
  rw [Module.End.mul_apply]
  change Additive.ofMul (autV r (β * γ) w.toMul) = Additive.ofMul (autV r β (autV r γ w.toMul))
  rw [autV_mul]
  rfl

theorem linV_one : linV r (1 : MulAut X) = 1 := by
  ext w
  change Additive.ofMul (autV r (1 : MulAut X) w.toMul) = w
  rw [autV_one]
  rfl

theorem actsScalar_iff_linV (β : MulAut X) (k : ℕ) :
    ActsScalar r β k ↔ linV r β = (k : ZMod r) • 1 := by
  rw [actsScalar_iff]
  constructor
  · intro h
    ext w
    obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective w.toMul
    rw [LinearMap.smul_apply, Module.End.one_apply, Nat.cast_smul_eq_nsmul]
    change Additive.ofMul (autV r β w.toMul) = k • w
    rw [← hd, h d, ofMul_pow, hd]
    rfl
  · intro h d
    have h1 := congrArg (fun f => f (Additive.ofMul (d : ↥(CFSG.pCore r X) ⧸ _))) h
    simp only [LinearMap.smul_apply, Module.End.one_apply, Nat.cast_smul_eq_nsmul,
      linV_ofMul] at h1
    rw [← ofMul_pow] at h1
    exact Additive.ofMul.injective h1

theorem finrank_le_two (hV : Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) ≤ r ^ 2) :
    Module.finrank (ZMod r) (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) ≤ 2 := by
  have h := FiniteField.pow_finrank_eq_natCard r
    (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)))
  have h2 : r ^ Module.finrank (ZMod r)
      (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) ≤ r ^ 2 := by
    rw [h]
    exact hV
  exact (Nat.pow_le_pow_iff_right (Fact.out : r.Prime).one_lt).mp h2

theorem ActsScalar.mul {α β : MulAut X} {k m : ℕ} (hα : ActsScalar r α k) (hβ : ActsScalar r β m) :
    ActsScalar r (α * β) (k * m) := by
  rw [actsScalar_iff_linV] at hα hβ ⊢
  rw [linV_mul, hα, hβ, smul_mul_smul_comm, mul_one, Nat.cast_mul]

theorem actsScalar_of_comm
    (hV : Nat.card (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)) ≤ r ^ 2)
    (hF : ∀ f ∈ CFSG.fittingSubgroup X, ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) f)
    (hna : ∃ x y : X, ¬ ActsTriviallyOnFrattiniQuotient (CFSG.pCore r X) (x * y * x⁻¹ * y⁻¹))
    {α : MulAut X} (hα : ∀ x : X, x⁻¹ * α x ∈ CFSG.fittingSubgroup X) :
    ∃ k : ℕ, ActsScalar r α k := by
  obtain ⟨x, y, hxy⟩ := hna
  let L : X → Module.End (ZMod r) (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) :=
    fun z => linV r (MulAut.conj z)
  have hLmul : ∀ a b : X, L (a * b) = L a * L b := fun a b => by
    simp only [L, map_mul, linV_mul]
  have hL1 : L 1 = 1 := by simp only [L, map_one, linV_one]
  have hLF : ∀ f ∈ CFSG.fittingSubgroup X, L f = 1 := fun f hf => by
    have h := (actsTrivially_iff r f).mp (hF f hf)
    rw [actsScalar_iff_linV, Nat.cast_one, one_smul] at h
    exact h
  have hcomm : ∀ z : X, linV r α * L z = L z * linV r α := by
    intro z
    have h1 : α * MulAut.conj z = MulAut.conj (α z) * α := by
      ext w
      simp [MulAut.conj_apply, map_mul, map_inv]
    have h2 : linV r α * L z = L (α z) * linV r α := by
      simp only [L]
      rw [← linV_mul, h1, linV_mul]
    have h3 : L (α z) = L z := by
      have e : α z = z * (z⁻¹ * α z) := by group
      rw [e, hLmul, hLF _ (hα z), mul_one]
    rw [h2, h3]
  have hne : L x * L y ≠ L y * L x := by
    intro h
    apply hxy
    rw [actsTrivially_iff, actsScalar_iff_linV, Nat.cast_one, one_smul]
    change L (x * y * x⁻¹ * y⁻¹) = 1
    rw [hLmul, hLmul, hLmul, h]
    calc L y * L x * L x⁻¹ * L y⁻¹ = L y * L (x * x⁻¹) * L y⁻¹ := by
          rw [hLmul x, mul_assoc (L y)]
      _ = 1 := by rw [mul_inv_cancel, hL1, mul_one, ← hLmul, mul_inv_cancel, hL1]
  obtain ⟨c, hc⟩ := exists_smul_of_commute (finrank_le_two r hV) (hcomm x) (hcomm y) hne
  refine ⟨c.val, ?_⟩
  rw [actsScalar_iff_linV, hc, ZMod.natCast_zmod_val]

theorem actsScalar_comm {α : MulAut X} {k : ℕ} (hk : ActsScalar r α k) (γ : MulAut X) :
    ActsScalar r (α * γ * α⁻¹ * γ⁻¹) 1 := by
  rw [actsScalar_iff_linV] at hk ⊢
  have hc : linV r α * linV r γ = linV r γ * linV r α := by
    rw [hk, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinv : ∀ β : MulAut X, linV r β⁻¹ * linV r β = 1 := fun β => by
    rw [← linV_mul, inv_mul_cancel, linV_one]
  have hinv' : ∀ β : MulAut X, linV r β * linV r β⁻¹ = 1 := fun β => by
    rw [← linV_mul, mul_inv_cancel, linV_one]
  rw [Nat.cast_one, one_smul, linV_mul, linV_mul, linV_mul, hc, mul_assoc (linV r γ),
    hinv', mul_one, hinv']

theorem actsScalar_sign {α : MulAut X} {k : ℕ} (hk : ActsScalar r α k)
    (h2 : ActsScalar r (α ^ 2) 1) : ActsScalar r α 1 ∨ ActsScalar r α (r - 1) := by
  rw [actsScalar_iff_linV] at hk h2
  rw [actsScalar_iff_linV, actsScalar_iff_linV]
  rcases subsingleton_or_nontrivial
    (Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X))) with hs | hn
  · left
    exact LinearMap.ext fun w => Subsingleton.elim _ _
  have := hn
  obtain ⟨w, hw⟩ := exists_ne (0 : Additive (↥(CFSG.pCore r X) ⧸ frattini ↥(CFSG.pCore r X)))
  have hsq' : linV r (α ^ 2) = ((k : ZMod r) * k) • 1 := by
    rw [pow_two, linV_mul, hk, smul_mul_smul_comm, mul_one]
  have hsq : ((k : ZMod r) * k - 1) • w = 0 := by
    have h := congrArg (fun f => f w) (hsq'.symm.trans h2)
    simp only [LinearMap.smul_apply, Module.End.one_apply, Nat.cast_one, one_smul] at h
    rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp hsq with h | h
  · have h' : ((k : ZMod r) - 1) * ((k : ZMod r) + 1) = 0 := by
      rw [← h]
      ring
    rcases mul_eq_zero.mp h' with h1 | h1
    · left
      rw [hk, sub_eq_zero.mp h1, Nat.cast_one]
    · right
      rw [hk, eq_neg_of_add_eq_zero_left h1, Nat.cast_sub (Fact.out : r.Prime).one_le,
        ZMod.natCast_self, Nat.cast_one, zero_sub]
      rfl
  · exact absurd h hw

theorem fix_of_actsScalar_one (hr2 : r ≠ 2) {α : MulAut X} {e : ℕ} (hαe : α ^ 2 ^ e = 1)
    (h : ActsScalar r α 1) : ∀ d ∈ CFSG.pCore r X, α d = d := by
  have hk : autP r α ∈
      CFSG.SignalizerFunctor.Helpers.frattiniAutomorphismKernel ↥(CFSG.pCore r X) := by
    intro d
    have h1 := (actsScalar_iff r α 1).mp h d
    rw [autV_mk, pow_one] at h1
    exact h1
  have hpow : autP r α ^ 2 ^ e = 1 := by rw [← autP_pow, hαe, autP_one]
  have h2 : IsPGroup 2 (Subgroup.zpowers (autP r α)) := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨e, Subtype.ext ?_⟩
    change (autP r α ^ n) ^ 2 ^ e = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have hbot := CFSG.SignalizerFunctor.Helpers.frattini_automorphism_kernel_coprime_subgroup_trivial
    r 2 (Fact.out) Nat.prime_two hr2 CFSG.pCore_isPGroup (Subgroup.zpowers (autP r α))
    ((Subgroup.zpowers_le).mpr hk) h2
  have h1 : autP r α = 1 := by
    have h3 : autP r α ∈ Subgroup.zpowers (autP r α) := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at h3
    exact h3
  intro d hd
  have h3 := congrArg (fun f : MulAut ↥(CFSG.pCore r X) => ((f ⟨d, hd⟩ : ↥(CFSG.pCore r X)) : X))
    h1
  simpa [autP_coe] using h3

end Lin

end CFSG.Quasithin.Vol2.Ch11.O6

module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fixed

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def FixedClauses (p : ℕ) {X : Type*} [Group X] (C : Subgroup X) : Prop :=
  (∀ T : Subgroup X, T ≠ ⊥ → Group.IsSolvable T → ¬ C ≤ Subgroup.normalizer (T : Set X)) ∧
  (IsSimpleGroup (signalizerGeneralizedFitting C) ∧
    ∃ a b : signalizerGeneralizedFitting C, a * b ≠ b * a) ∧
  (∀ g : MulAut X, Nat.Coprime p (orderOf g) → (∀ x ∈ C, g x = x) → g = 1)

theorem FixedClauses.of_congr {p : ℕ} {X : Type*} [Group X] (g : X ≃* X) (f : MulAut X)
    (h : FixedClauses p (signalizerFixedSubgroup (MulAut.congr g.symm f))) :
    FixedClauses p (signalizerFixedSubgroup f) :=
  ⟨TransportA.not_le_normalizer_of_congr g f h.1, TransportA.fitting_clause_of_congr g f h.2.1,
    TransportA.eq_one_of_congr g f h.2.2⟩

theorem sylow_conj {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P P₀ : Sylow p G) :
    ∃ h : G, ∀ x : G, x ∈ (P : Subgroup G) ↔ h⁻¹ * x * h ∈ (P₀ : Subgroup G) := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P
  refine ⟨h, fun x => ?_⟩
  rw [← hh]
  simp only [Sylow.smul_def]
  change x ∈ (MulAut.conj h • (P₀ : Subgroup G)) ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem orderOf_conj_eq {G : Type*} [Group G] (a b : G) : orderOf (a * b * a⁻¹) = orderOf b :=
  (MulAut.conj a).orderOf_eq b

theorem mem_zpowers_of_orderOf_eq_prime {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    [IsCyclic G] {a b : G} (ha : orderOf a = p) (hb : orderOf b = p) :
    b ∈ Subgroup.zpowers a := by
  classical
  have := Fintype.ofFinite G
  have hbl : (Finset.univ.filter (fun x : G => x ^ p = 1)).card ≤ p :=
    IsCyclic.card_pow_eq_one_le hp.pos
  have hsub : (Finset.univ.filter (· ∈ Subgroup.zpowers a)) ⊆
      (Finset.univ.filter (fun x : G => x ^ p = 1)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Finset.univ.filter (· ∈ Subgroup.zpowers a)).card = p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_zpowers, ha]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hbl)
  have hbmem : b ∈ (Finset.univ.filter (fun x : G => x ^ p = 1)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hb]; exact pow_orderOf_eq_one b
  rw [← heq] at hbmem
  simpa using hbmem

theorem mem_fixedSubgroup_iff_forall_mem_zpowers {X : Type*} [Group X] (f : MulAut X) (x : X) :
    x ∈ signalizerFixedSubgroup f ↔ ∀ a ∈ Subgroup.zpowers f, a x = x := by
  constructor
  · intro hx a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    clear ha
    have hfx : f x = x := hx
    have hf : (f⁻¹ : MulAut X) x = x := by
      change f.symm x = x
      rw [MulEquiv.symm_apply_eq]; exact hfx.symm
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hfx, ih]
    | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, hf, ih]
  · intro h
    exact h f (Subgroup.mem_zpowers f)

theorem signalizerFixedSubgroup_eq_of_zpowers_eq {X : Type*} [Group X] {f f' : MulAut X}
    (h : Subgroup.zpowers f = Subgroup.zpowers f') :
    signalizerFixedSubgroup f = signalizerFixedSubgroup f' := by
  ext x
  rw [mem_fixedSubgroup_iff_forall_mem_zpowers, mem_fixedSubgroup_iff_forall_mem_zpowers, h]

theorem exists_conj_fixed_eq {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hcyc : PSubgroupsCyclic p X) {f f₀ : MulAut X} (hf : orderOf f = p) (hf₀ : orderOf f₀ = p) :
    ∃ g : X ≃* X, signalizerFixedSubgroup (MulAut.congr g.symm f) = signalizerFixedSubgroup f₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hPf : IsPGroup p (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf, pow_one])
  have hPf₀ : IsPGroup p (Subgroup.zpowers f₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hf₀, pow_one])
  obtain ⟨Q, hQ⟩ := hPf.exists_le_sylow
  obtain ⟨Q₀, hQ₀⟩ := hPf₀.exists_le_sylow
  obtain ⟨h, hh⟩ := sylow_conj p Q Q₀
  have hmem : h⁻¹ * f * h ∈ (Q₀ : Subgroup (MulAut X)) :=
    (hh f).mp (hQ (Subgroup.mem_zpowers f))
  have hf₀mem : f₀ ∈ (Q₀ : Subgroup (MulAut X)) := hQ₀ (Subgroup.mem_zpowers f₀)
  have : IsCyclic (Q₀ : Subgroup (MulAut X)) := hcyc _ Q₀.isPGroup'
  have hconj : orderOf (h⁻¹ * f * h) = p := by
    have := orderOf_conj_eq h⁻¹ f
    rwa [inv_inv, hf] at this
  have hord1 : orderOf (⟨h⁻¹ * f * h, hmem⟩ : (Q₀ : Subgroup (MulAut X))) = p := by
    rw [Subgroup.orderOf_mk, hconj]
  have hord2 : orderOf (⟨f₀, hf₀mem⟩ : (Q₀ : Subgroup (MulAut X))) = p := by
    rw [Subgroup.orderOf_mk, hf₀]
  have hbmem := mem_zpowers_of_orderOf_eq_prime p hp hord2 hord1
  have hmem' : h⁻¹ * f * h ∈ Subgroup.zpowers f₀ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, congrArg Subtype.val hk⟩
  have hle : Subgroup.zpowers (h⁻¹ * f * h) ≤ Subgroup.zpowers f₀ := by
    rw [Subgroup.zpowers_le]; exact hmem'
  have heq : Subgroup.zpowers (h⁻¹ * f * h) = Subgroup.zpowers f₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hf₀, hconj]
  refine ⟨h, ?_⟩
  have hcongr : MulAut.congr h.symm f = h⁻¹ * f * h := by
    ext x; rfl
  rw [hcongr]
  exact signalizerFixedSubgroup_eq_of_zpowers_eq heq

theorem hypothesisA_of_fixedClauses {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hcop : Nat.Coprime p (Nat.card X)) (hcyc : PSubgroupsCyclic p X)
    (hfield : (∃ f : MulAut X, orderOf f = p) →
      ∃ f₀ : MulAut X, orderOf f₀ = p ∧ FixedClauses p (signalizerFixedSubgroup f₀)) :
    signalizerMcBrideHypothesisA p X := by
  refine ⟨hp, hsimple, hnonab, hcop, hcyc, Or.inr fun f hf => ?_⟩
  obtain ⟨f₀, hf₀, hcl⟩ := hfield ⟨f, hf⟩
  obtain ⟨g, hg⟩ := exists_conj_fixed_eq hp hcyc hf hf₀
  have h1 : FixedClauses p (signalizerFixedSubgroup (MulAut.congr g.symm f)) := by
    rw [hg]; exact hcl
  exact FixedClauses.of_congr g f h1

end CFSG.SignalizerFunctorTheorem.CatalogBridge

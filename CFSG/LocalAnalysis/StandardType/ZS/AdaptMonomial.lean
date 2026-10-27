module

public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.Quasithin.Background.SimsG4OrthUPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

open scoped BigOperators

private lemma span_singleton_eq_iff_of_basis {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {n : ℕ} (b : Module.Basis (Fin n) F V) {i j : Fin n} :
    Submodule.span F {b i} = Submodule.span F {b j} ↔ i = j := by
  constructor
  · intro h
    by_contra hne
    have hmem : b j ∈ Submodule.span F {b i} := by
      rw [h]
      exact Submodule.mem_span_singleton_self (b j)
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hcoord := congrArg (fun v => b.repr v j) hc
    simp [map_smul, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hne)] at hcoord
  · rintro rfl
    rfl

private lemma lineStabilizer_inv_mem {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {n : ℕ} (b : Module.Basis (Fin n) F V) (U : Fin n → Submodule F V)
    (hU : ∀ i, U i = Submodule.span F {b i}) (a : V ≃ₗ[F] V)
    (ha : ∀ i, ∃ j, (U i).map (a : V →ₗ[F] V) = U j) :
    ∀ i, ∃ j, (U i).map ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = U j := by
  intro i
  choose σ hσ using ha
  have hσinj : Function.Injective σ := by
    intro i i' hii
    have hUi : Submodule.span F {b i} = Submodule.span F {b i'} := by
      have h1 : ((Submodule.span F {b i}).map (a : V →ₗ[F] V)).map
          ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = Submodule.span F {b i} := by
        rw [← Submodule.map_comp]
        change (Submodule.span F {b i}).map ((a⁻¹ * a : V ≃ₗ[F] V) : V →ₗ[F] V) =
          Submodule.span F {b i}
        rw [inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
      have h2 : ((Submodule.span F {b i'}).map (a : V →ₗ[F] V)).map
          ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) = Submodule.span F {b i'} := by
        rw [← Submodule.map_comp]
        change (Submodule.span F {b i'}).map ((a⁻¹ * a : V ≃ₗ[F] V) : V →ₗ[F] V) =
          Submodule.span F {b i'}
        rw [inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
      calc Submodule.span F {b i} = ((Submodule.span F {b i}).map (a : V →ₗ[F] V)).map
            ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := h1.symm
        _ = ((Submodule.span F {b i'}).map (a : V →ₗ[F] V)).map
            ((a⁻¹ : V ≃ₗ[F] V) : V →ₗ[F] V) := by
          rw [← hU i, ← hU i', hσ i, hσ i', hii]
        _ = Submodule.span F {b i'} := h2
    exact (span_singleton_eq_iff_of_basis b).mp hUi
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  obtain ⟨k, hk⟩ := hσsurj i
  refine ⟨k, ?_⟩
  rw [← hk, ← hσ k, ← Submodule.map_comp, hU k]
  change (Submodule.span F {b k}).map ((a⁻¹ * a : V ≃ₗ[F] V) : V →ₗ[F] V) =
    Submodule.span F {b k}
  rw [inv_mul_cancel, LinearEquiv.coe_toLinearMap_one, Submodule.map_id]

private def lineStabilizer {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    {n : ℕ} (b : Module.Basis (Fin n) F V) (U : Fin n → Submodule F V)
    (hU : ∀ i, U i = Submodule.span F {b i}) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ i, ∃ j, (U i).map (g : V →ₗ[F] V) = U j}
  one_mem' := by
    intro i
    refine ⟨i, ?_⟩
    rw [LinearEquiv.coe_toLinearMap_one, Submodule.map_id]
  mul_mem' := by
    intro a b' ha hb i
    obtain ⟨j, hj⟩ := hb i
    obtain ⟨k, hk⟩ := ha j
    refine ⟨k, ?_⟩
    change Submodule.map ((a : V →ₗ[F] V).comp (b' : V →ₗ[F] V)) (U i) = U k
    rw [Submodule.map_comp, hj, hk]
  inv_mem' := by
    intro a ha
    exact lineStabilizer_inv_mem b U hU a ha

theorem isImprimitiveOnV_closure_of_monomial {F : Type} [Field F] {V : Type} [AddCommGroup V]
    [Module F V] {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) F V) {S : Set (V ≃ₗ[F] V)}
    (hS : ∀ g ∈ S, ∀ i, ∃ j, ∃ c : F, g (b i) = c • b j) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV (Subgroup.closure S) := by
  classical
  let U : Fin n → Submodule F V := fun i => Submodule.span F {b i}
  have hn1 : 1 < Nat.card (Fin n) := by
    rw [Nat.card_fin]
    omega
  have hU0 : ∀ i, U i ≠ ⊥ := by
    intro i h
    dsimp only [U] at h
    rw [Submodule.span_singleton_eq_bot] at h
    exact b.ne_zero i h
  have hind : iSupIndep U := by
    dsimp only [U]
    simpa using b.linearIndependent.iSupIndep_span_singleton
  have hsup : (⨆ i, U i) = ⊤ := by
    dsimp only [U]
    rw [Submodule.iSup_span, Set.iUnion_singleton_eq_range, b.span_eq]
  have hmemS : S ⊆ {g : V ≃ₗ[F] V | ∀ i, ∃ j, (U i).map (g : V →ₗ[F] V) = U j} := by
    intro g hg i
    obtain ⟨j, c, hc⟩ := hS g hg i
    have hc0 : c ≠ 0 := by
      intro hc0
      have hzero : g (b i) = 0 := by rw [hc, hc0, zero_smul]
      have hbi : b i = 0 := g.injective (by simpa using hzero)
      exact b.ne_zero i hbi
    refine ⟨j, ?_⟩
    rw [Submodule.map_span, Set.image_singleton]
    change Submodule.span F {g (b i)} = Submodule.span F {b j}
    rw [hc, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) (b j)]
  have hline : ∀ g ∈ Subgroup.closure S, ∀ i, ∃ j, (U i).map (g : V →ₗ[F] V) = U j := by
    intro g hg
    exact (Subgroup.closure_le (lineStabilizer b U (fun i => rfl))).mpr hmemS hg
  exact CFSG.Quasithin.SimsG4.isImprimitiveOnV_of_family hn1 U hU0 hind hsup hline

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma two_ne_zero_of_prime_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have h2p : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd
  exact hp h2p

private def epsB (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U) : Fin ℓ → U :=
  fun k => Finset.sum (Finset.univ.filter (fun j : Fin ℓ => k ≤ j ∧ j.val < ℓ - 1))
      (fun j => u j) + (2 : ZMod p)⁻¹ • u ⟨ℓ - 1, hℓ⟩

private lemma sum_filter_split {ℓ : ℕ} (i : Fin ℓ) (hi : i.val < ℓ - 1) (f : Fin ℓ → U) :
    Finset.sum (Finset.univ.filter (fun j : Fin ℓ => i ≤ j ∧ j.val < ℓ - 1)) f =
      f i + Finset.sum (Finset.univ.filter
        (fun j : Fin ℓ => (⟨i.val + 1, by omega⟩ : Fin ℓ) ≤ j ∧ j.val < ℓ - 1)) f := by
  have hset : Finset.univ.filter (fun j : Fin ℓ => i ≤ j ∧ j.val < ℓ - 1) =
      insert i (Finset.univ.filter
        (fun j : Fin ℓ => (⟨i.val + 1, by omega⟩ : Fin ℓ) ≤ j ∧ j.val < ℓ - 1)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, true_and]
    constructor
    · rintro ⟨hij, hjn⟩
      by_cases h : j = i
      · left; exact h
      · right
        refine ⟨?_, hjn⟩
        have hle : i.val ≤ j.val := Fin.le_def.mp hij
        have hne : i.val ≠ j.val := by
          intro hval
          exact h (Fin.ext hval.symm)
        exact Fin.le_def.mpr (by omega : i.val + 1 ≤ j.val)
    · rintro (rfl | ⟨hij, hjn⟩)
      · exact ⟨le_rfl, by omega⟩
      · have hle : i.val ≤ j.val := by
          have hle' : i.val + 1 ≤ j.val := Fin.le_def.mp hij
          omega
        exact ⟨Fin.le_def.mpr hle, hjn⟩
  rw [hset, Finset.sum_insert]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    have hle : i.val + 1 ≤ i.val := Fin.le_def.mp h.1
    omega

private lemma u_eq_epsB_sub {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U)
    (i : Fin ℓ) (hi : i.val < ℓ - 1) :
    u i = epsB p hℓ u i - epsB p hℓ u ⟨i.val + 1, by omega⟩ := by
  simp only [epsB]
  rw [sum_filter_split i hi u]
  abel

private lemma epsB_last {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U) :
    epsB p hℓ u ⟨ℓ - 1, hℓ⟩ = (2 : ZMod p)⁻¹ • u ⟨ℓ - 1, hℓ⟩ := by
  simp only [epsB]
  have hempty : Finset.univ.filter
      (fun j : Fin ℓ => (⟨ℓ - 1, hℓ⟩ : Fin ℓ) ≤ j ∧ j.val < ℓ - 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have h1 : (ℓ - 1) ≤ j.val := hj.1
    have h2 : j.val < ℓ - 1 := hj.2
    omega
  rw [hempty, Finset.sum_empty, zero_add]

private lemma u_last_eq {ℓ : ℕ} (hp : p ≠ 2) (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U) :
    u ⟨ℓ - 1, hℓ⟩ = (2 : ZMod p) • epsB p hℓ u ⟨ℓ - 1, hℓ⟩ := by
  rw [epsB_last hℓ u]
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_prime_ne_two hp
  rw [smul_smul, mul_inv_cancel₀ h2, one_smul]

theorem isImprimitiveOnV_gmmn {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U)
    (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV (gmmn p b i₀ i₁ ζ) := by
  dsimp only [gmmn]
  apply isImprimitiveOnV_closure_of_monomial hn b
  intro g hg i
  rcases hg with hg | hg
  · rcases hg with ⟨σ, rfl⟩
    exact ⟨σ i, 1, by simp [permMap_apply_basis]⟩
  · rcases hg with rfl
    exact ⟨i, (pairUnit p i₀ i₁ ζ i : ZMod p), by simp [diagMap_apply_basis]⟩

theorem isImprimitiveOnV_g2mmn {n : ℕ} (hn : 2 ≤ n) (b : Module.Basis (Fin n) (ZMod p) U)
    (i₀ i₁ : Fin n) (ζ : (ZMod p)ˣ) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV (g2mmn p b i₀ i₁ ζ) := by
  dsimp only [g2mmn]
  apply isImprimitiveOnV_closure_of_monomial hn b
  intro g hg i
  rcases hg with hg | hg
  · rcases hg with ⟨σ, rfl⟩
    exact ⟨σ i, 1, by simp [permMap_apply_basis]⟩
  · rcases hg with hg | hg
    · rcases hg with rfl
      refine ⟨i, ((if i = i₀ then (-1 : (ZMod p)ˣ) else 1) : ZMod p), ?_⟩
      rw [diagMap_apply_basis]
      split_ifs <;> simp
    · rcases hg with rfl
      exact ⟨i, (pairUnit p i₀ i₁ ζ i : ZMod p), by simp [diagMap_apply_basis]⟩

private lemma zmod_two_smul (x : U) : (2 : ZMod p) • x = x + x := by
  rw [show (2 : ZMod p) = 1 + 1 by norm_num, add_smul, one_smul]

private lemma zmod_neg_one_smul (x : U) : (-1 : ZMod p) • x = -x := by
  exact neg_one_smul (ZMod p) x

private lemma zmod_two_add_neg_one : (2 : ZMod p) + -1 = 1 := by
  rw [show (2 : ZMod p) = 1 + 1 by norm_num]
  abel

private lemma phi_epsB_last (hp : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.B ℓ i j : ZMod p)) (i : Fin ℓ) :
    φ i (epsB p hℓ u ⟨ℓ - 1, hℓ⟩) =
      (if i = ⟨ℓ - 1, hℓ⟩ then 1 else if i.val + 1 = ℓ - 1 then -1 else 0) := by
  rw [epsB_last hℓ u, map_smul, hK]
  by_cases hi_last : i = ⟨ℓ - 1, hℓ⟩
  · rw [hi_last] at *
    simp [CartanMatrix.B, Matrix.of_apply, smul_eq_mul,
      inv_mul_cancel₀ (two_ne_zero_of_prime_ne_two hp)]
  · by_cases hi_pen : i.val + 1 = ℓ - 1
    · have hi_eq : i = ⟨ℓ - 2, by omega⟩ := by ext; simp only; omega
      rw [hi_eq] at *
      have hk1 : ¬ (⟨ℓ - 2, by omega⟩ : Fin ℓ) = ⟨ℓ - 1, hℓ⟩ := by omega
      have hk2 : (⟨ℓ - 2, by omega⟩ : Fin ℓ).val + 1 = (⟨ℓ - 1, hℓ⟩ : Fin ℓ).val := by omega
      have hk3 : (⟨ℓ - 1, hℓ⟩ : Fin ℓ).val = ℓ - 1 := by simp
      have hk4 : ¬ (⟨ℓ - 2, by omega⟩ : Fin ℓ).val = ℓ - 1 := by omega
      have hk5 : (⟨ℓ - 2, by omega⟩ : Fin ℓ).val + 1 = ℓ - 1 := by omega
      simp [CartanMatrix.B, Matrix.of_apply, hk1, hk2]
      rw [show (2 : ZMod p)⁻¹ * 2 = 1 by exact inv_mul_cancel₀ (two_ne_zero_of_prime_ne_two hp)]
    · simp [CartanMatrix.B, Matrix.of_apply, hi_last, hi_pen, smul_eq_mul,
        show ℓ - 1 + 1 ≠ i.val by omega]

private lemma phi_epsB_step {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.B ℓ i j : ZMod p)) (i k : Fin ℓ)
    (hklt : k.val < ℓ - 1) :
    φ i (epsB p hℓ u k) =
      (CartanMatrix.B ℓ i k : ZMod p) +
        φ i (epsB p hℓ u ⟨k.val + 1, by omega⟩) := by
  have h : epsB p hℓ u k = u k + epsB p hℓ u ⟨k.val + 1, by omega⟩ := by
    have h' := u_eq_epsB_sub (p := p) hℓ u k hklt
    rw [h']
    abel
  rw [h, map_add, hK]

private lemma phi_epsB_local {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (i k : Fin ℓ)
    (hklt : k.val < ℓ - 1) :
    (CartanMatrix.B ℓ i k : ZMod p) +
        (if i = ⟨k.val + 1, by omega⟩ then 1 else
          if i.val + 1 = k.val + 1 then -1 else 0) =
      (if i = k then 1 else if i.val + 1 = k.val then -1 else 0) := by
  by_cases h1 : i = k
  · rw [h1]
    simp [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    exact zmod_two_add_neg_one
  · by_cases h2 : i.val + 1 = k.val
    · have hk1 : ¬ i = ⟨k.val + 1, by omega⟩ := by
        intro h
        have h' : i.val = k.val + 1 := by simp [h]
        rw [h'] at h2
        omega
      have hk2 : ¬ i.val + 1 = k.val + 1 := by omega
      have hk3 : k.val ≠ ℓ - 1 := by omega
      have hik : i.val ≠ k.val := by omega
      simp [h1, h2, hk1, hk3, hik, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    · by_cases h3 : i = ⟨k.val + 1, by omega⟩
      · have h3' : i.val = k.val + 1 := by simp [h3]
        have hk2 : ¬ i.val + 1 = k.val + 1 := by omega
        have hk3 : k.val ≠ ℓ - 1 := by omega
        have hik : i.val ≠ k.val := by omega
        have hk4 : k.val + 1 + 1 ≠ k.val := by omega
        simp [h3, hk4, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
      · by_cases h4 : i.val + 1 = k.val + 1
        · exfalso
          exact h1 (Fin.ext (by omega))
        · have hk3 : k.val ≠ ℓ - 1 := by omega
          have hik : i.val ≠ k.val := by omega
          have hk1 : ¬ i = ⟨k.val + 1, by omega⟩ := h3
          have hk1' : k.val + 1 ≠ i.val := by
            intro h
            exact h3 (Fin.ext h.symm)
          simp [h1, h2, h3, hk1', hik, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]

private lemma phi_epsB (hp : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.B ℓ i j : ZMod p)) (i : Fin ℓ) :
    ∀ k : Fin ℓ, φ i (epsB p hℓ u k) =
      (if i = k then 1 else if i.val + 1 = k.val then -1 else 0) := by
  have hmain : ∀ m, ∀ (k : Fin ℓ), ℓ - 1 - k.val = m →
      φ i (epsB p hℓ u k) =
        (if i = k then 1 else if i.val + 1 = k.val then -1 else 0) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro k hk
      by_cases hklast : k.val = ℓ - 1
      · have hk_eq : k = ⟨ℓ - 1, hℓ⟩ := by ext; simp only; omega
        rw [hk_eq] at *
        rw [phi_epsB_last hp hℓ u φ hK i]
      · have hklt : k.val < ℓ - 1 := by omega
        rw [phi_epsB_step hℓ u φ hK i k hklt]
        have hih := ih (ℓ - 1 - (⟨k.val + 1, by omega⟩ : Fin ℓ).val) (by simp; omega)
          (⟨k.val + 1, by omega⟩ : Fin ℓ) rfl
        rw [hih]
        exact phi_epsB_local hℓ i k hklt
  intro k
  exact hmain (ℓ - 1 - k.val) k rfl

private lemma monomial_epsB (hp : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) {u : Fin ℓ → U}
    {φ : Fin ℓ → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.B ℓ i j : ZMod p)) :
    ∀ i k, ∃ j, ∃ c : ZMod p,
      Module.reflection (hφ i) (epsB p hℓ u k) = c • epsB p hℓ u j := by
  intro i k
  have hC : φ i (epsB p hℓ u k) =
      (if i = k then 1 else if i.val + 1 = k.val then -1 else 0) :=
    phi_epsB hp hℓ u φ hK i k
  rw [Module.reflection_apply, hC]
  by_cases hik : i = k
  · rw [hik] at *
    by_cases hi_last : k = ⟨ℓ - 1, hℓ⟩
    · rw [hi_last] at *
      refine ⟨⟨ℓ - 1, hℓ⟩, -1, ?_⟩
      rw [if_pos rfl, one_smul, u_last_eq (p := p) hp hℓ u]
      rw [zmod_two_smul, zmod_neg_one_smul]
      abel_nf
    · have hklt : k.val < ℓ - 1 := by
        have hne : k.val ≠ ℓ - 1 := by
          intro h; exact hi_last (Fin.ext h)
        omega
      refine ⟨⟨k.val + 1, by omega⟩, 1, ?_⟩
      rw [if_pos rfl, one_smul, u_eq_epsB_sub (p := p) hℓ u k hklt]
      simp only [one_smul]
      abel_nf
  · by_cases hik1 : i.val + 1 = k.val
    · refine ⟨i, 1, ?_⟩
      rw [if_neg hik, if_pos hik1, one_smul]
      have hk_eq : k = ⟨i.val + 1, by omega⟩ := by ext; simp only; omega
      have hilt : i.val < ℓ - 1 := by omega
      rw [hk_eq, u_eq_epsB_sub (p := p) hℓ u i hilt]
      rw [zmod_neg_one_smul]
      abel_nf
    · refine ⟨k, 1, ?_⟩
      rw [if_neg hik, if_neg hik1, one_smul]
      simp

private lemma span_epsB (hp : p ≠ 2) {ℓ : ℕ} (hℓ : ℓ - 1 < ℓ) (u : Fin ℓ → U)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    Submodule.span (ZMod p) (Set.range (epsB p hℓ u)) = ⊤ := by
  rw [← hspan]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp only [epsB]
    exact Submodule.add_mem _ (Submodule.sum_mem _ fun j hj => Submodule.subset_span ⟨j, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ℓ - 1, hℓ⟩, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < ℓ - 1
    · rw [u_eq_epsB_sub (p := p) hℓ u i hi]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
        (Submodule.subset_span ⟨⟨i.val + 1, by omega⟩, rfl⟩)
    · have hi' : i = ⟨ℓ - 1, hℓ⟩ := by
        ext
        simp only
        omega
      subst hi'
      rw [u_last_eq (p := p) hp hℓ u]
      exact Submodule.smul_mem _ (2 : ZMod p) (Submodule.subset_span
        (Set.mem_range_self (f := epsB p hℓ u) ⟨ℓ - 1, hℓ⟩))

theorem exists_monomial_basis_of_cartan_B (hp : p ≠ 2) {ℓ : ℕ} {u : Fin ℓ → U}
    {φ : Fin ℓ → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.B ℓ i j : ZMod p))
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    ∃ b : Module.Basis (Fin ℓ) (ZMod p) U, ∀ i k, ∃ j, ∃ c : ZMod p,
      Module.reflection (hφ i) (b k) = c • b j := by
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have hsub : Subsingleton U := by
      have h : (⊥ : Submodule (ZMod p) U) = ⊤ := by
        simpa using hspan
      refine ⟨fun x y => ?_⟩
      have hx : x ∈ (⊥ : Submodule (ZMod p) U) := by rw [h]; exact Submodule.mem_top
      have hy : y ∈ (⊥ : Submodule (ZMod p) U) := by rw [h]; exact Submodule.mem_top
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]
    have hsub' : Subsingleton U := hsub
    exact ⟨Module.Basis.empty U, by intro i; exact Fin.elim0 i⟩
  · have hℓ : ℓ - 1 < ℓ := by omega
    have hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
      have hB : (Matrix.of fun i j => φ i (u j)) =
          (CartanMatrix.B ℓ).map (fun x => (x : ZMod p)) := by
        ext i j
        simp [hK]
      rw [hB, ← Int.cast_det]
      rw [CartanMatrix.B_det (Nat.pos_of_ne_zero hℓ0)]
      rw [Int.cast_ofNat]
      exact two_ne_zero_of_prime_ne_two hp
    have hinde : LinearIndependent (ZMod p) u := linearIndependent_of_det_ne_zero u φ hdet
    have hfin : Module.finrank (ZMod p) U = ℓ := by
      have h := (linearIndependent_iff_card_eq_finrank_span (R := ZMod p) (b := u)).mp hinde
      rw [Fintype.card_fin, Set.finrank, hspan, finrank_top] at h
      exact h.symm
    have hspan_eps := span_epsB hp hℓ u hspan
    have hind_eps : LinearIndependent (ZMod p) (epsB p hℓ u) := by
      apply linearIndependent_of_top_le_span_of_card_eq_finrank
      · rw [hspan_eps]
      · simp [Fintype.card_fin, hfin]
    let b : Module.Basis (Fin ℓ) (ZMod p) U := Module.Basis.mk hind_eps hspan_eps.ge
    refine ⟨b, ?_⟩
    intro i k
    have hb : ∀ j, b j = epsB p hℓ u j := fun j => by simp [b, Module.Basis.coe_mk]
    obtain ⟨j, c, hc⟩ := monomial_epsB hp hℓ (u := u) (φ := φ) hφ hK i k
    exact ⟨j, c, by rw [hb k, hc, ← hb j]⟩

private lemma cartanD_last_entries {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2) :
    CartanMatrix.D ℓ last last = 2 ∧
    CartanMatrix.D ℓ last sndlast = 0 ∧
    CartanMatrix.D ℓ sndlast last = 0 ∧
    CartanMatrix.D ℓ sndlast sndlast = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [CartanMatrix.D, Matrix.of_apply]
     split_ifs <;> simp only [Fin.ext_iff] at * <;> omega)

private lemma cartanB_last_entries {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2) :
    CartanMatrix.B ℓ last last = 2 ∧
    CartanMatrix.B ℓ last sndlast = -1 ∧
    CartanMatrix.B ℓ sndlast last = -2 ∧
    CartanMatrix.B ℓ sndlast sndlast = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [CartanMatrix.B, Matrix.of_apply]
     split_ifs <;> simp only [Fin.ext_iff] at * <;> omega)

private lemma cartanD_eq_B_of_ne_last {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last : Fin ℓ)
    (hlast : last.val = ℓ - 1) (i j : Fin ℓ) (hi : i ≠ last) (hj : j ≠ last) :
    CartanMatrix.D ℓ i j = CartanMatrix.B ℓ i j := by
  have hi' : i.val ≠ ℓ - 1 := by
    intro h; exact hi (Fin.ext (h.trans hlast.symm))
  have hj' : j.val ≠ ℓ - 1 := by
    intro h; exact hj (Fin.ext (h.trans hlast.symm))
  simp only [CartanMatrix.D, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

private lemma cartanD_col {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (i : Fin ℓ) (hi : i.val ≠ ℓ - 1) :
    CartanMatrix.D ℓ i last - CartanMatrix.D ℓ i sndlast =
      CartanMatrix.B ℓ i last := by
  simp only [CartanMatrix.D, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

private lemma cartanD_row_int {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (j : Fin ℓ) (hj : j ≠ last) :
    CartanMatrix.D ℓ last j - CartanMatrix.D ℓ sndlast j =
      if j = sndlast then -2 else 0 := by
  have hj' : j.val ≠ ℓ - 1 := by
    intro h; exact hj (Fin.ext (h.trans hlast.symm))
  simp only [CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

private lemma cartanB_row_int {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (j : Fin ℓ) (hj : j ≠ last) :
    CartanMatrix.B ℓ last j = if j = sndlast then -1 else 0 := by
  have hj' : j.val ≠ ℓ - 1 := by
    intro h; exact hj (Fin.ext (h.trans hlast.symm))
  simp only [CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> simp only [Fin.ext_iff] at * <;> omega

private lemma zmod_inv_two_smul_neg_two (hp : p ≠ 2) :
    (2 : ZMod p)⁻¹ • (-(2 : ZMod p)) = (-1 : ZMod p) := by
  rw [smul_neg, smul_eq_mul, inv_mul_cancel₀ (two_ne_zero_of_prime_ne_two hp)]


private def cartanDW {ℓ : ℕ} (u : Fin ℓ → U) (last sndlast : Fin ℓ) : Fin ℓ → U :=
  Function.update u last (u last - u sndlast)

private def cartanDPhi {ℓ : ℕ} (φ : Fin ℓ → Module.Dual (ZMod p) U) (last sndlast : Fin ℓ) :
    Fin ℓ → Module.Dual (ZMod p) U :=
  Function.update φ last ((2 : ZMod p)⁻¹ • (φ last - φ sndlast))

private lemma cartanDW_apply_of_ne {ℓ : ℕ} (u : Fin ℓ → U) {last sndlast j : Fin ℓ}
    (hj : j ≠ last) : cartanDW u last sndlast j = u j := by
  simp only [cartanDW, Function.update_of_ne hj]

private lemma cartanDW_apply_last {ℓ : ℕ} (u : Fin ℓ → U) (last sndlast : Fin ℓ) :
    cartanDW u last sndlast last = u last - u sndlast := by
  simp only [cartanDW, Function.update_self]

private lemma cartanDPhi_apply_of_ne {ℓ : ℕ} (φ : Fin ℓ → Module.Dual (ZMod p) U)
    {last sndlast i : Fin ℓ} (hi : i ≠ last) : cartanDPhi φ last sndlast i = φ i := by
  simp only [cartanDPhi, Function.update_of_ne hi]

private lemma cartanDPhi_apply_last {ℓ : ℕ} (φ : Fin ℓ → Module.Dual (ZMod p) U)
    (last sndlast : Fin ℓ) :
    cartanDPhi φ last sndlast last = (2 : ZMod p)⁻¹ • (φ last - φ sndlast) := by
  simp only [cartanDPhi, Function.update_self]

private lemma span_cartanDW {ℓ : ℕ} (u : Fin ℓ → U) (last sndlast : Fin ℓ)
    (hsne : sndlast ≠ last) (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    Submodule.span (ZMod p) (Set.range (cartanDW u last sndlast)) = ⊤ := by
  rw [← hspan]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = last
    · rw [hj]
      rw [cartanDW_apply_last]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨last, rfl⟩)
        (Submodule.subset_span ⟨sndlast, rfl⟩)
    · rw [cartanDW_apply_of_ne u hj]
      exact Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = last
    · rw [hj]
      have hul : u last = cartanDW u last sndlast last + cartanDW u last sndlast sndlast := by
        rw [cartanDW_apply_last, cartanDW_apply_of_ne u hsne]
        abel
      rw [hul]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨last, rfl⟩)
        (Submodule.subset_span ⟨sndlast, rfl⟩)
    · refine Submodule.subset_span ⟨j, ?_⟩
      exact cartanDW_apply_of_ne u hj

private lemma cartanD_phi_w_last {ℓ : ℕ} (hp : p ≠ 2) (hℓ : 4 ≤ ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.D ℓ i j : ZMod p)) :
    ∀ j, cartanDPhi φ last sndlast last (cartanDW u last sndlast j) =
      (CartanMatrix.B ℓ last j : ZMod p) := by
  intro j
  by_cases hj : j = last
  · rw [hj]
    rw [cartanDPhi_apply_last, cartanDW_apply_last, LinearMap.smul_apply, LinearMap.sub_apply]
    simp only [map_sub]
    rw [hK last last, hK last sndlast, hK sndlast last, hK sndlast sndlast]
    obtain ⟨d11, d12, d21, d22⟩ := cartanD_last_entries hℓ last sndlast hlast hsndlast
    rw [d11, d12, d21, d22]
    obtain ⟨b11, b12, b21, b22⟩ := cartanB_last_entries hℓ last sndlast hlast hsndlast
    rw [b11]
    push_cast
    rw [show (2 : ZMod p) - 0 - (0 - 2) = 4 by norm_num]
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (two_ne_zero_of_prime_ne_two hp), one_mul]
  · rw [cartanDPhi_apply_last, cartanDW_apply_of_ne u hj, LinearMap.smul_apply,
      LinearMap.sub_apply]
    rw [hK last j, hK sndlast j, ← Int.cast_sub]
    rw [cartanD_row_int hℓ last sndlast hlast hsndlast j hj]
    rw [cartanB_row_int hℓ last sndlast hlast hsndlast j hj]
    by_cases hjs : j = sndlast
    · rw [if_pos hjs, if_pos hjs]
      push_cast
      exact zmod_inv_two_smul_neg_two hp
    · rw [if_neg hjs, if_neg hjs]
      push_cast
      rw [smul_zero]

private lemma cartanD_phi_w_other {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.D ℓ i j : ZMod p)) :
    ∀ i, i ≠ last → ∀ j, cartanDPhi φ last sndlast i (cartanDW u last sndlast j) =
      (CartanMatrix.B ℓ i j : ZMod p) := by
  intro i hi j
  by_cases hj : j = last
  · rw [hj]
    rw [cartanDPhi_apply_of_ne φ hi, cartanDW_apply_last]
    simp only [map_sub]
    rw [hK i last, hK i sndlast, ← Int.cast_sub]
    rw [cartanD_col hℓ last sndlast hlast hsndlast i (by
      intro h; exact hi (Fin.ext (h.trans hlast.symm)))]
  · rw [cartanDPhi_apply_of_ne φ hi, cartanDW_apply_of_ne u hj, hK i j]
    rw [cartanD_eq_B_of_ne_last hℓ last hlast i j hi hj]

private lemma cartanD_phi_w {ℓ : ℕ} (hp : p ≠ 2) (hℓ : 4 ≤ ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U) (last sndlast : Fin ℓ)
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.D ℓ i j : ZMod p)) :
    ∀ i j, cartanDPhi φ last sndlast i (cartanDW u last sndlast j) =
      (CartanMatrix.B ℓ i j : ZMod p) := by
  intro i j
  by_cases hi : i = last
  · rw [hi]
    exact cartanD_phi_w_last hp hℓ u φ last sndlast hlast hsndlast hK j
  · exact cartanD_phi_w_other hℓ u φ last sndlast hlast hsndlast hK i hi j

private lemma cartanD_reflection_last {ℓ : ℕ} (hp : p ≠ 2) (hℓ : 4 ≤ ℓ) (u : Fin ℓ → U)
    (φ : Fin ℓ → Module.Dual (ZMod p) U) (w : Fin ℓ → U)
    (φ' : Fin ℓ → Module.Dual (ZMod p) U) (last sndlast : Fin ℓ) (hsne : sndlast ≠ last)
    (hφ : ∀ i, φ i (u i) = 2) (hφ' : ∀ i, φ' i (w i) = 2)
    (hK' : ∀ i j, φ' i (w j) = (CartanMatrix.B ℓ i j : ZMod p))
    (hlast : last.val = ℓ - 1) (hsndlast : sndlast.val = ℓ - 2)
    (hw_last : w last = u last - u sndlast) (hw_ne : ∀ j, j ≠ last → w j = u j)
    (hφ'_ne : ∀ i, i ≠ last → φ' i = φ i)
    (hφ'_last : φ' last = (2 : ZMod p)⁻¹ • (φ last - φ sndlast)) :
    Module.reflection (hφ' last) * Module.reflection (hφ' sndlast) * Module.reflection (hφ' last)
      = Module.reflection (hφ last) := by
  have hws : w sndlast = u sndlast := hw_ne sndlast hsne
  have hval_ls : φ' last (w sndlast) = -1 := by
    rw [hK' last sndlast, (cartanB_last_entries hℓ last sndlast hlast hsndlast).2.1]
    norm_num
  have hval_sl : φ' sndlast (w last) = -2 := by
    rw [hK' sndlast last, (cartanB_last_entries hℓ last sndlast hlast hsndlast).2.2.1]
    norm_num
  have hfl : φ' sndlast + (2 : ZMod p) • φ' last = φ last := by
    ext z
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [hφ'_ne sndlast hsne, hφ'_last, LinearMap.smul_apply, LinearMap.sub_apply]
    rw [smul_smul]
    rw [show (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 by
      rw [mul_inv_cancel₀ (two_ne_zero_of_prime_ne_two hp)]]
    rw [one_smul]
    abel
  have h1 : Module.preReflection (w last) (φ' last) (w sndlast) = u last := by
    rw [Module.preReflection_apply, hval_ls, hws, hw_last, zmod_neg_one_smul]
    abel
  have h2 : Module.preReflection (φ' last) (Module.Dual.eval (ZMod p) U (w last))
      (φ' sndlast) = φ last := by
    ext z
    rw [Module.preReflection_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.Dual.eval_apply]
    rw [hval_sl, show (-2 : ZMod p) = -(2) by norm_num, neg_smul, sub_neg_eq_add]
    exact congrArg (fun f : Module.Dual (ZMod p) U => f z) hfl
  have hpre := Module.preReflection_preReflection (y := w sndlast) (g := φ' sndlast)
    (h := hφ' last)
  rw [h1, h2] at hpre
  apply LinearEquiv.ext
  intro z
  have hz := congrArg (fun (f : U →ₗ[ZMod p] U) => f z) hpre
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.mul_apply,
    Module.reflection_apply, Module.preReflection_apply, LinearMap.sub_apply] using hz.symm

private lemma monomial_cartanD_of_B (hp : p ≠ 2) {ℓ : ℕ} {u : Fin ℓ → U}
    {φ : Fin ℓ → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2) {w : Fin ℓ → U}
    {φ' : Fin ℓ → Module.Dual (ZMod p) U} {last sndlast : Fin ℓ}
    (hφ' : ∀ i, φ' i (w i) = 2)
    (hK' : ∀ i j, φ' i (w j) = (CartanMatrix.B ℓ i j : ZMod p))
    (hspan_w : Submodule.span (ZMod p) (Set.range w) = ⊤)
    (hconj : Module.reflection (hφ' last) * Module.reflection (hφ' sndlast) *
      Module.reflection (hφ' last) = Module.reflection (hφ last))
    (hw_ne : ∀ j, j ≠ last → w j = u j) (hφ'_ne : ∀ i, i ≠ last → φ' i = φ i) :
    ∃ b : Module.Basis (Fin ℓ) (ZMod p) U, ∀ i k, ∃ j, ∃ c : ZMod p,
      Module.reflection (hφ i) (b k) = c • b j := by
  obtain ⟨b, hb⟩ := exists_monomial_basis_of_cartan_B hp (u := w) (φ := φ') hφ' hK' hspan_w
  refine ⟨b, ?_⟩
  intro i k
  by_cases hi : i = last
  · rw [hi]
    rw [← hconj, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    obtain ⟨j1, c1, hc1⟩ := hb last k
    obtain ⟨j2, c2, hc2⟩ := hb sndlast j1
    obtain ⟨j3, c3, hc3⟩ := hb last j2
    refine ⟨j3, c1 * c2 * c3, ?_⟩
    rw [hc1]
    simp only [map_smul]
    rw [hc2]
    simp only [map_smul]
    rw [hc3]
    simp only [smul_smul]
    rw [mul_assoc]
  · have hrefl : Module.reflection (hφ i) = Module.reflection (hφ' i) := by
      apply LinearEquiv.ext
      intro z
      rw [Module.reflection_apply, Module.reflection_apply, hw_ne i hi, hφ'_ne i hi]
    obtain ⟨j, c, hc⟩ := hb i k
    exact ⟨j, c, by rw [hrefl, hc]⟩

theorem exists_monomial_basis_of_cartan_D (hp : p ≠ 2) {ℓ : ℕ} (hℓ : 4 ≤ ℓ) {u : Fin ℓ → U}
    {φ : Fin ℓ → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.D ℓ i j : ZMod p))
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    ∃ b : Module.Basis (Fin ℓ) (ZMod p) U, ∀ i k, ∃ j, ∃ c : ZMod p,
      Module.reflection (hφ i) (b k) = c • b j := by
  have hℓ' : ℓ - 1 < ℓ := by omega
  let last : Fin ℓ := ⟨ℓ - 1, hℓ'⟩
  let sndlast : Fin ℓ := ⟨ℓ - 2, by omega⟩
  have hlast : last.val = ℓ - 1 := rfl
  have hsndlast : sndlast.val = ℓ - 2 := rfl
  have hsne : sndlast ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    simp only [hlast, hsndlast] at hv
    omega
  have hspan_w := span_cartanDW u last sndlast hsne hspan
  have hK' := cartanD_phi_w hp hℓ u φ last sndlast hlast hsndlast hK
  have hφ' : ∀ i, cartanDPhi φ last sndlast i (cartanDW u last sndlast i) = 2 := by
    intro i
    rw [hK' i i, CartanMatrix.B_diag]
    norm_num
  have hconj := cartanD_reflection_last hp hℓ u φ (cartanDW u last sndlast)
    (cartanDPhi φ last sndlast) last sndlast hsne hφ hφ' hK' hlast hsndlast
    (cartanDW_apply_last u last sndlast) (fun j hj => cartanDW_apply_of_ne u hj)
    (fun i hi => cartanDPhi_apply_of_ne φ hi) (cartanDPhi_apply_last φ last sndlast)
  exact monomial_cartanD_of_B hp hφ hφ' hK' hspan_w hconj
    (fun j hj => cartanDW_apply_of_ne u hj) (fun i hi => cartanDPhi_apply_of_ne φ hi)

theorem isImprimitiveOnV_of_isCartanModel_B (hp : p ≠ 2) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : IsCartanModel p (CartanMatrix.B ℓ) A) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  rcases hA with ⟨u, φ, hφ, hK, hspan, hker, hAeq⟩
  obtain ⟨b, hb⟩ := exists_monomial_basis_of_cartan_B hp (u := u) (φ := φ) hφ hK hspan
  rw [hAeq]
  exact isImprimitiveOnV_closure_of_monomial hℓ b (by
    intro g hg i
    rcases hg with ⟨j, rfl⟩
    exact hb j i)

theorem isImprimitiveOnV_of_isCartanModel_D (hp : p ≠ 2) {ℓ : ℕ} (hℓ : 4 ≤ ℓ)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : IsCartanModel p (CartanMatrix.D ℓ) A) :
    CFSG.Quasithin.SimsG4.IsImprimitiveOnV A := by
  rcases hA with ⟨u, φ, hφ, hK, hspan, hker, hAeq⟩
  obtain ⟨b, hb⟩ := exists_monomial_basis_of_cartan_D hp hℓ (u := u) (φ := φ) hφ hK hspan
  rw [hAeq]
  exact isImprimitiveOnV_closure_of_monomial (by omega : 2 ≤ ℓ) b (by
    intro g hg i
    rcases hg with ⟨j, rfl⟩
    exact hb j i)

end CFSG.StandardType.ZS

end

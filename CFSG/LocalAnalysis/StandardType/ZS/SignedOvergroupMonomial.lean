module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.ZS.MonomialStab
import CFSG.LocalAnalysis.StandardType.ZS.SignedOvergroupAxes
import TauCeti.GroupTheory.Perm.Basic

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {n : ℕ}

private theorem eq_of_smul_basis_eq_smul_basis (b : Module.Basis (Fin n) (ZMod p) U)
    {i j : Fin n} {a c : ZMod p} (ha : a ≠ 0) (h : a • b i = c • b j) : i = j ∧ a = c := by
  have h1 := congrArg b.repr h
  rw [map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.smul_single,
    Finsupp.smul_single, smul_eq_mul, mul_one, smul_eq_mul, mul_one] at h1
  rcases (Finsupp.single_eq_single_iff i j a c).mp h1 with ⟨hij, hac⟩ | ⟨h0, -⟩
  · exact ⟨hij, hac⟩
  · exact absurd h0 ha

private theorem pairUnit_comp_symm {i₀ i₁ : Fin n} (τ : Equiv.Perm (Fin n)) (c : (ZMod p)ˣ) :
    pairUnit p i₀ i₁ c ∘ τ.symm = pairUnit p (τ i₀) (τ i₁) c := by
  funext k
  simp only [Function.comp_apply, pairUnit, Equiv.symm_apply_eq]

private theorem permMap_conj_pairUnit (b : Module.Basis (Fin n) (ZMod p) U)
    {i₀ i₁ i j : Fin n} (τ : Equiv.Perm (Fin n)) (hτ₀ : τ i₀ = i) (hτ₁ : τ i₁ = j)
    (c : (ZMod p)ˣ) :
    permMap p b τ * diagMap p b (pairUnit p i₀ i₁ c) * (permMap p b τ)⁻¹ =
      diagMap p b (pairUnit p i j c) := by
  rw [permMap_mul_diagMap_mul_inv, pairUnit_comp_symm, hτ₀, hτ₁]

private theorem diagMap_f_eq_diagMap_b (b f : Module.Basis (Fin n) (ZMod p) U)
    (π : Equiv.Perm (Fin n)) (c : Fin n → (ZMod p)ˣ) (hf : ∀ i, f i = (c i : ZMod p) • b (π i))
    (d : Fin n → (ZMod p)ˣ) : diagMap p f d = diagMap p b (d ∘ π.symm) := by
  have hbk : ∀ i, b i = ((c (π.symm i) : ZMod p))⁻¹ • f (π.symm i) := fun i => by
    rw [hf (π.symm i), Equiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero (c (π.symm i))), one_smul]
  refine b.ext' fun i => ?_
  have hstep : diagMap p f d (b i) =
      ((c (π.symm i) : ZMod p))⁻¹ • diagMap p f d (f (π.symm i)) := by rw [hbk i, map_smul]
  rw [hstep, diagMap_apply_basis, hf (π.symm i), Equiv.apply_symm_apply, diagMap_apply_basis]
  have hsc : (((c (π.symm i) : ZMod p))⁻¹ * (d (π.symm i) : ZMod p)) * (c (π.symm i) : ZMod p)
      = (d (π.symm i) : ZMod p) := by
    rw [mul_assoc, mul_comm ((d (π.symm i) : ZMod p)) ((c (π.symm i) : ZMod p)), ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero (c (π.symm i))), one_mul]
  rw [smul_smul, smul_smul, hsc, Function.comp_apply]

private theorem diagMap_prod_mem (b : Module.Basis (Fin n) (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {ι : Type*} (s : Finset ι)
    (f : ι → Fin n → (ZMod p)ˣ) (h : ∀ k ∈ s, diagMap p b (f k) ∈ H) :
    diagMap p b (∏ k ∈ s, f k) ∈ H := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty, diagMap_one]
    exact H.one_mem
  · intro a s ha ih h
    rw [Finset.prod_insert ha, ← diagMap_mul]
    exact H.mul_mem (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

private theorem diagMap_pow (b : Module.Basis (Fin n) (ZMod p) U) (d : Fin n → (ZMod p)ˣ)
    (k : ℕ) : diagMap p b (d ^ k) = diagMap p b d ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, diagMap_one]
  | succ k ih => rw [pow_succ, pow_succ, ← diagMap_mul, ih]

private theorem two_pow_lt_three_pow_pred {n : ℕ} (hn : 3 ≤ n) : 2 ^ n < 3 ^ (n - 1) := by
  have h2 : 2 ^ n = 8 * 2 ^ (n - 3) := by
    conv_lhs => rw [show n = n - 3 + 3 by omega]
    rw [pow_add]
    norm_num
    ring
  have h3 : 3 ^ (n - 1) = 9 * 3 ^ (n - 3) := by
    conv_lhs => rw [show n - 1 = n - 3 + 2 by omega]
    rw [pow_add]
    norm_num
    ring
  rw [h2, h3]
  calc 8 * 2 ^ (n - 3) < 9 * 2 ^ (n - 3) :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num : 0 < 2))
    _ ≤ 9 * 3 ^ (n - 3) := Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left (by norm_num) _)

private theorem monomial_witness_of_gmmn (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hA : A = gmmn p f i₀ i₁ ζ) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i) := by
  intro a ha
  obtain ⟨d, σ, -, -, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi (hA ▸ ha)
  exact ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => by
    rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]⟩

private theorem monomial_witness_of_g2mmn (f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ)
    (hA : A = g2mmn p f i₀ i₁ ζ) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
      ∀ i, a (f i) = c i • f (σ i) := by
  intro a ha
  obtain ⟨d, σ, -, -, haeq⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi (hA ▸ ha)
  exact ⟨σ, fun i => (d (σ i) : ZMod p), fun i => Units.ne_zero (d (σ i)), fun i => by
    rw [haeq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]⟩

private theorem false_of_prod_eq_one_of_ite_neg_one {d : Fin n → (ZMod p)ˣ}
    {π : Equiv.Perm (Fin n)} {j₀ : Fin n} (hp : p ≠ 2) (hprod : ∏ k, d k = 1)
    (hd : ∀ k, d k = (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k)) : False := by
  have hεprod : ∏ l, (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) l = -1 := by simp
  have hcontr : (1 : (ZMod p)ˣ) = -1 := by
    calc (1 : (ZMod p)ˣ) = ∏ k, d k := hprod.symm
      _ = ∏ k, (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k) :=
          Finset.prod_congr rfl (fun k _ => hd k)
      _ = ∏ l, (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) l :=
          Equiv.prod_comp π (fun l => if l = j₀ then (-1 : (ZMod p)ˣ) else 1)
      _ = -1 := hεprod
  have hone : (-1 : ZMod p) = 1 := by
    have h := congrArg Units.val hcontr
    rw [Units.val_one, Units.val_neg, Units.val_one] at h
    exact h.symm
  rcases (ZMod.neg_one_eq_one_iff (n := p)).mp hone with h1 | h1
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp h1

theorem false_of_gmmn_of_signed_le (hp : p ≠ 2) (hn : 3 ≤ n)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) (ζ : (ZMod p)ˣ) (hA : A = gmmn p f i₀ i₁ ζ) : False := by
  classical
  have hmon := monomial_witness_of_gmmn f hi ζ hA
  obtain ⟨π, c, hf⟩ := exists_eq_smul_of_signed_le_monomial hp hn b f hperm hsgn hmon
  have hn0 : 0 < n := by omega
  let j₀ : Fin n := ⟨0, hn0⟩
  obtain ⟨d, σ, -, hprod, heq⟩ :=
    exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi (hA ▸ hsgn j₀)
  have hsval : ∀ k, diagMap p b (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (f k) =
      (((fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k)) : ZMod p) • f k := by
    intro k
    rw [hf k, map_smul, diagMap_apply_basis]
    simp only [smul_smul]
    rw [mul_comm]
  have hnorm : ∀ k, (d (σ k) : ZMod p) • f (σ k) =
      (((fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k)) : ZMod p) • f k := by
    intro k
    rw [← hsval k, heq, LinearEquiv.mul_apply, permMap_apply_basis, diagMap_apply_basis]
  have hdσ : ∀ k, σ k = k ∧
      d (σ k) = (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k) := by
    intro k
    obtain ⟨h1, h2⟩ := eq_of_smul_basis_eq_smul_basis f (Units.ne_zero (d (σ k))) (hnorm k)
    exact ⟨h1, Units.ext h2⟩
  have hdval : ∀ k, d k = (fun j => if j = j₀ then (-1 : (ZMod p)ˣ) else 1) (π k) := by
    intro k
    have h2 := (hdσ k).2
    rw [(hdσ k).1] at h2
    exact h2
  exact false_of_prod_eq_one_of_ite_neg_one hp hprod hdval

private theorem monomial_on_b_of_monomial_on_f (b f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {π : Equiv.Perm (Fin n)} {c : Fin n → (ZMod p)ˣ}
    (hf : ∀ i, f i = (c i : ZMod p) • b (π i))
    (hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (e : Fin n → ZMod p), (∀ i, e i ≠ 0) ∧
      ∀ i, a (f i) = e i • f (σ i)) :
    ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (e : Fin n → ZMod p), (∀ i, e i ≠ 0) ∧
      ∀ i, a (b i) = e i • b (σ i) := by
  intro a ha
  obtain ⟨σ, e, hne, haeq⟩ := hmon a ha
  have hbk : ∀ k, b k = ((c (π.symm k) : ZMod p))⁻¹ • f (π.symm k) := fun k => by
    rw [hf (π.symm k), Equiv.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero (c (π.symm k))), one_smul]
  have hae : ∀ k, a (b k) = ((c (π.symm k) : ZMod p))⁻¹ • a (f (π.symm k)) :=
    fun k => by rw [hbk k, map_smul]
  have hfσ : ∀ k, a (f (π.symm k)) = e (π.symm k) • f (σ (π.symm k)) := fun k => haeq _
  have hbσ : ∀ k, f (σ (π.symm k)) =
      (c (σ (π.symm k)) : ZMod p) • b (π (σ (π.symm k))) := fun k => hf _
  refine ⟨π * σ * π.symm,
    fun k => (c (π.symm k))⁻¹ * e (π.symm k) * c (σ (π.symm k)),
    fun k => mul_ne_zero (mul_ne_zero (Units.ne_zero ((c (π.symm k))⁻¹)) (hne _))
      (Units.ne_zero _), fun k => ?_⟩
  rw [hae k, hfσ k, hbσ k, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp only [smul_smul, mul_assoc, Units.val_inv_eq_inv_val]

private theorem exists_twist_mem_of_gen (b f : Module.Basis (Fin n) (ZMod p) U)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ A)
    {π : Equiv.Perm (Fin n)} {c : Fin n → (ZMod p)ˣ}
    (hf : ∀ i, f i = (c i : ZMod p) • b (π i))
    (hperm_f : ∀ σ, permMap p f σ ∈ A) {i₀ i₁ : Fin n} (hi : i₀ ≠ i₁)
    {ζ : (ZMod p)ˣ} {m : ℕ} (hm : 2 ≤ m) (hord : orderOf ζ = 2 * m)
    (hgen : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ A) :
    ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ → ∃ ζ' : (ZMod p)ˣ, (ζ' : ZMod p) ≠ 1 ∧ (ζ' : ZMod p) ≠ -1 ∧
      diagMap p b (pairUnit p a₁ a₂ ζ') * permMap p b (Equiv.swap a₁ a₂) ∈ A := by
  intro a₁ a₂ ha₁₂
  have hπne : π.symm a₁ ≠ π.symm a₂ := fun h => ha₁₂ (π.symm.injective h)
  obtain ⟨τ, -, hτ₀, hτ₁⟩ := TauCeti.exists_pair_perm_fixed (s := ∅) hi hπne
    (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _) (Set.notMem_empty _)
  have hconj : diagMap p f (pairUnit p (π.symm a₁) (π.symm a₂) ζ) ∈ A := by
    rw [← permMap_conj_pairUnit f τ hτ₀ hτ₁ ζ]
    exact A.mul_mem (A.mul_mem (hperm_f τ) hgen) (A.inv_mem (hperm_f τ))
  have heq : diagMap p f (pairUnit p (π.symm a₁) (π.symm a₂) ζ) =
      diagMap p b (pairUnit p a₁ a₂ ζ) := by
    rw [diagMap_f_eq_diagMap_b b f π c hf, pairUnit_comp_symm]
    simp only [Equiv.apply_symm_apply]
  have hunit1 : (ζ : ZMod p) ≠ 1 := by
    rintro h
    have h1 : ζ = 1 := Units.ext h
    rw [h1] at hord
    simp only [orderOf_one] at hord
    omega
  have hunit2 : (ζ : ZMod p) ≠ -1 := by
    rintro h
    have h2 : ζ ^ 2 = 1 := by
      have hζ : ζ = (-1 : (ZMod p)ˣ) := Units.ext (by rw [h]; rfl)
      rw [hζ]
      exact neg_one_sq
    have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact ⟨ζ, hunit1, hunit2, heq ▸ A.mul_mem hconj (hperm (Equiv.swap a₁ a₂))⟩

theorem exists_twist_mem_of_g2mmn (hp : p ≠ 2) (hn : 3 ≤ n)
    (b f : Module.Basis (Fin n) (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ A)
    (hsgn : ∀ i, diagMap p b (fun j => if j = i then -1 else 1) ∈ A) {i₀ i₁ : Fin n}
    (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} {m : ℕ} (hm : 2 ≤ m) (hord : orderOf ζ = 2 * m)
    (hA : A = g2mmn p f i₀ i₁ ζ) :
    (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i ≠ 0) ∧
        ∀ i, a (b i) = c i • b (σ i)) ∧
      ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ → ∃ ζ' : (ZMod p)ˣ, (ζ' : ZMod p) ≠ 1 ∧ (ζ' : ZMod p) ≠ -1 ∧
        diagMap p b (pairUnit p a₁ a₂ ζ') * permMap p b (Equiv.swap a₁ a₂) ∈ A := by
  classical
  have hmon_f := monomial_witness_of_g2mmn f hi ζ hA
  obtain ⟨π, c, hf⟩ := exists_eq_smul_of_signed_le_monomial hp hn b f hperm hsgn hmon_f
  have hperm_f : ∀ σ : Equiv.Perm (Fin n), permMap p f σ ∈ A := fun σ =>
    hA.symm ▸ Subgroup.subset_closure (Or.inl (Set.mem_range_self σ))
  have hgen : diagMap p f (pairUnit p i₀ i₁ ζ) ∈ A :=
    hA.symm ▸ Subgroup.subset_closure (Or.inr (Or.inr rfl))
  refine ⟨?_, ?_⟩
  · exact monomial_on_b_of_monomial_on_f b f hf hmon_f
  · exact exists_twist_mem_of_gen b f hperm hf hperm_f hi hm hord hgen

theorem twist_apply_basis_of_ne (b : Module.Basis (Fin n) (ZMod p) U) {a₁ a₂ k : Fin n}
    (h₁ : k ≠ a₁) (h₂ : k ≠ a₂) (ζ : (ZMod p)ˣ) :
    (diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂)) (b k) = b k := by
  rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_of_ne_of_ne h₁ h₂,
    diagMap_apply_basis]
  have h : pairUnit p a₁ a₂ ζ k = 1 := by simp only [pairUnit, h₁, h₂, if_false]
  rw [h, Units.val_one, one_smul]

theorem twist_not_signed (b : Module.Basis (Fin n) (ZMod p) U) {a₁ a₂ : Fin n} (ha : a₁ ≠ a₂)
    {ζ : (ZMod p)ˣ} (hζ1 : (ζ : ZMod p) ≠ 1) (hζ2 : (ζ : ZMod p) ≠ -1) :
    ¬ ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i = 1 ∨ c i = -1) ∧
      ∀ i, (diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂)) (b i) =
        c i • b (σ i) := by
  rintro ⟨σ, c, hc, h⟩
  have h1 : pairUnit p a₁ a₂ ζ a₂ = ζ⁻¹ := by
    simp only [pairUnit, Ne.symm ha, if_false, if_true]
  have ht : (diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂)) (b a₁) =
      ((ζ : ZMod p))⁻¹ • b a₂ := by
    rw [LinearEquiv.mul_apply, permMap_apply_basis, Equiv.swap_apply_left, diagMap_apply_basis, h1,
      Units.val_inv_eq_inv_val]
  obtain ⟨-, hcoef⟩ :=
    eq_of_smul_basis_eq_smul_basis b (inv_ne_zero (Units.ne_zero ζ)) (ht.symm.trans (h a₁))
  rcases hc a₁ with h2 | h2
  · have hcu : (ζ⁻¹ : (ZMod p)ˣ) = 1 :=
      Units.ext (by rw [Units.val_inv_eq_inv_val, hcoef, h2]; rfl)
    exact hζ1 (by rw [← inv_inv ζ, hcu, inv_one]; rfl)
  · have hcu : (ζ⁻¹ : (ZMod p)ˣ) = -1 :=
      Units.ext (by rw [Units.val_inv_eq_inv_val, hcoef, h2]; rfl)
    exact hζ2 (by rw [← inv_inv ζ, hcu, inv_neg_one]; rfl)

private noncomputable def diagTuple {a₂ : Fin n} {m : ℕ} (ζ : (ZMod p)ˣ)
    (e : {k : Fin n // k ≠ a₂} → Fin m) : Fin n → (ZMod p)ˣ :=
  ∏ k : {k : Fin n // k ≠ a₂}, (pairUnit p k.1 a₂ ζ) ^ (e k : ℕ)

private theorem three_le_orderOf_of_ne_one_ne_neg_one {ζ : (ZMod p)ˣ}
    (hζ1 : (ζ : ZMod p) ≠ 1) (hζ2 : (ζ : ZMod p) ≠ -1) : 3 ≤ orderOf ζ := by
  have hne1 : orderOf ζ ≠ 1 := by
    intro h
    have h1 : ζ = 1 := orderOf_eq_one_iff.mp h
    exact hζ1 (by rw [h1]; simp)
  have hne2 : orderOf ζ ≠ 2 := by
    intro h
    have hsq : (ζ : ZMod p) ^ 2 = 1 := by
      have hpow := pow_orderOf_eq_one ζ
      rw [h] at hpow
      simpa using congrArg Units.val hpow
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exact hζ1 h1
    · exact hζ2 h1
  have hpos : 0 < orderOf ζ := orderOf_pos ζ
  omega

private theorem diagTuple_apply {a₂ : Fin n} {m : ℕ} (ζ : (ZMod p)ˣ)
    (e : {k : Fin n // k ≠ a₂} → Fin m) (k : {k : Fin n // k ≠ a₂}) :
    diagTuple ζ e k.1 = ζ ^ (e k : ℕ) := by
  have hstep : diagTuple ζ e k.1 =
      ∏ j : {k : Fin n // k ≠ a₂}, ((pairUnit p j.1 a₂ ζ) ^ (e j : ℕ)) k.1 := by
    rw [diagTuple, Finset.prod_apply]
  rw [hstep]
  have hsingle : (∏ j : {k : Fin n // k ≠ a₂},
      ((pairUnit p j.1 a₂ ζ) ^ (e j : ℕ)) k.1) =
      ((pairUnit p k.1 a₂ ζ) ^ (e k : ℕ)) k.1 := by
    refine Finset.prod_eq_single k ?_ ?_
    · intro j _ hj
      have hjk : j.1 ≠ k.1 := fun h => hj (Subtype.ext h)
      rw [Pi.pow_apply]
      have h1 : pairUnit p j.1 a₂ ζ k.1 = 1 := by
        simp only [pairUnit, Ne.symm hjk, k.2, if_false]
      rw [h1, one_pow]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [hsingle, Pi.pow_apply]
  have h1 : pairUnit p k.1 a₂ ζ k.1 = ζ := by simp only [pairUnit, if_true, k.2]
  rw [h1]

private theorem diagMap_diagTuple_mem {m : ℕ} (b : Module.Basis (Fin n) (ZMod p) U)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hperm : ∀ σ, permMap p b σ ∈ H) {a₁ a₂ : Fin n}
    (ha : a₁ ≠ a₂) {ζ : (ZMod p)ˣ}
    (ht : diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂) ∈ H) :
    ∀ e : {k : Fin n // k ≠ a₂} → Fin m, diagMap p b (diagTuple ζ e) ∈ H := by
  have hdiag : diagMap p b (pairUnit p a₁ a₂ ζ) ∈ H := by
    have h := H.mul_mem ht (H.inv_mem (hperm (Equiv.swap a₁ a₂)))
    simpa [mul_assoc] using h
  have hgen : ∀ k : Fin n, k ≠ a₂ → diagMap p b (pairUnit p k a₂ ζ) ∈ H := by
    intro k hk
    have hτ₀ : Equiv.swap a₁ k a₁ = k := Equiv.swap_apply_left a₁ k
    have hτ₁ : Equiv.swap a₁ k a₂ = a₂ :=
      Equiv.swap_apply_of_ne_of_ne ha.symm (Ne.symm hk)
    rw [← permMap_conj_pairUnit b (Equiv.swap a₁ k) hτ₀ hτ₁ ζ]
    exact H.mul_mem (H.mul_mem (hperm _) hdiag) (H.inv_mem (hperm _))
  intro e
  refine diagMap_prod_mem b Finset.univ (fun k => (pairUnit p k.1 a₂ ζ) ^ (e k : ℕ)) ?_
  intro k _
  rw [diagMap_pow]
  exact H.pow_mem (hgen k.1 k.2) (e k : ℕ)

private theorem diagTuple_mul_permMap_injective (b : Module.Basis (Fin n) (ZMod p) U)
    {a₂ : Fin n} (ζ : (ZMod p)ˣ) {m : ℕ} (hm : orderOf ζ = m) :
    Function.Injective (fun q : ({k : Fin n // k ≠ a₂} → Fin m) × Equiv.Perm (Fin n) =>
      diagMap p b (diagTuple ζ q.1) * permMap p b q.2) := by
  rintro ⟨e, σ⟩ ⟨e', σ'⟩ hq
  have h2 : ∀ i, σ i = σ' i ∧ diagTuple ζ e (σ i) = diagTuple ζ e' (σ i) := by
    intro i
    have h3 : (diagTuple ζ e (σ i) : ZMod p) • b (σ i) =
        (diagTuple ζ e' (σ' i) : ZMod p) • b (σ' i) := by
      have h4 := congrArg (fun f : U ≃ₗ[ZMod p] U => f (b i)) hq
      simpa only [LinearEquiv.mul_apply, diagMap_apply_basis, permMap_apply_basis] using h4
    obtain ⟨hσ, hco⟩ := eq_of_smul_basis_eq_smul_basis b
      (Units.ne_zero (diagTuple ζ e (σ i))) h3
    rw [← hσ] at hco
    exact ⟨hσ, Units.ext hco⟩
  have he : e = e' := by
    funext k
    have hk1 : diagTuple ζ e k.1 = diagTuple ζ e' k.1 := by
      have h := (h2 (σ.symm k.1)).2
      rwa [Equiv.apply_symm_apply] at h
    rw [diagTuple_apply ζ e k, diagTuple_apply ζ e' k] at hk1
    have hmod : (e k : ℕ) ≡ (e' k : ℕ) [MOD m] := by
      have h := (pow_eq_pow_iff_modEq (x := ζ) (n := (e k : ℕ)) (m := (e' k : ℕ))).mp hk1
      rwa [hm] at h
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod (e k).isLt (e' k).isLt)
  have hσ : σ = σ' := Equiv.ext fun i => (h2 i).1
  rw [he, hσ]

private theorem card_diagTuple_perm (a₂ : Fin n) (m : ℕ) :
    Nat.card (({k : Fin n // k ≠ a₂} → Fin m) × Equiv.Perm (Fin n)) =
      m ^ (n - 1) * n.factorial := by
  have hcardι : Fintype.card {k : Fin n // k ≠ a₂} = n - 1 := by
    have h := Fintype.card_subtype_compl (fun k : Fin n => k = a₂)
    rw [Fintype.card_fin, Fintype.card_subtype_eq] at h
    exact h
  have hcardD : Nat.card ({k : Fin n // k ≠ a₂} → Fin m) = m ^ (n - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcardι]
  have hcardperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [Nat.card_prod, hcardD, hcardperm]

theorem two_pow_mul_factorial_lt_card_of_twist_mem (hn : 3 ≤ n)
    (b : Module.Basis (Fin n) (ZMod p) U) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hperm : ∀ σ, permMap p b σ ∈ H) {a₁ a₂ : Fin n} (ha : a₁ ≠ a₂) {ζ : (ZMod p)ˣ}
    (hζ1 : (ζ : ZMod p) ≠ 1) (hζ2 : (ζ : ZMod p) ≠ -1)
    (ht : diagMap p b (pairUnit p a₁ a₂ ζ) * permMap p b (Equiv.swap a₁ a₂) ∈ H) :
    2 ^ n * n.factorial < Nat.card H := by
  classical
  have hfinH : Finite H := by
    refine Finite.of_injective
      (f := fun f : H => fun i : Fin n => b.equivFun ((f : U ≃ₗ[ZMod p] U) (b i))) ?_
    intro f g hfg
    refine Subtype.ext (b.ext' fun i => b.equivFun.injective (congrFun hfg i))
  set m := orderOf ζ with hm
  have hm3 : 3 ≤ m := by rw [hm]; exact three_le_orderOf_of_ne_one_ne_neg_one hζ1 hζ2
  have hDmem : ∀ e : {k : Fin n // k ≠ a₂} → Fin m, diagMap p b (diagTuple ζ e) ∈ H :=
    diagMap_diagTuple_mem b hperm ha ht
  have hinj : Function.Injective
      (fun q : ({k : Fin n // k ≠ a₂} → Fin m) × Equiv.Perm (Fin n) =>
        (⟨diagMap p b (diagTuple ζ q.1) * permMap p b q.2,
          H.mul_mem (hDmem q.1) (hperm q.2)⟩ : H)) := by
    intro q₁ q₂ hq
    exact diagTuple_mul_permMap_injective b ζ hm.symm (Subtype.ext_iff.mp hq)
  have hle : m ^ (n - 1) * n.factorial ≤ Nat.card H := by
    have h := @Nat.card_le_card_of_injective _ _ hfinH _ hinj
    rwa [card_diagTuple_perm a₂ m] at h
  calc 2 ^ n * n.factorial < m ^ (n - 1) * n.factorial :=
        Nat.mul_lt_mul_of_pos_right
          (lt_of_lt_of_le (two_pow_lt_three_pow_pred hn) (Nat.pow_le_pow_left hm3 _))
          (Nat.factorial_pos n)
    _ ≤ Nat.card H := hle

end CFSG.StandardType.ZS

end

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Data.Nat.Prime.Factorial

public section

namespace CFSG.Walter.JT

open Module

section Weights

variable {K V Γ : Type*} [Field K] [AddCommGroup V] [Module K V] [Group Γ]

@[expose] noncomputable def weightSpace (ρ : Representation K Γ V) (N : Subgroup Γ)
    (χ : N → K) : Submodule K V :=
  ⨅ n : N, Module.End.eigenspace (ρ n) (χ n)

theorem mem_weightSpace {ρ : Representation K Γ V} {N : Subgroup Γ} {χ : N → K} {v : V} :
    v ∈ weightSpace ρ N χ ↔ ∀ n : N, ρ n v = χ n • v := by
  simp [weightSpace]

abbrev weights (ρ : Representation K Γ V) (N : Subgroup Γ) : Type _ :=
  {χ : N → K // weightSpace ρ N χ ≠ ⊥}

theorem iSupIndep_weightSpace_and_iSup_eq_top [IsAlgClosed K] [FiniteDimensional K V]
    [Finite Γ] (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0) :
    iSupIndep (weightSpace ρ N) ∧ ⨆ χ, weightSpace ρ N χ = ⊤ := by
  classical
  let f : N → Module.End K V := fun n => ρ n
  have hcomm (i j : N) : Commute (f i) (f j) := hN i i.2 j j.2
  have hss (n : N) : (f n).IsFinitelySemisimple := by
    refine Module.End.IsSemisimple.isFinitelySemisimple <|
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (Polynomial.separable_X_pow_sub_C 1 hNchar one_ne_zero).squarefree ?_
    have h1 : f n ^ Nat.card N = 1 := by
      change ρ n ^ Nat.card N = 1
      rw [← map_pow, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one, map_one]
    simp [h1]
  have hEG (χ : N → K) : weightSpace ρ N χ = ⨅ n, (f n).maxGenEigenspace (χ n) := by
    simp only [weightSpace, f, (hss _).maxGenEigenspace_eq_eigenspace]
  have hfun : weightSpace ρ N = fun χ : N → K => ⨅ n, (f n).maxGenEigenspace (χ n) :=
    funext hEG
  refine ⟨?_, ?_⟩
  · have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
    rwa [hfun]
  · rw [hfun]
    exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun i j _ => hcomm i j) fun i => Module.End.iSup_maxGenEigenspace_eq_top _

theorem finite_weights_and_card_le [IsAlgClosed K] [FiniteDimensional K V] [Finite Γ]
    (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0) :
    Finite (weights ρ N) ∧ Nat.card (weights ρ N) ≤ finrank K V := by
  classical
  have hind := (iSupIndep_weightSpace_and_iSup_eq_top ρ N hN hNchar).1
  let : Fintype {χ // weightSpace ρ N χ ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  refine ⟨inferInstanceAs (Finite {χ // weightSpace ρ N χ ≠ ⊥}), ?_⟩
  change Nat.card {χ // weightSpace ρ N χ ≠ ⊥} ≤ _
  rw [Nat.card_eq_fintype_card]
  exact hind.subtype_ne_bot_le_finrank

theorem conj_mem_of_mem_normalizer {N : Subgroup Γ} (g : Subgroup.normalizer (N : Set Γ))
    (n : N) : (g : Γ)⁻¹ * n * g ∈ N :=
  (Subgroup.mem_normalizer_iff''.mp g.2 n).mp n.2

@[expose] def twist {N : Subgroup Γ} (g : Subgroup.normalizer (N : Set Γ)) (χ : N → K) :
    N → K :=
  fun n => χ ⟨(g : Γ)⁻¹ * n * g, conj_mem_of_mem_normalizer g n⟩

omit [Field K] [AddCommGroup V] [Module K V] in
theorem twist_one {N : Subgroup Γ} (χ : N → K) : twist (1 : Subgroup.normalizer (N : Set Γ)) χ = χ :=
  funext fun n => congrArg χ (Subtype.ext (by simp))

omit [Field K] [AddCommGroup V] [Module K V] in
theorem twist_mul {N : Subgroup Γ} (g h : Subgroup.normalizer (N : Set Γ)) (χ : N → K) :
    twist (g * h) χ = twist g (twist h χ) :=
  funext fun n => congrArg χ (Subtype.ext (by simp [mul_assoc]))

theorem map_mem_weightSpace_twist {ρ : Representation K Γ V} {N : Subgroup Γ}
    (g : Subgroup.normalizer (N : Set Γ)) {χ : N → K} {v : V} (hv : v ∈ weightSpace ρ N χ) :
    ρ g v ∈ weightSpace ρ N (twist g χ) := by
  rw [mem_weightSpace] at hv ⊢
  intro n
  have h1 : (n : Γ) * g = g * ((g : Γ)⁻¹ * n * g) := by group
  change ρ n (ρ g v) = χ ⟨_, conj_mem_of_mem_normalizer g n⟩ • ρ g v
  rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply,
    ← map_smul, ← hv ⟨_, conj_mem_of_mem_normalizer g n⟩]

theorem weightSpace_twist_ne_bot {ρ : Representation K Γ V} {N : Subgroup Γ}
    (g : Subgroup.normalizer (N : Set Γ)) {χ : N → K} (hχ : weightSpace ρ N χ ≠ ⊥) :
    weightSpace ρ N (twist g χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine fun h0 => hv0 ?_
  have h1 := map_mem_weightSpace_twist (ρ := ρ) g hv
  rw [h0, Submodule.mem_bot] at h1
  have h2 : ρ (g : Γ)⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← h2, h1, map_zero]

@[expose, instance_reducible] noncomputable def weightAction (ρ : Representation K Γ V) (N : Subgroup Γ) :
    MulAction (Subgroup.normalizer (N : Set Γ)) (weights ρ N) where
  smul g χ := ⟨twist g χ.1, weightSpace_twist_ne_bot g χ.2⟩
  one_smul χ := Subtype.ext (twist_one χ.1)
  mul_smul g h χ := Subtype.ext (twist_mul g h χ.1)

theorem map_conj_eq_of_forall_twist_eq [IsAlgClosed K] [FiniteDimensional K V] [Finite Γ]
    (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    (g : Subgroup.normalizer (N : Set Γ))
    (hg : ∀ χ : N → K, weightSpace ρ N χ ≠ ⊥ → twist g χ = χ) :
    ∀ n ∈ N, ρ ((g : Γ) * n * (g : Γ)⁻¹) = ρ n := by
  intro n hn
  have htop := (iSupIndep_weightSpace_and_iSup_eq_top ρ N hN hNchar).2
  have hle : ∀ χ, weightSpace ρ N χ ≤
      LinearMap.eqLocus (ρ ((g : Γ) * n * (g : Γ)⁻¹)) (ρ n) := by
    intro χ v hv
    by_cases hχ : weightSpace ρ N χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hv
      rw [hv]
      exact (LinearMap.eqLocus _ _).zero_mem
    ·
      have hfix : twist g⁻¹ χ = χ := by
        calc twist g⁻¹ χ = twist g⁻¹ (twist g χ) := by rw [hg χ hχ]
          _ = χ := by rw [← twist_mul, inv_mul_cancel, twist_one]
      have hw : ρ ((g⁻¹ : Subgroup.normalizer (N : Set Γ)) : Γ) v ∈ weightSpace ρ N χ := by
        have := map_mem_weightSpace_twist (ρ := ρ) g⁻¹ hv
        rwa [hfix] at this
      rw [mem_weightSpace] at hv hw
      change ρ ((g : Γ) * n * (g : Γ)⁻¹) v = ρ n v
      have hw' := hw ⟨n, hn⟩
      simp only [Subgroup.coe_inv] at hw'
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw', map_smul,
        ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
        hv ⟨n, hn⟩]
  have : LinearMap.eqLocus (ρ ((g : Γ) * n * (g : Γ)⁻¹)) (ρ n) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le hle
  exact LinearMap.eqLocus_eq_top.mp this

@[expose] noncomputable def weightPerm (ρ : Representation K Γ V) (N : Subgroup Γ) :
    Subgroup.normalizer (N : Set Γ) →* Equiv.Perm (weights ρ N) :=
  @MulAction.toPermHom _ _ _ (weightAction ρ N)

theorem weightPerm_apply_val (ρ : Representation K Γ V) (N : Subgroup Γ)
    (g : Subgroup.normalizer (N : Set Γ)) (χ : weights ρ N) :
    (weightPerm ρ N g χ).1 = twist g χ.1 := rfl

theorem map_conj_eq_of_weightPerm_eq_one [IsAlgClosed K] [FiniteDimensional K V] [Finite Γ]
    (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    (g : Subgroup.normalizer (N : Set Γ)) (hg : weightPerm ρ N g = 1) :
    ∀ n ∈ N, ρ ((g : Γ) * n * (g : Γ)⁻¹) = ρ n := by
  refine map_conj_eq_of_forall_twist_eq ρ N hN hNchar g fun χ hχ => ?_
  have := congrArg (fun τ : Equiv.Perm (weights ρ N) => (τ ⟨χ, hχ⟩).1) hg
  simpa [weightPerm_apply_val] using this

end Weights

theorem perm_fin_sq_or_cube {n : ℕ} (hn : n ≤ 3) (σ : Equiv.Perm (Fin n)) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  interval_cases n <;> revert σ <;> decide

theorem perm_sq_or_cube {α : Type*} [Finite α] (hα : Nat.card α ≤ 3) (σ : Equiv.Perm α) :
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin (Fintype.card α)) := Equiv.permCongrHom e
  have hc : Fintype.card α ≤ 3 := by rwa [← Nat.card_eq_fintype_card]
  rcases perm_fin_sq_or_cube hc (φ σ) with h | h
  · left
    apply φ.injective
    rw [map_pow, h, map_one]
  · right
    apply φ.injective
    rw [map_pow, h, map_one]

section Consequences

variable {K V Γ : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Group Γ] [Finite Γ]

theorem map_conj_sq_or_cube (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    (hV : finrank K V ≤ 3) {g : Γ} (hg : g ∈ Subgroup.normalizer (N : Set Γ)) :
    (∀ n ∈ N, ρ (g ^ 2 * n * (g ^ 2)⁻¹) = ρ n) ∨
      (∀ n ∈ N, ρ (g ^ 3 * n * (g ^ 3)⁻¹) = ρ n) := by
  obtain ⟨hfin, hcard⟩ := finite_weights_and_card_le ρ N hN hNchar
  set g' : Subgroup.normalizer (N : Set Γ) := ⟨g, hg⟩
  rcases perm_sq_or_cube (hcard.trans hV) (weightPerm ρ N g') with h | h
  · left
    rw [← map_pow] at h
    simpa [g'] using map_conj_eq_of_weightPerm_eq_one ρ N hN hNchar (g' ^ 2) h
  · right
    rw [← map_pow] at h
    simpa [g'] using map_conj_eq_of_weightPerm_eq_one ρ N hN hNchar (g' ^ 3) h

theorem map_conj_eq_of_coprime_six (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    (hV : finrank K V ≤ 3) {g : Γ} (hg : g ∈ Subgroup.normalizer (N : Set Γ))
    (hcop : Nat.Coprime (orderOf g) 6) :
    ∀ n ∈ N, ρ (g * n * g⁻¹) = ρ n := by
  obtain ⟨hfin, hcard⟩ := finite_weights_and_card_le ρ N hN hNchar
  set g' : Subgroup.normalizer (N : Set Γ) := ⟨g, hg⟩
  have h1 : orderOf (weightPerm ρ N g') ∣ orderOf g := by
    have := orderOf_map_dvd (weightPerm ρ N) g'
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (weightPerm ρ N g') ∣ 6 := by
    rcases perm_sq_or_cube (hcard.trans hV) (weightPerm ρ N g') with h | h
    · exact (orderOf_dvd_of_pow_eq_one h).trans (by norm_num)
    · exact (orderOf_dvd_of_pow_eq_one h).trans (by norm_num)
  have h3 : orderOf (weightPerm ρ N g') = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left h1) h2
  simpa [g'] using map_conj_eq_of_weightPerm_eq_one ρ N hN hNchar g' (orderOf_eq_one_iff.mp h3)

theorem map_conj_eq_of_isPGroup (ρ : Representation K Γ V) (N : Subgroup Γ)
    (hN : ∀ a ∈ N, ∀ b ∈ N, ρ a * ρ b = ρ b * ρ a) (hNchar : ((Nat.card N : ℕ) : K) ≠ 0)
    {r : ℕ} (hr : r.Prime) (hV : finrank K V < r) {R : Subgroup Γ} (hR : IsPGroup r R)
    (hRN : R ≤ Subgroup.normalizer (N : Set Γ)) :
    ∀ g ∈ R, ∀ n ∈ N, ρ (g * n * g⁻¹) = ρ n := by
  obtain ⟨hfin, hcard⟩ := finite_weights_and_card_le ρ N hN hNchar
  intro g hgR
  set g' : Subgroup.normalizer (N : Set Γ) := ⟨g, hRN hgR⟩
  obtain ⟨k, hk⟩ := hR ⟨g, hgR⟩
  have hgk : g ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf (weightPerm ρ N g') ∣ r ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : g' ^ r ^ k = 1 := Subtype.ext (by simpa [g'] using hgk)
    rw [this, map_one]
  have h2 : orderOf (weightPerm ρ N g') ∣ (Nat.card (weights ρ N)).factorial := by
    have := orderOf_dvd_natCard (weightPerm ρ N g')
    rwa [Nat.card_perm] at this
  have h3 : Nat.Coprime (r ^ k) (Nat.card (weights ρ N)).factorial :=
    Nat.Coprime.pow_left _ (Nat.Prime.coprime_factorial_of_lt hr (by omega))
  have hσ : weightPerm ρ N g' = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)
  simpa [g'] using map_conj_eq_of_weightPerm_eq_one ρ N hN hNchar g' hσ

end Consequences

end CFSG.Walter.JT

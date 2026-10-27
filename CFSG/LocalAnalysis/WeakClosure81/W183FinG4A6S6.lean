module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def w183finG4A6AutS6 {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6)) :
    Subgroup (MulAut M) :=
  (MonoidHom.range
    (MulAut.conjNormal : Equiv.Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6)))).comap
      (MulAut.congr e).toMonoidHom

theorem w183finG4A6_mem_autS6_iff {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6))
    (γ : MulAut M) : γ ∈ w183finG4A6AutS6 e ↔ ∃ π : Equiv.Perm (Fin 6), ∀ m : M,
      ((e (γ m) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        π * ((e m : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * π⁻¹ := by
  simp only [w183finG4A6AutS6, Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨π, hπ⟩
    refine ⟨π, fun m => ?_⟩
    have h := congrArg (fun σ : MulAut (alternatingGroup (Fin 6)) =>
      ((σ (e m) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) hπ
    simp only [MulAut.conjNormal_apply] at h
    simpa using h.symm
  · rintro ⟨π, hπ⟩
    refine ⟨π, MulEquiv.ext fun a => ?_⟩
    apply Subtype.ext
    have h := hπ (e.symm a)
    simp only [MulEquiv.apply_symm_apply] at h
    simpa [MulAut.conjNormal_apply] using h.symm

theorem w183finG4A6_center_eq_bot {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6)) :
    Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    have := congrArg e (hz (e.symm y))
    simpa using this
  rw [alternatingGroup.center_eq_bot (by simp)] at hz'
  have h1 : e z = 1 := hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by simpa using h1)

private theorem w183finG4A6_relIndex_psl_s6 :
    A6Models.psl29.relIndex A6Facts.s6 = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨A6Models.tFrob, A6Facts.tFrob_mem_s6, A6Facts.tFrob_not_mem_psl, ?_⟩
  intro b hb
  exact (A6Facts.s6_cases hb).elim Or.inr Or.inl

theorem w183finG4A6_model_card_s6 : Nat.card A6Facts.s6 = 720 := by
  have hcard := Subgroup.relIndex_mul_card (H := A6Models.psl29) (K := A6Facts.s6)
  rw [w183finG4A6_relIndex_psl_s6, inf_eq_left.mpr A6Facts.psl29_le_s6, A6Facts.card_psl29] at hcard
  norm_num at hcard
  exact hcard.symm

theorem w183finG4A6_model_psl_s6 :
    (A6Models.psl29.subgroupOf A6Facts.s6).Normal ∧
      A6Models.psl29.relIndex A6Facts.s6 = 2 := by
  refine ⟨?_, w183finG4A6_relIndex_psl_s6⟩
  rw [Subgroup.normal_subgroupOf_iff A6Facts.psl29_le_s6]
  intro h k hh hk
  exact A6Facts.psl29_normal k (A6Facts.s6_le_autA6 hk) h hh

theorem w183finG4A6_model_s6_normal :
    ∀ g ∈ A6Models.autA6, ∀ x ∈ A6Facts.s6, g * x * g⁻¹ ∈ A6Facts.s6 := by
  have hcardH : Nat.card (A6Facts.s6.subgroupOf A6Models.autA6) = 720 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A6Facts.s6_le_autA6).toEquiv,
      w183finG4A6_model_card_s6]
  have hindex : (A6Facts.s6.subgroupOf A6Models.autA6).index = 2 := by
    have h := Subgroup.index_mul_card (H := A6Facts.s6.subgroupOf A6Models.autA6)
    rw [hcardH, A6Facts.card_autA6] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 720) (by rw [h])
  haveI hN : (A6Facts.s6.subgroupOf A6Models.autA6).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  intro g hg x hx
  have hmem := hN.conj_mem (⟨x, A6Facts.s6_le_autA6 hx⟩ : ↥A6Models.autA6) hx ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem w183finG4A6_exists_model {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 6)) :
    ∃ f : MulAut M →* Equiv.Perm (Fin 10), Function.Injective f ∧
      (∀ γ, f γ ∈ A6Models.autA6) ∧ (∀ x ∈ A6Models.autA6, ∃ γ, f γ = x) ∧
      (∀ γ, γ ∈ innAutOf M ↔ f γ ∈ A6Models.psl29) ∧
      (∀ γ, γ ∈ w183finG4A6AutS6 e ↔ f γ ∈ A6Facts.s6) := by
  obtain ⟨θ, ψ, hθinj, hψθ⟩ := Unc25K1.A6Model.exists_pslEquiv
  set φ : M ≃* ↥A6Models.psl29 := e.trans ψ.symm with hφ
  set Θ : MulAut M ≃* ↥A6Models.autA6 := Unc25K1.A6Model.thetaEquiv φ with hΘ
  set f : MulAut M →* Equiv.Perm (Fin 10) := A6Models.autA6.subtype.comp Θ.toMonoidHom with hf
  have hcard6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hθsurj : Function.Surjective θ :=
    (hθinj.bijective_of_nat_card_le (by rw [hcard6, w183finG4A6_model_card_s6])).2
  have hΘconj : ∀ m : M,
      ((Unc25K1.A6Model.thetaEquiv φ (MulAut.conj m) : ↥A6Models.autA6) : P10) =
        (φ m : P10) := fun m => congrArg Subtype.val
    (Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conj m)
      ⟨φ m, A6Facts.psl29_le_autA6 (φ m).2⟩ fun _ => by
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
        rfl)
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf]
    exact Subtype.val_injective.comp Θ.injective
  · intro γ
    rw [hf]
    exact (Θ γ).2
  · intro x hx
    refine ⟨Θ.symm ⟨x, hx⟩, ?_⟩
    rw [hf]
    simp
  · intro γ
    rw [hf]
    constructor
    · intro hγ
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hγ
      rw [← hm]
      change ((Θ (MulAut.conj m) : ↥A6Models.autA6) : P10) ∈ A6Models.psl29
      rw [hΘ, hΘconj m]
      exact (φ m).2
    · intro hf'
      have hx : ((Θ γ : ↥A6Models.autA6) : P10) ∈ A6Models.psl29 := hf'
      obtain ⟨m, hm⟩ := φ.surjective ⟨((Θ γ : ↥A6Models.autA6) : P10), hx⟩
      refine MonoidHom.mem_range.2 ⟨m, ?_⟩
      apply Θ.injective
      apply Subtype.ext
      rw [hΘ, hΘconj m]
      exact congrArg Subtype.val hm
  · intro γ
    rw [hf]
    constructor
    · intro hγ
      rw [w183finG4A6_mem_autS6_iff e γ] at hγ
      obtain ⟨π, hπ⟩ := hγ
      obtain ⟨y, hy⟩ := hθsurj π
      have hrel : ∀ k : M, ((φ (γ k) : ↥A6Models.psl29) : P10) =
          (y : P10) * ((φ k : ↥A6Models.psl29) : P10) * (y : P10)⁻¹ := by
        intro k
        have h1 : θ (Subgroup.inclusion A6Facts.psl29_le_s6 (φ (γ k))) =
            π * θ (Subgroup.inclusion A6Facts.psl29_le_s6 (φ k)) * π⁻¹ := by
          have e1 : ψ (φ (γ k)) = e (γ k) := by simp [hφ]
          have e2 : ψ (φ k) = e k := by simp [hφ]
          have h4 : ((e (γ k) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
              θ (Subgroup.inclusion A6Facts.psl29_le_s6 (φ (γ k))) := by
            rw [← e1]; exact hψθ _
          have h5 : ((e k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
              θ (Subgroup.inclusion A6Facts.psl29_le_s6 (φ k)) := by
            rw [← e2]; exact hψθ _
          rw [← h4, ← h5]
          exact hπ k
        have h2 : Subgroup.inclusion A6Facts.psl29_le_s6 (φ (γ k)) =
            y * Subgroup.inclusion A6Facts.psl29_le_s6 (φ k) * y⁻¹ := by
          apply hθinj
          rw [h1, ← hy, map_mul, map_mul, map_inv]
        simpa using congrArg (fun z : ↥A6Facts.s6 => (z : P10)) h2
      have hb : ((Unc25K1.A6Model.thetaEquiv φ γ : ↥A6Models.autA6) : P10) = (y : P10) :=
        congrArg Subtype.val
          (Unc25K1.A6Model.thetaEquiv_eq φ γ ⟨y, A6Facts.s6_le_autA6 y.2⟩ hrel)
      change ((Unc25K1.A6Model.thetaEquiv φ γ : ↥A6Models.autA6) : P10) ∈ A6Facts.s6
      rw [hb]
      exact y.2
    · intro hf'
      exact (w183finG4A6_mem_autS6_iff e γ).2
        (Unc25K1.A6Model.s6_induces θ ψ hψθ e γ hf')

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusStd

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU

section Aut

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type*} [Group H] (ρ : H →* Module.End K V)

theorem map_flagKernel_of_conj (α : H ≃* H) (g : V ≃ₗ[K] V)
    (hα : ∀ h v, ρ (α h) v = g (ρ h (g.symm v))) (F : ℕ → Submodule K V) :
    (flagKernel ρ F).map α.toMonoidHom =
      flagKernel ρ (fun k => (F k).map (g : V →ₗ[K] V)) := by
  have hmemF : ∀ {k : ℕ} {v : V}, v ∈ (F k).map (g : V →ₗ[K] V) ↔ g.symm v ∈ F k := by
    intro k v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨g.symm v, hv, by simp⟩
  have hinv : ∀ h v, ρ (α h)⁻¹ v = g (ρ h⁻¹ (g.symm v)) := fun h v => by
    rw [← map_inv, hα]
  ext x
  constructor
  · rintro ⟨h, ⟨hS, hK⟩, rfl⟩
    refine ⟨fun k v hv => ?_, fun k v hv => ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [MulEquiv.coe_toMonoidHom, hα, hmemF, LinearEquiv.symm_apply_apply]
        exact (hS k _ (hmemF.mp hv)).1
      · rw [MulEquiv.coe_toMonoidHom, hinv, hmemF, LinearEquiv.symm_apply_apply]
        exact (hS k _ (hmemF.mp hv)).2
    · rw [MulEquiv.coe_toMonoidHom, hα, hmemF, map_sub, LinearEquiv.symm_apply_apply]
      exact hK k _ (hmemF.mp hv)
  · intro hx
    refine ⟨α.symm x, ⟨fun k v hv => ?_, fun k v hv => ?_⟩, by simp⟩
    · have hx' := hx.1 k (g v) (hmemF.mpr (by simpa using hv))
      have e1 : ∀ w, ρ (α.symm x) w = g.symm (ρ x (g w)) := fun w => by
        have := hα (α.symm x) (g w)
        rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at this
        rw [this, LinearEquiv.symm_apply_apply]
      have e2 : ∀ w, ρ (α.symm x)⁻¹ w = g.symm (ρ x⁻¹ (g w)) := fun w => by
        have := hinv (α.symm x) (g w)
        rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at this
        rw [this, LinearEquiv.symm_apply_apply]
      exact ⟨by rw [e1]; exact hmemF.mp hx'.1, by rw [e2]; exact hmemF.mp hx'.2⟩
    · have e1 : ρ (α.symm x) v = g.symm (ρ x (g v)) := by
        have := hα (α.symm x) (g v)
        rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at this
        rw [this, LinearEquiv.symm_apply_apply]
      have hx' := hx.2 k (g v) (hmemF.mpr (by simpa using hv))
      rw [hmemF, map_sub, LinearEquiv.symm_apply_apply] at hx'
      rw [e1]
      exact hx'

end Aut

variable {n : ℕ} {K : Type} [Field K]

section Conj

variable [CharP K 2]

omit [CharP K 2] in
theorem map_conj_range_spinAction (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)) :
    (spinAction (quadPlus n K)).range.map ((MulAut.conj g : _ ≃* _) : _ →* _) =
      (spinAction (quadPlus n K)).range := by
  rw [range_spinAction_quadPlus hn]
  refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_elementaryGroup hg hx
  · have := conj_mem_elementaryGroup (inv_mem hg) hx
    rwa [inv_inv] at this

@[expose] noncomputable def plusConj (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K)) :
    spinGroup (quadPlus n K) ≃* spinGroup (quadPlus n K) :=
  ((MonoidHom.ofInjective RootCentOmega.spinAction_quadPlus_injective).trans
    (((MulAut.conj g).subgroupMap (spinAction (quadPlus n K)).range).trans
      (MulEquiv.subgroupCongr (map_conj_range_spinAction hn hg)))).trans
    (MonoidHom.ofInjective RootCentOmega.spinAction_quadPlus_injective).symm

theorem spinAction_plusConj (hn : 3 ≤ n) {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (h : spinGroup (quadPlus n K)) :
    spinAction (quadPlus n K) (plusConj hn hg h) = g * spinAction (quadPlus n K) h * g⁻¹ := by
  have key := MonoidHom.ofInjective_apply RootCentOmega.spinAction_quadPlus_injective
    (x := plusConj hn hg h)
  rw [← key]
  simp only [plusConj, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply,
    MonoidHom.ofInjective_apply]

theorem plusRep_plusConj (hn : 3 ≤ n) {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (h : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K) :
    plusRep n K (plusConj hn hg h) v = g (plusRep n K h (g.symm v)) := by
  rw [plusRep_apply, spinAction_plusConj, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    plusRep_apply]
  rfl

theorem map_flagKernel_plusConj (hn : 3 ≤ n)
    {g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K))
    (F : ℕ → Submodule K (Fin n ⊕ Fin n → K)) :
    (flagKernel (plusRep n K) F).map (plusConj hn hg).toMonoidHom =
      flagKernel (plusRep n K) (fun k => (F k).map (g : _ →ₗ[K] _)) :=
  map_flagKernel_of_conj _ _ g (plusRep_plusConj hn hg) F

end Conj

variable (n K) in
@[expose] noncomputable def plusJ : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.sumComm (Fin n) (Fin n))

theorem plusJ_apply (v : Fin n ⊕ Fin n → K) (c : Fin n ⊕ Fin n) : plusJ n K v c = v c.swap :=
  rfl

theorem plusJ_mem : plusJ n K ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [quadPlus_apply, quadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [plusJ_apply, plusJ_apply, Sum.swap_inl, Sum.swap_inr, mul_comm]

theorem map_plusJ_stdFlag (ℓ : Fin n ⊕ Fin n → ℕ) (k : ℕ) :
    (stdFlag ℓ k).map (plusJ n K : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) =
      stdFlag (ℓ ∘ Sum.swap) k := by
  have h := map_stdFlag_comp_of_apply (K := K) (τ := Equiv.sumComm (Fin n) (Fin n))
    (f := (plusJ n K : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)))
    (fun c => Sum.swap_swap c) (fun v c => plusJ_apply v c) (ℓ ∘ Sum.swap) k
  have e : (ℓ ∘ Sum.swap) ∘ (Equiv.sumComm (Fin n) (Fin n)) = ℓ := by
    funext c
    simp
  rwa [e] at h

@[expose] noncomputable def plusU (ℓ : Fin n ⊕ Fin n → ℕ) : Subgroup (spinGroup (quadPlus n K)) :=
  flagKernel (plusRep n K) (stdFlag ℓ)

@[expose] noncomputable def plusP (ℓ : Fin n ⊕ Fin n → ℕ) : Subgroup (spinGroup (quadPlus n K)) :=
  flagStab (plusRep n K) (stdFlag ℓ)

variable [CharP K 2]

theorem plusU_comp_swap (hn : 3 ≤ n) (ℓ : Fin n ⊕ Fin n → ℕ) :
    plusU (K := K) (ℓ ∘ Sum.swap) = (plusU ℓ).map (plusConj hn plusJ_mem).toMonoidHom := by
  rw [plusU, plusU, map_flagKernel_plusConj]
  congr 1
  funext k
  exact (map_plusJ_stdFlag ℓ k).symm

theorem radicalTwo_plusU_comp_swap (hn : 3 ≤ n) {ℓ : Fin n ⊕ Fin n → ℕ}
    (h : GGRadicalTwo ⊤ (plusU (K := K) ℓ)) : GGRadicalTwo ⊤ (plusU (K := K) (ℓ ∘ Sum.swap)) := by
  rw [plusU_comp_swap hn]
  exact radicalTwo_map_mulEquiv _ h

theorem card_plusU_comp_swap (hn : 3 ≤ n) (ℓ : Fin n ⊕ Fin n → ℕ) :
    Nat.card (plusU (K := K) (ℓ ∘ Sum.swap)) = Nat.card (plusU (K := K) ℓ) := by
  rw [plusU_comp_swap hn]
  exact Subgroup.card_map_of_injective (plusConj hn plusJ_mem).injective

theorem plusU_comp_swap_inf_plusP {M : ℕ} {ℓ : Fin n ⊕ Fin n → ℕ} (hℓ : IsSpLevel M ℓ) :
    plusU (K := K) (ℓ ∘ Sum.swap) ⊓ plusP ℓ = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh => plusRep_injective ?_
  obtain ⟨hU, hP⟩ := Subgroup.mem_inf.mp hh
  have hbasis : ∀ a, plusRep n K h (Pi.single a (1 : K)) = (Pi.single a (1 : K) :
      Fin n ⊕ Fin n → K) := by
    intro a
    set w : Fin n ⊕ Fin n → K := plusRep n K h (Pi.single a (1 : K)) - Pi.single a (1 : K)
      with hw
    have h1 : w ∈ stdFlag (K := K) (ℓ ∘ Sum.swap) (ℓ a.swap) :=
      hU.2 _ _ (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
    have h2 : w ∈ stdFlag (K := K) ℓ (ℓ a + 1) :=
      sub_mem (flagStab_apply_mem _ hP (single_mem_stdFlag.mpr (Nat.lt_succ_self _)))
        (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
    have hw0 : w = 0 := by
      funext c
      by_cases hca : ℓ a < ℓ c
      · exact h2 c (by omega)
      · refine h1 c ?_
        have := hℓ.add_swap a
        have := hℓ.add_swap c
        simp only [Function.comp_apply]
        omega
    rw [hw, sub_eq_zero] at hw0
    exact hw0
  rw [map_one]
  exact (Pi.basisFun K (Fin n ⊕ Fin n)).ext fun a => by
    rw [Pi.basisFun_apply, hbasis, Module.End.one_apply]

end GGOppRadOmega

end CFSG.StandardType

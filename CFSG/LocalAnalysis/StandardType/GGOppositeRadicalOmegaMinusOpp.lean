module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusStd
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusOpp

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions GGOppRad GGOppRadSpU

theorem map_stdFlag_comp_of_apply' {ι K : Type*} [Field K] {f : (ι → K) →ₗ[K] (ι → K)}
    {τ : ι → ι} (hτ : ∀ c, τ (τ c) = c) (hf : ∀ v c, f v c = v (τ c))
    (ℓ : ι → ℕ) (k : ℕ) : (stdFlag (ℓ ∘ τ) k).map f = stdFlag (K := K) ℓ k := by
  refine le_antisymm ?_ fun w hw => ⟨fun c => w (τ c), fun a ha => ?_, funext fun c => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ c hc
    rw [hf]
    exact hv (τ c) (by simp only [Function.comp_apply, hτ]; exact hc)
  · exact hw (τ a) ha
  · rw [hf, hτ]

variable {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

section Conj

variable [CharP K 2]

omit [CharP K 2] in
include hirr in
theorem map_conj_range_spinAction_minus (hn : 4 ≤ n) {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) :
    (spinAction (quadMinus n K b c)).range.map ((MulAut.conj g : _ ≃* _) : _ →* _) =
      (spinAction (quadMinus n K b c)).range := by
  rw [range_spinAction_quadMinus hn hirr]
  refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_elementaryGroup hg hx
  · have := conj_mem_elementaryGroup (inv_mem hg) hx
    rwa [inv_inv] at this

@[expose] noncomputable def minusConj (hn : 4 ≤ n) {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) :
    spinGroup (quadMinus n K b c) ≃* spinGroup (quadMinus n K b c) :=
  ((MonoidHom.ofInjective (RootCentOmega.spinAction_quadMinus_injective hirr)).trans
    (((MulAut.conj g).subgroupMap (spinAction (quadMinus n K b c)).range).trans
      (MulEquiv.subgroupCongr (map_conj_range_spinAction_minus hirr hn hg)))).trans
    (MonoidHom.ofInjective (RootCentOmega.spinAction_quadMinus_injective hirr)).symm

theorem spinAction_minusConj (hn : 4 ≤ n) {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (h : spinGroup (quadMinus n K b c)) :
    spinAction (quadMinus n K b c) (minusConj hirr hn hg h) =
      g * spinAction (quadMinus n K b c) h * g⁻¹ := by
  have key := MonoidHom.ofInjective_apply (RootCentOmega.spinAction_quadMinus_injective hirr)
    (x := minusConj hirr hn hg h)
  rw [← key]
  simp only [minusConj, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply,
    MonoidHom.ofInjective_apply]

theorem minusRep_minusConj (hn : 4 ≤ n) {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (h : spinGroup (quadMinus n K b c)) (v : Vm n K) :
    minusRep n K b c (minusConj hirr hn hg h) v = g (minusRep n K b c h (g.symm v)) := by
  rw [minusRep_apply, spinAction_minusConj, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    minusRep_apply]
  rfl

theorem map_flagKernel_minusConj (hn : 4 ≤ n) {g : Vm n K ≃ₗ[K] Vm n K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c))
    (F : ℕ → Submodule K (Vm n K)) :
    (flagKernel (minusRep n K b c) F).map (minusConj hirr hn hg).toMonoidHom =
      flagKernel (minusRep n K b c) (fun k => (F k).map (g : _ →ₗ[K] _)) :=
  map_flagKernel_of_conj _ _ g (minusRep_minusConj hirr hn hg) F

end Conj

@[expose] def mprJ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  | .inl i => .inr (.inl i)
  | .inr (.inl i) => .inl i
  | .inr (.inr t) => .inr (.inr t)

omit [Finite K] in
theorem mprJ_mprJ (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) : mprJ (mprJ a) = a := by
  rcases a with i | i | t <;> rfl

variable (n K) in
@[expose] noncomputable def minusJ : Vm n K ≃ₗ[K] Vm n K :=
  LinearEquiv.funCongrLeft K K ⟨mprJ, mprJ, mprJ_mprJ, mprJ_mprJ⟩

omit [Finite K] in
theorem minusJ_apply (v : Vm n K) (a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :
    minusJ n K v a = v (mprJ a) :=
  rfl

omit [Finite K] in
theorem minusJ_mem : minusJ n K ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [quadMinus_apply, quadMinus_apply]
  simp only [minusJ_apply, mprJ]
  congr 1
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Finite K] in
theorem comp_mprJ_eq {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) : ℓ ∘ mprJ = ℓ ∘ mpr := by
  funext a
  rcases a with i | i | t
  · rfl
  · rfl
  · simp only [Function.comp_apply, mprJ, mpr]
    have h0 := hℓ.plane t
    have h1 := hℓ.plane t.rev
    omega

omit [Finite K] in
theorem map_minusJ_stdFlag {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) (k : ℕ) :
    (stdFlag ℓ k).map (minusJ n K : Vm n K →ₗ[K] Vm n K) = stdFlag (ℓ ∘ mpr) k := by
  have h := map_stdFlag_comp_of_apply' (K := K) (τ := mprJ)
    (f := (minusJ n K : Vm n K →ₗ[K] Vm n K)) mprJ_mprJ (fun v c => minusJ_apply v c)
    (ℓ ∘ mprJ) k
  have e : (ℓ ∘ mprJ) ∘ mprJ = ℓ := by
    funext a
    simp [mprJ_mprJ]
  rwa [e, comp_mprJ_eq hℓ] at h

omit [Finite K] in
theorem IsMinusLevel.comp_mpr {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) : IsMinusLevel M (ℓ ∘ mpr) := by
  refine ⟨fun a => ?_, ?_⟩
  · simp only [Function.comp_apply, mpr_mpr]
    have := hℓ.1 a
    omega
  · simp only [Function.comp_apply, mpr]
    have h0 := hℓ.plane 0
    have h1 := hℓ.plane 1
    change ℓ (.inr (.inr 1)) = ℓ (.inr (.inr 0))
    omega

@[expose] noncomputable def minusU (ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  flagKernel (minusRep n K b c) (stdFlag ℓ)

@[expose] noncomputable def minusP (ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  flagStab (minusRep n K b c) (stdFlag ℓ)

variable [CharP K 2]

theorem minusU_comp_mpr (hn : 4 ≤ n) {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) :
    minusU (b := b) (c := c) (ℓ ∘ mpr) =
      (minusU ℓ).map (minusConj hirr hn minusJ_mem).toMonoidHom := by
  rw [minusU, minusU, map_flagKernel_minusConj]
  congr 1
  funext k
  exact (map_minusJ_stdFlag hℓ k).symm

include hirr in
theorem radicalTwo_minusU_comp_mpr (hn : 4 ≤ n) {M : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ)
    (h : GGRadicalTwo ⊤ (minusU (b := b) (c := c) ℓ)) :
    GGRadicalTwo ⊤ (minusU (b := b) (c := c) (ℓ ∘ mpr)) := by
  rw [minusU_comp_mpr hirr hn hℓ]
  exact radicalTwo_map_mulEquiv _ h

include hirr in
theorem card_minusU_comp_mpr (hn : 4 ≤ n) {M : ℕ}
    {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ : IsMinusLevel M ℓ) :
    Nat.card (minusU (b := b) (c := c) (ℓ ∘ mpr)) = Nat.card (minusU (b := b) (c := c) ℓ) := by
  rw [minusU_comp_mpr hirr hn hℓ]
  exact Subgroup.card_map_of_injective (minusConj hirr hn minusJ_mem).injective

include hirr in
theorem minusU_comp_mpr_inf_minusP {M : ℕ} {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel M ℓ) :
    minusU (b := b) (c := c) (ℓ ∘ mpr) ⊓ minusP ℓ = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).mpr fun h hh => minusRep_injective hirr ?_
  obtain ⟨hU, hP⟩ := Subgroup.mem_inf.mp hh
  have hbasis : ∀ a, minusRep n K b c h (Pi.single a (1 : K)) = (Pi.single a (1 : K) : Vm n K) := by
    intro a
    set w : Vm n K := minusRep n K b c h (Pi.single a (1 : K)) - Pi.single a (1 : K) with hw
    have h1 : w ∈ stdFlag (K := K) (ℓ ∘ mpr) (ℓ (mpr a)) :=
      hU.2 _ _ (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
    have h2 : w ∈ stdFlag (K := K) ℓ (ℓ a + 1) :=
      sub_mem (flagStab_apply_mem _ hP (single_mem_stdFlag.mpr (Nat.lt_succ_self _)))
        (single_mem_stdFlag.mpr (Nat.lt_succ_self _))
    have hw0 : w = 0 := by
      funext c'
      by_cases hca : ℓ a < ℓ c'
      · exact h2 c' (by omega)
      · refine h1 c' ?_
        have := hℓ.1 a
        have := hℓ.1 c'
        simp only [Function.comp_apply]
        omega
    rw [hw, sub_eq_zero] at hw0
    exact hw0
  rw [map_one]
  exact (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).ext fun a => by
    rw [Pi.basisFun_apply, hbasis, Module.End.one_apply]

end GGOppRadOmega

end CFSG.StandardType

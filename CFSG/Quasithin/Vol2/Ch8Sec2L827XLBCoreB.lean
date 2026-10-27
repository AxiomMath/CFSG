module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBFourier
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBOrbit

public section

namespace CFSG.Quasithin.H13.L827X.LBCoreB

open CFSG.Quasithin.H13.L827X.LBFourier
open CFSG.Quasithin.H13.L827X.LBOrbit

@[expose] def dualAct {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    (e : E ≃ₗ[ZMod p] E) (f : Module.Dual (ZMod p) E) : Module.Dual (ZMod p) E :=
  f ∘ₗ (e.symm : E →ₗ[ZMod p] E)

private theorem dualAct_one {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    (f : Module.Dual (ZMod p) E) : dualAct (1 : E ≃ₗ[ZMod p] E) f = f :=
  LinearMap.ext fun _ => rfl

private theorem dualAct_mul {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    (g h : E ≃ₗ[ZMod p] E) (f : Module.Dual (ZMod p) E) :
    dualAct (g * h) f = dualAct g (dualAct h f) :=
  LinearMap.ext fun _ => rfl

@[reducible] private def dualMulAction {p : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    {Γ : Type*} [Group Γ] (σ : Γ →* (E ≃ₗ[ZMod p] E)) :
    MulAction Γ (Module.Dual (ZMod p) E) where
  smul γ f := dualAct (σ γ) f
  one_smul f := by
    show dualAct (σ 1) f = f
    rw [map_one, dualAct_one]
  mul_smul γ δ f := by
    show dualAct (σ (γ * δ)) f = dualAct (σ γ) (dualAct (σ δ) f)
    rw [map_mul, dualAct_mul]

private theorem chi_dualAct {p : ℕ} {F : Type*} [Field F] {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] (ζ : F) (g : E ≃ₗ[ZMod p] E) (f : Module.Dual (ZMod p) E) (x : E) :
    chi ζ (dualAct g f) (g x) = chi ζ f x := by
  simp [chi, dualAct]

private theorem chi_ne_one_of_ne_zero {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    (f : Module.Dual (ZMod p) E) {y : E} (hy : f y ≠ 0) : chi ζ f y ≠ 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro h
  have h' : ζ ^ (f y).val = 1 := h
  have hdvd : p ∣ (f y).val := (hζ.pow_eq_one_iff_dvd _).mp h'
  have hv : (f y).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
  exact hy ((ZMod.val_eq_zero _).mp hv)

private theorem idem_mul_rho_comm {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Fintype E]
    {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M)
    (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y) (f : Module.Dual (ZMod p) E) (y : E) :
    idem ζ ρ f * ρ y = chi ζ f y • idem ζ ρ f := by
  have hcomm : ∀ x : E, ρ x * ρ y = ρ y * ρ x := fun x => by
    rw [← hρadd, ← hρadd, add_comm x y]
  have hc : idem ζ ρ f * ρ y = ρ y * idem ζ ρ f := by
    rw [idem_eq_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hcomm x]
  rw [hc, rho_mul_idem hζ ρ hρadd f y]

private theorem idem_zero_eq_zero_of_fixed {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    [Fintype E] {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M)
    (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y)
    (hC : ∀ m : M, (∀ x : E, ρ x m = m) → m = 0) :
    idem ζ ρ (0 : Module.Dual (ZMod p) E) = 0 := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.zero_apply]
  apply hC
  intro x
  have h := congrArg (fun L : Module.End F M => L v)
    (rho_mul_idem hζ ρ hρadd (0 : Module.Dual (ZMod p) E) x)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, chi_dual_zero, one_smul] at h
  exact h

private theorem idem_apply_eq_zero_of_fixed {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
    [Fintype E] {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M)
    (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y) (f : Module.Dual (ZMod p) E) (y : E) (w : M)
    (hw : ρ y w = w) (hf : chi ζ f y ≠ 1) : idem ζ ρ f w = 0 := by
  have h := congrArg (fun L : Module.End F M => L w) (idem_mul_rho_comm hζ ρ hρadd f y)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hw] at h
  have h2 : (1 - chi ζ f y) • idem ζ ρ f w = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hf))

private theorem ne_zero_iff_one_le_finrank_range_end {F : Type*} [Field F] {M : Type*}
    [AddCommGroup M] [Module F M] [FiniteDimensional F M] (T : Module.End F M) :
    T ≠ 0 ↔ 1 ≤ Module.finrank F (LinearMap.range T) := by
  rw [Submodule.one_le_finrank_iff, ne_eq, ne_eq, LinearMap.range_eq_bot]

private theorem idem_conj {p : ℕ} {F : Type*} [Field F] (ζ : F) {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] [Fintype E] {Γ : Type*} [Group Γ] (σ : Γ →* (E ≃ₗ[ZMod p] E))
    {M : Type*} [AddCommGroup M] [Module F M] (τ : Γ →* (M ≃ₗ[F] M))
    (ρ : E → Module.End F M)
    (hcompat : ∀ (γ : Γ) (x : E),
      (τ γ : Module.End F M) * ρ x = ρ (σ γ x) * (τ γ : Module.End F M))
    (γ : Γ) (f : Module.Dual (ZMod p) E) :
    (τ γ : Module.End F M) * idem ζ ρ f
      = idem ζ ρ (dualAct (σ γ) f) * (τ γ : Module.End F M) := by
  have hsum : ∑ x : E, (chi ζ f x)⁻¹ • ρ (σ γ x)
      = ∑ z : E, (chi ζ (dualAct (σ γ) f) z)⁻¹ • ρ z := by
    refine Fintype.sum_equiv (σ γ).toEquiv _ _ fun x => ?_
    show (chi ζ f x)⁻¹ • ρ (σ γ x) = (chi ζ (dualAct (σ γ) f) (σ γ x))⁻¹ • ρ (σ γ x)
    rw [chi_dualAct]
  have key : ∑ x : E, (chi ζ f x)⁻¹ • (ρ (σ γ x) * (τ γ : Module.End F M))
      = ∑ z : E, (chi ζ (dualAct (σ γ) f) z)⁻¹ • (ρ z * (τ γ : Module.End F M)) := by
    simp only [← smul_mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
  simp only [idem_eq_sum]
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp only [mul_smul_comm, smul_mul_assoc, hcompat]
  exact key

private theorem finrank_range_idem_dualAct {p : ℕ} {F : Type*} [Field F] (ζ : F)
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Fintype E] {Γ : Type*} [Group Γ]
    (σ : Γ →* (E ≃ₗ[ZMod p] E)) {M : Type*} [AddCommGroup M] [Module F M]
    (τ : Γ →* (M ≃ₗ[F] M)) (ρ : E → Module.End F M)
    (hcompat : ∀ (γ : Γ) (x : E),
      (τ γ : Module.End F M) * ρ x = ρ (σ γ x) * (τ γ : Module.End F M))
    (γ : Γ) (f : Module.Dual (ZMod p) E) :
    Module.finrank F (LinearMap.range (idem ζ ρ (dualAct (σ γ) f)))
      = Module.finrank F (LinearMap.range (idem ζ ρ f)) := by
  have hconj := idem_conj ζ σ τ ρ hcompat γ f
  have hsurj : LinearMap.range ((τ γ : Module.End F M)) = ⊤ :=
    LinearMap.range_eq_top.mpr (τ γ).surjective
  have hA : LinearMap.range ((τ γ : Module.End F M) * idem ζ ρ f)
      = (LinearMap.range (idem ζ ρ f)).map (τ γ : Module.End F M) := by
    rw [Module.End.mul_eq_comp, LinearMap.range_comp]
  have hB : LinearMap.range (idem ζ ρ (dualAct (σ γ) f) * (τ γ : Module.End F M))
      = LinearMap.range (idem ζ ρ (dualAct (σ γ) f)) := by
    rw [Module.End.mul_eq_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]
  have hrange : LinearMap.range (idem ζ ρ (dualAct (σ γ) f))
      = (LinearMap.range (idem ζ ρ f)).map (τ γ : Module.End F M) := by
    rw [← hA, hconj, hB]
  rw [hrange]
  exact LinearEquiv.finrank_map_eq (τ γ) _

private theorem finrank_iSup_range_idem_eq {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hpF : (p : F) ≠ 0) {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] [Fintype E] (hE : Module.finrank (ZMod p) E = 2)
    {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : E → Module.End F M) (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y)
    (T : Finset (Module.Dual (ZMod p) E)) :
    Module.finrank F (⨆ f ∈ T, LinearMap.range (idem ζ ρ f) : Submodule F M)
      = ∑ f ∈ T, Module.finrank F (LinearMap.range (idem ζ ρ f)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert g T hg ih =>
    have hW : (⨆ f ∈ T, LinearMap.range (idem ζ ρ f)) ≤ LinearMap.ker (idem ζ ρ g) := by
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨u, rfl⟩
      have hfg : g ≠ f := fun h => hg (h ▸ hf)
      have hm : idem ζ ρ g * idem ζ ρ f = 0 := by
        rw [idem_mul_idem hζ hpF hE ρ hρadd g f]
        simp [hfg]
      have hu := congrArg (fun L : Module.End F M => L u) hm
      simp only [Module.End.mul_apply, LinearMap.zero_apply] at hu
      exact hu
    have hdisj : LinearMap.range (idem ζ ρ g) ⊓ (⨆ f ∈ T, LinearMap.range (idem ζ ρ f)) = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨⟨v, rfl⟩, hwW⟩
      have h0 : idem ζ ρ g (idem ζ ρ g v) = 0 := hW hwW
      have hsq : idem ζ ρ g * idem ζ ρ g = idem ζ ρ g := by
        rw [idem_mul_idem hζ hpF hE ρ hρadd g g]
        simp
      have h1 : idem ζ ρ g (idem ζ ρ g v) = idem ζ ρ g v := by
        have := congrArg (fun L : Module.End F M => L v) hsq
        simpa only [Module.End.mul_apply] using this
      rw [h1] at h0
      rw [Submodule.mem_bot]
      exact h0
    have hsplit := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (idem ζ ρ g))
      (⨆ f ∈ T, LinearMap.range (idem ζ ρ f))
    rw [hdisj, finrank_bot, add_zero] at hsplit
    rw [Finset.iSup_insert, Finset.sum_insert hg, ← ih]
    exact hsplit

private theorem ker_sub_le_iSup_range_idem {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hpF : (p : F) ≠ 0) {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] [Fintype E] (hE : Module.finrank (ZMod p) E = 2)
    {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : E → Module.End F M) (hρ0 : ρ 0 = 1) (y : E) (T : Finset (Module.Dual (ZMod p) E))
    (hT : ∀ f, f ∉ T → ∀ w : M, ρ y w = w → idem ζ ρ f w = 0) :
    LinearMap.ker (ρ y - 1) ≤ ⨆ f ∈ T, LinearMap.range (idem ζ ρ f) := by
  classical
  intro w hw
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
  have hsumw : ∑ f : Module.Dual (ZMod p) E, idem ζ ρ f w = w := by
    have h := congrArg (fun L : Module.End F M => L w) (sum_idem hζ hpF hE ρ hρ0)
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using h
  have hsubs : ∑ f ∈ T, idem ζ ρ f w = w :=
    (Finset.sum_subset (Finset.subset_univ T) fun f _ hf => hT f hf w hw).trans hsumw
  rw [← hsubs]
  exact Submodule.sum_mem _ fun f hf =>
    Submodule.mem_iSup_of_mem f (Submodule.mem_iSup_of_mem hf (LinearMap.mem_range_self _ _))

theorem core_sixteen_le {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (hpF : (p : F) ≠ 0)
    {E : Type*} [AddCommGroup E] [Module (ZMod p) E] [Fintype E]
    (hE : Module.finrank (ZMod p) E = 2)
    {Γ : Type*} [Group Γ] [Finite Γ]
    (σ : Γ →* (E ≃ₗ[ZMod p] E))
    {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M] [Nontrivial M]
    (τ : Γ →* (M ≃ₗ[F] M)) (ρ : E → Module.End F M) (hρ0 : ρ 0 = 1)
    (hρadd : ∀ x y, ρ (x + y) = ρ x * ρ y)
    (hcompat : ∀ (γ : Γ) (x : E),
      (τ γ : Module.End F M) * ρ x = ρ (σ γ x) * (τ γ : Module.End F M))
    (hC : ∀ m : M, (∀ x : E, ρ x m = m) → m = 0)
    (hO2 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 →
      24 ≤ Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    (hO3 : ∀ f : Module.Dual (ZMod p) E, f ≠ 0 → ∀ y : E, y ≠ 0 →
      3 * Set.ncard ({g | ∃ γ : Γ, dualAct (σ γ) f = g} ∩ {g | g y = 0}) ≤
        Set.ncard {g | ∃ γ : Γ, dualAct (σ γ) f = g})
    {y : E} (hy : y ≠ 0) :
    16 ≤ Module.finrank F (LinearMap.range (ρ y - 1)) := by
  classical
  letI : MulAction Γ (Module.Dual (ZMod p) E) := dualMulAction σ
  have horb : ∀ ω : Module.Dual (ZMod p) E,
      MulAction.orbit Γ ω = {g | ∃ γ : Γ, dualAct (σ γ) ω = g} := by
    intro ω
    ext g
    exact MulAction.mem_orbit_iff
  obtain ⟨S, hmemS⟩ : ∃ S : Finset (Module.Dual (ZMod p) E),
      ∀ f, f ∈ S ↔ idem ζ ρ f ≠ 0 :=
    ⟨Finset.univ.filter (fun f => idem ζ ρ f ≠ 0), fun f => by simp⟩
  obtain ⟨c, hc_def⟩ : ∃ c : Module.Dual (ZMod p) E → ℕ,
      ∀ f, c f = Module.finrank F (LinearMap.range (idem ζ ρ f)) :=
    ⟨fun f => Module.finrank F (LinearMap.range (idem ζ ρ f)), fun f => rfl⟩
  have hmemS' : ∀ f, f ∈ S ↔ 1 ≤ c f := fun f => by
    rw [hmemS f, hc_def f]
    exact ne_zero_iff_one_le_finrank_range_end _
  have he0 : idem ζ ρ (0 : Module.Dual (ZMod p) E) = 0 :=
    idem_zero_eq_zero_of_fixed hζ ρ hρadd hC
  have hS0 : (0 : Module.Dual (ZMod p) E) ∉ S := by
    rw [hmemS, he0]
    simp
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have h0 : ∑ f : Module.Dual (ZMod p) E, idem ζ ρ f = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      by_contra hf
      have hfS : f ∈ S := (hmemS f).mpr hf
      rw [hne] at hfS
      simp at hfS
    rw [sum_idem hζ hpF hE ρ hρ0] at h0
    exact one_ne_zero h0
  have hcinv : ∀ (γ : Γ) (f : Module.Dual (ZMod p) E), c (dualAct (σ γ) f) = c f := by
    intro γ f
    rw [hc_def, hc_def]
    exact finrank_range_idem_dualAct ζ σ τ ρ hcompat γ f
  have hc' : ∀ (γ : Γ) (ω : Module.Dual (ZMod p) E), c (γ • ω) = c ω :=
    fun γ ω => hcinv γ ω
  have hSinv : ∀ (γ : Γ), ∀ ω ∈ S, γ • ω ∈ S := fun γ ω hω => by
    rw [hmemS'] at hω ⊢
    rw [hc' γ ω]
    exact hω
  have hO3' : ∀ ω ∈ S,
      3 * (MulAction.orbit Γ ω ∩ {g : Module.Dual (ZMod p) E | g y = 0}).ncard
        ≤ (MulAction.orbit Γ ω).ncard := by
    intro ω hω
    have hω0 : ω ≠ 0 := by
      rintro rfl
      exact hS0 hω
    rw [horb ω]
    exact hO3 ω hω0 y hy
  have hW := orbit_weight_third S hSinv c hc' {g : Module.Dual (ZMod p) E | g y = 0} hO3'
  have hker : Module.finrank F (LinearMap.ker (ρ y - 1))
      ≤ ∑ f ∈ S.filter (· ∈ {g : Module.Dual (ZMod p) E | g y = 0}), c f := by
    have hT : ∀ f, f ∉ S.filter (· ∈ {g : Module.Dual (ZMod p) E | g y = 0}) →
        ∀ w : M, ρ y w = w → idem ζ ρ f w = 0 := by
      intro f hf w hw
      by_cases hfS : f ∈ S
      · have hfy : f y ≠ 0 := by
          intro h0
          exact hf (Finset.mem_filter.mpr ⟨hfS, h0⟩)
        exact idem_apply_eq_zero_of_fixed hζ ρ hρadd f y w hw
          (chi_ne_one_of_ne_zero hζ f hfy)
      · have h0 : idem ζ ρ f = 0 := by
          by_contra h
          exact hfS ((hmemS f).mpr h)
        rw [h0, LinearMap.zero_apply]
    calc Module.finrank F (LinearMap.ker (ρ y - 1))
        ≤ Module.finrank F (⨆ f ∈ S.filter (· ∈ {g : Module.Dual (ZMod p) E | g y = 0}),
            LinearMap.range (idem ζ ρ f) : Submodule F M) :=
          Submodule.finrank_mono (ker_sub_le_iSup_range_idem hζ hpF hE ρ hρ0 y _ hT)
      _ = ∑ f ∈ S.filter (· ∈ {g : Module.Dual (ZMod p) E | g y = 0}),
            Module.finrank F (LinearMap.range (idem ζ ρ f)) :=
          finrank_iSup_range_idem_eq hζ hpF hE ρ hρadd _
      _ = ∑ f ∈ S.filter (· ∈ {g : Module.Dual (ZMod p) E | g y = 0}), c f :=
          Finset.sum_congr rfl fun f _ => (hc_def f).symm
  have hsumS : S.card ≤ ∑ f ∈ S, c f := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f hf => (hmemS' f).mp hf
  have hsumle : ∑ f ∈ S, c f ≤ Module.finrank F M := by
    have hcs : ∑ f ∈ S, c f = ∑ f ∈ S, Module.finrank F (LinearMap.range (idem ζ ρ f)) :=
      Finset.sum_congr rfl fun f _ => hc_def f
    rw [hcs, ← finrank_iSup_range_idem_eq hζ hpF hE ρ hρadd S]
    exact Submodule.finrank_le _
  have h24 : 24 ≤ S.card := by
    obtain ⟨f, hf⟩ := hSne
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact hS0 hf
    have hsub : ∀ γ : Γ, ∀ ω ∈ (S : Set (Module.Dual (ZMod p) E)),
        γ • ω ∈ (S : Set (Module.Dual (ZMod p) E)) := fun γ ω hω => by
      rw [Finset.mem_coe] at hω ⊢
      exact hSinv γ ω hω
    have h2 := card_le_of_mem_orbit_subset (S : Set (Module.Dual (ZMod p) E)) hsub
      (Finset.mem_coe.mpr hf)
    rw [Set.ncard_coe_finset, horb f] at h2
    exact (hO2 f hf0).trans h2
  have hrk := LinearMap.finrank_range_add_finrank_ker (ρ y - 1)
  omega

end CFSG.Quasithin.H13.L827X.LBCoreB

end

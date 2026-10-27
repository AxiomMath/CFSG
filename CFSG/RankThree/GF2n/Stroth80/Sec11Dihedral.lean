module

public import CFSG.RankThree.GF2n.Stroth80.Sec11LinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n.Tim79

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {γ : G → K}

theorem exists_mu_of_dihedral (M₀ : QuadModel QF V K γ)
    {D T : M₀.E ≃ₗ[K] M₀.E} (hD : ∀ e, M₀.Qf (D e) = M₀.Qf e) (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hD2 : ∀ e, D (D e) = e) (hDT : ∀ e, D (T e) = T.symm (D e))
    {m : ℕ} (hm : Odd m) (hTm : (T : M₀.E →ₗ[K] M₀.E) ^ m = 1)
    (hR : Module.finrank K (LinearMap.range ((D : M₀.E →ₗ[K] M₀.E) - 1)) ≤ 2)
    (hsing : ∀ v ∈ LinearMap.range ((D : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0) :
    ∃ μ : K, ∀ e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1),
      T (T (T (T e) + μ • T e + e)) + μ • T (T (T e) + μ • T e + e) +
        (T (T e) + μ • T e + e) = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2m : ∀ v : M₀.E, v + v = 0 := fun v => by rw [← two_smul K v, h2, zero_smul]
  have hBsymm : ∀ u v : M₀.E, M₀.B u v = M₀.B v u := fun u v => by
    rw [QuadModel.B_comm u v, CharTwo.neg_eq]
  have hTs : ∀ e, M₀.Qf (T.symm e) = M₀.Qf e := fun e => by
    have := hT (T.symm e)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hBT : ∀ u v, M₀.B (T u) (T v) = M₀.B u v := fun u v =>
    QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) hT u v
  have hBTs : ∀ u v, M₀.B (T.symm u) (T.symm v) = M₀.B u v := fun u v =>
    QuadModel.B_iso (T := (T.symm : M₀.E →ₗ[K] M₀.E)) hTs u v
  have hDTs : ∀ e, D (T.symm e) = T (D e) := fun e => by
    have h := hDT (T.symm e)
    rw [LinearEquiv.apply_symm_apply] at h
    have h' := congrArg T h
    rw [LinearEquiv.apply_symm_apply] at h'
    exact h'.symm
  set E₂ : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) with hE₂def
  have hE₂ : ∀ v, v ∈ E₂ ↔ ∃ e, T e - e = v := fun v => by
    simp [hE₂def, LinearMap.mem_range]
  have hE₂T : ∀ v ∈ E₂, T v ∈ E₂ := by
    intro v hv
    obtain ⟨e, rfl⟩ := (hE₂ v).mp hv
    exact (hE₂ _).mpr ⟨T e, by simp [map_sub]⟩
  have hE₂Ts : ∀ v ∈ E₂, T.symm v ∈ E₂ := by
    intro v hv
    obtain ⟨e, rfl⟩ := (hE₂ v).mp hv
    refine (hE₂ _).mpr ⟨T.symm e, ?_⟩
    simp only [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  have hE₂D : ∀ v ∈ E₂, D v ∈ E₂ := by
    intro v hv
    obtain ⟨e, rfl⟩ := (hE₂ v).mp hv
    refine (hE₂ _).mpr ⟨- T.symm (D e), ?_⟩
    have : D (T e - e) = T.symm (D e) - D e := by rw [map_sub, hDT]
    rw [this]
    simp only [map_neg, LinearEquiv.apply_symm_apply]
    abel
  have hmem2 : ∀ v ∈ E₂, ∃ w ∈ E₂, T w - w = v := by
    intro v hv
    have := range_sub_one_le_map_range hm hTm hv
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp this
    exact ⟨w, hw, by simpa using hwv⟩
  have hE₂E₁ : ∀ v ∈ E₂, ∀ z, T z = z → M₀.B v z = 0 := by
    intro v hv z hz
    obtain ⟨e, rfl⟩ := (hE₂ v).mp hv
    have h1 := hBT e z
    rw [hz] at h1
    rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  have hdecomp : ∀ e, ∃ e₁ e₂, T e₁ = e₁ ∧ e₂ ∈ E₂ ∧ e = e₁ + e₂ := by
    intro e
    have he : e ∈ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) ⊔ E₂ := by
      rw [hE₂def, ker_sup_range_eq_top_of_pow_eq_one hm hTm]
      trivial
    obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp he
    refine ⟨k, r, ?_, hr, rfl⟩
    have := LinearMap.mem_ker.mp hk
    simpa [sub_eq_zero] using this
  set sL : M₀.E →ₗ[K] M₀.E := (T : M₀.E →ₗ[K] M₀.E) + (T.symm : M₀.E →ₗ[K] M₀.E) with hsLdef
  have hsL : ∀ e, sL e = T e + T.symm e := fun e => by simp [hsLdef]
  have hsT : ∀ e, T (sL e) = sL (T e) := fun e => by
    rw [hsL, hsL, map_add, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, add_comm]
  have hsTs : ∀ e, T.symm (sL e) = sL (T.symm e) := fun e => by
    rw [hsL, hsL, map_add, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, add_comm]
  have hsD : ∀ e, D (sL e) = sL (D e) := fun e => by
    rw [hsL, hsL, map_add, hDT, hDTs, add_comm]
  have hE₂s : ∀ v ∈ E₂, sL v ∈ E₂ := fun v hv => by
    rw [hsL]
    exact E₂.add_mem (hE₂T v hv) (hE₂Ts v hv)
  have hE₂sE₂ : ∀ v ∈ E₂, ∃ w ∈ E₂, sL w = v := by
    intro v hv
    obtain ⟨w₁, hw₁, rfl⟩ := hmem2 v hv
    obtain ⟨u, hu, rfl⟩ := hmem2 w₁ hw₁
    refine ⟨T u, hE₂T u hu, ?_⟩
    rw [hsL, LinearEquiv.symm_apply_apply, map_sub]
    linear_combination (norm := module) (h2m (T u)) 
  set Nl : M₀.E →ₗ[K] M₀.E := (D : M₀.E →ₗ[K] M₀.E) - 1 with hNldef
  have hNl : ∀ e, Nl e = D e - e := fun e => by simp [hNldef]
  set P : Submodule K M₀.E := E₂.map Nl with hPdef
  have hP : ∀ v, v ∈ P ↔ ∃ e ∈ E₂, D e - e = v := fun v => by
    constructor
    · rintro hv
      obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hv
      exact ⟨e, he, (hNl e).symm ▸ rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact Submodule.mem_map.mpr ⟨e, he, hNl e⟩
  have hPle : P ≤ LinearMap.range ((D : M₀.E →ₗ[K] M₀.E) - 1) := LinearMap.map_le_range
  have hPsing : ∀ v ∈ P, M₀.Qf v = 0 := fun v hv => hsing v (hPle hv)
  have hPiso : ∀ x ∈ P, ∀ y ∈ P, M₀.B x y = 0 := by
    intro x hx y hy
    have h1 := M₀.Qf_add x y
    rw [hPsing _ (P.add_mem hx hy), hPsing x hx, hPsing y hy] at h1
    linear_combination -h1
  have hPE₂ : ∀ v ∈ P, v ∈ E₂ := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := (hP v).mp hv
    exact E₂.sub_mem (hE₂D e he) he
  have hsP : ∀ x ∈ P, sL x ∈ P := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hP x).mp hx
    refine (hP _).mpr ⟨sL e, hE₂s e he, ?_⟩
    rw [map_sub, hsD]
  have hdecE₂ : ∀ v ∈ E₂, ∃ p ∈ P, ∃ q ∈ P, v = p + T.symm q := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hE₂sE₂ v hv
    refine ⟨D (T w) - T w, (hP _).mpr ⟨T w, hE₂T w hw, rfl⟩, D w - w,
      (hP _).mpr ⟨w, hw, rfl⟩, ?_⟩
    rw [hsL, hDT, map_sub]
    linear_combination (norm := module) h2m (T w) + h2m (T.symm w) - h2m (T.symm (D w))
  have hadj1 : ∀ u v, M₀.B (T u) v = M₀.B u (T.symm v) := fun u v => by
    have := hBT u (T.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  have hadj2 : ∀ u v, M₀.B (T.symm u) v = M₀.B u (T v) := fun u v => by
    have := hBTs u (T v)
    rw [LinearEquiv.symm_apply_apply] at this
    exact this
  have hTsplit : ∀ y, T y = sL y + T.symm y := fun y => by
    rw [hsL]
    linear_combination (norm := module) -h2m (T.symm y)
  let β : P →ₗ[K] P →ₗ[K] K :=
    M₀.B.compl₁₂ P.subtype ((T.symm : M₀.E →ₗ[K] M₀.E) ∘ₗ P.subtype)
  have hβ : ∀ x y : P, β x y = M₀.B (x : M₀.E) (T.symm (y : M₀.E)) := fun x y => rfl
  let σ : P →ₗ[K] P := LinearMap.restrict sL hsP
  have hσ : ∀ x : P, ((σ x : P) : M₀.E) = sL (x : M₀.E) := fun x => rfl
  have hsymmβ : ∀ x y : P, β x y = β y x := by
    intro x y
    rw [hβ, hβ]
    have h1 : M₀.B (y : M₀.E) (T.symm (x : M₀.E)) = M₀.B (T (y : M₀.E)) (x : M₀.E) := by
      have := hBT (y : M₀.E) (T.symm (x : M₀.E))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, hBsymm (T (y : M₀.E)) (x : M₀.E), hTsplit (y : M₀.E), map_add,
      hPiso x x.2 (sL (y : M₀.E)) (hsP y y.2), zero_add]
  have hndβ : ∀ x : P, (∀ y : P, β x y = 0) → x = 0 := by
    intro x hx
    have hxE₂ : (x : M₀.E) ∈ E₂ := hPE₂ x x.2
    have hB0 : ∀ z, M₀.B (x : M₀.E) z = 0 := by
      intro z
      obtain ⟨z₁, z₂, hz₁, hz₂, rfl⟩ := hdecomp z
      obtain ⟨p, hp, q, hq, rfl⟩ := hdecE₂ z₂ hz₂
      have hq0 := hx ⟨q, hq⟩
      rw [hβ] at hq0
      simp only at hq0
      rw [map_add, map_add, hE₂E₁ x hxE₂ z₁ hz₁, hPiso x x.2 p hp, hq0]
      ring
    exact Subtype.ext (by simpa using M₀.nondeg _ hB0)
  have hsaβ : ∀ x y : P, β (σ x) y = β x (σ y) := by
    intro x y
    rw [hβ, hβ, hσ, hσ, hsL (x : M₀.E), hsL (y : M₀.E)]
    simp only [map_add, LinearMap.add_apply, hadj1, hadj2, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
    abel
  have hzβ : ∀ x : P, β (σ x) x = 0 := by
    intro x
    show M₀.B (sL (x : M₀.E)) (T.symm (x : M₀.E)) = 0
    have h1 := hT (x : M₀.E)
    rw [hTsplit (x : M₀.E), M₀.Qf_add, hPsing _ (hsP x x.2), hTs, hPsing x x.2] at h1
    linear_combination h1
  have hfinP : Module.finrank K P ≤ 2 := (Submodule.finrank_mono hPle).trans hR
  obtain ⟨μ, hμ⟩ := exists_sq_scalar_of_alt_selfadjoint hfinP β hsymmβ hndβ σ hsaβ hzβ
  have hμ' : ∀ x ∈ P, sL (sL x) = (μ * μ) • x := fun x hx => by
    exact congrArg Subtype.val (hμ ⟨x, hx⟩)
  refine ⟨μ, fun e he => ?_⟩
  have hY : ∀ y, T (T y) + μ • T y + y = sL (T y) + μ • T y := fun y => by
    rw [hsL, LinearEquiv.symm_apply_apply]
    abel
  have hkey : ∀ u ∈ E₂, sL (sL u) + (μ * μ) • u = 0 := by
    intro u hu
    obtain ⟨p, hp, q, hq, rfl⟩ := hdecE₂ u hu
    have hsplit : sL (sL (p + T.symm q)) = sL (sL p) + T.symm (sL (sL q)) := by
      simp only [map_add, ← hsTs]
    rw [hsplit, hμ' p hp, hμ' q hq, map_smul, smul_add]
    linear_combination (norm := module) h2m ((μ * μ) • p) + h2m ((μ * μ) • T.symm q)
  have hu : T (T e) ∈ E₂ := hE₂T _ (hE₂T e he)
  have hy : T (T e) + μ • T e + e = sL (T e) + μ • T e := hY e
  have hTy : T (T (T e) + μ • T e + e) = sL (T (T e)) + μ • T (T e) := by
    rw [hy, map_add, map_smul, hsT]
  rw [hY (T (T e) + μ • T e + e), hTy, map_add, map_smul]
  have h5 := hkey _ hu
  linear_combination (norm := module) h5 + h2m (μ • sL (T (T e)))

theorem pow_card_sq_sub_one_of_dihedral (M₀ : QuadModel QF V K γ)
    {D T : M₀.E ≃ₗ[K] M₀.E} (hD : ∀ e, M₀.Qf (D e) = M₀.Qf e) (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hD2 : ∀ e, D (D e) = e) (hDT : ∀ e, D (T e) = T.symm (D e))
    {m : ℕ} (hm : Odd m) (hTm : (T : M₀.E →ₗ[K] M₀.E) ^ m = 1)
    (hR : Module.finrank K (LinearMap.range ((D : M₀.E →ₗ[K] M₀.E) - 1)) ≤ 2)
    (hsing : ∀ v ∈ LinearMap.range ((D : M₀.E →ₗ[K] M₀.E) - 1), M₀.Qf v = 0) :
    (T : M₀.E →ₗ[K] M₀.E) ^ (Nat.card K ^ 2 - 1) = 1 := by
  obtain ⟨μ, hμ⟩ := exists_mu_of_dihedral M₀ hD hT hD2 hDT hm hTm hR hsing
  set E₂ : Submodule K M₀.E := LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) with hE₂def
  have hTE₂ : ∀ v ∈ E₂, (T : M₀.E →ₗ[K] M₀.E) v ∈ E₂ := by
    intro v hv
    obtain ⟨e, rfl⟩ := hv
    exact ⟨T e, by simp [map_sub]⟩
  let T₂ : E₂ →ₗ[K] E₂ := LinearMap.restrict (T : M₀.E →ₗ[K] M₀.E) hTE₂
  have hcoe : ∀ (k : ℕ) (v : E₂), ((T₂ ^ k) v : M₀.E) = (T ^ k : M₀.E ≃ₗ[K] M₀.E) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, LinearEquiv.mul_apply]
      exact ih (T₂ v)
  have hT₂m : T₂ ^ m = 1 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hcoe]
    have h1 : (T ^ m : M₀.E ≃ₗ[K] M₀.E) = 1 := by
      refine LinearEquiv.ext fun e => ?_
      have := congrArg (fun f : M₀.E →ₗ[K] M₀.E => f e) hTm
      simp only [Module.End.coe_pow] at this
      rw [LinearEquiv.coe_pow]
      exact this
    rw [h1]
    rfl
  have hsq : (T₂ * T₂ + μ • T₂ + 1) * (T₂ * T₂ + μ • T₂ + 1) = 0 := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have h := hμ (v : M₀.E) v.2
    simpa [T₂] using h
  have hzero : T₂ * T₂ + μ • T₂ + 1 = 0 := eq_zero_of_sq_eq_zero_of_pow_eq_one hm hT₂m hsq
  have hpow : T₂ ^ (Nat.card K ^ 2 - 1) = 1 := pow_card_sq_sub_one_eq_one hm hT₂m hzero
  refine LinearMap.ext fun e => ?_
  have he : e ∈ LinearMap.ker ((T : M₀.E →ₗ[K] M₀.E) - 1) ⊔ E₂ := by
    rw [hE₂def, ker_sup_range_eq_top_of_pow_eq_one hm hTm]
    trivial
  obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp he
  have hk' : T k = k := by
    have := LinearMap.mem_ker.mp hk
    simpa [sub_eq_zero] using this
  have hkpow : ∀ j : ℕ, ((T : M₀.E →ₗ[K] M₀.E) ^ j) k = k := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      rw [show (T : M₀.E →ₗ[K] M₀.E) k = k from hk']
      exact ih
  have hrpow : ((T : M₀.E →ₗ[K] M₀.E) ^ (Nat.card K ^ 2 - 1)) r = r := by
    have h1 := congrArg (fun f : E₂ →ₗ[K] E₂ => ((f ⟨r, hr⟩ : E₂) : M₀.E)) hpow
    simp only [hcoe, Module.End.one_apply] at h1
    rw [Module.End.coe_pow]
    have h2 : ((T ^ (Nat.card K ^ 2 - 1) : M₀.E ≃ₗ[K] M₀.E)) r = r := h1
    rw [LinearEquiv.coe_pow] at h2
    exact h2
  rw [map_add, hkpow, hrpow]
  rfl

end CFSG.RankThree.GF2n.Stroth80

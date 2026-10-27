module

public import CFSG.LocalAnalysis.StandardType.GGQ2HypLin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V ι : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2Sub_two_smul (w : V) : (2 : ZMod 3) • w = -w := by
  rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul]

private theorem ggQ2Sub_s_apply_apply (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (i : ι) (v : V) :
    s i (s i v) = v := by
  have h : s i = Module.reflection (hαc i) := by
    ext w
    rw [hs i w, Module.reflection_apply]
  rw [h]
  exact Module.involutive_reflection (hαc i) v

private theorem ggQ2Sub_dual_eq_zero_on (U : Submodule (ZMod 3) V) {c₀ : V}
    (φ : Module.Dual (ZMod 3) V) (hφ : φ c₀ = 2)
    (hU : ∀ u ∈ U, Module.reflection hφ u ∈ U) (hc₀ : c₀ ∉ U) :
    ∀ u ∈ U, φ u = 0 := by
  intro u hu
  have h1 : Module.reflection hφ u ∈ U := hU u hu
  rw [Module.reflection_apply] at h1
  have h2 : φ u • c₀ ∈ U := by
    have h3 : φ u • c₀ = u - Module.reflection hφ u := by
      rw [Module.reflection_apply]
      abel
    rw [h3]
    exact U.sub_mem hu h1
  by_contra hne
  apply hc₀
  have h4 : c₀ = (φ u)⁻¹ • (φ u • c₀) := by
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [h4]
  exact U.smul_mem _ h2

private theorem ggQ2Sub_centre_mem_span (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hTF : TransvectionFree A) (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U)
    (hRU : ∀ r ∈ reflGp A, ∀ u ∈ U, r u ∈ U)
    {c₀ : V} {φ : Module.Dual (ZMod 3) V} (hφ : φ c₀ = 2)
    (ht : Module.reflection hφ ∈ A) (hc₀ : c₀ ∉ U) :
    c₀ ∈ Submodule.span (ZMod 3) {x} := by
  have htR : Module.reflection hφ ∈ reflGp A :=
    Subgroup.subset_closure ⟨ht, c₀, φ, hφ, rfl⟩
  have hφU : ∀ u ∈ U, φ u = 0 :=
    ggQ2Sub_dual_eq_zero_on U φ hφ (fun u hu => hRU _ htR u hu) hc₀
  have hφc : ∀ i, φ (c i) = 0 := fun i =>
    hφU (c i) (hHU (Submodule.subset_span ⟨i, rfl⟩))
  have hαc₀ : ∀ i, α i c₀ = 0 := by
    intro i
    by_contra hne
    have hsri : Module.reflection (hαc i) = s i := by
      ext v
      rw [Module.reflection_apply, hs i v]
    have htrans : IsTransvectionLin ((Module.reflection hφ * Module.reflection (hαc i)) ^ 2) :=
      transvection_of_pair hφ (hαc i) (hφc i) hne
    have hmem : ((Module.reflection hφ * Module.reflection (hαc i)) ^ 2) ∈ A := by
      rw [hsri]
      exact A.pow_mem (A.mul_mem ht (hsA i)) 2
    exact hTF _ hmem htrans
  exact hfix c₀ hαc₀

private theorem ggQ2Sub_exists_refl_moves (A : Subgroup (V ≃ₗ[ZMod 3] V)) (x : V)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∃ (c' : V) (φ' : Module.Dual (ZMod 3) V) (h' : φ' c' = 2),
      Module.reflection h' ∈ A ∧ φ' x ≠ 0 ∧ c' ∉ Submodule.span (ZMod 3) {x} := by
  classical
  have hx0 : x ≠ 0 := by
    intro hx
    apply hRx
    intro r _
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  by_contra hcon
  apply hRx
  intro r hr
  rw [reflGp] at hr
  refine Subgroup.closure_induction (p := fun a _ => a x ∈ Submodule.span (ZMod 3) {x})
    ?_ ?_ ?_ ?_ hr
  · rintro t ⟨htA, htRefl⟩
    obtain ⟨c', φ', h', rfl⟩ := htRefl
    by_cases hφ'x : φ' x = 0
    · rw [Module.reflection_apply, hφ'x, zero_smul, sub_zero]
      exact Submodule.mem_span_singleton_self x
    · by_cases hc'x : c' ∈ Submodule.span (ZMod 3) {x}
      · rw [Module.reflection_apply]
        exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self x)
          (Submodule.smul_mem _ _ hc'x)
      · exact absurd ⟨c', φ', h', htA, hφ'x, hc'x⟩ hcon
  · simpa using Submodule.mem_span_singleton_self x
  · intro a b _ _ iha ihb
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp ihb
    rw [LinearEquiv.mul_apply, ← hμ, map_smul]
    exact Submodule.smul_mem _ μ iha
  · intro a _ iha
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp iha
    have hμ0 : μ ≠ 0 := by
      intro h0
      apply hx0
      have hax : a x = 0 := by rw [← hμ, h0, zero_smul]
      exact a.injective (by rw [hax, map_zero])
    have hinv : a⁻¹ x = μ⁻¹ • x := by
      apply a.injective
      calc a (a⁻¹ x) = x := a.apply_symm_apply x
        _ = a (μ⁻¹ • x) := by
            rw [map_smul, ← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    rw [hinv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

private theorem ggQ2Sub_commutator_apply (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) {g : V ≃ₗ[ZMod 3] V} (i : ι)
    (hgc : g (c i) = c i) (v : V) :
    (s i * g * s i * g.symm) v = v - α i (g (g.symm v) - g.symm v) • c i := by
  simp only [LinearEquiv.mul_apply, hs, map_sub, map_smul, hgc,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hαc i]
  module

private theorem ggQ2Sub_commutator_apply_smul (c : ι → V) (α : ι → Module.Dual (ZMod 3) V)
    (hαc : ∀ i, α i (c i) = 2) (s : ι → (V ≃ₗ[ZMod 3] V))
    (hs : ∀ i v, s i v = v - α i v • c i) {g : V ≃ₗ[ZMod 3] V} (i : ι) {ε : ZMod 3}
    (hgc : g (c i) = ε • c i) (v : V) :
    (s i * g * s i * g.symm) v - v = (ε * α i (g.symm v) - α i v) • c i := by
  simp only [LinearEquiv.mul_apply, hs, map_sub, map_smul, hgc,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hαc i]
  module

theorem ggQ2Sub_refl_centre (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U)
    (hRU : ∀ r ∈ reflGp A, ∀ u ∈ U, r u ∈ U)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x})
    {c₀ : V} {φ : Module.Dual (ZMod 3) V} (hφ : φ c₀ = 2) (ht : Module.reflection hφ ∈ A) :
    c₀ ∈ U := by
  classical
  by_contra hc₀
  have hsA : ∀ i, s i ∈ A := fun i => ggWAut_reflGp_le A (hsR i)
  have htR : Module.reflection hφ ∈ reflGp A :=
    Subgroup.subset_closure ⟨ht, c₀, φ, hφ, rfl⟩
  have hc₀span : c₀ ∈ Submodule.span (ZMod 3) {x} :=
    ggQ2Sub_centre_mem_span A hTF c α hαc s hs hsA x hfix U hHU hRU hφ ht hc₀
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hc₀span
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact (by decide : (2 : ZMod 3) ≠ 0) hφ.symm
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hc₀0
    rw [← hlam, h0, zero_smul]
  obtain ⟨c', φ', h', ht', hφ'x, hc'x⟩ := ggQ2Sub_exists_refl_moves A x hRx
  have ht'R : Module.reflection h' ∈ reflGp A :=
    Subgroup.subset_closure ⟨ht', c', φ', h', rfl⟩
  have hc'U : c' ∈ U := by
    by_contra hc'U
    exact hc'x (ggQ2Sub_centre_mem_span A hTF c α hαc s hs hsA x hfix U hHU hRU h' ht' hc'U)
  have hφU : ∀ u ∈ U, φ u = 0 :=
    ggQ2Sub_dual_eq_zero_on U φ hφ (fun u hu => hRU _ htR u hu) hc₀
  have hφc' : φ c' = 0 := hφU c' hc'U
  have hφ'c₀ : φ' c₀ ≠ 0 := by
    rw [← hlam, map_smul, smul_eq_mul]
    exact mul_ne_zero hlam0 hφ'x
  have htrans : IsTransvectionLin ((Module.reflection hφ * Module.reflection h') ^ 2) :=
    transvection_of_pair hφ h' hφc' hφ'c₀
  have hmem : ((Module.reflection hφ * Module.reflection h') ^ 2) ∈ A :=
    A.pow_mem (A.mul_mem ht ht') 2
  exact hTF _ hmem htrans

theorem ggQ2Sub_R_move (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U)
    (hRU : ∀ r ∈ reflGp A, ∀ u ∈ U, r u ∈ U)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ r ∈ reflGp A, ∀ v, r v - v ∈ U := by
  classical
  intro r hr v
  rw [reflGp] at hr
  refine Subgroup.closure_induction (p := fun a _ => ∀ w, a w - w ∈ U) ?_ ?_ ?_ ?_ hr v
  · rintro t ⟨htA, htRefl⟩ w
    obtain ⟨c₀, φ, hφ, rfl⟩ := htRefl
    have hc₀U : c₀ ∈ U :=
      ggQ2Sub_refl_centre A hTF c α hαc s hs hsR x hfix U hHU hRU hRx hφ htA
    rw [Module.reflection_apply]
    have hsub : w - φ w • c₀ - w = -(φ w • c₀) := by abel
    rw [hsub]
    exact U.neg_mem (U.smul_mem _ hc₀U)
  · intro w
    simpa using U.zero_mem
  · intro a b _ _ iha ihb w
    have hxy : (a * b) w - w = (a (b w) - b w) + (b w - w) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [hxy]
    exact U.add_mem (iha (b w)) (ihb w)
  · intro a _ iha w
    have hxv : a⁻¹ w - w = -(a (a⁻¹ w) - a⁻¹ w) := by
      have hxx : a (a⁻¹ w) = w := by simp
      rw [hxx]
      abel
    rw [hxv]
    exact U.neg_mem (iha (a⁻¹ w))

theorem ggQ2Sub_eq_one (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ A) (hU : ∀ u ∈ U, g u = u) (hV : ∀ v, g v - v ∈ U) :
    ∀ v, g v = v := by
  classical
  by_contra hne
  rw [not_forall] at hne
  obtain ⟨v₀, hv₀⟩ := hne
  let f : V →ₗ[ZMod 3] V := (g : V →ₗ[ZMod 3] V) - LinearMap.id
  have hf : ∀ w, f w = g w - w := fun w => by simp [f]
  have hψzero : ∀ i w, α i (f w) = 0 := by
    intro i w
    let ψ : Module.Dual (ZMod 3) V := -((α i).comp (f.comp (g.symm).toLinearMap))
    have hgc : g (c i) = c i := hU (c i) (hHU (Submodule.subset_span ⟨i, rfl⟩))
    have hkform : ∀ v, (s i * g * s i * g.symm) v = v + ψ v • c i := by
      intro v
      rw [ggQ2Sub_commutator_apply c α hαc s hs i hgc v]
      simp [ψ, f]
      module
    have hψc : ψ (c i) = 0 := by
      have hgic : g.symm (c i) = c i := by
        apply g.injective
        simpa [hgc]
      simp [ψ, hgic, f, hgc]
    have hci0 : c i ≠ 0 := by
      intro h0
      have h1 := hαc i
      rw [h0, map_zero] at h1
      exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
    by_cases hψ : ψ = 0
    · have h' : ψ (g w) = 0 := by
        simpa using congrArg (fun ψ : Module.Dual (ZMod 3) V => ψ (g w)) hψ
      have h'' : -α i (f w) = 0 := by
        simpa [ψ, LinearEquiv.symm_apply_apply] using h'
      exact neg_eq_zero.mp h''
    · exfalso
      have hkA : (s i * g * s i * g.symm) ∈ A :=
        A.mul_mem (A.mul_mem (A.mul_mem (hsA i) hg) (hsA i)) (A.inv_mem hg)
      exact hTF _ hkA ⟨c i, ψ, hci0, hψ, hψc, hkform⟩
  have hspan : ∀ w, f w ∈ Submodule.span (ZMod 3) {x} :=
    fun w => hfix (f w) (fun i => hψzero i w)
  have hfv₀ : f v₀ ≠ 0 := by
    intro h0
    apply hv₀
    have h1 : g v₀ - v₀ = 0 := by rwa [hf] at h0
    exact sub_eq_zero.mp h1
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp (hspan v₀)
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hfv₀
    rw [← hμ, h0, zero_smul]
  have hxU : x ∈ U := by
    have hmem : f v₀ ∈ U := by
      rw [hf]
      exact hV v₀
    have hx : x = μ⁻¹ • f v₀ := by
      rw [← hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    rw [hx]
    exact U.smul_mem _ hmem
  have hx0 : x ≠ 0 := by
    intro h0
    apply hfv₀
    rw [← hμ, h0, smul_zero]
  have hfx : f x = 0 := by
    rw [hf, hU x hxU, sub_self]
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one (ZMod 3) hx0
  let ψ : Module.Dual (ZMod 3) V := χ.comp f
  have hψx : ψ x = 0 := by
    change χ (f x) = 0
    rw [hfx, map_zero]
  have hψv₀ : ψ v₀ ≠ 0 := by
    change χ (f v₀) ≠ 0
    rw [← hμ, map_smul, hχ, smul_eq_mul, mul_one]
    exact hμ0
  have hψne : ψ ≠ 0 := by
    intro h0
    apply hψv₀
    rw [h0]
    exact LinearMap.zero_apply v₀
  have hform : ∀ v, g v = v + ψ v • x := by
    intro v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan v)
    have hψv : ψ v = a := by
      change χ (f v) = a
      rw [← ha, map_smul, hχ, smul_eq_mul, mul_one]
    have hgv : g v = v + f v := by
      rw [hf]
      abel
    rw [hgv, hψv, ← ha]
  exact hTF g hg ⟨x, ψ, hx0, hψne, hψx, hform⟩

theorem ggQ2Sub_scalar_x (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hxfix : ∀ i, α i x = 0)
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U)
    {g : V ≃ₗ[ZMod 3] V} (hg : g ∈ A) {ε : ZMod 3} (hε : ε ≠ 0) (hU : ∀ u ∈ U, g u = ε • u) :
    g x ∈ Submodule.span (ZMod 3) {x} := by
  classical
  have hg_inv_smul : ∀ u ∈ U, g.symm u = ε⁻¹ • u := by
    intro u hu
    have h1 : g (ε⁻¹ • u) = u := by
      rw [map_smul, hU u hu, smul_smul, inv_mul_cancel₀ hε, one_smul]
    calc g.symm u = g.symm (g (ε⁻¹ • u)) := by rw [h1]
      _ = ε⁻¹ • u := by simp
  have hmain : ∀ i, α i (g x) = 0 := by
    intro i
    let k : V ≃ₗ[ZMod 3] V := s i * g * s i * g.symm
    have hkA : k ∈ A :=
      A.mul_mem (A.mul_mem (A.mul_mem (hsA i) hg) (hsA i)) (A.inv_mem hg)
    have hkc : g (c i) = ε • c i := hU (c i) (hHU (Submodule.subset_span ⟨i, rfl⟩))
    have hkU : ∀ u ∈ U, k u = u := by
      intro u hu
      have hsu_mem : s i (g.symm u) ∈ U := by
        rw [hs i (g.symm u)]
        exact U.sub_mem (by rw [hg_inv_smul u hu]; exact U.smul_mem _ hu)
          (U.smul_mem _ (hHU (Submodule.subset_span ⟨i, rfl⟩)))
      have hg_scalar : g (s i (g.symm u)) = ε • s i (g.symm u) := hU _ hsu_mem
      calc k u = s i (g (s i (g.symm u))) := by simp only [k, LinearEquiv.mul_apply]
        _ = s i (ε • s i (g.symm u)) := by rw [hg_scalar]
        _ = ε • s i (s i (g.symm u)) := by rw [map_smul]
        _ = ε • g.symm u := by rw [ggQ2Sub_s_apply_apply c α hαc s hs i (g.symm u)]
        _ = u := by rw [hg_inv_smul u hu, smul_smul, mul_inv_cancel₀ hε, one_smul]
    have hkV : ∀ v, k v - v ∈ U := by
      intro v
      have hform : k v - v = (ε * α i (g.symm v) - α i v) • c i := by
        simpa only [k] using ggQ2Sub_commutator_apply_smul c α hαc s hs i hkc v
      rw [hform]
      exact U.smul_mem _ (hHU (Submodule.subset_span ⟨i, rfl⟩))
    have hk1 : ∀ v, k v = v :=
      ggQ2Sub_eq_one A hTF c α hαc s hs hsA x hfix U hHU hkA hkU hkV
    have hkgx : k (g x) = s i (g x) := by
      simp only [k, LinearEquiv.mul_apply]
      simp [hs, hxfix]
    have hgi : s i (g x) = g x := by
      rw [← hkgx]
      exact hk1 (g x)
    have h3 : g x - α i (g x) • c i = g x := by
      rw [← hs i (g x), hgi]
    have h2 : α i (g x) • c i = 0 := sub_eq_self.mp h3
    have hci0 : c i ≠ 0 := by
      intro h0
      have h1 := hαc i
      rw [h0, map_zero] at h1
      exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
    exact (smul_eq_zero.mp h2).resolve_right hci0
  exact hfix (g x) hmain

theorem ggQ2Sub_not_neg (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A)
    (c : ι → V) (α : ι → Module.Dual (ZMod 3) V) (hαc : ∀ i, α i (c i) = 2)
    (s : ι → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsR : ∀ i, s i ∈ reflGp A)
    (x : V) (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hxfix : ∀ i, α i x = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)))
    (U : Submodule (ZMod 3) V) (hHU : Submodule.span (ZMod 3) (Set.range c) ≤ U) (hUtop : U ≠ ⊤)
    (hRU : ∀ r ∈ reflGp A, ∀ u ∈ U, r u ∈ U)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x}) :
    ∀ r ∈ reflGp A, ¬ ∀ u ∈ U, r u = -u := by
  classical
  have hsA : ∀ i, s i ∈ A := fun i => ggWAut_reflGp_le A (hsR i)
  intro r₀ hr₀ hneg
  have hr₀A : r₀ ∈ A := ggWAut_reflGp_le A hr₀
  have hr₀inv_neg : ∀ u ∈ U, r₀.symm u = -u := by
    intro u hu
    apply r₀.injective
    rw [show r₀ (r₀.symm u) = u from r₀.apply_symm_apply u, map_neg, hneg u hu, neg_neg]
  by_cases hxU : x ∈ U
  ·
    have hcomm : ∀ r ∈ reflGp A, r₀ * r = r * r₀ := by
      intro r hr
      let k : V ≃ₗ[ZMod 3] V := r₀ * r * r₀⁻¹ * r⁻¹
      have hk_mem : k ∈ reflGp A :=
        (reflGp A).mul_mem ((reflGp A).mul_mem ((reflGp A).mul_mem hr₀ hr)
          ((reflGp A).inv_mem hr₀)) ((reflGp A).inv_mem hr)
      have hkA : k ∈ A := ggWAut_reflGp_le A hk_mem
      have hkfixU : ∀ u ∈ U, k u = u := by
        intro u hu
        have h1 : r⁻¹ u ∈ U := hRU r⁻¹ ((reflGp A).inv_mem hr) u hu
        have h2 : r₀⁻¹ (r⁻¹ u) = -(r⁻¹ u) := hr₀inv_neg _ h1
        have h3 : r (r₀⁻¹ (r⁻¹ u)) = -u := by
          rw [h2, map_neg]
          simp
        have h4 : r₀ (r (r₀⁻¹ (r⁻¹ u))) = u := by
          rw [h3, hneg (-u) (U.neg_mem hu), neg_neg]
        calc k u = r₀ (r (r₀⁻¹ (r⁻¹ u))) := by simp only [k, LinearEquiv.mul_apply]
          _ = u := h4
      have hkV : ∀ v, k v - v ∈ U :=
        ggQ2Sub_R_move A hTF c α hαc s hs hsR x hfix U hHU hRU hRx k hk_mem
      have hk1 : ∀ v, k v = v :=
        ggQ2Sub_eq_one A hTF c α hαc s hs hsA x hfix U hHU hkA hkfixU hkV
      have hkeq : k = 1 := LinearEquiv.ext hk1
      have h1 : r₀ * r * r₀⁻¹ = r := by
        have h2 := congrArg (fun e : V ≃ₗ[ZMod 3] V => e * r) hkeq
        have h3 : k * r = r₀ * r * r₀⁻¹ := by
          simp only [k]
          group
        rw [h3] at h2
        simpa using h2
      calc r₀ * r = (r₀ * r * r₀⁻¹) * r₀ := by group
        _ = r * r₀ := by rw [h1]
    let E : Submodule (ZMod 3) V := LinearMap.ker ((r₀ : V →ₗ[ZMod 3] V) - LinearMap.id)
    have hEdisj : E ⊓ U = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzE, hzU⟩ := Submodule.mem_inf.mp hz
      rw [Submodule.mem_bot]
      have hzE' : r₀ z = z := by
        have h := hzE
        rw [LinearMap.mem_ker] at h
        change r₀ z - z = 0 at h
        exact sub_eq_zero.mp h
      have hzneg : r₀ z = -z := hneg z hzU
      have hsum : z + z = 0 := by
        have hz' : z = -z := hzE'.symm.trans hzneg
        have h := congrArg (fun w => z + w) hz'
        rw [h]
        abel
      have htwo : (2 : ZMod 3) • z = 0 := by
        rw [two_smul]
        exact hsum
      exact (smul_eq_zero.mp htwo).resolve_left (by decide)
    have hEstab : ∀ r ∈ reflGp A, ∀ e ∈ E, r e ∈ E := by
      intro r hr e he
      rw [LinearMap.mem_ker] at he ⊢
      change r₀ e - e = 0 at he
      change r₀ (r e) - r e = 0
      have he' : r₀ e = e := sub_eq_zero.mp he
      have hre : r₀ (r e) = r (r₀ e) := by
        have h := congrArg (fun (f : V ≃ₗ[ZMod 3] V) => f e) (hcomm r hr)
        simpa only [LinearEquiv.mul_apply] using h
      rw [hre, he', sub_self]
    have hE : ∀ i, ∀ e ∈ E, α i e • c i ∈ E := by
      intro i e he
      have h1 : s i e ∈ E := hEstab (s i) (hsR i) e he
      have h2 : s i e = e - α i e • c i := hs i e
      have h3 : α i e • c i = e - s i e := by rw [h2]; abel
      rw [h3]
      exact E.sub_mem he h1
    have hHne : Submodule.span (ZMod 3) (Set.range c) ≠ ⊥ := by
      intro hbot
      have hfr : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) = 0 := by
        rw [hbot]
        simp
      omega
    obtain ⟨v, -, hvU⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hUtop)
    let w : V := r₀ v - v
    have hwU : w ∈ U :=
      ggQ2Sub_R_move A hTF c α hαc s hs hsR x hfix U hHU hRU hRx r₀ hr₀ v
    have hv₁notU : v - w ∉ U := by
      intro h
      apply hvU
      have h1 : v = (v - w) + w := by abel
      rw [h1]
      exact U.add_mem h hwU
    have hv₁E : v - w ∈ E := by
      rw [LinearMap.mem_ker]
      change r₀ (v - w) - (v - w) = 0
      have hrv : r₀ v = v + w := by
        change r₀ v = v + (r₀ v - v)
        abel
      rw [map_sub, hrv, hneg w hwU]
      have hww : w + w = -w := by
        rw [← two_smul (ZMod 3) w, ggQ2Sub_two_smul]
      rw [sub_neg_eq_add, add_assoc, hww]
      abel
    have hxspanU : Submodule.span (ZMod 3) {x} ≤ U := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hxU
    rcases ggQ2Mix_stable_dichotomy c α x hfix hconn E hE with hHE | hEx
    · exfalso
      have hle : Submodule.span (ZMod 3) (Set.range c) ≤ ⊥ := by
        rw [← hEdisj]
        exact le_inf hHE hHU
      exact hHne (le_bot_iff.mp hle)
    · exfalso
      exact hv₁notU (hxspanU (hEx hv₁E))
  ·
    have hr₀xspan : r₀ x ∈ Submodule.span (ZMod 3) {x} :=
      ggQ2Sub_scalar_x A hTF c α hαc s hs hsA x hfix hxfix U hHU hr₀A
        (ε := -1) (by decide) (fun u hu => by rw [hneg u hu, neg_one_smul])
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hr₀xspan
    have hr₀xmove : r₀ x - x ∈ U :=
      ggQ2Sub_R_move A hTF c α hαc s hs hsR x hfix U hHU hRU hRx r₀ hr₀ x
    have hlam1 : lam = 1 := by
      by_contra hne
      have hcoef : lam - 1 ≠ 0 := sub_ne_zero.mpr hne
      apply hxU
      have hmem : (lam - 1) • x ∈ U := by
        have h := hr₀xmove
        rw [← hlam] at h
        have heq : lam • x - x = (lam - 1) • x := by rw [sub_smul, one_smul]
        rwa [heq] at h
      have hx : x = (lam - 1)⁻¹ • ((lam - 1) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hcoef, one_smul]
      rw [hx]
      exact U.smul_mem _ hmem
    have hr₀x : r₀ x = x := by
      rw [← hlam, hlam1, one_smul]
    have hr₀inv_x : r₀.symm x = x := by
      have h : r₀.symm (r₀ x) = r₀.symm x := congrArg (fun v => r₀.symm v) hr₀x
      simpa using h.symm
    obtain ⟨c', φ', h', ht', hφ'x, hc'x⟩ := ggQ2Sub_exists_refl_moves A x hRx
    have hc'U : c' ∈ U :=
      ggQ2Sub_refl_centre A hTF c α hαc s hs hsR x hfix U hHU hRU hRx h' ht'
    have hr₀inv_c' : r₀.symm c' = -c' := by
      apply r₀.injective
      rw [show r₀ (r₀.symm c') = c' from r₀.apply_symm_apply c', map_neg, hneg c' hc'U,
        neg_neg]
    let φ'' : Module.Dual (ZMod 3) V := -(φ'.comp (r₀⁻¹).toLinearMap)
    have hφ'' : φ'' c' = 2 := by
      simp [φ'', hr₀inv_c', h']
    let t'' : V ≃ₗ[ZMod 3] V := r₀ * Module.reflection h' * r₀⁻¹
    have ht''A : t'' ∈ A := A.mul_mem (A.mul_mem hr₀A ht') (A.inv_mem hr₀A)
    have ht''eq : t'' = Module.reflection hφ'' := by
      ext v
      rw [Module.reflection_apply]
      calc t'' v = r₀ (r₀⁻¹ v - φ' (r₀⁻¹ v) • c') := by
            simp only [t'', LinearEquiv.mul_apply, Module.reflection_apply]
        _ = v + φ' (r₀⁻¹ v) • c' := by
            rw [map_sub, map_smul, show r₀ (r₀⁻¹ v) = v from r₀.apply_symm_apply v,
              hneg c' hc'U]
            module
        _ = v - φ'' v • c' := by
            simp [φ'']
    have ht''reflA : Module.reflection hφ'' ∈ A := by
      rw [← ht''eq]
      exact ht''A
    by_cases hφeq : φ' = φ''
    · have hx := congrArg (fun φ : Module.Dual (ZMod 3) V => φ x) hφeq
      have hnegx : φ' x = -φ' x := by
        calc φ' x = φ'' x := hx
          _ = -φ' x := by simp [φ'', hr₀inv_x]
      have hsum : φ' x + φ' x = 0 := by
        have h := congrArg (fun a : ZMod 3 => φ' x + a) hnegx
        rw [h]
        abel
      have htwo : (2 : ZMod 3) • φ' x = 0 := by
        rw [two_smul]
        exact hsum
      exact hφ'x ((smul_eq_zero.mp htwo).resolve_left (by decide))
    · have htv : IsTransvectionLin (Module.reflection hφ'' * Module.reflection h') :=
        transvection_of_same_centre h' hφ'' hφeq
      have hmem : Module.reflection hφ'' * Module.reflection h' ∈ A :=
        A.mul_mem ht''reflA ht'
      exact hTF _ hmem htv

end CFSG.StandardType

end

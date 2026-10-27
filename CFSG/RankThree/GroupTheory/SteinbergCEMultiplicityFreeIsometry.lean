module

public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.GroupTheory

section Multiplicity

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] {A : Type*} [Group A]
  {ρ : Representation k A V}

theorem subrep_linearMap_eq_zero {U₁ U₂ : Subrepresentation ρ}
    (h₁ : U₁.toRepresentation.IsIrreducible) (h₂ : U₂.toRepresentation.IsIrreducible)
    (hne : IsEmpty (U₁.toRepresentation.Equiv U₂.toRepresentation))
    (f : U₁.toSubmodule →ₗ[k] U₂.toSubmodule)
    (hf : ∀ a x, f (U₁.toRepresentation a x) = U₂.toRepresentation a (f x)) : f = 0 := by
  have := h₁
  have := h₂
  let F := LinearMap.intertwiningMap_of_isIntertwiningMap U₁.toRepresentation
    U₂.toRepresentation f hf
  rcases Representation.IsIrreducible.bijective_or_eq_zero F with h | h
  · exact (hne.false (F.ofBijective h)).elim
  · exact congrArg Representation.IntertwiningMap.toLinearMap h

theorem eq_bot_or_eq_of_le_subrep {U : Subrepresentation ρ} (hU : U.toRepresentation.IsIrreducible)
    {W : Submodule k V} (hWU : W ≤ U.toSubmodule) (hW : ∀ a, ∀ v ∈ W, ρ a v ∈ W) :
    W = ⊥ ∨ W = U.toSubmodule := by
  rcases eq_bot_or_eq_top_of_isIrreducible hU (W.comap U.toSubmodule.subtype)
      (fun a x hx => hW a x hx) with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : (⟨w, hWU hw⟩ : U.toSubmodule) ∈ W.comap U.toSubmodule.subtype := hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h1
  · right
    refine le_antisymm hWU fun u hu => ?_
    have h1 : (⟨u, hu⟩ : U.toSubmodule) ∈ W.comap U.toSubmodule.subtype := by
      rw [h]
      exact Submodule.mem_top
    exact h1

theorem subrep_ne_bot {U : Subrepresentation ρ} (hU : U.toRepresentation.IsIrreducible) :
    U.toSubmodule ≠ ⊥ :=
  Submodule.nontrivial_iff_ne_bot.mp (nontrivial_of_isIrreducible hU)

theorem bilin_eq_zero_of_subrep_ne {b : LinearMap.BilinForm k V}
    (hρb : ∀ a x y, b (ρ a x) (ρ a y) = b x y) {U₁ U₂ : Subrepresentation ρ}
    (h₁ : U₁.toRepresentation.IsIrreducible) (h₂ : U₂.toRepresentation.IsIrreducible)
    (hne : IsEmpty (U₁.toRepresentation.Equiv U₂.toRepresentation))
    (hdual : Nonempty (U₂.toRepresentation.Equiv U₂.toRepresentation.dual)) :
    ∀ x ∈ U₁.toSubmodule, ∀ y ∈ U₂.toSubmodule, b x y = 0 := by
  obtain ⟨ψ⟩ := hdual
  set f : U₁.toSubmodule →ₗ[k] Module.Dual k U₂.toSubmodule :=
    b.compl₁₂ U₁.toSubmodule.subtype U₂.toSubmodule.subtype with hf_def
  have hf : ∀ a x, f (U₁.toRepresentation a x) = U₂.toRepresentation.dual a (f x) := by
    intro a x
    apply LinearMap.ext
    intro y
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    change b (ρ a x) y = b x (ρ a⁻¹ y)
    calc b (ρ a x) y = b (ρ a x) (ρ a (ρ a⁻¹ y)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      _ = b x (ρ a⁻¹ y) := hρb a x _
  have h0 := subrep_linearMap_eq_zero h₁ h₂ hne (ψ.symm.toLinearMap ∘ₗ f) fun a x => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf]
    exact ψ.symm.toIntertwiningMap.isIntertwining _ _ a (f x)
  intro x hx y hy
  have h1 : f ⟨x, hx⟩ = 0 := by
    have h2 := LinearMap.congr_fun h0 ⟨x, hx⟩
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at h2
    have h3 := congrArg ψ h2
    rwa [map_zero, Representation.Equiv.coe_toLinearMap, Representation.Equiv.apply_symm_apply]
      at h3
  have h4 := LinearMap.congr_fun h1 ⟨y, hy⟩
  exact h4

theorem eq_zero_of_bilin_subrep {ι : Type*} [DecidableEq ι] {b : LinearMap.BilinForm k V}
    (hb : b.Nondegenerate) {U : ι → Subrepresentation ρ}
    (hU : DirectSum.IsInternal fun i => (U i).toSubmodule)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ (U i).toSubmodule, ∀ y ∈ (U j).toSubmodule, b x y = 0)
    {j : ι} {u : V} (hu : u ∈ (U j).toSubmodule) (h : ∀ v ∈ (U j).toSubmodule, b u v = 0) :
    u = 0 := by
  apply hb.1 u
  intro w
  have hw : w ∈ ⨆ i, (U i).toSubmodule := by
    rw [hU.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => b u w = 0) hw (fun i w hw => ?_)
    (map_zero _) fun x y hx hy => by rw [map_add, hx, hy, add_zero]
  by_cases hij : i = j
  · subst hij
    exact h w hw
  · exact horth j i (Ne.symm hij) u hu w hw

theorem exists_subrep_le_of_invariant [FiniteDimensional k V] {ι : Type*} [DecidableEq ι]
    {U : ι → Subrepresentation ρ} (hU : DirectSum.IsInternal fun i => (U i).toSubmodule)
    (hirr : ∀ i, (U i).toRepresentation.IsIrreducible)
    (hne : ∀ i j, i ≠ j → IsEmpty ((U i).toRepresentation.Equiv (U j).toRepresentation))
    {T : Submodule k V} (hT : ∀ a, ∀ v ∈ T, ρ a v ∈ T) (hT0 : T ≠ ⊥) :
    ∃ j, (U j).toSubmodule ≤ T := by
  classical
  obtain ⟨S, hST, hSinv, hS0, hSmin⟩ : ∃ S : Submodule k V, S ≤ T ∧
      (∀ a, ∀ v ∈ S, ρ a v ∈ S) ∧ S ≠ ⊥ ∧ ∀ S' : Submodule k V, S' ≤ S →
        (∀ a, ∀ v ∈ S', ρ a v ∈ S') → S' ≠ ⊥ → S' = S := by
    have hP : ∃ n, ∃ S : Submodule k V, S ≤ T ∧ (∀ a, ∀ v ∈ S, ρ a v ∈ S) ∧ S ≠ ⊥ ∧
        Module.finrank k S = n := ⟨_, T, le_rfl, hT, hT0, rfl⟩
    obtain ⟨S, hST, hSinv, hS0, hSn⟩ := Nat.find_spec hP
    refine ⟨S, hST, hSinv, hS0, fun S' hS'S hS'inv hS'0 => ?_⟩
    have hmin := Nat.find_min' hP ⟨S', hS'S.trans hST, hS'inv, hS'0, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hS'S (hSn ▸ hmin)
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun i => (U i).toSubmodule) hU
  set π : ι → V →ₗ[k] V := fun i => (U i).toSubmodule.subtype ∘ₗ
    (DirectSum.component k ι (fun i => (U i).toSubmodule) i) ∘ₗ e.symm.toLinearMap with hπ
  have hπapply : ∀ i v, π i v = ((e.symm v) i : V) := fun i v => rfl
  have hπmem : ∀ i v, π i v ∈ (U i).toSubmodule := fun i v => (e.symm v i).2
  have hπself : ∀ i v, v ∈ (U i).toSubmodule → π i v = v := fun i v hv => by
    rw [hπapply, hU.ofBijective_coeLinearMap_of_mem hv]
  have hπne : ∀ i j v, i ≠ j → v ∈ (U i).toSubmodule → π j v = 0 := fun i j v hij hv => by
    rw [hπapply, hU.ofBijective_coeLinearMap_of_mem_ne hij hv, ZeroMemClass.coe_zero]
  have hπρ : ∀ i a v, π i (ρ a v) = ρ a (π i v) := by
    intro i a v
    have hv : v ∈ ⨆ j, (U j).toSubmodule := by
      rw [hU.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun v => π i (ρ a v) = ρ a (π i v)) hv
      (fun j w hw => ?_) (by rw [map_zero, map_zero, map_zero]) fun x y hx hy => by
        rw [map_add, map_add, hx, hy, map_add, map_add]
    have hρw : ρ a w ∈ (U j).toSubmodule := (U j).apply_mem_toSubmodule a hw
    by_cases hij : j = i
    · subst hij
      rw [hπself _ _ hρw, hπself _ _ hw]
    · rw [hπne _ _ _ hij hρw, hπne _ _ _ hij hw, map_zero]
  have hπzero : ∀ v, (∀ i, π i v = 0) → v = 0 := by
    intro v hv
    have h1 : e.symm v = 0 := by
      ext i
      have h2 := hv i
      rw [hπapply] at h2
      rw [DirectSum.zero_apply, ZeroMemClass.coe_zero]
      exact h2
    calc v = e (e.symm v) := (e.apply_symm_apply v).symm
      _ = 0 := by rw [h1, map_zero]
  obtain ⟨s₀, hs₀, hs₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨j, hj⟩ : ∃ j, π j s₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hs₀0 (hπzero s₀ h)
  set φ : S →ₗ[k] (U j).toSubmodule := (π j).restrict fun v _ => hπmem j v with hφ
  have hφapply : ∀ s : S, (φ s : V) = π j s := fun s => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    have hK : S ⊓ LinearMap.ker (π j) = ⊥ := by
      by_contra hK
      have h1 := hSmin _ inf_le_left (fun a v hv => ?_) hK
      · have h2 : s₀ ∈ S ⊓ LinearMap.ker (π j) := by
          rw [h1]
          exact hs₀
        exact hj (Submodule.mem_inf.mp h2).2
      · obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
        refine Submodule.mem_inf.mpr ⟨hSinv a v hv1, ?_⟩
        rw [LinearMap.mem_ker] at hv2 ⊢
        rw [hπρ, hv2, map_zero]
    rw [eq_bot_iff]
    intro s hs
    rw [LinearMap.mem_ker] at hs
    have h1 : (s : V) ∈ S ⊓ LinearMap.ker (π j) :=
      Submodule.mem_inf.mpr ⟨s.2, by rw [LinearMap.mem_ker, ← hφapply, hs, ZeroMemClass.coe_zero]⟩
    rw [hK, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot]
    exact Subtype.ext h1
  have hφsurj : Function.Surjective φ := by
    have hRinv : ∀ a, ∀ v ∈ S.map (π j), ρ a v ∈ S.map (π j) := by
      intro a v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      rw [← hπρ]
      exact Submodule.mem_map_of_mem (hSinv a w hw)
    have hR : S.map (π j) = (U j).toSubmodule := by
      rcases eq_bot_or_eq_of_le_subrep (hirr j) (W := S.map (π j))
          (Submodule.map_le_iff_le_comap.mpr fun v _ => hπmem j v) hRinv with h | h
      · exfalso
        have h1 : π j s₀ ∈ S.map (π j) := Submodule.mem_map_of_mem hs₀
        rw [h, Submodule.mem_bot] at h1
        exact hj h1
      · exact h
    intro u
    have hu : (u : V) ∈ S.map (π j) := by
      rw [hR]
      exact u.2
    obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp hu
    exact ⟨⟨w, hw⟩, Subtype.ext hwu⟩
  set φe := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφeρ : ∀ a (u : (U j).toSubmodule),
      ((φe.symm ((U j).toRepresentation a u) : S) : V) = ρ a (φe.symm u : V) := by
    intro a u
    set s := φe.symm u
    have hs : φe s = u := φe.apply_symm_apply u
    have h1 : φe ⟨ρ a s, hSinv a s s.2⟩ = (U j).toRepresentation a u := by
      apply Subtype.ext
      change π j (ρ a s) = ρ a (u : V)
      rw [hπρ, ← hs]
      rfl
    rw [← h1, LinearEquiv.symm_apply_apply]
  have hother : ∀ i, i ≠ j → ∀ s ∈ S, π i s = 0 := by
    intro i hij s hs
    set θ : (U j).toSubmodule →ₗ[k] (U i).toSubmodule :=
      ((π i).restrict fun v _ => hπmem i v : S →ₗ[k] (U i).toSubmodule) ∘ₗ φe.symm.toLinearMap
    have hθ : θ = 0 := subrep_linearMap_eq_zero (hirr j) (hirr i) (hne j i (Ne.symm hij)) θ
      fun a u => by
        apply Subtype.ext
        change π i ((φe.symm ((U j).toRepresentation a u) : S) : V) =
          ρ a (π i (φe.symm u : V))
        rw [hφeρ, hπρ]
    have h1 := LinearMap.congr_fun hθ (φe ⟨s, hs⟩)
    have h2 : (θ (φe ⟨s, hs⟩) : V) = π i s := by
      change π i ((φe.symm (φe ⟨s, hs⟩) : S) : V) = π i s
      rw [LinearEquiv.symm_apply_apply]
    rw [← h2, h1, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  have hSU : S ≤ (U j).toSubmodule := by
    intro s hs
    have h1 : s - π j s = 0 := by
      refine hπzero _ fun i => ?_
      rw [map_sub]
      by_cases hij : i = j
      · subst hij
        rw [hπself _ _ (hπmem i s), sub_self]
      · rw [hother i hij s hs, hπne _ _ _ (Ne.symm hij) (hπmem j s), sub_self]
    rw [sub_eq_zero] at h1
    rw [h1]
    exact hπmem j s
  rcases eq_bot_or_eq_of_le_subrep (hirr j) hSU hSinv with h | h
  · exact absurd h hS0
  · exact ⟨j, h ▸ hST⟩

end Multiplicity

open CFSG.QuasithinUnique.Setup.X7 in
theorem multiplicity_free_self_dual_isometry_action_excludes_normalized_defining_prime_subgroups
    {k : Type*} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] {V : Type*}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {b : LinearMap.BilinForm k V}
    (hb : b.Nondegenerate) {A : Type*} [Group A] (ρ : Representation k A V)
    (hρb : ∀ a x y, b (ρ a x) (ρ a y) = b x y) {ι : Type*} [DecidableEq ι]
    (U : ι → Subrepresentation ρ) (hU : DirectSum.IsInternal fun i => (U i).toSubmodule)
    (hirr : ∀ i, (U i).toRepresentation.IsIrreducible)
    (hne : ∀ i j, i ≠ j → IsEmpty ((U i).toRepresentation.Equiv (U j).toRepresentation))
    (hdual : ∀ i, Nonempty ((U i).toRepresentation.Equiv (U i).toRepresentation.dual))
    {R : Subgroup (LinearMap.GeneralLinearGroup k V)}
    (hRb : ∀ r ∈ R, ∀ x y, b ((r : Module.End k V) x) ((r : Module.End k V) y) = b x y)
    (hR : IsPGroup ℓ R)
    (hRA : ∀ a : A, ∀ r ∈ R, ρ.asGroupHom a * r * (ρ.asGroupHom a)⁻¹ ∈ R) :
    R = ⊥ := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (Module.End k V) :=
    Finite.of_injective (fun f : V →ₗ[k] V => (f : V → V)) DFunLike.coe_injective
  have : Finite (LinearMap.GeneralLinearGroup k V) :=
    Finite.of_injective (fun u : LinearMap.GeneralLinearGroup k V => (u : Module.End k V))
      Units.val_injective
  have horth : ∀ i j, i ≠ j → ∀ x ∈ (U i).toSubmodule, ∀ y ∈ (U j).toSubmodule, b x y = 0 :=
    fun i j hij => bilin_eq_zero_of_subrep_ne hρb (hirr i) (hirr j) (hne i j hij) (hdual j)
  let F : Submodule k V :=
    { carrier := {v | ∀ r ∈ R, (r : Module.End k V) v = v}
      add_mem' := fun {v w} hv hw r hr => by rw [map_add, hv r hr, hw r hr]
      zero_mem' := fun r _ => map_zero _
      smul_mem' := fun c v hv r hr => by rw [map_smul, hv r hr] }
  let Fp : Submodule k V :=
    { carrier := {w | ∀ u ∈ F, b u w = 0}
      add_mem' := fun {v w} hv hw u hu => by rw [map_add, hv u hu, hw u hu, add_zero]
      zero_mem' := fun u _ => map_zero _
      smul_mem' := fun c w hw u hu => by rw [map_smul, hw u hu, smul_zero] }
  have hmemF : ∀ v, v ∈ F ↔ ∀ r ∈ R, (r : Module.End k V) v = v := fun v => Iff.rfl
  have hmemFp : ∀ w, w ∈ Fp ↔ ∀ u ∈ F, b u w = 0 := fun w => Iff.rfl
  have hρinv : ∀ a v, ρ a (ρ a⁻¹ v) = v := fun a v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hFA : ∀ a, ∀ v ∈ F, ρ a v ∈ F := by
    intro a v hv r hr
    have h1 := hv _ (hRA a⁻¹ r hr)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ← map_inv,
      inv_inv, Representation.asGroupHom_apply, Representation.asGroupHom_apply] at h1
    calc (r : Module.End k V) (ρ a v) = ρ a (ρ a⁻¹ ((r : Module.End k V) (ρ a v))) :=
          (hρinv a _).symm
      _ = ρ a v := by rw [h1]
  have hFpA : ∀ a, ∀ w ∈ Fp, ρ a w ∈ Fp := by
    intro a w hw u hu
    rw [← hρinv a u, hρb]
    exact hw _ (hFA a⁻¹ u hu)
  have hFpR : ∀ r ∈ R, ∀ w ∈ Fp, (r : Module.End k V) w ∈ Fp := by
    intro r hr w hw u hu
    rw [← hu r hr, hRb r hr]
    exact hw u hu
  have hT : F ⊓ Fp = ⊥ := by
    by_contra hT
    obtain ⟨j, hj⟩ := exists_subrep_le_of_invariant hU hirr hne
      (fun a v hv => Submodule.mem_inf.mpr ⟨hFA a v (Submodule.mem_inf.mp hv).1,
        hFpA a v (Submodule.mem_inf.mp hv).2⟩) hT
    apply subrep_ne_bot (hirr j)
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    exact eq_zero_of_bilin_subrep hb hU horth hu fun v hv =>
      (Submodule.mem_inf.mp (hj hv)).2 u (Submodule.mem_inf.mp (hj hu)).1
  have hFp : Fp = ⊥ := by
    by_contra hFp
    obtain ⟨w, hw, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup k (Fact.out : ℓ.Prime) hR
      ((Units.coeHom (Module.End k V)).comp R.subtype) Fp
      (fun r w hw => hFpR r r.2 w hw) hFp
    apply hw0
    have hwF : w ∈ F := fun r hr => hwfix ⟨r, hr⟩
    have h1 : w ∈ F ⊓ Fp := Submodule.mem_inf.mpr ⟨hwF, hw⟩
    rwa [hT, Submodule.mem_bot] at h1
  have hFtop : F = ⊤ := by
    let L : V →ₗ[k] Module.Dual k F := b.flip.compl₂ F.subtype
    have hker : LinearMap.ker L = Fp := by
      ext w
      rw [LinearMap.mem_ker, hmemFp]
      constructor
      · intro h u hu
        exact LinearMap.congr_fun h ⟨u, hu⟩
      · intro h
        apply LinearMap.ext
        intro u
        exact h u u.2
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    rw [hker, hFp, finrank_bot, add_zero] at h1
    have h2 : Module.finrank k (LinearMap.range L) ≤ Module.finrank k F := by
      calc Module.finrank k (LinearMap.range L) ≤ Module.finrank k (Module.Dual k F) :=
            Submodule.finrank_le _
        _ = Module.finrank k F := Subspace.dual_finrank_eq
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le F) (h1 ▸ h2))
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply LinearMap.ext
  intro v
  have hv : v ∈ F := by
    rw [hFtop]
    exact Submodule.mem_top
  exact hv r hr


end CFSG.RankThree.GroupTheory

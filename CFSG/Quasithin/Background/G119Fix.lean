module

public import CFSG.Quasithin.Background.G119Basic
public import CFSG.Quasithin.Background.G119E11
public import CFSG.Quasithin.Background.G119Geom

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem g119_conjSub_orthogonal_eq {B : LinearMap.BilinForm (ZMod 2) V} {x : GLV V}
    (hB : ∀ v w, B (x v) (x w) = B v w) {U : Submodule (ZMod 2) V} (hxU : conjSub x U = U) :
    conjSub x (B.orthogonal U) = B.orthogonal U := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff] at hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hn' : n ∈ conjSub x U := by rw [hxU]; exact hn
    obtain ⟨n₀, hn₀, rfl⟩ := hn'
    have := hm n₀ hn₀
    show B (x n₀) (x m) = 0
    rw [hB]
    exact this
  · intro m hm
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm
    refine ⟨x.symm m, ?_, by simp⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have hxn : x n ∈ U := by
      have : x n ∈ conjSub x U := apply_mem_conjSub hn
      rwa [hxU] at this
    have h1 := hm (x n) hxn
    have h2 : B (x n) (x (x.symm m)) = B n (x.symm m) := hB _ _
    rw [LinearEquiv.apply_symm_apply] at h2
    exact h2 ▸ h1

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem exists_of_not_le_orthogonal (hk : Module.finrank (ZMod 2) V = 3 * Module.finrank (ZMod 2) I)
    {x : GLV V} (hx : x ∈ X) {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J)
    (hne : J ≠ I) (hfix : conjSub x J = J) (hnle : ¬ J ≤ B.orthogonal I) :
    ∃ M : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) M ∧ M ≤ B.orthogonal I ∧ M ≠ I ∧
      conjSub x M = M := by
  classical
  set H := normalClosure Γ L with hH
  have hrefl : B.IsRefl := c.hyp.toG101Hyp.isRefl
  have hirrJ := c.irrPlus_isIrr hJ
  have hirrI := c.irr
  have hIJ : I ⊓ J = ⊥ := by
    rw [inf_comm]
    exact c.inf_eq_bot_of_ne hJ c.irrPlus hne
  have hJperp : J ⊓ B.orthogonal I = ⊥ := by
    rcases hirrJ.eq_bot_or_eq (hirrJ.1.inf c.invariant_orthogonal_H) inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hnle
  have hIperp : I ⊓ B.orthogonal J = ⊥ := by
    have hinv : Invariant H (I ⊓ B.orthogonal J) :=
      hirrI.1.inf (hirrJ.1.orthogonal c.hyp.H_isometry)
    rcases hirrI.eq_bot_or_eq hinv inf_le_left with h | h
    · exact h
    · exfalso
      apply hnle
      have hIle : I ≤ B.orthogonal J := h ▸ inf_le_right
      intro j hj
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.1 (hIle hn)) j hj
      exact hrefl _ _ h1
  have hnd : NondegOn B (I ⊔ J) := by
    intro u hu hu0
    obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hu
    have hj0 : j = 0 := by
      have hjperp : j ∈ B.orthogonal I := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro n hn
        have h1 := hu0 n (Submodule.mem_sup_left hn)
        rw [map_add, LinearMap.add_apply, c.isotropic i hi n hn, zero_add] at h1
        exact hrefl _ _ h1
      have : j ∈ J ⊓ B.orthogonal I := ⟨hj, hjperp⟩
      rw [hJperp] at this
      exact (Submodule.mem_bot _).1 this
    subst hj0
    rw [add_zero]
    have hi' : i ∈ B.orthogonal J := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 := hu0 n (Submodule.mem_sup_right hn)
      rw [add_zero] at h1
      exact hrefl _ _ h1
    have : i ∈ I ⊓ B.orthogonal J := ⟨hi, hi'⟩
    rw [hIperp] at this
    exact (Submodule.mem_bot _).1 this
  have hcompl := c.hyp.isCompl_orthogonal hnd
  set M := B.orthogonal (I ⊔ J) with hM
  have hIJinv : Invariant H (I ⊔ J) := c.irrPlus.1.sup hJ.1
  have hMinv : Invariant H M := hIJinv.orthogonal c.hyp.H_isometry
  have hxM : conjSub x M = M := by
    refine g119_conjSub_orthogonal_eq (c.hyp.isometry x (c.X_le hx)) ?_
    rw [conjSub_sup, c.conjSub_I hx, hfix]
  have hrankIJ : Module.finrank (ZMod 2) ↥(I ⊔ J) = 2 * Module.finrank (ZMod 2) I := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq I J
    rw [hIJ, finrank_bot, c.finrank_eq hJ] at h1
    omega
  have hrankM : Module.finrank (ZMod 2) ↥M = Module.finrank (ZMod 2) I := by
    have h1 : Module.finrank (ZMod 2) ↥M =
        Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) ↥(I ⊔ J) :=
      LinearMap.BilinForm.finrank_orthogonal c.hyp.toG101Hyp.nondegenerate' _
    omega
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hrankM
    have := c.two_lt
    omega
  obtain ⟨J', hJ'le, hJ'irr⟩ := exists_isIrr_le hMinv hMne
  have hJ'plus : IrrPlus H J' := hJ'irr.irrPlus c.fixedSpace_H
  have hJ'M : J' = M :=
    Submodule.eq_of_le_of_finrank_eq hJ'le (by rw [c.finrank_eq hJ'plus, hrankM])
  rw [hJ'M] at hJ'plus
  refine ⟨M, hJ'plus, LinearMap.BilinForm.orthogonal_le le_sup_left, ?_, hxM⟩
  intro hMI
  have hle : I ≤ B.orthogonal J := by
    have : I ≤ M := hMI ▸ le_rfl
    exact this.trans (LinearMap.BilinForm.orthogonal_le le_sup_right)
  have : I ⊓ B.orthogonal J = I := inf_eq_left.2 hle
  rw [hIperp] at this
  exact hirrI.ne_bot this.symm

theorem exists_fixed (hE : G119E11Use) {x : GLV V} (hx : x ∈ X) :
    ∃ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J ∧ J ≤ B.orthogonal I ∧ J ≠ I ∧
      conjSub x J = J := by
  classical
  set H := normalClosure Γ L with hH
  obtain ⟨F, hFfield, hFfin, hFchar, U, hUgrp, hUmod, hUfin, ψ, ha, hc, hd⟩ :=
    hE V H I c.homog c.irrPlus c.fixedSpace_H c.hyp.sSup_isIrr
  have hxnorm : x ∈ Subgroup.normalizer (H : Set (GLV V)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    refine ⟨fun hh => c.X_normalizes x hx h hh, fun hh => ?_⟩
    have h1 := normalClosure_normal Γ L x⁻¹ (Subgroup.inv_mem _ (c.X_le hx)) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rw [e] at h1
    exact h1
  obtain ⟨τ, σ, hσ, hψσ⟩ := hc x hxnorm
  set ρ := Projectivization.map σ hσ with hρ
  have hρJ : ∀ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J),
      ψ ⟨conjSub x J, c.irrPlus_conj hJ hx⟩ = ρ (ψ ⟨J, hJ⟩) := fun J hJ =>
    hψσ J hJ (c.irrPlus_conj hJ hx)
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    obtain ⟨⟨J, hJ⟩, rfl⟩ := ψ.surjective p
    rw [← hρJ J hJ, ← hρJ (conjSub x J) (c.irrPlus_conj hJ hx)]
    congr 1
    apply Subtype.ext
    show conjSub x (conjSub x J) = J
    rw [← conjSub_mul, c.X_sq hx, conjSub_one]
  set p₀ : Projectivization F U := ψ ⟨I, c.irrPlus⟩ with hp₀
  have hρp₀ : ρ p₀ = p₀ := by
    rw [hp₀, ← hρJ I c.irrPlus]
    congr 1
    exact Subtype.ext (c.conjSub_I hx)
  have hσne : ∀ v : U, v ≠ 0 → σ v ≠ 0 := fun v hv h => hv (hσ (by rw [h, map_zero]))
  have hρmk : ∀ (v : U) (hv : v ≠ 0),
      ρ (Projectivization.mk F v hv) = Projectivization.mk F (σ v) (hσne v hv) := fun v hv => rfl
  have hinv : ∀ s : U, ∃ a : F, σ (σ s) = a • s := by
    intro s
    by_cases hs : s = 0
    · exact ⟨0, by simp [hs]⟩
    · have h := hρρ (Projectivization.mk F s hs)
      rw [hρmk, hρmk] at h
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ hs).1 h
      exact ⟨a, ha.symm⟩
  set v₀ : U := p₀.rep with hv₀
  have hv₀0 : v₀ ≠ 0 := p₀.rep_nonzero
  have hp₀mk : Projectivization.mk F v₀ hv₀0 = p₀ := Projectivization.mk_rep p₀
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : F, σ v₀ = c₀ • v₀ := by
    have h : ρ (Projectivization.mk F v₀ hv₀0) = Projectivization.mk F v₀ hv₀0 := by
      rw [hp₀mk]
      exact hρp₀
    rw [hρmk] at h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' F _ _ _ hv₀0).1 h
    exact ⟨a, ha.symm⟩
  have key : ∀ S : Submodule F U, (∀ s ∈ S, σ s ∈ S) → 3 ≤ Module.finrank F S →
      p₀.submodule ≤ S → ∃ (J : Submodule (ZMod 2) V) (hJ : IrrPlus H J), J ≠ I ∧
        conjSub x J = J ∧ (ψ ⟨J, hJ⟩).submodule ≤ S := by
    intro S hS hdim hp₀S
    have hv₀S : v₀ ∈ S :=
      hp₀S (by rw [Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _)
    obtain ⟨v, hvS, hvnot, c', hc'⟩ :=
      g119_exists_second_eigenline τ σ hσ hS (fun s _ => hinv s) hdim hv₀S hv₀0 hc₀
    have hv0 : v ≠ 0 := fun h => hvnot (h ▸ Submodule.zero_mem _)
    set p : Projectivization F U := Projectivization.mk F v hv0 with hp
    have hρp : ρ p = p := by
      rw [hp, hρmk]
      exact (Projectivization.mk_eq_mk_iff' F _ _ _ hv0).2 ⟨c', hc'.symm⟩
    obtain ⟨⟨J, hJ⟩, hψJ⟩ := ψ.surjective p
    refine ⟨J, hJ, ?_, ?_, ?_⟩
    · intro hJI
      have h1 : p = p₀ := by
        rw [← hψJ, hp₀]
        congr 1
        exact Subtype.ext hJI
      have h' : Projectivization.mk F v hv0 = Projectivization.mk F v₀ hv₀0 := by
        rw [hp₀mk]
        exact h1
      obtain ⟨a, ha'⟩ := (Projectivization.mk_eq_mk_iff' F _ _ hv0 hv₀0).1 h'
      exact hvnot (ha' ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v₀))
    · have h1 := hρJ J hJ
      rw [hψJ, hρp] at h1
      exact congrArg Subtype.val (ψ.injective (h1.trans hψJ.symm))
    · rw [hψJ, hp, Projectivization.submodule_mk]
      exact (Submodule.span_singleton_le_iff_mem _ _).2 hvS
  have hkge : 3 ≤ Module.finrank F U := by
    by_contra hlt
    have h1 : Module.finrank F U * Module.finrank (ZMod 2) I ≤ 2 * Module.finrank (ZMod 2) I :=
      Nat.mul_le_mul_right _ (by omega)
    have := c.rank
    omega
  by_cases hk3 : Module.finrank F U = 3
  ·
    obtain ⟨J, hJ, hne, hfix, -⟩ :=
      key ⊤ (fun _ _ => Submodule.mem_top) (by rw [finrank_top]; omega) le_top
    by_cases hle : J ≤ B.orthogonal I
    · exact ⟨J, hJ, hle, hne, hfix⟩
    · rw [hk3] at ha
      exact c.exists_of_not_le_orthogonal ha.symm hx hJ hne hfix hle
  ·
    obtain ⟨S, hSiff, hSdim⟩ := hd (B.orthogonal I) c.invariant_orthogonal_H
    have hp₀S : p₀.submodule ≤ S := (hSiff I c.irrPlus).1 c.le_orthogonal
    have hS : ∀ s ∈ S, σ s ∈ S := by
      intro s hs
      by_cases hs0 : s = 0
      · simp [hs0]
      · have hq : (Projectivization.mk F s hs0).submodule ≤ S := by
          rw [Projectivization.submodule_mk]
          exact (Submodule.span_singleton_le_iff_mem _ _).2 hs
        obtain ⟨⟨J, hJ⟩, hψJ⟩ := ψ.surjective (Projectivization.mk F s hs0)
        have hJM : J ≤ B.orthogonal I := (hSiff J hJ).2 (by rw [hψJ]; exact hq)
        have hxJM : conjSub x J ≤ B.orthogonal I :=
          (conjSub_mono x hJM).trans (c.invariant_orthogonal_X.conjSub_eq hx).le
        have h1 := (hSiff (conjSub x J) (c.irrPlus_conj hJ hx)).1 hxJM
        rw [hρJ J hJ, hψJ, hρmk, Projectivization.submodule_mk] at h1
        exact (Submodule.span_singleton_le_iff_mem _ _).1 h1
    have hdim : 3 ≤ Module.finrank F S := by
      by_contra hlt
      have h1 : Module.finrank F S * Module.finrank (ZMod 2) I ≤ 2 * Module.finrank (ZMod 2) I :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : 4 * Module.finrank (ZMod 2) I ≤ Module.finrank F U * Module.finrank (ZMod 2) I :=
        Nat.mul_le_mul_right _ (by omega)
      have h3 := c.finrank_orthogonal
      have := c.two_lt
      omega
    obtain ⟨J, hJ, hne, hfix, hJS⟩ := key S hS hdim hp₀S
    exact ⟨J, hJ, (hSiff J hJ).2 hJS, hne, hfix⟩

end G119Ctx

end G11

end CFSG.Quasithin

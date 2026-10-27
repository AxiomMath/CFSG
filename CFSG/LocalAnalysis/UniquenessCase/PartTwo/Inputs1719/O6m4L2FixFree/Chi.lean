module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

private lemma exists_mem_notMem_span_singleton_F07 {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {W : Submodule K V}
    (hW2 : Module.finrank K ↥W = 2) (v : V) :
    ∃ w ∈ W, w ∉ Submodule.span K ({v} : Set V) := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hle : W ≤ Submodule.span K ({v} : Set V) := fun x hx => h x hx
  have h1 : Module.finrank K ↥W ≤ Module.finrank K ↥(Submodule.span K ({v} : Set V)) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank K ↥(Submodule.span K ({v} : Set V)) ≤ 1 := by
    simpa using finrank_span_le_card (R := K) ({v} : Set V)
  rw [hW2] at h1
  exact absurd (h1.trans h2) (by decide)

private lemma injective_of_monoidHom_apply_F07 {K V H : Type} [Field K] [AddCommGroup V]
    [Module K V] [Group H] (ρ : H →* Module.End K V) (g : H) : Function.Injective (ρ g) := by
  have hleft : Function.LeftInverse (ρ g⁻¹) (ρ g) := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  exact hleft.injective

private lemma sup_span_eq_of_notMem_F07 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} (hW2 : Module.finrank K ↥W = 2) {v w : V}
    (hvW : v ∈ W) (hv0 : v ≠ 0) (hwW : w ∈ W)
    (hwL : w ∉ Submodule.span K ({v} : Set V)) :
    Submodule.span K ({v} : Set V) ⊔ Submodule.span K ({w} : Set V) = W := by
  have hw0 : w ≠ 0 := fun h => hwL (by rw [h]; exact Submodule.zero_mem _)
  have hinf : Submodule.span K ({v} : Set V) ⊓ Submodule.span K ({w} : Set V) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨hyL, hyM⟩ := Submodule.mem_inf.mp hy
    rw [Submodule.mem_span_singleton] at hyL hyM
    obtain ⟨a, ha⟩ := hyL
    obtain ⟨b, hb⟩ := hyM
    by_cases hb0 : b = 0
    · rw [hb0, zero_smul] at hb; exact hb.symm
    · exfalso
      apply hwL
      rw [Submodule.mem_span_singleton]
      refine ⟨b⁻¹ * a, ?_⟩
      rw [mul_smul, ha, ← hb, inv_smul_smul₀ hb0]
  have hfin : Module.finrank K ↥(Submodule.span K ({v} : Set V) ⊔
      Submodule.span K ({w} : Set V)) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K ({v} : Set V))
      (Submodule.span K ({w} : Set V))
    rw [hinf, finrank_bot, add_zero] at h
    have hL1 : Module.finrank K ↥(Submodule.span K ({v} : Set V)) = 1 :=
      finrank_span_singleton hv0
    have hM1 : Module.finrank K ↥(Submodule.span K ({w} : Set V)) = 1 :=
      finrank_span_singleton hw0
    rw [hL1, hM1] at h
    simpa using h
  have hle : Submodule.span K ({v} : Set V) ⊔ Submodule.span K ({w} : Set V) ≤ W := by
    apply sup_le
    · rw [Submodule.span_singleton_le_iff_mem]; exact hvW
    · rw [Submodule.span_singleton_le_iff_mem]; exact hwW
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hW2])

private lemma map_mem_of_maps_generators_F07 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {W L M : Submodule K V} {v w : V} {F : V →ₗ[K] V}
    (hL : L = Submodule.span K ({v} : Set V)) (hM : M = Submodule.span K ({w} : Set V))
    (hW : L ⊔ M = W) (hFv : F v ∈ L) (hFw : F w ∈ L) : ∀ x ∈ W, F x ∈ L := by
  intro x hx
  have hx' : x ∈ L ⊔ M := by rw [hW]; exact hx
  rw [Submodule.mem_sup] at hx'
  obtain ⟨p, hpL, q, hqM, hpq⟩ := hx'
  have hpmem : F p ∈ L := by
    rw [hL, Submodule.mem_span_singleton] at hpL
    obtain ⟨s, rfl⟩ := hpL
    rw [map_smul]
    exact Submodule.smul_mem _ _ hFv
  have hqmem : F q ∈ L := by
    rw [hM, Submodule.mem_span_singleton] at hqM
    obtain ⟨t, rfl⟩ := hqM
    rw [map_smul]
    exact Submodule.smul_mem _ _ hFw
  rw [← hpq, map_add]
  exact Submodule.add_mem _ hpmem hqmem

private lemma sub_mul_smul_mem_span_F07 {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (ρ : H →* Module.End K V) {W : Submodule K V} {v : V} {g h : H} {cg ch : Kˣ}
    (hgv : ρ g v = v)
    (hcg : ∀ x ∈ W, ρ g x - (cg : K) • x ∈ Submodule.span K ({v} : Set V))
    (hch : ∀ x ∈ W, ρ h x - (ch : K) • x ∈ Submodule.span K ({v} : Set V)) :
    ∀ x ∈ W, ρ (g * h) x - ((cg : K) * (ch : K)) • x ∈ Submodule.span K ({v} : Set V) := by
  set L : Submodule K V := Submodule.span K ({v} : Set V) with hL
  set Fg : V →ₗ[K] V := ρ g - (cg : K) • (1 : Module.End K V) with hFg
  set Fh : V →ₗ[K] V := ρ h - (ch : K) • (1 : Module.End K V) with hFh
  have hvL : v ∈ L := by rw [hL]; exact Submodule.subset_span (Set.mem_singleton v)
  have hρgL : ∀ y ∈ L, ρ g y ∈ L := by
    intro y hy
    rw [hL, Submodule.mem_span_singleton] at hy
    obtain ⟨s, rfl⟩ := hy
    rw [map_smul, hgv]
    exact Submodule.smul_mem _ _ hvL
  intro x hx
  have hFhx : Fh x ∈ L := by
    rw [hL, hFh]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact hch x hx
  have hFgx : Fg x ∈ L := by
    rw [hL, hFg]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact hcg x hx
  have hρh : ρ h x = Fh x + (ch : K) • x := by
    rw [hFh, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_add_cancel]
  have hρg : ρ g x = Fg x + (cg : K) • x := by
    rw [hFg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_add_cancel]
  have hkey : ρ (g * h) x
      = ρ g (Fh x) + (ch : K) • Fg x + ((cg : K) * (ch : K)) • x := by
    calc ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ g (Fh x + (ch : K) • x) := by rw [hρh]
      _ = ρ g (Fh x) + (ch : K) • ρ g x := by rw [map_add, map_smul]
      _ = ρ g (Fh x) + (ch : K) • (Fg x + (cg : K) • x) := by rw [hρg]
      _ = ρ g (Fh x) + (ch : K) • Fg x + ((ch : K) * (cg : K)) • x := by
            rw [smul_add, smul_smul, add_assoc]
      _ = ρ g (Fh x) + (ch : K) • Fg x + ((cg : K) * (ch : K)) • x := by
            rw [mul_comm (ch : K) (cg : K)]
  rw [hkey, add_sub_cancel_right]
  exact Submodule.add_mem _ (hρgL (Fh x) hFhx) (Submodule.smul_mem _ _ hFgx)

theorem eq_of_smul_sub_mem_span {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} (hW2 : Module.finrank K ↥W = 2) {v : V}
    {T : V →ₗ[K] V} {c c' : K} (hc : ∀ x ∈ W, T x - c • x ∈ Submodule.span K {v})
    (hc' : ∀ x ∈ W, T x - c' • x ∈ Submodule.span K {v}) : c = c' := by
  obtain ⟨w, hwW, hwL⟩ := exists_mem_notMem_span_singleton_F07 hW2 v
  by_contra hcc
  have hdiff : (T w - c' • w) - (T w - c • w) = (c - c') • w := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]
  have hmem : (c - c') • w ∈ Submodule.span K ({v} : Set V) := by
    rw [← hdiff]
    exact Submodule.sub_mem _ (hc' w hwW) (hc w hwW)
  have hw' : w = (c - c')⁻¹ • ((c - c') • w) := by
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hcc), one_smul]
  exact hwL (by rw [hw']; exact Submodule.smul_mem _ _ hmem)

theorem exists_unit_smul_sub_mem_span {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group H] (ρ : H →* Module.End K V) {W : Submodule K V}
    (hW2 : Module.finrank K ↥W = 2) {v : V} (hvW : v ∈ W) (hv0 : v ≠ 0) {g : H}
    (hgv : ρ g v = v) (hgW : ∀ w ∈ W, ρ g w ∈ W) :
    ∃ c : Kˣ, ∀ x ∈ W, ρ g x - (c : K) • x ∈ Submodule.span K {v} := by
  obtain ⟨w, hwW, hwL⟩ := exists_mem_notMem_span_singleton_F07 hW2 v
  have hW0 := sup_span_eq_of_notMem_F07 hW2 hvW hv0 hwW hwL
  set L : Submodule K V := Submodule.span K ({v} : Set V) with hL
  set M : Submodule K V := Submodule.span K ({w} : Set V) with hM
  have hW : L ⊔ M = W := by rw [hL, hM]; exact hW0
  have hρw' : ρ g w ∈ L ⊔ M := by rw [hW]; exact hgW w hwW
  rw [Submodule.mem_sup] at hρw'
  obtain ⟨p, hpL, q, hqM, hpq⟩ := hρw'
  rw [hL, Submodule.mem_span_singleton] at hpL
  rw [hM, Submodule.mem_span_singleton] at hqM
  obtain ⟨a, ha⟩ := hpL
  obtain ⟨b, hb⟩ := hqM
  set F : V →ₗ[K] V := ρ g - b • (1 : Module.End K V) with hF
  have hFv : F v ∈ L := by
    rw [hF, hL]
    have h1 : (ρ g - b • (1 : Module.End K V)) v = (1 - b) • v := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hgv, sub_smul,
        one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hFw : F w ∈ L := by
    rw [hF]
    have h1 : (ρ g - b • (1 : Module.End K V)) w = a • v := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, ← hpq, ← ha, ← hb,
        add_sub_cancel_right]
    rw [h1, hL]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hFW : ∀ x ∈ W, F x ∈ L := map_mem_of_maps_generators_F07 hL hM hW hFv hFw
  have hb0 : b ≠ 0 := by
    intro hb0
    have hw_eq : ρ g w = a • v := by
      rw [← hpq, ← ha, ← hb, hb0, zero_smul, add_zero]
    have hinj : Function.Injective (ρ g) := injective_of_monoidHom_apply_F07 ρ g
    have : w = a • v := hinj (by rw [map_smul, hgv, hw_eq])
    apply hwL
    rw [this, Submodule.mem_span_singleton]
    exact ⟨a, rfl⟩
  refine ⟨Units.mk0 b hb0, fun x hx => ?_⟩
  exact hFW x hx

theorem exists_chi {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group H] (ρ : H →* Module.End K V) {W : Submodule K V} (hW2 : Module.finrank K ↥W = 2)
    {v : V} (hvW : v ∈ W) (hv0 : v ≠ 0) (J : Subgroup H) (hJv : ∀ g ∈ J, ρ g v = v)
    (hJW : ∀ g ∈ J, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ χ : ↥J →* Kˣ, ∀ g : ↥J, ∀ x ∈ W, ρ ↑g x - (χ g : K) • x ∈ Submodule.span K {v} := by
  choose c hc using fun g : ↥J =>
    exists_unit_smul_sub_mem_span ρ hW2 hvW hv0 (hJv g g.2) (hJW g g.2)
  have hmul : ∀ g h : ↥J, c (g * h) = c g * c h := by
    intro g h
    refine Units.ext ?_
    rw [Units.val_mul]
    exact eq_of_smul_sub_mem_span hW2 (hc (g * h))
      (sub_mul_smul_mem_span_F07 ρ (hJv g g.2)
        (fun x hx => hc g x hx) (fun x hx => hc h x hx))
  exact ⟨MonoidHom.mk' c hmul, fun g x hx => hc g x hx⟩

theorem sub_mem_span_of_chi_eq_one {K V H : Type} [Field K] [AddCommGroup V] [Module K V]
    [Group H] (ρ : H →* Module.End K V) {W : Submodule K V} {v : V} {J : Subgroup H}
    {χ : ↥J →* Kˣ}
    (hχ : ∀ g : ↥J, ∀ x ∈ W, ρ ↑g x - (χ g : K) • x ∈ Submodule.span K {v}) {g : ↥J}
    (hg : χ g = 1) : ∀ x ∈ W, ρ ↑g x - x ∈ Submodule.span K {v} := by
  intro x hx
  have h := hχ g x hx
  rwa [hg, Units.val_one, one_smul] at h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

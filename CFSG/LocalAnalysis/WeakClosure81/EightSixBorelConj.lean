module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped Pointwise

theorem borel86_conj_exists_mem_normalizer_conj_ne {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) {t t₁ d₀ : X}
    (hP : ∀ x ∈ (P : Subgroup X), x * t = t * x) (hd₀ : d₀ * t * d₀⁻¹ = t₁)
    (hC : ∀ y : X, y * t = t * y ↔ y * t₁ = t₁ * y) (hne : t₁ ≠ t) :
    ∃ d ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), d * t * d⁻¹ ≠ t := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({t} : Set X)
  have hPC : (P : Subgroup X) ≤ C := by
    intro x hx
    change x ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hP x hx
  let Q : Sylow p X := d₀ • P
  have hQC : (Q : Subgroup X) ≤ C := by
    intro y hy
    change y ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply (hC y).mpr
    have hy' : y ∈ MulAut.conj d₀ • (P : Subgroup X) := by
      change y ∈ ((d₀ • P : Sylow p X) : Subgroup X) at hy
      rwa [Sylow.coe_subgroup_smul] at hy
    obtain ⟨x, hxP, hxy⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj d₀) (P : Subgroup X)).mp hy'
    rw [MulAut.smul_def, MulAut.conj_apply] at hxy
    rw [← hxy, ← hd₀]
    calc d₀ * x * d₀⁻¹ * (d₀ * t * d₀⁻¹) = d₀ * (x * t) * d₀⁻¹ := by group
      _ = d₀ * (t * x) * d₀⁻¹ := by rw [hP x hxP]
      _ = (d₀ * t * d₀⁻¹) * (d₀ * x * d₀⁻¹) := by group
  let PC : Sylow p C := P.subtype hPC
  let QC : Sylow p C := Q.subtype hQC
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C QC PC
  have hc' : (c : X) • Q = P := by
    have hsub : (c • Q).subtype (Sylow.smul_le hQC c) = P.subtype hPC := by
      rw [← Sylow.smul_subtype (P := Q) hQC c]
      exact hc
    simpa only [Subgroup.smul_def] using Sylow.subtype_injective (N := C) hsub
  have hmem : (c : X) * d₀ ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    have hsmul : ((c : X) * d₀) • P = P := by
      rw [mul_smul]
      exact hc'
    exact Sylow.smul_eq_iff_mem_normalizer.mp hsmul
  have hct : (c : X) * t = t * (c : X) := Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hct₁ : (c : X) * t₁ = t₁ * (c : X) := (hC (c : X)).mp hct
  refine ⟨(c : X) * d₀, hmem, ?_⟩
  intro hfix
  have hdt : (c : X) * d₀ * t * ((c : X) * d₀)⁻¹ = t₁ := by
    rw [mul_inv_rev]
    calc (c : X) * d₀ * t * (d₀⁻¹ * (c : X)⁻¹)
        = (c : X) * (d₀ * t * d₀⁻¹) * (c : X)⁻¹ := by group
      _ = (c : X) * t₁ * (c : X)⁻¹ := by rw [hd₀]
      _ = t₁ := by rw [hct₁]; group
  exact hne (hdt.symm.trans hfix)

theorem borel86_conj_eq_one_of_forall_fix {S : Type} [Group S] [IsSimpleGroup S] {t : S}
    (ht : t ≠ 1) (α : MulAut S) (hα : ∀ s : S, α (s * t * s⁻¹) = s * t * s⁻¹) : α = 1 := by
  have hEq : Set.EqOn α.toMonoidHom (MonoidHom.id S)
      (Group.conjugatesOfSet ({t} : Set S)) := by
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    show α x = x
    rw [← hc]
    exact hα c
  have hle : Subgroup.normalClosure ({t} : Set S) ≤
      MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id S) :=
    MonoidHom.eqOn_closure hEq
  have htop : Subgroup.normalClosure ({t} : Set S) = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.normalClosure ({t} : Set S)) with h | h
    · exfalso
      have htmem : t ∈ Subgroup.normalClosure ({t} : Set S) :=
        Subgroup.subset_normalClosure (Set.mem_singleton t)
      rw [h] at htmem
      exact ht (Subgroup.mem_bot.mp htmem)
    · exact h
  have hHtop : MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id S) = ⊤ :=
    le_antisymm le_top (htop ▸ hle)
  ext x
  have hx : α x = x :=
    (show x ∈ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id S) from by rw [hHtop]; trivial)
  simpa only [MulAut.one_apply] using hx

end CFSG.LocalAnalysis.WeakClosure81

end

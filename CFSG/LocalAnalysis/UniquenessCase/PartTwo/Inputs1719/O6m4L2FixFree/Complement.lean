module

public import CFSG.LieType.BorelTits.Families
import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open CFSG.LieType.BorelTits

private lemma polar_restrict_F06 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) (A : Submodule K V) (x y : ↥A) :
    QuadraticMap.polar (fun a : ↥A => Φ.Q (a : V)) x y = Φ.polar.β (x : V) (y : V) := by
  simp only [QuadraticMap.polar, Submodule.coe_add, Φ.Q_add]
  ring

theorem exists_complement_in_perp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) {W : Submodule K V} (hW : Φ.IsTotallySingular W) :
    ∃ A : Submodule K V, Disjoint W A ∧ W ⊔ A = Φ.polar.perp W := by
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl W
  refine ⟨D ⊓ Φ.polar.perp W, hD.disjoint.mono_right inf_le_left, ?_⟩
  have hWP : W ≤ Φ.polar.perp W := hW.isTotallyIsotropic
  rw [← sup_inf_assoc_of_le D hWP, hD.sup_eq_top, top_inf_eq]

theorem finrank_complement_in_perp {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Φ : QuadForm K V) {W A : Submodule K V} (hd : Disjoint W A)
    (hs : W ⊔ A = Φ.polar.perp W) :
    Module.finrank K ↥A + 2 * Module.finrank K ↥W = Module.finrank K V := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W A
  rw [hs, disjoint_iff.mp hd, finrank_bot, add_zero] at h1
  have h2 := Φ.polar.finrank_perp W
  omega

theorem eq_zero_of_polar_eq_zero_complement {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Φ : QuadForm K V) {W A : Submodule K V}
    (hd : Disjoint W A) (hs : W ⊔ A = Φ.polar.perp W) {a : V} (ha : a ∈ A)
    (h : ∀ a' ∈ A, Φ.polar.β a a' = 0) : a = 0 := by
  have haP : a ∈ Φ.polar.perp W := by
    rw [← hs]
    exact Submodule.mem_sup_right ha
  have hmem : a ∈ Φ.polar.perp (Φ.polar.perp W) := by
    rw [ReflForm.mem_perp]
    intro p hp
    rw [← hs] at hp
    obtain ⟨w, hw, a', ha', hwa⟩ := Submodule.mem_sup.mp hp
    rw [← hwa, Φ.polar.add_left, haP w hw, Φ.polar_symm a' a, h a' ha', zero_add]
  have haW : a ∈ W := by
    rw [← Φ.polar.perp_perp W]
    exact hmem
  have hamem : a ∈ W ⊓ A := ⟨haW, ha⟩
  rwa [disjoint_iff.mp hd, Submodule.mem_bot] at hamem

theorem exists_quadraticForm_restrict {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) (A : Submodule K V) :
    ∃ q : QuadraticForm K ↥A, (∀ a : ↥A, q a = Φ.Q ↑a) ∧
      ∀ a a' : ↥A, QuadraticMap.polar q a a' = Φ.polar.β ↑a ↑a' := by
  refine ⟨QuadraticMap.ofPolar (fun a : ↥A => Φ.Q (a : V)) ?_ ?_ ?_, ?_, ?_⟩
  · intro c x
    rw [Submodule.coe_smul, Φ.Q_smul, smul_eq_mul]
    ring
  · intro x x' y
    simp only [polar_restrict_F06, Submodule.coe_add, Φ.polar.add_left]
  · intro c x y
    rw [polar_restrict_F06, polar_restrict_F06, Submodule.coe_smul, Φ.polar.smul_left,
      Φ.polar_σ]
    simp
  · intro a
    rfl
  · intro a a'
    exact polar_restrict_F06 Φ A a a'

theorem nondegenerate_polarBilin_complement {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Φ : QuadForm K V) {W A : Submodule K V}
    (hd : Disjoint W A) (hs : W ⊔ A = Φ.polar.perp W) (q : QuadraticForm K ↥A)
    (hq : ∀ a a' : ↥A, QuadraticMap.polar q a a' = Φ.polar.β ↑a ↑a') :
    (QuadraticMap.polarBilin q).Nondegenerate := by
  apply CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall
  intro v hv
  apply Subtype.ext
  apply eq_zero_of_polar_eq_zero_complement Φ hd hs v.2
  intro a' ha'
  have h := hq v ⟨a', ha'⟩
  rw [hv ⟨a', ha'⟩] at h
  exact h.symm

theorem exists_projection_complement {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : QuadForm K V) {W A : Submodule K V} (hd : Disjoint W A)
    (hs : W ⊔ A = Φ.polar.perp W) :
    ∃ π : V →ₗ[K] ↥A, (∀ a : ↥A, π ↑a = a) ∧ (∀ w ∈ W, π w = 0) ∧
      ∀ x ∈ Φ.polar.perp W, (↑(π x) : V) - x ∈ W := by
  have hWP : W ≤ Φ.polar.perp W := by rw [← hs]; exact le_sup_left
  have hAP : A ≤ Φ.polar.perp W := by rw [← hs]; exact le_sup_right
  obtain ⟨E, hE⟩ := Submodule.exists_isCompl (Φ.polar.perp W)
  have hdA : Disjoint A (W ⊔ E) := by
    rw [Submodule.disjoint_def]
    intro a haA hwe
    obtain ⟨w, hw, e, he, hwe'⟩ := Submodule.mem_sup.mp hwe
    have heP : e ∈ Φ.polar.perp W := by
      have heq : e = a - w := by rw [← hwe', add_sub_cancel_left]
      rw [heq]
      exact Submodule.sub_mem _ (hAP haA) (hWP hw)
    have he0 : e = 0 := by
      have hem : e ∈ (Φ.polar.perp W) ⊓ E := ⟨heP, he⟩
      rwa [disjoint_iff.mp hE.disjoint, Submodule.mem_bot] at hem
    have haW : a ∈ W := by
      rw [← hwe', he0, add_zero]
      exact hw
    have hamem : a ∈ W ⊓ A := ⟨haW, haA⟩
    rwa [disjoint_iff.mp hd, Submodule.mem_bot] at hamem
  have hsupA : A ⊔ (W ⊔ E) = ⊤ := by
    rw [← sup_assoc, sup_comm A W, hs]
    exact hE.sup_eq_top
  have hcompl : IsCompl A (W ⊔ E) := IsCompl.of_eq (disjoint_iff.mp hdA) hsupA
  refine ⟨Submodule.projectionOnto A (W ⊔ E) hcompl, ?_, ?_, ?_⟩
  · intro a
    exact Submodule.projectionOnto_apply_left hcompl a
  · intro w hw
    exact Submodule.projectionOnto_apply_right hcompl ⟨w, Submodule.mem_sup_left hw⟩
  · intro x hx
    have hx' : x ∈ W ⊔ A := by rw [hs]; exact hx
    obtain ⟨w, hw, a, ha, hwa⟩ := Submodule.mem_sup.mp hx'
    have hπ : Submodule.projectionOnto A (W ⊔ E) hcompl x = ⟨a, ha⟩ := by
      rw [← hwa, map_add]
      rw [show Submodule.projectionOnto A (W ⊔ E) hcompl w = 0 from
            Submodule.projectionOnto_apply_right hcompl ⟨w, Submodule.mem_sup_left hw⟩,
          show Submodule.projectionOnto A (W ⊔ E) hcompl a = ⟨a, ha⟩ from
            Submodule.projectionOnto_apply_left hcompl ⟨a, ha⟩]
      simp
    have hmem : (↑(Submodule.projectionOnto A (W ⊔ E) hcompl x) : V) - x = -w := by
      rw [hπ, ← hwa, Submodule.coe_mk]
      abel
    rw [hmem]
    exact Submodule.neg_mem W hw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

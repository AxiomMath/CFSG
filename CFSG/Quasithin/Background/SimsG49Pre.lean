module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.SimsG4.G49

section Pre

variable {Γ M : Type*} [Group Γ] [Group M] {H : Subgroup Γ} (f : ↥H →* M)

@[expose] def pre (S : Subgroup M) : Subgroup Γ :=
  (S.comap f).map H.subtype

variable {f}

theorem mem_pre {S : Subgroup M} {x : Γ} : x ∈ pre f S ↔ ∃ hx : x ∈ H, f ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx, rfl⟩

variable (f) in
theorem pre_le (S : Subgroup M) : pre f S ≤ H :=
  Subgroup.map_subtype_le _

theorem nonempty_mulEquiv_pre (hf : Function.Injective f) {S : Subgroup M} (hS : S ≤ f.range) :
    Nonempty (↥(pre f S) ≃* ↥S) :=
  ⟨(Subgroup.equivMapOfInjective (S.comap f) H.subtype H.subtype_injective).symm.trans <|
    (Subgroup.equivMapOfInjective (S.comap f) f hf).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hS))⟩

theorem conj_mem_pre {S : Subgroup M} (hS : ∀ y ∈ f.range, ∀ s ∈ S, y * s * y⁻¹ ∈ S) :
    ∀ g ∈ H, ∀ n ∈ pre f S, g * n * g⁻¹ ∈ pre f S := by
  intro g hg n hn
  obtain ⟨hnH, hfn⟩ := mem_pre.mp hn
  refine mem_pre.mpr ⟨H.mul_mem (H.mul_mem hg hnH) (H.inv_mem hg), ?_⟩
  have e : f ⟨g * n * g⁻¹, H.mul_mem (H.mul_mem hg hnH) (H.inv_mem hg)⟩ =
      f ⟨g, hg⟩ * f ⟨n, hnH⟩ * (f ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact hS _ ⟨_, rfl⟩ _ hfn

omit [Group Γ] in
theorem conj_mem_of_index_two {O S : Subgroup M} (hSO : S ≤ O)
    (hidx : (S.subgroupOf O).index = 2) : ∀ y ∈ O, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
  intro y hy s hs
  haveI := Subgroup.normal_of_index_eq_two hidx
  exact (inferInstance : (S.subgroupOf O).Normal).conj_mem ⟨s, hSO hs⟩ hs ⟨y, hy⟩

theorem commute_pre (hf : Function.Injective f) {S₁ S₂ : Subgroup M}
    (hcomm : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) :
    ∀ x ∈ pre f S₁, ∀ y ∈ pre f S₂, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hxH, hfx⟩ := mem_pre.mp hx
  obtain ⟨hyH, hfy⟩ := mem_pre.mp hy
  have h := hcomm _ hfx _ hfy
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (hf h)

theorem pre_sup {S₁ S₂ : Subgroup M} (h₁ : S₁ ≤ f.range) (h₂ : S₂ ≤ f.range) :
    pre f (S₁ ⊔ S₂) = pre f S₁ ⊔ pre f S₂ := by
  rw [pre, pre, pre, ← Subgroup.comap_sup_eq_of_le_range f h₁ h₂, Subgroup.map_sup]

theorem pre_inf_eq_bot (hf : Function.Injective f) {S₁ S₂ : Subgroup M} (h : S₁ ⊓ S₂ = ⊥) :
    pre f S₁ ⊓ pre f S₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxH, hf₁⟩ := mem_pre.mp hx₁
  obtain ⟨hxH', hf₂⟩ := mem_pre.mp hx₂
  have h1 : f ⟨x, hxH⟩ = 1 := by
    have h12 := Subgroup.mem_inf.mpr ⟨hf₁, hf₂⟩
    rw [h, Subgroup.mem_bot] at h12
    exact h12
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (hf (h1.trans (map_one f).symm)))

theorem eq_one_of_commute_pre (hf : Function.Injective f) {S : Subgroup M} (hS : S ≤ f.range)
    (hC : ∀ y ∈ f.range, (∀ s ∈ S, y * s = s * y) → y = 1) :
    ∀ g ∈ H, (∀ n ∈ pre f S, g * n = n * g) → g = 1 := by
  intro g hg hgc
  have h1 : f ⟨g, hg⟩ = 1 := by
    refine hC _ ⟨_, rfl⟩ fun s hs => ?_
    obtain ⟨n, rfl⟩ := hS hs
    have h := hgc n (mem_pre.mpr ⟨n.2, hs⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext h)
  exact congrArg Subtype.val (hf (h1.trans (map_one f).symm))

theorem mem_pre_or_mul_mem_pre {S : Subgroup M} (hS : S ≤ f.range)
    (hidx : (S.subgroupOf f.range).index = 2) {t : Γ} (ht : t ∈ H) (htS : f ⟨t, ht⟩ ∉ S) :
    ∀ h ∈ H, h ∈ pre f S ∨ h * t ∈ pre f S := by
  intro h hh
  by_cases hfh : f ⟨h, hh⟩ ∈ S
  · exact Or.inl (mem_pre.mpr ⟨hh, hfh⟩)
  · refine Or.inr (mem_pre.mpr ⟨H.mul_mem hh ht, ?_⟩)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨f ⟨h, hh⟩, ⟨_, rfl⟩⟩) (b := ⟨f ⟨t, ht⟩, ⟨_, rfl⟩⟩)).mpr
      ⟨fun ha => absurd ha hfh, fun hb => absurd hb htS⟩
    have e : f ⟨h * t, H.mul_mem hh ht⟩ = f ⟨h, hh⟩ * f ⟨t, ht⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact key

end Pre

theorem nonabelian_of_mulEquiv {Γ X : Type*} [Group Γ] [Group X] {N : Subgroup Γ}
    (e : ↥N ≃* X) (hX : ∃ a b : X, a * b ≠ b * a) : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := hX
  refine ⟨e.symm a, (e.symm a).2, e.symm b, (e.symm b).2, fun h => hab ?_⟩
  have h' : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
  rw [← map_mul, ← map_mul] at h'
  exact e.symm.injective h'

theorem exists_sl2_ne_comm (K : Type*) [Field K] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩, fun h => ?_⟩
  have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 =
    (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 at h00
  simp [Matrix.mul_fin_two] at h00

theorem nonempty_sl2_mulEquiv {R S : Type*} [CommRing R] [CommRing S] (σ : R ≃+* S) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S) :=
  ⟨MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
    (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by ext A : 1; apply Subtype.ext; ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])⟩

end CFSG.Quasithin.SimsG4.G49

module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

structure CoreSetting {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] (ρ : Representation k G Q) (A₁ A₂ Δ : Subgroup G) : Prop where
  irr : ρ.IsIrreducible
  gen : A₁ ⊔ A₂ ⊔ Δ = ⊤
  comm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a
  norm₁ : ∀ d ∈ Δ, ∀ a ∈ A₁, d * a * d⁻¹ ∈ A₁
  norm₂ : ∀ d ∈ Δ, ∀ b ∈ A₂, d * b * d⁻¹ ∈ A₂
  elem : IsElemAbelian 2 Δ
  quad : ∀ d ∈ Δ, ∀ d' ∈ Δ, ∀ q : Q, ρ d (ρ d' q - q) = ρ d' q - q
  faith : ∀ d ∈ Δ, (∀ q : Q, ρ d q = q) → d = 1
  quasi₁ : CFSG.Open.IsQuasisimple ↥A₁
  quasi₂ : CFSG.Open.IsQuasisimple ↥A₂
  nontriv₁ : ∃ a ∈ A₁, ∃ q : Q, ρ a q ≠ q
  nontriv₂ : ∃ a ∈ A₂, ∃ q : Q, ρ a q ≠ q
  two₁ : ¬ Δ ≤ Subgroup.centralizer (A₂ : Set G)
  two₂ : ¬ Δ ≤ Subgroup.centralizer (A₁ : Set G)

theorem w183b2_quasi_of_simple_nonab {G : Type*} [Group G] {A : Subgroup G}
    (hs : IsSimpleGroup ↥A) (hnab : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple ↥A := by
  haveI : IsSimpleGroup ↥A := hs
  haveI : Group.IsPerfect ↥A := by
    refine ⟨?_⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥A) with h | h
    · exfalso
      haveI := (commutator_eq_bot_iff ↥A).mp h
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      exact hab (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩))
    · exact h
  exact CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥A

theorem w183b2_absIrrOverF4_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AbsIrrOverF4 Y) : AbsIrrOverF4 X := by
  intro n ρ hirr
  obtain ⟨F, P, hF, hcard, hent⟩ := h n (ρ.comp e.symm.toMonoidHom) (by
    intro W hW
    refine hirr W (fun x w hw => ?_)
    have := hW (e x) w hw
    simpa using this)
  exact ⟨F, P, hF, hcard, fun x i j => by simpa using hent (e x) i j⟩

theorem w183b2_absIrrOverF4_of_shape {X : Type} [Group X]
    (hs : IsL3 X 2 ∨ IsAlt X 6 ∨ IsSp4 X 2) (hFD : FinG11Models) : AbsIrrOverF4 X := by
  rcases hs with hs | hs | hs
  · exact hFD.1 X hs
  · exact hFD.2.1 X hs
  · exact hFD.2.2 X hs

theorem w183b2_quadratic_operator {k : Type} [Field k] {G : Type} [Group G] {Q : Type}
    [AddCommGroup Q] [Module k Q] {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {d d' : G} (hd : d ∈ Δ) (hd' : d' ∈ Δ) :
    (ρ d - 1) * (ρ d' - 1) = 0 := by
  ext q
  have hq := h.quad d hd d' hd' q
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply]
  rw [hq, sub_self]

theorem w183b2_rho_comm {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {d d' : G} (hd : d ∈ Δ) (hd' : d' ∈ Δ) :
    ρ d * ρ d' = ρ d' * ρ d := by
  haveI : IsMulCommutative ↥Δ := h.elem.1
  have hcomm : (⟨d, hd⟩ : ↥Δ) * ⟨d', hd'⟩ = ⟨d', hd'⟩ * ⟨d, hd⟩ := mul_comm' _ _
  have hdd : d * d' = d' * d := congrArg Subtype.val hcomm
  rw [← map_mul, ← map_mul, hdd]

theorem w183b2_faithful_kernel {k : Type} [Field k] {G : Type} [Group G] {Q : Type}
    [AddCommGroup Q] [Module k Q] {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {d : G} (hd : d ∈ Δ) (h1 : ρ d = 1) : d = 1 :=
  h.faith d hd (fun q => by rw [h1]; rfl)

theorem w183b2_normal_sup {k : Type} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) : (A₁ ⊔ A₂).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  rw [← h.gen]
  refine sup_le (Subgroup.le_normalizer (H := A₁ ⊔ A₂)) (fun d hd => ?_)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmap₁ : A₁.map (MulAut.conj d) = A₁ := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using h.norm₁ d hd a ha
    · intro a ha
      refine ⟨d⁻¹ * a * d, ?_, ?_⟩
      · simpa [mul_assoc] using h.norm₁ d⁻¹ (Δ.inv_mem hd) a ha
      · simp [MulAut.conj_apply, mul_assoc]
  have hmap₂ : A₂.map (MulAut.conj d) = A₂ := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using h.norm₂ d hd b hb
    · intro b hb
      refine ⟨d⁻¹ * b * d, ?_, ?_⟩
      · simpa [mul_assoc] using h.norm₂ d⁻¹ (Δ.inv_mem hd) b hb
      · simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_sup, hmap₁, hmap₂]

@[expose] def w183b2InvSub {k : Type*} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] (ρ : Representation k G Q) (N : Subgroup G) (U : Submodule k Q) : Prop :=
  ∀ n ∈ N, ∀ u ∈ U, ρ n u ∈ U

@[expose] def w183b2SimpleSub {k : Type*} [Field k] {G : Type} [Group G] {Q : Type}
    [AddCommGroup Q] [Module k Q] (ρ : Representation k G Q) (N : Subgroup G)
    (U : Submodule k Q) : Prop :=
  U ≠ ⊥ ∧ w183b2InvSub ρ N U ∧
    ∀ V : Submodule k Q, w183b2InvSub ρ N V → V ≤ U → V = ⊥ ∨ V = U

@[expose] def w183b2NLin {k : Type*} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] (ρ : Representation k G Q) (N : Subgroup G) (U : Submodule k Q)
    (f : U →ₗ[k] Q) : Prop :=
  ∀ n ∈ N, ∀ u v : U, ρ n (u : Q) = (v : Q) → f v = ρ n (f u)

@[expose] def w183b2NIso {k : Type*} [Field k] {G : Type} [Group G] {Q : Type} [AddCommGroup Q]
    [Module k Q] (ρ : Representation k G Q) (N : Subgroup G) (U V : Submodule k Q) : Prop :=
  ∃ f : U →ₗ[k] Q, Function.Injective f ∧ LinearMap.range f = V ∧ w183b2NLin ρ N U f

theorem w183b2_fixes_of_disjoint_image {k : Type} [Field k] {G : Type} [Group G] {Q : Type}
    [AddCommGroup Q] [Module k Q] {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) {U : Submodule k Q} {d f : G} (hd : d ∈ Δ) (hf : f ∈ Δ)
    (hfU : ∀ u ∈ U, ρ f u ∈ U) (hdisj : U.map (ρ d) ⊓ U = ⊥) :
    ∀ u ∈ U, ρ f u = u := by
  intro u hu
  have hq := congrArg (fun F : Module.End k Q => F u) (w183b2_quadratic_operator h hd hf)
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at hq
  have hfd : ρ f u - u ∈ U := U.sub_mem (hfU u hu) hu
  have hfix : ρ d (ρ f u - u) = ρ f u - u := sub_eq_zero.mp hq
  have hmem : ρ f u - u ∈ U.map (ρ d) :=
    hfix ▸ (Submodule.mem_map.mpr ⟨ρ f u - u, hfd, rfl⟩)
  have hbot : ρ f u - u ∈ (⊥ : Submodule k Q) := by
    rw [← hdisj]
    exact ⟨hmem, hfd⟩
  exact sub_eq_zero.mp ((Submodule.mem_bot k).mp hbot)

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import CFSG.RankThree.PartOne.S11d.OrthSplitModel
public import CFSG.RankThree.PartOne.S11d.OrthLayer

public section

namespace CFSG.RankThree.PartOne

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

structure SplitFourModel (R : QuadraticForm K W) where
  ψ : W ≃ₗ[K] Matrix (Fin 2) (Fin 2) K
  e : ↥(TauCeti.QuadraticMap.orthogonalGroup R) ≃* DeterminantIsometries K
  hψ : ∀ v, R v = (ψ v).det
  he : ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) (X : Matrix (Fin 2) (Fin 2) K),
    (e g).val X = ψ (g.val (ψ.symm X))
  hcomm_eq : commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) =
    (determinantLeftFactor K).map e.symm.toMonoidHom ⊔
      (determinantRightFactor K).map e.symm.toMonoidHom
  hqL : CFSG.IsQuasisimple ↥((determinantLeftFactor K).map e.symm.toMonoidHom)
  hqR : CFSG.IsQuasisimple ↥((determinantRightFactor K).map e.symm.toMonoidHom)
  hnL : (((determinantLeftFactor K).map e.symm.toMonoidHom).subgroupOf
    (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).Normal
  hnR : (((determinantRightFactor K).map e.symm.toMonoidHom).subgroupOf
    (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).Normal
  hcomm : ∀ u ∈ (determinantLeftFactor K).map e.symm.toMonoidHom,
    ∀ v ∈ (determinantRightFactor K).map e.symm.toMonoidHom, u * v = v * u

namespace SplitFourModel

variable {R : QuadraticForm K W} (M : SplitFourModel R)

@[expose] noncomputable def act :
    SL(2, K) × SL(2, K) →* ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
  M.e.symm.toMonoidHom.comp specialRho

theorem act_apply (z : SL(2, K) × SL(2, K)) : M.act z = M.e.symm (specialRho z) := rfl

theorem e_act (z : SL(2, K) × SL(2, K)) : M.e (M.act z) = specialRho z :=
  M.e.apply_symm_apply _

theorem psi_act (z : SL(2, K) × SL(2, K)) (w : W) :
    M.ψ ((M.act z).val w) = z.1.val * M.ψ w * (z.2⁻¹ : SL(2, K)).val := by
  have h := M.he (M.act z) (M.ψ w)
  rw [LinearEquiv.symm_apply_apply] at h
  rw [← h, M.e_act, specialRho_apply]

theorem act_injective [CharP K 2] : Function.Injective M.act := fun _ _ h =>
  specialRho_injective (M.e.symm.injective h)

theorem range_act : M.act.range = commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  rw [M.hcomm_eq, ← Subgroup.map_sup, determinantFactors_sup]
  exact (MonoidHom.map_range M.e.symm.toMonoidHom specialRho).symm

theorem mem_commutator_iff (g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :
    g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) ↔ ∃ z, M.act z = g := by
  rw [← M.range_act]
  exact MonoidHom.mem_range

end SplitFourModel

end Model

section Dickson

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {R : QuadraticForm K W}

theorem reflect_not_mem_commutator (hR : (polarBilin R).Nondegenerate) {a : W} (ha : R a ≠ 0) :
    (⟨reflect R a, reflect_mem_orthogonalGroup R a⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ∉
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  intro hmem
  have hΩ : reflect R a ∈ orthDerived R := by
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact ⟨_, hmem, rfl⟩
  have h := dicksonHom_apply_orthDerived_eq_one hR hΩ
  rw [dicksonHom_reflect hR ha] at h
  exact absurd (ofAdd_eq_one.mp h) (by decide)

omit [FiniteDimensional K W] in
theorem commute_reflect_of_fixes {a : W} {g : ↥(TauCeti.QuadraticMap.orthogonalGroup R)}
    (hga : g.val a = a) :
    g * (⟨reflect R a, reflect_mem_orthogonalGroup R a⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup R)) =
      ⟨reflect R a, reflect_mem_orthogonalGroup R a⟩ * g := by
  apply Subtype.ext
  have h := reflect_conj g.2 a
  rw [hga] at h
  change (g : W ≃ₗ[K] W) * reflect R a = reflect R a * (g : W ≃ₗ[K] W)
  calc (g : W ≃ₗ[K] W) * reflect R a = ((g : W ≃ₗ[K] W) * reflect R a * (g : W ≃ₗ[K] W)⁻¹) *
        (g : W ≃ₗ[K] W) := by group
    _ = reflect R a * (g : W ≃ₗ[K] W) := by rw [h]

variable [Finite K] [CharP K 2]

theorem specialImage_eq_leftRightImage : specialImage K = leftRightImage K :=
  le_antisymm (by rintro _ ⟨z, rfl⟩; exact ⟨specialPairs z, rfl⟩)
    (by rintro _ ⟨z, rfl⟩; exact rho_mem_specialImage_char2 z)

theorem SplitFourModel.index_orthDerived (M : SplitFourModel R) [Nontrivial W]
    (hR : (polarBilin R).Nondegenerate) :
    ((orthDerived R).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup R)).index = 2 := by
  have hsub : (orthDerived R).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup R) =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective _
  have hmap : commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) =
      (specialImage K).map M.e.symm.toMonoidHom := by
    rw [← M.range_act]
    exact (MonoidHom.map_range M.e.symm.toMonoidHom specialRho).symm
  have hdvd : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).index ∣ 2 := by
    have h := Subgroup.index_map_equiv (specialImage K) M.e.symm
    rw [hmap, show Subgroup.map M.e.symm.toMonoidHom (specialImage K) =
      Subgroup.map (M.e.symm : _ →* _) (specialImage K) from rfl, h, specialImage_eq_leftRightImage]
    exact leftRightImage_index_dvd_two
  obtain ⟨a, ha⟩ := exists_map_ne_zero hR
  have hne : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)).index ≠ 1 := by
    intro h1
    have h2 := Subgroup.index_eq_one.mp h1
    exact reflect_not_mem_commutator hR ha (by rw [h2]; trivial)
  rw [hsub]
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

theorem SplitFourModel.dicksonDerived (M : SplitFourModel R) [Nontrivial W]
    (hR : (polarBilin R).Nondegenerate) : DicksonDerived R hR :=
  fun _ hg => mem_orthDerived_of_dicksonHom_eq_one hR (M.index_orthDerived hR) hg

theorem SplitFourModel.commute_iff_of_fixes (M : SplitFourModel R) [Nontrivial W]
    (hR : (polarBilin R).Nondegenerate) {a : W} (ha : R a ≠ 0) {z₁ z₂ : SL(2, K) × SL(2, K)}
    (h₁ : (M.act z₁).val a = a) (h₂ : (M.act z₂).val a = a) :
    Commute z₁.1 z₂.1 ↔ Commute z₁.2 z₂.2 := by
  set r : ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    ⟨reflect R a, reflect_mem_orthogonalGroup R a⟩ with hr
  have hζ : M.e r ∉ specialImage K := by
    rintro ⟨z, hz⟩
    apply reflect_not_mem_commutator hR ha
    rw [← hr, M.mem_commutator_iff]
    exact ⟨z, by rw [M.act_apply, hz, MulEquiv.symm_apply_apply]⟩
  have hfix : ∀ z : SL(2, K) × SL(2, K), (M.act z).val a = a →
      M.e r * specialRho z * (M.e r)⁻¹ = specialRho z := by
    intro z hz
    have h := congrArg M.e (commute_reflect_of_fixes hz)
    rw [map_mul, map_mul, M.e_act] at h
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm
  exact commute_iff_of_swap_fixed hζ (hfix z₁ h₁) (hfix z₂ h₂)

end Dickson

end CFSG.RankThree.PartOne

module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedFrame
import CFSG.LocalAnalysis.StandardType.TrialityLineIdentity
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.StandardType CFSG.StandardType.Triality

section Aut

variable {G : Type*} [Group G]

private theorem mul_conj_eq (φ : MulAut G) (g : G) :
    φ * MulAut.conj g = MulAut.conj (φ g) * φ := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

private theorem mul_conj_pow_three (A : MulAut G) (g : G) :
    (A * MulAut.conj g) ^ 3 = MulAut.conj (A g * (A * A) g * (A * A * A) g) * (A * A * A) := by
  ext x
  simp only [pow_three', MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_inv_rev]

end Aut

set_option maxHeartbeats 800000 in
theorem TrialityData.exists_line {X : Type} [Group X] {s : X}
    {ε : X →* Equiv.Perm (Fin 3)} (h : TrialityData X s ε) :
    ∃ a b t : X, IsConj s a ∧ IsConj s b ∧ IsConj s t ∧ ε a = ε b ∧ ε t ≠ ε a ∧
      orderOf (a * b) = 3 ∧ orderOf (t * a) = 3 ∧ orderOf (t * b) = 3 ∧
      orderOf (t * (b * a * b⁻¹)) = 3 := by
  obtain ⟨F, _, _, _, Λ, s₁, hs₁, hΛs₁, hker⟩ := h.exists_orthFrame
  have hmap : (ε.ker.subgroupOf (ε.ker ⊔ Subgroup.zpowers s)).map Λ.toMonoidHom =
      (matrixDerived (coordinateQuadPlus 4 F)).subgroupOf
        (matrixIsometries (coordinateQuadPlus 4 F)) := by
    ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hker,
      MulEquiv.apply_symm_apply]
  let ψ : ↥ε.ker ≃* Om8 F :=
    (Subgroup.subgroupOfEquivOfLe (le_sup_left : ε.ker ≤ ε.ker ⊔ Subgroup.zpowers s)).symm.trans
      ((Λ.subgroupMap _).trans ((MulEquiv.subgroupCongr hmap).trans
        (Subgroup.subgroupOfEquivOfLe (matrixDerived_le_isometries _))))
  have hψ : ∀ m : ↥ε.ker, ((ψ m : Om8 F) : GL (Fin (2 * 4)) F) =
      ((Λ ⟨m, Subgroup.mem_sup_left m.2⟩ : matrixIsometries (coordinateQuadPlus 4 F)) :
        GL (Fin (2 * 4)) F) := fun m => rfl
  let c : X →* MulAut (Om8 F) := (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal
  have hc : ∀ (x : X) (m : ↥ε.ker), c x (ψ m) = ψ (MulAut.conjNormal x m) := by
    intro x m
    change ψ (MulAut.conjNormal x (ψ.symm (ψ m))) = _
    rw [MulEquiv.symm_apply_apply]
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (ε.ker : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h1 := hc x ⟨m, hm⟩
      rw [hx, MulAut.one_apply] at h1
      have h2 := congrArg Subtype.val (ψ.injective h1)
      rw [MulAut.conjNormal_apply] at h2
      calc m * x = x * m * x⁻¹ * x := by rw [← h2]
        _ = x * m := by group
    rwa [h.centralizer_ker, Subgroup.mem_bot] at hxc
  have hP2 : ∀ x : ↥(ε.ker ⊔ Subgroup.zpowers s),
      c x = conjAct _ (matrixIsometryInclusion _ (Λ x)) := by
    intro x
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨m, rfl⟩ := ψ.surjective y
    rw [hc, conjAct_inclusion_val, hψ, hψ]
    have hx : (⟨((MulAut.conjNormal (x : X) m : ↥ε.ker) : X),
        Subgroup.mem_sup_left (MulAut.conjNormal (x : X) m).2⟩ :
          ↥(ε.ker ⊔ Subgroup.zpowers s)) = x * ⟨m, Subgroup.mem_sup_left m.2⟩ * x⁻¹ :=
      Subtype.ext (MulAut.conjNormal_apply _ _)
    rw [hx, map_mul, map_mul, map_inv]
    rfl
  have hP3 : ∀ m : ↥ε.ker, c m = MulAut.conj (ψ m) := by
    intro m
    refine MulEquiv.ext fun y => ?_
    obtain ⟨n, rfl⟩ := ψ.surjective y
    rw [hc, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (MulAut.conjNormal_apply _ _))
  have hconjinj : Function.Injective (MulAut.conj : Om8 F →* MulAut (Om8 F)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨m, rfl⟩ := ψ.surjective g
    have h1 : c m = 1 := by rw [hP3, hg]
    have h2 : (m : X) = 1 := hinj (by rw [h1, map_one])
    rw [show m = 1 from Subtype.ext h2, map_one]
  have hinner : ∀ g : Om8 F, c (ψ.symm g) = MulAut.conj g := fun g => by
    rw [hP3, MulEquiv.apply_symm_apply]
  have hkerc : ∀ x : X, c x ∈ ComponentClassification.OuterAutomorphisms.inner (Om8 F) →
      x ∈ ε.ker := by
    rintro x ⟨g, hg⟩
    rw [← hinj ((hinner g).trans hg)]
    exact (ψ.symm g).2
  have hcker : ∀ m : ↥ε.ker, c m ∈ ComponentClassification.OuterAutomorphisms.inner (Om8 F) :=
    fun m => ⟨ψ m, (hP3 m).symm⟩
  have hcs₁ : c s₁ = AutOm.plusRefl one_le_four := by
    rw [hP2, show Λ s₁ = ⟨_, reflMat_mem_isometries _
      (AutOm.plusUnitVector_form_ne_zero (K := F) one_le_four)⟩ from Subtype.ext hΛs₁]
    rfl
  have hρρ : AutOm.plusRefl (K := F) one_le_four * AutOm.plusRefl one_le_four = 1 :=
    AutOm.plusRefl_mul_self _
  have hρinv : (AutOm.plusRefl (K := F) one_le_four)⁻¹ = AutOm.plusRefl one_le_four :=
    inv_eq_of_mul_eq_one_right hρρ
  have hρθiρ : AutOm.plusRefl (K := F) one_le_four * (theta : MulAut (Om8 F))⁻¹ *
      AutOm.plusRefl one_le_four = theta := by
    have h1 := congrArg (·⁻¹) (plusRefl_theta_plusRefl (K := F))
    simp only [mul_inv_rev, hρinv, inv_inv] at h1
    rw [← mul_assoc] at h1
    exact h1
  have hθ3 : (theta : MulAut (Om8 F)) ^ 3 = 1 := theta_cube
  have hθ1 : (theta : MulAut (Om8 F)) ≠ 1 := fun h1 =>
    conjAct_ne_theta (1 : similarityPairs (coordinateQuadPlus 4 F)) (by rw [map_one, h1])
  have hθinner : ∀ j : ℕ, (theta : MulAut (Om8 F)) ^ j ∈
      ComponentClassification.OuterAutomorphisms.inner (Om8 F) → theta ^ j = 1 :=
    fun j hj => (theta_pow_mul_mem_inner j (one_mem _) (by rwa [mul_one])).1
  have hθsq : (theta : MulAut (Om8 F)) ^ 2 ∉
      ComponentClassification.OuterAutomorphisms.inner (Om8 F) := fun h2 => hθ1 (by
    calc (theta : MulAut (Om8 F)) = theta ^ 3 * (theta ^ 2)⁻¹ := by group
      _ = 1 := by rw [hθ3, hθinner 2 h2, inv_one, mul_one])
  have hθk : ∀ j : ℕ, AutOm.plusRefl (K := F) one_le_four * ((theta : MulAut (Om8 F)) ^ j)⁻¹ =
      theta ^ j * AutOm.plusRefl one_le_four := by
    intro j
    have h1 := conj_pow (a := AutOm.plusRefl (K := F) one_le_four)
      (b := (theta : MulAut (Om8 F))⁻¹) (i := j)
    rw [hρinv, hρθiρ, inv_pow] at h1
    calc AutOm.plusRefl one_le_four * (theta ^ j)⁻¹
        = AutOm.plusRefl one_le_four * (theta ^ j)⁻¹ *
          (AutOm.plusRefl one_le_four * AutOm.plusRefl one_le_four) := by rw [hρρ, mul_one]
      _ = AutOm.plusRefl one_le_four * (theta ^ j)⁻¹ * AutOm.plusRefl one_le_four *
          AutOm.plusRefl one_le_four := by group
      _ = theta ^ j * AutOm.plusRefl one_le_four := by rw [← h1]
  have hρconj : ∀ g : Om8 F, AutOm.plusRefl one_le_four * MulAut.conj g *
      AutOm.plusRefl one_le_four = MulAut.conj (AutOm.plusRefl (K := F) one_le_four g) := by
    intro g
    rw [mul_conj_eq, mul_assoc, hρρ, mul_one]
  have hτ : ε s₁ ≠ 1 ∧ ε s₁ * ε s₁ = 1 := h.map_ne_one_and_mul_self hs₁
  have hS3 : ∀ τ : Equiv.Perm (Fin 3), τ ≠ 1 → τ * τ = 1 →
      Equiv.swap 0 1 * Equiv.swap 1 2 * τ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ * τ ≠ 1 := by
    decide
  obtain ⟨y, hy⟩ := h.surjective (Equiv.swap 0 1 * Equiv.swap 1 2)
  obtain ⟨z, hz⟩ : ∃ z : X, c z = theta := by
    obtain ⟨ι, hι, k, d, hd, hyk⟩ := exists_inner_mul_theta_pow_mul (c y)
    have hdρ : d * AutOm.plusRefl one_le_four = AutOm.plusRefl one_le_four * d := by
      obtain ⟨σ, rfl | rfl⟩ := AutOm.mem_plusCompl.1 hd
      · exact (AutOm.plusRefl_mul_fieldAutP _ σ).symm
      · rw [mul_assoc, ← AutOm.plusRefl_mul_fieldAutP]
    have hdρd : d * AutOm.plusRefl one_le_four * d⁻¹ = AutOm.plusRefl one_le_four := by
      rw [hdρ, mul_inv_cancel_right]
    have hu : c (y * s₁ * y⁻¹ * s₁) = ι * theta ^ (k + k) *
        (AutOm.plusRefl one_le_four * ι⁻¹ * AutOm.plusRefl one_le_four) := by
      rw [map_mul, map_mul, map_mul, map_inv, hcs₁, hyk]
      calc ι * (theta ^ k * d) * AutOm.plusRefl one_le_four * (ι * (theta ^ k * d))⁻¹ *
            AutOm.plusRefl one_le_four
          = ι * theta ^ k * (d * AutOm.plusRefl one_le_four * d⁻¹) * (theta ^ k)⁻¹ * ι⁻¹ *
            AutOm.plusRefl one_le_four := by group
        _ = ι * theta ^ k * (AutOm.plusRefl one_le_four * (theta ^ k)⁻¹) * ι⁻¹ *
            AutOm.plusRefl one_le_four := by rw [hdρd]; group
        _ = ι * theta ^ (k + k) * (AutOm.plusRefl one_le_four * ι⁻¹ *
            AutOm.plusRefl one_le_four) := by rw [hθk, pow_add]; group
    have hι' : AutOm.plusRefl one_le_four * ι⁻¹ * AutOm.plusRefl one_le_four ∈
        ComponentClassification.OuterAutomorphisms.inner (Om8 F) := by
      have h1 := (inner_normal (Om8 F)).conj_mem ι⁻¹ (inv_mem hι) (AutOm.plusRefl one_le_four)
      rwa [hρinv] at h1
    have hnot : (theta : MulAut (Om8 F)) ^ (k + k) ∉
        ComponentClassification.OuterAutomorphisms.inner (Om8 F) := by
      intro hin
      have h1 : c (y * s₁ * y⁻¹ * s₁) ∈
          ComponentClassification.OuterAutomorphisms.inner (Om8 F) := by
        rw [hu]
        exact mul_mem (mul_mem hι hin) hι'
      have h2 := hkerc _ h1
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hy] at h2
      exact hS3 _ hτ.1 hτ.2 h2
    obtain ⟨g₁, hg₁⟩ := hι
    obtain ⟨g₂, hg₂⟩ := hι'
    have hθr : c ((ψ.symm g₁⁻¹ : X) * (y * s₁ * y⁻¹ * s₁) * (ψ.symm g₂⁻¹ : X)) =
        theta ^ (k + k) := by
      rw [map_mul, map_mul, hinner, hinner, hu, map_inv, map_inv, hg₁, hg₂]
      group
    have hmod : (theta : MulAut (Om8 F)) ^ (k + k) = theta ^ ((k + k) % 3) := pow_eq_pow_mod _ hθ3
    rcases (by omega : (k + k) % 3 = 0 ∨ (k + k) % 3 = 1 ∨ (k + k) % 3 = 2) with h0 | h0 | h0
    · rw [h0, pow_zero] at hmod
      exact absurd (by rw [hmod]; exact one_mem _) hnot
    · rw [h0, pow_one] at hmod
      exact ⟨_, hθr.trans hmod⟩
    · rw [h0] at hmod
      refine ⟨((ψ.symm g₁⁻¹ : X) * (y * s₁ * y⁻¹ * s₁) * (ψ.symm g₂⁻¹ : X))⁻¹, ?_⟩
      rw [map_inv, hθr, hmod, theta_sq, inv_inv]
  have hs₁s₁ : (s₁ : X) * s₁ = 1 := hinj (by rw [map_mul, hcs₁, hρρ, map_one])
  generalize (s₁ : X) = a at hs₁ hcs₁ hτ hs₁s₁
  obtain ⟨m, hmk, hcm⟩ : ∃ m : X, m ∈ ε.ker ∧ c m = MulAut.conj lineK :=
    ⟨ψ.symm lineK, (ψ.symm lineK).2, hinner _⟩
  have hw : lineW (K := F) = AutOm.plusRefl one_le_four lineK * lineK⁻¹ := rfl
  have hta : c (z * a * z⁻¹ * a) = theta ^ 2 := by
    simp only [map_mul, map_inv]
    rw [hz, hcs₁]
    calc (theta : MulAut (Om8 F)) * AutOm.plusRefl one_le_four * theta⁻¹ *
          AutOm.plusRefl one_le_four
        = theta * (AutOm.plusRefl one_le_four * theta⁻¹ * AutOm.plusRefl one_le_four) := by group
      _ = theta ^ 2 := by rw [hρθiρ, pow_two]
  have hab : c (a * (m * a * m⁻¹)) = MulAut.conj lineW := by
    simp only [map_mul, map_inv]
    rw [hcs₁, hcm, hw, map_mul, map_inv]
    calc AutOm.plusRefl one_le_four * (MulAut.conj lineK * AutOm.plusRefl one_le_four *
          (MulAut.conj lineK)⁻¹)
        = AutOm.plusRefl one_le_four * MulAut.conj lineK * AutOm.plusRefl one_le_four *
          (MulAut.conj lineK)⁻¹ := by group
      _ = MulAut.conj (AutOm.plusRefl one_le_four lineK) * (MulAut.conj lineK)⁻¹ := by
        rw [hρconj]
  have hinvb : (MulAut.conj lineK * AutOm.plusRefl one_le_four * (MulAut.conj lineK)⁻¹)⁻¹ =
      MulAut.conj (lineK (K := F)) * AutOm.plusRefl one_le_four * (MulAut.conj lineK)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, hρinv, mul_assoc]
  have habab : c (a * ((m * a * m⁻¹) * a * (m * a * m⁻¹)⁻¹)) = MulAut.conj (lineW ^ 2) := by
    simp only [map_mul, map_inv]
    rw [hcs₁, hcm, hinvb, pow_two, map_mul, hw, map_mul, map_inv]
    calc AutOm.plusRefl one_le_four * (MulAut.conj lineK * AutOm.plusRefl one_le_four *
          (MulAut.conj lineK)⁻¹ * AutOm.plusRefl one_le_four * (MulAut.conj lineK *
            AutOm.plusRefl one_le_four * (MulAut.conj lineK)⁻¹))
        = AutOm.plusRefl one_le_four * MulAut.conj lineK * AutOm.plusRefl one_le_four *
          (MulAut.conj lineK)⁻¹ * (AutOm.plusRefl one_le_four * MulAut.conj lineK *
            AutOm.plusRefl one_le_four * (MulAut.conj lineK)⁻¹) := by group
      _ = MulAut.conj (AutOm.plusRefl one_le_four lineK) * (MulAut.conj lineK)⁻¹ *
          (MulAut.conj (AutOm.plusRefl one_le_four lineK) * (MulAut.conj lineK)⁻¹) := by
        rw [hρconj]
  have hA2 : (theta : MulAut (Om8 F)) ^ 2 * theta ^ 2 = theta := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hθ3, one_mul, pow_one]
  have hA3 : (theta : MulAut (Om8 F)) ^ 2 * theta ^ 2 * theta ^ 2 = 1 := by
    rw [hA2, ← pow_succ', hθ3]
  have hcube : ∀ g : Om8 F, ((theta : MulAut (Om8 F)) ^ 2 * MulAut.conj g) ^ 3 =
      MulAut.conj ((theta ^ 2 : MulAut (Om8 F)) g * theta g * g) := by
    intro g
    rw [mul_conj_pow_three, hA3, hA2, MulAut.one_apply, mul_one]
  have hne : ∀ g : Om8 F, (theta : MulAut (Om8 F)) ^ 2 * MulAut.conj g ≠ 1 := by
    intro g h1
    apply hθsq
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem ⟨g, rfl⟩
  have hord : ∀ x : X, orderOf x = orderOf (c x) := fun x => (orderOf_injective c hinj x).symm
  refine ⟨a, m * a * m⁻¹, z * a * z⁻¹, hs₁, hs₁.trans (isConj_iff.2 ⟨m, rfl⟩),
    hs₁.trans (isConj_iff.2 ⟨z, rfl⟩), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, (MonoidHom.mem_ker).1 hmk, one_mul, inv_one, mul_one]
  · intro hta'
    have h1 : z * a * z⁻¹ * a ∈ ε.ker := by
      rw [MonoidHom.mem_ker, map_mul, hta', hτ.2]
    exact hθsq (by rw [← hta]; exact hcker ⟨_, h1⟩)
  · rw [hord, hab, orderOf_injective _ hconjinj, orderOf_lineW]
  · rw [hord, hta]
    refine orderOf_eq_prime ?_ (fun h1 => hθsq (by rw [h1]; exact one_mem _))
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hθ3, one_pow]
  · have h1 : z * a * z⁻¹ * (m * a * m⁻¹) = (z * a * z⁻¹ * a) * (a * (m * a * m⁻¹)) := by
      calc z * a * z⁻¹ * (m * a * m⁻¹) = z * a * z⁻¹ * (a * a) * (m * a * m⁻¹) := by
            rw [hs₁s₁, mul_one]
        _ = _ := by group
    rw [hord, h1, map_mul, hta, hab]
    exact orderOf_eq_prime (by rw [hcube, theta_sq_lineW_mul, map_one]) (hne _)
  · have h1 : z * a * z⁻¹ * ((m * a * m⁻¹) * a * (m * a * m⁻¹)⁻¹) =
        (z * a * z⁻¹ * a) * (a * ((m * a * m⁻¹) * a * (m * a * m⁻¹)⁻¹)) := by
      calc z * a * z⁻¹ * ((m * a * m⁻¹) * a * (m * a * m⁻¹)⁻¹)
          = z * a * z⁻¹ * (a * a) * ((m * a * m⁻¹) * a * (m * a * m⁻¹)⁻¹) := by
            rw [hs₁s₁, mul_one]
        _ = _ := by group
    rw [hord, h1, map_mul, hta, habab]
    exact orderOf_eq_prime (by rw [hcube, theta_sq_lineW_sq_mul, map_one]) (hne _)

end CFSG.LocalAnalysis.WeakClosure81

end

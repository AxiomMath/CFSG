module

public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Fitting
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec6.Wales65B

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_subgroup_of_le {M N : Subgroup G} (hMN : M ≤ N) (hN : Group.IsSolvable N) :
    Group.IsSolvable M :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hMN)
    (Subgroup.inclusion_injective _)

theorem mem_thetaQuotCentralizer_of_isSolvable {X Z : Subgroup G} {b : G}
    (hXp : Group.IsPerfect X) (hXq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hZp : Group.IsPerfect Z) (hZX : Z ≤ X)
    (hXZ : X ≤ Z ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    (hsol : Group.IsSolvable (⁅Z, Subgroup.zpowers b⁆ : Subgroup G)) :
    b ∈ thetaQuotCentralizer X := by
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set Zb := Subgroup.zpowers b with hZb
  set M := ⁅Z, Zb⁆ with hM
  have hZbX : Zb ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hbX
  have hZbθ : Zb ≤ Subgroup.normalizer (θX : Set G) :=
    hZbX.trans (normalizer_le_normalizer_theta X)
  have hZθ : Z ≤ Subgroup.normalizer (θX : Set G) := hZX.trans (le_normalizer_theta X)
  have hMX : M ≤ X := (Subgroup.commutator_mono hZX le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hZbX)
  have hZM : Z ≤ Subgroup.normalizer (M : Set G) := le_normalizer_commutator_left Z Zb
  have hXN : X ≤ Subgroup.normalizer ((M ⊔ θX : Subgroup G) : Set G) := by
    refine hXZ.trans (sup_le ?_ ?_)
    · apply le_normalizer_sup_of_conj
      · intro z hz x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hZM hz) x).mp hx)
      · intro z hz x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hZθ hz) x).mp hx)
    · apply le_normalizer_sup_of_conj
      · intro t ht m hm
        have h1 : m⁻¹ * t * m⁻¹⁻¹ ∈ θX := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta X (X.inv_mem (hMX hm))) t).mp ht
        rw [show t * m * t⁻¹ = m * ((m⁻¹ * t * m⁻¹⁻¹) * t⁻¹) by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
          (Subgroup.mem_sup_right (θX.mul_mem h1 (θX.inv_mem ht)))
      · intro t ht x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (le_normalizer_theta X (theta_le X ht)) x).mp hx)
  rcases sup_theta_eq_or_commutator_le hXq (sup_le hMX (theta_le X)) hXN with hcov | hcen
  ·
    exfalso
    have hMθ : M ≤ Subgroup.normalizer (θX : Set G) := hMX.trans (le_normalizer_theta X)
    have hXsol := isSolvable_sup_of_le_normalizer hMθ (theta_solvable_and_not_dvd X).1 hsol
    rw [sup_assoc, sup_idem] at hcov
    rw [sup_comm] at hXsol
    have hsolX : Group.IsSolvable X := hcov ▸ hXsol
    have hq : Group.IsSolvable (X ⧸ aschbacherSolvableCore 3 X) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    have : Nontrivial (X ⧸ aschbacherSolvableCore 3 X) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have := hXq.1
    exact Group.IsPerfect.not_isSolvable (X ⧸ aschbacherSolvableCore 3 X) hq
  ·
    have h1 : ⁅⁅Z, Zb⁆, Z⁆ ≤ θX :=
      (Subgroup.commutator_mono le_sup_left hZX).trans hcen
    have h2 : ⁅⁅Zb, Z⁆, Z⁆ ≤ θX := by rw [Subgroup.commutator_comm Zb Z]; exact h1
    have h3 := three_subgroups_mod (X := Z) (Y := Zb) (Z := Z) (N := θX) hZθ hZbθ hZθ h1 h2
    rw [commutator_self_eq_of_isPerfect hZp] at h3
    have hXb : ⁅X, Zb⁆ ≤ θX := by
      calc ⁅X, Zb⁆ ≤ ⁅Z ⊔ θX, Zb⁆ := Subgroup.commutator_mono hXZ le_rfl
        _ ≤ ⁅Z, Zb⁆ ⊔ θX := commutator_sup_le_of_le_normalizer hZθ hZbθ
        _ ≤ θX := sup_le h3 le_rfl
    exact (commutator_le_theta_iff hZbX).mp hXb (Subgroup.mem_zpowers b)

theorem not_mem_thetaQuotCentralizer_of_cover {X₁ X₂ Z : Subgroup G} {b : G}
    (hX₁p : Group.IsPerfect X₁) (hX₁q : IsQuasisimple (X₁ ⧸ aschbacherSolvableCore 3 X₁))
    (hbX₁ : b ∈ Subgroup.normalizer (X₁ : Set G)) (hbC : b ∉ thetaQuotCentralizer X₁)
    (hZp : Group.IsPerfect Z) (hZX₁ : Z ≤ X₁)
    (hX₁Z : X₁ ≤ Z ⊔ inSubgroup (aschbacherSolvableCore 3) X₁) (hZX₂ : Z ≤ X₂)
    (hbX₂ : b ∈ Subgroup.normalizer (X₂ : Set G)) : b ∉ thetaQuotCentralizer X₂ := by
  intro hbC₂
  have hZbX₂ : Subgroup.zpowers b ≤ Subgroup.normalizer (X₂ : Set G) :=
    Subgroup.zpowers_le.mpr hbX₂
  have h1 : ⁅X₂, Subgroup.zpowers b⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X₂ :=
    (commutator_le_theta_iff hZbX₂).mpr (Subgroup.zpowers_le.mpr hbC₂)
  have h2 : ⁅Z, Subgroup.zpowers b⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X₂ :=
    (Subgroup.commutator_mono hZX₂ le_rfl).trans h1
  exact hbC (mem_thetaQuotCentralizer_of_isSolvable hX₁p hX₁q hbX₁ hZp hZX₁ hX₁Z
    (isSolvable_subgroup_of_le h2 (theta_solvable_and_not_dvd X₂).1))

theorem commutator_zpowers_eq_of_not_mem_thetaQuotCentralizer {X Y : Subgroup G} {b : G}
    (hXp : Group.IsPerfect X) (hXq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
    (hbX : b ∈ Subgroup.normalizer (X : Set G)) (hbC : b ∉ thetaQuotCentralizer X)
    (hYp : Group.IsPerfect Y) (hYX : Y ≤ X)
    (hXY : X ≤ Y ⊔ inSubgroup (aschbacherSolvableCore 3) X)
    (hbY : b ∈ Subgroup.normalizer (Y : Set G)) :
    ⁅Y, Subgroup.zpowers b⁆ = Y := by
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set Zb := Subgroup.zpowers b with hZb
  have hZbX : Zb ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr hbX
  have hZbY : Zb ≤ Subgroup.normalizer (Y : Set G) := Subgroup.zpowers_le.mpr hbY
  have hZbθ : Zb ≤ Subgroup.normalizer (θX : Set G) :=
    hZbX.trans (normalizer_le_normalizer_theta X)
  have hYθ : Y ≤ Subgroup.normalizer (θX : Set G) := hYX.trans (le_normalizer_theta X)
  have hnot : ¬ ⁅X, Zb⁆ ≤ θX := fun h =>
    hbC ((commutator_le_theta_iff hZbX).mp h (Subgroup.mem_zpowers b))
  have hXb : ⁅X, Zb⁆ = X := commutator_eq_of_not_le_theta hXp hXq hZbX hnot
  set Q := ⁅Y, Zb⁆ with hQ
  have hQY : Q ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hZbY
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_commutator_left Y Zb
  have hXQ : X ≤ Q ⊔ θX := by
    calc X = ⁅X, Zb⁆ := hXb.symm
      _ ≤ ⁅Y ⊔ θX, Zb⁆ := Subgroup.commutator_mono hXY le_rfl
      _ ≤ ⁅Y, Zb⁆ ⊔ θX := commutator_sup_le_of_le_normalizer hYθ hZbθ
  have hYθY : Y ⊓ θX ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
    refine le_theta_of_normal inf_le_left
      ((le_inf Subgroup.le_normalizer hYθ).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (isSolvable_subgroup_of_le inf_le_right (theta_solvable_and_not_dvd X).1) fun h3 => ?_
    exact (theta_solvable_and_not_dvd X).2 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hsup : Q ⊔ inSubgroup (aschbacherSolvableCore 3) Y = Y := by
    refine le_antisymm (sup_le hQY (theta_le Y)) fun y hy => ?_
    have hy' : y ∈ (Q : Set G) * (θX : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Q θX (hQY.trans hYθ)]
      exact hXQ (hYX hy)
    obtain ⟨q, hq, t, ht, rfl⟩ := hy'
    have htY : t ∈ Y := by
      have := Y.mul_mem (Y.inv_mem (hQY hq)) hy
      simpa using this
    exact Subgroup.mul_mem_sup hq (hYθY ⟨htY, ht⟩)
  exact eq_of_sup_theta_eq hYp hQY hYQ hsup

omit [Finite G] in
theorem le_centralizer_of_commutator_zpowers_eq {Y M : Subgroup G} {b : G}
    (hYb : ⁅Y, Subgroup.zpowers b⁆ = Y) (hMb : M ≤ Subgroup.centralizer {b})
    (hYM : Y ≤ Subgroup.normalizer (M : Set G)) : Y ≤ Subgroup.centralizer (M : Set G) := by
  have hbM : b ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hMb hm)
  rw [← hYb, Subgroup.commutator_le]
  intro y hy z hz
  have hzM : z ∈ Subgroup.centralizer (M : Set G) := Subgroup.zpowers_le.mpr hbM hz
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have h1 : y⁻¹ * m * y⁻¹⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hYM (Y.inv_mem hy)) m).mp hm
  have e1 : (y⁻¹ * m * y⁻¹⁻¹) * z = z * (y⁻¹ * m * y⁻¹⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hzM _ h1
  have e2 : m * z⁻¹ = z⁻¹ * m := Subgroup.mem_centralizer_iff.mp (inv_mem hzM) m hm
  calc m * ⁅y, z⁆ = y * ((y⁻¹ * m * y⁻¹⁻¹) * z) * y⁻¹ * z⁻¹ := by
        rw [commutatorElement_def]; group
    _ = y * (z * (y⁻¹ * m * y⁻¹⁻¹)) * y⁻¹ * z⁻¹ := by rw [e1]
    _ = y * z * y⁻¹ * (m * z⁻¹) := by group
    _ = y * z * y⁻¹ * (z⁻¹ * m) := by rw [e2]
    _ = ⁅y, z⁆ * m := by rw [commutatorElement_def]; group

omit [Finite G] in
theorem commutator_eq_bot_of_commutator_zpowers_eq {Y N : Subgroup G} {b : G}
    (hYp : Group.IsPerfect Y) (hYb : ⁅Y, Subgroup.zpowers b⁆ = Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hNYb : ⁅N, Y⁆ ≤ Subgroup.centralizer {b}) :
    ⁅N, Y⁆ = ⊥ := by
  have hYC := le_centralizer_of_commutator_zpowers_eq hYb hNYb (le_normalizer_commutator_right N Y)
  have h1 : ⁅⁅N, Y⁆, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
  have h2 : ⁅⁅Y, N⁆, Y⁆ = ⊥ := by rw [Subgroup.commutator_comm Y N]; exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [commutator_self_eq_of_isPerfect hYp] at h3
  rw [Subgroup.commutator_comm]
  exact h3

end CFSG.RankThree.PartTwo.Sec6.Wales65B

module

public import CFSG.RankThree.PartOne.S13K.Pair134
public import CFSG.RankThree.PartOne.S11d.ThetaCalc

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_inf {K C X : Subgroup G} (h : (K.subgroupOf C).IsSubnormal) :
    (K.subgroupOf (X ⊓ C)).IsSubnormal := by
  have h1 := h.comap (Subgroup.inclusion (inf_le_right : X ⊓ C ≤ C))
  have h2 : (K.subgroupOf C).comap (Subgroup.inclusion (inf_le_right : X ⊓ C ≤ C)) =
      K.subgroupOf (X ⊓ C) := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rwa [h2] at h1

variable [Finite G]

theorem kZero_mem_thetaComponents_inf {p : ℕ} (hp : p.Prime) {E : Subgroup G} {t : MulAut E}
    (hq : CFSG.IsQuasisimple ↥(kZero p E t)) {X : Subgroup G} (hX : kZero p E t ≤ X) :
    (kZero p E t).subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG E t : Set G)) ∈
      thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG E t : Set G)) := by
  have h1 := kZero_mem_thetaComponents hp hq
  have hK : kZero p E t ≤ X ⊓ Subgroup.centralizer (autFixedInG E t : Set G) :=
    le_inf hX (kZero_le_centralizer_fixed p E t)
  have hq' : CFSG.IsQuasisimple ↥((kZero p E t).subgroupOf
      (X ⊓ Subgroup.centralizer (autFixedInG E t : Set G))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK).symm hq
  exact mem_thetaComponents_of_quasisimple hp hq' (isSubnormal_subgroupOf_inf h1.2.1)

theorem commutator_mem_theta_M {p : ℕ} (hp : p.Prime) {M K K' : Subgroup G}
    (hK : K.subgroupOf M ∈ thetaComponents p ↥M) (hK' : K'.subgroupOf M ∈ thetaComponents p ↥M)
    (hne : K.subgroupOf M ≠ K'.subgroupOf M) (hKM : K ≤ M) (hK'M : K' ≤ M) :
    ∀ k ∈ K, ∀ k' ∈ K', k * k' * k⁻¹ * k'⁻¹ ∈ inSubgroup (aschbacherSolvableCore p) M := by
  intro k hk k' hk'
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := ↥M) hp
  set N := aschbacherSolvableCore p ↥M with hN
  set π := QuotientGroup.mk' N with hπ
  have hc₁ := isComponent_map_of_mem_thetaComponents hp hK
  have hc₂ := isComponent_map_of_mem_thetaComponents hp hK'
  have hne'' : (K.subgroupOf M).map π ≠ (K'.subgroupOf M).map π := fun h =>
    hne (hbij.injOn hK hK' h)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hc₁ hc₂).resolve_left hne''
  have hkF : k ∈ M := hKM hk
  have hk'F : k' ∈ M := hK'M hk'
  have h1 : π ⟨k, hkF⟩ ∈ (K.subgroupOf M).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
  have h2 : π ⟨k', hk'F⟩ ∈ (K'.subgroupOf M).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk')
  have h3 : ⁅π ⟨k, hkF⟩, π ⟨k', hk'F⟩⁆ ∈ ⁅(K.subgroupOf M).map π, (K'.subgroupOf M).map π⁆ :=
    Subgroup.commutator_mem_commutator h1 h2
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h3
  have h4 : (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : ↥M) ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨k, hkF⟩ * ⟨k', hk'F⟩ * ⟨k, hkF⟩⁻¹ * ⟨k', hk'F⟩⁻¹ : ↥M) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact h3
  exact ⟨_, h4, rfl⟩

theorem centralizes_of_mem_theta_M {p : ℕ} (hp : p.Prime) {M E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEM : E ≤ M) {y : G}
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hyθ : y ∈ inSubgroup (aschbacherSolvableCore p) M) : ∀ a ∈ E, y * a * y⁻¹ = a := by
  intro a ha
  set θ := inSubgroup (aschbacherSolvableCore p) M with hθ
  obtain ⟨hθC, hθn⟩ := theta_le_and_normal p M
  obtain ⟨-, hθp⟩ := theta_solvable_and_not_dvd hp M
  have haC : a ∈ M := hEM ha
  have hyC : y ∈ M := hθC hyθ
  have h1 : a * y⁻¹ * a⁻¹ ∈ θ := by
    have := hθn.conj_mem ⟨y⁻¹, M.inv_mem hyC⟩ (Subgroup.mem_subgroupOf.mpr (θ.inv_mem hyθ))
      ⟨a, haC⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hz : y * a * y⁻¹ * a⁻¹ ∈ θ := by
    have := θ.mul_mem hyθ h1
    simpa [mul_assoc] using this
  have hzE : y * a * y⁻¹ * a⁻¹ ∈ E := by
    have h2 : y * a * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
    exact E.mul_mem h2 (E.inv_mem ha)
  have hzp : (y * a * y⁻¹ * a⁻¹) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ hzE
  have hord : orderOf (y * a * y⁻¹ * a⁻¹) = 1 := by
    have hdvdp : orderOf (y * a * y⁻¹ * a⁻¹) ∣ p := orderOf_dvd_of_pow_eq_one hzp
    rcases (Nat.dvd_prime hp).mp hdvdp with h | h
    · exact h
    · exfalso
      apply hθp
      have : orderOf (⟨y * a * y⁻¹ * a⁻¹, hz⟩ : ↥θ) ∣ Nat.card ↥θ := orderOf_dvd_natCard _
      rw [← Subgroup.orderOf_coe] at this
      simp only [h] at this
      exact this
  have hz1 : y * a * y⁻¹ * a⁻¹ = 1 := orderOf_eq_one_iff.mp hord
  exact mul_inv_eq_one.mp hz1

theorem commute_of_distinct_components_M {p : ℕ} (hp : p.Prime) {M E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEM : E ≤ M) {I₁ I₂ : Subgroup G}
    (h1 : I₁.subgroupOf M ∈ thetaComponents p ↥M) (h2 : I₂.subgroupOf M ∈ thetaComponents p ↥M)
    (hne : I₁.subgroupOf M ≠ I₂.subgroupOf M) (h1M : I₁ ≤ M) (h2M : I₂ ≤ M) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ I₁) (hk₂ : k₂ ∈ I₂) (hn₁ : k₁ ∈ Subgroup.normalizer (E : Set G))
    (hn₂ : k₂ ∈ Subgroup.normalizer (E : Set G)) :
    E.normalizerMonoidHom ⟨k₁, hn₁⟩ * E.normalizerMonoidHom ⟨k₂, hn₂⟩ =
      E.normalizerMonoidHom ⟨k₂, hn₂⟩ * E.normalizerMonoidHom ⟨k₁, hn₁⟩ := by
  have hcomm := commutator_mem_theta_M hp h1 h2 hne h1M h2M k₁ hk₁ k₂ hk₂
  have hzN : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
    mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)
  have hzc := centralizes_of_mem_theta_M hp hE hEM hzN hcomm
  have hone : E.normalizerMonoidHom ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hzN⟩ = 1 := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    exact hzc a a.2
  have hprod : E.normalizerMonoidHom ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, hzN⟩ =
      E.normalizerMonoidHom ⟨k₁, hn₁⟩ * E.normalizerMonoidHom ⟨k₂, hn₂⟩ *
        (E.normalizerMonoidHom ⟨k₁, hn₁⟩)⁻¹ * (E.normalizerMonoidHom ⟨k₂, hn₂⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hprod] at hone
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hone)

end CFSG.RankThree.PartOne.Q1327

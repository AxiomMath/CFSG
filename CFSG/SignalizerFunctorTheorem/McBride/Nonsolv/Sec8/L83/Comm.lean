module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {G : Type*} [Group G]

@[expose] def vK (Ω : Set (Subgroup G)) (V K : Subgroup G) : Subgroup G :=
  V ⊓ Subgroup.centralizer ((sSup (Ω \ {K}) : Subgroup G) : Set G)

theorem vK_le (Ω : Set (Subgroup G)) (V K : Subgroup G) : vK Ω V K ≤ V :=
  inf_le_left

theorem le_centralizer_vK {Ω : Set (Subgroup G)} {V K K' : Subgroup G} (hK' : K' ∈ Ω)
    (hne : K' ≠ K) : K' ≤ Subgroup.centralizer ((vK Ω V K : Subgroup G) : Set G) :=
  Subgroup.le_centralizer_iff.mp (inf_le_right.trans (Subgroup.centralizer_le
    (SetLike.coe_subset_coe.mpr (le_sSup (show K' ∈ Ω \ {K} from ⟨hK', hne⟩)))))

theorem le_vK {Ω : Set (Subgroup G)} {V K X : Subgroup G} (hXV : X ≤ V)
    (h : ∀ K' ∈ Ω, K' ≠ K → K' ≤ Subgroup.centralizer (X : Set G)) : X ≤ vK Ω V K :=
  le_inf hXV (Subgroup.le_centralizer_iff.mpr (sSup_le fun K' hK' => h K' hK'.1 hK'.2))

theorem commutator_sup_le {M Z : Subgroup G} (hZM : Z ≤ Subgroup.normalizer (M : Set G))
    (hZ : Z ≤ Subgroup.centralizer (Z : Set G)) : ⁅M ⊔ Z, M ⊔ Z⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M Z hZM] at hg₁ hg₂
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hg₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hg₂
  have hz : z₁ * z₂ * z₁⁻¹ = z₂ := by
    rw [(Subgroup.mem_centralizer_iff.mp (hZ hz₁) z₂ hz₂).symm]
    group
  have h1 : z₁ * m₂ * z₁⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hZM hz₁) m₂).mp hm₂
  have h2 : z₂ * m₁⁻¹ * z₂⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hZM hz₂) m₁⁻¹).mp (inv_mem hm₁)
  have e : ⁅m₁ * z₁, m₂ * z₂⁆ =
      m₁ * (z₁ * m₂ * z₁⁻¹) * (z₁ * z₂ * z₁⁻¹) * (m₁⁻¹ * z₂⁻¹ * m₂⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, hz]
  have e2 : m₁ * (z₁ * m₂ * z₁⁻¹) * z₂ * (m₁⁻¹ * z₂⁻¹ * m₂⁻¹) =
      m₁ * (z₁ * m₂ * z₁⁻¹) * (z₂ * m₁⁻¹ * z₂⁻¹) * m₂⁻¹ := by group
  rw [e2]
  exact mul_mem (mul_mem (mul_mem hm₁ h1) h2) (inv_mem hm₂)

theorem commutator_self_le (N : Subgroup G) : ⁅N, N⁆ ≤ N :=
  Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)

variable {Ω : Set (Subgroup G)} {V Z : Subgroup G}

theorem sup_vK_le_centralizer
    (hΩ : ∀ K ∈ Ω, ∀ K' ∈ Ω, K ≠ K' → K ≤ Subgroup.centralizer (K' : Set G))
    (hV : V ≤ Subgroup.centralizer (V : Set G)) {K K' : Subgroup G} (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hne : K ≠ K') :
    K ⊔ vK Ω V K ≤ Subgroup.centralizer ((K' ⊔ vK Ω V K' : Subgroup G) : Set G) := by
  rw [CFSG.SignalizerFunctorTheorem.centralizer_sup]
  refine sup_le (le_inf (hΩ K hK K' hK' hne) (le_centralizer_vK hK hne)) (le_inf ?_ ?_)
  · exact Subgroup.le_centralizer_iff.mp (le_centralizer_vK hK' hne.symm)
  · exact (vK_le Ω V K).trans (hV.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (vK_le Ω V K'))))

theorem commutator_normalized
    (hΩ : ∀ K ∈ Ω, ∀ K' ∈ Ω, K ≠ K' → K ≤ Subgroup.centralizer (K' : Set G))
    (hV : V ≤ Subgroup.centralizer (V : Set G)) (hZV : Z ≤ V)
    (hZ : Z ≤ ⨆ K ∈ Ω, vK Ω V K) {L : Subgroup G} (hL : L ∈ Ω) :
    ⁅L ⊔ Z, L ⊔ Z⁆ ≤ L ⊔ Z ∧
      Z ⊔ sSup Ω ≤ Subgroup.normalizer ((⁅L ⊔ Z, L ⊔ Z⁆ : Subgroup G) : Set G) := by
  have hWN : ∀ K ∈ Ω,
      K ⊔ vK Ω V K ≤ Subgroup.normalizer ((L ⊔ vK Ω V L : Subgroup G) : Set G) := by
    intro K hK
    by_cases hKL : K = L
    · subst hKL
      exact Subgroup.le_normalizer
    · exact (sup_vK_le_centralizer hΩ hV hK hL hKL).trans (Subgroup.centralizer_le_normalizer _)
  have hZN : Z ≤ Subgroup.normalizer ((L ⊔ vK Ω V L : Subgroup G) : Set G) :=
    hZ.trans (iSup₂_le fun K hK => le_sup_right.trans (hWN K hK))
  have hZc : Z ≤ Subgroup.centralizer (Z : Set G) :=
    hZV.trans (hV.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV)))
  have hle : ⁅L ⊔ Z, L ⊔ Z⁆ ≤ L ⊔ vK Ω V L :=
    (Subgroup.commutator_mono (sup_le_sup_right le_sup_left Z)
      (sup_le_sup_right le_sup_left Z)).trans (commutator_sup_le hZN hZc)
  refine ⟨commutator_self_le _, sup_le ?_ (sSup_le fun K hK => ?_)⟩
  · exact fun g hg => mem_normalizer_commutator
      (Subgroup.le_normalizer ((le_sup_right : Z ≤ L ⊔ Z) hg))
  · by_cases hKL : K = L
    · subst hKL
      exact fun g hg => mem_normalizer_commutator
        (Subgroup.le_normalizer ((le_sup_left : K ≤ K ⊔ Z) hg))
    · have hKW : K ≤ Subgroup.centralizer ((L ⊔ vK Ω V L : Subgroup G) : Set G) := by
        rw [CFSG.SignalizerFunctorTheorem.centralizer_sup]
        exact le_inf (hΩ K hK L hL hKL) (le_centralizer_vK hK hKL)
      exact (hKW.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle))).trans
        (Subgroup.centralizer_le_normalizer _)

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

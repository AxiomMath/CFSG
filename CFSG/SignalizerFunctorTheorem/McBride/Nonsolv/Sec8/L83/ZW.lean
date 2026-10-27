module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Z0
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L83.Za

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L83

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G} {E K : Subgroup G}

theorem zOf_le_iSup_vK
    (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    (hB : TypeBCore p A θ E K) {B : Subgroup G} (hB2 : B ∈ signalizerFunctorEk p 2 A)
    (hEB : E ≤ B) :
    zOf S ≤ ⨆ K' ∈ Ind (thetaOf θ B), vK (Ind (thetaOf θ B)) (vOf S E) K' := by
  have hZA : A ≤ Subgroup.normalizer (zOf S : Set G) := fun g hg =>
    mem_normalizer_zOf (Counterexample.normalizes_of_isSr hS hg)
  have hZc : Nat.Coprime p (Nat.card (zOf S)) :=
    hS.1.1.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le (zOf_le S))
  have hpA : p ≤ Nat.card A := by
    rw [h.card]
    exact Nat.le_self_pow (by norm_num) p
  have h51 := iSup_centralizer_hyperplanes h.prime h.elemAbelian hpA hZA hZc
  refine h51.symm.le.trans (iSup₂_le fun A₀ hA₀ => ?_)
  have hA₀2 : A₀ ∈ signalizerFunctorEk p 2 A := by
    refine ⟨hA₀.1, Nat.eq_of_mul_eq_mul_left h.prime.pos ?_⟩
    rw [← hA₀.2, h.card]
    ring
  by_cases hEA₀ : E ≤ A₀
  · have hle : zOf S ⊓ Subgroup.centralizer (A₀ : Set G) ≤
        zOf (S ⊓ Subgroup.centralizer (E : Set G)) :=
      (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEA₀))).trans
        (inf_centralizer_le_zOf S E)
    exact hle.trans (zOf_inf_centralizer_le h hr hS hB hB2 hEB)
  · have hne : A₀ ≠ B := fun heq => hEA₀ (heq ▸ hEB)
    have hF₁ := h.inf_mem_E1_of_ne_E2 hA₀2 hB2 hne
    obtain ⟨a, haA, ha1, hF₁eq⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF₁
    have haA₀B : a ∈ A₀ ⊓ B := hF₁eq ▸ Subgroup.mem_zpowers a
    have haE : a ∉ E := by
      intro haE
      have hle : A₀ ⊓ B ≤ E := by
        rw [← hF₁eq]
        exact Subgroup.zpowers_le.mpr haE
      have heq : A₀ ⊓ B = E :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hB.mem.2, hF₁.2])
      exact hEA₀ (heq ▸ inf_le_left)
    have hz := zOf_inf_centralizer_le_of_mem h hr hS hB hB2 hEB haA₀B.2 haE ha1
    exact le_trans (inf_le_inf_left _
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA₀B.1))) hz

end L83

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

module

public import CFSG.Quasithin.EmptyFaithful.T1531Geom
public import CFSG.Quasithin.EmptyFaithful.T1531Stage2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem lemma_15_3_47 (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂) :
    Res15347 T M V₁ := by
  intro x hx
  by_cases hne : ⁅VZ T M, Subgroup.zpowers x⁆ = ⊥
  · exact Or.inl hne
  · right
    intro g hg
    have hxM : x ∈ M := r46.normalizer_ZS (Subgroup.centralizer_le_normalizer _ hx)
    have hnts := not_isTotSingular153_commutator c.hyp c.decomp hxM hx hne
    have hHv : M = Subgroup.normalizer (VZ T M : Set G) := c.hyp.isHv_of_inM' c.hyp.inM
    have hBM : Subgroup.normalizer ((⁅VZ T M, Subgroup.zpowers x⁆ : Subgroup G) : Set G) ≤ M := by
      by_contra hn
      have hBV : ⁅VZ T M, Subgroup.zpowers x⁆ ≤ VZ T M := by
        rw [Subgroup.commutator_le]
        intro v hv y hy
        have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) :=
          c.hyp.le_normalizer (Subgroup.zpowers_le.mpr hxM hy)
        have h1 : y * v⁻¹ * y⁻¹ ∈ VZ T M :=
          (Subgroup.mem_normalizer_iff.mp hyN v⁻¹).mp ((VZ T M).inv_mem hv)
        have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
          rw [commutatorElement_def]; group
        rw [e]
        exact (VZ T M).mul_mem hv h1
      by_cases hBeq : ⁅VZ T M, Subgroup.zpowers x⁆ = VZ T M
      · apply hn
        rw [hBeq, ← hHv]
      · exact hnts (r46.totSingular_of_normalizer _ hBV (bot_lt_iff_ne_bot.mpr hne)
          (lt_of_le_of_ne hBV hBeq) hn)
    exact r46.conj_le_centralizer g (hg.trans hBM)

theorem stage15347 : Stage15347 := fun _ _ _ _ _ _ _ _ _ c _ r46 => lemma_15_3_47 c r46

end CFSG.Quasithin

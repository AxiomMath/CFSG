module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace RootCentOmega

theorem mem_range_of_mul_mem_centralizer {U G : Type*} [Group U] [Group G] {ψ : U →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {y g : G} (hg : g ∈ ψ.range)
    (hyg : y * g ∈ Subgroup.centralizer (ψ.range : Set G)) : y ∈ ψ.range := by
  rw [hC, Subgroup.mem_bot] at hyg
  rw [eq_inv_of_mul_eq_one_left hyg]
  exact ψ.range.inv_mem hg

theorem exists_zpowers_sup_of_centralizer_le {U G : Type*} [Group U] [Group G] (ψ : U →* G)
    (hψ : Function.Injective ψ) {x u : U}
    (hx : Subgroup.centralizer {x} ≤ ggOTwoPrime (Subgroup.centralizer {x})) (Y : Subgroup G)
    (hY : ∀ y ∈ Y, y ∈ ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ (u * x * u⁻¹)}) :=
  ⟨1, Y.one_mem, fun y hy => Subgroup.mem_sup_right
    (OTwoGen.inf_centralizer_le_ggOTwoPrime ψ hψ (OTwoGen.centralizer_conj_le_ggOTwoPrime hx u)
      (hY y hy))⟩

end RootCentOmega

section Tags

theorem ggRootCentralizerCyclicTag_POmegaPlus : GGRootCentralizerCyclicTag .POmegaPlus := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ hadm _ hker hC r hr Y hY hYd
    obtain ⟨-, -, hn4⟩ := hadm
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn).le
    obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
    obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY hr2 ⊢
    obtain ⟨i, j, hij, s, t, -, hX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
    have hx' : x ∈ ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := by
      rw [← hX]
      exact hx
    obtain ⟨c₀, rfl⟩ := hx'
    have hc : Multiplicative.toAdd c₀ ≠ 0 := by
      intro h0
      have hc₀ : c₀ = 1 := by rw [← ofAdd_toAdd c₀, h0, ofAdd_zero]
      rw [hc₀, map_one, mul_one, mul_inv_cancel, map_one, orderOf_one] at hr2
      exact absurd hr2 (by norm_num)
    have hcx := RootCentOmega.centralizer_longRoot_plus_le (K := GaloisField 2 f) hn4 hij s t hc
    refine RootCentOmega.exists_zpowers_sup_of_centralizer_le ψ hinj hcx Y fun y hy => ?_
    obtain ⟨g, hg, hyg⟩ :=
      PsiDiag.SpinP.exists_mem_centralizer (K := GaloisField 2 f) hn ψ hker (hYd y hy)
    exact Subgroup.mem_inf.mpr
      ⟨RootCentOmega.mem_range_of_mul_mem_centralizer hC hg hyg, (hY hy).2⟩
  · intro ψ hadm
    exact absurd hadm.2.2 (by omega)

theorem ggRootCentralizerCyclicTag_POmegaMinus : GGRootCentralizerCyclicTag .POmegaMinus := by
  intro G _ _ n f ψ hadm _ hker hC r hr Y hY hYd
  obtain ⟨-, -, hn⟩ := hadm
  have hirr := minusCoeffs_irr 2 f
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 f) hirr hn).le
  obtain ⟨hr2, γ, ⟨-, hγl⟩, u, hru⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY ⊢
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx1 (map_one _)
  have hcx := RootCentOmega.centralizer_longRoot_minus_le hirr hn hij s t ha
  refine RootCentOmega.exists_zpowers_sup_of_centralizer_le ψ hinj hcx Y fun y hy => ?_
  obtain ⟨g, hg, hyg⟩ :=
    PsiDiag.SpinM.exists_mem_centralizer (K := GaloisField 2 f) hirr hn ψ hker (hYd y hy)
  exact Subgroup.mem_inf.mpr
    ⟨RootCentOmega.mem_range_of_mul_mem_centralizer hC hg hyg, (hY hy).2⟩

end Tags

end CFSG.StandardType

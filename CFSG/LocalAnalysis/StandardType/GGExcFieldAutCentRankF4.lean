module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Basic
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Form
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Lang
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Transfer
import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankGeneral
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

namespace ExcFieldAutCentRankF4

section Assembly


private theorem exists_centralizing_elemAbelian_field_F4
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {n f : ℕ}
    {ψ : adjointGroup .F4 (GaloisField 2 f) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (ggU .F4 n f).D .F4 n f ψ)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : orderOf y = p)
    (hni : ¬ GGPsiInnerDiag (ggU .F4 n f).D ψ y) :
    ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
      Nat.card Bs ≤ p * Nat.card E₀ := by
  classical
  have hpp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have hf : 1 ≤ f := hS.presents.1.1.2.1
  have hf0 : f ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  have hrange : ψ.range = G₀ := hS.range_eq
  have hker : ψ.ker ≤ Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) :=
    hS.presents.2.1.2
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  have hBsr : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_F4 G n f ψ G₀ hS.presents b (hS.bstar_le hb)
      (hS.innerDiag b hb)
    rw [hS.centralizer_eq_bot, Subgroup.mem_bot] at hbg
    rw [hrange, eq_inv_of_mul_eq_one_left hbg]
    exact G₀.inv_mem hg
  have hyM' : y ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hyM
  obtain ⟨α, hα⟩ := exists_aut_of_mem_normalizer ψ hinj hyM'
  have hαk : ∀ (k : ℕ) u, ψ ((α ^ k) u) = y ^ k * ψ u * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih => intro u; rw [pow_succ', MulAut.mul_apply, hα, ih]; group
  have hyp1 : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext fun u => hinj ?_
    rw [hαk, hyp1]
    simp
  have hnin : ∀ h : adjointGroup .F4 (GaloisField 2 f), α ≠ MulAut.conj h := by
    intro h hh
    apply hni
    refine ggPsiInnerDiag_of_mem_range _ ?_
    have hc : (ψ h)⁻¹ * y ∈ Subgroup.centralizer (G₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [← hrange] at hx
      obtain ⟨u, rfl⟩ := hx
      have e : y * ψ u * y⁻¹ = ψ h * ψ u * (ψ h)⁻¹ := by
        rw [← hα u, hh]
        simp [MulAut.conj_apply, map_mul, map_inv]
      calc ψ u * ((ψ h)⁻¹ * y) = (ψ h)⁻¹ * (ψ h * ψ u * (ψ h)⁻¹) * y := by group
        _ = (ψ h)⁻¹ * (y * ψ u * y⁻¹) * y := by rw [e]
        _ = (ψ h)⁻¹ * y * ψ u := by group
    rw [hS.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact ⟨h, rfl⟩
  have hNF : ∀ α : MulAut (adjointGroup .F4 (GaloisField 2 f)), α ^ p = 1 →
      (∀ h : adjointGroup .F4 (GaloisField 2 f), α ≠ MulAut.conj h) →
      ∃ (x : adjointGroup .F4 (GaloisField 2 f)) (σ : GaloisField 2 f ≃+* GaloisField 2 f),
        σ ^ p = 1 ∧ σ ≠ 1 ∧ α = MulAut.conj x * entrywiseAdjointAut .F4 σ := by
    intro α hαp hnin
    obtain ⟨σ, g, hσ1, hσp, hαg⟩ := exists_field_form (K := GaloisField 2 f) hpp hp2 hαp hnin
    exact ⟨g, σ, hσp, hσ1, hαg⟩
  have hTransfer : GGFieldRankTransfer .F4 (GaloisField 2 f) p := by
    intro σ hσp hσ1 B hB
    obtain ⟨E, hE, hcard⟩ :=
      exists_elemAbelian_fixSubfield (K := GaloisField 2 f) hpp hp2 σ hσ1 hσp hB
    refine ⟨E.map (fixedFieldInclusion σ), hE.map _, ?_, ?_⟩
    · intro x hx
      obtain ⟨u, -, rfl⟩ := hx
      exact entrywise_fixedFieldInclusion σ u
    · rw [Subgroup.card_map_of_injective (fixedFieldInclusion_injective σ)]
      exact hcard
  obtain ⟨hBel, hBcard⟩ := pullback_elemAbelian ψ hinj p Bs hBsr hS.elem
  exact exists_elemAbelian_centralizing_of_mulAut_field (τ := .F4) (K := GaloisField 2 f)
    (f := f) hpp hp2 hf hK hinj hrange hS.centralizer_eq_bot hBel
    (le_of_eq hBcard.symm) hyM hyp hNF hTransfer α hα hαp hnin

end Assembly

end ExcFieldAutCentRankF4

section Final


theorem ggExcFieldAutCentRank_F4 :
    GGExcFieldAutCentRank .F4 := by
  intro G _ _ p Bs G₀ n f ψ hS y hyM hyp _ hni
  exact ExcFieldAutCentRankF4.exists_centralizing_elemAbelian_field_F4 hS hyM hyp hni

end Final

end CFSG.StandardType

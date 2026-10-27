module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthFourHomDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthRTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorExt
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ChartsThreeFar
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeTwo
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Extension
import CFSG.Permutation.Embedding

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.PhanDn
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

private theorem t_swap_two_three_eq {G : Type} [Group G]
    {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
    {E : QuadExt F K (unitaryInvolution K 2 1)} {κ₂ : normOmega E 3 →* G}
    {t : Equiv.Perm (Fin 4) →* G}
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl)) :
    t (Equiv.swap 2 3) = κ₂ (normPerm E le_rfl (Equiv.swap 1 2)) := by
  have h := DFunLike.congr_fun ht₂ (Equiv.swap (1 : Fin 3) 2)
  simp only [MonoidHom.comp_apply] at h
  rw [← h, CFSG.Permutation.viaEmbeddingHom_swap]
  rw [show (Fin.succEmb 3) (1 : Fin 3) = (2 : Fin 4) from Fin.ext rfl,
    show (Fin.succEmb 3) (2 : Fin 3) = (3 : Fin 4) from Fin.ext rfl]

private theorem ggConjAut_congr {G : Type} [Group G] {Bs : Subgroup G} {g g' : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hg' : g' ∈ Subgroup.normalizer (Bs : Set G))
    (h : g = g') : ggConjAut Bs hg = ggConjAut Bs hg' := by
  subst h
  rfl

section Context


theorem ggQTwoOrthFourHomInput_holds : GGQTwoOrthFourHomInput := by
  intro hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB G _ _ B Bs x L D J 𝒦 hR hB eta i0 hSigned hAL
    hLab hRM hG0 w hw j hj hact
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  obtain ⟨-, hZ, hN, F, Kf, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2, π, κ₁, κ₂, χ, t,
    hlast, hzero, h₁, h₂, ht₁, ht₂, hpoint⟩ :=
    exists_permHom_of_qTwoOrth (k := 0) hcfg eta hAL hLab hSigned hG0 hw hj hact
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hcut : ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) :=
    ggBstar_mem_iff_coord_eq_one hcfg hZ hN eta i0 hAL
  have hX₁ : ∀ b : ↥Bs, (b : G) ∈ L → eta b (π (Fin.last 3)) = 1 := by
    intro b hb
    rw [hlast]
    exact (hcut b).mp hb
  have hX₂ : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom →
      eta b (((finRotate 4).trans π) (Fin.last 3)) = 1 := by
    intro b hb
    have hbj := (mem_map_conj_iff_coord_eq_one hw hact hcut b).mp hb
    rw [Equiv.trans_apply, finRotate_last, hzero]
    simpa only [Equiv.swap_apply_left] using hbj
  have hAct1 : ∀ (σ : Equiv.Perm (Fin 3))
      (hσ : κ₁ (normPerm E le_rfl σ) ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
        ((Fin.castSuccEmb (n := 3)).trans π.toEmbedding) σ) := fun σ hσ =>
    GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last (E := E) h₁ le_rfl hSC hX₁ σ hσ
  have hAct2 : ∀ (σ : Equiv.Perm (Fin 3))
      (hσ : κ₂ (normPerm E le_rfl σ) ∈ Subgroup.normalizer (Bs : Set G)),
      MulAut.congr eta (ggConjAut Bs hσ) = SpCoord.permAut (Equiv.Perm.viaEmbeddingHom
        ((Fin.castSuccEmb (n := 3)).trans ((finRotate 4).trans π).toEmbedding) σ) :=
    fun σ hσ =>
    GGSecFiveBPermOmKFrame.congr_normPerm_of_coord_last (E := E) h₂ le_rfl hSC hX₂ σ hσ
  have hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁,
      Commute (t (Equiv.swap 2 3)) y :=
    commute_anchorBlock_of_two_charts_three ht₁ ht₂ hpoint
  have ht23 := t_swap_two_three_eq ht₂
  have hN₂ : κ₂ (normPerm E le_rfl (Equiv.swap 1 2)) ∈ Subgroup.normalizer (Bs : Set G) :=
    GGSecFiveBPermOmKFrame.normPerm_mem_normalizer (hframe := h₂) (hr := le_rfl) (hSC := hSC) _
  have htN : t (Equiv.swap 2 3) ∈ Subgroup.normalizer (Bs : Set G) := ht23 ▸ hN₂
  have htAct : MulAut.congr eta (ggConjAut Bs htN) =
      SpCoord.permAut (Equiv.swap (π 2) (π (Fin.last 3))) := by
    rw [ggConjAut_congr htN hN₂ ht23, hAct2 _ hN₂, CFSG.Permutation.viaEmbeddingHom_swap]
    rfl
  have hR2 := GGSecFiveRouteCfg.commute_normPureBlock_conj_of_qTwoOrth_four hX hTCJ hRig hTPn
    hA8 hraw hiso hFC hLB hR hB eta i0 hSigned hAL hLab hRM hG0 hZ hN hF2 hlast h₁ ht₂ hpoint
    hC htN htAct
  obtain ⟨Ψ, hΨcast, hΨperm⟩ :=
    exists_hom_normOmegaCast_normPerm_three_of_card_two E hF2 t κ₁ ht₁ hC hR2
  refine ⟨hZ, hN, F, Kf, hFieldF, hFieldK, hAlgFK, hFinK, hCharK, E, hF2, π, κ₁, κ₂, χ, t, Ψ,
    hlast, hzero, h₁, h₂, ht₁, ht₂, hpoint, hAct1, hAct2,
    injective_normOmega_hom E (by norm_num) κ₁ h₁.1 Ψ hΨcast, hΨcast, hΨperm, ?_⟩
  rw [range_normOmega_hom E (by norm_num) t κ₁ Ψ hΨcast hΨperm, h₁.2.1]

end Context

end CFSG.StandardType

end

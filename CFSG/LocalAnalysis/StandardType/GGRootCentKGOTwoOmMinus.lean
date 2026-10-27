module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LieType.Universal.Spin.Twisted.Frame
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusAut
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusConj
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusStep
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LieType.Universal.Spin.Twisted.Datum

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem

namespace KGOm

theorem pCoreOf_le_range_of_longRoot_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {G : Type} [Group G]
    {ψ : spinGroup (quadMinus n K b c) →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer
      {ψ ((minusFrame n b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) true
        true (.ofAdd 1))}) ≤ ψ.range := by
  intro a ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := (GGRootNorm.pCoreOf_le _ ha).1
  obtain ⟨γ, φ, k, hconj, hφA⟩ := exists_conj_minusSemi_of_mem_normalizer hn4 hirr hψ ha_norm
  have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp
  have hc0 := map_longRoot_of_minusSemi (by omega) hirr hφA h01 true true 1
  rw [one_pow] at hc0
  obtain ⟨hCx, hLQ, hdisj, hQ⟩ := centralizer_decomp_minus hn4 hirr h01 true true one_ne_zero
  obtain ⟨h, hh, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha hc0 hconj
  have hcid := eq_self_of_minusLevi_conj hn4 hirr hφA h01 true true hh hkey
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := γ) fun z => by rw [hconj, hcid]

end KGOm

section Tags

private theorem pCoreOf_le_range_POmegaMinus {G : Type} [Group G] {n f : ℕ} (hn : 4 ≤ n)
    {ψ : (ggU .POmegaMinus n f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus n f).K)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {r : G}
    (hr : GGRootInvolution (ggU .POmegaMinus n f).D .POmegaMinus ψ r) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {r}) ≤ ψ.range := by
  have hirr := minusCoeffs_irr 2 f
  revert ψ
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), minusDatum n hirr⟩ from rfl]
  intro ψ hker hC hr
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
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hx
  have ha : a ≠ 0 := by
    rintro rfl
    exact hx1 (map_one _)
  obtain ⟨w, hw⟩ := KGOm.exists_conj_longRoot_std_minus hn hirr hij s t ha
  let ψ' := ψ.comp (MulAut.conj (u * w)).toMonoidHom
  have hψ' : Function.Injective ψ' := RCSTSp.comp_conj_injective hinj (u * w)
  have hrange : ψ'.range = ψ.range := RCSTSp.range_comp_conj ψ (u * w)
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hx₀ : ψ' ((minusFrame n _ _).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp)
      true true (.ofAdd 1)) = ψ (u * (minusFrame n _ _).longRoot hij s t (.ofAdd a) * u⁻¹) := by
    change ψ ((u * w) * _ * (u * w)⁻¹) = _
    rw [show ∀ y, (u * w) * y * (u * w)⁻¹ = u * (w * y * w⁻¹) * u⁻¹ from fun y => by group, hw]
  have h := KGOm.pCoreOf_le_range_of_longRoot_minus hn hirr hψ' hC'
  rw [hx₀, hrange] at h
  exact h

theorem ggRootCentOTwoTag_POmegaMinus : GGRootCentOTwoTag .POmegaMinus := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr _
  exact pCoreOf_le_range_POmegaMinus hadm.2.2 hker hC hr

end Tags

end CFSG.StandardType

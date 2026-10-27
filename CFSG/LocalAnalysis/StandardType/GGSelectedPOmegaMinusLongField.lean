module

public import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLong
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
import CFSG.LocalAnalysis.StandardType.PhanDNativeNodeMinus
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusRank
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusTorus
import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.Sporadic.ThSchreier.GlobalData

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
  CFSG.StandardType.RankOneXfer CFSG.LieType.Steinberg CFSG.StandardType.PsiDiagChar

theorem exists_selectedSL2Model_minusDatum_long_range
    {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    ∃ model : SelectedSL2Model (minusDatum n hirr) K (Pi.single k 1),
      model.phi.range = rankOne (minusDatum n hirr).rootGroup k ∧
        Set.range (fun t : K => model.phi (sl2Lower t)) =
          ((minusDatum n hirr).rootGroup (-Pi.single k 1) : Set _) := by
  letI : Fintype K := Fintype.ofFinite _
  have hroot : (Pi.single k 1 : Fin (n - 1) → ℤ) ∈ (minusDatum n hirr).roots :=
    (isCTRootSystem (minusDatum n hirr).isFiniteType (minusDatum n hirr).divisible).single_mem k
  set phi := rLong n b c hk with hphi
  have hupper : (sl2UpperUniSub K).map phi =
      (minusDatum n hirr).rootGroup (Pi.single k 1) :=
    PhanDNative.map_rLong_sl2UpperUniSub hirr hk
  have hdiag : ∀ a : Kˣ, phi (sl2Diag a) ∈ ggTorus (minusDatum n hirr) :=
    PhanDNative.rLong_sl2Diag_mem_ggTorus hirr hk
  have hX : (minusDatum n hirr).rootGroup (Pi.single k 1) =
      ((minusFrame n b c).longRoot
        (succ_ne_of_lt n hk) true false).range :=
    minusRootGroup_single_of_lt n hirr hk
  have hct := minusDatum_isCTGroupDatum n hirr hn
  have hext := minusDatum_steinbergExtras n hirr
  have hscalar : ∀ h ∈ ggTorus (minusDatum n hirr), ∃ c : K, ∀ t,
      h * phi (sl2Upper t) * h⁻¹ = phi (sl2Upper (c * t)) := by
    intro h hh
    obtain ⟨t, ht, htz⟩ := PsiDiag.exists_torus_conj_of_mem_ggTorus hct hext k
      (fun y hy z hz => PsiDiag.mul_comm_of_mem_range _ (hX ▸ hy) (hX ▸ hz)) hh
    obtain ⟨χ, hχ⟩ := PsiDiag.SpinM.torus_le_scalarAct_long hirr hk ht
    refine ⟨χ, fun a => ?_⟩
    have hup : ∀ s : K, phi (sl2Upper s) =
        (minusFrame n b c).longRoot (succ_ne_of_lt n hk)
          true false (Multiplicative.ofAdd s) := fun s => by
      rw [hphi, ← LevisExtras.tv01_eq_sl2Upper, rLong_tv01]
    have hmem : phi (sl2Upper a) ∈ (minusDatum n hirr).rootGroup (Pi.single k 1) := by
      rw [← hupper]
      exact Subgroup.mem_map.mpr ⟨sl2Upper a, mem_sl2UpperUniSub_iff.mpr ⟨a, rfl⟩, rfl⟩
    rw [htz _ hmem, hup, hχ, hup]
  have hlower : Set.range (fun t : K => phi (sl2Lower t)) =
      ((minusDatum n hirr).rootGroup (-Pi.single k 1) : Set _) := by
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      change phi (sl2Lower t) ∈ (minusDatum n hirr).rootGroup (-Pi.single k 1)
      rw [hphi, ← LevisExtras.tv10_eq_sl2Lower]
      exact rLong_lower hirr hk t
    · intro hg
      obtain ⟨t, rfl⟩ := rLong_param_lower hirr hk g hg
      refine ⟨t, ?_⟩
      show phi (sl2Lower t) = phi (tv 1 0 t)
      rw [LevisExtras.tv10_eq_sl2Lower]
  refine ⟨SelectedSL2Model.ofRootMap (minusDatum n hirr) (Pi.single k 1) hroot phi (rLong_injective hk)
      hupper hdiag hscalar, ?_, hlower⟩
  change _ = (minusDatum n hirr).rootGroup (Pi.single k 1) ⊔
    (minusDatum n hirr).rootGroup (-Pi.single k 1)
  exact SelectedSL2Model.ofRootMap_range (minusDatum n hirr) (Pi.single k 1) hroot phi
    (rLong_injective hk) hupper hdiag hscalar hlower


theorem exists_selectedSL2Model_POmegaMinus_long_range {n f : ℕ} (hn : 4 ≤ n) :
    ∃ δ ∈ (ggU .POmegaMinus n f).D.roots, GGLongRoot (ggU .POmegaMinus n f).D δ ∧
      ∃ model : SelectedSL2Model (ggU .POmegaMinus n f).D (GaloisField 2 f) δ,
        model.phi.range = ggRootLevi (ggU .POmegaMinus n f).D δ ∧
          Set.range (fun t : GaloisField 2 f => model.phi (sl2Lower t)) =
            ((ggU .POmegaMinus n f).D.rootGroup (-δ) : Set _) := by
  have hirr := minusCoeffs_irr 2 f
  let k : Fin (n - 1) := ⟨0, by omega⟩
  have hk : k.val + 1 < n - 1 := by dsimp [k]; omega
  obtain ⟨model, hrange, hlower⟩ :=
    exists_selectedSL2Model_minusDatum_long_range hn hirr hk
  refine ⟨Pi.single k 1, model.root_mem, ggLongRoot_minusDatum_single hirr hk,
    model, ?_, hlower⟩
  exact hrange

end CFSG.StandardType.SelectedRoot

end

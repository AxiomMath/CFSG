module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKToral
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusSign
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted


theorem ggSecFiveBPermLinOmK_exists_frame (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))
    (eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))) {i0 : Fin (r + 2)}
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0)
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1) (hωo : orderOf ω = p) :
    ∃ π : Fin (r + 2) ≃ Fin (r + 2), π 0 = i0 ∧
      ∃ (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) →* G) (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ),
        GGSecFiveBPermLinOmKFrame Bs X eta π κ χ := by
  classical
  let D : (Fin (r + 1) → Multiplicative (ZMod p)) →*
      spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) :=
    spinMinusSplitTorus hr (minusCoeffs_irr 2 f) hω
  have hD : Function.Injective D :=
    spinMinusSplitTorus_injective hr (minusCoeffs_irr 2 f) hω hωo
  have hZ : Subgroup.center (spinGroup (quadMinus (r + 2) (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = ⊥ :=
    PsiDiag.SpinM.center_eq_bot (minusCoeffs_irr 2 f) (by omega)
  have hcard := ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le hp2 hA
  obtain ⟨κ₀, hκ₀inj, hκ₀X, htor⟩ :=
    ggSecFiveBPermLinOmK_exists_toral hMp hp2 hf hr hBs hmark e hcard hω hωo
  have htorD : ∀ b ∈ Bs, ∃ t : Fin (r + 1) → Multiplicative (ZMod p), ∀ s,
      b * κ₀ s * b⁻¹ = κ₀ (D t * s * (D t)⁻¹) := by
    intro b hb
    obtain ⟨t, ht⟩ := htor b hb
    exact ⟨t, fun s => by simpa [D] using ht s⟩
  have hN : ∀ u : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2),
      (∀ f, ∃ f', u * D f * u⁻¹ = D f') →
      ∃ (π : Equiv.Perm (Fin (r + 1))) (ε : Fin (r + 1) → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', u * D f * u⁻¹ = D f' →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) := by
    intro u hu
    exact spinMinusSplitTorus_signedPerm_of_normalizes hr (minusCoeffs_irr 2 f) hω hωo u hu
  obtain ⟨T, hT, π', hπ'0, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align_of_toral hp2 hr eta hA hκ₀inj hκ₀X hD hZ htorD hN
  obtain ⟨χ, hχinj, hχapp⟩ := ggSecFiveBPermSpK_exists_frame_char hc hω hωo
  obtain ⟨W, hW⟩ := SpJoin.exists_conj_sign_of_update
    (D := D) (fun l => spinMinusSplitTorus_conj_update hr (minusCoeffs_irr 2 f) hω l) ε hε
  let τ : ↥Bs → spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) :=
    fun b => D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))
  have hτ : ∀ b, τ b = D (fun k => Multiplicative.ofAdd
      (ε k * Multiplicative.toAdd (T b k))) := fun _ => rfl
  have hα : ∀ t, MulAut.conj W⁻¹ (D t) =
      D (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (t k))) := by
    intro t
    simpa [MulAut.conj_apply] using hW t
  obtain ⟨κ, hκinj, hκX, hframe⟩ :=
    ggSecFiveBPermSpK_exists_signFree_of_conj hκ₀inj hκ₀X hT (α := MulAut.conj W⁻¹) hα hτ
  refine ⟨π', hπ'0, κ, χ, hκinj, hκX, hχinj, fun b => ?_⟩
  refine ⟨τ b, ?_, hframe b⟩
  have hdiag := spinMinusSplitTorus_diagAct hr (minusCoeffs_irr 2 f) hω
    (fun k : Fin (r + 1) => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))
  refine hdiag.congr ?_
  funext m
  have halign_m : Multiplicative.toAdd (T b m) =
      ε m * c * Multiplicative.toAdd (eta b (π' m.succ)) := by
    simpa [MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using halign (eta b) m
  rw [hχapp, ggSecFiveBPermSpK_sign_mul_eq (hε m) halign_m]

theorem ggSecFiveBPermOmKFrameInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermOmKFrameInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 hB hlab f K
    i0 hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hf, hK𝒦, ⟨ψ, hker, hrange⟩, hKe, hA⟩ := hcell
  have hr : 2 ≤ r := by omega
  have hcfg := hR.1.1
  obtain ⟨σ, χL, hLF⟩ :=
    exists_ggSecFiveBPermSpLFrame hMp hcfg.tableB_facts.1
      hcfg.1.2.2.2.2.2.1.2.1 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hR.1.2.2.1.1
      hcfg.card_bstar_inf_centralizer_L.le h4 eta hAfull (by omega) hker hrange r
      (Equiv.refl _)
  let ω : (GaloisField 2 f)ˣ := χL (Multiplicative.ofAdd 1)
  have hω : ω ^ p = 1 := by
    change (χL (Multiplicative.ofAdd 1)) ^ p = 1
    rw [← map_pow]
    have hpow : (Multiplicative.ofAdd 1 : Multiplicative (ZMod p)) ^ p = 1 := by
      rw [← ofAdd_nsmul]
      simp
    rw [hpow, map_one]
  have hωo : orderOf ω = p := by
    change orderOf (χL (Multiplicative.ofAdd 1)) = p
    rw [orderOf_injective χL hLF.2.2.1 (Multiplicative.ofAdd 1)]
    rw [orderOf_ofAdd_eq_addOrderOf]
    exact ZMod.addOrderOf_one p
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK𝒦
  have hmark : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hN
  have hBs : GGBstar p B Bs := hR.1.1.2.1
  exact ⟨r, ggSecFiveBPermLinOmK_exists_frame hMp hp2 (by omega) hr hBs hmark
    (Classical.choice hKe) eta hA hω hωo⟩

theorem ggSecFiveBPermOmChartInput_of_mp
    (hMp : GGInnerDiagMpInput) : GGSecFiveBPermOmChartInput :=
  ggSecFiveBPermOmChartInput_of_frames hMp (ggSecFiveBPermOmKFrameInput_of_mp hMp)

end CFSG.StandardType

end

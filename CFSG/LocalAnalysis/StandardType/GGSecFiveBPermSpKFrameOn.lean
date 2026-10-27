module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKAlignOn
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKToral
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKSigned
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
import CFSG.LocalAnalysis.StandardType.GGTorCPlane
import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem ggSecFiveBPermSpK_exists_chart_conj {G S : Type} [Group G] [Group S]
    {Bs X : Subgroup G} {κ₁ : S →* G} (hκ₁ : Function.Injective κ₁) (hκ₁X : κ₁.range = X)
    (P : S) {τ τ₁ : ↥Bs → S} (hτ : ∀ b, P * τ b * P⁻¹ = τ₁ b)
    (hframe : ∀ (b : ↥Bs) s, (b : G) * κ₁ s * (b : G)⁻¹ = κ₁ (τ₁ b * s * (τ₁ b)⁻¹)) :
    ∃ κ : S →* G, Function.Injective κ ∧ κ.range = X ∧
      ∀ (b : ↥Bs) s, (b : G) * κ s * (b : G)⁻¹ = κ (τ b * s * (τ b)⁻¹) := by
  let κ : S →* G := κ₁.comp (MulAut.conj P).toMonoidHom
  have hκ : ∀ s, κ s = κ₁ (P * s * P⁻¹) := fun _ => rfl
  refine ⟨κ, hκ₁.comp (MulAut.conj P).injective, ?_, fun b s => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj P).surjective,
      Subgroup.map_top, hκ₁X]
  · rw [hκ, hκ, hframe b, ← hτ b]
    congr 1
    group


open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl in
theorem ggSecFiveBPermSpK_exists_planeChartOn (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {I : Finset (Fin n)}
    {ι : Fin (r + 1) → Fin n} (hι : Function.Injective ι) (hI : ∀ j, j ∈ I ↔ ∃ k, ι k = j)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hζw : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹) (hζc : SpJoin.SpPlaneConj (GaloisField 2 f) p ζ) :
    ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
      (ζ' : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      ζ'.range = ζ.range ∧ Function.Injective κ ∧ κ.range = X ∧ Function.Injective ζ' ∧
      ∀ (b : ↥Bs) (s : StatedSp (r + 1) (GaloisField 2 f)),
        (b : G) * κ s * (b : G)⁻¹ =
          κ (SpJoin.spPlaneTorus (r + 1) ζ' (fun k => eta b (ι k)) * s *
            (SpJoin.spPlaneTorus (r + 1) ζ' (fun k => eta b (ι k)))⁻¹) := by
  classical
  have hIimage : I = Finset.univ.image ι := by
    ext j
    rw [hI j, Finset.mem_image]
    simp
  have hIcard : I.card = r + 1 := by
    rw [hIimage, Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
  have hcard := ggSecFiveBPermSpK_pow_mul_card_inf_centralizer_le_of_bBlockOn hp2 hA
  rw [hIcard] at hcard
  obtain ⟨hDin, κ₀, hκ₀inj, hκ₀range, htor⟩ :=
    ggSecFiveBPermSpK_exists_toral hMp hf hr hBs hmark e hcard hζc
  have hζ : Function.Injective ζ := ggSecFiveBPermSpK_zeta_injective hDin
  have hcenter : Subgroup.center (StatedSp (r + 1) (GaloisField 2 f)) = ⊥ :=
    ggSecFiveBPermSpK_center_statedSp_galoisField_eq_bot f (r + 1)
  obtain ⟨T, hTs, hTspec, hker⟩ :=
    ggSecFiveBPermSpK_exists_toralHom_of_card hκ₀inj hκ₀range hDin hcenter htor hcard
  let T' := T.comp eta.symm.toMonoidHom
  have hTs' : Function.Surjective T' := by
    intro y
    obtain ⟨b, hb⟩ := hTs y
    refine ⟨eta b, ?_⟩
    simpa [T'] using hb
  have hker' : ∀ x, T' x = 1 → ∀ j ∈ I, x j = 1 := by
    intro x hx j hj
    have hmem : (eta.symm x : G) ∈ Subgroup.centralizer (X : Set G) := hker (eta.symm x) hx
    simpa using ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer_of_bBlockOn hp2 hA hmem hj
  have hW : ∀ w ∈ bBlockOn n p I, ∃ (π : Equiv.Perm (Fin (r + 1)))
      (ε : Fin (r + 1) → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, Multiplicative.toAdd (T' (w x) (π i)) = ε i * Multiplicative.toAdd (T' x i) := by
    intro w hw
    rw [← hA] at hw
    obtain ⟨φ, hφ, hφw⟩ := Subgroup.mem_map.mp hw
    obtain ⟨π, ε, hε, hπ⟩ :=
      ggSecFiveBPermSpK_signedPerm_of_mem_automizer_of_normalizes hκ₀inj hκ₀range hcenter
        (fun u hu => TorC.exists_signedPerm_of_normalizes (F := GaloisField 2 f) (p := p)
          (Fact.out) hp2 hζ u hu) T hTs hTspec hφ
    refine ⟨π, ε, hε, fun x i => ?_⟩
    have hx : T' (w x) = T (φ (eta.symm x)) := by
      have hwapply : w x = eta (φ (eta.symm x)) := by
        rw [← hφw]
        simp [MulAut.congr_apply, MulEquiv.trans_apply]
      simp only [T', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hwapply, MulEquiv.symm_apply_apply]
    rw [hx]
    simpa [T'] using hπ (eta.symm x) i
  obtain ⟨σ, c, hc, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align_on hp2 hr hι hI T' hTs' hker' hW
  obtain ⟨ζ', hζ'inj, hζ'range, hζ'app⟩ := ggSecFiveBPermSpK_exists_calibratedZeta hc hζ
  have hτ : ∀ b : ↥Bs, SpJoin.spPlaneTorus (r + 1) ζ' (fun k => eta b (ι (σ k))) =
      SpJoin.spPlaneTorus (r + 1) ζ
        (fun k => Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k))) := by
    intro b
    refine TorC.spPlaneTorus_eq_of_forall fun k => ?_
    have halign_b : Multiplicative.toAdd (T b k) =
        ε k * c * Multiplicative.toAdd (eta b (ι (σ k))) := by
      simpa [T', MonoidHom.comp_apply, MulEquiv.symm_apply_apply] using halign (eta b) k
    show ζ' (eta b (ι (σ k))) =
      ζ (Multiplicative.ofAdd (ε k * Multiplicative.toAdd (T b k)))
    rw [hζ'app, ggSecFiveBPermSpK_sign_mul_eq (hε k) halign_b]
  obtain ⟨κ₁, hκ₁inj, hκ₁X, hframe₁⟩ := ggSecFiveBPermSpK_exists_signFree
    (τ := fun b => SpJoin.spPlaneTorus (r + 1) ζ' (fun k => eta b (ι (σ k))))
    hζw hκ₀inj hκ₀range hTspec hε hτ
  let P : StatedSp (r + 1) (GaloisField 2 f) :=
    CFSG.SeitzReduction.SymplecticPilot.permSp (GaloisField 2 f) σ.symm
  have hP : ∀ u : Fin (r + 1) → Multiplicative (ZMod p),
      P * SpJoin.spPlaneTorus (r + 1) ζ' u * P⁻¹ =
        SpJoin.spPlaneTorus (r + 1) ζ' (fun k => u (σ k)) := by
    intro u
    rw [SympMinus.sympMinus_permSp_conj_spPlaneTorus ζ' σ.symm u]
    congr 1
  obtain ⟨κ, hκinj, hκX, hframe⟩ := ggSecFiveBPermSpK_exists_chart_conj hκ₁inj hκ₁X P
    (τ := fun b => SpJoin.spPlaneTorus (r + 1) ζ' (fun k => eta b (ι k)))
    (fun b => hP fun k => eta b (ι k)) hframe₁
  exact ⟨κ, ζ', hζ'range, hκinj, hκX, hζ'inj, hframe⟩

theorem ggSecFiveBPermSpK_exists_planeChartOn_of_conj (hMp : GGInnerDiagMpInput) {G : Type}
    [Group G] [Finite G] {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs X : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs X)
    (e : ↥X ≃* StatedSp (r + 1) (GaloisField 2 f))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {I : Finset (Fin n)}
    {ι : Fin (r + 1) → Fin n} (hι : Function.Injective ι) (hI : ∀ j, j ∈ I ↔ ∃ k, ι k = j)
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I) :
    ∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
      (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
      Function.Injective κ ∧ κ.range = X ∧ Function.Injective ζ ∧
      ∀ (b : ↥Bs) (s : StatedSp (r + 1) (GaloisField 2 f)),
        (b : G) * κ s * (b : G)⁻¹ =
          κ (SpJoin.spPlaneTorus (r + 1) ζ (fun k => eta b (ι k)) * s *
            (SpJoin.spPlaneTorus (r + 1) ζ (fun k => eta b (ι k)))⁻¹) := by
  obtain ⟨ζ, hζw, hζc⟩ := SpJoin.exists_spPlaneConj (F := GaloisField 2 f) (p := p)
    (CharP.cast_eq_zero (GaloisField 2 f) 2) Fact.out hp2
  obtain ⟨κ, ζ', -, hframe⟩ :=
    ggSecFiveBPermSpK_exists_planeChartOn hMp hp2 hf hr hBs hmark e eta hι hI hA hζw hζc
  exact ⟨κ, ζ', hframe⟩

end CFSG.StandardType

end

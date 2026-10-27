module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueRootPlaneA
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalUInner
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.LieType.SteinbergBRSemidirectSLEven
public import CFSG.ClassicalInvolution.Phan.CenterScalars
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

namespace SLSU4Vac

private theorem det_eq_one_gfTwo (A : GL (Fin 4) (GaloisField 2 1)) :
    (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 1)).det = 1 := by
  have hcard : Nat.card (Units (GaloisField 2 1)) = 1 := by
    rw [Nat.card_units, GaloisField.card 2 1 (by norm_num)]
    norm_num
  haveI : Subsingleton (Units (GaloisField 2 1)) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet]
  rfl

private theorem card_specialLinearGroup_four_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 1)) = 20160 := by
  rw [← CFSG.Open.StatedAPI.card_statedSL 4 (GaloisField 2 1)]
  exact CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two
    (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num)

private theorem center_unitarySU_four :
    Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1
      (GaloisField 2 (2 * 1)) 4) = ⊥ := by
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1
      (GaloisField 2 (2 * 1)) := ⟨Nat.prime_two, by norm_num, by rw [hF]; norm_num⟩
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) :=
    CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have h3 : CFSG.LieType.Universal.Unitary.SUid
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4 =
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 (GaloisField 2 (2 * 1)) 4 :=
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4).trans rfl
  rw [← h3]
  rw [CFSG.ClassicalInvolution.Phan.center_SUid_eq hσ (by norm_num)]
  rw [h3]
  rw [← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hdat (n := 4) (by norm_num)]
  exact Subgroup.card_eq_one.mp (by
    rw [CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hdat (by norm_num : 1 ≤ 4)]
    norm_num)

end SLSU4Vac

theorem ggSix_false_of_slFourTwo {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {ψ : (ggU .PSL 4 1).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .PSL 4 1).D .PSL 4 1 ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) : False := by
  let F := GaloisField 2 1
  let ψ' : Matrix.SpecialLinearGroup (Fin (3 + 1)) F →* G := ψ
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hker' : ψ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (3 + 1)) F) := hker
  have hC : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [show ψ'.range = ggG0 3 B x L D J from hrange]
    exact s1.1
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin (3 + 1)) F) = ⊥ :=
    CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (m := 3 + 1) (by norm_num)
      (Or.inr (by dsimp [F]; rw [GaloisField.card 2 1 (by norm_num)]; norm_num))
  have hψinj : Function.Injective ψ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker'.trans hcenter.le
  have hBψ : Bs ≤ ψ'.range := by
    refine bstar_le_range_of_inner hC fun b hb => ?_
    obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag (m := 3) (by norm_num) hker'
      (hctx.2.2.2.2.2.2.1.2 b hb)
    set s : Matrix.SpecialLinearGroup (Fin (3 + 1)) F :=
      ⟨(A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F),
        SLSU4Vac.det_eq_one_gfTwo A⟩ with hs
    have hconj : ∀ u : Matrix.SpecialLinearGroup (Fin (3 + 1)) F,
        ψ' (InnerDiagA.conjSL A u) = ψ' s * ψ' u * (ψ' s)⁻¹ := by
      intro u
      rw [show ψ' s * ψ' u * (ψ' s)⁻¹ = ψ' (s * u * s⁻¹) by
        rw [map_mul, map_mul, map_inv]]
      congr 1
      have htoGL : Matrix.SpecialLinearGroup.toGL s = A := by
        rw [hs]
        apply Units.ext
        rfl
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, htoGL]
    refine ⟨ψ' s, ⟨s, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have h1 : ψ' u = (b * ψ' s) * ψ' u * (b * ψ' s)⁻¹ := by
      calc ψ' u = b * (b⁻¹ * ψ' u * b) * b⁻¹ := by group
        _ = b * ψ' (InnerDiagA.conjSL A u) * b⁻¹ := by rw [hA u]
        _ = b * (ψ' s * ψ' u * (ψ' s)⁻¹) * b⁻¹ := by rw [hconj u]
        _ = (b * ψ' s) * ψ' u * (b * ψ' s)⁻¹ := by group
    calc ψ' u * (b * ψ' s) = ((b * ψ' s) * ψ' u * (b * ψ' s)⁻¹) * (b * ψ' s) := by
          conv_lhs => rw [h1]
      _ = (b * ψ' s) * ψ' u := by group
  have hpow : 3 ^ 4 ∣ Nat.card Bs := by
    have hcardBs := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian
      (G := G) Nat.prime_three hctx.2.1.2.1
    rw [hcardBs]
    refine Nat.pow_dvd_pow 3 ?_
    have hle : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 Bs := by
      rw [← hcardBs]
      exact ggSixCtxV2_card_bstar hctx
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have hBdvd : Nat.card Bs ∣ Nat.card ψ'.range := Subgroup.card_dvd_of_le hBψ
  have hUeq : Nat.card ψ'.range =
      Nat.card (Matrix.SpecialLinearGroup (Fin (3 + 1)) F) :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hdvd : 3 ^ 4 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin (3 + 1)) F) :=
    hUeq ▸ (hpow.trans hBdvd)
  rw [show Nat.card (Matrix.SpecialLinearGroup (Fin (3 + 1)) F) = 20160 by
    dsimp [F]
    exact SLSU4Vac.card_specialLinearGroup_four_two] at hdvd
  norm_num at hdvd

theorem ggSix_false_of_suFourTwo {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {ψ : (ggU .PSU 4 1).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .PSU 4 1).D .PSU 4 1 ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) : False := by
  let F := GaloisField 2 (2 * 1)
  let ψ' : CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 1) 4 →* G := ψ
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hker' : ψ'.ker ≤ Subgroup.center (CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution F 2 1) 4) := hker
  have hC : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
    rw [show ψ'.range = ggG0 3 B x L D J from hrange]
    exact s1.1
  have hF : Nat.card F = (2 ^ 1) ^ 2 := by
    dsimp [F]
    rw [GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have hdat : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, by norm_num, by rw [hF]; norm_num⟩
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 2) (f := 1) hF 4
  let φ := SURep.ggFrameU hF ψ' P₀ hP₀
  have hBsφ : Bs ≤ φ.range := by
    intro b hb
    obtain ⟨s, hs, -⟩ := OrdPInnerSU.exists_eq_frame_of_innerDiag hF (by norm_num) (by norm_num)
      hker' hC hP₀ (by norm_num : Nat.Coprime 3 (Nat.gcd 4 (2 ^ 1 + 1)))
      (hctx.2.2.2.2.2.2.1.2 b hb) (hctx.2.1.2.1.2 b hb)
    exact ⟨s, hs⟩
  have hcenter : Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F 4) = ⊥ := by
    dsimp [F]
    exact SLSU4Vac.center_unitarySU_four
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (SURep.ker_ggFrameU_le hF ψ' P₀ hP₀ hker').trans hcenter.le
  have hkerGL : ∀ A : ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F 4),
      φ A = 1 ↔ (A : GL (Fin 4) F) ∈ Subgroup.center (GL (Fin 4) F) := by
    intro A
    have hscal : (A : GL (Fin 4) F) ∈ Subgroup.center (GL (Fin 4) F) ↔ A = 1 := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center (Fin 4) F]
      change A ∈ (CFSG.Open.StatedScalars (Fin 4) F).subgroupOf
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F 4) ↔ A = 1
      rw [← CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hdat (n := 4) (by norm_num)]
      constructor
      · intro hA
        have h1 : CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars hdat 4 = ⊥ :=
          Subgroup.card_eq_one.mp (by
            rw [CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars hdat (by norm_num : 1 ≤ 4)]
            norm_num)
        rw [h1, Subgroup.mem_bot] at hA
        exact hA
      · intro hA
        rw [hA]
        exact Subgroup.one_mem _
    rw [hscal]
    exact ⟨fun h => hφinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hpK : 3 ∣ Nat.card (Units F) := by
    dsimp [F]
    rw [Nat.card_units, GaloisField.card 2 (2 * 1) (by norm_num)]
    norm_num
  have h27 : Nat.card Bs ≤ 27 := by
    have h := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel
      (p := 3) (n := 4) (K := F) Nat.prime_three (by norm_num) hpK (by norm_num)
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F 4) φ hkerGL Bs hBsφ hctx.2.1.2.1
    simpa using h
  have h81 : 3 ^ 4 ≤ Nat.card Bs := ggSixCtxV2_card_bstar hctx
  omega

end Inputs

end CFSG.StandardType

end

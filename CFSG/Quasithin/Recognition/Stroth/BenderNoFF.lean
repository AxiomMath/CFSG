module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open CFSG.HardMathSupport.Cooperstein.Coordinator

noncomputable section

def suzukiGroupEquivSz (a : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : CFSG.Blueprint.suzukiGroup a K ≃* Sz a :=
  (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).trans
    (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm

theorem isQuasisimple_sz (a : ℕ) (ha : 1 ≤ a) : CFSG.IsQuasisimple ↥(Sz a) := by
  haveI : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (CFSG.SectionRank.suzukiMatrixGroup_nonabelian a (by omega))).1

theorem center_sz (a : ℕ) (ha : 1 ≤ a) : Subgroup.center ↥(Sz a) = ⊥ := by
  haveI : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
    (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).1
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (CFSG.SectionRank.suzukiMatrixGroup_nonabelian a (by omega))).2
  have hmap := Subgroup.map_center_eq (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)
  rw [hZ] at hmap
  exact Subgroup.map_eq_bot_iff_of_injective _
    (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).injective |>.1 hmap

theorem noIrrFFOffender_sz
    (a : ℕ) (ha : 1 ≤ a) : NoIrrFFOffender ↥(Sz a) := by
  intro W _ _ hW L E hLq hirr ⟨e⟩ hEN hEne hEel hEquad
  haveI : Nontrivial W := hirr.1
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hlt := (CFSG.QuasithinUnique.Setup.Family.suzuki_irreducible_normalizer_excludes
    a ha hK W hW L hLq.1 hirr.2
    (e.trans (suzukiGroupEquivSz a (GaloisField 2 (2 * a + 1)) hK).symm)).2.2.2.2
    E hEne hEel hEN
  exact hlt

theorem noIrrFFOffender_statedProjSU3
    {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    NoIrrFFOffender (StatedProj (StatedSU 3 (2 ^ n) F)) := by
  intro W _ _ hW L E hLq hirr ⟨e⟩ hEN hEne hEel hEquad
  have hnt : Nontrivial W := hirr.1
  have hadm : StatedLieAdmissible .PSU 3 2 n := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_⟩
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hle : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  exact CFSG.QuasithinUnique.Setup.X5.evenUnitaryThreeNoOffender n hn W hW hnt L E hLq.1
    hirr.2 hmodel hEne hEel hEN

theorem not_isFFModule_of_noIrrFFOffender {W : Type} [CommGroup W] [Finite W]
    {H L : Subgroup (MulAut W)} {Y : Type} [Group Y]
    (hW : ∀ w : W, w * w = 1) (hLF : L = quasithinGenFitting H)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : CFSG.pCore 2 ↥H = ⊥)
    (hY : NoIrrFFOffender Y) (e : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y)) :
    ¬ IsFFModule H := by
  intro hFF
  obtain ⟨A, hAH, hAne, hAel, hAoff⟩ := hFF
  obtain ⟨B, -, hB⟩ := exists_isBestOffender_le hAH hAne hAel hAoff
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hLcomp : Family.IsComp L H :=
    ⟨hLH, IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN)
      (IsSubnormal.refl H), ⟨hLq.1.commutator_eq_top, hLq.2.1⟩⟩
  have hLB : ⁅L, B⁆ ≠ ⊥ := commutator_ne_bot_of_elemAbelian hLF hO2 hB.1 hB.2.1 hB.2.2.1
  obtain ⟨hBN, -, ⟨sec⟩⟩ := Layer.Actor.irreducibleSectionProp W hW H L B hLcomp hB hLB
  set ρ : ↥L →* MulAut sec.W := sec.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hφ : ∃ k, ρ.rangeRestrict k ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 sec.lbar_ne_bot
    obtain ⟨k, hk⟩ := hsurj a
    exact ⟨k, hk ▸ ha⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hφ
  let eL := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hLq hsurj hker
  have hlt := hY sec.W
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_sq hW sec) ρ.range
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range sec.lbar_quasisimple
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_isIrrOn sec)
    ⟨eL.symm.trans e.some⟩
    (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_range_le_normalizer sec hBN)
    sec.abar_ne_bot sec.abar_elem sec.abar_quadratic
  exact absurd sec.abar_offender (not_le.2 hlt)

end

end CFSG.Quasithin.Stroth

end

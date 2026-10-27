module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.RankThree.PartTwo.CTU6.Long
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKRootComm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKSingleton
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUAgreement
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

theorem ggSecFiveBPermSU_exists_lFrame {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Subgroup G} {i0 : Fin n}
    (hc : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0) (π : Fin 4 ≃ Fin n) :
    ∃ (σ : SL(4, GaloisField 2 (2 * a)) →* G)
      (χ : Multiplicative (ZMod p) →* (GaloisField 2 (2 * a))ˣ),
      GGSecFiveBPermSpLFrame Bs L eta π σ χ := by
  have hcfg := hR.1.1
  have ha := hc.2.1
  have hn : 4 ≤ n := by rw [hc.1]
  obtain ⟨ψ, hker, hrange⟩ := hc.2.2.2.2.1
  exact exists_ggSecFiveBPermSpLFrame hMp hcfg.tableB_facts.1
    hcfg.1.2.2.2.2.2.1.2.1 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hR.1.2.2.1.1
    hcfg.card_bstar_inf_centralizer_L.le hn eta hA (by omega) hker hrange 2 π

theorem ggSecFiveBPermSU_exists_charts {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Subgroup G} {i0 : Fin n}
    (hcell : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0) :
    ∃ (φ : SL(4, GaloisField 2 (2 * a)) →* G)
      (κ : Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G),
      φ.ker ≤ Subgroup.center SL(4, GaloisField 2 (2 * a)) ∧ φ.range = L ∧
      Function.Injective κ ∧ κ.range = K ∧
      (φ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 (2 * a)) 3 1)).range =
        (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS0 _
          (CFSG.LieType.BorelTits.unitaryInvolution_involutive
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 a
              (by have := hcell.2.1; omega))))).range ∧
      (φ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 (2 * a)) 3 2)).range =
        (κ.comp (CFSG.RankThree.PartTwo.CTU6.rS1 _
          (CFSG.LieType.BorelTits.unitaryInvolution_involutive
            (CFSG.LieType.Universal.card_galoisField_two_mul 2 a
              (by have := hcell.2.1; omega))))).range ∧
      ∀ y ∈ (φ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 (GaloisField 2 (2 * a)) 3 0)).range,
        ∀ z ∈ (κ.comp (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range,
          y * z = z * y := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ0, c, hc0, κ, hκinj, hκK, hκrep,
    hact, hK0, hK1⟩ := ggSecFiveBPermSU_exists_calibrated_frame_short_commutators hMp hR eta hcell
  have ha := hcell.2.1
  obtain ⟨σ, χ, hσ⟩ := ggSecFiveBPermSU_exists_lFrame hMp hR eta hAL hcell π
  have hcfg := hR.1.1
  obtain ⟨-, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (hR.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.2.2.1
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hcell.2.2.2.1
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNy.1.2.2.2.2.1
  have hK2 := ggSecFiveBPermSU_singletonComm_K_rL hp hp2 h hcell.2.2.1 hBc hBsmax hyBs hKcomp
    hκinj hκK hζ hτ hc0 hact
  obtain ⟨h1, h2, hcross⟩ := ggSecFiveBPermSU_agreement_crossing_of_frames hp2 ha hBc hBsmax
    hxBs hLcomp hAL hσ h ⟨hκinj, hκK⟩ hK0 hK1 hK2
  let eH : CFSG.ClassicalGroups.UnitaryFlag.hypSU h 3 0 ≃*
      Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  let ρ := κ.comp eH.symm.toMonoidHom
  have hρinj : Function.Injective ρ := hκinj.comp eH.symm.injective
  have hρK : ρ.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 eH.symm.surjective, Subgroup.map_top]
    exact hκK
  exact ⟨σ, ρ, hσ.1, hσ.2.1, hρinj, hρK, h1, h2, hcross⟩

theorem ggSecFiveBPermSU_exists_recognized_pair {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Subgroup G} {i0 : Fin n}
    (hcell : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0) :
    ∃ Ψ : (ggU .PSU 8 a).K →* G,
      Ψ.ker ≤ Subgroup.center (ggU .PSU 8 a).K ∧ Ψ.range = L ⊔ K := by
  obtain ⟨φ, κ, hφ, hφL, hκinj, hκK, h1, h2, hcross⟩ :=
    ggSecFiveBPermSU_exists_charts hMp hR eta hAL hcell
  have hκker : κ.ker ≤ Subgroup.center _ := by
    rw [(MonoidHom.ker_eq_bot_iff κ).mpr hκinj]
    exact bot_le
  obtain ⟨Ψ, hker, hrange⟩ := ggSU8_even_of_charts hcell.2.1 φ hφ κ hκker h1 h2 hcross
  exact ⟨Ψ, hker, by rw [hrange, hφL, hκK]⟩

theorem ggSecFiveBPermSUDataInput_of_rec (hJ : BMaxJoinInput)
    (hRec : GGSecFiveBPermSURecInput) : GGSecFiveBPermSUDataInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab a K i0 hc
  obtain ⟨Ψ, hker, hrange⟩ :=
    hRec G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab a K i0 hc
  have hK : K ∈ 𝒦 := hc.2.2.2.1
  have hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n p i0 := hc.2.2.2.2.2.2
  have hpair : ggG0 p B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_bCoordinateBlock hJ hR e hP (by omega) hRM eta h𝒦 hLeta hK hA
  have hadm : StatedLieAdmissible .PSU 8 2 a :=
    ⟨Nat.prime_two, by have := hc.2.1; omega, by norm_num, by simp⟩
  exact Or.inr (Or.inr ⟨.PSU, 8, a,
    ggSecFivePres_of_psi_PSU hadm (by norm_num [bnRank]) Ψ hker
      (hrange.trans hpair.symm)⟩)

theorem ggSecFiveBPermSURecInput_holds : GGSecFiveBPermSURecInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta hAJ hAL hRM hG0 hB hlab a K i0 hcell
  exact ggSecFiveBPermSU_exists_recognized_pair ggInnerDiagMpInput_holds hR eta hAL hcell

end CFSG.StandardType

end

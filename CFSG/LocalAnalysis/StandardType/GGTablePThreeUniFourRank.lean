module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLiftThree
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofLieP
import CFSG.Open.StatedSUFieldChange
import CFSG.Open.PGLModelStated
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private theorem uniFourRank_center_eq_bot {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Subgroup.center (PSUg 4 K (2 ^ f)) = ⊥ :=
  CFSG.StandardType.TableBUE.center_proj_eq_bot (K := K) (n := f) (d := 4) hK
    (by norm_num) (by simp)

private theorem uniFourRank_conj_injective {G : Type} [Group G]
    (h : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro x y hxy
  have hz : x * y⁻¹ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : MulAut.conj (x * y⁻¹) g = g := by rw [h1]; rfl
    rw [MulAut.conj_apply] at h2
    have h3 : (x * y⁻¹) * g = g * (x * y⁻¹) := by
      calc (x * y⁻¹) * g = (x * y⁻¹) * g * (x * y⁻¹)⁻¹ * (x * y⁻¹) := by group
        _ = g * (x * y⁻¹) := by rw [h2]
    exact h3.symm
  rw [h, Subgroup.mem_bot] at hz
  exact mul_inv_eq_one.mp hz

private theorem uniFourRank_isElemAbelian_comap {G : Type} [Group G] {A : Subgroup (MulAut G)}
    {f : G →* MulAut G} (hf : Function.Injective f) (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.comap f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    show f ((x : G) * y) = f (y * (x : G))
    rw [map_mul, map_mul]
    have hcomm := hA.1.is_comm.comm ⟨f x, Subgroup.mem_comap.mp x.2⟩
      ⟨f y, Subgroup.mem_comap.mp y.2⟩
    simpa using congrArg (fun z : A => (z : MulAut G)) hcomm
  · apply hf
    rw [map_pow, hA.2 _ (Subgroup.mem_comap.mp hx), map_one]

private theorem uniFourRank_pRank_le_two {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hmod : 2 ^ f % 3 = 1) :
    CFSG.pRank 3 (PSUg 4 K (2 ^ f)) ≤ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have hcardN : Nat.card K = Nat.card (GaloisField 2 (2 * f)) := by
    rw [hK, GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm f 2]
  have hcardF : Fintype.card K = Fintype.card (GaloisField 2 (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardN
  have e1 : PSUg 4 K (2 ^ f) ≃* CFSG.Open.StatedProj
      (CFSG.Open.StatedSU 4 (2 ^ f) (GaloisField 2 (2 * f))) :=
    CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
      (FiniteField.ringEquivOfCardEq hcardF) 4 (2 ^ f)
  calc CFSG.pRank 3 (PSUg 4 K (2 ^ f))
      = CFSG.pRank 3 (CFSG.Open.StatedProj
          (CFSG.Open.StatedSU 4 (2 ^ f) (GaloisField 2 (2 * f)))) :=
        CFSG.pRank_congr_of_mulEquiv e1 3
    _ = CFSG.pRank 3 (CFSG.PGLModel.projSU 4 2 f) :=
        CFSG.pRank_congr_of_mulEquiv (CFSG.PGLModel.projSUEquivStatedProj 4 2 f).symm 3
    _ ≤ 2 := CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_projSU_four_le_two (p := 2) (f := f)
        (by norm_num) hf hmod

theorem uni_four_rank_of_dvd_sub_one {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q - 1) {Ā : Subgroup (MulAut (PSUg 4 K q))} (hĀ : IsElemAbelian 3 Ā)
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K q))
      (LargeEvenGUSet (Fin 4) K q)) :
    Nat.card Ā ≤ 3 ^ 2 := by
  obtain ⟨f, hf, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod : 2 ^ f % 3 = 1 := by
    obtain ⟨k, hk⟩ := hq3
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 2 ^ f = 3 * k + 1 := by omega
    rw [h2, Nat.mul_add_mod_self_left]
  have hpRank : CFSG.pRank 3 (PSUg 4 K (2 ^ f)) ≤ 2 := uniFourRank_pRank_le_two hf hK hmod
  have hInn : Ā ≤ LargeEvenInnSet (PSUg 4 K (2 ^ f)) := by
    intro a ha
    exact CFSG.LocalAnalysis.GLTheoremA.K155XOr.orth_matConj_SU_sub_inn (E := K) (q := 2 ^ f)
      (f := f) rfl hf hK (hĀI a ha)
  have hcenter : Subgroup.center (PSUg 4 K (2 ^ f)) = ⊥ := uniFourRank_center_eq_bot hK
  have hinj : Function.Injective (MulAut.conj : PSUg 4 K (2 ^ f) →* MulAut (PSUg 4 K (2 ^ f))) :=
    uniFourRank_conj_injective hcenter
  let Esub : Subgroup (PSUg 4 K (2 ^ f)) :=
    Ā.comap (MulAut.conj : PSUg 4 K (2 ^ f) →* MulAut (PSUg 4 K (2 ^ f)))
  have hEmap : Esub.map (MulAut.conj : PSUg 4 K (2 ^ f) →* MulAut (PSUg 4 K (2 ^ f))) = Ā := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hInn
  have hEcard : Nat.card Esub = Nat.card Ā := by
    rw [← hEmap, Subgroup.card_map_of_injective hinj]
  have hEelem : CFSG.IsElementaryAbelian 3 Esub :=
    CFSG.RankThree.PartTwo.Sec14.Proof1413Res2.isElementaryAbelian_of_isElemAbelian
      (uniFourRank_isElemAbelian_comap hinj hĀ)
  calc Nat.card Ā = Nat.card Esub := hEcard.symm
    _ ≤ 3 ^ CFSG.pRank 3 (PSUg 4 K (2 ^ f)) :=
        CFSG.RankThree.PartTwo.Sec21.card_le_pow_pRank hEelem
    _ ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hpRank

end CFSG.StandardType.TablePThreeKG

end

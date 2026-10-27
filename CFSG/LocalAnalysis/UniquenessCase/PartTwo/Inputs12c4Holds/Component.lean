module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Quasithin.Background.B2FactorizationBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFiveA
import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Lift
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

private theorem nonempty_centerQuot_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B) :=
  ⟨QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)⟩

private theorem isQuasisimple_autI_and_centerQuot {M V L : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ normalizer (V : Set G)) (hP : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hL : F12.IsComponentModO2 M L) (hLV : ⁅L, V⁆ ≠ ⊥) :
    CFSG.IsQuasisimple ↥(autI hVe L) ∧
      Nonempty (↥(autI hVe L) ⧸ Subgroup.center ↥(autI hVe L) ≃*
        Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
  obtain ⟨hN, hq⟩ := hL.2.2.2
  have hPL : pCoreOf 2 M ≤ L := hL.1
  have hLM : L ≤ M := hL.2.1
  have hsn : CFSG.Open.IsSubnormal L M := hL.2.2.1
  haveI : ((pCoreOf 2 M).subgroupOf L).Normal := hN
  have hLnorm : L ≤ normalizer (V : Set G) := hLM.trans hMN
  let φ : ↥L →* MulAut (IntMod V hVe) := convHom hVe L hLnorm
  have hφrange : φ.range = autI hVe L := range_convHom hVe L hLnorm
  have hkerφ : (pCoreOf 2 M).subgroupOf L ≤ φ.ker := by
    rw [ker_convHom hVe L hLnorm]
    exact Subgroup.comap_mono (le_inf hPL hP)
  let φbar : (↥L ⧸ (pCoreOf 2 M).subgroupOf L) →* MulAut (IntMod V hVe) :=
    QuotientGroup.lift ((pCoreOf 2 M).subgroupOf L) φ hkerφ
  have hφbar_mk : ∀ l : ↥L, φbar (QuotientGroup.mk l) = φ l :=
    fun l => QuotientGroup.lift_mk' _ hkerφ l
  have hrangeφbar : φbar.range = autI hVe L := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H l => rw [hφbar_mk, ← hφrange]; exact MonoidHom.mem_range.mpr ⟨l, rfl⟩
    · intro hx
      obtain ⟨l, rfl⟩ := hφrange ▸ hx
      exact ⟨QuotientGroup.mk l, hφbar_mk l⟩
  have hne : φbar.ker ≠ ⊤ := by
    intro htop
    have hone : φbar = 1 := by
      refine MonoidHom.ext fun q => ?_
      exact MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top q)
    have hbot : φbar.range = ⊥ := by rw [hone, MonoidHom.range_one]
    rw [hrangeφbar] at hbot
    exact hLV (Subgroup.commutator_eq_bot_iff_le_centralizer.2
      ((autI_eq_bot_iff hVe hLnorm).1 hbot))
  have hQopen : CFSG.Open.IsQuasisimple (↥L ⧸ (pCoreOf 2 M).subgroupOf L) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hkerle : φbar.ker ≤ Subgroup.center (↥L ⧸ (pCoreOf 2 M).subgroupOf L) :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hQopen φbar.ker hne
  obtain ⟨hqrange, he⟩ :=
    CFSG.ComponentClassification.CatFC.KGHS3.quasisimple_range_of_ker_le_center hq φbar hkerle
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hrangeφbar).symm hqrange, ?_⟩
  have hsub : CFSG.pCore 2 ↥L = (pCoreOf 2 M).subgroupOf L := by
    have h := congrArg (fun S : Subgroup G => S.subgroupOf L)
      (TwelveTwentyFive.pCoreOf_eq hL)
    rw [show (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L from
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _] at h
    exact h
  obtain ⟨e₁⟩ := he
  obtain ⟨e₂⟩ := nonempty_centerQuot_mulEquiv (MulEquiv.subgroupCongr hrangeφbar).symm
  obtain ⟨e₃⟩ := nonempty_centerQuot_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq hsub).symm
  exact ⟨e₂.trans (e₁.trans e₃)⟩

theorem isComponentOf_autI {M V L : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ normalizer (V : Set G)) (hP : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hL : F12.IsComponentModO2 M L) (hLV : ⁅L, V⁆ ≠ ⊥) :
    CFSG.Open.IsComponentOf (autI hVe L) (autI hVe M) := by
  have hLM : L ≤ M := hL.2.1
  have hsn : CFSG.Open.IsSubnormal L M := hL.2.2.1
  have hsnmap : CFSG.Open.IsSubnormal (autI hVe L) (autI hVe M) := by
    have h := CFSG.Open.IsSubnormal.map (convHom hVe M hMN) (hsn.comap M.subtype)
    have htop : M.comap M.subtype = (⊤ : Subgroup ↥M) := Subgroup.subgroupOf_self M
    rw [htop, Subgroup.map_top, range_convHom hVe M hMN] at h
    have hmap : autI hVe L = (L.comap M.subtype).map (convHom hVe M hMN) :=
      autI_eq_map_convHom hVe hMN hLM
    rwa [← hmap] at h
  refine ⟨autI_mono hVe hLM, hsnmap, ?_⟩
  obtain ⟨hq, -⟩ := isQuasisimple_autI_and_centerQuot hVe hMN hP hL hLV
  exact ⟨hq.1.commutator_eq_top, hq.2.1⟩

theorem nonempty_centerQuot_autI_equiv {M V L : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hMN : M ≤ normalizer (V : Set G)) (hP : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hL : F12.IsComponentModO2 M L) (hLV : ⁅L, V⁆ ≠ ⊥) :
    Nonempty (↥(autI hVe L) ⧸ Subgroup.center ↥(autI hVe L) ≃*
      Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
  exact (isQuasisimple_autI_and_centerQuot hVe hMN hP hL hLV).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.McClurg

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.HPairGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaMinusFourIrr.Line
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaMinusFourIrr.Transport
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmegaTwo
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace OmegaMinusFourIrr

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem eq_top_of_forall_smul_e1M_mem (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {J : AddSubgroup (ιM → K)}
    (hJ : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v ∈ J, (γ : Matrix ιM ιM K) *ᵥ v ∈ J)
    (hall : ∀ d : K, d • KTabC.e1M K ∈ J) : J = ⊤ := by
  let S : Submodule K (ιM → K) :=
    { carrier := {v | ∀ d : K, d • v ∈ J}
      zero_mem' := fun d => by rw [smul_zero]; exact J.zero_mem
      add_mem' := fun hv hw d => by rw [smul_add]; exact J.add_mem (hv d) (hw d)
      smul_mem' := fun c x hx d => by rw [smul_smul]; exact hx (d * c) }
  have hS : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ x ∈ S,
      (γ : Matrix ιM ιM K) *ᵥ x ∈ S := by
    intro γ hγ x hx d
    have h1 := hJ γ hγ (d • x) (hx d)
    rwa [Matrix.mulVec_smul] at h1
  have he0 : KTabC.e1M K ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      simpa [KTabC.e1M] using congr_fun h0 (Sum.inl (0 : Fin (2 - 1)))
    exact one_ne_zero h1
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hmem : KTabC.e1M K ∈ S := hall
    rw [hbot, Submodule.mem_bot] at hmem
    exact he0 hmem
  have htop : S = ⊤ := by
    rcases CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaMinus_two hirr S hS with h | h
    · exact absurd h hSne
    · exact h
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
  simpa using hv 1

theorem isNatIrr_statedOmegaMinus_two (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Quasithin.H.PairG.IsNatIrr (StatedOmega (StatedQuadMinus 2 K b c)) := by
  intro J hJ
  by_cases hJne : J = ⊥
  · exact Or.inl hJne
  · obtain ⟨a, ha, haJ⟩ := exists_smul_e1M_mem hirr hJ hJne
    exact Or.inr (eq_top_of_forall_smul_e1M_mem hirr hJ (smul_e1M_mem hJ ha haJ))

end OmegaMinusFourIrr

theorem isIrrOn_of_natOmegaMinus_four {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {k : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 4 k) :
    PartTwo.IsIrrOn H ⊤ ⊥ := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  let : Field K := hField
  let : Finite K := hFinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 4 / 2 = 2 by norm_num] at hR
  have : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inl (0 : Fin (2 - 1))⟩
  exact PartTwo.isIrrOn_of_isNatIrr (OmegaMinusFourIrr.isNatIrr_statedOmegaMinus_two hirr) hR

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

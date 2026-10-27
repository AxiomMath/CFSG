module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Quasithin.EmptyFaithful.S146zYZSzArith
public import CFSG.Quasithin.EmptyFaithful.S146zYZSzCount
public import CFSG.Quasithin.EmptyFaithful.S146zYZSzData
public import Certificates.Certificate113
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.S146zY.SzNoFive

theorem sz_no_five :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m : ℕ) (y : A),
      IsSz m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) → y ∈ B → orderOf y = 5 → False := by
  intro A _ _ L B U m y hSz hUB hBL hUL hB hy hord
  obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := hSz
  let e' : ↥L ≃* CFSG.Open.Sz a := e.trans
    ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  have hU2 : IsPGroup 2 (U.subgroupOf L) :=
    hUL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUL.1).symm
  let S : Sylow 2 ↥L := hU2.toSylow hUL.2.2
  have H := szSylowData_of_equiv ha e' S
  have hSB : (S : Subgroup ↥L) ≤ B.subgroupOf L := fun x hx => hUB hx
  have hcardB : Nat.card (B.subgroupOf L) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hB' : ∀ r : ℕ, r.Prime → r ∣ Nat.card (B.subgroupOf L) → r = 2 ∨ r = 5 := by
    rw [hcardB]
    exact hB
  have h5B : 5 ∣ Nat.card (B.subgroupOf L) := by
    rw [hcardB, ← hord]
    exact Subgroup.orderOf_dvd_natCard B hy
  obtain ⟨j, hj⟩ := exists_five_pow_eq H (not_five_dvd_sq_mul_pred a) hSB hB' h5B
  exact sq_add_one_ne_five_pow a j ha hj

end CFSG.Quasithin.S146zY

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Transport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Bridges
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S265C.DynE

private theorem rckCP_dvd_card_of_not_centMod {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {L : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G)) (hyC : ¬ CentMod p L y) :
    p ∣ Nat.card ↥L := by
  by_contra hpd
  have hcop : Nat.Coprime p (Nat.card ↥L) := (hp.coprime_iff_not_dvd).2 hpd
  have hcore : GLAPPrimeCoreOf p L = L := gLAPPrimeCoreOf_eq_self_of_coprime hcop
  have hcomm : ⁅L, Subgroup.zpowers y⁆ ≤ GLAPPrimeCoreOf p L :=
    ((Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers y) (K := L)).1
      (Subgroup.zpowers_le.mpr hyN)).trans (le_of_eq hcore.symm)
  exact hyC ⟨hyN, hcomm⟩

theorem i141DynkinAt_notSmall_comp
    (hC : CompTypeLie2Small)
    {G : Type} [Group G] [Finite G] {p : ℕ} {L K A : Subgroup G} {y : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hLns : TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥L)
    (hAel : IsElemAbelian p A) (hInn : CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn p A L)
    (hyA : y ∈ A) (hyC : ¬ CentMod p L y)
    (hK : CFSG.Open.IsComponentOf K (L ⊓ Subgroup.centralizer ({y} : Set G))) :
    TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥K ∨
      Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hInn.1 hyA
  have hpL : p ∣ Nat.card ↥L := rckCP_dvd_card_of_not_centMod hp hyN hyC
  obtain ⟨labL, β, J', hlab, hcen, hin, hβp, hβ1, hJ', ⟨eK⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I141F.exists_sLevel_of_component hLq hAel hInn hyA hyC hK
  let eL : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
    CFSG.StandardType.RCKU33.u33_centerQuotEquivPSimple hp hLq hpL
  have hX : ∃ t r e, ¬ RCKSmallLieTag t ∧
      CFSG.Blueprint.LieModel (PSimple p L) t r 2 e := by
    obtain ⟨t, r, e, ht, hm⟩ := hLns
    exact ⟨t, r, e, ht, CFSG.Blueprint.LieModel.of_mulEquiv eL hm⟩
  have hl := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.lambda2_of_hasLabel hlab
  have hM := CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hlab
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := tag_ne_of_notSmall hX hl hM
  rcases hC (PSimple p L) labL β p hp hp2 hcen hin hβp hβ1 h1 h2 h3 h4 h5 h6 J' hJ' with
    ⟨t, r, e, ht, hm⟩ | h360
  · exact Or.inl ⟨t, r, e, ht, hm.of_mulEquiv eK.symm⟩
  · exact Or.inr ((Nat.card_congr eK.toEquiv).trans h360)

end CFSG.StandardType.RCKSmall

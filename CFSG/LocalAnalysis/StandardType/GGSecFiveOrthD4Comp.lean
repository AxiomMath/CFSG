module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSetup

public section

namespace CFSG.StandardType.OrthF3

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.LieType.Universal TauCeti

theorem ggOrthD4_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {ι : Additive ↥Bs ≃+ V} (S : GGOrthSetup B Bs x L D J 𝒦 Q ι) (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K) :
    CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K) := by
  have hR : GGSecFiveRestHyp 3 B Bs x L D J := S.cfg.1
  have hcfg : GGConfig 3 B Bs x L D J := hR.1
  have hI : GGThmIHyp 3 B x L := hcfg.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hK_le : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hnb.2.1
  have hJK : J ≤ K := le_of_ggNbr hL hI hDJ (hP G 3 B x L D J hI hDJ) hnb
  have hJleCx : J ≤ Subgroup.centralizer ({x} : Set G) := fun j hj => (hJY.1 hj).2
  have hJle : J ≤ Subgroup.centralizer ({x} : Set G) ⊓ K := le_inf hJleCx hJK
  have hNle : Subgroup.centralizer ({x} : Set G) ⊓ K ≤
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf (inf_le_right.trans hK_le) inf_le_left
  have hsub : CFSG.Assembly.IsSubnormal J (Subgroup.centralizer ({x} : Set G) ⊓ K) := by
    have h := hJY.2.1.inf_of_le hNle
    rwa [inf_eq_left.mpr hJle] at h
  exact ⟨hJle, hsub, hJY.2.2⟩

end CFSG.StandardType.OrthF3

end

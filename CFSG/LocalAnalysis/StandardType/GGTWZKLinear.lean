module

public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearDatum
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGTWZKRank
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem card_block_eq_of_ggResSideDatum
    {G : Type} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) (hr : 4 ≤ r)
    {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* X} (hψ : Function.Surjective ψ)
    (hker : ∀ g, ψ g = 1 → g ∈ scalars (r + 1) F)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ a t)
    (S : Finset (Fin (r + 1))) (hS : 2 ≤ S.card)
    (hJ : J = (blockSpecialLinear S).map (X.subtype.comp ψ))
    (hSide : GGResSideDatum p Bs X J) :
    S.card = r := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨V, hVadd, hVmod, ι, ρ, φ, h, α, hNperm, hρ, hφ, hlin, hrefl, hpair,
    ⟨eX, heX⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover hp2 hpF (by omega : 3 ≤ r) hBs hSC hN hψ hker hdiag
  have hρinj : Function.Injective ρ :=
    injective_perm_action_of_typeA_equiv ρ eX (ggAutomizer X Bs).subtype
      (Subgroup.subtype_injective _) (fun i => (hφ i).symm.trans (heX i).symm)
  have hmap : ((blockSpecialLinear S).map ψ).map X.subtype =
      (blockSpecialLinear S).map (X.subtype.comp ψ) :=
    Subgroup.map_map _ _ _
  have hAutoEq := TypeANbrDvd.ggAutomizer_blockSpecialLinear_ambient_eq
    (K := F) (d := r + 1) (p := p) (G := G) (X := X) (Bs := Bs)
    hp hp2 hpF hN hBs hSC hψ hker hdiag hNperm ρ hρ S
  have hAutoEqJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ := by
    rw [hJ, ← hmap]
    exact hAutoEq
  exact card_supported_eq_of_ggResSideDatum (by omega) ρ hρinj eX S hS hAutoEqJ hSide

theorem ggHasLabel_typeA_of_large_linear_side
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hr : 4 ≤ r)
    (hpq : p ∣ 2 ^ f - 1)
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    (hJK : J ≤ K) (hSide : GGResSideDatum p Bs K J) :
    GGHasLabel ⟨.A, r - 1, f⟩ (J ⧸ Subgroup.center J) ∧
      LargeEvenInLambda2 ⟨.A, r - 1, f⟩ := by
  classical
  obtain ⟨F, hField, hFinite, hChar, hN, ψ, hF, hψs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_K hRig hH hr hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hH.1 hH.2.2.2.2.1 hJK
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag ψ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  have hcomp' : CFSG.Assembly.IsComponentOf J (K ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x : Subgroup G) : Set G)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    hψs hker hdiag' (Subgroup.zpowers_le.mpr hx) hcomp'
  have hScard : S.card = r := card_block_eq_of_ggResSideDatum hp2
    (by simpa only [hF] using hpq) hr hH.1.tableB_facts.2.1 hH.1.2.1.2.2.2
    hN hψs hker hdiag S hS hJ hSide
  have hk : (K.subtype.comp ψ).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (r + 1)) F) := by
    intro g hg
    have hgψ : ψ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    exact scalars_le_center (r + 1) F (hker g hgψ)
  have hmodel : CFSG.Blueprint.LieModel (J ⧸ Subgroup.center J) .PSL r 2 f := by
    have hm := LinTorus.lieModel_map_blockSpecialLinear hF hΛ.1 hk (show 3 ≤ S.card by omega)
    rw [← hJ, hScard] at hm
    exact hm
  have hc : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (J ⧸ Subgroup.center J) .PSL (r - 1 + 1) 2 f := by
    have he : r - 1 + 1 = r := by omega
    rw [he]
    exact hmodel.statedClassicalModel (by decide)
  exact ⟨ggHasLabel_typeA hc, largeEvenInLambda2_typeA hc⟩

theorem not_ggResSideDatum_of_linear_centerPrime_of_le
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p r f : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hr : 4 ≤ r)
    (hpq : p ∣ 2 ^ f - 1) (hpd : p ∣ r + 1)
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (K ⧸ Subgroup.center K))
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hpJ : p ∣ labJ.rank + 3)
    (hJK : J ≤ K) (hSide : GGResSideDatum p Bs K J) : False := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hlabel, hlambda⟩ :=
    ggHasLabel_typeA_of_large_linear_side hRig hH hr hpq hΛ hLab hJK hSide
  have hiso := hRig labJ ⟨.A, r - 1, f⟩ _ hJΛ hlambda hJLab hlabel
  have hreq : labJ.rank = r - 1 := rank_eq_of_ggLabelIso_typeA_right (by omega) hiso
  have hd : p ∣ r + 2 := by
    simpa only [hreq, show r - 1 + 3 = r + 2 by omega] using hpJ
  have h1 : p ∣ 1 := by simpa using Nat.dvd_sub hd hpd
  exact hp.not_dvd_one h1

end CFSG.StandardType

end

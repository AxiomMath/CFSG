module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySides
public import CFSG.LocalAnalysis.StandardType.GGTWZKRank
public import CFSG.LocalAnalysis.StandardType.GGTWZKPrimeJ
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySix
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
public import CFSG.LocalAnalysis.StandardType.GGTWZKQuotient
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.Line63.H5
open CFSG.StandardType.TableBUE CFSG.StandardType.UnitTB CFSG.StandardType.LineU

theorem ggLabelIso_twA_eq_of_A_or_twA {labJ : LargeEvenLabel} {r f : ℕ}
    (hr : 3 ≤ r) (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hiso : GGLabelIso labJ ⟨.twA, r, f⟩) : labJ = ⟨.twA, r, f⟩ := by
  obtain ⟨t, l, m⟩ := labJ
  simp only [GGLabelIso] at hiso
  simp only [LargeEvenLabel.tag, LargeEvenLabel.rank, LargeEvenLabel.n] at hJtag
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all

theorem ggHasLabel_twA_of_supported_unitary_block
    {G : Type} [Group G] {K J : Subgroup G} {r f : ℕ}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hr : 4 ≤ r) (hF : Nat.card F = (2 ^ f) ^ 2)
    {φ : ↥(unitarySU 2 f F (r + 1)) →* K}
    (hM : UnitTB.Model φ) (S : Finset (Fin (r + 1)))
    (hJblock : J = (TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ))
    (hS_card : S.card = r) :
    GGHasLabel ⟨.twA, r - 1, f⟩ (J ⧸ Subgroup.center J) ∧
      LargeEvenInLambda2 ⟨.twA, r - 1, f⟩ := by
  classical
  have hf1 : 1 ≤ f := hM.field.one_le
  have hS3 : 3 ≤ S.card := by omega
  have hVq : (S.card, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h1 : S.card = 3 := congrArg Prod.fst h
    omega
  have hKd : UnitaryFieldData 2 f F := TableBU.unitaryFieldData_of_card hF hf1
  have hker : (K.subtype.comp φ).ker ≤
      Subgroup.center ↥(unitarySU 2 f F (r + 1)) :=
    UnitTB.ker_comp_subtype_le_center hM
  obtain ⟨e⟩ := SUTorus.nonempty_mulEquiv_quotient_center_blockSU hKd hker hS3 hVq
  have hLabBlockS : GGHasLabel ⟨.twA, S.card - 1, f⟩
      (↥((TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ)) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := F) (n := f) S).map
          (K.subtype.comp φ))) := by
    have hsc : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hF
      (hsc.symm ▸ e)
  have hLabBlock : GGHasLabel ⟨.twA, r - 1, f⟩
      (↥((TableBUE.blockSU (K := F) (n := f) S).map (K.subtype.comp φ)) ⧸
        Subgroup.center ↥((TableBUE.blockSU (K := F) (n := f) S).map
          (K.subtype.comp φ))) := by
    have h : S.card - 1 = r - 1 := by omega
    simpa only [h] using hLabBlockS
  have hΛBlock : LargeEvenInLambda2 ⟨.twA, r - 1, f⟩ := by
    refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hf1
      (by omega) ?_
    intro hb
    omega
  exact ⟨hJblock.symm ▸ hLabBlock, hΛBlock⟩

theorem ggHasLabel_twA_of_large_unitary_side
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {r f : ℕ} (hH : GGResHyp p B Bs x L D J y K)
    (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLabK : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    (hSide : GGResSideDatum p Bs K J) (hJK : J ≤ K) :
    GGHasLabel ⟨.twA, r - 1, f⟩ (J ⧸ Subgroup.center J) ∧
      LargeEvenInLambda2 ⟨.twA, r - 1, f⟩ := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨F, hField, hFinite, hChar, hN, ψ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_large_unitary_side hRig hH (Or.inr ⟨y, hnb⟩)
      hr hr5 hpq hpd hLabK hΛK
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hΛK.1
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eX, heX⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hf1 hp2 hpq (by omega : 3 ≤ r)
      hBs hSC hN hM hdiag
  have hρinj : Function.Injective ρ :=
    injective_perm_action_of_typeA_equiv ρ eX (ggAutomizer _ _).subtype
      (Subgroup.subtype_injective _) (fun i => (hφ i).symm.trans (heX i).symm)
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component
    (by omega : 2 ≤ r) hf1 hpq hBs hN hF hM hdiag
      (Set.singleton_subset_iff.mpr hx) hcomp
  have hAutoEqJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin (r + 1))) ((S : Set (Fin (r + 1)))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hM hF hp hp2 hpq
      (by omega : 4 ≤ r + 1) hN hBs hSC hdiag hNP ρ hρ S
  have hS_card : S.card = r :=
    card_supported_eq_of_ggResSideDatum (by omega : 1 ≤ r) ρ hρinj eX S hS2
      hAutoEqJ hSide
  exact ggHasLabel_twA_of_supported_unitary_block hr hF hM S hJblock hS_card

theorem ggZK_unitary_dangerous_of_J_le_K
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {r f : ℕ}
    (hH : GGResHyp p B Bs x L D J y K)
    (hr : 4 ≤ r) (hr5 : r ≠ 5) (hpq : p ∣ 2 ^ f + 1) (hpd : p ∣ r + 1)
    (hLabK : GGHasLabel ⟨.twA, r, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, r, f⟩)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpJ : p ∣ labJ.rank + 3)
    (hSide : GGResSideDatum p Bs K J) (hJK : J ≤ K) : False := by
  obtain ⟨hLabBlockJ, hΛBlock⟩ :=
    ggHasLabel_twA_of_large_unitary_side hRig hH hr hr5 hpq hpd hLabK hΛK hSide hJK
  have hiso := hRig labJ ⟨.twA, r - 1, f⟩ _ hJΛ hΛBlock hJLab hLabBlockJ
  have hlabJ := ggLabelIso_twA_eq_of_A_or_twA (by omega : 3 ≤ r - 1) hJtag hiso
  have hd : p ∣ r + 2 := by
    simpa only [hlabJ, LargeEvenLabel.rank, show r - 1 + 3 = r + 2 by omega] using hpJ
  exact (Fact.out : p.Prime).not_dvd_one (by simpa using Nat.dvd_sub hd hpd)

theorem ggLabelIso_twA_of_unitary_six_of_f_ne_one
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {f : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    (hpJ3 : 3 ∣ Nat.card J)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hSide : GGResSideDatum 3 Bs K J) :
    GGLabelIso labJ ⟨.twA, 4, f⟩ := by

  classical
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ3 hnb
  obtain ⟨F, hField, hFinite, hChar, hN, ψ, hF, hM, hdiag⟩ :=
    exists_diagonal_cover_of_unitary_six_side hRig hLB hH (Or.inr rfl)
      hf hpq hLabK hΛK hpJ3
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eX, heX⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF hΛK.1 hp2 hpq
      (by norm_num : 3 ≤ 5) hBs hSC hN hM hdiag
  have hρinj : Function.Injective ρ :=
    injective_perm_action_of_typeA_equiv ρ eX (ggAutomizer _ _).subtype
      (Subgroup.subtype_injective _) (fun i => (hφ i).symm.trans (heX i).symm)
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  obtain ⟨S, hJblock, hS2⟩ := exists_block_of_diagonal_unitary_component
    (p := 3) (r := 5) (f := f) (G := G)
    (by norm_num : 2 ≤ 5) hΛK.1 hpq hBs hN hF hM hdiag
      (Set.singleton_subset_iff.mpr hx) hcomp
  have hAutoEqJ : ggAutomizer J Bs =
      (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρ := by
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hM hF (by norm_num) hp2 hpq
      (by norm_num : 4 ≤ 6) hN hBs hSC hdiag hNP ρ hρ S
  have hS_card : S.card = 5 :=
    card_supported_eq_of_ggResSideDatum (by norm_num : 1 ≤ 5) ρ hρinj eX S hS2
      hAutoEqJ hSide
  obtain ⟨hLabBlockJ, hΛBlock⟩ :=
    ggHasLabel_twA_of_supported_unitary_block (by norm_num : 4 ≤ 5)
      hF hM S hJblock hS_card
  have hLabBlockJ4 : GGHasLabel ⟨.twA, 4, f⟩ (J ⧸ Subgroup.center J) := by
    simpa using hLabBlockJ
  have hΛBlock4 : LargeEvenInLambda2 ⟨.twA, 4, f⟩ := by
    simpa using hΛBlock
  exact hRig labJ ⟨.twA, 4, f⟩ (J ⧸ Subgroup.center J)
    hJΛ hΛBlock4 hJLab hLabBlockJ4

theorem ggZK_unitary_dangerous_six_of_f_ne_one
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {f : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hf : f ≠ 1) (hpq : 3 ∣ 2 ^ f + 1)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpJ : 3 ∣ labJ.rank + 3)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  classical
  have hpJ3 : 3 ∣ Nat.card J :=
    card_J_dvd_of_ggResHyp hH hJΛ hJLab hJtag hpJ
  have hiso := ggLabelIso_twA_of_unitary_six_of_f_ne_one
    hRig hLB hH hLabK hΛK hf hpq hpJ3 hJΛ hJLab hSide
  have hlabJ := ggLabelIso_twA_eq_of_A_or_twA (by norm_num : 3 ≤ 4) hJtag hiso
  have hp7 : 3 ∣ (7 : ℕ) := by
    simpa [hlabJ, LargeEvenLabel.rank] using hpJ
  norm_num at hp7

theorem ggLabelIso_twA_of_unitary_six_two
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    (hpJ3 : 3 ∣ Nat.card J)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hSide : GGResSideDatum 3 Bs K J) :
    GGLabelIso labJ ⟨.twA, 4, 1⟩ := by

  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hH.1.1 hH.1.2.2 hpJ3 hnb
  have hInn : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
  have hmark := ggInnerDiagOn_relabel hRig hInn hΛK hLabK
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, _, _, _, hP₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨heq, -, -⟩ := hP₀
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have hF4 : Nat.card F = 4 := by simpa using hFK
  have : CharP F 2 := charP_two_of_card (by simpa using hF4 : Nat.card F = 2 ^ 2)
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  obtain ⟨-, hN, hBI⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.tableB_facts.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hγcard : 3 ^ 4 ≤ Nat.card (ggGamma K hN).range :=
    four_le_card_ggGamma_of_unitary_six_side hRig hLB hH (Or.inr rfl)
      (by norm_num) hLabK hΛK hpJ3 hN
  obtain ⟨hNbar, φ, hM, hdiag⟩ := exists_diagonal_cover_of_unitary_six_two_red
    hF4 hXperf θ hN hBs hBI hγcard
  let NX : Subgroup G := Subgroup.normalizer (K : Set G)
  let Xbar : Subgroup (RedGrp K) := (redMkL K).range
  let Bbar : Subgroup (RedGrp K) := (redMkB hN).range
  let Jbar : Subgroup (RedGrp K) := (J.subgroupOf NX).map (redMk K)
  let C : Subgroup G := Subgroup.zpowers x
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hH.2.2.1.1
  have hNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub
      (fun a ha b hb => congrArg Subtype.val
        (hBs.1.is_comm.comm (⟨a, ha⟩ : Bs) ⟨b, hb⟩))
      hH.1.2.1.1 hH.1.2.2.1 hNL
  have hxD : x ∈ D := hH.1.2.2.1.2.2.2.1
  have hx : x ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hxD)
  have hCB : C ≤ Bs := Subgroup.zpowers_le.mpr hx
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hH.1 hnb hJK
  have hJC : IsComponentOf J (K ⊓ Subgroup.centralizer (C : Set G)) := by
    change IsComponentOf J (K ⊓ Subgroup.centralizer
      (Subgroup.zpowers x : Set G))
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hcomp
  have hXbar_image : (K.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (redMk K) = Xbar := by
    dsimp [Xbar]
    rw [redMkL, MonoidHom.range_comp, Subgroup.inclusion_range]
  obtain ⟨S, hS2, hJblock, -, hJbarLab⟩ :=
    exists_block_unitarySix_reduced hF4 hBs hN hCB hJC hJLab hNbar φ hM hdiag
  let eBs : ↥Bs ≃* ↥Bbar := MonoidHom.ofInjective (redMkB_injective hN hBs)
  have hXaut : ggAutomizer Xbar Bbar =
      (ggAutomizer K Bs).map (MulAut.congr eBs).toMonoidHom := by
    have h := ggAutomizer_redMk_eq hBs hN Subgroup.le_normalizer hN
    rw [hXbar_image] at h
    simpa [eBs] using h
  have hJaut : ggAutomizer Jbar Bbar =
      (ggAutomizer J Bs).map (MulAut.congr eBs).toMonoidHom := by
    have h := ggAutomizer_redMk_eq hBs hN
      (hJK.trans Subgroup.le_normalizer) hNJ
    simpa [Jbar, eBs] using h
  have hSideBar : GGResSideDatum 3 Bbar Xbar Jbar :=
    GGResSideDatum.transport eBs hXaut hJaut hSide
  have hF1 : Nat.card F = (2 ^ 1) ^ 2 := by rw [hF4]; norm_num
  have hBsbar : IsElemAbelian 3 Bbar := isElemAbelian_redB hN hBs
  have hSCbar : ∀ g ∈ Subgroup.centralizer (Bbar : Set (RedGrp K)),
      g ^ 3 = 1 → g ∈ Bbar := redSC hN hBs hSC
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨V, hVadd, hVmod, ι, ρ, φW, h, α, hNP, hρ, hφ, hlin, hrefl, hpair,
    ⟨eX, heX⟩, hclos⟩ :=
    exists_weyl_datum_of_diagonal_unitary_cover hF1 (by norm_num : 1 ≤ 1)
      hp2 (by norm_num : 3 ∣ 2 ^ 1 + 1) (by norm_num : 3 ≤ 5)
      hBsbar hSCbar hNbar hM hdiag
  have hρinj : Function.Injective ρ :=
    injective_perm_action_of_typeA_equiv ρ eX (ggAutomizer _ _).subtype
      (Subgroup.subtype_injective _) (fun i => (hφ i).symm.trans (heX i).symm)
  have hAutoEqJ : ggAutomizer Jbar Bbar =
      (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρ := by
    change ggAutomizer (Subgroup.map (redMk K) (J.subgroupOf NX)) Bbar =
      (fixingSubgroup (Equiv.Perm (Fin 6)) ((S : Set (Fin 6))ᶜ)).map ρ
    rw [hJblock]
    exact UnitAct.ggAutomizer_blockSU_ambient_eq_four hM hF1 (by norm_num) hp2
      (by norm_num : 3 ∣ 2 ^ 1 + 1) (by norm_num : 4 ≤ 6)
      hNbar hBsbar hSCbar hdiag hNP ρ hρ S
  have hS_card : S.card = 5 :=
    card_supported_eq_of_ggResSideDatum (by norm_num : 1 ≤ 5) ρ hρinj eX S hS2
      hAutoEqJ hSideBar
  obtain ⟨hLabBlockJbar, hΛBlockJbar⟩ :=
    ggHasLabel_twA_of_supported_unitary_block (by norm_num : 4 ≤ 5)
      hF1 hM S hJblock hS_card
  have hLabBlockJbar4 : GGHasLabel ⟨.twA, 4, 1⟩
      (Jbar ⧸ Subgroup.center Jbar) := by
    simpa [Jbar] using hLabBlockJbar
  have hΛBlockJbar4 : LargeEvenInLambda2 ⟨.twA, 4, 1⟩ := by
    simpa using hΛBlockJbar
  exact hRig labJ ⟨.twA, 4, 1⟩ (Jbar ⧸ Subgroup.center Jbar)
    hJΛ hΛBlockJbar4 hJbarLab hLabBlockJbar4

theorem ggZK_unitary_dangerous_six_two
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, 1⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, 1⟩)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpJ : 3 ∣ labJ.rank + 3)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpJ3 : 3 ∣ Nat.card J :=
    card_J_dvd_of_ggResHyp hH hJΛ hJLab hJtag hpJ
  have hiso := ggLabelIso_twA_of_unitary_six_two
    hRig hLB hH hLabK hΛK hpJ3 hJΛ hJLab hSide
  have hlabJ := ggLabelIso_twA_eq_of_A_or_twA (by norm_num : 3 ≤ 4) hJtag hiso
  have hp7 : 3 ∣ (7 : ℕ) := by
    simpa [hlabJ, LargeEvenLabel.rank] using hpJ
  norm_num at hp7

theorem ggLabelIso_twA_of_unitary_six_side
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {f : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hpq : 3 ∣ 2 ^ f + 1)
    (hpJ3 : 3 ∣ Nat.card J)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hSide : GGResSideDatum 3 Bs K J) :
    GGLabelIso labJ ⟨.twA, 4, f⟩ := by
  by_cases hf : f = 1
  · subst f
    exact ggLabelIso_twA_of_unitary_six_two
      hRig hLB hH hLabK hΛK hpJ3 hJΛ hJLab hSide
  · exact ggLabelIso_twA_of_unitary_six_of_f_ne_one
      hRig hLB hH hLabK hΛK hf hpq hpJ3 hJΛ hJLab hSide

theorem ggZK_unitary_dangerous_six
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {f : ℕ}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLabK : GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))
    (hΛK : LargeEvenInLambda2 ⟨.twA, 5, f⟩)
    (hpq : 3 ∣ 2 ^ f + 1)
    {labJ : LargeEvenLabel} (hJΛ : LargeEvenInLambda2 labJ)
    (hJLab : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpJ : 3 ∣ labJ.rank + 3)
    (hSide : GGResSideDatum 3 Bs K J) : False := by
  by_cases hf : f = 1
  · subst f
    exact ggZK_unitary_dangerous_six_two hRig hLB hH hLabK hΛK
      hJΛ hJLab hJtag hpJ hSide
  · exact ggZK_unitary_dangerous_six_of_f_ne_one hRig hLB hH hLabK hΛK
      hf hpq hJΛ hJLab hJtag hpJ hSide

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSix
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGSCNoTVCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open
open scoped MatrixGroups

section Unitary

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveE6QTwoCfg.card_bstar_eq_of_twA5
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L) :
    Nat.card Bs = 3 ^ 5 :=
  (GGSecFiveE6QTwoCfg.card_bstar_eq_or_of_twA5 hC hlab).resolve_right
    (GGSecFiveE6QTwoCfg.false_of_card_bstar_eq_three_pow_six hT hC hlab)

theorem GGSecFiveRouteCfg.center_eq_bot_of_twA5_E6
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hE6 : ∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e')
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 5) :
    Subgroup.center L = ⊥ := by
  classical
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hG : IsCharTwoType G := hconf.1.2.2.2.1
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hconf.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hconf.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
      IsCyclic S := fun S hSp hSL => hconf.1.2.2.2.2.2.2.1.2.2.2.2 S hSL hSp
  obtain ⟨e', rfl⟩ := hE6
  have hWeyl : GGWeylOfType 3 CoxeterMatrix.E₆
      (ggAutomizer L Bs ⊔ ggAutomizer (ggConjPreimage Bs (ggAutomizerJoin L Bs 𝒦)) Bs) := by
    rw [sup_ggAutomizer_ggConjPreimage]
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega (K := K) hK4
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center hK4 θ hperf hBs hNT hcard hxB hx1 hLx hBL hstar hBsN hI
      hWeyl
  obtain ⟨-, θ', hmap⟩ :=
    E6QTwo.card_inf_eq_and_exists_map_eq_torU_of_isPGroup hK4 θ hperf hZ2 hBs hcard hxB
      hx1 hBL hstar hBsN hI
  have hxL : x ∉ L := not_mem_of_isPGroup_two_center hZ2 horderx hLx
  have hN : (L.subgroupOf (Subgroup.centralizer {x})).Normal :=
    E6QTwo.normal_of_sStar_of_marking_twA5 hS
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hlab)
  have hconj : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ h : n * x * n⁻¹ ∈ L,
      θ' (QuotientGroup.mk (⟨n * x * n⁻¹, h⟩ : L)) = USixTwo.threeA hω :=
    exists_mem_normalizer_conj_eq_threeA hK4 hω θ' hZ2 hmap hBs hNT hcard hxB hxL hLx hWeyl
      card_coxeterE6_group
  exact E6QTwo.center_eq_bot_of_isPGroup_two hG hK4 hω θ' hperf hZ2 horderx hLx hN hcyc
    hBs hxB hcard hmap hconj

theorem GGSecFiveRouteCfg.center_eq_bot_of_twA5_E6_member
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hE6 : ∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e')
    (hBBs : B = Bs)
    {X : Subgroup G} (hX : X ∈ 𝒦)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs X)
    (hcard : Nat.card Bs = 3 ^ 5) :
    Subgroup.center X = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hG : IsCharTwoType G := hconf.1.2.2.2.1
  obtain ⟨-, hBs, -, -, -⟩ := hconf.tableB_facts
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hconf.2.1.2.2.2
  have hstdSub : LargeEvenStdSub 3 B x L D J := hconf.2.2
  obtain ⟨hperfX, K, hKfield, hKfinite, θ, hK4, hBsNX, hIX⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  obtain ⟨y, hnbr⟩ := hcfg.2.2.2.1.2 X hX
  have hSHat : LargeEvenSHat 3 B y X := hnbr.1
  have hBmax := hSHat.1
  have hyB := hSHat.2.1
  have hy1 := hSHat.2.2.1
  have hXy := hSHat.2.2.2.1
  have hyBs : y ∈ Bs := by simpa [hBBs] using hyB
  have hcen : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y := by
    simpa [hBBs] using inf_centralizer_eq_zpowers_of_sHat hSHat
  have hcardBL : Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ 3 := by
    have hle : (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤ Subgroup.zpowers y :=
      le_of_eq hcen
    have hcard' := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hcard'
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (hBs.2 y hyBs)
    have hne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    have horder : orderOf y = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
    rwa [horder] at hcard'
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S →
      S ≤ Subgroup.centralizer (X : Set G) → IsCyclic S := by
    intro S hSp hSX
    exact ggSCNoTV_isCyclic (p := 3) (by norm_num) hBs hstar hNT
      (hBsNX.trans (normalizer_le_normalizer_centralizer X)) hcardBL hSX hSp
  have hcomp : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hconf.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hstdSub hnbr)).1
  have hSStar : LargeEvenSStar 3 B y X :=
    ⟨hBmax, hyB, hy1, hcomp, fun S hSX hSp => hcyc S hSp hSX⟩
  have hN : (X.subgroupOf (Subgroup.centralizer ({y} : Set G))).Normal :=
    E6QTwo.normal_of_sStar_of_marking_twA5 hSStar
      (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hlab)
  obtain ⟨e', rfl⟩ := hE6
  let A : Subgroup (MulAut ↥Bs) := ggAutomizerJoin L Bs 𝒦
  have hAle : A ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top)
  have hXle : ggAutomizer X Bs ≤ A :=
    le_sup_of_le_right (le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) X hX)
  have hsup : ggAutomizer X Bs ⊔ ggAutomizer (ggConjPreimage Bs A) Bs = A := by
    rw [ggAutomizer_ggConjPreimage hAle]
    exact sup_eq_right.mpr hXle
  have hW : GGWeylOfType 3 CoxeterMatrix.E₆
      (ggAutomizer X Bs ⊔ ggAutomizer (ggConjPreimage Bs A) Bs) := by
    rw [hsup]
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  obtain ⟨ω, hω, φ, hLS, -⟩ :=
    E6QTwo.exists_localSetting_and_package (L := X) (M := ggConjPreimage Bs A) (x := y)
      hG hK4 θ hperfX hBs hNT hcard hyBs hy1 hXy hN hcyc hstar hBsNX hIX hW
  exact USixTwo.LocalSetting.center_L_eq_bot hLS

theorem GGSecFiveE6QTwoCfg.center_eq_bot_of_twA5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs L)
    (hcard : Nat.card Bs = 3 ^ 5) :
    Subgroup.center L = ⊥ := by
  obtain ⟨𝒦, hcfg, -, ι, M, e, hpres, hE6, -⟩ := hC
  exact hcfg.center_eq_bot_of_twA5_E6 hpres hE6 hlab hcard

theorem GGSecFiveE6QTwoCfg.unitaryEnd'
    (hRig : GGLabelRigidInput)
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hE6 : GGSecFiveWeylAt 3 B Bs x L D J CoxeterMatrix.E₆)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
      (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      USixTwo.LocalSetting hω x L φ Bs ∧
      (∃ W : Subgroup G, W ≤ Subgroup.normalizer (Bs : Set G) ∧
        W ⊓ Subgroup.centralizer {x} ≤
          (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) ∧
        (∃ n ∈ W, ∃ hnL : n * x * n⁻¹ ∈ L, φ ⟨n * x * n⁻¹, hnL⟩ = USixTwo.threeA hω) ∧
        ∃ g ∈ W, (∀ z ∈ Bs ⊓ L, g * z * g⁻¹ = z) ∧ g * x * g⁻¹ = x⁻¹) ∧
      ∃ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' ∧ ⁅K', K'⁆ = K' ∧ ¬ K' ≤ L ∧
        Bs ≤ L ⊔ K' := by
  classical
  obtain ⟨hRest, hG, hS, hBs, hxB, hx1, -, hLx, hstar, hcyc, hNT⟩ :=
    e6QTwo_config_facts hC
  have hIDall : GGInnerDiagAll 3 B Bs x L D J := hRest.2.2.1
  obtain ⟨y, K', hNbr, hWeyl⟩ := hE6
  have hSclosed : ∀ lab lab' : LargeEvenLabel, GGLabelIso lab lab' →
      (lab'.tag = .twA ∧ lab'.rank = 5 ∧ lab'.n = 1) →
      (lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) := by
    intro lab lab' hiso h'
    have heq : lab = lab' :=
      E6QTwo.eq_of_ggLabelIso_end hiso ⟨Or.inl ⟨h'.1, h'.2.1⟩, h'.2.2⟩
    rw [heq]
    exact h'
  have hlab' : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1)
      3 Bs L :=
    E6QTwo.innerDiagOnLabel_of_marking hRig hSclosed hIDall.1 hlab
  have hcard : Nat.card Bs = 3 ^ 5 := GGSecFiveE6QTwoCfg.card_bstar_eq_of_twA5 hT hC hlab'
  obtain ⟨hperf, K, hfieldK, hfiniteK, θ, hK4, hBsN, hI⟩ :=
    exists_unitaryDatum_of_innerDiagOnLabel_twA5 hlab'
  obtain ⟨ω, hω, φ, hLS, hWpkg⟩ :=
    E6QTwo.exists_localSetting_and_package hG hK4 θ hperf hBs hNT hcard hxB hx1 hLx
      (E6QTwo.normal_of_sStar_of_marking_twA5 hS hlab) hcyc hstar hBsN hI hWeyl
  refine ⟨K, hfieldK, hfiniteK, ω, hω, φ, hLS, hWpkg, y, K', hNbr, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_subtype_commutator K',
      (hIDall.2 y K' hNbr).1, Subgroup.map_top, Subgroup.range_subtype]
  · exact E6QTwo.not_le_of_weylOfType_E6 hBs hNT hxB hx1 hLx hWeyl hcard
  · exact E6QTwo.le_sup_of_weylOfType_E6 hBs hNT hBsN (GGInnerDiagOn.le_normalizer
      (hIDall.2 y K' hNbr)) hWeyl hcard

end Unitary

end CFSG.StandardType

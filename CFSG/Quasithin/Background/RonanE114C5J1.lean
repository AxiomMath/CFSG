module

public import CFSG.Quasithin.Background.RonanE114C5Gen
public import CFSG.Quasithin.Background.A312SporJ1
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.RonanE114ClausesL52He
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Quasithin.EmptyFaithful.SzN15Good
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.H13.QRCBenderPairModel
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.RonanE114.C5.J1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.Quasithin.A312S CFSG.Sporadic.J1

theorem levi5_of_simple_index_two {Z : Type} [Group Z] [Finite Z] {K : Subgroup Z}
    [hKs : IsSimpleGroup ↥K] (hK : Nat.card ↥K = 60) (hZ : Nat.card Z = 120) {u : Z}
    (hu : ∀ z : Z, u * z = z * u) (hu1 : u ≠ 1) :
    ∃ ρ : Z →* Equiv.Perm (Fin 5), IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range := by
  classical
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥K := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hKs
    rw [hK] at hp
    exact absurd hp (by norm_num)
  have hidx : K.index = 2 := by
    have h := K.card_mul_index
    rw [hK, hZ] at h
    omega
  haveI hKn : K.Normal := Subgroup.normal_of_index_eq_two hidx
  have huK : u ∉ K := fun huK =>
    hu1 (congrArg Subtype.val (P7.eq_one_of_commutes hnab (x := (⟨u, huK⟩ : ↥K))
      fun n => Subtype.ext (hu n.1).symm))
  have hu2 : u ^ 2 = 1 := by
    have h1 : u ^ K.index ∈ K := Subgroup.pow_index_mem K u
    rw [hidx] at h1
    have h2 : (⟨u ^ 2, h1⟩ : ↥K) = 1 :=
      P7.eq_one_of_commutes hnab (x := (⟨u ^ 2, h1⟩ : ↥K)) fun n =>
        Subtype.ext ((Commute.pow_left (show Commute u n.1 from hu n.1) 2).eq.symm)
    exact congrArg Subtype.val h2
  have hou : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  set V : Subgroup Z := Subgroup.zpowers u with hV
  haveI hVn : V.Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * u ^ k * g⁻¹ = u ^ k := by
      rw [(Commute.zpow_left (show Commute u g from hu g) k).eq.symm]
      group
    rw [this]
    exact Subgroup.zpow_mem_zpowers _ _⟩
  have hVcard : Nat.card V = 2 := by rw [hV, Nat.card_zpowers, hou]
  have hV2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 1) (by rw [hVcard]; rfl)
  have hKV : K ⊓ V = ⊥ := by
    have hdvd : Nat.card ↥(K ⊓ V) ∣ 2 := hVcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have : K ⊓ V = V := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hVcard, h2])
      have hmem : u ∈ K ⊓ V := by
        rw [this]
        exact Subgroup.mem_zpowers u
      exact huK hmem.1
  let φ : ↥K →* Z ⧸ V := (QuotientGroup.mk' V).comp K.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : Z) ∈ V := (QuotientGroup.eq_one_iff (x : Z)).mp hx
    have h2 : (x : Z) ∈ K ⊓ V := ⟨x.2, h1⟩
    rw [hKV, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hquot : Nat.card (Z ⧸ V) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [hVcard, hZ] at h
    omega
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hK, hquot]⟩
  let e1 : ↥K ≃* Z ⧸ V := MulEquiv.ofBijective φ hbij
  obtain ⟨eK⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty (G := ↥K) hK
  exact levi5_of_quotient hV2 (e1.symm.trans eK)

section Centralizer

theorem j1_cent_data (u : ↥J) (hou : orderOf u = 2) :
    Nat.card (Subgroup.centralizer ({u} : Set ↥J)) = 120 ∧
      ∃ KJ : Subgroup ↥J, KJ ≤ Subgroup.centralizer ({u} : Set ↥J) ∧ IsSimpleGroup ↥KJ ∧
        Nat.card ↥KJ = 60 := by
  set t : CFSG.Blueprint.NativeSporadic.J1 := nativeEquiv.symm u with ht
  have hot : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq]; exact hou
  set u' : Equiv.Perm (Fin 3080) :=
    ((CFSG.Sporadic.Schreier.j1PermEquiv t : CFSG.Sporadic.Schreier.j1P) :
      Equiv.Perm (Fin 3080)) with hu'
  have hu'P : u' ∈ CFSG.Sporadic.Schreier.j1P := (CFSG.Sporadic.Schreier.j1PermEquiv t).2
  have hou' : orderOf u' = 2 := by
    rw [hu', Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hot
  obtain ⟨h120, -, -⟩ := CFSG.Sporadic.Schreier.j1P_involution_centralizer u' hu'P hou'
  set φ := CFSG.Sporadic.Schreier.j1PermEquiv with hφ
  have hCt : Nat.card (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)) =
      120 := by
    have e1 : Nat.card (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)) =
        Nat.card ((Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)).map
          φ.toMonoidHom) := (Subgroup.card_map_of_injective φ.injective).symm
    rw [map_centralizer_equiv φ t] at e1
    have e2 : Nat.card (Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)) =
        Nat.card ((Subgroup.centralizer ({φ t} : Set ↥CFSG.Sporadic.Schreier.j1P)).map
          CFSG.Sporadic.Schreier.j1P.subtype) :=
      (Subgroup.card_map_of_injective CFSG.Sporadic.Schreier.j1P.subtype_injective).symm
    rw [map_centralizer_subtype] at e2
    rw [e1, e2, ← h120]
  have hCu : Nat.card (Subgroup.centralizer ({u} : Set ↥J)) = 120 := by
    have e1 := map_centralizer_equiv nativeEquiv t
    have hut' : nativeEquiv t = u := by rw [ht, MulEquiv.apply_symm_apply]
    rw [hut'] at e1
    rw [← e1, Subgroup.card_map_of_injective nativeEquiv.injective, hCt]
  refine ⟨hCu, ?_⟩
  obtain ⟨K, -, hKs, hK60, hKna, -⟩ :=
    CFSG.Sporadic.Schreier.qt_unique_j1_involution_centralizer_normal_simple_subgroup t hot
  set KJ : Subgroup ↥J :=
    (K.map (Subgroup.centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.J1)).subtype).map
      nativeEquiv.toMonoidHom with hKJ
  have eK : ↥KJ ≃* ↥K :=
    ((K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      ((K.map _).equivMapOfInjective nativeEquiv.toMonoidHom nativeEquiv.injective)).symm
  refine ⟨KJ, ?_, eK.isSimpleGroup, by rw [Nat.card_congr eK.toEquiv, hK60]⟩
  have h1 := map_centralizer_equiv nativeEquiv t
  rw [ht, MulEquiv.apply_symm_apply] at h1
  rw [← h1, ← ht]
  exact Subgroup.map_mono (Subgroup.map_subtype_le K)

end Centralizer

section Lattice

theorem member_or_top {Z : Subgroup ↥J} (hZ : E2P.SporB.j1S ≤ Z) :
    (∃ j < 17, Z = E2P.SporB.j1Y j) ∨ Z = ⊤ := by
  obtain ⟨j, hj, hZeq⟩ := E2P.SporB.j1_all Z hZ
  change j ≤ 17 at hj
  change Z = memberOrTop 17 E2P.SporB.j1Y j at hZeq
  by_cases h : j < 17
  · left
    exact ⟨j, h, by rw [hZeq]; simp [memberOrTop, h]⟩
  · right
    rw [hZeq]
    simp [memberOrTop, h]

def j1Idx (j : ℕ) : ℕ := #[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21][j]!

theorem card_Y {j : ℕ} (hj : j < 17) : Nat.card (E2P.SporB.j1Y j) = j1Idx j * 2 ^ 3 :=
  E2P.SporB.j1_Y_card hj

theorem card_Y16 : Nat.card (E2P.SporB.j1Y 16) = 168 := by
  rw [card_Y (by norm_num)]
  rfl

theorem good_Y16 : GoodGam (innerU E2P.SporB.j1S) (E2P.SporB.j1Y 16) := by
  by_cases hs : Group.IsSolvable ↥(E2P.SporB.j1Y 16)
  · exact GoodGam.solvable (inv_of_inner (E2P.SporB.j1_S_le_Y 16)) hs
  · haveI : IsSimpleGroup ↥(E2P.SporB.j1Y 16) := A312Ru.isSimpleGroup_of_card_168 card_Y16 hs
    have hpsl : IsPSL 3 2 1 ↥(E2P.SporB.j1Y 16) :=
      CFSG.Quasithin.HSRuLoc.Mod.isPSL_three_two_of_simple_card_168 card_Y16
    obtain ⟨φ⟩ := P7.exists_mulEquiv_sl3_of_isPSL hpsl
    refine GoodGam.levi3 (inv_of_inner (E2P.SporB.j1_S_le_Y 16)) ⟨φ.toMonoidHom, φ.surjective, ?_⟩
    have hker : φ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr φ.injective
    rw [hker]
    exact IsPGroup.of_card (n := 0) (by simp)

theorem exists_central_involution :
    ∃ u : ↥J, u ∈ E2P.SporB.j1S ∧ orderOf u = 2 ∧ ∀ s ∈ E2P.SporB.j1S, u * s = s * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥E2P.SporB.j1S := E2P.SporB.j1_S_isPGroup
  have hcard : Nat.card ↥E2P.SporB.j1S = 8 := by
    rw [E2P.SporB.j1_card_S]
    rfl
  haveI : Nontrivial ↥E2P.SporB.j1S :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  haveI : Nontrivial ↥(Subgroup.center ↥E2P.SporB.j1S) := hS2.center_nontrivial
  have hC2 : IsPGroup 2 ↥(Subgroup.center ↥E2P.SporB.j1S) := hS2.to_subgroup _
  obtain ⟨n, hn0, hn⟩ := hC2.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥E2P.SporB.j1S) := hn ▸ dvd_pow_self 2 (ne_of_gt hn0)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥E2P.SporB.j1S)) 2 hdvd
  refine ⟨((x : ↥E2P.SporB.j1S) : ↥J), (x : ↥E2P.SporB.j1S).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have := Subgroup.mem_center_iff.mp x.2 ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm

end Lattice

section Main

theorem exists_good_centralizer :
    ∃ C : Subgroup ↥J, E2P.SporB.j1S ≤ C ∧ Nat.card C = 120 ∧ GoodGam (innerU E2P.SporB.j1S) C := by
  obtain ⟨u, huS, hou, hcomm⟩ := exists_central_involution
  obtain ⟨h120, KJ, hKJle, hKJs, hKJ60⟩ := j1_cent_data u hou
  set C : Subgroup ↥J := Subgroup.centralizer ({u} : Set ↥J) with hC
  have hSC : E2P.SporB.j1S ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm s hs).symm
  have huC : u ∈ C := hSC huS
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hou
    exact absurd hou (by norm_num)
  have eK : ↥(KJ.subgroupOf C) ≃* ↥KJ := Subgroup.subgroupOfEquivOfLe hKJle
  haveI : IsSimpleGroup ↥(KJ.subgroupOf C) := eK.isSimpleGroup
  have hK60 : Nat.card ↥(KJ.subgroupOf C) = 60 := by rw [Nat.card_congr eK.toEquiv, hKJ60]
  have hlevi : ∃ ρ : ↥C →* Equiv.Perm (Fin 5),
      IsPGroup 2 ρ.ker ∧ alternatingGroup (Fin 5) ≤ ρ.range :=
    levi5_of_simple_index_two (u := (⟨u, huC⟩ : ↥C)) hK60 h120 (fun z =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp z.2).symm)
      (fun h => hu1 (congrArg Subtype.val h))
  exact ⟨C, hSC, h120, GoodGam.levi5 (inv_of_inner hSC) hlevi⟩

theorem sup_Y16 {C : Subgroup ↥J} (hSC : E2P.SporB.j1S ≤ C) (hC : Nat.card C = 120) :
    E2P.SporB.j1Y 16 ⊔ C = ⊤ := by
  have hS : E2P.SporB.j1S ≤ E2P.SporB.j1Y 16 ⊔ C := le_sup_of_le_left (E2P.SporB.j1_S_le_Y 16)
  rcases member_or_top hS with ⟨j, hj, hjeq⟩ | htop
  · exfalso
    have h1 : Nat.card (E2P.SporB.j1Y 16) ∣ Nat.card (E2P.SporB.j1Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_left)
    have h2 : Nat.card C ∣ Nat.card (E2P.SporB.j1Y j) :=
      Subgroup.card_dvd_of_le (hjeq ▸ le_sup_right)
    rw [card_Y16] at h1
    rw [hC] at h2
    rw [card_Y hj] at h1 h2
    have hd1 : 21 ∣ j1Idx j := by
      have : 168 = 21 * 2 ^ 3 := by norm_num
      rw [this] at h1
      exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h1
    have hd2 : 15 ∣ j1Idx j := by
      have : 120 = 15 * 2 ^ 3 := by norm_num
      rw [this] at h2
      exact Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
    have key : ∀ j < 17, 21 ∣ j1Idx j → 15 ∣ j1Idx j → False := by decide
    exact key j hj hd1 hd2
  · exact htop

theorem nParam_le_two_of_isJ1
    {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hJ1 : IsSporadic .J1 (ASInputs.FStar G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) : E1.nParam (⊤ : Subgroup G) ≤ ((2 : ℕ) : ℕ∞) := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨e₀⟩ := hJ1
  let e : ↥(CFSG.generalizedFitting G) ≃* ↥J := e₀.trans nativeEquiv
  have hnab : ∃ a b : ↥(CFSG.generalizedFitting G), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥(CFSG.generalizedFitting G) := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hFs
    rw [Nat.card_congr e.toEquiv, card_J] at hp
    exact absurd hp (by norm_num)
  have hC := centralizer_fStar_eq_bot hFs hnab
  obtain ⟨C, hSC, h120, hgoodC⟩ := exists_good_centralizer
  exact nParam_le_two_of_goodPair_inner (U := E2P.SporB.j1S) E2P.SporB.j1_sylow (sup_Y16 hSC h120)
    CFSG.Quasithin.E2P.SporB.j1_inner
    ⟨good_Y16, hgoodC⟩ hLn e hC hTs hFT

end Main

end CFSG.Quasithin.RonanE114.C5.J1

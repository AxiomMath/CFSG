module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6Prop87
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferData
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TransferMark
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnit63Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableB CFSG.StandardType.TableBExc.E6Three
open CFSG.StandardType.E6ThreeModel CFSG.StandardType.S2MathAs51642Interfaces

theorem marking_of_central_image {X R : Type} [Group X] [Group R]
    {ψ : X →* R} (hker : ψ.ker ≤ Subgroup.center X)
    {A : Subgroup (MulAut X)} (β : A →* MulAut R)
    (hβ : ∀ a : A, ∀ x, β a (ψ x) = ψ ((a : MulAut X) x))
    {J : Subgroup X} (hJ : ⁅J, J⁆ = J)
    (hN : ∀ a ∈ β.range, ∀ j ∈ J.map ψ, a j ∈ J.map ψ)
    (hmark : LargeEvenMarking ↥(J.map ψ)
      (fun _ _ _ I _ θ => GGAutsInduceOn β.range (J.map ψ) θ I)) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking ↥J (fun _ _ _ I _ θ => GGAutsInduceOn A J θ I) := by
  have hN' : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha
    exact (SCFourCover.mapsTo_map_iff hker (hβ ⟨a, ha⟩) hJ).2
      (hN _ ⟨⟨a, ha⟩, rfl⟩)
  refine ⟨hN', ?_⟩
  have hperf : commutator ↥J = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hJ)
  refine SCFourCover.largeEvenMarking_centerQuot
    (SCFourCover.centerQuotMap hker hJ) hperf ?_ hmark
  intro lab R' _ I F θ hind a ha
  obtain ⟨φ, hφ, hφa⟩ := hind (β ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
  refine ⟨φ, hφ, ?_⟩
  have hlift := (SCFourCover.largeEvenInduces_map_iff hker (hβ ⟨a, ha⟩) hJ
    (hN' a ha) θ φ).2 (by
      intro j j' hj
      exact hφa j j' hj.symm)
  intro j j' hj
  exact hlift j j' hj.symm

theorem componentMarking_of_quotient_components
    {X R : Type} [Group X] [Finite X] [Group R] {p r : ℕ}
    (hperf : commutator X = ⊤) (θ : X ⧸ Subgroup.center X ≃* R)
    {A : Subgroup (MulAut X)} (hA : IsElemAbelian p A)
    (hcard : p ^ r ≤ Nat.card A) {I : Set (MulAut R)}
    (hI : ∀ a ∈ A, ggInducedAut θ a ∈ I)
    {u : MulAut X} (hu : u ∈ A) (hu1 : u ≠ 1) {J : Subgroup X}
    (hJ : IsComponentOf J (ggAutFixedSubgroup u))
    (supplier : ∀ {E : Subgroup (MulAut R)}, IsElemAbelian p E →
      (∀ a ∈ E, a ∈ I) → p ^ r ≤ Nat.card E →
      ∀ {v : MulAut R}, v ∈ E → v ≠ 1 → ∀ {C : Subgroup R},
      IsComponentOf C (ggAutFixedSubgroup v) →
      (∀ a ∈ E, ∀ j ∈ C, a j ∈ C) ∧
        LargeEvenMarking C (fun _ _ _ I' _ θC => GGAutsInduceOn E C θC I')) :
    (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧
      LargeEvenMarking J (fun _ _ _ I' _ θJ => GGAutsInduceOn A J θJ I') := by
  classical
  let ψ : X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp
      (θ.injective (hx.trans (map_one θ).symm))
  let β : A →* MulAut R := (ggInducedAut θ).comp A.subtype
  have hβinj : Function.Injective β :=
    (ggInducedAut_injective_of_perfect hperf θ).comp Subtype.val_injective
  have hβ : ∀ a : A, ∀ x : X, β a (ψ x) =
      ψ ((a : MulAut X) x) := by
    intro a x
    exact ggInducedAut_apply θ (a : MulAut X) x
  have hB : IsElemAbelian p β.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact TableB.isElemAbelian_map hA (ggInducedAut θ)
  have hBI : ∀ a ∈ β.range, a ∈ I := by
    rintro _ ⟨a, rfl⟩
    exact hI a a.2
  have hBcard : p ^ r ≤ Nat.card β.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hperf θ)]
    exact hcard
  have hB1 : β ⟨u, hu⟩ ≠ 1 := by
    intro h
    have he : (⟨u, hu⟩ : A) = 1 := hβinj (h.trans (map_one β).symm)
    exact hu1 (congrArg Subtype.val he)
  have hcommJ : ⁅J, J⁆ = J := SCFourCover.commutator_eq_self_of_isComponentOf hJ
  have hJimage : IsComponentOf (J.map ψ)
      (ggAutFixedSubgroup (β ⟨u, hu⟩)) :=
    (S2MathAs51600.centralFixedComponentTransfer_holds ψ
      hψ hker u (β ⟨u, hu⟩)
      (fun x => (hβ ⟨u, hu⟩ x).symm) J hJ).1
  obtain ⟨hJN, hmark⟩ := supplier hB hBI hBcard ⟨⟨u, hu⟩, rfl⟩ hB1 hJimage
  exact marking_of_central_image hker β hβ hcommJ hJN hmark

theorem ggInnerDiagOn_stdSub_of_quotient_components
    {G : Type} [Group G] [Finite G] {p r : ℕ} (hp : p.Prime)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {I : Set (MulAut R)}
    (hI : ∀ (b : G) (hb : b ∈ Bs), ggBeta L θ hN ⟨b, hb⟩ ∈ I)
    (hcard : p ^ r ≤ Nat.card (ggGamma L hN).range)
    (supplier : ∀ {A : Subgroup (MulAut R)}, IsElemAbelian p A →
      (∀ a ∈ A, a ∈ I) → p ^ r ≤ Nat.card A →
      ∀ {u : MulAut R}, u ∈ A → u ≠ 1 → ∀ {C : Subgroup R},
      CFSG.Assembly.IsComponentOf C (ggAutFixedSubgroup u) →
      (∀ a ∈ A, ∀ j ∈ C, a j ∈ C) ∧
        LargeEvenMarking C (fun _ _ _ I' _ θC => GGAutsInduceOn A C θC I')) :
    GGInnerDiagOn Bs J := by
  classical
  have hperf := hcfg.data_L.2.2.2
  let A : Subgroup (MulAut ↥L) := (ggGamma L hN).range
  have hA : IsElemAbelian p A :=
    isElemAbelian_range
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hcfg.2.1.2.1 a.2 b.2))
      (fun a => Subtype.ext (hcfg.2.1.2.1.2 a a.2)) _
  have hAI : ∀ a ∈ A, ggInducedAut θ a ∈ I := by
    rintro _ ⟨b, rfl⟩
    exact hI b b.2
  obtain ⟨z, u, -, hzu, huord, -, hJL, hJopen⟩ := q1_fixed_component_data hcfg hN
  have hu : u ∈ A := ⟨z, hzu⟩
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huord
    exact hp.ne_one huord.symm
  have hJ : IsComponentOf (J.subgroupOf L) (ggAutFixedSubgroup u) :=
    Assembly.isComponentOf_iff_open.mpr hJopen
  obtain ⟨hnorm, hpart⟩ := componentMarking_of_quotient_components
    hperf θ hA hcard hAI hu hu1 hJ supplier
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub (fun a ha b hb =>
      TableB.IsElemAbelian.comm hcfg.2.1.2.1 ha hb) hcfg.2.1.1 hcfg.2.2.1 hN
  have hconc : Q1ComponentConclusion p ⟨.E6, 0, 1⟩ A (J.subgroupOf L)
      (fun _ _ _ => True) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, hnorm, h⟩) hpart
  have hfinal := q1_marking_of_component_conclusion hN hJL hBsJ hconc
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hfinal

theorem q1E6Three_of_adjointMarking
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (h3 : 3 ∣ Nat.card F - 1)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup .E6 F)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ (b : G) (hb : b ∈ Bs), ggBeta L θ hN ⟨b, hb⟩ ∈ (hatAut .E6 F).range) :
    GGInnerDiagOn Bs J := by
  have hperf := hcfg.data_L.2.2.2
  have hcard : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
    have hβ := (pow_le_card_range_ggBeta Nat.prime_three hcfg.1.2.2.2.2.2.2.1 hperf θ
      (hcfg.2.1.1.trans hN) (TableBExc.ggTorusLift_adjoint_E6_three h3)).trans
      (Subgroup.card_le_of_le (range_ggBeta_le θ hcfg.2.1.1 _ hN))
    have hmap : (ggGamma L hN).range.map (ggInducedAut θ) = (ggBeta L θ hN).range := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨c, hc⟩ := hb
        exact ⟨c, congrArg (ggInducedAut θ) hc⟩
      · rintro ⟨c, rfl⟩
        exact ⟨ggGamma L hN c, ⟨c, rfl⟩, rfl⟩
    rwa [← hmap, Subgroup.card_map_of_injective
      (ggInducedAut_injective_of_perfect hperf θ)] at hβ
  refine ggInnerDiagOn_stdSub_of_quotient_components Nat.prime_three hcfg θ hN hI hcard ?_
  intro A hA hAI h5 u hu hu1 C hC
  exact Q1E6ThreeModel.q1E6ThreeModel_holds h3 hA hAI h5 hu hu1 hC

theorem q1E6Three_holds : Q1E6Three := by
  intro G _ _ p B Bs x L D J hcfg hmark
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨R, _, I, F, _, _, θ, hsel, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ht, hp, h3⟩ := hsel
  subst p
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h3
  subst t
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  let e := TableBExc.recipeEquiv .E6 K
  have hI : ∀ (b : G) (hb : b ∈ Bs),
      ggBeta L (θK.trans e) hN ⟨b, hb⟩ ∈ (hatAut .E6 K).range := by
    intro b hb
    obtain ⟨φ, hφ, hind⟩ := hactors b⁻¹ (Bs.inv_mem hb)
    have heq : φ = ggLAut L θK ⟨b, hN hb⟩ := by
      ext r
      obtain ⟨q, rfl⟩ := θK.surjective r
      induction q using QuotientGroup.induction_on with
      | H z =>
        rw [ggLAut_apply]
        apply hind z (L.normalizerMonoidHom ⟨b, hN hb⟩ z)
        change b * (z : G) * b⁻¹ = (b⁻¹)⁻¹ * (z : G) * b⁻¹
        rw [inv_inv]
    change ggLAut L (θK.trans e) ⟨b, hN hb⟩ ∈ _
    have htrans := NbrLangTypeA.ggLAut_trans (K := L) θK e ⟨b, hN hb⟩
    rw [htrans]
    exact (recipeID_iff_hatAut _).1 (heq ▸ hφ)
  exact q1E6Three_of_adjointMarking (by rw [hK]; exact h3) hcfg (θK.trans e) hN hI

end CFSG.StandardType

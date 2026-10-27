module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEight
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveRoot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

structure SevenEightBarConfig {X : Type} [Group X] (S L : Subgroup X) : Prop where
  le : S ≤ L
  generated : (⨆ (g : X) (_ : conjSubgroup S g ≤ L), conjSubgroup S g) = L
  quot : HasQuotShape L (pCoreOf 2 L : Set X) (fun Y _ => IsSymGp Y 3)
  four_le : 4 ≤ Set.ncard {W : Subgroup X | ∃ x ∈ pCoreOf 2 L, W = conjSubgroup S x}

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem isGeneratedByOmega_omegaUnder {X : Type} [Group X] (φ : ↥(kSub V H E) →* X)
    (Lb : Subgroup X) : IsGeneratedByOmega V H E (omegaUnder V H E φ Lb) := by
  unfold IsGeneratedByOmega omegaWithin omegaUnder
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun U hU => hU.2
  · refine iSup₂_le fun U hU => le_iSup₂_of_le U ⟨hU.1, le_omegaUnder hU.1 hU.2⟩ le_rfl

theorem omegaUnder_le_barPre {X : Type} [Group X] (φ : ↥(kSub V H E) →* X) (Lb : Subgroup X) :
    omegaUnder V H E φ Lb ≤ barPre (kSub V H E) φ Lb := by
  unfold omegaUnder
  refine iSup₂_le fun U hU => ?_
  intro u hu
  refine mem_barPre.mpr ⟨le_kSub hU.1 hu, hU.2 (mem_barSub.mpr ⟨⟨u, le_kSub hU.1 hu⟩, hu, rfl⟩)⟩

theorem barSub_omegaUnder_eq (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Lb : Subgroup X} (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    barSub (kSub V H E) φ (omegaUnder V H E φ Lb) = Lb := by
  refine le_antisymm ?_ ?_
  · calc barSub (kSub V H E) φ (omegaUnder V H E φ Lb)
        ≤ barSub (kSub V H E) φ (barPre (kSub V H E) φ Lb) :=
          Subgroup.map_mono (Subgroup.subgroupOf_mono (kSub V H E) (omegaUnder_le_barPre φ Lb))
      _ = Lb := barSub_barPre hφ Lb
  · have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
    have key : (⨆ (g : X) (_ : conjSubgroup (barSub (kSub V H E) φ V) g ≤ Lb),
        conjSubgroup (barSub (kSub V H E) φ V) g) ≤
        barSub (kSub V H E) φ (omegaUnder V H E φ Lb) := by
      refine iSup₂_le fun g hg => ?_
      obtain ⟨k, rfl⟩ := hφ.surjective g
      have hVk : conjSubgroup V (k : G) ∈ omegaSet V H E :=
        conjSubgroup_mem_omegaSet h.le h.normal h.mem (hKH k.2)
      have hbar : barSub (kSub V H E) φ (conjSubgroup V (k : G)) ≤ Lb := by
        rwa [barSub_conjSubgroup φ V k]
      have hle : conjSubgroup V (k : G) ≤ omegaUnder V H E φ Lb :=
        le_omegaUnder hVk hbar
      rw [← barSub_conjSubgroup φ V k]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono (kSub V H E) hle)
    rwa [hc.generated] at key

theorem pCoreOf_eq_inf_barPre {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    (hφ : IsBarMap K (pCoreOf 2 K) φ) {L : Subgroup G} (hLK : L ≤ K) :
    pCoreOf 2 L = L ⊓ barPre K φ (pCoreOf 2 (barSub K φ L)) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  refine le_antisymm ?_ ?_
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) ?_
    have hPb_p : IsPGroup 2 (barSub K φ (pCoreOf 2 L)) :=
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).comap_of_injective K.subtype
        K.subtype_injective).map φ
    have hPb_le : barSub K φ (pCoreOf 2 L) ≤ pCoreOf 2 (barSub K φ L) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.map_mono (Subgroup.subgroupOf_mono K (CFSG.LieType.BorelTits.pCoreOf_le 2 L)))
        (barSub_le_normalizer_barSub φ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
        hPb_p
    intro x hx
    refine mem_barPre.mpr ⟨hLK ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx), ?_⟩
    exact hPb_le (mem_barSub.mpr ⟨⟨x, hLK ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx)⟩, hx, rfl⟩)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · refine (le_inf Subgroup.le_normalizer ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      exact le_normalizer_barPre hφ hLK
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (barSub K φ L))
    · exact (isPGroup_barPre hφ
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (barSub K φ L))).to_le inf_le_right

theorem hasQuotShape_omegaUnder (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Lb : Subgroup X} (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    HasQuotShape (omegaUnder V H E φ Lb) (pCoreOf 2 (omegaUnder V H E φ Lb) : Set G)
      (fun Y _ => IsSymGp Y 3) := by
  obtain ⟨Y, hYgrp, ψ, hψ_surj, hψ_ker, hY⟩ := hc.quot
  letI : Group Y := hYgrp
  have hLb : barSub (kSub V H E) φ (omegaUnder V H E φ Lb) = Lb := barSub_omegaUnder_eq h hφ hc
  have hcore : pCoreOf 2 (omegaUnder V H E φ Lb) =
      omegaUnder V H E φ Lb ⊓ barPre (kSub V H E) φ (pCoreOf 2 Lb) := by
    have h2 := pCoreOf_eq_inf_barPre hφ (omegaUnder_le_kSub φ Lb)
    rwa [hLb] at h2
  let θ : ↥(omegaUnder V H E φ Lb) →* ↥Lb :=
    (φ.comp (Subgroup.inclusion (omegaUnder_le_kSub φ Lb))).codRestrict Lb
      fun l => (mem_barPre.mp (omegaUnder_le_barPre φ Lb l.2)).2
  have hθ_val : ∀ l : ↥(omegaUnder V H E φ Lb),
      ((θ l : ↥Lb) : X) = φ ⟨l, omegaUnder_le_kSub φ Lb l.2⟩ := fun l => rfl
  have hθ_surj : Function.Surjective θ := by
    intro y
    have hy : (y : X) ∈ barSub (kSub V H E) φ (omegaUnder V H E φ Lb) := by
      rw [hLb]
      exact y.2
    obtain ⟨a, haL, haφ⟩ := mem_barSub.mp hy
    refine ⟨⟨a, haL⟩, Subtype.ext ?_⟩
    rw [hθ_val]
    exact haφ
  refine ⟨Y, hYgrp, ψ.comp θ, hψ_surj.comp hθ_surj, ?_, hY⟩
  intro l
  rw [MonoidHom.comp_apply, hψ_ker (θ l), SetLike.mem_coe, SetLike.mem_coe, hcore,
    Subgroup.mem_inf, hθ_val]
  constructor
  · intro hmem
    exact ⟨l.2, mem_barPre.mpr ⟨omegaUnder_le_kSub φ Lb l.2, hmem⟩⟩
  · intro hmem
    exact (mem_barPre.mp hmem.2).2

theorem four_le_ncard_omegaUnder (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Lb : Subgroup X} (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    4 ≤ Set.ncard {W : Subgroup G | ∃ g ∈ pCoreOf 2 (omegaUnder V H E φ Lb),
      W = conjSubgroup V g ⊔ pCoreOf 2 (kSub V H E)} := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hLb : barSub (kSub V H E) φ (omegaUnder V H E φ Lb) = Lb := barSub_omegaUnder_eq h hφ hc
  have hcore : pCoreOf 2 (omegaUnder V H E φ Lb) =
      omegaUnder V H E φ Lb ⊓ barPre (kSub V H E) φ (pCoreOf 2 Lb) := by
    have h2 := pCoreOf_eq_inf_barPre hφ (omegaUnder_le_kSub φ Lb)
    rwa [hLb] at h2
  have hbarJ : barSub (kSub V H E) φ (pCoreOf 2 (kSub V H E)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, hkJ, rfl⟩ := mem_barSub.mp hy
    rw [Subgroup.mem_bot]
    exact (hφ.ker_iff k).mpr hkJ
  have hsub : {W : Subgroup X | ∃ x ∈ pCoreOf 2 Lb,
      W = conjSubgroup (barSub (kSub V H E) φ V) x} ⊆
      barSub (kSub V H E) φ '' {W : Subgroup G | ∃ g ∈ pCoreOf 2 (omegaUnder V H E φ Lb),
        W = conjSubgroup V g ⊔ pCoreOf 2 (kSub V H E)} := by
    rintro W ⟨x, hx, rfl⟩
    have hxL : x ∈ barSub (kSub V H E) φ (omegaUnder V H E φ Lb) := by
      rw [hLb]
      exact CFSG.LieType.BorelTits.pCoreOf_le 2 Lb hx
    obtain ⟨k, hkL, rfl⟩ := mem_barSub.mp hxL
    have hkcore : (k : G) ∈ pCoreOf 2 (omegaUnder V H E φ Lb) := by
      rw [hcore]
      exact Subgroup.mem_inf.mpr ⟨hkL, mem_barPre.mpr ⟨k.2, hx⟩⟩
    refine ⟨conjSubgroup V (k : G) ⊔ pCoreOf 2 (kSub V H E), ⟨(k : G), hkcore, rfl⟩, ?_⟩
    have hVk : conjSubgroup V (k : G) ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet h.le h.normal h.mem (hKH k.2)
    rw [barSub_sup (le_kSub hVk) hJK φ, barSub_conjSubgroup φ V k, hbarJ, sup_bot_eq]
  exact le_trans hc.four_le (le_trans (Set.ncard_le_ncard hsub) Set.ncard_image_le)

theorem hyp78_omegaUnder (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Lb : Subgroup X} (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    Hyp78 V H E (pCoreOf 2 (kSub V H E)) (omegaUnder V H E φ Lb) :=
  ⟨h.toHyp73, h.oddCore, h.transitive, omegaUnder_le_kSub φ Lb,
    isGeneratedByOmega_omegaUnder φ Lb, le_omegaUnder h.mem hc.le,
    hasQuotShape_omegaUnder h hφ hc, four_le_ncard_omegaUnder h hφ hc⟩

section Core


theorem commutator_fusionOddCore_eq_bot_of_sevenEightBarConfig (h : Hyp711 V H E)
    {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {Lb : Subgroup X}
    (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    ⁅Lb, fusionOddCore X⁆ = ⊥ := by
  have h78 := hyp78_omegaUnder h hφ hc
  have hseven := seven_eight_barSub h78 hφ
  rwa [barSub_omegaUnder_eq h hφ hc] at hseven

theorem fusionOddCore_le_center_of_sevenEightBarConfig (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    {Lb : Subgroup X} (hc : SevenEightBarConfig (barSub (kSub V H E) φ V) Lb) :
    fusionOddCore X ≤ Subgroup.center X := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h8 := commutator_fusionOddCore_eq_bot_of_sevenEightBarConfig h hφ hc
  have hLC : Lb ≤ Subgroup.centralizer (fusionOddCore X : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h8
  have hVC : barSub (kSub V H E) φ V ≤ Subgroup.centralizer (fusionOddCore X : Set X) :=
    hc.le.trans hLC
  have hNC : Subgroup.normalClosure (barSub (kSub V H E) φ V : Set X) ≤
      Subgroup.centralizer (fusionOddCore X : Set X) :=
    Subgroup.normalClosure_le_normal hVC
  rw [normalClosure_barSub_eq_top h hφ] at hNC
  intro o ho
  rw [Subgroup.mem_center_iff]
  intro g
  exact (Subgroup.mem_centralizer_iff.mp (hNC (Subgroup.mem_top g)) o ho).symm

end Core

end CFSG.LocalAnalysis.WeakClosure81

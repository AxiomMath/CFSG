module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Vocab
public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem reducedAggregate_props [Finite G] (X : Subgroup G) :
    (∀ v ∈ reducedAggregate X, v ^ 2 = 1) ∧
      (∀ v ∈ reducedAggregate X, ∀ w ∈ reducedAggregate X, v * w = w * v) ∧
      pCoreOf 2 X ≤ Subgroup.centralizer (reducedAggregate X : Set G) := by
  obtain ⟨-, -, hle⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  have key : ∀ a ∈ primeReducedAggregate ↥X 2, a ∈ CFSG.pCore 2 ↥X ∧
      (∀ k ∈ CFSG.pCore 2 ↥X, k * a = a * k) ∧ a ^ 2 = 1 := fun a ha =>
    BlueprintB2.mem_centerTorsion_iff.1 (hle ha)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (key a ha).2.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val ((key b hb).2.1 a (key a ha).1)
  · rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have hc' : c ∈ CFSG.pCore 2 ↥X := by exact hc
    exact (congrArg Subtype.val ((key a ha).2.1 c hc')).symm

theorem autOn_sup {H K V : Subgroup G} (hH : H ≤ Subgroup.normalizer (V : Set G))
    (hK : K ≤ Subgroup.normalizer (V : Set G)) : autOn (H ⊔ K) V = autOn H V ⊔ autOn K V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hH hK

theorem Lem328.isPGroup_autOn {T V : Subgroup G} (hT : IsPGroup 2 ↥T) :
    IsPGroup 2 ↥(autOn T V) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hT

theorem autOn_le_normalizer {L T V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hT : T ≤ Subgroup.normalizer (V : Set G)) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    autOn T V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hTL

theorem isQuasisimple_autOn {L V : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hO2 : ∀ x ∈ CFSG.pCore 2 ↥L, (x : G) ∈ Subgroup.centralizer (V : Set G))
    (hnt : ∃ l ∈ L, l ∉ Subgroup.centralizer (V : Set G)) :
    CFSG.IsQuasisimple ↥(autOn L V) := by
  let ψ : ↥L →* ↥(autOn L V) := (A4.actionOn V L hL).codRestrict (autOn L V)
    (fun l => (A4.mem_autOn_iff hL).2 ⟨l, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hL).1 ha
    exact ⟨l, rfl⟩
  have hker : CFSG.pCore 2 ↥L ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Subtype.ext ((A4.actionOn_eq_one_iff hL x).2 (hO2 x hx))
  let φ : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L V) := QuotientGroup.lift _ ψ hker
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨l, rfl⟩ := hψ a
    exact ⟨QuotientGroup.mk l, rfl⟩
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hφ ?_
  obtain ⟨l, hl, hlc⟩ := hnt
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, fun h1 => hlc ?_⟩
  have h2 : ψ ⟨l, hl⟩ = 1 := h1
  exact (A4.actionOn_eq_one_iff hL ⟨l, hl⟩).1 (congrArg Subtype.val h2)

theorem sqtkGroup_autOn
    [Finite G] {H L V : Subgroup G} (hH : SQTKGroup ↥H) (hLH : L ≤ H)
    (hL : L ≤ Subgroup.normalizer (V : Set G)) (hq : CFSG.IsQuasisimple ↥(autOn L V)) :
    SQTKGroup ↥(autOn L V) := by
  let ψ : ↥(L.subgroupOf H) →* ↥(autOn L V) :=
    ((A4.actionOn V L hL).comp (Subgroup.subgroupOfEquivOfLe hLH).toMonoidHom).codRestrict
      (autOn L V) (fun x => (A4.mem_autOn_iff hL).2 ⟨_, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hL).1 ha
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLH).symm l, ?_⟩
    apply Subtype.ext
    simp [ψ]
  let e : ↥(L.subgroupOf H) ⧸ ψ.ker ≃* ↥(autOn L V) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hE : CFSG.layer (↥(L.subgroupOf H) ⧸ ψ.ker) = ⊤ :=
    B5.layer_eq_top_of_quasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq)
  have hsqt := CFSG.SectionRank.sqtk_semisimple_section_rank_of_catalog
    CFSG.SectionRank.oddKernelCentralization CFSG.SectionRank.catalogStepHyp hH.isSQTKCat
    (L.subgroupOf H) ψ.ker hE
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp
      (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hsqt),
    ((hH.2.subgroup (L.subgroupOf H)).quotient ψ.ker).of_mulEquiv e.symm⟩

theorem stmt3_2_8_of
    (hB42 : AsB42) (hI16 : AsI16Cover328) : Stmt3_2_8 := by
  intro G _ _ T L V₀ hfsu hLT hV₀T ⟨hcomm, hFF⟩
  refine ⟨hcomm, ?_⟩
  have hirrIn := hfsu.irrPlus
  rw [← hLT] at hirrIn
  obtain ⟨hVR, hV1, hLN, hVL, hlt, hirr', -⟩ := hirrIn
  obtain ⟨hsq, -, hO2R⟩ := reducedAggregate_props (L ⊔ T)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    rw [hLT]
    exact le_normalizer_conjClosure L T
  have hTN : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hV₀T]
    exact le_normalizer_conjClosure V₀ T
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hO2 : ∀ x ∈ CFSG.pCore 2 ↥L, (x : G) ∈ Subgroup.centralizer (V₀ : Set G) := by
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L :=
      ⟨x, by exact hx, rfl⟩
    exact Subgroup.centralizer_le (fun v hv => hVR hv) (hO2R (hQL h1))
  have hnt : ∃ l ∈ L, l ∉ Subgroup.centralizer (V₀ : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hV1
    rw [← hVL, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have := Subgroup.mem_centralizer_iff.1 (hcon l hl) v hv
    rw [Subgroup.mem_bot, commutatorElement_def, this]
    group
  have hq := isQuasisimple_autOn hLN hfsu.quasisimple hO2 hnt
  have hNV : pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) ≠ ⊥ := by
    have hV2 : IsPGroup 2 ↥V₀ := fun v => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, hsq v (hVR v.2)]; rfl)⟩
    have hle : V₀ ≤ pCoreOf 2 (Subgroup.normalizer (V₀ : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
    exact fun h => hV1 (le_bot_iff.1 (h ▸ hle))
  have hSQ := sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hNV
  have hsqtk := sqtkGroup_autOn hSQ hLN hLN hq
  obtain ⟨htop, hIrr⟩ := top_mem_irrPlus_autOn hLN ⟨le_rfl, hV1, hLN, hVL, hlt, hirr'⟩
  have hT2 : IsPGroup 2 ↥T := hfsu.sylow.1
  obtain ⟨S, hS, hTS⟩ := exists_isSylowTwoOf_ge (autOn_le_normalizer hLN hTN hTL)
    (Lem328.isPGroup_autOn hT2)
  have hsec : Sec328 (autOn L V₀) S :=
    { sq := fun v => Subtype.ext (by rw [Subgroup.coe_pow, hsq v (hVR v.2)]; rfl)
      quasi := hq
      sqtk := hsqtk
      irr := by rw [htop]; exact hIrr
      top := htop
      two := hS.2.1
      norm := hS.1 }
  have hc := hsec.concl hB42 hI16 hS hFF hTS
  unfold Concl328 at hc
  rw [fixV_autOn hLN, ← autOn_sup hLN hTN] at hc
  exact hc

end CFSG.Quasithin.H13

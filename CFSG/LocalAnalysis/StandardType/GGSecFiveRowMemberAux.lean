module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCasesLab
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrPRank
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggX_exists_overGamma_lift (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hInn : GGInnerDiagOn Bs X) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (Q : ∀ (L' : Type) [Group L'], Subgroup (MulAut L') → Prop)
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → Q L' A) :
    ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G), Q ↥X (ggGamma X hN).range ∧
      ∀ a ∈ ggTorusReflSet p (ggGamma X hN).range,
        ∃ c ∈ ggAutomizer X Bs, GGIsReflection p c ∧ GGOverGamma hN c a := by
  rcases hX with rfl | ⟨y, hnb⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hN, -⟩ := largeEvenMarking_exists_hasLabel hInn
    obtain ⟨R, _, θ, I, F, hBsI, ⟨r, hl, hfr⟩⟩ :=
      exists_datum_of_label hRig hInn hlab hhas hF hN
    obtain ⟨hp, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
    have hp2 : p ≠ 2 := hcfg.1.1.1.2.2.2.2.2.1.2.1
    have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
      hcfg.1.1.2.1.2.2.2
    obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg.1.1 hInn.1 θ hN hl
    have hTB := ggTorusTBGroup_of_marking hp hBs hSC hInn.1 θ hN hBsI hr h3
    refine ⟨hN, hfr X (ggQuotHom θ) (ggGamma X hN).range hTB, ?_⟩
    rintro _ ⟨n, hn, hW, rfl, hr'⟩
    obtain ⟨g, hgK, hg, hrefl, hov⟩ :=
      exists_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hN hW hn hr'
    exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgK hg, hrefl, hov⟩
  · exact ggNbr_exists_overGamma_lift hRig hcfg.1.1 hnb hInn hlab hhas Q hF

theorem ggX_exists_frame_pair (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hInn : GGInnerDiagOn Bs X) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (X ⧸ Subgroup.center X))
    (hF : LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A) :
    ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs, GGIsReflection p c₁ ∧
      GGIsReflection p c₂ ∧ 4 ∣ orderOf (c₁ * c₂) := by
  obtain ⟨hN, ⟨a₁, ha₁, a₂, ha₂, hord⟩, hlift⟩ := ggX_exists_overGamma_lift hRig hcfg
    (hX.imp_right fun h => h.1) hInn hlab hhas (fun _ _ A => GGTorusFrame p A) hF
  obtain ⟨c₁, hc₁, hr₁, hov₁⟩ := hlift a₁ ha₁
  obtain ⟨c₂, hc₂, hr₂, hov₂⟩ := hlift a₂ ha₂
  exact ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, hord.trans (hov₁.mul hov₂).orderOf_dvd⟩

theorem ggX_inndiag_pRank_ge_three {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    {S : ℕ → LargeEvenLabel → Prop} (hrow : GGInnerDiagOnLabel S p Bs X) :
    StandardType.LargeEvenMarking ↥X (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  rcases hX with rfl | hK
  · obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.1.1.tableB_facts
    obtain ⟨hBBs, -, -, -⟩ := hcfg.1.1.2.1
    have hS : LargeEvenSStar p B x X := hcfg.1.1.1.2.2.2.2.2.2.1
    have hxB : x ∈ B := hS.2.1
    have hxp : x ^ p = 1 := hcfg.1.1.1.2.2.2.2.2.2.1.1.1.2 x hxB
    have hxCL : x ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
    have hCeq : B ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · intro z hz
        have hz' : z ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := ⟨hBBs hz.1, hz.2⟩
        rwa [hcfg.1.1.bstar_inf_centralizer_L] at hz'
      · exact Subgroup.zpowers_le.mpr ⟨hxB, hxCL⟩
    have hBc : Nat.card ↥B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.1.1.2.2.2.2.2.1.2.2.2
    have hcardB : p ^ 4 ≤ Nat.card ↥B := by
      rw [hBc]
      exact Nat.pow_le_pow_right hp.pos h4
    refine largeEvenMarking_mono ?_ hrow
    intro lab R _ I _ θ hP
    obtain ⟨hSlab, hN, hind⟩ := hP
    have hBN : B ≤ Subgroup.normalizer (X : Set G) := hBBs.trans hN
    have hBsB : IsElemAbelian p B := isElemAbelian_of_le hBs hBBs
    refine ⟨hSlab, (ggBeta X θ hBN).range, ?_,
      isElemAbelian_range_ggBeta θ hBsB hBN, ?_⟩
    · rintro _ ⟨b, rfl⟩
      exact ggBeta_mem X θ hBN (fun b hb => hind b (hBBs hb)) b
    have hker : (ggBeta X θ hBN).ker.map B.subtype ≤ Subgroup.zpowers x := by
      rintro _ ⟨b, hb, rfl⟩
      have hb1 : ggLAut X θ ⟨b, hBN b.2⟩ = 1 :=
        (ggBeta_eq X θ hBN b).symm.trans (MonoidHom.mem_ker.mp hb)
      have hc := mem_centralizer_of_ggLAut_eq_one X θ hrow.1 hb1
      have hbC : (b : G) ∈ B ⊓ Subgroup.centralizer (X : Set G) := ⟨b.2, hc⟩
      rwa [hCeq] at hbC
    have hcard : Nat.card (ggBeta X θ hBN).ker ≤ p := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective]
      refine (Subgroup.card_le_of_le hker).trans ?_
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one hp.pos hxp
    refine Nat.le_of_mul_le_mul_right ?_ hp.pos
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥B := hcardB
      _ = Nat.card (ggBeta X θ hBN).range * Nat.card (ggBeta X θ hBN).ker :=
        (TableB.card_range_mul_card_ker _).symm
      _ ≤ Nat.card (ggBeta X θ hBN).range * p := Nat.mul_le_mul_left _ hcard
  · obtain ⟨y, hnb⟩ := hK.1
    exact ggNbr_inndiag_pRank_ge_three hcfg hK hrow

theorem ggX_row_absurd_of_frame (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hF : GGRowFrame S) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | hK
    · exact hcfg.1.2.2.1.1
    · obtain ⟨y, hnb⟩ := hK.1
      exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
    ggX_exists_frame_pair hRig hcfg hX hInn hΛ hhas
      (hF p hp hodd lab hΛ hS)
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with rfl | hK
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hK.2
  have hC₁ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₁) hr₁
  have hC₂ := ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₂) hr₂
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hC₁ hC₂ with h | h
  · have h42 : 4 ∣ 2 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega
  · have h43 : 4 ∣ 3 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega

theorem ggX_row_absurd_of_pRank {S : ℕ → LargeEvenLabel → Prop} (hP : GGRowPRankLeTwo S)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  exact not_largeEvenMarking_of_labelAll_card_lt (S := S p)
    (fun lab hlab hS => hP p hp hodd lab hlab hS) (ggX_inndiag_pRank_ge_three hcfg hX hrow)

theorem ggRowSplit_distrib {p : ℕ} {lab : LargeEvenLabel} (h : GGNSRowLab p lab)
    (hs : LargeEvenSplit p lab) :
    (ggRowP_SA p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_SD p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_SE6 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_SE7 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_SE8 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_ESU p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_EOmP p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_EOmM p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_ETwE6 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_EE7 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_EE8 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NB p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NF4 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NAP p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NTwAM p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NDOdd p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NTwD p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_NE6 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_Small p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_ZA8 p lab ∧ LargeEvenSplit p lab) ∨
    (ggRowP_ZE6 p lab ∧ LargeEvenSplit p lab) := by
  simp only [GGNSRowLab] at h ⊢
  tauto

theorem dvd_sub_or_add_of_split_triD4 {p : ℕ} {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) (ht : lab.tag = .triD4) : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  rcases hs with ⟨hu, h⟩ | ⟨-, -, h⟩ | ⟨hd, h⟩ | ⟨hn, hp3⟩
  · exact Or.inl h
  · exact Or.inr h
  · rcases hd with hd | hd
    · exact absurd hd (by simp)
    · exact Or.inl h
  · subst hn; subst hp3; norm_num

theorem dvd_sub_or_add_of_split_twF4 {p : ℕ} {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) (ht : lab.tag = .twF4) : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  rcases hs with ⟨hu, h⟩ | ⟨-, -, h⟩ | ⟨hd, h⟩ | ⟨hn, hp3⟩
  · exact absurd hu (by simp [LargeEvenUntwisted])
  · exact Or.inr h
  · rcases hd with hd | hd
    · exact absurd hd (by simp)
    · exact absurd hd (by simp)
  · subst hn; subst hp3; norm_num

theorem not_split_twA_dvd_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (ht : lab.tag = .twA) (hs : LargeEvenSplit p lab) (hd : p ∣ 2 ^ lab.n - 1) : False := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  have hno : ∀ m, p ∣ 2 ^ m - 1 → p ∣ 2 ^ m + 1 → False := fun m h1 h2 => by
    have hle := Nat.le_of_dvd (by norm_num) (ggDvd_two_of_dvd_pow_sub_add h1 h2)
    have hpge : 2 ≤ p := hp.two_le
    omega
  rcases hs with ⟨hu, h⟩ | ⟨-, -, h⟩ | ⟨hd', h⟩ | ⟨hn, hp3⟩
  · exact absurd hu (by simp [LargeEvenUntwisted])
  · exact hno _ hd h
  · rcases hd' with hd' | hd'
    · exact absurd hd' (by simp)
    · exact absurd hd' (by simp)
  · subst hn; subst hp3; norm_num at hd

theorem not_split_ZA8 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ZA8 p lab) :
    ¬ LargeEvenSplit p lab := by
  intro hs
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hr, hn, hp7⟩ := h
  subst ht; subst hr; subst hn; subst hp7
  norm_num [LargeEvenSplit, LargeEvenUntwisted] at hs

theorem not_split_ZE6 {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_ZE6 p lab) :
    ¬ LargeEvenSplit p lab := by
  intro hs
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨ht, hn, hp7⟩ := h
  subst ht; subst hn; subst hp7
  norm_num [LargeEvenSplit, LargeEvenUntwisted] at hs

theorem ntwam_split {p : ℕ} {lab : LargeEvenLabel}
    (h : ggRowP_NTwAM p lab ∧ LargeEvenSplit p lab) :
    ((lab.tag = .twA ∧ 3 ≤ lab.rank) ∧ p ∣ 2 ^ lab.n - 1 ∧ LargeEvenSplit p lab) ∨
      ((lab.tag = .twD ∧ lab.rank = 3) ∧ p ∣ 2 ^ lab.n - 1 ∧ LargeEvenSplit p lab) := by
  obtain ⟨⟨⟨ht, hr⟩ | ⟨ht, hr⟩, hd⟩, hs⟩ := h
  · exact Or.inl ⟨⟨ht, hr⟩, hd, hs⟩
  · exact Or.inr ⟨⟨ht, hr⟩, hd, hs⟩

theorem not_split_NsE6 {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .E6) (hs : LargeEvenSplit p lab) (hnot : ¬ p ∣ 2 ^ lab.n - 1)
    (hnot3 : ¬ (lab.n = 1 ∧ p = 3)) : False := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  rcases hs with ⟨hu, h⟩ | ⟨hu, -, h⟩ | ⟨hd, h⟩ | ⟨hn, hp3⟩
  · exact hnot h
  · exact hu (by simp [LargeEvenUntwisted])
  · rcases hd with hd | hd <;> simp at hd
  · exact hnot3 ⟨hn, hp3⟩

theorem ggX_row_absurd_of_cells (hRig : GGLabelRigidInput)
    {S Sf Sp : ℕ → LargeEvenLabel → Prop}
    (hcov : ∀ p lab, S p lab → Sf p lab ∨ Sp p lab) (hF : GGRowFrame Sf)
    (hP : GGRowPRankLeTwo Sp) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  have hor : GGInnerDiagOnLabel (fun p lab => Sf p lab ∨ Sp p lab) p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact ggX_row_absurd_of_frame hRig hF hcfg hpres hle3 hX h
  · exact ggX_row_absurd_of_pRank hP hcfg hX h

end CFSG.StandardType

end

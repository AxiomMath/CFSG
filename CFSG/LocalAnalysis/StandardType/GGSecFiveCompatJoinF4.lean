module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrderSixAD
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4Contracts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4SmallDefs
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH3
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGF4CommonA2
import CFSG.LocalAnalysis.StandardType.GGF4CoxeterSystem
import CFSG.LocalAnalysis.StandardType.GGAutomizerJoinInduced
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Internal

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

theorem GGSecFiveRouteCfg.bstar_le_ggG0_of_F4 (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hF4 : GGIsWeylMatrixF4 M) :
    Bs ≤ ggG0 p B x L D J := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, rfl⟩ := hF4
  have hW : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs 𝒦) :=
    GGWeylOfType.of_reindex ⟨e, hP.2⟩
  obtain ⟨par, root, depth, hpar, hdepth⟩ := SecFiveRootRefl.cartanTree_F₄
  refine hcfg.bstar_le_ggG0_of_cartan hp2 ggIntCartan_F₄
    (by intro i j; fin_cases i <;> fin_cases j <;> decide) par root depth hpar hdepth hW
    (card_le_pow_rank_of_isUnit_det ?_ hW fun b hb => hcfg.eq_one_of_forall_join_fix hTBF hWI b hb)
  rw [CartanMatrix.F₄_det, Int.cast_one]
  exact isUnit_one

end Internal

section Helpers

variable {G : Type} [Group G]

private theorem ggAutomizer_le_of_le {H H' Bs : Subgroup G} (h : H ≤ H') :
    ggAutomizer H Bs ≤ ggAutomizer H' Bs :=
  Subgroup.closure_mono fun _ ⟨g, hg, hgN, hφ⟩ => ⟨g, h hg, hgN, hφ⟩

private theorem mem_closure_of_map_eq {Bs : Subgroup G} {A X : Subgroup (MulAut ↥Bs)}
    {f : Fin 3 → ↥A} (hf : (Subgroup.closure (Set.range f)).map A.subtype = X) {u : ↥A}
    (hu : (u : MulAut ↥Bs) ∈ X) : u ∈ Subgroup.closure (Set.range f) := by
  rw [← hf] at hu
  obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu
  rwa [show w = u from Subtype.ext hwu] at hw

end Helpers

section Action

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {𝒦 : Finset (Subgroup G)}

@[expose] def GGF4JoinB3GuardedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs) →
          LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)

@[expose] def GGF4JoinA3ProperInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) →
          ∀ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs 𝒦

@[expose] def GGF4JoinMemberAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs) →
        ∀ (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          x ∈ ggG0 p B x L D J →
          LargeEvenMarking ↥L (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) →
            ∃ S : Subgroup G, MemberSelectedSL2At L S ∧ PresentedSelectedSL2At ψ S

theorem ggF4JoinMemberAt_of_known (hMem : KnownActualMemberSelectedInput) (t : StatedLieTag) :
    GGF4JoinMemberAt t :=
  fun G _ _ p B Bs x L D J _ hcfg _ _ _ _ _ _ _ _ _ _ n f ψ hpres _ hx hmark =>
    hMem G p B Bs x L D J hcfg.1.1 t n f ψ hpres L (Or.inl ⟨rfl, hx⟩) hmark

theorem ggSecFiveCompatJoinResNAt_F4_of_leaves (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hTypes : GGSecFiveF4OriginalTypesInput) (hSmall : GGSecFiveF4SmallLabelInput)
    (hExcl : GGSecFiveF4SmallExclusionInput) (hA3 : GGF4JoinA3ProperInput)
    (hB3 : GGF4JoinB3GuardedInput) (hMem : ∀ t, GGF4JoinMemberAt t) :
    GGSecFiveCompatJoinResNAt GGIsWeylMatrixF4 := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hP hF4 hSix t n f ψ hpres hJ
  obtain ⟨-, -, hxBs, hLx, -⟩ := hcfg.1.1.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hne : 𝒦.Nonempty := by
    by_contra h𝒦
    have hempty : 𝒦 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h𝒦
    have hA : ggAutomizerJoin L Bs 𝒦 = ggAutomizer L Bs := by
      rw [ggAutomizerJoin, hempty]
      simp
    have h1 := hcfg.eq_one_of_forall_join_fix hTBF hWI ⟨x, hxBs⟩ fun a ha =>
      ggRC_automizer_fixes_y hxBs hLx a (hA ▸ ha)
    exact hx1 (congrArg Subtype.val h1)
  rcases hTypes G p B Bs x L D J 𝒦 hcfg hReg hne ι M e hP hF4 with hA | hB
  · have hprop := hA3 G p B Bs x L D J 𝒦 hcfg hReg ι M e hP hF4 hA
    obtain ⟨hp3, hL, hK⟩ := hSmall G p B Bs x L D J 𝒦 hcfg hReg ι M e hP hF4 hA hprop
    exact (hExcl G p B Bs x L D J 𝒦 hcfg hReg ι M e hP hF4 hA hprop hp3 hL hK).elim
  · have hmark := hB3 G p B Bs x L D J 𝒦 hcfg hReg ι M e hP hF4 hB
    have hx : x ∈ ggG0 p B x L D J := hcfg.bstar_le_ggG0_of_F4 hTBF hWI hP hF4 hxBs
    obtain ⟨S, hS₁, hS₂⟩ :=
      hMem t G p B Bs x L D J 𝒦 hcfg hReg hrow hQ ι M e hP hF4 hSix hB n f ψ hpres hJ hx hmark
    exact ggCompat_of_selected_packages hpres (Or.inl rfl) hS₁ hS₂

@[expose] def GGF4JoinJReflA2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) →
          ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs,
            GGIsReflection p u ∧ GGIsReflection p v ∧ orderOf (u * v) = 3

theorem ggF4JoinA3ProperInput_of_jRefl (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hJ : GGF4JoinJReflA2Input) : GGF4JoinA3ProperInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hReg ι M e hPres hF hA3 K hK
  obtain ⟨hp, hBs, -, -, -⟩ := hR.1.1.tableB_facts
  obtain ⟨-, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  obtain ⟨cs, hcs⟩ := ggF4_exists_coxeterSystem hp hp2 hBs hR.1.2.2.2.1
    (ggAutomizerJoin_le_ggInduced_top L 𝒦) hPres hF
  have hLA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
  have hKA : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    ggAutomizer_le_ggAutomizerJoin (Or.inr hK)
  obtain ⟨eA, hPA⟩ := hA3
  obtain ⟨a, ha, hao, hac⟩ := ggF4_presentation_family hcs hLA
    (⟨CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 3 (by norm_num), hPA⟩ :
      GGCoxeterPres p (ggAutomizer L Bs) (CoxeterMatrix.A 3) eA)
  have ha01 : orderOf (a 0 * a 1) = 3 := by simpa [CoxeterMatrix.A] using hao 0 1
  have ha12 : orderOf (a 1 * a 2) = 3 := by simpa [CoxeterMatrix.A] using hao 1 2
  have ha02 : orderOf (a 0 * a 2) = 2 := by simpa [CoxeterMatrix.A] using hao 0 2
  obtain ⟨b, hb, hb01, hb12, hb02, hbc, -⟩ := ggF4_exists_family_of_typeA3B3 hcs hKA
    (hR.nbr_typeA3B3_of_F4 hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hFC hPres hF hK)
  obtain ⟨u, hu, v, hv, hur, hvr, huv⟩ :=
    hJ G p B Bs x L D J 𝒦 hR hReg ι M e hPres hF ⟨eA, hPA⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK
  have hJK : J ≤ K := ggNbrSubcomponentInput_of_lBalance hL hP G p B x L D J hcfg.1 hcfg.2.2 y K hN
  have huL := ggAutomizer_le_of_le hJL hu
  have hvL := ggAutomizer_le_of_le hJL hv
  have huK := ggAutomizer_le_of_le hJK hu
  have hvK := ggAutomizer_le_of_le hJK hv
  let u' : ↥(ggAutomizerJoin L Bs 𝒦) := ⟨u, hLA huL⟩
  let v' : ↥(ggAutomizerJoin L Bs 𝒦) := ⟨v, hLA hvL⟩
  have huv' : orderOf (u' * v') = 3 := by
    rw [← orderOf_injective (ggAutomizerJoin L Bs 𝒦).subtype
      (ggAutomizerJoin L Bs 𝒦).subtype_injective]
    exact huv
  intro hjoin
  exact F4Model.closure_ne_top_of_common_a2 cs ha hb ha01 ha12 ha02 hb01 hb12 hb02
    ((hcs u').2 hur) ((hcs v').2 hvr) huv' (mem_closure_of_map_eq (u := u') hac huL)
    (mem_closure_of_map_eq (u := v') hac hvL) (mem_closure_of_map_eq (u := u') hbc huK)
    (mem_closure_of_map_eq (u := v') hbc hvK)
    ((ggF4_closure_union_eq_top_iff _ _ a b hac hbc).2 hjoin)

end Action

end CFSG.StandardType

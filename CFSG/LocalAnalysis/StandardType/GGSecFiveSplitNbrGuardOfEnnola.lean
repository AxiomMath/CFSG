module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrPRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCases
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNTwAMCells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZReduce
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNMoreAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Cells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNF4Cells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZA8
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSE
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneHolds
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCasesLab
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNBCells
import CFSG.RankThree.PartOne.Q1327T.Item7UBasic

public section

namespace CFSG.StandardType

section E2part

section

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

theorem s2jn_ggRouteCfg_prime {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) :
    p.Prime ∧ p ≠ 2 := by
  obtain ⟨⟨⟨⟨_, _, _, _, _, hβ, _⟩, _⟩, _⟩, _⟩ := h
  obtain ⟨hp, hp2, _⟩ := hβ
  exact ⟨hp, hp2⟩

theorem s2jn_ggRouteCfg_isElemAbelian {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) :
    IsElemAbelian p Bs :=
  h.1.1.2.1.2.1

theorem s2jn_ggRouteCfg_noTransvection {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) :
    GGNoTransvection p Bs :=
  h.1.2.2.2.1

theorem s2jn_ggCoxRefl_of_cfg {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥A} (hpres : GGCoxeterPres p A M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r : MulAut ↥Bs} (hrA : r ∈ A) (hr : GGIsReflection p r) : r ∈ ggCoxRefl M e := by
  obtain ⟨hp, hodd⟩ := s2jn_ggRouteCfg_prime hcfg
  exact ggCoxRefl_of_isReflection hp hodd (s2jn_ggRouteCfg_isElemAbelian hcfg) hpres h3
    (ggNoTransvection_of_le_automizer (s2jn_ggRouteCfg_noTransvection hcfg) hA) hrA hr

end

section

open CFSG.Assembly CFSG.Open

theorem s2jn_ggNbr_inndiag_pRank_ge_three
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K)
    {S : ℕ → LargeEvenLabel → Prop} (hrow : GGInnerDiagOnLabel S p Bs K) :
    StandardType.LargeEvenMarking ↥K (fun lab R _ I _ _ => S p lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  have hy := hnb
  obtain ⟨⟨hBel, hBcard, -⟩, hyB, -, -, -, hSc⟩ := hy.1
  obtain ⟨hp, -, -, h4⟩ := hcfg.1.1.1.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  refine largeEvenMarking_mono ?_ hrow
  intro lab R _ I _ θ hP
  obtain ⟨hSlab, hN, hind⟩ := hP
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  refine ⟨hSlab, (ggBeta K θ hBN).range, ?_, isElemAbelian_range_ggBeta θ hBel hBN, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ggBeta_mem K θ hBN (fun b hb => hind b (hBBs hb)) b
  have hker : (ggBeta K θ hBN).ker.map B.subtype ≤ Subgroup.zpowers y := by
    rintro _ ⟨b, hb, rfl⟩
    have hb1 : ggLAut K θ ⟨b, hBN b.2⟩ = 1 :=
      (ggBeta_eq K θ hBN b).symm.trans (MonoidHom.mem_ker.mp hb)
    have hc := mem_centralizer_of_ggLAut_eq_one K θ hrow.1 hb1
    refine (hSc b).mp ⟨b.2, hBN b.2, ?_⟩
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ?_).trans_le bot_le
    exact Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hc)
  have hcard : Nat.card (ggBeta K θ hBN).ker ≤ p := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    refine (Subgroup.card_le_of_le hker).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos (hBel.2 y hyB)
  refine Nat.le_of_mul_le_mul_right ?_ hp.pos
  calc p ^ 3 * p = p ^ 4 := by ring
    _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
    _ = Nat.card ↥B := hBcard.symm
    _ = Nat.card (ggBeta K θ hBN).range * Nat.card (ggBeta K θ hBN).ker :=
      (TableB.card_range_mul_card_ker _).symm
    _ ≤ Nat.card (ggBeta K θ hBN).range * p := Nat.mul_le_mul_left _ hcard

end

section

open CFSG.Assembly

theorem s2jn_ggNbr_rowCases
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G}
    {y : G} (hnb : GGNbr p B x D J y K) : GGInnerDiagOnLabel GGNSRowLab p Bs K := by
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hcfg.1.1 hnb hInnK
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hInnK hlab hhas
  refine largeEvenMarking_mono (fun lab' _ _ _ _ _ hP' => ⟨?_, hP'.2⟩) hmark
  rw [hP'.1]
  exact ggNSRowLab_of_halfSplit hlab hHSlab

theorem s2jn_ggRow_absurd_of_frame
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hF : GGRowFrame S) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := s2jn_ggRouteCfg_prime hcfg
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩ :=
    ggNbr_exists_frame_pair hRig hcfg.1.1 hnb hInnK hΛ hhas (hF p hp hodd lab hΛ hS)
  have hC₁ := s2jn_ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₁) hr₁
  have hC₂ := s2jn_ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc₂) hr₂
  rcases ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hC₁ hC₂ with h | h
  · have h42 : 4 ∣ 2 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega
  · have h43 : 4 ∣ 3 := h4.trans (orderOf_dvd_of_pow_eq_one h)
    omega

theorem s2jn_ggRow_absurd_of_pRank
    {S : ℕ → LargeEvenLabel → Prop} (hP : GGRowPRankLeTwo S)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G}
    {y : G} (hnb : GGNbr p B x D J y K) (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := s2jn_ggRouteCfg_prime hcfg
  exact not_largeEvenMarking_of_labelAll_card_lt (S := S p)
    (fun lab hlab hS => hP p hp hodd lab hlab hS) (s2jn_ggNbr_inndiag_pRank_ge_three hcfg hnb hrow)

theorem s2jn_ggRow_absurd_of_cells
    (hRig : GGLabelRigidInput) {S Sf Sp : ℕ → LargeEvenLabel → Prop}
    (hcov : ∀ p lab, S p lab → Sf p lab ∨ Sp p lab) (hF : GGRowFrame Sf)
    (hP : GGRowPRankLeTwo Sp) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  have hor : GGInnerDiagOnLabel (fun p lab => Sf p lab ∨ Sp p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact s2jn_ggRow_absurd_of_frame hRig hF hcfg hpres hle3 hnb hle h
  · exact s2jn_ggRow_absurd_of_pRank hP hcfg hnb h

theorem s2jn_ggRow_absurd_of_clauseFive
    {S : ℕ → LargeEvenLabel → Prop}
    (h3 : ∀ p lab, S p lab → p ≠ 3 ∨ ∀ (X : Type) [Group X], MarkedModel lab X →
      ∀ lab' : LargeEvenLabel, markChar lab' ≠ 2 → ¬ MarkedModel lab' X)
    (hout : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I))
    (hdet : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      S p lab → ∀ (X : Type) [Group X], MarkedModel lab X → ∀ lab' : LargeEvenLabel,
        LargeEvenInLambda2 lab' → markChar lab' = 2 → MarkedModel lab' X →
          ∀ c, ¬ LargeEvenHalfSplit p lab' c)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G}
    {y : G} (hnb : GGNbr p B x D J y K) (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := s2jn_ggRouteCfg_prime hcfg
  have hc := hcfg.1.1
  have h5 := (hc.1.2.2.2.2.2.2.2.2.2.1 y K ⟨hnb.1, D, J, hc.2.2, hnb.2⟩).2
  have hxB : x ∈ B := hc.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hc.1.2.2.2.2.2.2.1.1.1.2 x hxB
  have hxBs : x ∈ Bs := hc.2.1.1 hxB
  obtain ⟨hKp, lab, hlab, hraw⟩ := largeEvenMarking_markedModel hrow
  have hSl : S p lab := by
    obtain ⟨_, _, _, _, -, -, _, ⟨hS, -⟩, -⟩ := largeEvenRawDatum_exists hraw
    exact hS
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, ⟨-, hN, hind⟩, hMM⟩, hO⟩ :=
    largeEvenRawDatum_exists (hout p lab hp hp2 hlab hSl _ hraw)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  have hxI : ggLAut K θ ⟨x, hxK⟩ ∈ I := ggLAut_mem_of_induces K θ hN hind hxBs
  have hφp : ggLAut K θ ⟨x, hxK⟩ ^ p = 1 := by
    have e : (⟨x, hxK⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [← map_pow, e, map_one]
  obtain ⟨r, hr⟩ := hO hs hna _ hxI hφp
  obtain ⟨k, hk, hkx⟩ := NbrInnerMore.exists_conj_of_ggLAut_eq_conj hKp θ hxK hr.symm
  have hMK : MarkedModel lab (K ⧸ Subgroup.center K) := MarkedModel.of_mulEquiv θ.symm hMM
  rcases h3 p lab hSl with hp3 | hX3
  · exact ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 ⟨k, hk, hkx⟩
      (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
      (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5
  · exact NbrInnerMore.not_ggNbrClauseFiveMarking_of_inner' ⟨k, hk, hkx⟩
      (fun lab' hlab' hc' hM' => hdet p lab hp hp2 hlab hSl _ hMK lab' hlab' hc' hM' _)
      (fun lab' hc' hM' => hX3 _ hMK lab' hc' hM')
      (fun lab' hlab' _ _ => ggRawInnFieldInput_holds p hp hp2 lab' hlab') h5

theorem s2jn_ggRowZ_absurd_of_detElt
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hF : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      S p lab → GGDetAt p lab) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K)
    (hrow : GGInnerDiagOnLabel S p Bs K) : False := by
  obtain ⟨hp, hodd⟩ := s2jn_ggRouteCfg_prime hcfg
  have hInnK : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  obtain ⟨c, hc, hP, hcomm, hexp, hdet⟩ :=
    ggNbr_exists_detElt hRig hcfg.1.1 hnb hInnK hΛ hhas (hF p hp hodd lab hΛ hS)
  exact hdet (ggDet_sq_eq_one_of_reflGen hP hcomm hexp (hcfg.2.1 y K hnb) hc)

theorem s2jn_eq_of_ggLabelIso_triD4_twF4
    {lab lab' : LargeEvenLabel}
    (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (h : GGLabelIso lab lab') : lab' = lab := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  unfold GGLabelIso at h
  rcases ht with rfl | rfl <;> rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem s2jn_dvd_sub_or_add_of_halfSplit
    {p : ℕ} (hp : p.Prime) {lab lab' : LargeEvenLabel}
    {c : Prop} (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) (hiso : GGLabelIso lab lab')
    (hlab' : LargeEvenInLambda2 lab') (h : LargeEvenHalfSplit p lab' c) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  rw [s2jn_eq_of_ggLabelIso_triD4_twF4 ht hiso] at hlab' h
  rcases largeEvenHalfSplit_dvd hlab' h with h | ⟨-, h | h⟩
  · rw [pow_two, mul_self_tsub_one] at h
    exact (hp.dvd_mul.mp h).symm
  all_goals (subst h; simp at ht)

theorem s2jn_ggRowSmall_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K)
    (hrow : GGInnerDiagOnLabel ggRowP_Small p Bs K) : False := by
  obtain ⟨hp, hp2, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  obtain ⟨lab', hlab', hhas', -, -, -, -, -, hHS⟩ := largeEvenMarking_exists_hasLabel
    (ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds (ggRawInndiagIsoInput_of_rest
      (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)) hcfg.1.1 hnb
      (hcfg.1.2.2.1.2 y K hnb))
  obtain ⟨hX, lab, hlab, hraw⟩ := s2jn_ggNbr_inndiag_pRank_ge_three hcfg hnb hrow
  have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  have hiso := ggLabelRigidInput_holds lab lab' _ hlab hlab' hhas hhas'
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists hraw
  have key : ∀ T : LargeEvenLabel → Prop, T lab → StandardType.LargeEvenMarking ↥K
      (fun lab R _ I _ _ => T lab ∧ ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) := fun T hT =>
    ⟨hX, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _, hE⟩ =>
      ⟨hs, hna, θ, hT, hE⟩) hraw⟩
  obtain ⟨t, r, n⟩ := lab
  dsimp only [ggRowP_Small] at hS
  rcases hS with ⟨rfl, hr⟩ | hBC | rfl | rfl | rfl | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | rfl | rfl | rfl | rfl
  · have h1 : 1 ≤ r := hlab.2.1
    rcases (by omega : r = 1 ∨ r = 2) with hr | hr
    · exact ggInndiag_pRank_le_two_A1 hp hp2 (key _ ⟨rfl, hr⟩)
    · exact ggInndiag_pRank_le_two_A2 hp hp2 (key _ ⟨rfl, hr⟩)
  · exact ggInndiag_pRank_le_two_B2 hp hp2 (key _ hBC)
  · exact ggInndiag_pRank_le_two_B2der hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_G2 hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_G2der hp hp2 (key _ rfl)
  · have h2 : 2 ≤ r := hlab.2.1
    exact ggInndiag_pRank_le_two_twA2 hp hp2 (key _ ⟨rfl, (by omega : r = 2)⟩)
  · exact ggInndiag_pRank_le_two_twD2 hp hp2 (key _ ⟨rfl, hr⟩)
  · exact ggInndiag_pRank_le_two_triD4 hp
      (key _ ⟨rfl, s2jn_dvd_sub_or_add_of_halfSplit hp (.inl rfl) hiso hlab' hHS⟩)
  · exact ggInndiag_pRank_le_two_twB2 hp hp2 (key _ rfl)
  · exact ggInndiag_pRank_le_two_twF4 hp hp2
      (key _ ⟨rfl, s2jn_dvd_sub_or_add_of_halfSplit hp (.inr rfl) hiso hlab' hHS⟩)
  · exact ggInndiag_pRank_le_two_twF4der hp hp2 (key _ rfl)

end

end E2part

section E3part

section

open CFSG.Assembly

theorem s2jn_ggRowNAP_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NAP p Bs K) : False := by
  refine s2jn_ggRow_absurd_of_cells ggLabelRigidInput_holds
    (Sf := fun p lab => lab.tag = .A ∧ 5 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ?_
    (fun p hp hp2 lab hlab h => ggNbrFrameInputOne_holds p hp hp2 lab hlab (Or.inr (Or.inl h)))
    ggRowPRankLeTwo_smallPlus hcfg hpres hle3 hnb hle hrow
  rintro p lab ⟨⟨ht, hr⟩ | ⟨ht, hr⟩, hd⟩
  · by_cases h5 : 5 ≤ lab.rank
    · exact Or.inl ⟨ht, h5, hd⟩
    · exact Or.inr ⟨Or.inl ⟨ht, by omega⟩, hd⟩
  · exact Or.inr ⟨Or.inr ⟨ht, hr⟩, hd⟩

theorem s2jn_ggRowNTwD_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NTwD p Bs K) : False := by
  refine s2jn_ggRow_absurd_of_frame ggLabelRigidInput_holds ?_ hcfg hpres hle3 hnb hle hrow
  rintro p hp hp2 lab hlab ⟨ht, hr, ⟨he, hd⟩ | hd⟩
  · exact largeEvenLabelAll_frame_omegaMinusNs hp hlab ⟨ht, hr, he, hd⟩
  · exact largeEvenLabelAll_frame_omegaMinus hp hp2 hlab ⟨ht, hr, hd⟩

theorem s2jn_ggRowNDOdd_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NDOdd p Bs K) : False :=
  s2jn_ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun _ hp _ _ hlab h => largeEvenLabelAll_frame_omegaPlusNs hp hlab h) hcfg hpres hle3 hnb hle hrow

theorem s2jn_ggRowNB_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NB p Bs K) : False :=
  s2jn_ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun _ hp _ _ hlab h => h.2.2.elim
      (fun hd => largeEvenLabelAll_frame_symplectic hp hlab ⟨h.1, hd⟩)
      (fun hd => largeEvenLabelAll_frame_symplecticNs hp hlab ⟨h.1, hd⟩))
    hcfg hpres hle3 hnb hle hrow

theorem s2jn_ggRowNTwAM_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NTwAM p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := s2jn_ggRouteCfg_prime hcfg
  have hcov : ∀ lab, ggRowP_NTwAM p lab →
      ((lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) ∨
        (((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
          p ∣ 2 ^ lab.n - 1)) ∨ GGNbrNsUnitLabel p lab := by
    rintro lab ⟨⟨ht, hl⟩ | ⟨ht, hl⟩, hd⟩
    · rcases (by omega : lab.rank = 3 ∨ lab.rank = 4 ∨ lab.rank = 5 ∨ 6 ≤ lab.rank) with
        h | h | h | h
      · exact Or.inl (Or.inr ⟨Or.inl ⟨ht, Or.inl h⟩, hd⟩)
      · exact Or.inl (Or.inr ⟨Or.inl ⟨ht, Or.inr h⟩, hd⟩)
      · exact Or.inl (Or.inl ⟨ht, h, hd⟩)
      · exact Or.inr ⟨ht, by omega, not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hd,
          fun h5 => by omega⟩
    · exact Or.inl (Or.inr ⟨Or.inr ⟨ht, hl⟩, hd⟩)
  have hor : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) ∨
        (((lab.tag = .twA ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧
          p ∣ 2 ^ lab.n - 1)) ∨ GGNbrNsUnitLabel p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · exact s2jn_ggRow_absurd_of_cells ggLabelRigidInput_holds
      (Sf := fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) (fun _ _ h => h)
      (fun p hp hp2 lab hlab h => ggNbrFrameInputOne_holds p hp hp2 lab hlab (Or.inr (Or.inr h)))
      ggRowPRankLeTwo_smallMinus hcfg hpres hle3 hnb hle h
  · exact s2jn_ggRow_absurd_of_clauseFive
      (fun _ _ h => Or.inr fun _ _ hX _ hc =>
        NbrInnerMore.not_markedModel_char_ne_two_unit h.1 h.2.1 hX hc)
      (fun _ _ hp _ hlab h =>
        (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab h.1 h.2.2.1).mono
          fun _ _ _ _ h _ _ => h)
      (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
        NbrInnerMore.not_halfSplit_of_markedModel_unit h hX hc' hX' c)
      hcfg hnb h

theorem s2jn_ggRowNE6_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel ggRowP_NE6 p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := s2jn_ggRouteCfg_prime hcfg
  have hcov : ∀ lab, ggRowP_NE6 p lab →
      ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGNbrNsE6Label p lab := by
    rintro lab (⟨ht, hd⟩ | h)
    · by_cases h13 : lab.n = 1 ∧ p = 3
      · exact Or.inl (Or.inl ⟨ht, h13⟩)
      · refine Or.inr ⟨ht, fun h1 => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 h1 hd, h13,
          fun h17 => ?_⟩
        rw [h17.1, h17.2] at hd
        norm_num at hd
    · exact Or.inl (Or.inr h)
  have hor : GGInnerDiagOnLabel (fun p lab =>
      ((lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) ∨
        GGNbrNsE6Label p lab) p Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hQ => ⟨hcov _ hQ.1, hQ.2⟩) hrow
  rcases hor.elim_or with h | h
  · refine s2jn_ggRow_absurd_of_frame ggLabelRigidInput_holds (fun q hq hq2 lab hlab h => ?_)
      hcfg hpres hle3 hnb hle h
    rcases h with ⟨ht, hn, rfl⟩ | h
    · exact largeEvenLabelAll_frame_E6Two ⟨ht, hn⟩
    · exact largeEvenLabelAll_frame_twE6Dvd hq hq2 hlab h
  · exact s2jn_ggRow_absurd_of_clauseFive
      (fun _ _ h => Or.inr fun _ _ hX _ hc => NbrInnerMore.not_markedModel_char_ne_two_E6 h.1 hX hc)
      (fun _ _ hp _ _ h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E6 hp h.1 h.2.1)
      (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
        NbrInnerMore.not_halfSplit_of_markedModel_E6 hlab h hX hlab' hc' hX' c)
      hcfg hnb h

theorem s2jn_ggRowNF4Cells_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hle : ggAutomizer K Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_NF4 p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))
      p Bs K) : False :=
  s2jn_ggRow_absurd_of_frame ggLabelRigidInput_holds
    (fun q hp hp2 _ _ h => h.1.2.elim
      (fun hd => largeEvenLabelAll_frame_F4Split hp hp2 ⟨h.1.1, hd⟩)
      (fun hd => largeEvenLabelAll_frame_F4Plus hp (by
        have h4 : q ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        have h3 : q ≠ 3 := fun h3 => h.2 ⟨h3, hd⟩
        have := hp.two_le
        omega) ⟨h.1.1, hd⟩))
    hcfg hpres hle3 hnb hle hrow

end

section

open CFSG.Assembly TableB

theorem s2jn_ggRowZA8_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G}
    {y : G} (hnb : GGNbr p B x D J y K) (hrow : GGInnerDiagOnLabel ggRowP_ZA8 p Bs K) : False := by
  refine s2jn_ggRowZ_absurd_of_detElt ggLabelRigidInput_holds (S := ggRowP_ZA8) ?_ hcfg hnb hrow
  intro p' _ _ lab _ h
  have hp7 : p' = 7 := h.2.2.2
  subst hp7
  rw [ggRowP_ZA8_eq_label lab h]
  exact ggDetAt_A8

end

section

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration TableB

theorem s2jn_ggRowZE6_absurd
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) {K : Subgroup G}
    {y : G} (hnb : GGNbr p B x D J y K) (hrow : GGInnerDiagOnLabel ggRowP_ZE6 p Bs K) : False := by
  refine s2jn_ggRowZ_absurd_of_detElt ggLabelRigidInput_holds (S := ggRowP_ZE6) ?_ hcfg hnb hrow
  intro p' _ _ lab _ h
  obtain ⟨ht, hn, rfl⟩ := h
  exact ggDetAt_E6_two_seven ⟨ht, hn⟩

end

end E3part

section E5part

open CFSG.Assembly
open scoped MatrixGroups

theorem s2jn_mono'
    {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs K : Subgroup G} (hST : ∀ lab, S p lab → T p lab) (h : GGInnerDiagOnLabel S p Bs K) :
    GGInnerDiagOnLabel T p Bs K :=
  largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hST lab hP.1, hP.2⟩) h

theorem s2jn_toMarking
    {G : Type} [Group G] {S : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs K : Subgroup G} (h : GGInnerDiagOnLabel S p Bs K) :
    LargeEvenMarking ↥K (fun lab _ _ _ _ _ => S p lab) :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h

theorem s2jn_ggRowEnnola_absurd
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBr : GGSplitLieLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hL : GGSplitLie p L)
    {K : Subgroup G} {y : G} (hnb : GGNbr p B x D J y K) (hrow : GGInnerDiagOnLabel ggRowP_Ennola p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := s2jn_ggRouteCfg_prime hcfg
  have hInnL : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  obtain ⟨labL, hΛL, hhasL, hpL⟩ := hBr G p L hp hp2 hL
  have hLlab : GGInnerDiagOnLabel (fun p lab => p ∣ 2 ^ lab.n - 1) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hpL, hP⟩)
      (ggInnerDiagOn_relabel hRig hInnL hΛL hhasL)
  obtain ⟨lab, labJ, -, hS, -, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg.1.1 hLlab hnb
  obtain ⟨labJ', hΛJ', hhasJ', hJ1, hJ2⟩ :=
    ggNbr_label_J_ennola hKn hLB hP hcfg.1.1 hrow hnb labJ hΛJ hhasJ
  exact ggLabelIso_ennola_absurd hp hp2 (hRig _ _ _ hΛJ' hΛJ hhasJ' hhasJ) hdvd hS hJ1 hJ2


theorem s2jn_ggSecFiveSplitNbrGuardInput'
    (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : GGSecFiveSplitNbrGuardInput' := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hTCJ : GGTCJKnown := TCJ.ggTCJKnown_holds
  have hBr : GGSplitLieLabelInput := fun G _ _ p L hp hp2 hL => ggSplitLie_label hp hp2 hL
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL hguard y K hnb hle
  obtain ⟨ι, M, e, hpres, hle3⟩ := hguard
  have hp : p.Prime := (s2jn_ggRouteCfg_prime hcfg).1
  have hEn : ∀ {S : ℕ → LargeEvenLabel → Prop}, (∀ lab, S p lab → ggRowP_Ennola p lab) →
      GGInnerDiagOnLabel S p Bs K → False := fun hST h =>
    s2jn_ggRowEnnola_absurd hRig hTCJ hKn hLB hP hBr hcfg hL hnb (s2jn_mono' hST h)
  have h0 := s2jn_ggNbr_rowCases hcfg hnb
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SA) h0 with h | h
  · exact ggSplitLie_of_rowSA hp (s2jn_toMarking h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SD) h with h | h
  · exact ggSplitLie_of_rowSD hp (s2jn_toMarking h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE6) h with h | h
  · exact ggSplitLie_of_rowSE6 hp (s2jn_toMarking h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE7) h with h | h
  · exact ggSplitLie_of_rowSE7 hp (s2jn_toMarking h)
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE8) h with h | h
  · exact ggSplitLie_of_rowSE8 hp (s2jn_toMarking h)
  exfalso
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ESU) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inl h)) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmP) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inl h))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmM) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inl h)))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ETwE6) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE8) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NB) h with h | h
  · exact s2jn_ggRowNB_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NF4) h with h | h
  · have h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_NF4 p lab ∧ (p = 3 ∧ p ∣ 2 ^ lab.n + 1)) ∨
        (ggRowP_NF4 p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))) p Bs K :=
      s2jn_mono' (fun lab hl => (em (p = 3 ∧ p ∣ 2 ^ lab.n + 1)).imp (fun h3 => ⟨hl, h3⟩)
        (fun h3 => ⟨hl, h3⟩)) h
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · exact hEn (fun _ h => Or.inr h) h
    · exact s2jn_ggRowNF4Cells_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NAP) h with h | h
  · exact s2jn_ggRowNAP_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NTwAM) h with h | h
  · exact s2jn_ggRowNTwAM_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NDOdd) h with h | h
  · exact s2jn_ggRowNDOdd_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NTwD) h with h | h
  · exact s2jn_ggRowNTwD_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NE6) h with h | h
  · exact s2jn_ggRowNE6_absurd hcfg hpres hle3 hnb hle h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_Small) h with h | h
  · exact s2jn_ggRowSmall_absurd hcfg hnb h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ZA8) h with h | h
  · exact s2jn_ggRowZA8_absurd hcfg hnb h
  · exact s2jn_ggRowZE6_absurd hcfg hnb h

end E5part

end CFSG.StandardType

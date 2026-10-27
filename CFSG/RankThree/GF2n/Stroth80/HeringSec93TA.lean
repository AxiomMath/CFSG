module

public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem h352_of (hc : Ctx M Q Z B) (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) :
    ∀ m ∈ M, CQt Q Z (LB M Q (conjSubgroup m B)) =
      ((conjSubgroup m B ⊔ Z : Subgroup G) : Set G) := fun _ hm => hc.CQt_conj hm h35

theorem conj_LB_eq_of_forall_comm_mem_Z (hc : Ctx M Q Z B) {g : G} (hg : g ∈ M)
    (h : ∀ b ∈ B, ⁅g, b⁆ ∈ Z) : conjSubgroup g (LB M Q B) = LB M Q B := by
  have hBZ : conjSubgroup g B ⊔ Z = conjSubgroup 1 B ⊔ Z := by
    rw [conjSubgroup_one]
    apply le_antisymm
    · refine sup_le (fun x hx => ?_) le_sup_right
      rw [mem_conjSubgroup] at hx
      have e : x = ⁅g, g⁻¹ * x * g⁆ * (g⁻¹ * x * g) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (B ⊔ Z : Subgroup G).mul_mem (Subgroup.mem_sup_right (h _ hx))
        (Subgroup.mem_sup_left hx)
    · refine sup_le (fun b hb => ?_) le_sup_right
      have hgb : g * b * g⁻¹ ∈ conjSubgroup g B := by
        rw [mem_conjSubgroup]
        have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
        rw [e]
        exact hb
      have e : b = ⁅g, b⁆⁻¹ * (g * b * g⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (conjSubgroup g B ⊔ Z).mul_mem (Subgroup.mem_sup_right (Z.inv_mem (h b hb)))
        (Subgroup.mem_sup_left hgb)
  have key := hc.conj_LB_eq_of_conj_BZ hg M.one_mem hBZ
  rwa [conjSubgroup_one] at key

theorem Q_le_pCoreIn (hc : Ctx M Q Z B) {X : Subgroup G} (hQX : Q ≤ X) (hXM : X ≤ M) :
    Q ≤ inSubgroup (pCore 2) X := by
  have hQn : (Q.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun x hx => hc.hyp.Q_normal.2 (hXM hx))
  have hQp : IsPGroup 2 ↥(Q.subgroupOf X) :=
    (isPGroup_Q' hc.hyp).of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  have h1 : Q.subgroupOf X ≤ CFSG.pCore 2 ↥X :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hQn hQp
  intro x hx
  refine ⟨⟨x, hQX hx⟩, h1 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem Q1_le_Wt (hc : Ctx M Q Z B) {s : G} (hsH : s ∈ H0 M Z) {V : Subgroup G}
    (hV : ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = V) : Q1 hc s ≤ Wt Q V := by
  have hsZ : Subgroup.zpowers s ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.zpowers_le.mpr hsH.2
  have hZs : Z ≤ Subgroup.centralizer (Subgroup.zpowers s : Set G) := sec39_centralizer_symm hsZ
  have hZQ : Z ≤ Subgroup.centralizer (Q : Set G) := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc.hyp.toHyp79.V_central hz hy).symm
  have h1 : ⁅⁅Subgroup.zpowers s, Q1 hc s⁆, Q⁆ = ⊥ := by
    have hle : ⁅Subgroup.zpowers s, Q1 hc s⁆ ≤ Z :=
      Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => hg₂.2 g₁ hg₁
    exact le_bot_iff.mp ((Subgroup.commutator_mono_left hle).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZQ).le)
  have h2 : ⁅⁅Q1 hc s, Q⁆, Subgroup.zpowers s⁆ = ⊥ := by
    have hle : ⁅Q1 hc s, Q⁆ ≤ Z :=
      Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => hc.hyp.toHyp79.comm_mem_V hg₁.1 hg₂
    exact le_bot_iff.mp ((Subgroup.commutator_mono_left hle).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZs).le)
  have h3 : ⁅⁅Q, Subgroup.zpowers s⁆, Q1 hc s⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have h4 : ⁅Q, Subgroup.zpowers s⁆ ≤ Subgroup.centralizer (Q1 hc s : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have h5 : Z ≤ Subgroup.centralizer (Q1 hc s : Set G) :=
    fun z hz => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc.hyp.toHyp79.V_central hz hy.1).symm
  have h6 : V ≤ Subgroup.centralizer (Q1 hc s : Set G) := hV ▸ sup_le h4 h5
  intro x hx
  exact ⟨hx.1, sec39_centralizer_symm h6 hx⟩

theorem conjB_le_Wt_of_mem_F {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Z0 B' F : Subgroup G}
    (hB'Q : B' ≤ Q) (hZ0L : Z0 ≤ LB M Q B)
    (hV : ∀ s ∈ Z0, s ∉ Q → ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t)
    {s : G} (hsZ : s ∈ Z0) (hsQ : s ∉ Q) (hsF : s ∈ F)
    (hFB' : ∀ f ∈ F, ∀ b ∈ B', ⁅f, b⁆ ∈ Z) : B' ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hsH : s ∈ H0 M Z := hc.LB_le_H0 (hZ0L hsZ)
  have hsM : s ∈ M := hsH.1
  intro b hb
  have hb1 : b ∈ Q1 hc s := (hc.mem_Q1_iff hsM).mpr ⟨hB'Q hb, hFB' s hsF b hb⟩
  exact Q1_le_Wt hc hsH (hV s hsZ hsQ) hb1

theorem conjB_le_Wt_of_inf_CN (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {h : G} (hh : h ∈ M) {x : G} (hxL : x ∈ LB M Q B)
    (hxL' : x ∈ conjSubgroup h (LB M Q B)) (hxN : x ∈ hc.CN t) (hxQ : x ∉ Q) :
    conjSubgroup h B ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hB'Q : conjSubgroup h B ≤ Q := hc'.le
  have hpair : ∀ m ∈ M, t ∈ conjSubgroup m (LB M Q B) → ∀ b ∈ conjSubgroup m B,
      ∀ c ∈ conjSubgroup h B, b * c = c * b := by
    intro m hm hT b hb c hcB
    have hcm : Ctx M Q Z (conjSubgroup m B) := hc.conj_of_mem hm
    have hxnorm : conjSubgroup x (LB M Q (conjSubgroup m B)) = LB M Q (conjSubgroup m B) :=
      conj_LB_eq_of_forall_comm_mem_Z hcm hxM fun b' hb' =>
        (Ctx.mem_CN.mp hxN).2 b' (sec39_conjB_le_Vt hm hT hb')
    have hne : conjSubgroup (h * m⁻¹) (LB M Q (conjSubgroup m B)) ⊓
        Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G) ≠ Q := by
      intro hne'
      have hxmem : x ∈ conjSubgroup (h * m⁻¹) (LB M Q (conjSubgroup m B)) ⊓
          Subgroup.normalizer (LB M Q (conjSubgroup m B) : Set G) := by
        refine ⟨?_, conjSubgroup_eq_self_iff.mp hxnorm⟩
        rw [hc.LB_conj hm, ← conjSubgroup_mul, mul_assoc, inv_mul_cancel, mul_one]
        exact hxL'
      rw [hne'] at hxmem
      exact hxQ hxmem
    have key := stroth_3_6_of_3_5 hcm (h352_of hc h35 m hm) (M.mul_mem hh (M.inv_mem hm)) hne
    have e : conjSubgroup (h * m⁻¹) (conjSubgroup m B) = conjSubgroup h B := by
      rw [← conjSubgroup_mul, mul_assoc, inv_mul_cancel, mul_one]
    exact key b hb c (by rw [e]; exact hcB)
  have hVc : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (conjSubgroup h B : Set G) := by
    refine sec39_Vt_le ?_ fun m hm hT => ?_
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro c hcB
      exact (hc.hyp.toHyp79.V_central hz (hB'Q hcB)).symm
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hcB
      exact (hpair m hm hT b hb c hcB).symm
  intro c hcB
  exact ⟨hB'Q hcB, sec39_centralizer_symm hVc hcB⟩

end HS9

end CFSG.RankThree.GF2n.Stroth80

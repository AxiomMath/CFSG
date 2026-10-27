module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MSubBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mSub_eq_one {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥) : mSub V₀ = 1 := by
  have h1 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.one_le_mSub_of_ne_bot
    h.hyp125.pairFacts.elemAbelian₀ hV₀
  exact le_antisymm h.small h1

theorem four_le_card_V_of_hyp125 (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    4 ≤ Nat.card V := by
  rcases h.1 with ⟨hW, rfl⟩ | ⟨h0, -⟩
  · have h8 : 8 ≤ Nat.card V := hW.1.2.1
    omega
  · have hV0M : V₀ ≤ V := h0.2.2.1
    have hTI0 : CFSG.CGT.Timmesfeld75.IsTI V₀ := h0.2.2.2.1
    have hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI V := h0.2.2.2.2.1
    have hne : V₀ ≠ V := fun he => hTI (he ▸ hTI0)
    have hne0 : V₀ ≠ ⊥ := h0.1.1
    have hc0 : 1 < Nat.card V₀ := (Subgroup.one_lt_card_iff_ne_bot (H := V₀)).2 hne0
    have hmul : V₀.relIndex V * Nat.card V₀ = Nat.card V := by
      have h := Subgroup.relIndex_mul_card (H := V₀) (K := V)
      rwa [inf_eq_left.mpr hV0M] at h
    have hpos : 0 < V₀.relIndex V := by
      rcases Nat.eq_zero_or_pos (V₀.relIndex V) with h0 | h0
      · rw [h0, zero_mul] at hmul
        exact absurd hmul.symm (Nat.card_pos.ne')
      · exact h0
    have hidx : 1 < V₀.relIndex V := by
      rcases Nat.lt_or_ge 1 (V₀.relIndex V) with h1 | h1
      · exact h1
      · exfalso
        have h1' : V₀.relIndex V = 1 := by omega
        exact hne (le_antisymm hV0M (Subgroup.relIndex_eq_one.1 h1'))
    have h4 : 2 * 2 ≤ V₀.relIndex V * Nat.card V₀ :=
      Nat.mul_le_mul hidx hc0
    omega

theorem card_L0_le_four {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g)
    (hsmall : mSub V₀ ≤ 1) : Nat.card (L0Of M V₀ g) ≤ 4 := by
  have hV₀ : IsElemAbelian 2 V₀ := h.elemAbelian.mono h.le
  have h2 : Nat.card V₀ ≤ 2 := (mSub_le_one_iff hV₀).1 hsmall
  have hZ : Nat.card (Z0Of M V₀ g) ≤ 2 :=
    (Subgroup.card_le_of_le inf_le_left).trans h2
  have hYcard : Nat.card (conjSubgroup V₀ g) = Nat.card V₀ :=
    CFSG.Quasithin.E3.card_conjSubgroup V₀ g
  have hY : Nat.card (YOf M V₀ g) ≤ 2 :=
    (Subgroup.card_le_of_le (inf_le_left : YOf M V₀ g ≤ conjSubgroup V₀ g)).trans
      (by rw [hYcard]; exact h2)
  let f : ↥(Z0Of M V₀ g) × ↥(YOf M V₀ g) → ↥(L0Of M V₀ g) := fun p =>
    ⟨p.1.1 * p.2.1, Subgroup.mul_mem _
      (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (L0Of M V₀ g : Set G) := hx
    rw [Hyp65.L0_coe_eq_mul h] at hx'
    obtain ⟨z, hz, y, hy, rfl⟩ := hx'
    exact ⟨(⟨z, hz⟩, ⟨y, hy⟩), Subtype.ext rfl⟩
  have hcard : Nat.card (L0Of M V₀ g) ≤
      Nat.card (↥(Z0Of M V₀ g) × ↥(YOf M V₀ g)) :=
    Nat.card_le_card_of_surjective f hsurj
  rw [Nat.card_prod] at hcard
  have hcd : Nat.card (Z0Of M V₀ g) * Nat.card (YOf M V₀ g) ≤ 2 * 2 :=
    Nat.mul_le_mul hZ hY
  omega

theorem card_mulAut_L0 {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g)
    (hsmall : mSub V₀ ≤ 1) :
    Nat.card (MulAut ↥(L0Of M V₀ g)) = 1 ∨ Nat.card (MulAut ↥(L0Of M V₀ g)) = 6 := by
  have hcard : Nat.card (L0Of M V₀ g) ≤ 4 := card_L0_le_four h hsmall
  have hL0 : IsElemAbelian 2 (L0Of M V₀ g) := h.L0_isElemAbelian
  have hL0pg : IsPGroup 2 (L0Of M V₀ g) := IsElemAbelian.isPGroup hL0
  have hcardpow : Nat.card (L0Of M V₀ g) = 2 ^ mSub (L0Of M V₀ g) :=
    card_eq_two_pow_mSub hL0pg
  have hn : mSub (L0Of M V₀ g) ≤ 2 := by
    have hle : 2 ^ mSub (L0Of M V₀ g) ≤ 2 ^ 2 := by
      rw [← hcardpow]
      norm_num
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (W := ↥(L0Of M V₀ g)) (fun a b => hL0.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hL0.2 a a.2)) hcardpow
  have h0 : mSub (L0Of M V₀ g) = 0 ∨ mSub (L0Of M V₀ g) = 1 ∨
      mSub (L0Of M V₀ g) = 2 := by omega
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2) (n := mSub (L0Of M V₀ g))]
  rcases h0 with h0 | h0 | h0 <;> rw [h0] <;> simp [Fin.prod_univ_two] <;> norm_num

theorem mQuot_le_one_of_hyp65
    {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g)
    (hsmall : mSub V₀ ≤ 1) : CFSG.Quasithin.E3.mQuot V (conjSubgroup M g) ≤ 1 := by
  have hcard : Nat.card (L0Of M V₀ g) ≤ 4 := card_L0_le_four h hsmall
  have haut := card_mulAut_L0 h hsmall
  haveI := h.K_normal
  let ψ : ↥(LOf V g) →* MulAut ↥(L0Of M V₀ g) :=
    (L0Of M V₀ g).normalizerMonoidHom.comp
      (Subgroup.inclusion (Hyp65.L_le_normalizer_L0 h))
  have hψ : ∀ (x : ↥(LOf V g)) (a : ↥(L0Of M V₀ g)),
      ((ψ x) a : G) = (x : G) * (a : G) * (x : G)⁻¹ := by
    intro x a
    exact (L0Of M V₀ g).normalizerMonoidHom_apply_apply_coe
      ((Subgroup.inclusion (Hyp65.L_le_normalizer_L0 h)) x) a
  have hker : ψ.ker = (KOf M V g).subgroupOf (LOf V g) := by
    rw [← Hyp65.C_eq_K h]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, COf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      refine ⟨x.2, fun y hy => ?_⟩
      have h2 : ((ψ x) ⟨y, hy⟩ : G) = y := by rw [hx]; rfl
      rw [hψ] at h2
      have hcomm : (x : G) * y = y * (x : G) := by
        calc (x : G) * y = ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
          _ = y * (x : G) := by rw [h2]
      exact hcomm.symm
    · rintro ⟨-, hxcent⟩
      ext a
      rw [hψ]
      have h1 : (x : G) * (a : G) = (a : G) * (x : G) := (hxcent a a.2).symm
      calc (x : G) * (a : G) * (x : G)⁻¹ = (a : G) * (x : G) * (x : G)⁻¹ := by rw [h1]
        _ = (a : G) := by group
        _ = ((1 : MulAut ↥(L0Of M V₀ g)) a : G) := rfl
  have hdvd : Nat.card (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) ∣
      Nat.card (MulAut ↥(L0Of M V₀ g)) := by
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have hrel : (conjSubgroup M g).relIndex V ∣
      Nat.card (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) := by
    rw [← Hyp65.card_imgK h]
    exact Subgroup.card_subgroup_dvd_card (imgK M V g V)
  have hpos : (conjSubgroup M g).relIndex V ≠ 0 := CFSG.Quasithin.E3.relIndex_ne_zero' V _
  rcases haut with h1 | h6
  · have hLK1 : Nat.card (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) = 1 :=
      Nat.dvd_one.1 (h1 ▸ hdvd)
    have hrel1 : (conjSubgroup M g).relIndex V = 1 := Nat.dvd_one.1 (hLK1 ▸ hrel)
    unfold CFSG.Quasithin.E3.mQuot
    rw [hrel1]
    simp
  · have hrel6 : (conjSubgroup M g).relIndex V ∣ 6 := by
      refine hrel.trans (hdvd.trans ?_)
      rw [h6]
    have h4 : ¬ 4 ∣ (conjSubgroup M g).relIndex V := by
      intro h4
      have : 4 ∣ 6 := h4.trans hrel6
      norm_num at this
    have h2 : padicValNat 2 ((conjSubgroup M g).relIndex V) ≤ 1 := by
      by_contra hcon
      exact h4 ((padicValNat_dvd_iff_le (p := 2) (n := 2) hpos).mpr (by omega))
    exact h2

theorem inCalO_one_of_hyp65
    {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g)
    (hsmall : mSub V₀ ≤ 1) : InCalO 1 M V₀ V g := by
  have hmq := mQuot_le_one_of_hyp65 h hsmall
  have hsmall' : mSub (conjSubgroup V₀ g) ≤ 1 := by
    rw [mSub_le_one_iff (CFSG.Quasithin.E3.isElemAbelian_conjSubgroup (h.elemAbelian.mono h.le) g),
      CFSG.Quasithin.E3.card_conjSubgroup]
    exact (mSub_le_one_iff (h.elemAbelian.mono h.le)).1 hsmall
  have hmq' : CFSG.Quasithin.E3.mQuot (conjSubgroup V g) M ≤ 1 := by
    have h' := mQuot_le_one_of_hyp65 (Hyp65.swap h) hsmall'
    rwa [conjSubgroup_conjSubgroup_inv] at h'
  exact ⟨⟨h.inCalO1.1.1.1, hmq, h.inCalO1.1.1.2.2⟩,
    ⟨h.inCalO1.1.2.1, hmq', h.inCalO1.1.2.2.2⟩⟩

theorem lt_rMV_of_hyp125 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) : (mBar D.M V₀ V h.isElemAbelian : ℕ∞) < rMV D.M V := by
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
  by_cases hm1 : 1 < mBar D.M V₀ V h.isElemAbelian
  · have hbound := h162 D V₀ V hW hx h61 hV₀ hm1
    have hpos : 0 < mSub V₀ := by
      have := CFSG.LocalAnalysis.UniquenessCase.PartTwo.one_le_mSub_of_ne_bot
        h.pairFacts.elemAbelian₀ hV₀
      omega
    have hlt : ((mBar D.M V₀ V h.isElemAbelian : ℕ) : ℕ∞) <
        ((mBar D.M V₀ V h.isElemAbelian + mSub V₀ : ℕ) : ℕ∞) := by
      rw [ENat.natCast_lt_natCast]
      omega
    exact lt_of_lt_of_le hlt hbound
  · have hle : (mBar D.M V₀ V h.isElemAbelian : ℕ∞) ≤ 1 := by
      have h1 : mBar D.M V₀ V h.isElemAbelian ≤ 1 := not_lt.1 hm1
      exact ENat.natCast_le_natCast.2 h1
    exact lt_of_le_of_lt hle
      (TwelveTen.one_lt_rMV D hx h61 h.inCalV (four_le_card_V_of_hyp125 D h))

theorem concl18_1_2_of_calO_one
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥) (hO1 : calO 1 D.M V₀ V = ∅) :
    Concl18_1_2 D V₀ V h.hyp125.isElemAbelian := by
  have hV := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp125 hV₀
  have h1 := lt_rMV_of_hyp125 D hx h61 h127 h1114 h162 h.hyp125 hV₀
  intro n hn
  ext X
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, rfl, hOg⟩
  have hO : InCalO1 n D.M V₀ V g :=
    (six_six hV hP.le hP.le_normalizer hP.le_normalizer₀ hn g).1 hOg
  have hr : ((mSub V₀ + n : ℕ) : ℕ∞) < rMV D.M V := by
    have hm : mSub V₀ + n ≤ mBar D.M V₀ V hV := by
      have := mSub_eq_one h hV₀
      omega
    exact lt_of_le_of_lt (ENat.natCast_le_natCast.2 hm) h1
  have h65 : Hyp65 n D.M V₀ V g := hW.hyp6H.hyp65 hV₀ hO
  have hO' : InCalO 1 D.M V₀ V g := inCalO_one_of_hyp65 h65 h.small
  have hmem : conjSubgroup V g ∈ calO 1 D.M V₀ V := ⟨g, rfl, hO'⟩
  rw [hO1] at hmem
  exact hmem

theorem eighteen_one_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) : R18_1_1At D V₀ V p L h := by
  intro hV₀ _ _
  exact lt_rMV_of_hyp125 D hx h61 h127 h1114 h162 h.hyp125 hV₀

theorem eighteen_one_two
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L) :
    R18_1_2At D V₀ V p L h := by
  intro hV₀ hhyp hXbar
  have hV := h.hyp125.isElemAbelian
  have hempty1 : calO 1 D.M V₀ V = ∅ := by
    rcases hhyp with hgt | hzero
    · have hb : bBar (UC22.conjClosure D.M L) D.M V₀ V hV < mBar D.M V₀ V hV - 1 := by
        have hk := (h.hyp125.mBarGT_iff_lt_mBar
          (bBar (UC22.conjClosure D.M L) D.M V₀ V hV + 1)).1 hgt
        omega
      have hno := twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482 h.hyp125 hV₀
        (TwelveTwentyThree.conjClosure_le h.hL.1.1.le)
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L) hXbar hb
        (TwelveTwentyThree.xCond1218_conjClosure h.hyp125 hV₀ h.hL.1.1 h.hL.1.2.2 1)
      ext X
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, rfl, hOg⟩
      exact hno g hOg
    · exact hzero
  exact concl18_1_2_of_calO_one D hx h61 h127 h1114 h162 h hV₀ hempty1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

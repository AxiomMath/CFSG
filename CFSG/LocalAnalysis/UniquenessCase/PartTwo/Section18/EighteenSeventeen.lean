module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBarHyp18
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteenCaseThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_deltaN_of_centralizer_commElt (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (n d : ℕ)
    (hgap : ∀ (t : stabTil V₀ V), (t : G) ∈ D.M → (∃ k : ℕ, orderOf (t : G) = 2 ^ k) →
      ¬ CentralizesMod V₀ V (t : G) →
      Nat.card V < 2 ^ d * Nat.card (centMod V₀ V (t : G)) →
      ∀ z ∈ commElt V (t : G), z ≠ 1 → Subgroup.centralizer ({z} : Set G) ≤ D.M) :
    (d : ℕ∞) ≤ deltaN n D.M V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hVM : V ≤ D.M := h.hyp62.le_M
  have hM0 : D.M ≤ Subgroup.normalizer (V₀ : Set G) := h.hyp62.normal
  have hMN : D.M ≤ Subgroup.normalizer (V : Set G) := le_of_eq h.hyp62.normalizer_eq.symm
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, t, ⟨htM, htC⟩, ⟨k, hk⟩, W, hWV, -, hUW, hWt, hP⟩ := hU
  have htS : t ∈ stabTil V₀ V := le_stabTil hMN hM0 htM
  obtain ⟨w, hwW, hwt⟩ := SetLike.not_le_iff_exists.1 hWt
  have hwM : w ∈ D.M := hVM (hWV hwW)
  have hz1 : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
    intro h1
    apply hwt
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : t⁻¹ * w * t = w := by
      have := congrArg (fun y => w * y) h1
      simpa [mul_assoc] using this
    have h3 : w * t = t * w := by
      have := congrArg (fun y => t * y) h2
      simpa [mul_assoc] using this
    exact h3
  have hzmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
  have hzcomm : w⁻¹ * t⁻¹ * w * t ∈ commElt V t :=
    (Subgroup.closure_mono (fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hWV hy, rfl⟩))
      hzmem
  by_cases hct : CentralizesMod V₀ V t
  · exfalso
    have hc : t * w * t⁻¹ * w⁻¹ ∈ V₀ := hct w (hWV hwW)
    have hc1 : t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 htM) _).1 (V₀.inv_mem hc)
    have hc2 : w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w ∈ V₀ :=
      (Subgroup.mem_normalizer_iff''.1 (hM0 hwM) _).1 hc1
    have hzV₀ : w⁻¹ * t⁻¹ * w * t ∈ V₀ := by
      have e : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ * t) * w := by group
      rw [e]
      exact hc2
    have hXV : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
    have hX1 : Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz1
    have hN := h.hyp62.normalizer_le _ hXV hX1
    have hcent_eq : Subgroup.centralizer ({w⁻¹ * t⁻¹ * w * t} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers (w⁻¹ * t⁻¹ * w * t) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hP _ hzmem (((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN)
  · by_cases hbig : 2 ^ d * Nat.card (centMod V₀ V t) ≤ Nat.card V
    · have hsub : (U : Set G) ⊆ centMod V₀ V t := by
        intro u hu
        refine ⟨hUV hu, ?_⟩
        have hut : Commute u t := (Subgroup.mem_centralizer_iff.1 htC u hu)
        have hone : t * u * t⁻¹ * u⁻¹ = 1 := by
          rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
          exact hut.symm.eq
        rw [hone]
        exact V₀.one_mem
      have hcard : Nat.card U ≤ Nat.card (centMod V₀ V t) := Nat.card_mono (Set.toFinite _) hsub
      have hle : 2 ^ d * Nat.card U ≤ Nat.card V := by
        calc 2 ^ d * Nat.card U ≤ 2 ^ d * Nat.card (centMod V₀ V t) :=
              Nat.mul_le_mul_left _ hcard
          _ ≤ Nat.card V := hbig
      have hVU := E3.card_eq_two_pow_mul hV2 hUV
      have hpos : 0 < Nat.card U := Nat.card_pos
      have h3 : 2 ^ d * Nat.card U ≤ 2 ^ E3.mQuot V U * Nat.card U := by
        rw [← hVU]
        exact hle
      have h4 := Nat.le_of_mul_le_mul_right h3 hpos
      have h5 : d ≤ E3.mQuot V U := (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
      exact_mod_cast h5
    · exfalso
      have hsmall : Nat.card V < 2 ^ d * Nat.card (centMod V₀ V t) := Nat.lt_of_not_le hbig
      exact hP _ hzmem (hgap ⟨t, htS⟩ htM ⟨k, hk⟩ hct hsmall _ hzcomm hz1)

theorem centralizer_le_of_gap (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {z : G} (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hmod : ∃ Q : Subgroup G,
      Q ≤ D.M ⊓ Subgroup.centralizer ({z} : Set G) ∧ IsPGroup p Q ∧ ¬ IsCyclic Q) :
    Subgroup.centralizer ({z} : Set G) ≤ D.M := by
  obtain ⟨Q, hQM, hQp, hQc⟩ := hmod
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.centralizer_le_of_noncyclic D h61 hp
    (hQM.trans inf_le_left) hQp hQc hz1
    ⟨1, by simpa using h.isElemAbelian.2 z hzV⟩ (hQM.trans inf_le_right)

theorem commElt_le_V_of_mem_M (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {t : G} (htM : t ∈ D.M) {z : G}
    (hz : z ∈ commElt V t) : z ∈ V := by
  have hMN : D.M ≤ Subgroup.normalizer (V : Set G) := le_of_eq h.normalizer_eq.symm
  refine CFSG.LocalAnalysis.WeakClosure81.commElt_le_of_commutator_mem (V₀ := V) (W := V) (t := t)
    Subgroup.le_normalizer (hMN htM) (fun w hw => ?_) hz
  rw [commutatorElement_def]
  exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hMN htM) w).1 hw) (V.inv_mem hw)

@[expose] def Gap_18_17_one (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_1 D V₀ V p L h → ∀ (t : stabTil V₀ V), (t : G) ∈ D.M →
    (∃ k : ℕ, orderOf (t : G) = 2 ^ k) → ¬ CentralizesMod V₀ V (t : G) →
    Nat.card V < 2 ^ (2 * S17.nOf L) * Nat.card (centMod V₀ V (t : G)) →
    ∀ z ∈ commElt V (t : G), z ≠ 1 →
      ∃ Q : Subgroup G,
        Q ≤ D.M ⊓ Subgroup.centralizer ({z} : Set G) ∧ IsPGroup p Q ∧ ¬ IsCyclic Q

@[expose] def Gap_18_17_two (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ s : ℕ, P18_13_2 D V₀ V p L h s → ∀ (t : stabTil V₀ V), (t : G) ∈ D.M →
    (∃ k : ℕ, orderOf (t : G) = 2 ^ k) → ¬ CentralizesMod V₀ V (t : G) →
    Nat.card V < 2 ^ (2 * S17.nOf L * s) * Nat.card (centMod V₀ V (t : G)) →
    ∀ z ∈ commElt V (t : G), z ≠ 1 →
      ∃ Q : Subgroup G,
        Q ≤ D.M ⊓ Subgroup.centralizer ({z} : Set G) ∧ IsPGroup p Q ∧ ¬ IsCyclic Q

theorem eighteen_seventeen_one (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (hgap : Gap_18_17_one D V₀ V p L h) :
    R18_17_1At D V₀ V p L h := by
  intro h1
  refine le_deltaN_of_centralizer_commElt D h.hyp125 (mSub V) (2 * S17.nOf L) ?_
  intro t htM ht2 hnc hsmall z hz hz1
  have hzV : z ∈ V := commElt_le_V_of_mem_M D h.hyp125 htM hz
  exact centralizer_le_of_gap D h61 h.hyp125 h.hp hzV hz1
    (hgap h1 t htM ht2 hnc hsmall z hz hz1)

theorem eighteen_seventeen_two (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h61 : UC6.R6_1 D) (hgap : Gap_18_17_two D V₀ V p L h) :
    R18_17_2At D V₀ V p L h := by
  intro s h2
  refine le_deltaN_of_centralizer_commElt D h.hyp125 (mSub V) (2 * S17.nOf L * s) ?_
  intro t htM ht2 hnc hsmall z hz hz1
  have hzV : z ∈ V := commElt_le_V_of_mem_M D h.hyp125 htM hz
  exact centralizer_le_of_gap D h61 h.hyp125 h.hp hzV hz1
    (hgap s h2 t htM ht2 hnc hsmall z hz hz1)

@[expose] def Gap_18_19_aBar (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  P18_13_3 D V₀ V p L h → aBar D.M V₀ V h.hyp125.isElemAbelian ≤ S17.nOf L

section Certified


theorem two_lt_nOf_of_p18_13_3 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) (h4 : R18_4At D V₀ V p L) :
    P18_13_3 D V₀ V p L h → 2 < S17.nOf L := by
  intro h3
  obtain ⟨f, hO, -⟩ := h3
  obtain ⟨hL2, hnof, h2f, -⟩ := isOmegaPlus_barSub_cong h h1742 hO
  by_contra hle
  have hf : f = 2 := by omega
  rw [hf] at hL2
  apply h4
  have hmodel : CFSG.Blueprint.LieModel (Bar2 L) .PSL 2 2 2 := hL2
  have hSC : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 2 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hmodel (by decide)
  have hsimple : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity (Bar2 L) 2 2 2 hSC).2
  have hcard : Nat.card (Bar2 L) = 60 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hSC
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hcard

theorem eighteen_nineteen (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h16 : R18_16_3wAt D V₀ V p L h) (h17 : R18_17_3At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h)
    (hgapA : Gap_18_19_aBar D V₀ V p L h)
    (h1742 : S17.R17_42At D V₀ V) (h4 : R18_4At D V₀ V p L) :
    R18_19At D V₀ V p L h := by
  intro h3
  have hn : 2 < S17.nOf L := two_lt_nOf_of_p18_13_3 D h h1742 h4 h3
  have hAbar : aBar D.M V₀ V h.hyp125.isElemAbelian ≤ S17.nOf L := hgapA h3
  have hMne : D.M ≠ ⊤ := uc22p20a_M_ne_top D
  have hrMVle : rMV D.M V ≤ (mSub V : ℕ∞) := by
    have hCbot : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤ D.M := by
      rw [show Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ by simp]
      exact fun hle => hMne (top_le_iff.mp hle)
    calc rMV D.M V ≤ (E3.mQuot V ⊥ : ℕ∞) :=
          CFSG.LocalAnalysis.WeakClosure81.rMV_le_mQuot D.M V ⊥ bot_le hCbot
      _ = (mSub V : ℕ∞) := by rw [E3.mQuot_bot_eq_rk]; rfl
  have hr : ((2 * S17.nOf L + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V := h16 h3
  have hδ : ((2 * S17.nOf L : ℕ) : ℕ∞) ≤ deltaInf D.M V := h17 h3
  have hrm : ((2 * S17.nOf L - 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 2 * S17.nOf L - 1 + mSub V₀ <
      2 * S17.nOf L + mSub V₀)) hr
  have h2n1_lt : 2 * S17.nOf L - 1 < mSub V := by
    have h1 : ((2 * S17.nOf L - 1 : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast (by omega :
        2 * S17.nOf L - 1 ≤ 2 * S17.nOf L - 1 + mSub V₀)) hrm
    exact_mod_cast lt_of_lt_of_le h1 hrMVle
  have hjle : 2 * S17.nOf L ≤ mSub V := by omega
  have hj3 : 3 ≤ 2 * S17.nOf L := by omega
  obtain ⟨A, hA, hAne⟩ :=
    exists_gammaTwo_barSub_ne_bot_of_hyp18 D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669
  have hAgam : A ∈ F12.Gam 2 D.M V := ⟨hA.1.trans D.sylowM.le, hA.2⟩
  obtain ⟨-, U, g, hUV, hcard, hAeq⟩ := hA
  obtain ⟨B, hB⟩ := eighteen_twenty_exists_gamma h.hyp125.isElemAbelian hUV hcard hAeq hj3 hjle
  have hmem := (h18 2 A hAgam hAne (2 * S17.nOf L) hδ hrm B hB).1
  have hk0 : 0 < 2 * S17.nOf L - 2 := by omega
  have hle : 2 * S17.nOf L - 2 ≤ aBar D.M V₀ V h.hyp125.isElemAbelian := by
    have h' := CFSG.Quasithin.E3.le_aParam_of_mem_aSet
      (W := Vtil V₀ V h.hyp125.isElemAbelian) hk0 hmem
    simpa [aBar, calABar] using h'
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

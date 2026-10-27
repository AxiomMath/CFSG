module

public import CFSG.GroupTheory.StronglyPEmbeddedRank
public import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixteen_twentyThree_two_gen (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {p : ℕ}
    (hp : p ∈ D.sig)
    (hcent : ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)))
    {i : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G}
    (hAg : A ≤ conjSubgroup V g)
    (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hδ : (i : ℕ∞) < deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V) :
    ⁅V ⊓ centralizer (A : Set G), conjSubgroup V g ⊓ D.M⁆ = ⊥ := by
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hel : IsElemAbelian 2 V := h62.isElemAbelian
  by_cases hg : g ∈ D.M
  ·
    have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    have hB : conjSubgroup V g ⊓ D.M = V := by
      rw [conjSubgroup_eq_iff_mem_normalizer.2 hgN]
      exact inf_eq_left.2 h62.le_M
    rw [hB, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (IsElemAbelian.comm hel (Subgroup.mem_inf.1 hx).1 hy)
  · have hmQ : E3.mQuot (conjSubgroup V g) A = i := mQuot_eq_of_mem_gammaSet hA hAg
    have hD : A ≤ conjSubgroup V g ⊓ D.M := le_inf hAg hA.1
    have hr : ((E3.mQuot (conjSubgroup V g) A + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
      rw [hmQ]
      exact hi
    have hδ' : (E3.mQuot (conjSubgroup V g) A : ℕ∞) <
        deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V := by
      rw [hmQ]
      exact hδ
    have hCM : ∀ v ∈ V, v ≠ 1 →
        ¬ D.M ⊓ centralizer ({v} : Set G) ≤ conjSubgroup D.M g := by
      have hpsig : p ∈ D.sig := hp
      have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
        hSg.sig1_sp p (h1219 ▸ hpsig)
      intro v hvV hv1 hle
      exact hg (CFSG.GroupTheory.mem_of_pRank_pos_of_le_inf_conjSubgroup (D.sig_prime p hpsig).1 hsp
        (le_inf inf_le_left hle) (hcent v hvV hv1))
    exact six_two_four h62 hD hr hCM hδ'

theorem barSub_mem_calABar_of_gammaSet_gen (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {p : ℕ}
    (hp : p ∈ D.sig)
    (hcent : ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)))
    (hinf : ∀ g : G, g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥)
    {i k : ℕ} (hr : ((k + i + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V)
    (hδ : ((k + i : ℕ) : ℕ∞) ≤ deltaInf D.M V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) (hA1 : barSub V₀ V h.isElemAbelian A ≠ ⊥) :
    barSub V₀ V h.isElemAbelian A ∈ calABar k D.M V₀ V h.isElemAbelian := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  obtain ⟨hAM, g, hAg, hmA⟩ := id hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAst : A ≤ stabTil V₀ V := hAM.trans hMst
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  refine ⟨barSub_mono V₀ V hV hAM, hA1, isElemAbelian2_barSub hV hAel, ?_⟩
  intro C hC hlt
  have hBA : preBarSub A V₀ V hV C ≤ A := inf_le_left
  have hBst : preBarSub A V₀ V hV C ≤ stabTil V₀ V := hBA.trans hAst
  have hbarB : barSub V₀ V hV (preBarSub A V₀ V hV C) = C := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hmB : E3.mQuot A (preBarSub A V₀ V hV C) = E3.mQuot (barSub V₀ V hV A) C :=
    (mQuot_barSub_preBarSub_gen hV hAst hC).symm
  generalize hBdef : preBarSub A V₀ V hV C = B at hBA hBst hbarB hmB
  have hjk : E3.mQuot A B < k := hmB ▸ hlt
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot A B + i) D.M :=
    ⟨hBA.trans hAM, g, hBA.trans hAg, by rw [E3.mQuot_add hBA hAg, hmA]⟩
  have hi : ((E3.mQuot A B + i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot A B + i + mSub V₀ <
      k + i + mSub V₀)) hr
  have hi0 : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : i + mSub V₀ < k + i + mSub V₀)) hr
  obtain ⟨-, hcB, -⟩ :=
    S18.twentyThree_one_of_inf D h hBγ (hBA.trans hAg) hi (hinf g)
  obtain ⟨-, hcA, -⟩ := S18.twentyThree_one_of_inf D h hA hAg hi0 (hinf g)
  have hpB : preCTilde V₀ V B hV = V ⊓ centralizer (B : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hBst hcB
  have hpA : preCTilde V₀ V A hV = V ⊓ centralizer (A : Set G) :=
    preCTilde_eq_inf_centralizer_of hV hAst hcA
  have hn : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M) ≤ mSub V := by
    have h1 := mQuot_le_rk_of_le hVg.isPGroup (inf_le_left : conjSubgroup V g ⊓ D.M ≤ _)
    have h2 : rk ↥(conjSubgroup V g) = rk ↥V := by
      unfold rk
      rw [E3.card_conjSubgroup]
    unfold mSub
    omega
  have hδj : ((E3.mQuot A B + i : ℕ) : ℕ∞) <
      deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot A B + i < k + i))
      (hδ.trans (deltaN_anti hn))
  have hcomm := sixteen_twentyThree_two_gen D hSg h1219 h hp hcent hBγ (hBA.trans hAg) hi hδj
  have hle : V ⊓ centralizer (B : Set G) ≤ V ⊓ centralizer (A : Set G) := by
    intro u hu
    refine Subgroup.mem_inf.2 ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have h1 := Subgroup.commutator_mem_commutator hu
      (show a ∈ conjSubgroup V g ⊓ D.M from ⟨hAg ha, hAM ha⟩)
    rw [hcomm, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hge : V ⊓ centralizer (A : Set G) ≤ V ⊓ centralizer (B : Set G) :=
    inf_le_inf_left V (Subgroup.centralizer_le hBA)
  have hpeq : preCTilde V₀ V B hV = preCTilde V₀ V A hV := by
    rw [hpB, hpA]
    exact le_antisymm hle hge
  exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpeq)

theorem sixteen_twentyTwo_gen (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V : Subgroup G} (hVel : IsElemAbelian 2 V) {p : ℕ}
    (hp : p ∈ D.sig)
    (hcent : ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G))) :
    ∀ g : G, g ∉ D.M → ∀ U : Subgroup G, U ≤ V → rankThreeGamma 1 2 U ≤ D.M →
      conjSubgroup U g ⊓ V = ⊥ := by
  intro g hg U hU hΓ
  have hpsig : p ∈ D.sig := hp
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (h1219 ▸ hpsig)
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hwU, hwV⟩ := Subgroup.mem_inf.1 hw
  have hu : g * w * g⁻¹ ∈ U := mem_conjSubgroup_iff.mp hwU
  have hu1 : g * w * g⁻¹ ≠ 1 := by
    intro h1
    apply hw1
    have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [e, h1]
    group
  have hcentu : centralizer ({g * w * g⁻¹} : Set G) ≤ D.M :=
    CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hu
      (orderOf_eq_prime (hVel.2 _ (hU hu)) hu1)
  have hcentw : centralizer ({w} : Set G) ≤ conjSubgroup D.M g := by
    intro x hx
    rw [mem_conjSubgroup_iff]
    apply hcentu
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g * x * g⁻¹ * (g * w * g⁻¹) = g * (x * w) * g⁻¹ := by group
      _ = g * (w * x) * g⁻¹ := by rw [hx]
      _ = (g * w * g⁻¹) * (g * x * g⁻¹) := by group
  exact hg (CFSG.GroupTheory.mem_of_pRank_pos_of_le_inf_conjSubgroup (D.sig_prime p hpsig).1 hsp
    (inf_le_inf_left _ hcentw) (hcent w hwV hw1))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem Hyp125.centralizer_le_of_mem_V₀ {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {w : G} (hw : w ∈ V₀) (hw1 : w ≠ 1) : centralizer ({w} : Set G) ≤ D.M :=
  (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers w).trans
    (h.hyp62.normalizer_le _ (Subgroup.zpowers_le.2 hw) (Subgroup.zpowers_ne_bot.mpr hw1))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R18_18bAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) : Prop :=
  ∀ (i : ℕ) (A : Subgroup G), A ∈ F12.Gam i D.M V →
    barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥ →
    ∀ j : ℕ, (j : ℕ∞) ≤ deltaInf D.M V → ((j - 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V →
    ∀ (B : Subgroup G), B ∈ F12.Gam (j - 1) A V →
      barSub V₀ V h.hyp125.isElemAbelian A ∈ calABar (j - i) D.M V₀ V h.hyp125.isElemAbelian ∧
        imgTil V₀ V h.hyp125.isElemAbelian (centralizer (B : Set G)) =
          CFSG.Quasithin.fixV (barSub V₀ V h.hyp125.isElemAbelian B)

theorem inf_conjSubgroup_eq_bot_of_r18_15 {D : Data G} (hSg : UC6S846.SigmaStd D)
    {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G} (h : Hyp18 D V₀ V p L)
    (h15 : R18_15At D V₀ V p L) (g : G) (hg : g ∉ D.M) : V₀ ⊓ conjSubgroup V g = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hw₀, hwV⟩ := Subgroup.mem_inf.1 hw
  have huV : g * w * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 hwV
  have hu1 : g * w * g⁻¹ ≠ 1 := by
    intro hu
    apply hw1
    have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [e, hu]
    group
  obtain ⟨hpp, hpd⟩ := h15 _ huV hu1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(D.M ⊓ centralizer ({g * w * g⁻¹} : Set G))) p hpd
  have hyM : (y : G) ∈ D.M := y.2.1
  have hyC : (y : G) ∈ centralizer ({g * w * g⁻¹} : Set G) := y.2.2
  have hc : (g * w * g⁻¹) * (y : G) = (y : G) * (g * w * g⁻¹) :=
    (Subgroup.mem_centralizer_iff.1 hyC) _ rfl
  have hy'conj : g⁻¹ * (y : G) * g ∈ conjSubgroup D.M g := by
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * (y : G) * g) * g⁻¹ = (y : G) := by group
    rw [e]
    exact hyM
  have hy'C : g⁻¹ * (y : G) * g ∈ centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro x rfl
    calc x * (g⁻¹ * (y : G) * g) = g⁻¹ * ((g * x * g⁻¹) * (y : G)) * g := by group
      _ = g⁻¹ * ((y : G) * (g * x * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * (y : G) * g * x := by group
  have hy'M : g⁻¹ * (y : G) * g ∈ D.M := h.hyp125.centralizer_le_of_mem_V₀ hw₀ hw1 hy'C
  have hord : orderOf (g⁻¹ * (y : G) * g) = p := by
    have e : g⁻¹ * (y : G) * g = MulAut.conj g⁻¹ (y : G) := by
      simp [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  have hdvd : p ∣ Nat.card (D.M ⊓ conjSubgroup D.M g : Subgroup G) := by
    have := Subgroup.orderOf_dvd_natCard (D.M ⊓ conjSubgroup D.M g)
      (x := g⁻¹ * (y : G) * g) ⟨hy'M, hy'conj⟩
    rwa [hord] at this
  exact h.p_not_dvd_card_inf hSg hg hdvd

theorem not_le_conj_of_r18_15 {D : Data G} (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h15 : R18_15At D V₀ V p L) {g : G} (hg : g ∉ D.M) :
    ∀ v ∈ V, v ≠ 1 → ¬ D.M ⊓ centralizer ({v} : Set G) ≤ conjSubgroup D.M g := by
  intro v hvV hv1 hle
  obtain ⟨-, hpd⟩ := h15 v hvV hv1
  exact h.p_not_dvd_card_inf hSg hg
    (hpd.trans (Subgroup.card_dvd_of_le (le_inf inf_le_left hle)))

theorem twentyThree_one_of_inf (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {i : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hinf : g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥) :
    V₀ ≤ centralizer (A : Set G) ∧
      (∀ v ∈ V, (∀ a ∈ A, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (A : Set G)) ∧
      V ⊓ centralizer (A : Set G) ≤ conjSubgroup D.M g := by
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  have hel : IsElemAbelian 2 V := h62.isElemAbelian
  by_cases hg : g ∈ D.M
  · have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    have hAV : A ≤ V := CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hgN ▸ hAg
    have hcomm : ∀ v ∈ V, v ∈ centralizer (A : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.2 fun a ha => (IsElemAbelian.comm hel hv (hAV ha)).symm
    refine ⟨fun v hv => hcomm v (h62.le hv), fun v hv _ => hcomm v hv, ?_⟩
    rw [CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)]
    exact inf_le_left.trans h62.le_M
  · have hmQ : E3.mQuot (conjSubgroup V g) A = i := mQuot_eq_of_mem_gammaSet hA hAg
    have hD : A ≤ conjSubgroup V g ⊓ D.M := le_inf hAg hA.1
    have hr : ((E3.mQuot (conjSubgroup V g) A + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
      rw [hmQ]
      exact hi
    have hU : preCTilde V₀ V A hel ≤ conjSubgroup D.M g := six_two_one h62 hD hr
    have hmemU : ∀ {u : G}, u ∈ V →
        (u ∈ preCTilde V₀ V A hel ↔ ∀ a ∈ A, ⁅u, a⁆ ∈ V₀) := fun hu =>
      mem_preCTilde_iff hel (h62.le_stabTil hD) hu
    have hV₀g : V₀ ⊓ conjSubgroup V g = ⊥ := hinf hg
    have hcomm1 : ∀ u ∈ preCTilde V₀ V A hel, ∀ a ∈ A, ⁅u, a⁆ = 1 := by
      intro u hu a ha
      have h1 : ⁅u, a⁆ ∈ V₀ := (hmemU (preCTilde_le V₀ V A hel hu)).1 hu a ha
      have huN : u ∈ normalizer (conjSubgroup V g : Set G) := by
        have := hU hu
        rwa [← h62.normalizer_eq, E3.conjSubgroup_normalizer] at this
      have h2 : ⁅u, a⁆ ∈ conjSubgroup V g := by
        rw [commutatorElement_def]
        exact (conjSubgroup V g).mul_mem ((Subgroup.mem_normalizer_iff.1 huN a).1 (hAg ha))
          ((conjSubgroup V g).inv_mem (hAg ha))
      have h3 : ⁅u, a⁆ ∈ V₀ ⊓ conjSubgroup V g := ⟨h1, h2⟩
      rwa [hV₀g, Subgroup.mem_bot] at h3
    have hUC : preCTilde V₀ V A hel ≤ centralizer (A : Set G) := fun u hu =>
      Subgroup.mem_centralizer_iff.2 fun a ha =>
        (commutatorElement_eq_one_iff_mul_comm.1 (hcomm1 u hu a ha)).symm
    refine ⟨fun v hv => hUC (le_preCTilde hel h62.le hv), fun v hvV hv =>
      hUC ((hmemU hvV).2 hv), fun v hv => hU ((hmemU hv.1).2 fun a ha => ?_)⟩
    rw [commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_centralizer_iff.1 hv.2 a ha).symm]
    exact V₀.one_mem

theorem twentyThree_two (D : Data G) (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h15 : R18_15At D V₀ V p L) {i : ℕ}
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hδ : (i : ℕ∞) < deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V) :
    ⁅V ⊓ centralizer (A : Set G), conjSubgroup V g ⊓ D.M⁆ = ⊥ := by
  have h62 : Hyp62 D.M V₀ V := h.hyp125.hyp62
  have hel : IsElemAbelian 2 V := h62.isElemAbelian
  by_cases hg : g ∈ D.M
  · have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    have hB : conjSubgroup V g ⊓ D.M = V := by
      rw [CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hgN]
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
    exact six_two_four h62 hD hr (not_le_conj_of_r18_15 hSg h h15 hg) hδ'

theorem eighteen_eighteen_b (D : Data G) (hSg : UC6S846.SigmaStd D) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (h15 : R18_15At D V₀ V p L) :
    R18_18bAt D V₀ V p L h := by
  intro i A hA hA1 j hδ hr B hB
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hP := h.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  rw [S17.gam_eq_gammaSet i D.M V hV] at hA
  rw [S17.gam_eq_gammaSet (j - 1) A V hV] at hB
  have hinf := inf_conjSubgroup_eq_bot_of_r18_15 hSg h h15
  obtain ⟨hAM, g, hAg, hmA⟩ := id hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hAst : A ≤ stabTil V₀ V := hAM.trans hMst
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  refine ⟨⟨barSub_mono V₀ V hV hAM, hA1, isElemAbelian2_barSub hV hAel, ?_⟩, ?_⟩
  · intro C hC hlt
    have hBA : preBarSub A V₀ V hV C ≤ A := inf_le_left
    have hBst : preBarSub A V₀ V hV C ≤ stabTil V₀ V := hBA.trans hAst
    have hbarB : barSub V₀ V hV (preBarSub A V₀ V hV C) = C := by
      rw [barSub_preBarSub]
      exact inf_eq_left.2 hC
    have hmB : E3.mQuot A (preBarSub A V₀ V hV C) = E3.mQuot (barSub V₀ V hV A) C :=
      (mQuot_barSub_preBarSub_gen hV hAst hC).symm
    generalize hBdef : preBarSub A V₀ V hV C = B' at hBA hBst hbarB hmB
    have hjk : E3.mQuot A B' < j - i := hmB ▸ hlt
    have hBγ : B' ∈ E3.gammaSet V (E3.mQuot A B' + i) D.M :=
      ⟨hBA.trans hAM, g, hBA.trans hAg, by rw [E3.mQuot_add hBA hAg, hmA]⟩
    have hi : ((E3.mQuot A B' + i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : E3.mQuot A B' + i + mSub V₀ ≤
        j - 1 + mSub V₀)) hr
    have hi0 : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_le_of_lt (by exact_mod_cast (by omega : i + mSub V₀ ≤ j - 1 + mSub V₀)) hr
    obtain ⟨-, hcB, -⟩ := twentyThree_one_of_inf D h.hyp125 hBγ (hBA.trans hAg) hi (hinf g)
    obtain ⟨-, hcA, -⟩ := twentyThree_one_of_inf D h.hyp125 hA hAg hi0 (hinf g)
    have hpB : preCTilde V₀ V B' hV = V ⊓ centralizer (B' : Set G) :=
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
    have hδj : ((E3.mQuot A B' + i : ℕ) : ℕ∞) <
        deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V :=
      lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot A B' + i < j))
        (hδ.trans (deltaN_anti hn))
    have hcomm := twentyThree_two D hSg h h15 hBγ (hBA.trans hAg) hi hδj
    have hle : V ⊓ centralizer (B' : Set G) ≤ V ⊓ centralizer (A : Set G) := by
      intro u hu
      refine Subgroup.mem_inf.2 ⟨hu.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      have h1 := Subgroup.commutator_mem_commutator hu
        (show a ∈ conjSubgroup V g ⊓ D.M from ⟨hAg ha, hAM ha⟩)
      rw [hcomm, Subgroup.mem_bot] at h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have hge : V ⊓ centralizer (A : Set G) ≤ V ⊓ centralizer (B' : Set G) :=
      inf_le_inf_left V (Subgroup.centralizer_le hBA)
    have hpeq : preCTilde V₀ V B' hV = preCTilde V₀ V A hV := by
      rw [hpB, hpA]
      exact le_antisymm hle hge
    exact (congrArg fixV hbarB).symm.trans (fixV_barSub_eq_of_preCTilde_eq hV hpeq)
  · obtain ⟨hBA, g', hBg', hmB⟩ := id hB
    have hBM : B ≤ D.M := hBA.trans hAM
    have hBγ : B ∈ E3.gammaSet V (j - 1) D.M := ⟨hBM, g', hBg', hmB⟩
    obtain ⟨-, hcB, -⟩ := twentyThree_one_of_inf D h.hyp125 hBγ hBg' hr (hinf g')
    have hpB : preCTilde V₀ V B hV = V ⊓ centralizer (B : Set G) :=
      preCTilde_eq_inf_centralizer_of hV (hBM.trans hMst) hcB
    have himg : imgTil V₀ V hV (centralizer (B : Set G)) =
        imgTil V₀ V hV (V ⊓ centralizer (B : Set G)) := by
      ext q
      rw [mem_imgTil, mem_imgTil]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, ⟨x.val_mem, hx⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx.2, rfl⟩
    rw [himg, ← hpB]
    exact imgTil_preTil V₀ V hV _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

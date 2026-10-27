module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_of_isTI {V₀ X : Subgroup G} (hTI : CFSG.CGT.Timmesfeld75.IsTI V₀)
    (hXV : X ≤ V₀) (hX1 : X ≠ ⊥) {m : G} (hm : ∀ y, y ∈ X ↔ m * y * m⁻¹ ∈ X) {v : G}
    (hv : v ∈ V₀) : m⁻¹ * v * m ∈ V₀ := by
  have hsub : X ≤ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup m V₀ := by
    refine le_inf hXV fun x hx => ?_
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
    have e : m * (m⁻¹ * x * m) * m⁻¹ = x := by group
    exact hXV ((hm (m⁻¹ * x * m)).2 (by rw [e]; exact hx))
  have hne : V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup m V₀ ≠ ⊥ := fun hbot =>
    hX1 (le_bot_iff.1 (hbot ▸ hsub))
  have heq := (hTI m).resolve_left hne
  have hmem : v ∈ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup m V₀ := by
    rw [heq]
    exact hv
  exact CFSG.CGT.Timmesfeld75.mem_conjSubgroup.1 (Subgroup.mem_inf.1 hmem).2

theorem Hyp125.hyp62 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    Hyp62 D.M V₀ V := by
  have hP := h.pairFacts
  refine ⟨hP.elemAbelian, h.normalizer_eq, hP.le, hP.le_normalizer₀, ?_⟩
  rcases h.1 with ⟨-, h0⟩ | ⟨⟨hV₀, -, -, hTI, -, -, -⟩, -, -⟩
  · intro X hX hX1
    exact absurd (le_bot_iff.1 (h0 ▸ hX)) hX1
  · intro X hXV hX1 n hn
    rw [← normalizer_eq_of_inCalV D hV₀, Subgroup.mem_normalizer_iff]
    rw [Subgroup.mem_normalizer_iff] at hn
    have hn' : ∀ y, y ∈ X ↔ n⁻¹ * y * n⁻¹⁻¹ ∈ X := by
      intro y
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      have := hn (n⁻¹ * y * n)
      rw [e] at this
      rw [inv_inv]
      exact this.symm
    intro y
    constructor
    · intro hy
      simpa using conj_mem_of_isTI hTI hXV hX1 hn' hy
    · intro hy
      have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
      have := conj_mem_of_isTI hTI hXV hX1 hn hy
      rwa [e] at this

theorem mQuot_eq_of_mem_gammaSet {V A M : Subgroup G} {i : ℕ} (hA : A ∈ E3.gammaSet V i M)
    {g : G} (hAg : A ≤ conjSubgroup V g) : E3.mQuot (conjSubgroup V g) A = i := by
  obtain ⟨-, g', hAg', hm⟩ := hA
  rw [← hm]
  unfold E3.mQuot
  congr 1
  have h1 := Subgroup.relIndex_mul_index hAg
  have h2 := Subgroup.relIndex_mul_index hAg'
  have hidx : (conjSubgroup V g).index = (conjSubgroup V g').index := by
    have c1 := Subgroup.card_mul_index (conjSubgroup V g)
    have c2 := Subgroup.card_mul_index (conjSubgroup V g')
    rw [E3.card_conjSubgroup] at c1 c2
    have hpos : 0 < Nat.card V := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (c1.trans c2.symm)
  have hne : (conjSubgroup V g).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← hidx] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (h1.trans h2.symm)

private theorem conjSubgroup_eq_self_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : conjSubgroup A g = A := by
  ext x
  rw [mem_conjSubgroup_iff]
  exact (Subgroup.mem_normalizer_iff.1 hg x).symm

private theorem mem_of_pRank_pos_of_le_inf_conjSubgroup {p : ℕ} (hp : p.Prime) {M : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) {g : G} {X : Subgroup G}
    (hX : X ≤ M ⊓ conjSubgroup M g) (hpos : 0 < CFSG.Open.pRank p X) : g ∈ M := by
  by_contra hg
  obtain ⟨E, hEX, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp X
  have hpE : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p (by omega)
  have hg' : g⁻¹ ∉ M := fun hh => hg (by simpa using M.inv_mem hh)
  exact hsp.2.2 g⁻¹ hg' (hpE.trans (Subgroup.card_dvd_of_le (hEX.trans hX)))

private theorem inf_conjSubgroup_eq_bot_of_R1622 {D : Data G} (h22 : R1622 D)
    {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {g : G} (hg : g ∉ D.M) :
    V₀ ⊓ conjSubgroup V g = ⊥ := by
  have h62 : Hyp62 D.M V₀ V := h.hyp125.hyp62
  have hΓ : rankThreeGamma 1 2 V₀ ≤ D.M :=
    rankThreeGamma_le_of_normalizer_le h62.normalizer_le le_rfl
  have hg' : g⁻¹ ∉ D.M := fun hh => hg (by simpa using D.M.inv_mem hh)
  have h22' := h22 V₀ V h g⁻¹ hg' V₀ h62.le hΓ
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  by_contra hw1
  obtain ⟨hw₀, hwV⟩ := Subgroup.mem_inf.1 hw
  have hmem : g * w * g⁻¹ ∈ conjSubgroup V₀ g⁻¹ ⊓ V := by
    refine Subgroup.mem_inf.2 ⟨?_, mem_conjSubgroup_iff.1 hwV⟩
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := by group
    rw [e]
    exact hw₀
  rw [h22', Subgroup.mem_bot] at hmem
  apply hw1
  have e : w = g⁻¹ * (g * w * g⁻¹) * g := by group
  rw [e, hmem]
  group

theorem sixteen_twentyThree_one_of_inf (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {i : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hinf : g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥) :
    V₀ ≤ centralizer (A : Set G) ∧
      (∀ v ∈ V, (∀ a ∈ A, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (A : Set G)) ∧
      V ⊓ centralizer (A : Set G) ≤ conjSubgroup D.M g := by
  have h62 : Hyp62 D.M V₀ V := h.hyp125.hyp62
  have hel : IsElemAbelian 2 V := h62.isElemAbelian
  by_cases hg : g ∈ D.M
  ·
    have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    have hAV : A ≤ V := conjSubgroup_eq_self_of_mem_normalizer hgN ▸ hAg
    have hcomm : ∀ v ∈ V, v ∈ centralizer (A : Set G) := fun v hv =>
      Subgroup.mem_centralizer_iff.2 fun a ha => (IsElemAbelian.comm hel hv (hAV ha)).symm
    refine ⟨fun v hv => hcomm v (h62.le hv), fun v hv _ => hcomm v hv, ?_⟩
    rw [conjSubgroup_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)]
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

theorem sixteen_twentyThree_one (D : Data G) (h22 : R1622 D) {V₀ V : Subgroup G}
    (h : Hyp16 D V₀ V) {i : ℕ} {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G}
    (hAg : A ≤ conjSubgroup V g) (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V) :
    V₀ ≤ centralizer (A : Set G) ∧
      (∀ v ∈ V, (∀ a ∈ A, ⁅v, a⁆ ∈ V₀) → v ∈ centralizer (A : Set G)) ∧
      V ⊓ centralizer (A : Set G) ≤ conjSubgroup D.M g :=
  sixteen_twentyThree_one_of_inf D h hA hAg hi fun hg => inf_conjSubgroup_eq_bot_of_R1622 h22 h hg

theorem sixteen_twentyThree_one_bot (D : Data G) {V : Subgroup G} (h : Hyp16 D ⊥ V) {i : ℕ}
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V i D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hi : ((i + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V) :
    (⊥ : Subgroup G) ≤ centralizer (A : Set G) ∧
      (∀ v ∈ V, (∀ a ∈ A, ⁅v, a⁆ ∈ (⊥ : Subgroup G)) → v ∈ centralizer (A : Set G)) ∧
      V ⊓ centralizer (A : Set G) ≤ conjSubgroup D.M g :=
  sixteen_twentyThree_one_of_inf D h hA hAg hi fun _ => bot_inf_eq _

theorem sixteen_twentyThree_two (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) {i : ℕ} {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hi : ((i + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hδ : (i : ℕ∞) < deltaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V) :
    ⁅V ⊓ centralizer (A : Set G), conjSubgroup V g ⊓ D.M⁆ = ⊥ := by
  have h62 : Hyp62 D.M V₀ V := h.hyp125.hyp62
  have hel : IsElemAbelian 2 V := h62.isElemAbelian
  by_cases hg : g ∈ D.M
  ·
    have hgN : g ∈ normalizer (V : Set G) := h62.normalizer_eq ▸ hg
    have hB : conjSubgroup V g ⊓ D.M = V := by
      rw [conjSubgroup_eq_self_of_mem_normalizer hgN]
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
      obtain ⟨p, hp, hv⟩ := h21 V₀ V h
      have hpsig : p ∈ D.sig := by rw [hp]; exact Set.mem_singleton p
      have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
        hSg.sig1_sp p (h1219 ▸ hpsig)
      intro v hvV hv1 hle
      exact hg (mem_of_pRank_pos_of_le_inf_conjSubgroup (D.sig_prime p hpsig).1 hsp
        (le_inf inf_le_left hle) (hv v hvV hv1))
    exact six_two_four h62 hD hr hCM hδ'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

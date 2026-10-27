module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Statements
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.LocalAnalysis.WeakClosure81.SixNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16b_barSub_eq_bot_iff (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    {A : Subgroup G} (hAM : A ≤ D.M) :
    barSub ⊥ V h.isElemAbelian A = ⊥ ↔ A ≤ centralizer (V : Set G) := by
  have hM := h.pairFacts.le_normalizer
  have hM₀ := h.pairFacts.le_normalizer₀
  rw [barSub_eq_bot_iff h.isElemAbelian hM hM₀ hAM]
  constructor
  · intro hA a ha
    have hc := ((mem_cTilde_iff_centralizes h.isElemAbelian hM hM₀).1 (hA ha)).2
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := Subgroup.mem_bot.1 (hc v hv)
    have h2 : a * v * a⁻¹ = v := mul_inv_eq_one.1 h1
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro hA a ha
    refine (mem_cTilde_iff_centralizes h.isElemAbelian hM hM₀).2 ⟨hAM ha, fun v hv => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hA ha) v hv
    rw [Subgroup.mem_bot, ← h1]
    simp

private theorem s16b_comm_eq_bot_of_le_M (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hW : ⁅E3.wClos V 0 D.T, V⁆ = ⊥) {g : G} (hg : conjSubgroup V g ≤ D.M) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isElemAbelian.isPGroup
  obtain ⟨m, hmM, hm⟩ := UC6.exists_conj_le_of_isSylowOf D.sylowM hg
    (E3.isPGroup_conjSubgroup hV2 g)
  have hle : conjSubgroup V (g * m) ≤ D.T := by
    rw [← conjSubgroup_conjSubgroup]
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have := hm _ hx
    simpa [mul_assoc] using this
  have hle0 : conjSubgroup V (g * m) ≤ E3.wClos V 0 D.T :=
    E3.le_wClos ⟨hle, g * m, le_rfl, E3.mQuot_self _⟩
  have h1 : ⁅V, conjSubgroup V (g * m)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.1 ((Subgroup.commutator_mono hle0 le_rfl).trans hW.le)
  have hVm : conjSubgroup V m⁻¹ = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (h.pairFacts.le_normalizer (by simpa using hmM))
  have h2 := E3.conjSubgroup_commutator V (conjSubgroup V (g * m)) m⁻¹
  rw [h1, E3.conjSubgroup_bot, hVm, conjSubgroup_conjSubgroup, mul_inv_cancel_right] at h2
  exact h2.symm

private theorem s16b_exists_gamma_barSub_ne_bot (D : Data G) {V : Subgroup G}
    (h : Hyp125 D ⊥ V) (hC : ¬ centralizer (E3.cClos V 1 D.T : Set G) ≤ D.M) :
    ∃ A ∈ E3.gammaSet V 1 D.T, barSub ⊥ V h.isElemAbelian A ≠ ⊥ := by
  by_contra hcon
  have hcon' : ∀ A ∈ E3.gammaSet V 1 D.T, barSub ⊥ V h.isElemAbelian A = ⊥ := fun A hA =>
    by_contra fun hne => hcon ⟨A, hA, hne⟩
  apply hC
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.inCalV
  have hW : E3.wClos V 1 D.T ≤ centralizer (V : Set G) :=
    E3.wClos_le_of_forall fun A hA =>
      (s16b_barSub_eq_bot_iff D h (hA.1.trans D.sylowM.le)).1 (hcon' A hA)
  have hVc : V ≤ E3.cClos V 1 D.T := le_inf hVT (Subgroup.le_centralizer_iff.1 hW)
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVc)).trans
    (centralizer_le_of_inCalV D h.inCalV)

private theorem s16b_mem_calO_one (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
    (hW : ⁅E3.wClos V 0 D.T, V⁆ = ⊥) {A : Subgroup G} (hA : A ∈ E3.gammaSet V 1 D.T)
    (hAbar : barSub ⊥ V h.isElemAbelian A ≠ ⊥) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hU : gammaOneBar V A ≤ conjSubgroup D.M g) (hidx : (gammaOneBar V A).relIndex V ≤ 2) :
    conjSubgroup V g ∈ calO 1 D.M ⊥ V := by
  have hAM : A ≤ D.M := hA.1.trans D.sylowM.le
  have hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥ := by
    intro hc
    apply hAbar
    have h1 : V ≤ centralizer (conjSubgroup V g : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    have h2 : V ≤ centralizer (A : Set G) :=
      h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hAg))
    exact (s16b_barSub_eq_bot_iff D h hAM).2 (Subgroup.le_centralizer_iff.1 h2)
  have hgM : ¬ conjSubgroup V g ≤ D.M := fun hg => hne (s16b_comm_eq_bot_of_le_M D h hW hg)
  have hgM' : ¬ V ≤ conjSubgroup D.M g := by
    intro hV
    have hle : conjSubgroup V g⁻¹ ≤ D.M := by
      have := E3.conjSubgroup_mono_left g⁻¹ hV
      rwa [E3.conjSubgroup_conj_inv] at this
    have h1 := s16b_comm_eq_bot_of_le_M D h hW hle
    have h2 := E3.conjSubgroup_commutator V (conjSubgroup V g⁻¹) g
    rw [h1, E3.conjSubgroup_bot, E3.conjSubgroup_inv_conj] at h2
    apply hne
    rw [Subgroup.commutator_comm]
    exact h2.symm
  have hUV : gammaOneBar V A ≤ V := iSup₂_le fun B _ => iSup_le fun _ => inf_le_left
  have hq : E3.mQuot V (conjSubgroup D.M g) ≤ 1 := by
    refine (E3.mQuot_mono hU).trans ?_
    unfold E3.mQuot
    have hn0 : (gammaOneBar V A).relIndex V ≠ 0 := E3.relIndex_ne_zero' V _
    generalize (gammaOneBar V A).relIndex V = n at hn0 hidx ⊢
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
    interval_cases n <;> simp
  have hm1 : E3.mQuot (conjSubgroup V g) A = 1 := mQuot_eq_of_mem_gammaSet hA hAg
  have hq' : E3.mQuot (conjSubgroup V g) D.M ≤ 1 := hm1 ▸ E3.mQuot_mono hAM
  exact ⟨g, rfl, ⟨hgM, hq, fun h0 => absurd rfl h0⟩, ⟨hgM', hq', fun h0 => absurd rfl h0⟩⟩

theorem sixteen_sixty_nine (D : Data G) (h136 : R4_136 D) (h7 : R16_7 D) (h25 : R16_25 D)
    (h33 : R16_33 D) (h40 : R16_40 D) (h48 : R16_48 D) (h57 : R16_57 D) (h63a : R16_63a D)
    (h63 : R16_63 D) (h64 : R16_64 D) (h67 : R16_67 D) (h68 : R16_68 D)
    (h68c : R16_68_close D) : Thm1669 D := by
  intro V₀ V hH hcard
  by_contra hnot
  have hsmall : mSub V₀ ≤ 2 := by
    have h2 : Nat.card V₀ = 2 ^ mSub V₀ :=
      card_eq_two_pow_mSub hH.pairFacts.elemAbelian₀.isPGroup
    have h4 : 2 ^ mSub V₀ ≤ 2 ^ 2 := by rw [← h2]; simpa using hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
  obtain ⟨L₀, hset₀, hne₀, hconc₀⟩ := h136 V₀ V ⟨hH, hsmall, hnot⟩
  have hV : IsElemAbelian 2 V := hH.isElemAbelian
  obtain ⟨L, hset, hne, hconc, h7L⟩ := h7 V₀ V L₀ hV hset₀ hne₀ hconc₀
  have hS : Sect16 D V₀ V L hV := ⟨hset, hne, hconc⟩
  have hn8 := h25 V₀ V L hV hS
  obtain ⟨hn5, hn6⟩ := h33 V₀ V L hV hS
  have hn1 := h40 V₀ V L hV hS
  have hn4 := h48 V₀ V L hV hS
  have hn7 := h57 V₀ V L hV hS
  have h23 : Case167_2 D V₀ V hV L ∨ Case167_3 D V₀ V hV L := by
    rcases h7L with c | c | c | c | c | c | c | c
    · exact absurd c hn1
    · exact Or.inl c
    · exact Or.inr c
    · exact absurd c hn4
    · exact absurd c hn5
    · exact absurd c hn6
    · exact absurd c hn7
    · exact absurd c hn8
  have h154 := h63a V₀ V L hV hS h23
  have hsit : Sit1663 D V₀ V hV L := ⟨h23, h154⟩
  have h3 : Case167_3 D V₀ V hV L := h23.resolve_left (h64 V₀ V L hV hS hsit)
  have hsit5 : Sit1665 D V₀ V hV L := ⟨h3, h154⟩
  obtain ⟨hV0, hC⟩ := h68 V₀ V L hV hS hsit5
  obtain ⟨hW, -⟩ := h63 V₀ V L hV hS hsit
  have hempty := h67 V₀ V L hV hS hsit5
  have hcentr := h68c V₀ V L hV hS hsit5 hV0
  subst hV0
  obtain ⟨A, hA, hAbar⟩ := s16b_exists_gamma_barSub_ne_bot D hH hC
  obtain ⟨g, hAg, -⟩ := hA.2
  obtain ⟨-, hU, hidx⟩ := hcentr A g hA hAbar hAg
  have hmem := s16b_mem_calO_one D hH hW hA hAbar hAg hU hidx
  rw [hempty] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

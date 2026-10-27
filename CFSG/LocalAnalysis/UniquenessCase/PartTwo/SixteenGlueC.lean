module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.UC6Syl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_27_4 (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_8 D V₀ V hV L →
      ∀ A : Subgroup G, A ≤ D.T → IsElemAbelian 2 A →
        barSub V₀ V hV A = ⊥ ∨
          ∃ a : ↥(lBar V₀ V hV L), IsSp6Transvection a ∧
            barSub V₀ V hV A = Subgroup.zpowers (a : MulAut (Vtil V₀ V hV))

private theorem s16b_three_le_C (D : Data G) (hSg : UC6S846.SigmaStd D) :
    ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M := fun p hp => by
  rw [UC6.groupPRank_eq_pRank]
  exact hSg.three_le p hp

private theorem s16b_mQuot_zpowers_bot {H : Type*} [Group H] {a : H} (ha : a ^ 2 = 1) :
    E3.mQuot (Subgroup.zpowers a) ⊥ ≤ 1 := by
  unfold E3.mQuot
  rw [Subgroup.relIndex_bot_left, Nat.card_zpowers]
  have hd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h <;> simp [h]

private theorem s16b_barSub_bot_iff_C (D : Data G) {V : Subgroup G} (h : Hyp125 D ⊥ V)
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

private theorem s16b_comm_eq_bot_of_le_M_C (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
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

theorem sixteen_twentyNine (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h129 : R129_1 D) (h61 : UC6.R6_1 D) (h274 : R16_27_4 D)
    (h28 : R16_28 D) : R16_29 D := by
  intro V₀ V L hV hS h8
  obtain ⟨hr, hδ1⟩ := h28 V₀ V L hV hS h8
  have hδ : (2 : ℕ∞) ≤ deltaInf D.M V := by
    have := Order.add_one_le_of_lt hδ1
    simpa [one_add_one_eq_two] using this
  have h := hS.setting.hyp16
  have hP := h.hyp125.pairFacts
  have hr2 : ((2 + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + mSub V₀ ≤ mSub V₀ + 4)) hr
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    have hAM : A ∈ E3.gammaSet V 0 D.M := E3.gammaSet_mono D.sylowM.le hA
    obtain ⟨hAT, g, hAg, -⟩ := hA
    have hAMle : A ≤ D.M := hAT.trans D.sylowM.le
    by_cases hbar : barSub V₀ V hV A = ⊥
    ·
      have hi0 : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
        lt_of_lt_of_le (by exact_mod_cast (by omega : 0 + mSub V₀ < 2 + mSub V₀)) hr2
      obtain ⟨-, hc, -⟩ := sixteen_twentyThree_one D h22 h hAM hAg hi0
      have hCt := (WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀
        hAMle).1 hbar
      have hVc : V ≤ centralizer (A : Set G) := fun v hv => hc v hv fun a ha => by
        have hcm := WeakClosure81.centralizesMod_of_mem_cTilde hV hP.le_normalizer
          hP.le_normalizer₀ (hCt ha) v hv
        have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
        rw [e]
        exact V₀.inv_mem hcm
      exact Subgroup.le_centralizer_iff.1 hVc
    ·
      exfalso
      have hmem := barSub_mem_calABar_of_gammaSet_zero D hSg h1219 h21 h22 h hr2 hδ hAM hbar
      have h2 : 2 ≤ E3.mQuot (barSub V₀ V hV A) ⊥ := E3.le_mQuot_bot_of_mem_aSet hmem
      have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
      have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
      rcases h274 V₀ V L hV hS h8 A hAT hAel with h0 | ⟨a, -, ha⟩
      · exact hbar h0
      · have ha2 : (a : MulAut (Vtil V₀ V hV)) ^ 2 = 1 :=
          hmem.2.2.1.2 _ (ha ▸ Subgroup.mem_zpowers _)
        rw [ha] at h2
        have := s16b_mQuot_zpowers_bot ha2
        omega
  exact ⟨hW, fifteen_thirteen_a D h129 h61 hSg.nonempty (s16b_three_le_C D hSg) h.hyp125 hW⟩

theorem sixteen_thirtyTwo (D : Data G) (h274 : R16_27_4 D) (h28 : R16_28 D) (h29 : R16_29 D)
    (h31 : R16_31 D) : R16_32 D := by
  intro V₀ V L hV hS h8
  obtain ⟨hV0, -⟩ := h31 V₀ V L hV hS h8
  subst hV0
  obtain ⟨hr, -⟩ := h28 ⊥ V L hV hS h8
  have hH : Hyp125 D ⊥ V := hS.setting.hyp16.hyp125
  have hW29 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (h29 ⊥ V L hV hS h8).1
  have hNV : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hH.inCalV
  have hm0 : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
  have hr4 : ((4 : ℕ) : ℕ∞) ≤ rMV D.M V := by simpa [hm0] using hr
  have hW : E3.wClos V 1 D.T ≤ centralizer (V : Set G) := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hmA⟩ := hA
    have hAM : A ≤ D.M := hAT.trans D.sylowM.le
    by_contra hnc
    have hbar : barSub ⊥ V hV A ≠ ⊥ := fun hb => hnc ((s16b_barSub_bot_iff_C D hH hAM).1 hb)
    have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
    have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
    have hAst : A ≤ stabTil ⊥ V :=
      hAM.trans (le_stabTil hH.pairFacts.le_normalizer hH.pairFacts.le_normalizer₀)
    have hbarq : E3.mQuot (barSub ⊥ V hV A) ⊥ ≤ 1 := by
      rcases h274 ⊥ V L hV hS h8 A hAT hAel with h0 | ⟨a, -, ha⟩
      · exact absurd h0 hbar
      · have ha2 : (a : MulAut (Vtil ⊥ V hV)) ^ 2 = 1 :=
          (isElemAbelian2_barSub hV hAel).2 _ (ha ▸ Subgroup.mem_zpowers _)
        rw [ha]
        exact s16b_mQuot_zpowers_bot ha2
    set Dk : Subgroup G := preBarSub A ⊥ V hV (⊥ : Subgroup (MulAut (Vtil ⊥ V hV))) with hDk
    have hDkA : Dk ≤ A := inf_le_left
    have hbarDk : barSub ⊥ V hV Dk = ⊥ := by
      rw [hDk, barSub_preBarSub]
      exact bot_inf_eq _
    have hDkC : Dk ≤ centralizer (V : Set G) :=
      (s16b_barSub_bot_iff_C D hH (hDkA.trans hAM)).1 hbarDk
    have hmDk : E3.mQuot A Dk ≤ 1 := by
      have e : E3.mQuot (barSub ⊥ V hV A) ⊥ = E3.mQuot A Dk :=
        mQuot_barSub_preBarSub_gen hV hAst bot_le
      rw [← e]
      exact hbarq
    have hq : E3.mQuot (conjSubgroup V g) Dk ≤ 2 := by
      rw [E3.mQuot_add hDkA hAg, hmA]
      omega
    have hlt : ((E3.mQuot (conjSubgroup V g) Dk : ℕ) : ℕ∞) <
        rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
      rw [rMV_conj hNV g]
      have h2 : ((E3.mQuot (conjSubgroup V g) Dk : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := by
        exact_mod_cast hq
      have h24 : ((2 : ℕ) : ℕ∞) < ((4 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : 2 < 4)
      exact lt_of_le_of_lt h2 (lt_of_lt_of_le h24 hr4)
    have hcent := centralizer_le_of_mQuot_lt_rMV (M := conjSubgroup D.M g)
      (V := conjSubgroup V g) (X := Dk) (hDkA.trans hAg) hlt
    have hVle : V ≤ conjSubgroup D.M g := (Subgroup.le_centralizer_iff.1 hDkC).trans hcent
    have hle : conjSubgroup V g⁻¹ ≤ D.M := by
      have := E3.conjSubgroup_mono_left g⁻¹ hVle
      rwa [E3.conjSubgroup_conj_inv] at this
    have h1 := s16b_comm_eq_bot_of_le_M_C D hH hW29 hle
    have h2 := E3.conjSubgroup_commutator V (conjSubgroup V g⁻¹) g
    rw [h1, E3.conjSubgroup_bot, E3.conjSubgroup_inv_conj] at h2
    have hVgC : conjSubgroup V g ≤ centralizer (V : Set G) := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_
      exact h2.symm
    exact hnc (hAg.trans hVgC)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hW

theorem sixteen_twentyFive_of_inputs (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h21 : R1621 D) (h22 : R1622 D) (h129 : R129_1 D)
    (h61 : UC6.R6_1 D) (h24 : R16_24c D) (h274 : R16_27_4 D) (h28 : R16_28 D)
    (h30 : R16_30 D) : R16_25 D := by
  have h29 := sixteen_twentyNine D hSg h1219 h21 h22 h129 h61 h274 h28
  have h31 := sixteen_thirtyOne D hSg h1219 h24 h29 h30
  exact sixteen_twentyFive D h31 (sixteen_thirtyTwo D h274 h28 h29 h31)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

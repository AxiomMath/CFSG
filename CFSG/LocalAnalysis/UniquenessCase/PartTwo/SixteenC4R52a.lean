module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Nonsing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c4_r52_comm_mem_inf (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hVM : V ≤ conjSubgroup D.M g) {a v : G} (ha : a ∈ conjSubgroup V g) (hv : v ∈ V) :
    ⁅a, v⁆ ∈ V ⊓ conjSubgroup V g := by
  have h62 := hS.setting.hyp16.hyp125.hyp62
  rw [Subgroup.mem_inf, commutatorElement_def]
  constructor
  · have haN : a ∈ normalizer (V : Set G) := by
      rw [h62.normalizer_eq]
      exact hAM ha
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 haN v).1 hv) (V.inv_mem hv)
  · have hvN : v ∈ normalizer (conjSubgroup V g : Set G) := by
      rw [← E3.conjSubgroup_normalizer V g, h62.normalizer_eq]
      exact hVM hv
    have hmem : v * a⁻¹ * v⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.1 hvN a⁻¹).1 ((conjSubgroup V g).inv_mem ha)
    simpa [mul_assoc] using (conjSubgroup V g).mul_mem ha hmem

theorem s16c4_r52_commV_le (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hVM : V ≤ conjSubgroup D.M g) :
    commV (barSub V₀ V hV (conjSubgroup V g)) ≤ imgTil V₀ V hV (V ⊓ conjSubgroup V g) := by
  rw [commV, Subgroup.closure_le]
  rintro y ⟨x, hxX, v, rfl⟩
  obtain ⟨u, rfl⟩ := mkTil_surjective V₀ V hV v
  obtain ⟨a, haX, hact⟩ := (mem_barSub V₀ V hV (conjSubgroup V g) x).1 hxX
  rw [← hact, actTil_mk, ← map_inv, ← map_mul]
  refine (mem_imgTil V₀ V hV (V ⊓ conjSubgroup V g) _).2
    ⟨actStab V₀ V hV a u * u⁻¹, ?_, rfl⟩
  rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, ← commutatorElement_def]
  exact s16c4_r52_comm_mem_inf D hS hAM hVM haX u.val_mem

theorem s16c4_r52_sing_of_mem_commV (D : Data G) (h61 : UC6.R6_1 D) (h22 : R1622 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) (F : UFrame V₀ V hV L) {g : G} (hg : g ∉ D.M)
    (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    {w : Vtil V₀ V hV} (hw : w ∈ commV (barSub V₀ V hV (conjSubgroup V g))) : F.Sing w := by
  have hw' : w ∈ imgTil V₀ V hV (V ⊓ conjSubgroup V g) :=
    s16c4_r52_commV_le D hS hAM hVM hw
  obtain ⟨x, hx, hxw⟩ := (mem_imgTil V₀ V hV (V ⊓ conjSubgroup V g) w).1 hw'
  rw [← hxw]
  exact s16c4_sing_of_mem_inf_conj D h61 h22 hS h4 F hg x (Subgroup.mem_inf.1 hx).2

theorem s16c4_r52_barSub_ne_bot (D : Data G) (h22 : R1622 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V) {g : G} (hAM : conjSubgroup V g ≤ D.M)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    barSub V₀ V hV (conjSubgroup V g) ≠ ⊥ := by
  intro hbot
  have h62 := hS.setting.hyp16.hyp125.hyp62
  have hA : conjSubgroup V g ∈ E3.gammaSet V 0 D.M := ⟨hAM, g, le_rfl, E3.mQuot_self _⟩
  have hi : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    refine lt_of_lt_of_le ?_ hr
    rw [ENat.natCast_lt_natCast]
    omega
  have h23 := (sixteen_twentyThree_one D h22 hS.setting.hyp16 hA le_rfl hi).2.1
  refine hne (le_bot_iff.1 (Subgroup.commutator_le.2 ?_))
  intro v hv a ha
  have hvcent : v ∈ centralizer (conjSubgroup V g : Set G) :=
    h23 v hv fun a ha => by
      have haM : a ∈ D.M := hAM ha
      have hstab : a ∈ stabTil V₀ V :=
        ⟨by rwa [h62.normalizer_eq], h62.normal haM⟩
      have hact : actTil V₀ V hV ⟨a, hstab⟩ ∈ barSub V₀ V hV (conjSubgroup V g) :=
        actTil_mem_barSub V₀ V hV ha hstab
      rw [hbot, Subgroup.mem_bot] at hact
      have hcomm : a * v * a⁻¹ * v⁻¹ ∈ V₀ :=
        (actTil_eq_one_iff V₀ V hV ⟨a, hstab⟩).1 hact v hv
      have : ⁅a, v⁆ ∈ V₀ := by rwa [commutatorElement_def]
      rw [← commutatorElement_inv]
      exact V₀.inv_mem this
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.1 hvcent a ha).symm

theorem s16c4_r52_symm (D : Data G) {V : Subgroup G} {g : G} (hg : g ∉ D.M)
    (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    g⁻¹ ∉ D.M ∧ conjSubgroup V g⁻¹ ≤ D.M ∧ V ≤ conjSubgroup D.M g⁻¹ ∧
      ⁅V, conjSubgroup V g⁻¹⁆ ≠ ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    exact hg (by simpa using D.M.inv_mem h)
  · intro x hx
    have hxv : g⁻¹ * x * g ∈ V := by simpa using (mem_conjSubgroup_iff.1 hx)
    have hmem : g * (g⁻¹ * x * g) * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 (hVM hxv)
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at hmem
  · intro v hv
    rw [mem_conjSubgroup_iff]
    refine hAM ?_
    rw [mem_conjSubgroup_iff]
    have e : g * (g⁻¹ * v * (g⁻¹)⁻¹) * g⁻¹ = v := by group
    rw [e]
    exact hv
  · intro h
    apply hne
    have h1 : conjSubgroup ⁅V, conjSubgroup V g⁻¹⁆ g = ⁅V, conjSubgroup V g⁆ := by
      rw [E3.conjSubgroup_commutator, E3.conjSubgroup_inv_conj, Subgroup.commutator_comm]
    rw [h, E3.conjSubgroup_bot] at h1
    exact h1.symm

theorem s16c4_r52_one (D : Data G) (h61 : UC6.R6_1 D) (h22 : R1622 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h4 : Case167_4 D V₀ V hV L) (F : UFrame V₀ V hV L)
    (hr : ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V)
    (h51 : ∀ A ∈ E3.gammaSet V 0 D.M, barSub V₀ V hV A ≠ ⊥ →
      barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV ∧ barSub V₀ V hV A ≤ lBar V₀ V hV L)
    {g : G} (hg : g ∉ D.M) (hAM : conjSubgroup V g ≤ D.M) (hVM : V ≤ conjSubgroup D.M g)
    (hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    barSub V₀ V hV (conjSubgroup V g) ≠ ⊥ ∧
      barSub V₀ V hV (conjSubgroup V g) ≤ lBar V₀ V hV L ∧
      commSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))) =
        fixSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))) ∧
      Nat.card (fixSp (F.suSub (barSub V₀ V hV (conjSubgroup V g)))) = 2 ^ 4 := by
  have hA : conjSubgroup V g ∈ E3.gammaSet V 0 D.M := ⟨hAM, g, le_rfl, E3.mQuot_self _⟩
  have hne' := s16c4_r52_barSub_ne_bot D h22 hS hr hAM hne
  obtain ⟨hcal, hAL⟩ := h51 (conjSubgroup V g) hA hne'
  have hX2 : IsElemAbelian2 (barSub V₀ V hV (conjSubgroup V g)) := hcal.2.2.1
  obtain ⟨hE2, hEc⟩ := F.suSub_sq_comm hAL hX2
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  have hmq : 2 ≤ E3.mQuot (barSub V₀ V hV (conjSubgroup V g)) ⊥ :=
    E3.le_mQuot_bot_of_mem_aSet hcal
  have hcardX : Nat.card (barSub V₀ V hV (conjSubgroup V g)) =
      2 ^ E3.mQuot (barSub V₀ V hV (conjSubgroup V g)) ⊥ := by
    rw [E3.mQuot, Subgroup.relIndex_bot_left]
    exact card_eq_two_pow_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hX2)
  have hcard :
      2 ^ (2 * 1) ≤ Nat.card ↥(F.suSub (barSub V₀ V hV (conjSubgroup V g))) := by
    rw [F.card_suSub hAL, hcardX]
    exact Nat.pow_le_pow_right (by norm_num) hmq
  have hts : ∀ u ∈ commSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))),
      herm F.σ u u = 0 := by
    intro u hu
    have hu' : F.vec (F.ofVec u) ∈
        commSp (F.suSub (barSub V₀ V hV (conjSubgroup V g))) := by simpa using hu
    have hmem : F.ofVec u ∈ commV (barSub V₀ V hV (conjSubgroup V g)) :=
      (F.mem_commV_iff_commSp hAL (F.ofVec u)).2 hu'
    have hs := s16c4_r52_sing_of_mem_commV D h61 h22 hS h4 F hg hAM hVM hmem
    simpa [UFrame.Sing] using hs
  obtain ⟨hts1, hts2⟩ :=
    ts_plane_model F.isUnitary F.two_eq_zero hE2 hEc (n := 1) le_rfl hF hcard hts
  exact ⟨hne', hAL, hts1, by rw [← hts1]; simpa using hts2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Frame
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {W : Type} [CommGroup W]

theorem s16c167_cfg2_rk_comm_cent [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {t : MulAut W} (ht1 : t ≠ 1)
    (hc : t ∈ Subgroup.centralizer (L : Set (MulAut W))) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hc' : ∀ y ∈ L, y * t = t * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hc) y hy
  have hstable : StableUnder L (commSub ⊤ (Subgroup.zpowers t)) :=
    s16c167_commV_stable hc'
  have hne : commSub ⊤ (Subgroup.zpowers t) ≠ ⊥ := by
    intro hbot
    have htop : fixV (Subgroup.zpowers t) = ⊤ :=
      top_le_iff.mp (commSub_eq_bot_iff.mp hbot)
    exact ht1 (eq_one_of_fixV_eq_top htop)
  have h3 : 3 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    by_contra h
    have hr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 2 := by omega
    have hle := s16c167_cfg2_perf_fixed F.sq F.perfect hstable hr
    rw [F.fix] at hle
    exact hne (le_bot_iff.mp hle)
  rwa [rkIdx_fixV_zpowers, commV_eq_commSub]

theorem s16c167_cfg2_rk_noncent [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {t : MulAut W} (ht : t ∈ X)
    (hc : t ∉ Subgroup.centralizer (L : Set (MulAut W))) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hJ0ne : J₀ ≠ ⊥ := ne_bot_of_mem_irrSet F.irr₀
  have hJ1ne : J₁ ≠ ⊥ := ne_bot_of_mem_irrSet F.irr₁
  have hJ0st : StableUnder L J₀ := stableUnder_of_mem_irrSet F.irr₀
  have hJ1st : StableUnder L J₁ := stableUnder_of_mem_irrSet F.irr₁
  have hfix0 : ¬ J₀ ≤ fixV (Subgroup.zpowers t) := fun hle =>
    hc (s16c167_cfg2_cent_of_fix F hJ0st hJ0ne ht hle)
  have hfix1 : ¬ J₁ ≤ fixV (Subgroup.zpowers t) := fun hle =>
    hc (s16c167_cfg2_cent_of_fix F hJ1st hJ1ne ht hle)
  have hex : ∀ J : Subgroup W, ¬ J ≤ fixV (Subgroup.zpowers t) → ∃ u ∈ J, t u ≠ u := by
    intro J hJfix
    by_contra h
    refine hJfix fun u hu => ?_
    rw [mem_fixV_zpowers t u]
    by_contra htu
    exact h ⟨u, hu, htu⟩
  have hmain : 2 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    by_cases hcase1 : J₀.map t.toMonoidHom = J₀ ∧ J₁.map t.toMonoidHom = J₁
    · obtain ⟨u0, hu0, htu0⟩ := hex J₀ hfix0
      obtain ⟨u1, hu1, htu1⟩ := hex J₁ hfix1
      have ha0J : t u0 * u0⁻¹ ∈ J₀ := by
        have h : t u0 ∈ J₀ := hcase1.1 ▸ (Subgroup.mem_map.mpr ⟨u0, hu0, rfl⟩)
        exact J₀.mul_mem h (J₀.inv_mem hu0)
      have ha1J : t u1 * u1⁻¹ ∈ J₁ := by
        have h : t u1 ∈ J₁ := hcase1.2 ▸ (Subgroup.mem_map.mpr ⟨u1, hu1, rfl⟩)
        exact J₁.mul_mem h (J₁.inv_mem hu1)
      have ha0ne : t u0 * u0⁻¹ ≠ 1 := fun h => htu0 (mul_inv_eq_one.mp h)
      have ha1ne : t u1 * u1⁻¹ ≠ 1 := fun h => htu1 (mul_inv_eq_one.mp h)
      have ha0T : t u0 * u0⁻¹ ∈ commSub ⊤ (Subgroup.zpowers t) :=
        Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u0, trivial, rfl⟩
      have ha1T : t u1 * u1⁻¹ ∈ commSub ⊤ (Subgroup.zpowers t) :=
        Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u1, trivial, rfl⟩
      have hne0 : rk ↥(commSub ⊤ (Subgroup.zpowers t) ⊓ J₀) ≠ 0 := by
        intro h0
        have hbot : commSub ⊤ (Subgroup.zpowers t) ⊓ J₀ = ⊥ := (rk_eq_zero_iff F.sq).mp h0
        have hmem : t u0 * u0⁻¹ ∈ (⊥ : Subgroup W) :=
          hbot ▸ (Subgroup.mem_inf.mpr ⟨ha0T, ha0J⟩)
        exact ha0ne (Subgroup.mem_bot.mp hmem)
      have hne1 : rk ↥(commSub ⊤ (Subgroup.zpowers t) ⊓ J₁) ≠ 0 := by
        intro h0
        have hbot : commSub ⊤ (Subgroup.zpowers t) ⊓ J₁ = ⊥ := (rk_eq_zero_iff F.sq).mp h0
        have hmem : t u1 * u1⁻¹ ∈ (⊥ : Subgroup W) :=
          hbot ▸ (Subgroup.mem_inf.mpr ⟨ha1T, ha1J⟩)
        exact ha1ne (Subgroup.mem_bot.mp hmem)
      have hpos0 : 1 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t) ⊓ J₀) := by
        have := Nat.pos_of_ne_zero hne0
        omega
      have hpos1 : 1 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t) ⊓ J₁) := by
        have := Nat.pos_of_ne_zero hne1
        omega
      have hinf : (commSub ⊤ (Subgroup.zpowers t) ⊓ J₀) ⊓
          (commSub ⊤ (Subgroup.zpowers t) ⊓ J₁) = ⊥ := by
        rw [eq_bot_iff]
        refine le_trans (le_inf (le_trans inf_le_left inf_le_right)
          (le_trans inf_le_right inf_le_right)) ?_
        rw [F.inf_eq]
      have hsum := rk_sup_add_rk_inf (commSub ⊤ (Subgroup.zpowers t) ⊓ J₀)
        (commSub ⊤ (Subgroup.zpowers t) ⊓ J₁)
      rw [hinf, rk_bot, add_zero] at hsum
      have hmono : rk ↥((commSub ⊤ (Subgroup.zpowers t) ⊓ J₀) ⊔
          (commSub ⊤ (Subgroup.zpowers t) ⊓ J₁)) ≤
          rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
        rk_mono (sup_le inf_le_left inf_le_left)
      rw [hsum] at hmono
      omega
    · have hcase2 : J₀.map t.toMonoidHom ≠ J₀ ∨ J₁.map t.toMonoidHom ≠ J₁ := by
        by_contra h
        apply hcase1
        constructor
        · by_contra h0
          exact h (Or.inl h0)
        · by_contra h1
          exact h (Or.inr h1)
      rcases hcase2 with h0 | h1
      · have hdisj : J₀ ⊓ J₀.map t.toMonoidHom = ⊥ :=
          (s16c167_cfg2_disj F F.irr₀ ht).resolve_left h0
        have hker : J₀ ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
          rw [eq_bot_iff]
          intro w hw
          obtain ⟨hwJ, hwF⟩ := Subgroup.mem_inf.mp hw
          have htw : t w = w := (mem_fixV_zpowers t w).mp hwF
          have hwmap : w ∈ J₀.map t.toMonoidHom := ⟨w, hwJ, by simpa using htw⟩
          have hmem : w ∈ J₀ ⊓ J₀.map t.toMonoidHom := ⟨hwJ, hwmap⟩
          rw [hdisj] at hmem
          exact Subgroup.mem_bot.mp hmem
        have hmapker := rk_map_add_rk_inf_ker (commHom t) J₀
        rw [ker_commHom t, hker, rk_bot, add_zero] at hmapker
        have hle : J₀.map (commHom t) ≤ commSub ⊤ (Subgroup.zpowers t) := by
          rw [← commV_eq_commSub, commV_zpowers_eq_map t]
          exact Subgroup.map_mono le_top
        have h3 : 3 ≤ rk ↥(J₀.map (commHom t)) := by
          rw [hmapker]
          exact s16c167_cfg2_rk_ge_three F F.irr₀
        have hmono := rk_mono hle
        omega
      · have hdisj : J₁ ⊓ J₁.map t.toMonoidHom = ⊥ :=
          (s16c167_cfg2_disj F F.irr₁ ht).resolve_left h1
        have hker : J₁ ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
          rw [eq_bot_iff]
          intro w hw
          obtain ⟨hwJ, hwF⟩ := Subgroup.mem_inf.mp hw
          have htw : t w = w := (mem_fixV_zpowers t w).mp hwF
          have hwmap : w ∈ J₁.map t.toMonoidHom := ⟨w, hwJ, by simpa using htw⟩
          have hmem : w ∈ J₁ ⊓ J₁.map t.toMonoidHom := ⟨hwJ, hwmap⟩
          rw [hdisj] at hmem
          exact Subgroup.mem_bot.mp hmem
        have hmapker := rk_map_add_rk_inf_ker (commHom t) J₁
        rw [ker_commHom t, hker, rk_bot, add_zero] at hmapker
        have hle : J₁.map (commHom t) ≤ commSub ⊤ (Subgroup.zpowers t) := by
          rw [← commV_eq_commSub, commV_zpowers_eq_map t]
          exact Subgroup.map_mono le_top
        have h3 : 3 ≤ rk ↥(J₁.map (commHom t)) := by
          rw [hmapker]
          exact s16c167_cfg2_rk_ge_three F F.irr₁
        have hmono := rk_mono hle
        omega
  rwa [rkIdx_fixV_zpowers, commV_eq_commSub]

theorem s16c167_cfg2_ge [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {t : MulAut W} (ht : t ∈ X) (ht1 : t ≠ 1) :
    2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  by_cases hc : t ∈ Subgroup.centralizer (L : Set (MulAut W))
  · exact le_trans (by norm_num) (s16c167_cfg2_rk_comm_cent F ht1 hc)
  · exact s16c167_cfg2_rk_noncent F ht hc

theorem s16c167_cfg2_nc [Finite W] {X L : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (F : Cfg2Setting X L J₀ J₁) {t : MulAut W} (ht : t ∈ X)
    (hr : rkIdx (fixV (Subgroup.zpowers t)) = 2) :
    ¬ J₀ ≤ fixV (Subgroup.zpowers t) ∧ ¬ J₁ ≤ fixV (Subgroup.zpowers t) := by
  have hJ0ne : J₀ ≠ ⊥ := ne_bot_of_mem_irrSet F.irr₀
  have hJ1ne : J₁ ≠ ⊥ := ne_bot_of_mem_irrSet F.irr₁
  have hJ0st : StableUnder L J₀ := stableUnder_of_mem_irrSet F.irr₀
  have hJ1st : StableUnder L J₁ := stableUnder_of_mem_irrSet F.irr₁
  have ht_ne : t ≠ 1 := by
    intro h1
    have hzero : rkIdx (fixV (Subgroup.zpowers t)) = 0 := by
      rw [h1, Subgroup.zpowers_one_eq_bot]
      have htop : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
        ext v
        simp [mem_fixV]
      rw [htop, rkIdx, Subgroup.index_top, padicValNat_one_right]
    omega
  constructor
  · intro hle
    have hc := s16c167_cfg2_cent_of_fix F hJ0st hJ0ne ht hle
    have h3 := s16c167_cfg2_rk_comm_cent F ht_ne hc
    omega
  · intro hle
    have hc := s16c167_cfg2_cent_of_fix F hJ1st hJ1ne ht hle
    have h3 := s16c167_cfg2_rk_comm_cent F ht_ne hc
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

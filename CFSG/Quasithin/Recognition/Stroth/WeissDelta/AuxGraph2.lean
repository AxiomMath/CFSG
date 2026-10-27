module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.AuxGraph
public import CFSG.GroupTheory.OddOrderClosure
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Divides
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Setup

public section

open scoped Pointwise

open CFSG.GroupTheory

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem oddOrderClosure_ne_bot [Finite H] {K : Subgroup H}
    (hK : ¬ IsPGroup 2 K) : oddOrderClosure K ≠ ⊥ := by
  intro hbot
  apply hK
  obtain ⟨k, hk⟩ := index_oddOrderClosure_eq_two_pow K
  rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hk
  exact IsPGroup.of_card (p := 2) hk

@[expose] def AuxInv (W : ClosedGoodPath H Γ) (u : V) : Prop :=
  (∃ g : H, g • W.x 0 = u) ∧
    ∃ W' : ClosedGoodPath H Γ, W'.x 0 = u ∧ W'.kernelAt 0 = W.kernelAt 0

private theorem inv_base (W : ClosedGoodPath H Γ) : AuxInv W (W.x 0) :=
  ⟨⟨1, by simp⟩, ⟨W, rfl, rfl⟩⟩

private theorem exists_conj_of_inv [Finite H] {W W' : ClosedGoodPath H Γ} {u : V}
    (hQ : W.QuarterHyp) (hW'0 : W'.x 0 = u) (hu : ∃ g : H, g • W.x 0 = u) :
    ∃ c : H, ∀ i, c • W.x i = W'.x i := by
  obtain ⟨g, hg⟩ := hu
  exact ClosedGoodPath.exists_smul_eq (by norm_num : 3 ≤ 8) hQ.moufang hQ.weissFree hQ.ne
    hQ.localFacts hQ.loc W W' ⟨g, by rw [hg, hW'0]⟩

private theorem normalizes_of_conj_kernel {W W' : ClosedGoodPath H Γ} {c : H}
    (hc : ∀ i, c • W.x i = W'.x i) (hK : W'.kernelAt 0 = W.kernelAt 0) :
    ∀ k : H, k ∈ W.kernelAt 0 ↔ c * k * c⁻¹ ∈ W.kernelAt 0 := by
  have hmap : (W.kernelAt 0).map (MulAut.conj c).toMonoidHom = W.kernelAt 0 := by
    have h := ClosedGoodPath.kernelAt_eq_map_conj W W' hc 0
    rw [hK] at h
    exact h.symm
  exact Subgroup.mem_normalizer_iff.mp (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)

private theorem quarter_le_congr {W W' : ClosedGoodPath H Γ} {c : H}
    (hc : ∀ i, c • W.x i = W'.x i) (hK : W'.kernelAt 0 = W.kernelAt 0) (i : ℤ) :
    W'.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W'.x i)) ↔
      W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x i)) := by
  have hnorm := normalizes_of_conj_kernel hc hK
  have hfix : fixingSubgroup H (Γ.neighborSet (W'.x i)) =
      (fixingSubgroup H (Γ.neighborSet (W.x i))).map (MulAut.conj c).toMonoidHom := by
    rw [← hc i, fixingSubgroup_neighborSet_smul]
  rw [hK, hfix]
  constructor
  · intro h k hk
    obtain ⟨k', hk', heq⟩ := Subgroup.mem_map.mp (h ((hnorm k).mp hk))
    have hkk' : k' = k := (MulAut.conj c).injective heq
    rwa [← hkk']
  · intro h k hk
    rw [Subgroup.mem_map]
    refine ⟨c⁻¹ * k * c, ?_, ?_⟩
    · exact h ((hnorm (c⁻¹ * k * c)).mpr (by simpa [mul_assoc] using hk))
    · simp [mul_assoc]

private theorem quarter_of_conj {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp)
    {W' : ClosedGoodPath H Γ} {c : H} (hc : ∀ i, c • W.x i = W'.x i)
    (hK : W'.kernelAt 0 = W.kernelAt 0) (i : ℤ) :
    W'.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W'.x i)) ↔ (2 : ℤ) ∣ i := by
  rw [quarter_le_congr hc hK i, hQ.quarter i]

private theorem hasThirdFix_of_conj {W W' : ClosedGoodPath H Γ} {c : H}
    (hc : ∀ i, c • W.x i = W'.x i) (hK : W'.kernelAt 0 = W.kernelAt 0) {i : ℤ}
    (h : W'.HasThirdFix (W'.kernelAt 0) i) : W.HasThirdFix (W.kernelAt 0) i := by
  obtain ⟨z, hzadj, hz1, hz2, hzfix⟩ := h
  have hnorm := normalizes_of_conj_kernel hc hK
  refine ⟨c⁻¹ • z, ?_, ?_, ?_, ?_⟩
  · rw [← GraphAction.adj_smul c (W.x i) (c⁻¹ • z), smul_inv_smul, hc i]
    exact hzadj
  · intro heq
    apply hz1
    have h := congrArg (fun v => c • v) heq
    simpa [hc (i - 1)] using h
  · intro heq
    apply hz2
    have h := congrArg (fun v => c • v) heq
    simpa [hc (i + 1)] using h
  · intro k hk
    have hk' : c * k * c⁻¹ ∈ W'.kernelAt 0 := by
      rw [hK]
      exact (hnorm k).mp hk
    have hz := hzfix (c * k * c⁻¹) hk'
    calc k • (c⁻¹ • z) = c⁻¹ • ((c * k * c⁻¹) • z) := by
          simp [mul_smul, mul_assoc]
      _ = c⁻¹ • z := by rw [hz]

theorem exists_common_adj_of_dist_eq_two {a b : V} (h : Γ.dist a b = 2) :
    ∃ y : V, Γ.Adj a y ∧ Γ.Adj b y := by
  have hne : a ≠ b := by rintro rfl; rw [SimpleGraph.dist_self] at h; omega
  have hreach : Γ.Reachable a b := by
    by_contra hnr
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hnr] at h
    omega
  have hed : Γ.edist a b = 2 := by
    rw [← hreach.coe_dist_eq_edist, h]
    norm_num
  have hnadj : ¬ Γ.Adj a b := by
    intro hadj
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at h
    omega
  obtain ⟨y, hy⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  exact ⟨y, hy.1, hy.2⟩

private theorem inv_step_of_on_path [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} (hu : AuxInv W u) {W' : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0)
    {c : H} (hc : ∀ i, c • W.x i = W'.x i) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ z : V, Γ.Adj (W'.x ε) z ∧ z ≠ u ∧
      W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet z) ∧ AuxInv W z ∧
      ∀ v : V, Γ.Adj (W'.x ε) v → v ≠ u →
        W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet v) → v = z := by
  have h2ε : ¬ (2 : ℤ) ∣ ε := by
    rintro ⟨k, hk⟩
    rcases hε with rfl | rfl <;> omega
  have hquarter := quarter_of_conj hQ hc hW'K
  have hthird : ¬ W'.HasThirdFix (W'.kernelAt 0) ε := by
    intro h
    have h' := hasThirdFix_of_conj hc hW'K h
    have hle := (ClosedGoodPath.hasThirdFix_iff_le (H := H) (by norm_num : 3 ≤ 8)
      hQ.weissFree hQ.localFacts hQ.three W 0 ε (hQ.zassenhaus (W.x ε))).mp h'
    exact h2ε ((hQ.quarter ε).mp hle)
  have hzu : W'.x (2 * ε) ≠ u := by
    rw [← hW'0]
    rcases hε with rfl | rfl
    · simpa using (W'.ne_add_two 0).symm
    · have h := W'.ne_add_two (-2)
      rw [show (-2 : ℤ) + 2 = 0 by norm_num] at h
      simpa using h
  have hzadj : Γ.Adj (W'.x ε) (W'.x (2 * ε)) := by
    rcases hε with rfl | rfl
    · simpa using W'.adj 1
    · have h := W'.adj (-2)
      rw [show (-2 : ℤ) + 1 = -1 by norm_num] at h
      simpa using h.symm
  have hzK' : W'.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W'.x (2 * ε))) :=
    (hquarter (2 * ε)).mpr ⟨ε, by ring⟩
  have hzK : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W'.x (2 * ε))) := by
    rw [← hW'K]
    exact hzK'
  have hshiftK : (W'.shift (2 * ε)).kernelAt 0 = W.kernelAt 0 := by
    rw [ClosedGoodPath.kernelAt_shift, ClosedGoodPath.kernelAt_eq_of_le (by norm_num : 3 ≤ 8)
      hQ.moufang hQ.weissFree hQ.ne hQ.localFacts hQ.loc W' ε hzK', hW'K]
  have hzshift : (W'.shift (2 * ε)).x 0 = W'.x (2 * ε) := by
    rw [ClosedGoodPath.shift_x]; simp
  have hyu : Γ.Adj u (W'.x ε) := by
    rw [← hW'0]
    rcases hε with rfl | rfl
    · simpa using W'.adj 0
    · have h := W'.adj (-1)
      rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
      exact h.symm
  obtain ⟨h, -, hhz⟩ := hQ.loc (W'.x ε) u (W'.x (2 * ε)) hyu.symm hzadj
  obtain ⟨g₀, hg₀⟩ := hu.1
  have horbit : ∃ g : H, g • W.x 0 = W'.x (2 * ε) :=
    ⟨h * g₀, by rw [mul_smul, hg₀, hhz]⟩
  refine ⟨W'.x (2 * ε), hzadj, hzu, hzK, ⟨horbit,
    ⟨W'.shift (2 * ε), hzshift, hshiftK⟩⟩, ?_⟩
  intro v hvadj hvu hvK
  by_contra hvz
  apply hthird
  refine ⟨v, hvadj, ?_, ?_, ?_⟩
  · rcases hε with rfl | rfl
    · simpa [hW'0] using hvu
    · rw [show (-1 : ℤ) - 1 = -2 by norm_num]
      exact hvz
  · rcases hε with rfl | rfl
    · rw [show (1 : ℤ) + 1 = 2 by norm_num]
      exact hvz
    · simpa [hW'0] using hvu
  · intro k hk
    have hk' : k ∈ W.kernelAt 0 := by rwa [← hW'K]
    exact MulAction.mem_stabilizer_iff.mp ((hQ.localFacts v).kernel_le (hvK hk'))

private theorem off_path_odd [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} {W' : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0) :
    oddOrderClosure (W.kernelAt 0) ≠ ⊥ ∧
      Odd (Nat.card ↥(oddOrderClosure (W.kernelAt 0))) ∧
      W.kernelAt 0 ≤ Subgroup.normalizer
        (oddOrderClosure (W.kernelAt 0) : Set H) := by
  have hKu : W.kernelAt 0 ≤ W'.stab := by
    rw [← hW'K]; exact inf_le_right
  have hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u) := by
    rw [← hW'0, ← hW'K]; exact inf_le_left
  have hKfixW : ∀ k ∈ W.kernelAt 0, ∀ j : ℤ, k • W'.x j = W'.x j :=
    fun k hk => ClosedGoodPath.mem_stab_iff.mp (hKu hk)
  have hKo_le_K : oddOrderClosure (W.kernelAt 0) ≤ W.kernelAt 0 := oddOrderClosure_le _
  have hK_norm_Ko : W.kernelAt 0 ≤
      Subgroup.normalizer (oddOrderClosure (W.kernelAt 0) : Set H) :=
    le_trans Subgroup.le_normalizer (normalizer_le_normalizer_oddOrderClosure _)
  have hS : {h : H | h ∈ W.kernelAt 0 ∧ Odd (orderOf h)} ⊆
      ↑(MulAction.stabilizer H (W'.x 1) ⊓ MulAction.stabilizer H (W'.x 0) ⊓
        MulAction.stabilizer H (W'.x 2)) := by
    rintro h ⟨hh, -⟩
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
      ⟨MulAction.mem_stabilizer_iff.mpr (hKfixW h hh 1),
        MulAction.mem_stabilizer_iff.mpr (hKfixW h hh 0)⟩,
      MulAction.mem_stabilizer_iff.mpr (hKfixW h hh 2)⟩
  have hodd1 : Odd ((fixingSubgroup H (Γ.neighborSet (W'.x 1))).relIndex
      (Subgroup.closure {h : H | h ∈ W.kernelAt 0 ∧ Odd (orderOf h)})) :=
    (hQ.localFacts (W'.x 1)).oddClosure (W'.x 0) (W'.x 2) (W'.adj 0).symm (W'.adj 1)
      (W'.ne_add_two 0) _ hS (fun h hh => hh.2)
  have hbot1 : W.kernelAt 0 ⊓ fixingSubgroup H (Γ.neighborSet (W'.x 1)) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hkK, hkG⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_bot.mpr
      (hQ.weissFree (W'.window 0 8) (W'.window_noBack 0 8) k ?_ ?_ ?_)
    · intro i hi
      rw [ClosedGoodPath.window_apply W' 0 hi]
      exact hKfixW k hkK (0 + (i : ℤ))
    · intro w hw
      rw [show W'.window 0 8 0 = W'.x 0 from by
        rw [ClosedGoodPath.window_apply W' 0 (Nat.zero_le 8)]; simp] at hw
      rw [hW'0] at hw
      exact (mem_fixingSubgroup_iff H).mp (hKu_fix hkK) w hw
    · intro w hw
      rw [show W'.window 0 8 1 = W'.x 1 from by
        rw [ClosedGoodPath.window_apply W' 0 (by omega : (1 : ℕ) ≤ 8)]; norm_num] at hw
      exact (mem_fixingSubgroup_iff H).mp hkG w hw
  have hbotKo1 : oddOrderClosure (W.kernelAt 0) ⊓
      fixingSubgroup H (Γ.neighborSet (W'.x 1)) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hkO, hkG⟩ := Subgroup.mem_inf.mp hk
    have hkK : k ∈ W.kernelAt 0 ⊓ fixingSubgroup H (Γ.neighborSet (W'.x 1)) :=
      Subgroup.mem_inf.mpr ⟨hKo_le_K hkO, hkG⟩
    rwa [hbot1] at hkK
  have hOddKo : Odd (Nat.card ↥(oddOrderClosure (W.kernelAt 0))) := by
    have h := hodd1
    rw [← oddOrderClosure_eq_closure] at h
    rw [← Subgroup.inf_relIndex_right (fixingSubgroup H (Γ.neighborSet (W'.x 1)))
      (oddOrderClosure (W.kernelAt 0))] at h
    rw [show fixingSubgroup H (Γ.neighborSet (W'.x 1)) ⊓ oddOrderClosure (W.kernelAt 0) = ⊥ by
      rw [inf_comm]; exact hbotKo1, Subgroup.relIndex_bot_left] at h
    exact h
  exact ⟨oddOrderClosure_ne_bot hQ.notTwo, hOddKo, hK_norm_Ko⟩

private theorem off_path_kernel_bot [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} {W' : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0) {y : V}
    (hy : Γ.Adj u y) (hy1 : y ≠ W'.x 1) :
    W.kernelAt 0 ⊓ fixingSubgroup H (Γ.neighborSet y) = ⊥ := by
  have hKu : W.kernelAt 0 ≤ W'.stab := by
    rw [← hW'K]; exact inf_le_right
  have hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u) := by
    rw [← hW'0, ← hW'K]; exact inf_le_left
  have hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u := by
    intro k hk
    rw [← hW'0]
    exact ClosedGoodPath.mem_stab_iff.mp (hKu hk) 0
  have hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y := by
    intro k hk
    exact (mem_fixingSubgroup_iff H).mp (hKu_fix hk) y hy
  have hKfixW : ∀ k ∈ W.kernelAt 0, ∀ j : ℤ, k • W'.x j = W'.x j :=
    fun k hk => ClosedGoodPath.mem_stab_iff.mp (hKu hk)
  let zs : ℕ → V := fun i =>
    if i = 0 then y else if i = 1 then u else W'.x ((i : ℤ) - 1)
  have hzs_adj : ∀ i, Γ.Adj (zs i) (zs (i + 1)) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have h1 : zs 0 = y := by simp [zs]
      have h2 : zs 1 = u := by simp [zs]
      rw [h1, h2]; exact hy.symm
    · by_cases hi1 : i = 1
      · subst hi1
        have h1 : zs 1 = u := by simp [zs]
        have h2 : zs 2 = W'.x 1 := by simp [zs]
        rw [h1, h2, ← hW'0]; exact W'.adj 0
      · have h1 : zs i = W'.x ((i : ℤ) - 1) := by
          show (if i = 0 then y else if i = 1 then u else W'.x ((i : ℤ) - 1)) =
            W'.x ((i : ℤ) - 1)
          rw [if_neg hi0, if_neg hi1]
        have h2 : zs (i + 1) = W'.x (((i + 1 : ℕ) : ℤ) - 1) := by
          show (if i + 1 = 0 then y else if i + 1 = 1 then u else
            W'.x (((i + 1 : ℕ) : ℤ) - 1)) = W'.x (((i + 1 : ℕ) : ℤ) - 1)
          rw [if_neg (by omega : ¬ i + 1 = 0), if_neg (by omega : ¬ i + 1 = 1)]
        rw [h1, h2]
        have h := W'.adj ((i : ℤ) - 1)
        rwa [show (i : ℤ) - 1 + 1 = ((i + 1 : ℕ) : ℤ) - 1 by push_cast; ring] at h
  let pB : GPath Γ 8 := GPath.seqPath zs hzs_adj 0 8
  have hpB : ∀ i, i ≤ 8 → pB i = zs i := by
    intro i hi
    show GPath.seqPath zs hzs_adj 0 8 i = zs i
    rw [GPath.seqPath_apply zs hzs_adj 0 8 hi]
    simp
  have hpB_nb : pB.NoBack := by
    intro i hi
    have hi8 : i ≤ 8 := by omega
    have hi28 : i + 2 ≤ 8 := hi
    rw [hpB i hi8, hpB (i + 2) hi28]
    by_cases hi0 : i = 0
    · subst hi0
      have h0 : zs 0 = y := by simp [zs]
      have h2 : zs 2 = W'.x 1 := by simp [zs]
      rw [h0, h2]; exact hy1
    · by_cases hi1 : i = 1
      · subst hi1
        have h1 : zs 1 = u := by simp [zs]
        have h3 : zs 3 = W'.x 2 := by simp [zs]
        rw [h1, h3, ← hW'0]
        exact W'.ne_add_two 0
      · have h1 : zs i = W'.x ((i : ℤ) - 1) := by simp [zs, hi0, hi1]
        have h3 : zs (i + 2) = W'.x (((i + 2 : ℕ) : ℤ) - 1) := by
          have h0 : i + 2 ≠ 0 := by omega
          have h2' : i + 2 ≠ 1 := by omega
          simp [zs, h0, h2']
        rw [h1, h3]
        have h := W'.ne_add_two ((i : ℤ) - 1)
        rwa [show (i : ℤ) - 1 + 2 = ((i + 2 : ℕ) : ℤ) - 1 by push_cast; ring] at h
  have hpB0 : pB 0 = y := by rw [hpB 0 (by omega)]; simp [zs]
  have hpB1 : pB 1 = u := by rw [hpB 1 (by omega)]; simp [zs]
  have hbot_y : W.kernelAt 0 ⊓ fixingSubgroup H (Γ.neighborSet y) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hkK, hkG⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_bot.mpr (hQ.weissFree pB hpB_nb k ?_ ?_ ?_)
    · intro i hi
      rw [hpB i hi]
      by_cases hi0 : i = 0
      · subst hi0
        have h0 : zs 0 = y := by simp [zs]
        rw [h0]; exact hKfixy k hkK
      · by_cases hi1 : i = 1
        · subst hi1
          have h1 : zs 1 = u := by simp [zs]
          rw [h1]; exact hKfixu k hkK
        · have hiz : zs i = W'.x ((i : ℤ) - 1) := by simp [zs, hi0, hi1]
          rw [hiz]
          exact hKfixW k hkK _
    · intro w hw
      rw [hpB0] at hw
      exact (mem_fixingSubgroup_iff H).mp hkG w hw
    · intro w hw
      rw [hpB1] at hw
      exact (mem_fixingSubgroup_iff H).mp (hKu_fix hkK) w hw
  exact hbot_y

private theorem off_path_fixed_point [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} {W' : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0) {y : V}
    (hy : Γ.Adj u y) (hy1 : y ≠ W'.x 1) :
    ∃ z : V, Γ.Adj y z ∧ z ≠ u ∧
      (∀ m ∈ oddOrderClosure (W.kernelAt 0), m • z = z) := by
  have hKu : W.kernelAt 0 ≤ W'.stab := by
    rw [← hW'K]; exact inf_le_right
  have hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u) := by
    rw [← hW'0, ← hW'K]; exact inf_le_left
  have hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u := by
    intro k hk
    rw [← hW'0]
    exact ClosedGoodPath.mem_stab_iff.mp (hKu hk) 0
  have hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y := by
    intro k hk
    exact (mem_fixingSubgroup_iff H).mp (hKu_fix hk) y hy
  have hKo_le_K : oddOrderClosure (W.kernelAt 0) ≤ W.kernelAt 0 := oddOrderClosure_le _
  obtain ⟨-, hOddKo, -⟩ := off_path_odd hQ hW'0 hW'K
  have hbot_y := off_path_kernel_bot hQ hW'0 hW'K hy hy1
  have hbotKo_y : oddOrderClosure (W.kernelAt 0) ⊓
      fixingSubgroup H (Γ.neighborSet y) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    obtain ⟨hkO, hkG⟩ := Subgroup.mem_inf.mp hk
    have hkK : k ∈ W.kernelAt 0 ⊓ fixingSubgroup H (Γ.neighborSet y) :=
      Subgroup.mem_inf.mpr ⟨hKo_le_K hkO, hkG⟩
    rwa [hbot_y] at hkK
  have hrel_y : Odd ((fixingSubgroup H (Γ.neighborSet y)).relIndex
      (oddOrderClosure (W.kernelAt 0))) := by
    rw [← Subgroup.inf_relIndex_right (fixingSubgroup H (Γ.neighborSet y))
      (oddOrderClosure (W.kernelAt 0))]
    rw [show fixingSubgroup H (Γ.neighborSet y) ⊓ oddOrderClosure (W.kernelAt 0) = ⊥ by
      rw [inf_comm]; exact hbotKo_y, Subgroup.relIndex_bot_left]
    exact hOddKo
  have hKo_stab_y : oddOrderClosure (W.kernelAt 0) ≤
      MulAction.stabilizer H y ⊓ MulAction.stabilizer H u := by
    refine le_inf ?_ ?_
    · intro k hk
      rw [MulAction.mem_stabilizer_iff]
      exact hKfixy k (hKo_le_K hk)
    · intro k hk
      rw [MulAction.mem_stabilizer_iff]
      exact hKfixu k (hKo_le_K hk)
  exact (hQ.localFacts y).oddFix u hy.symm (oddOrderClosure (W.kernelAt 0)) hKo_stab_y hrel_y

private def offPathSeq (W' : ClosedGoodPath H Γ) (u y z : V) (i : ℕ) : V :=
  if i = 0 then z else if i = 1 then y else if i = 2 then u else W'.x ((i : ℤ) - 2)

private theorem off_path_path9 [Finite V] [Finite H] {W' : ClosedGoodPath H Γ}
    {u y z : V} (hW'0 : W'.x 0 = u) (hy : Γ.Adj u y) (hzy : Γ.Adj y z)
    (hzu : z ≠ u) (hy1 : y ≠ W'.x 1) :
    ∃ q : GPath Γ 9, q.NoBack ∧ ∀ i, i ≤ 9 → q i = offPathSeq W' u y z i := by
  let qs : ℕ → V := offPathSeq W' u y z
  have hqs_adj : ∀ i, Γ.Adj (qs i) (qs (i + 1)) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have h1 : qs 0 = z := by simp [qs, offPathSeq]
      have h2 : qs 1 = y := by simp [qs, offPathSeq]
      rw [h1, h2]; exact hzy.symm
    · by_cases hi1 : i = 1
      · subst hi1
        have h1 : qs 1 = y := by simp [qs, offPathSeq]
        have h2 : qs 2 = u := by simp [qs, offPathSeq]
        rw [h1, h2]; exact hy.symm
      · by_cases hi2 : i = 2
        · subst hi2
          have h1 : qs 2 = u := by simp [qs, offPathSeq]
          have h2 : qs 3 = W'.x 1 := by simp [qs, offPathSeq]
          rw [h1, h2, ← hW'0]; exact W'.adj 0
        · have h1 : qs i = W'.x ((i : ℤ) - 2) := by
            show (if i = 0 then z else if i = 1 then y else if i = 2 then u else
              W'.x ((i : ℤ) - 2)) = W'.x ((i : ℤ) - 2)
            rw [if_neg hi0, if_neg hi1, if_neg hi2]
          have h2 : qs (i + 1) = W'.x (((i + 1 : ℕ) : ℤ) - 2) := by
            show (if i + 1 = 0 then z else if i + 1 = 1 then y else if i + 1 = 2 then u
              else W'.x (((i + 1 : ℕ) : ℤ) - 2)) = W'.x (((i + 1 : ℕ) : ℤ) - 2)
            rw [if_neg (by omega : ¬ i + 1 = 0), if_neg (by omega : ¬ i + 1 = 1),
              if_neg (by omega : ¬ i + 1 = 2)]
          rw [h1, h2]
          have h := W'.adj ((i : ℤ) - 2)
          rwa [show (i : ℤ) - 2 + 1 = ((i + 1 : ℕ) : ℤ) - 2 by push_cast; ring] at h
  let q : GPath Γ 9 := GPath.seqPath qs hqs_adj 0 9
  have hq : ∀ i, i ≤ 9 → q i = qs i := by
    intro i hi
    show GPath.seqPath qs hqs_adj 0 9 i = qs i
    rw [GPath.seqPath_apply qs hqs_adj 0 9 hi]
    simp
  have hq_nb : q.NoBack := by
    intro i hi
    have hi9 : i ≤ 9 := by omega
    have hi29 : i + 2 ≤ 9 := hi
    rw [hq i hi9, hq (i + 2) hi29]
    by_cases hi0 : i = 0
    · subst hi0
      have h0 : qs 0 = z := by simp [qs, offPathSeq]
      have h2 : qs 2 = u := by simp [qs, offPathSeq]
      rw [h0, h2]; exact hzu
    · by_cases hi1 : i = 1
      · subst hi1
        have h1 : qs 1 = y := by simp [qs, offPathSeq]
        have h3 : qs 3 = W'.x 1 := by simp [qs, offPathSeq]
        rw [h1, h3]; exact hy1
      · by_cases hi2 : i = 2
        · subst hi2
          have h1 : qs 2 = u := by simp [qs, offPathSeq]
          have h4 : qs 4 = W'.x 2 := by simp [qs, offPathSeq]
          rw [h1, h4, ← hW'0]; exact W'.ne_add_two 0
        · have h1 : qs i = W'.x ((i : ℤ) - 2) := by
            simp [qs, offPathSeq, hi0, hi1, hi2]
          have h3 : qs (i + 2) = W'.x (((i + 2 : ℕ) : ℤ) - 2) := by
            have h0 : i + 2 ≠ 0 := by omega
            have h2' : i + 2 ≠ 1 := by omega
            have h3' : ¬ (i + 2 = 2) := by omega
            simp [qs, offPathSeq, h0, h2', h3', hi0]
          rw [h1, h3]
          have h := W'.ne_add_two ((i : ℤ) - 2)
          rwa [show (i : ℤ) - 2 + 2 = ((i + 2 : ℕ) : ℤ) - 2 by push_cast; ring] at h
  exact ⟨q, hq_nb, fun i hi => by simpa [qs] using hq i hi⟩

private theorem off_path_L5 [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {W' : ClosedGoodPath H Γ} {u y z : V} {q : GPath Γ 9}
    (hq : q.NoBack) (hq0 : q 0 = z) (hq1 : q 1 = y) (hq2 : q 2 = u)
    (hqseq : ∀ i, i ≤ 9 → q i = offPathSeq W' u y z i)
    (hzfix : ∀ m ∈ oddOrderClosure (W.kernelAt 0), m • z = z)
    (hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y)
    (hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u)
    (hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u))
    (hKfixW : ∀ k ∈ W.kernelAt 0, ∀ j : ℤ, k • W'.x j = W'.x j) :
    ∃ L₅ : ClosedGoodPath H Γ, L₅.x 0 = z ∧ L₅.x 1 = y ∧ L₅.x 2 = u ∧
      (∀ i : ℕ, i ≤ 9 → L₅.x (i : ℤ) = offPathSeq W' u y z i) ∧
      oddOrderClosure (W.kernelAt 0) ≤ L₅.stab ∧
      oddOrderClosure (W.kernelAt 0) ≤ L₅.kernelAt 2 := by
  let qs : ℕ → V := offPathSeq W' u y z
  have hq' : ∀ i, i ≤ 9 → q i = qs i := fun i hi => by simpa [qs] using hqseq i hi
  obtain ⟨L₅, hL₅⟩ := ClosedGoodPath.exists_of_noBack (by norm_num : 3 ≤ 8)
    hQ.moufang hQ.weissFree hQ.ne hQ.localFacts hq
  have hL₅x : ∀ i : ℕ, i ≤ 9 → L₅.x (i : ℤ) = qs i := by
    intro i hi
    rw [hL₅ i hi, hq' i hi]
  have hL₅0 : L₅.x 0 = z := by
    change L₅.x ((0 : ℕ) : ℤ) = z
    rw [hL₅x 0 (by omega)]
    simp [qs, offPathSeq]
  have hL₅1 : L₅.x 1 = y := by
    change L₅.x ((1 : ℕ) : ℤ) = y
    rw [hL₅x 1 (by omega)]
    simp [qs, offPathSeq]
  have hL₅2 : L₅.x 2 = u := by
    change L₅.x ((2 : ℕ) : ℤ) = u
    rw [hL₅x 2 (by omega)]
    simp [qs, offPathSeq]
  have hKo_stab : oddOrderClosure (W.kernelAt 0) ≤ L₅.stab := by
    rw [← ClosedGoodPath.stabPath_window (H := H) (by norm_num : 3 ≤ 8) hQ.weissFree
      hQ.localFacts L₅ 0]
    intro k hk
    rw [GPath.mem_stabPath_iff]
    intro i hi
    rw [ClosedGoodPath.window_apply L₅ 0 hi]
    have hiz : L₅.x (0 + (i : ℤ)) = qs i := by
      rw [show 0 + (i : ℤ) = ((i : ℕ) : ℤ) by simp, hL₅x i hi]
    rw [hiz]
    by_cases hi0 : i = 0
    · subst hi0
      have h0 : qs 0 = z := by simp [qs, offPathSeq]
      rw [h0]; exact hzfix k hk
    · by_cases hi1 : i = 1
      · subst hi1
        have h1 : qs 1 = y := by simp [qs, offPathSeq]
        rw [h1]; exact hKfixy k (oddOrderClosure_le _ hk)
      · by_cases hi2 : i = 2
        · subst hi2
          have h2 : qs 2 = u := by simp [qs, offPathSeq]
          rw [h2]; exact hKfixu k (oddOrderClosure_le _ hk)
        · have hiz2 : qs i = W'.x ((i : ℤ) - 2) := by
            simp [qs, offPathSeq, hi0, hi1, hi2]
          rw [hiz2]
          exact hKfixW k (oddOrderClosure_le _ hk) _
  have hKo_H5 : oddOrderClosure (W.kernelAt 0) ≤ L₅.kernelAt 2 := by
    refine le_inf ?_ hKo_stab
    rw [show L₅.x 2 = u from hL₅2]
    exact le_trans (oddOrderClosure_le _) hKu_fix
  exact ⟨L₅, hL₅0, hL₅1, hL₅2, hL₅x, hKo_stab, hKo_H5⟩

private theorem off_path_conj [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {W' : ClosedGoodPath H Γ} {u z : V} {L₅ : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0)
    (hL₅2 : L₅.x 2 = u)
    (hKo_H5 : oddOrderClosure (W.kernelAt 0) ≤ L₅.kernelAt 2) :
    ∃ c₅ : H, (∀ i, c₅ • (L₅.shift 2).x i = W'.x i) ∧
      Nat.card ↥(L₅.kernelAt 2) = Nat.card ↥(W'.kernelAt 0) ∧
      oddOrderClosure (W.kernelAt 0) =
        (oddOrderClosure (L₅.kernelAt 2)).map (MulAut.conj c₅).toMonoidHom ∧
      Nat.card ↥(oddOrderClosure (W.kernelAt 0)) =
        Nat.card ↥(oddOrderClosure (L₅.kernelAt 2)) ∧
      oddOrderClosure (W.kernelAt 0) = oddOrderClosure (L₅.kernelAt 2) ∧
      L₅.stab ≤ Subgroup.normalizer (L₅.kernelAt 2 : Set H) ∧
      L₅.stab ≤ Subgroup.normalizer (oddOrderClosure (W.kernelAt 0) : Set H) := by
  have hL₅shift0 : (L₅.shift 2).x 0 = W'.x 0 := by
    rw [ClosedGoodPath.shift_x, show (0 : ℤ) + 2 = 2 by norm_num, hL₅2, hW'0]
  obtain ⟨c₅, hc₅⟩ := ClosedGoodPath.exists_smul_eq (by norm_num : 3 ≤ 8) hQ.moufang
    hQ.weissFree hQ.ne hQ.localFacts hQ.loc (L₅.shift 2) W'
    ⟨1, by rw [one_smul, hL₅shift0]⟩
  have hcardH5 : Nat.card ↥(L₅.kernelAt 2) = Nat.card ↥(W'.kernelAt 0) := by
    have h := ClosedGoodPath.kernelAt_eq_map_conj (L₅.shift 2) W' hc₅ 0
    rw [ClosedGoodPath.kernelAt_shift] at h
    rw [h, Subgroup.card_map_of_injective (MulAut.conj c₅).injective]
  have hoddConj : oddOrderClosure (W.kernelAt 0) =
      (oddOrderClosure (L₅.kernelAt 2)).map (MulAut.conj c₅).toMonoidHom := by
    have h := ClosedGoodPath.kernelAt_eq_map_conj (L₅.shift 2) W' hc₅ 0
    rw [ClosedGoodPath.kernelAt_shift] at h
    rw [← hW'K, h]
    exact (map_oddOrderClosure (MulAut.conj c₅) (L₅.kernelAt 2)).symm
  have hcardKo : Nat.card ↥(oddOrderClosure (W.kernelAt 0)) =
      Nat.card ↥(oddOrderClosure (L₅.kernelAt 2)) := by
    rw [hoddConj, Subgroup.card_map_of_injective (MulAut.conj c₅).injective]
  have hKo_le_H5o : oddOrderClosure (W.kernelAt 0) ≤ oddOrderClosure (L₅.kernelAt 2) := by
    rw [oddOrderClosure_le_iff]
    rintro k ⟨hkK, hkodd⟩
    exact mem_oddOrderClosure_of_mem_of_odd (hKo_H5
      (mem_oddOrderClosure_of_mem_of_odd hkK hkodd)) hkodd
  have hKo_eq : oddOrderClosure (W.kernelAt 0) = oddOrderClosure (L₅.kernelAt 2) :=
    Subgroup.eq_of_le_of_card_ge hKo_le_H5o (le_of_eq hcardKo.symm)
  have hstab_norm_H5 : L₅.stab ≤ Subgroup.normalizer (L₅.kernelAt 2 : Set H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hfix : ∀ i, a • L₅.x i = L₅.x i := ClosedGoodPath.mem_stab_iff.mp ha
    exact (ClosedGoodPath.kernelAt_eq_map_conj L₅ L₅ hfix 2).symm
  have hstab_norm_Ko : L₅.stab ≤
      Subgroup.normalizer (oddOrderClosure (W.kernelAt 0) : Set H) := by
    rw [hKo_eq]
    exact le_trans hstab_norm_H5 (normalizer_le_normalizer_oddOrderClosure _)
  exact ⟨c₅, hc₅, hcardH5, hoddConj, hcardKo, hKo_eq, hstab_norm_H5, hstab_norm_Ko⟩

private theorem off_path_torus [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {y z u : V} {L₅ : ClosedGoodPath H Γ}
    (hL₅0 : L₅.x 0 = z) (hL₅1 : L₅.x 1 = y) (hL₅2 : L₅.x 2 = u)
    (hKo_stab : oddOrderClosure (W.kernelAt 0) ≤ L₅.stab)
    (hstab_norm_Ko : L₅.stab ≤ Subgroup.normalizer
      (oddOrderClosure (W.kernelAt 0) : Set H))
    (hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u)
    (hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y)
    (hzfix : ∀ m ∈ oddOrderClosure (W.kernelAt 0), m • z = z) :
    (∀ t ∈ socTorus H Γ y z u, ∀ m ∈ oddOrderClosure (W.kernelAt 0),
      t * m * t⁻¹ ∈ oddOrderClosure (W.kernelAt 0) ⊔
        fixingSubgroup H (Γ.neighborSet y)) ∧
    oddOrderClosure (W.kernelAt 0) ≤
      MulAction.stabilizer H y ⊓ MulAction.stabilizer H u ⊓ MulAction.stabilizer H z := by
  have hgood_torus : socTorus H Γ y z u ≤
      L₅.stab ⊔ fixingSubgroup H (Γ.neighborSet y) := by
    have hgood := (L₅.good (-6) 9 (L₅.window (-6) 9) (fun j hj => by
      rw [ClosedGoodPath.window_apply L₅ (-6) hj])).2 7 (by norm_num) (by norm_num)
    have hstab : GPath.stabPath (H := H) (L₅.window (-6) 9) = L₅.stab := by
      rw [ClosedGoodPath.stabPath_window (H := H) (by norm_num : 3 ≤ 8) hQ.weissFree
        hQ.localFacts L₅ (-6)]
    rw [hstab] at hgood
    have h7 : L₅.window (-6) 9 7 = y := by
      rw [ClosedGoodPath.window_apply L₅ (-6) (by norm_num : (7 : ℕ) ≤ 9)]
      rw [show (-6 : ℤ) + ((7 : ℕ) : ℤ) = 1 by norm_num, hL₅1]
    have h6 : L₅.window (-6) 9 6 = z := by
      rw [ClosedGoodPath.window_apply L₅ (-6) (by norm_num : (6 : ℕ) ≤ 9)]
      rw [show (-6 : ℤ) + ((6 : ℕ) : ℤ) = 0 by norm_num, hL₅0]
    have h8 : L₅.window (-6) 9 8 = u := by
      rw [ClosedGoodPath.window_apply L₅ (-6) (by norm_num : (8 : ℕ) ≤ 9)]
      rw [show (-6 : ℤ) + ((8 : ℕ) : ℤ) = 2 by norm_num, hL₅2]
    rw [h7, h6, h8] at hgood
    exact le_trans hgood (sup_le_sup inf_le_left le_rfl)
  have hnormG : L₅.stab ≤
      Subgroup.normalizer (fixingSubgroup H (Γ.neighborSet y) : Set H) := by
    intro a ha
    refine stabilizer_le_normalizer_fixingSubgroup (H := H) (Γ := Γ) (z := y) ?_
    rw [MulAction.mem_stabilizer_iff, ← hL₅1]
    exact ClosedGoodPath.mem_stab_iff.mp ha 1
  have hnorm_torus : ∀ t ∈ socTorus H Γ y z u, ∀ m ∈ oddOrderClosure (W.kernelAt 0),
      t * m * t⁻¹ ∈ oddOrderClosure (W.kernelAt 0) ⊔
        fixingSubgroup H (Γ.neighborSet y) := by
    intro t ht m hm
    have ht' : t ∈ (↑(L₅.stab ⊔ fixingSubgroup H (Γ.neighborSet y)) : Set H) :=
      hgood_torus ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L₅.stab
      (fixingSubgroup H (Γ.neighborSet y)) hnormG] at ht'
    obtain ⟨a, ha, r, hr, har⟩ := ht'
    have ham : a * m * a⁻¹ ∈ oddOrderClosure (W.kernelAt 0) :=
      (Subgroup.mem_normalizer_iff.mp (hstab_norm_Ko ha) m).mp hm
    have hrm : m⁻¹ * r * m * r⁻¹ ∈ fixingSubgroup H (Γ.neighborSet y) := by
      rw [mem_fixingSubgroup_iff]
      intro v hv
      have hrv : r⁻¹ • v = v := by
        have h := (mem_fixingSubgroup_iff H).mp hr v hv
        calc r⁻¹ • v = r⁻¹ • (r • v) := by rw [h]
          _ = v := by simp
      have hmy : m • y = y := hKfixy m (oddOrderClosure_le _ hm)
      have hmv : Γ.Adj y (m • v) := by
        have h := (GraphAction.adj_smul m y v).mpr hv
        rwa [hmy] at h
      have hrmv : r • (m • v) = m • v := (mem_fixingSubgroup_iff H).mp hr (m • v) hmv
      calc (m⁻¹ * r * m * r⁻¹) • v = m⁻¹ • (r • (m • (r⁻¹ • v))) := by simp [mul_smul]
        _ = m⁻¹ • (r • (m • v)) := by rw [hrv]
        _ = m⁻¹ • (m • v) := by rw [hrmv]
        _ = v := by simp
    have haG : a * (m⁻¹ * r * m * r⁻¹) * a⁻¹ ∈
        fixingSubgroup H (Γ.neighborSet y) := by
      have hay : a • y = y := by
        rw [← hL₅1]
        exact ClosedGoodPath.mem_stab_iff.mp ha 1
      have hanorm := stabilizer_le_normalizer_fixingSubgroup (H := H) (Γ := Γ) (z := y)
        (MulAction.mem_stabilizer_iff.mpr hay)
      exact (Subgroup.mem_normalizer_iff.mp hanorm (m⁻¹ * r * m * r⁻¹)).mp hrm
    rw [← har]
    have heq : a * r * m * (a * r)⁻¹ =
        (a * m * a⁻¹) * (a * (m⁻¹ * r * m * r⁻¹) * a⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ham) (Subgroup.mem_sup_right haG)
  have hKo_stab_y : oddOrderClosure (W.kernelAt 0) ≤
      MulAction.stabilizer H y ⊓ MulAction.stabilizer H u := by
    refine le_inf ?_ ?_
    · intro k hk
      rw [MulAction.mem_stabilizer_iff]
      exact hKfixy k (oddOrderClosure_le _ hk)
    · intro k hk
      rw [MulAction.mem_stabilizer_iff]
      exact hKfixu k (oddOrderClosure_le _ hk)
  have hKo_stab_z : oddOrderClosure (W.kernelAt 0) ≤ MulAction.stabilizer H z := by
    intro k hk
    rw [MulAction.mem_stabilizer_iff]
    exact hzfix k hk
  exact ⟨hnorm_torus, le_inf hKo_stab_y hKo_stab_z⟩

private theorem off_path_notKG [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u y z : V} {L₅ : ClosedGoodPath H Γ}
    (hL₅0 : L₅.x 0 = z) (hL₅1 : L₅.x 1 = y) (hL₅2 : L₅.x 2 = u)
    (hKo_stab : oddOrderClosure (W.kernelAt 0) ≤ L₅.stab)
    (hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u)
    (hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y)
    (hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u)) :
    ¬ oddOrderClosure (W.kernelAt 0) ≤ fixingSubgroup H (Γ.neighborSet y) := by
  intro hKG
  let p2 : GPath Γ 8 := (L₅.window (-6) 8).rev
  have hp2_nb : p2.NoBack := (L₅.window_noBack (-6) 8).rev
  have hp2_apply : ∀ i, i ≤ 8 → p2 i = L₅.x (2 - (i : ℤ)) := by
    intro i hi
    show (L₅.window (-6) 8).rev i = L₅.x (2 - (i : ℤ))
    rw [GPath.rev_apply _ hi, ClosedGoodPath.window_apply L₅ (-6) (by omega)]
    congr 1
    omega
  have hp2_0 : p2 0 = u := by
    rw [hp2_apply 0 (by omega)]
    norm_num
    exact hL₅2
  have hp2_1 : p2 1 = y := by
    rw [hp2_apply 1 (by omega)]
    norm_num
    exact hL₅1
  have hbotKo : oddOrderClosure (W.kernelAt 0) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    refine Subgroup.mem_bot.mpr (hQ.weissFree p2 hp2_nb k ?_ ?_ ?_)
    · intro i hi
      rw [hp2_apply i hi]
      by_cases hi0 : i = 0
      · subst hi0
        have h2 : L₅.x (2 - ((0 : ℕ) : ℤ)) = u := by norm_num; exact hL₅2
        rw [h2]; exact hKfixu k (oddOrderClosure_le _ hk)
      · by_cases hi1 : i = 1
        · subst hi1
          have h2 : L₅.x (2 - ((1 : ℕ) : ℤ)) = y := by norm_num; exact hL₅1
          rw [h2]; exact hKfixy k (oddOrderClosure_le _ hk)
        · exact ClosedGoodPath.mem_stab_iff.mp (hKo_stab hk) (2 - (i : ℤ))
    · intro w hw
      rw [hp2_0] at hw
      exact (mem_fixingSubgroup_iff H).mp (hKu_fix (oddOrderClosure_le _ hk)) w hw
    · intro w hw
      rw [hp2_1] at hw
      exact (mem_fixingSubgroup_iff H).mp (hKG hk) w hw
  exact oddOrderClosure_ne_bot hQ.notTwo hbotKo

private theorem off_path_kernel_eq [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {W' : ClosedGoodPath H Γ} {u y z : V} {L₅ : ClosedGoodPath H Γ}
    {c : H}
    (hL₅0 : L₅.x 0 = z) (hL₅1 : L₅.x 1 = y) (hL₅2 : L₅.x 2 = u)
    (hL₅x : ∀ i : ℕ, i ≤ 9 → L₅.x (i : ℤ) = offPathSeq W' u y z i)
    (hW'K : W'.kernelAt 0 = W.kernelAt 0)
    (hK_norm_Ko : W.kernelAt 0 ≤ Subgroup.normalizer
      (oddOrderClosure (W.kernelAt 0) : Set H))
    (hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u))
    (hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u)
    (hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y)
    (hKfixW : ∀ k ∈ W.kernelAt 0, ∀ j : ℤ, k • W'.x j = W'.x j)
    (hzfix : ∀ m ∈ oddOrderClosure (W.kernelAt 0), m • z = z)
    (hzu : z ≠ u)
    (htwo : ∀ v : V, Γ.Adj y v →
      (∀ m ∈ oddOrderClosure (W.kernelAt 0), m • v = v) → v = u ∨ v = z)
    (hcardH5 : Nat.card ↥(L₅.kernelAt 2) = Nat.card ↥(W'.kernelAt 0))
    (hcL : ∀ i, c • W.x i = (L₅.shift 2).x i) :
    (∀ k ∈ W.kernelAt 0, k • z = z) ∧
      W.kernelAt 0 = L₅.kernelAt 2 ∧
      W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet z) ∧
      L₅.kernelAt 0 = W.kernelAt 0 := by
  have hzy : Γ.Adj y z := by
    have h := L₅.adj 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num] at h
    rw [hL₅0, hL₅1] at h
    exact h.symm
  have hfixZ : ∀ k ∈ W.kernelAt 0, k • z = z := by
    intro k hk
    have hkz_adj : Γ.Adj y (k • z) := by
      have h := (GraphAction.adj_smul k y z).mpr hzy
      rwa [hKfixy k hk] at h
    have hkz_fix : ∀ m ∈ oddOrderClosure (W.kernelAt 0), m • (k • z) = k • z := by
      intro m hm
      have hmem : k⁻¹ * m * k ∈ oddOrderClosure (W.kernelAt 0) := by
        simpa using conj_mem_oddOrderClosure (H := W.kernelAt 0)
          (Subgroup.le_normalizer (Subgroup.inv_mem _ hk)) hm
      calc m • (k • z) = k • ((k⁻¹ * m * k) • z) := by simp [mul_smul, mul_assoc]
        _ = k • z := by rw [hzfix _ hmem]
    have hkz_ne : k • z ≠ u := by
      intro heq
      have h1 : z = u := by
        have h := congrArg (fun w => k⁻¹ • w) heq
        have h' : z = k⁻¹ • u := by simpa using h
        have h2 : k⁻¹ • u = u := by
          calc k⁻¹ • u = k⁻¹ • (k • u) := by rw [hKfixu k hk]
            _ = u := by simp
        rwa [h2] at h'
      exact hzu h1
    rcases htwo (k • z) hkz_adj hkz_fix with h | h
    · exact absurd h hkz_ne
    · exact h
  have hKleH5 : W.kernelAt 0 ≤ L₅.kernelAt 2 := by
    refine le_inf ?_ ?_
    · rw [show L₅.x 2 = u from hL₅2]; exact hKu_fix
    · rw [← ClosedGoodPath.stabPath_window (H := H) (by norm_num : 3 ≤ 8) hQ.weissFree
        hQ.localFacts L₅ 0]
      intro k hk
      rw [GPath.mem_stabPath_iff]
      intro i hi
      rw [ClosedGoodPath.window_apply L₅ 0 hi]
      by_cases hi0 : i = 0
      · subst hi0
        have h0 : L₅.x (0 + ((0 : ℕ) : ℤ)) = z := by simpa using hL₅0
        rw [h0]; exact hfixZ k hk
      · by_cases hi1 : i = 1
        · subst hi1
          have h1 : L₅.x (0 + ((1 : ℕ) : ℤ)) = y := by simpa using hL₅1
          rw [h1]; exact hKfixy k hk
        · by_cases hi2 : i = 2
          · subst hi2
            have h2 : L₅.x (0 + ((2 : ℕ) : ℤ)) = u := by simpa using hL₅2
            rw [h2]; exact hKfixu k hk
          · have hL : L₅.x (0 + (i : ℤ)) = offPathSeq W' u y z i := by
              rw [show (0 : ℤ) + (i : ℤ) = ((i : ℕ) : ℤ) by simp, hL₅x i (by omega)]
            rw [hL]
            have hiz2 : offPathSeq W' u y z i = W'.x ((i : ℤ) - 2) := by
              simp [offPathSeq, hi0, hi1, hi2]
            rw [hiz2]
            exact hKfixW k hk _
  have hKeqH5 : W.kernelAt 0 = L₅.kernelAt 2 := by
    refine Subgroup.eq_of_le_of_card_ge hKleH5 ?_
    rw [hcardH5, hW'K]
  have hL₅shiftK : (L₅.shift 2).kernelAt 0 = W.kernelAt 0 := by
    rw [ClosedGoodPath.kernelAt_shift, hKeqH5]
  have hzK : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet z) := by
    rw [← hL₅shiftK]
    have h := (quarter_of_conj hQ hcL hL₅shiftK (-2)).mpr (by norm_num : (2 : ℤ) ∣ -2)
    rw [ClosedGoodPath.shift_x, show (-2 : ℤ) + 2 = 0 by norm_num, hL₅0] at h
    exact h
  have hL₅K0 : L₅.kernelAt 0 = W.kernelAt 0 := by
    have hle : (L₅.shift 2).kernelAt 0 ≤
        fixingSubgroup H (Γ.neighborSet ((L₅.shift 2).x (-2))) := by
      rw [ClosedGoodPath.shift_x, show (-2 : ℤ) + 2 = 0 by norm_num, hL₅0,
        hL₅shiftK]
      exact hzK
    have hle' : (L₅.shift 2).kernelAt 0 ≤
        fixingSubgroup H (Γ.neighborSet ((L₅.shift 2).x (2 * (-1)))) := by
      simpa [show 2 * (-1 : ℤ) = -2 by norm_num] using hle
    have h := ClosedGoodPath.kernelAt_eq_of_le (by norm_num : 3 ≤ 8) hQ.moufang
      hQ.weissFree hQ.ne hQ.localFacts hQ.loc (L₅.shift 2) (-1) hle'
    have hkernel : (L₅.shift 2).kernelAt (-2) = L₅.kernelAt 0 := by
      simp only [ClosedGoodPath.kernelAt, ClosedGoodPath.shift_x, ClosedGoodPath.stab_shift,
        show (-2 : ℤ) + 2 = 0 by norm_num]
    rw [show 2 * (-1 : ℤ) = -2 by norm_num, hkernel, ClosedGoodPath.kernelAt_shift] at h
    rw [h, hKeqH5]
  exact ⟨hfixZ, hKeqH5, hzK, hL₅K0⟩

private theorem inv_step_off_path [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} (hu : AuxInv W u) {W' : ClosedGoodPath H Γ}
    (hW'0 : W'.x 0 = u) (hW'K : W'.kernelAt 0 = W.kernelAt 0)
    {c : H} (hc : ∀ i, c • W.x i = W'.x i)
    {y : V} (hy : Γ.Adj u y) (hy1 : y ≠ W'.x 1) (hy2 : y ≠ W'.x (-1)) :
    ∃ z : V, Γ.Adj y z ∧ z ≠ u ∧
      W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet z) ∧ AuxInv W z ∧
      ∀ v : V, Γ.Adj y v → v ≠ u →
        W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet v) → v = z := by
  classical
  have hKu : W.kernelAt 0 ≤ W'.stab := by
    rw [← hW'K]; exact inf_le_right
  have hKu_fix : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet u) := by
    rw [← hW'0, ← hW'K]; exact inf_le_left
  have hKfixu : ∀ k ∈ W.kernelAt 0, k • u = u := by
    intro k hk
    rw [← hW'0]
    exact ClosedGoodPath.mem_stab_iff.mp (hKu hk) 0
  have hKfixy : ∀ k ∈ W.kernelAt 0, k • y = y := by
    intro k hk
    exact (mem_fixingSubgroup_iff H).mp (hKu_fix hk) y hy
  have hKfixW : ∀ k ∈ W.kernelAt 0, ∀ j : ℤ, k • W'.x j = W'.x j :=
    fun k hk => ClosedGoodPath.mem_stab_iff.mp (hKu hk)
  obtain ⟨-, -, hK_norm_Ko⟩ := off_path_odd hQ hW'0 hW'K
  have hKo_le_K : oddOrderClosure (W.kernelAt 0) ≤ W.kernelAt 0 := oddOrderClosure_le _
  obtain ⟨z, hzy, hzu, hzfix⟩ := off_path_fixed_point hQ hW'0 hW'K hy hy1
  obtain ⟨q, hq_nb, hqseq⟩ := off_path_path9 hW'0 hy hzy hzu hy1
  have hq0 : q 0 = z := by rw [hqseq 0 (by omega)]; simp [offPathSeq]
  have hq1 : q 1 = y := by rw [hqseq 1 (by omega)]; simp [offPathSeq]
  have hq2 : q 2 = u := by rw [hqseq 2 (by omega)]; simp [offPathSeq]
  obtain ⟨L₅, hL₅0, hL₅1, hL₅2, hL₅x, hKo_stab, hKo_H5⟩ :=
    off_path_L5 hQ hq_nb hq0 hq1 hq2 hqseq hzfix hKfixy hKfixu hKu_fix hKfixW
  obtain ⟨c₅, hc₅, hcardH5, -, -, -, -, hstab_norm_Ko⟩ :=
    off_path_conj (z := z) hQ hW'0 hW'K hL₅2 hKo_H5
  obtain ⟨hnorm_torus, hMle⟩ :=
    off_path_torus hQ hL₅0 hL₅1 hL₅2 hKo_stab hstab_norm_Ko hKfixu hKfixy hzfix
  have hnotKG := off_path_notKG hQ hL₅0 hL₅1 hL₅2 hKo_stab hKfixu hKfixy hKu_fix
  have htwo : ∀ v : V, Γ.Adj y v →
      (∀ m ∈ oddOrderClosure (W.kernelAt 0), m • v = v) → v = u ∨ v = z := by
    have hnorm_torus' : ∀ t ∈ socTorus H Γ y u z, ∀ m ∈ oddOrderClosure (W.kernelAt 0),
        t * m * t⁻¹ ∈ oddOrderClosure (W.kernelAt 0) ⊔
          fixingSubgroup H (Γ.neighborSet y) := by
      intro t ht m hm
      exact hnorm_torus t (by simpa [socTorus_comm] using ht) m hm
    rcases (hQ.zassenhaus y).dichotomy u z hy.symm hzy hzu.symm
      (oddOrderClosure (W.kernelAt 0)) hMle hnorm_torus' with h | h
    · exact absurd h hnotKG
    · exact h
  have hcL : ∀ i, (c₅⁻¹ * c) • W.x i = (L₅.shift 2).x i := by
    intro i
    rw [mul_smul, hc i]
    have h := congrArg (fun v => c₅⁻¹ • v) (hc₅ i)
    simpa using h.symm
  obtain ⟨-, -, hzK, hL₅K0⟩ :=
    off_path_kernel_eq hQ hL₅0 hL₅1 hL₅2 hL₅x hW'K hK_norm_Ko hKu_fix hKfixu hKfixy
      hKfixW hzfix hzu htwo hcardH5 hcL
  have hz_orbit : ∃ g : H, g • W.x 0 = z := by
    obtain ⟨h, -, hhz⟩ := hQ.loc y u z hy.symm hzy
    obtain ⟨g₀, hg₀⟩ := hu.1
    exact ⟨h * g₀, by rw [mul_smul, hg₀, hhz]⟩
  refine ⟨z, hzy, hzu, hzK, ⟨hz_orbit, ⟨L₅, hL₅0, hL₅K0⟩⟩, ?_⟩
  intro v hvy hvu hvK
  have hvfix : ∀ m ∈ oddOrderClosure (W.kernelAt 0), m • v = v := by
    intro m hm
    exact MulAction.mem_stabilizer_iff.mp
      ((hQ.localFacts v).kernel_le (hvK (hKo_le_K hm)))
  rcases htwo v hvy hvfix with h | h
  · exact absurd h hvu
  · exact h

private theorem inv_step [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} (hu : AuxInv W u) {y : V} (hy : Γ.Adj u y) :
    ∃ z : V, Γ.Adj y z ∧ z ≠ u ∧
      W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet z) ∧ AuxInv W z ∧
      ∀ v : V, Γ.Adj y v → v ≠ u →
        W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet v) → v = z := by
  have hu' : AuxInv W u := hu
  obtain ⟨⟨g₀, hg₀⟩, W', hW'0, hW'K⟩ := hu
  obtain ⟨c, hc⟩ := exists_conj_of_inv hQ hW'0 ⟨g₀, hg₀⟩
  by_cases h1 : y = W'.x 1
  · subst h1
    exact inv_step_of_on_path hQ hu' hW'0 hW'K hc (Or.inl rfl)
  · by_cases h2 : y = W'.x (-1)
    · subst h2
      exact inv_step_of_on_path hQ hu' hW'0 hW'K hc (Or.inr rfl)
    · exact inv_step_off_path hQ hu' hW'0 hW'K hc hy h1 h2

theorem auxInv_of_mem_auxComp [Finite V] [Finite H] {W : ClosedGoodPath H Γ}
    (hQ : W.QuarterHyp) {u : V} (hu : u ∈ auxComp Γ (W.kernelAt 0) (W.x 0)) :
    AuxInv W u := by
  have hreach : (auxGraph Γ (W.kernelAt 0)).Reachable (W.x 0) u :=
    SimpleGraph.ConnectedComponent.reachable_of_mem_supp
      ((auxGraph Γ (W.kernelAt 0)).connectedComponentMk (W.x 0))
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem hu
  obtain ⟨w⟩ := hreach
  have edge : ∀ {a b : V}, (auxGraph Γ (W.kernelAt 0)).Adj a b → AuxInv W a → AuxInv W b := by
    intro a b hab ha
    obtain ⟨y, hay, hby⟩ := exists_common_adj_of_dist_eq_two hab.2.2
    obtain ⟨z, -, -, -, hzInv, huniq⟩ := inv_step hQ ha hay
    have hba : b ≠ a := by
      intro hba
      subst hba
      have hdist := hab.2.2
      rw [SimpleGraph.dist_self] at hdist
      omega
    have hbz : b = z := huniq b hby.symm hba hab.2.1
    rw [hbz]
    exact hzInv
  have key : ∀ {a b : V}, (auxGraph Γ (W.kernelAt 0)).Walk a b → AuxInv W a → AuxInv W b := by
    intro a b w
    induction w with
    | nil => exact id
    | cons h p ih => exact fun ha => ih (edge h ha)
  exact key w (inv_base W)

theorem ClosedGoodPath.QuarterHyp.existsUnique_auxSet_adj [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) {u : V}
    (hu : u ∈ auxComp Γ (W.kernelAt 0) (W.x 0)) {w : V} (hw : Γ.Adj u w) :
    ∃! v : V, Γ.Adj w v ∧ v ≠ u ∧ v ∈ auxSet Γ (W.kernelAt 0) := by
  obtain ⟨z, hzw, hzu, hzK, -, huniq⟩ := inv_step hQ (auxInv_of_mem_auxComp hQ hu) hw
  exact ⟨z, ⟨hzw, hzu, hzK⟩, fun v hv => huniq v hv.1 hv.2.1 hv.2.2⟩

theorem ClosedGoodPath.QuarterHyp.kernel_eq_of_fix [Finite V] [Finite H]
    {W : ClosedGoodPath H Γ} (hQ : W.QuarterHyp) {u : V}
    (hu : u ∈ auxComp Γ (W.kernelAt 0) (W.x 0)) {p : GPath Γ 9} (hp : p.NoBack) (hp0 : p 0 = u)
    (hfix : ∀ j, j ≤ 9 → ∀ h ∈ W.kernelAt 0, h • p j = p j) :
    fixingSubgroup H (Γ.neighborSet u) ⊓ GPath.stabPath (H := H) p = W.kernelAt 0 := by
  obtain ⟨huOrbit, W', hW'0, hW'K⟩ := auxInv_of_mem_auxComp hQ hu
  obtain ⟨Wp, hWp⟩ := ClosedGoodPath.exists_of_noBack (by norm_num : 3 ≤ 8)
    hQ.moufang hQ.weissFree hQ.ne hQ.localFacts hp
  have hWp0 : Wp.x 0 = u := by
    change Wp.x ((0 : ℕ) : ℤ) = u
    rw [hWp 0 (by omega), hp0]
  have hstab : GPath.stabPath (H := H) p = Wp.stab := by
    rw [← ClosedGoodPath.stabPath_window (H := H) (by norm_num : 3 ≤ 8) hQ.weissFree
      hQ.localFacts Wp 0]
    congr 1
    apply GPath.ext'
    intro j hj
    rw [ClosedGoodPath.window_apply Wp 0 hj, ← hWp j hj]
    simp
  have hker : fixingSubgroup H (Γ.neighborSet u) ⊓ GPath.stabPath (H := H) p =
      Wp.kernelAt 0 := by
    rw [hstab, ← hWp0]
    rfl
  have hHle : W.kernelAt 0 ≤ Wp.kernelAt 0 := by
    rw [← hker]
    refine le_inf ?_ ?_
    · rw [← hW'0, ← hW'K]
      exact inf_le_left
    · intro h hh
      rw [GPath.mem_stabPath_iff]
      intro j hj
      exact hfix j hj h hh
  obtain ⟨c, hc⟩ := exists_conj_of_inv hQ hWp0 huOrbit
  have hcard : Nat.card ↥(Wp.kernelAt 0) = Nat.card ↥(W.kernelAt 0) := by
    rw [ClosedGoodPath.kernelAt_eq_map_conj W Wp hc 0,
      Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have heq : W.kernelAt 0 = Wp.kernelAt 0 :=
    Subgroup.eq_of_le_of_card_ge hHle (le_of_eq hcard)
  rw [hker, ← heq]

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.Lemma4Setup
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalTypes

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

private theorem smul_window_of_mem_pathRootGroup {n : ℕ} (hn : 3 ≤ n) (W : ClosedGoodPath H Γ)
    {a j : ℤ} {u : H} (hu : u ∈ pathRootGroup H Γ (W.window a n)) (haj : a ≤ j)
    (hjn : j ≤ a + n) : u • W.x j = W.x j := by
  have h0 : 0 ≤ j - a := by omega
  have hja : ((j - a).toNat : ℤ) = j - a := Int.toNat_of_nonneg h0
  have hi : (j - a).toNat ≤ n := by omega
  have h := smul_path_eq_self_of_mem_pathRootGroup hn hu (j - a).toNat hi
  rw [ClosedGoodPath.window_apply W a hi, show a + ((j - a).toNat : ℤ) = j by omega] at h
  exact h

private theorem mem_fixing_of_mem_pathRootGroup (W : ClosedGoodPath H Γ) {n : ℕ}
    {a j : ℤ} {u : H} (hu : u ∈ pathRootGroup H Γ (W.window a n)) (haj : a + 1 ≤ j)
    (hjn : j ≤ a + n - 1) : u ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
  have h0 : 0 ≤ j - a := by omega
  have hja : ((j - a).toNat : ℤ) = j - a := Int.toNat_of_nonneg h0
  have hi1 : 1 ≤ (j - a).toNat := by omega
  have hi2 : (j - a).toNat ≤ n - 1 := by omega
  have h := mem_pathRootGroup.mp hu (j - a).toNat hi1 hi2
  have hw : (W.window a n) (j - a).toNat = W.x j := by
    rw [ClosedGoodPath.window_apply W a (by omega)]
    congr 1
    omega
  rw [hw] at h
  refine (mem_fixingSubgroup_iff H).mpr fun z hz => h z ?_
  exact (SimpleGraph.mem_neighborSet Γ _ z).mp hz

private theorem conj_mem_fixingSubgroup {g x : H} {z : V}
    (hx : x ∈ fixingSubgroup H (Γ.neighborSet z)) :
    g * x * g⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (g • z)) := by
  rw [fixingSubgroup_neighborSet_smul (H := H) (Γ := Γ) g z]
  exact Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩

private theorem eq_left_or_right {d : ℕ} {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) {i : ℤ}
    (hi : ¬ (d : ℤ) ∣ i) {z : V} (hz : Γ.Adj (W.x i) z)
    (hfix : ∀ k ∈ W.kernelAt 0, k • z = z) :
    z = W.x (i - 1) ∨ z = W.x (i + 1) := by
  by_contra h
  push Not at h
  exact hi ((hd i).mp ⟨z, hz, h.1, h.2, hfix⟩)

private theorem not_dvd_coe_of_pos_of_lt {d : ℕ} {i : ℤ} (hi0 : 0 < i) (hid : i < (d : ℤ)) :
    ¬ (d : ℤ) ∣ i := by
  intro h
  have hle : (d : ℤ) ≤ i := Int.le_of_dvd hi0 h
  omega

private theorem not_dvd_coe_add_of_pos_of_lt {d : ℕ} {i : ℤ} (hi0 : 0 < i - (d : ℤ))
    (hid : i - (d : ℤ) < (d : ℤ)) : ¬ (d : ℤ) ∣ i := by
  intro h
  have h' : (d : ℤ) ∣ i - (d : ℤ) := by
    have hdvd := Int.dvd_sub h (dvd_refl (d : ℤ))
    simpa using hdvd
  exact not_dvd_coe_of_pos_of_lt hi0 hid h'

private theorem smul_add_one_of_mem_centralizer {d : ℕ} {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) {c : H}
    (hc : c ∈ Subgroup.centralizer (W.kernelAt 0 : Set H)) {i : ℤ} (hdi : ¬ (d : ℤ) ∣ i)
    (hi : c • W.x i = W.x i) (him : c • W.x (i - 1) = W.x (i - 1)) :
    c • W.x (i + 1) = W.x (i + 1) := by
  have hfix : ∀ k ∈ W.kernelAt 0, k • (c • W.x (i + 1)) = c • W.x (i + 1) := by
    intro k hk
    have hcomm : k * c = c * k := (Subgroup.mem_centralizer_iff.mp hc) k hk
    have hkfix : k • W.x (i + 1) = W.x (i + 1) :=
      (ClosedGoodPath.mem_stab_iff.mp (Subgroup.mem_inf.mp hk).2) (i + 1)
    rw [← mul_smul, hcomm, mul_smul, hkfix]
  have hadj : Γ.Adj (W.x i) (c • W.x (i + 1)) := by
    have h := (GraphAction.adj_smul (Γ := Γ) c (W.x i) (W.x (i + 1))).mpr (W.adj i)
    rwa [hi] at h
  rcases eq_left_or_right hd hdi hadj hfix with h | h
  · exfalso
    have hne : W.x (i + 1) ≠ W.x (i - 1) := by
      have h := W.ne_add_two (i - 1)
      rw [show i - 1 + 2 = i + 1 by ring] at h
      exact h.symm
    have heq : W.x (i + 1) = W.x (i - 1) := by
      have h2 : c • W.x (i + 1) = c • W.x (i - 1) := by rw [h, him]
      simpa using congrArg (fun v => c⁻¹ • v) h2
    exact hne heq
  · exact h

private theorem smul_sub_one_of_mem_centralizer {d : ℕ} {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) {c : H}
    (hc : c ∈ Subgroup.centralizer (W.kernelAt 0 : Set H)) {i : ℤ} (hdi : ¬ (d : ℤ) ∣ i)
    (hi : c • W.x i = W.x i) (hip : c • W.x (i + 1) = W.x (i + 1)) :
    c • W.x (i - 1) = W.x (i - 1) := by
  have hfix : ∀ k ∈ W.kernelAt 0, k • (c • W.x (i - 1)) = c • W.x (i - 1) := by
    intro k hk
    have hcomm : k * c = c * k := (Subgroup.mem_centralizer_iff.mp hc) k hk
    have hkfix : k • W.x (i - 1) = W.x (i - 1) :=
      (ClosedGoodPath.mem_stab_iff.mp (Subgroup.mem_inf.mp hk).2) (i - 1)
    rw [← mul_smul, hcomm, mul_smul, hkfix]
  have hadj : Γ.Adj (W.x i) (c • W.x (i - 1)) := by
    have h := W.adj (i - 1)
    rw [show i - 1 + 1 = i by ring] at h
    have h2 := (GraphAction.adj_smul (Γ := Γ) c (W.x i) (W.x (i - 1))).mpr h.symm
    rwa [hi] at h2
  rcases eq_left_or_right hd hdi hadj hfix with h | h
  · exact h
  · exfalso
    have hne : W.x (i - 1) ≠ W.x (i + 1) := by
      have h := W.ne_add_two (i - 1)
      rw [show i - 1 + 2 = i + 1 by ring] at h
      exact h
    have heq : W.x (i - 1) = W.x (i + 1) := by
      have h2 : c • W.x (i - 1) = c • W.x (i + 1) := by rw [h, hip]
      simpa using congrArg (fun v => c⁻¹ • v) h2
    exact hne heq

private theorem smul_range_of_mem_centralizer {d : ℕ} (hd2 : 2 ≤ d) {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) {c : H}
    (hc : c ∈ Subgroup.centralizer (W.kernelAt 0 : Set H))
    (hfixd : c • W.x (d : ℤ) = W.x (d : ℤ))
    (hfixdm : c • W.x ((d : ℤ) - 1) = W.x ((d : ℤ) - 1))
    (hfixdp : c • W.x ((d : ℤ) + 1) = W.x ((d : ℤ) + 1)) :
    ∀ j : ℤ, 0 ≤ j → j ≤ 2 * (d : ℤ) → c • W.x j = W.x j := by
  have hup : ∀ j : ℤ, (d : ℤ) + 1 ≤ j → j ≤ 2 * (d : ℤ) →
      c • W.x j = W.x j ∧ c • W.x (j - 1) = W.x (j - 1) := by
    intro j hj1 hj2
    revert hj2
    refine Int.le_induction (m := (d : ℤ) + 1)
      (motive := fun n _ => n ≤ 2 * (d : ℤ) → c • W.x n = W.x n ∧
        c • W.x (n - 1) = W.x (n - 1)) ?_ ?_ j hj1
    · intro _
      exact ⟨hfixdp, by rwa [show (d : ℤ) + 1 - 1 = (d : ℤ) by ring]⟩
    · intro n hn ih hn2
      obtain ⟨hx, hxm⟩ := ih (by omega)
      have hnd : ¬ (d : ℤ) ∣ n :=
        not_dvd_coe_add_of_pos_of_lt (i := n) (by omega) (by omega)
      have h := smul_add_one_of_mem_centralizer hd hc hnd hx hxm
      exact ⟨h, by rwa [show n + 1 - 1 = n by ring]⟩
  have hdown : ∀ j : ℤ, 0 ≤ j → j ≤ (d : ℤ) - 1 →
      c • W.x j = W.x j ∧ c • W.x (j + 1) = W.x (j + 1) := by
    intro j hj0 hjd
    revert hj0
    refine Int.le_induction_down (m := (d : ℤ) - 1)
      (motive := fun n _ => 0 ≤ n → c • W.x n = W.x n ∧
        c • W.x (n + 1) = W.x (n + 1)) ?_ ?_ j (by omega)
    · intro _
      exact ⟨hfixdm, by rwa [show (d : ℤ) - 1 + 1 = (d : ℤ) by ring]⟩
    · intro n hn ih hn0
      obtain ⟨hx, hxp⟩ := ih (by omega)
      have hnd : ¬ (d : ℤ) ∣ n := not_dvd_coe_of_pos_of_lt (by omega) (by omega)
      have h := smul_sub_one_of_mem_centralizer hd hc hnd hx hxp
      exact ⟨h, by rwa [show n - 1 + 1 = n by ring]⟩
  intro j hj0 hj2
  rcases (show j = (d : ℤ) ∨ j < (d : ℤ) ∨ (d : ℤ) < j by omega) with h | h | h
  · rw [h]
    exact hfixd
  · exact (hdown j hj0 (by omega)).1
  · exact (hup j (by omega) hj2).1

private theorem commute_window_neg {n d : ℕ} (hn : 3 ≤ n) (hnd : n = 2 * d)
    (hW : WeissFree H Γ n) {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) (hd2 : 2 ≤ d) {u w : H}
    (hu : u ∈ pathRootGroup H Γ (W.window (-(d : ℤ)) n))
    (hw : w ∈ pathRootGroup H Γ (W.window 0 n))
    (hcu : u ∈ Subgroup.centralizer (W.kernelAt 0 : Set H))
    (hcw : w ∈ Subgroup.centralizer (W.kernelAt 0 : Set H)) : u * w = w * u := by
  classical
  have hnc : (n : ℤ) = 2 * (d : ℤ) := by rw [hnd]; push_cast; ring
  set c : H := u * w * u⁻¹ * w⁻¹ with hc_def
  have hcC : c ∈ Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    rw [hc_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hcu hcw) (Subgroup.inv_mem _ hcu)) (Subgroup.inv_mem _ hcw)
  have hu_fix : ∀ j : ℤ, -(d : ℤ) + 1 ≤ j → j ≤ (d : ℤ) - 1 →
      u ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j h1 h2
    exact mem_fixing_of_mem_pathRootGroup W hu h1 (by omega)
  have hu_smul : ∀ j : ℤ, -(d : ℤ) ≤ j → j ≤ (d : ℤ) → u • W.x j = W.x j := by
    intro j h1 h2
    exact smul_window_of_mem_pathRootGroup hn W hu h1 (by omega)
  have hw_fix : ∀ j : ℤ, (1 : ℤ) ≤ j → j ≤ 2 * (d : ℤ) - 1 →
      w ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j h1 h2
    exact mem_fixing_of_mem_pathRootGroup W hw (by omega) (by omega)
  have hw_smul : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ 2 * (d : ℤ) → w • W.x j = W.x j := by
    intro j h1 h2
    exact smul_window_of_mem_pathRootGroup hn W hw (by omega) (by omega)
  have hstep1 : ∀ j : ℤ, (1 : ℤ) ≤ j → j ≤ (d : ℤ) →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hj1 hjd
    have hwu : w ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := hw_fix j hj1 (by omega)
    have hconj : u * w * u⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (u • W.x j)) :=
      conj_mem_fixingSubgroup hwu
    rw [hu_smul j (by omega) hjd] at hconj
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hwu)
  have hstep2 : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ (d : ℤ) - 1 →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hj0 hjdm
    have hui : u⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) :=
      Subgroup.inv_mem _ (hu_fix j (by omega) (by omega))
    have hconj : w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (w • W.x j)) :=
      conj_mem_fixingSubgroup hui
    rw [hw_smul j hj0 (by omega)] at hconj
    have hu' : u ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := hu_fix j (by omega) (by omega)
    have hEq : u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) := by group
    rw [hEq]
    exact Subgroup.mul_mem _ hu' hconj
  have hG1 : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ (d : ℤ) →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hj0 hjd
    rcases (show j = 0 ∨ 1 ≤ j by omega) with h | h
    · rw [h]
      exact hstep2 0 le_rfl (by omega)
    · exact hstep1 j h hjd
  have hpath : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ (d : ℤ) →
      (u * w * u⁻¹ * w⁻¹) • W.x j = W.x j := by
    intro j hj0 hjd
    have hu' : u • W.x j = W.x j := hu_smul j (by omega) hjd
    have hw' : w • W.x j = W.x j := hw_smul j hj0 (by omega)
    have hui : u⁻¹ • W.x j = W.x j := by
      calc u⁻¹ • W.x j = u⁻¹ • (u • W.x j) := by rw [hu']
        _ = W.x j := inv_smul_smul u (W.x j)
    have hwi : w⁻¹ • W.x j = W.x j := by
      calc w⁻¹ • W.x j = w⁻¹ • (w • W.x j) := by rw [hw']
        _ = W.x j := inv_smul_smul w (W.x j)
    have hmul : ∀ a b : H, a • W.x j = W.x j → b • W.x j = W.x j →
        (a * b) • W.x j = W.x j := by
      intro a b ha hb
      rw [mul_smul, hb, ha]
    exact hmul _ _ (hmul _ _ (hmul _ _ hu' hw') hui) hwi
  have hfixd : c • W.x (d : ℤ) = W.x (d : ℤ) := hpath (d : ℤ) (by omega) le_rfl
  have hfixdm : c • W.x ((d : ℤ) - 1) = W.x ((d : ℤ) - 1) := by
    have hmem := hG1 (d : ℤ) (by omega) le_rfl
    refine (mem_fixingSubgroup_iff H).mp hmem (W.x ((d : ℤ) - 1)) ?_
    have h := (W.adj ((d : ℤ) - 1)).symm
    rwa [show (d : ℤ) - 1 + 1 = (d : ℤ) by ring] at h
  have hfixdp : c • W.x ((d : ℤ) + 1) = W.x ((d : ℤ) + 1) := by
    have hmem := hG1 (d : ℤ) (by omega) le_rfl
    refine (mem_fixingSubgroup_iff H).mp hmem (W.x ((d : ℤ) + 1)) ?_
    exact W.adj (d : ℤ)
  have hcr := smul_range_of_mem_centralizer hd2 hd hcC hfixd hfixdm hfixdp
  have hweiss : c = 1 := by
    refine hW (W.window 0 n) (W.window_noBack 0 n) c ?_ ?_ ?_
    · intro i hi
      rw [ClosedGoodPath.window_apply W 0 hi]
      have hi2 : (i : ℤ) ≤ 2 * (d : ℤ) := by
        have h : (i : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi
        rwa [hnc] at h
      simpa using hcr (i : ℤ) (by omega) hi2
    · intro z hz
      rw [ClosedGoodPath.window_apply W 0 (Nat.zero_le n)] at hz
      exact (mem_fixingSubgroup_iff H).mp (hG1 0 (by omega) (by omega)) z hz
    · intro z hz
      rw [ClosedGoodPath.window_apply W 0 (by omega : 1 ≤ n)] at hz
      exact (mem_fixingSubgroup_iff H).mp (hG1 1 (by omega) (by omega)) z hz
  have h1 : u * w * u⁻¹ = w := by
    have h := congrArg (fun x => x * w) hweiss
    simpa [hc_def, mul_assoc] using h
  calc u * w = (u * w * u⁻¹) * u := by group
    _ = w * u := by rw [h1]

private theorem commute_window_pos {n d : ℕ} (hn : 3 ≤ n) (hnd : n = 2 * d)
    (hW : WeissFree H Γ n) {W : ClosedGoodPath H Γ}
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i) (hd2 : 2 ≤ d) {u w : H}
    (hu : u ∈ pathRootGroup H Γ (W.window (d : ℤ) n))
    (hw : w ∈ pathRootGroup H Γ (W.window 0 n))
    (hcu : u ∈ Subgroup.centralizer (W.kernelAt 0 : Set H))
    (hcw : w ∈ Subgroup.centralizer (W.kernelAt 0 : Set H)) : u * w = w * u := by
  classical
  have hnc : (n : ℤ) = 2 * (d : ℤ) := by rw [hnd]; push_cast; ring
  set c : H := u * w * u⁻¹ * w⁻¹ with hc_def
  have hcC : c ∈ Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    rw [hc_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hcu hcw) (Subgroup.inv_mem _ hcu)) (Subgroup.inv_mem _ hcw)
  have hu_fix : ∀ j : ℤ, (d : ℤ) + 1 ≤ j → j ≤ 3 * (d : ℤ) - 1 →
      u ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j h1 h2
    exact mem_fixing_of_mem_pathRootGroup W hu (by omega) (by omega)
  have hu_smul : ∀ j : ℤ, (d : ℤ) ≤ j → j ≤ 3 * (d : ℤ) → u • W.x j = W.x j := by
    intro j h1 h2
    exact smul_window_of_mem_pathRootGroup hn W hu (by omega) (by omega)
  have hw_fix : ∀ j : ℤ, (1 : ℤ) ≤ j → j ≤ 2 * (d : ℤ) - 1 →
      w ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j h1 h2
    exact mem_fixing_of_mem_pathRootGroup W hw (by omega) (by omega)
  have hw_smul : ∀ j : ℤ, (0 : ℤ) ≤ j → j ≤ 2 * (d : ℤ) → w • W.x j = W.x j := by
    intro j h1 h2
    exact smul_window_of_mem_pathRootGroup hn W hw (by omega) (by omega)
  have hstep1 : ∀ j : ℤ, (d : ℤ) ≤ j → j ≤ 2 * (d : ℤ) - 1 →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hjd hj2
    have hwu : w ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := hw_fix j (by omega) hj2
    have hconj : u * w * u⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (u • W.x j)) :=
      conj_mem_fixingSubgroup hwu
    rw [hu_smul j hjd (by omega)] at hconj
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hwu)
  have hstep2 : ∀ j : ℤ, (d : ℤ) + 1 ≤ j → j ≤ 2 * (d : ℤ) →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hj1 hj2
    have hui : u⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) :=
      Subgroup.inv_mem _ (hu_fix j hj1 (by omega))
    have hconj : w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (w • W.x j)) :=
      conj_mem_fixingSubgroup hui
    rw [hw_smul j (by omega) hj2] at hconj
    have hu' : u ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := hu_fix j hj1 (by omega)
    have hEq : u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) := by group
    rw [hEq]
    exact Subgroup.mul_mem _ hu' hconj
  have hG1 : ∀ j : ℤ, (d : ℤ) ≤ j → j ≤ 2 * (d : ℤ) →
      u * w * u⁻¹ * w⁻¹ ∈ fixingSubgroup H (Γ.neighborSet (W.x j)) := by
    intro j hjd hj2
    rcases (show j ≤ 2 * (d : ℤ) - 1 ∨ j = 2 * (d : ℤ) by omega) with h | h
    · exact hstep1 j hjd h
    · rw [h]
      exact hstep2 _ (by omega) le_rfl
  have hpath : ∀ j : ℤ, (d : ℤ) ≤ j → j ≤ 2 * (d : ℤ) →
      (u * w * u⁻¹ * w⁻¹) • W.x j = W.x j := by
    intro j hjd hj2
    have hu' : u • W.x j = W.x j := hu_smul j hjd (by omega)
    have hw' : w • W.x j = W.x j := hw_smul j (by omega) hj2
    have hui : u⁻¹ • W.x j = W.x j := by
      calc u⁻¹ • W.x j = u⁻¹ • (u • W.x j) := by rw [hu']
        _ = W.x j := inv_smul_smul u (W.x j)
    have hwi : w⁻¹ • W.x j = W.x j := by
      calc w⁻¹ • W.x j = w⁻¹ • (w • W.x j) := by rw [hw']
        _ = W.x j := inv_smul_smul w (W.x j)
    have hmul : ∀ a b : H, a • W.x j = W.x j → b • W.x j = W.x j →
        (a * b) • W.x j = W.x j := by
      intro a b ha hb
      rw [mul_smul, hb, ha]
    exact hmul _ _ (hmul _ _ (hmul _ _ hu' hw') hui) hwi
  have hfixd : c • W.x (d : ℤ) = W.x (d : ℤ) := hpath (d : ℤ) le_rfl (by omega)
  have hfixdm : c • W.x ((d : ℤ) - 1) = W.x ((d : ℤ) - 1) := by
    have hmem := hG1 (d : ℤ) le_rfl (by omega)
    refine (mem_fixingSubgroup_iff H).mp hmem (W.x ((d : ℤ) - 1)) ?_
    have h := (W.adj ((d : ℤ) - 1)).symm
    rwa [show (d : ℤ) - 1 + 1 = (d : ℤ) by ring] at h
  have hfixdp : c • W.x ((d : ℤ) + 1) = W.x ((d : ℤ) + 1) := by
    have hmem := hG1 (d : ℤ) le_rfl (by omega)
    refine (mem_fixingSubgroup_iff H).mp hmem (W.x ((d : ℤ) + 1)) ?_
    exact W.adj (d : ℤ)
  have hcr := smul_range_of_mem_centralizer hd2 hd hcC hfixd hfixdm hfixdp
  have hweiss : c = 1 := by
    refine hW (W.window 0 n).rev (W.window_noBack 0 n).rev c ?_ ?_ ?_
    · intro i hi
      rw [GPath.rev_apply _ hi, ClosedGoodPath.window_apply W 0 (by omega)]
      exact hcr _ (by omega) (by omega)
    · intro z hz
      have hz' : Γ.Adj (W.x (2 * (d : ℤ))) z := by
        rw [GPath.rev_apply (p := W.window 0 n) (i := 0) (by omega), show n - 0 = n by omega,
          ClosedGoodPath.window_apply W 0 (le_refl n)] at hz
        rwa [show (0 : ℤ) + (n : ℤ) = 2 * (d : ℤ) from by rw [hnc]; ring] at hz
      exact (mem_fixingSubgroup_iff H).mp (hG1 (2 * (d : ℤ)) (by omega) le_rfl) z hz'
    · intro z hz
      have hz' : Γ.Adj (W.x (2 * (d : ℤ) - 1)) z := by
        rw [GPath.rev_apply (p := W.window 0 n) (i := 1) (by omega),
          ClosedGoodPath.window_apply W 0 (by omega)] at hz
        rwa [show ((n - 1 : ℕ) : ℤ) = 2 * (d : ℤ) - 1 from by
          rw [Nat.cast_sub (by omega : 1 ≤ n), hnc]; norm_num,
          show (0 : ℤ) + (2 * (d : ℤ) - 1) = 2 * (d : ℤ) - 1 from by ring] at hz
      exact (mem_fixingSubgroup_iff H).mp (hG1 (2 * (d : ℤ) - 1) (by omega) (by omega)) z hz'
  have h1 : u * w * u⁻¹ = w := by
    have h := congrArg (fun x => x * w) hweiss
    simpa [hc_def, mul_assoc] using h
  calc u * w = (u * w * u⁻¹) * u := by group
    _ = w * u := by rw [h1]

theorem ClosedGoodPath.false_of_half [Finite H] {n d : ℕ} (hn : 3 ≤ n) (hnd : n = 2 * d)
    (hM : MoufangCondition H Γ n) (hW : WeissFree H Γ n)
    (h3 : ∀ v w w' : V, Γ.Adj v w → Γ.Adj v w' → ∃ u, Γ.Adj v u ∧ u ≠ w ∧ u ≠ w')
    (hL : ∀ z, LocalFacts H Γ z) (hR : ∀ z, RootFacts H Γ n z) (W : ClosedGoodPath H Γ)
    (hd : ∀ i : ℤ, W.HasThirdFix (W.kernelAt 0) i ↔ (d : ℤ) ∣ i)
    (hfull : W.kernelAt 0 ≤ fixingSubgroup H (Γ.neighborSet (W.x d))) :
    False := by
  classical
  have hd2 : 2 ≤ d := by omega
  have hPle : pathRootGroup H Γ (W.window (-(d : ℤ)) n) ≤
      Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    intro u hu'
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := n) (by omega) hW
      (p := (W.window (-(d : ℤ)) n).rev) (W.window_noBack (-(d : ℤ)) n).rev ?_ ?_
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hp0 : (W.window (-(d : ℤ)) n).rev 0 = W.x (d : ℤ) := by
          rw [GPath.rev_apply (p := W.window (-(d : ℤ)) n) (i := 0) (by omega),
            show n - 0 = n by omega, ClosedGoodPath.window_apply W (-(d : ℤ)) le_rfl]
          rw [show -(d : ℤ) + (n : ℤ) = (d : ℤ) by omega]
        rw [hp0]
        exact hfull hm
      · rw [GPath.stabPath_rev]
        exact W.stab_le_stabPath_window (-(d : ℤ)) n (Subgroup.mem_inf.mp hm).2
    · rwa [pathRootGroup_rev_eq]
  have hP'le : pathRootGroup H Γ (W.window (d : ℤ) n) ≤
      Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    intro u hu'
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := n) (by omega) hW
      (W.window_noBack (d : ℤ) n) ?_ hu'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hp0 : W.window (d : ℤ) n 0 = W.x (d : ℤ) := by
        rw [ClosedGoodPath.window_apply W (d : ℤ) (Nat.zero_le n)]
        simp
      rw [hp0]
      exact hfull hm
    · exact W.stab_le_stabPath_window (d : ℤ) n (Subgroup.mem_inf.mp hm).2
  have hQle : pathRootGroup H Γ (W.window 0 n) ≤
      Subgroup.centralizer (W.kernelAt 0 : Set H) := by
    intro w hw'
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    refine commute_of_mem_fixingSubgroup_inf_stabPath (n := n) (by omega) hW
      (W.window_noBack 0 n) ?_ hw'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hp0 : W.window 0 n 0 = W.x 0 := by
        rw [ClosedGoodPath.window_apply W 0 (Nat.zero_le n)]
        simp
      rw [hp0]
      exact (Subgroup.mem_inf.mp hm).1
    · exact W.stab_le_stabPath_window 0 n (Subgroup.mem_inf.mp hm).2
  have hq_n : (W.window (-(d : ℤ)) n) n = W.x (d : ℤ) := by
    rw [ClosedGoodPath.window_apply W (-(d : ℤ)) le_rfl]
    congr 1
    omega
  have hq_dm : (W.window (-(d : ℤ)) n) (n - 1) = W.x ((d : ℤ) - 1) := by
    rw [ClosedGoodPath.window_apply W (-(d : ℤ)) (by omega)]
    congr 1
    omega
  have hq'_n : (W.window (d : ℤ) n).rev n = W.x (d : ℤ) := by
    rw [GPath.rev_apply (p := W.window (d : ℤ) n) (i := n) le_rfl, show n - n = 0 by omega,
      ClosedGoodPath.window_apply W (d : ℤ) (Nat.zero_le n)]
    simp
  have hq'_dp : (W.window (d : ℤ) n).rev (n - 1) = W.x ((d : ℤ) + 1) := by
    rw [GPath.rev_apply (p := W.window (d : ℤ) n) (i := n - 1) (by omega),
      show n - (n - 1) = 1 by omega, ClosedGoodPath.window_apply W (d : ℤ) (by omega)]
    norm_num
  obtain ⟨b, hbU, hb_dm, hb_dp, hbodd, hb_notG1⟩ :=
    RootFacts.exists_odd_torus (H := H) (Γ := Γ) (n := n) hn (hR (W.x (d : ℤ)))
      (hL (W.x (d : ℤ))) (fun w w' h1 h2 => h3 (W.x (d : ℤ)) w w' h1 h2)
      (W.window_noBack (-(d : ℤ)) n) (W.window_noBack (d : ℤ) n).rev
      hq_n hq'_n (by
        rw [hq_dm, hq'_dp]
        have h := W.ne_add_two ((d : ℤ) - 1)
        rwa [show (d : ℤ) - 1 + 2 = (d : ℤ) + 1 by ring] at h)
  have hbU' : b ∈ pathRootGroup H Γ (W.window (-(d : ℤ)) n) ⊔
      pathRootGroup H Γ (W.window (d : ℤ) n) := by
    rwa [pathRootGroup_rev_eq] at hbU
  have hbC : b ∈ Subgroup.centralizer (W.kernelAt 0 : Set H) :=
    (sup_le hPle hP'le) hbU'
  have hb_xd : b • W.x (d : ℤ) = W.x (d : ℤ) := by
    have hPstab : pathRootGroup H Γ (W.window (-(d : ℤ)) n) ≤
        MulAction.stabilizer H (W.x (d : ℤ)) := by
      intro u hu'
      rw [MulAction.mem_stabilizer_iff]
      exact smul_window_of_mem_pathRootGroup hn W hu' (by omega) (by omega)
    have hP'stab : pathRootGroup H Γ (W.window (d : ℤ) n) ≤
        MulAction.stabilizer H (W.x (d : ℤ)) := by
      intro u hu'
      rw [MulAction.mem_stabilizer_iff]
      exact smul_window_of_mem_pathRootGroup hn W hu' (by omega) (by omega)
    exact MulAction.mem_stabilizer_iff.mp ((sup_le hPstab hP'stab) hbU')
  have hb_range : ∀ j : ℤ, 0 ≤ j → j ≤ 2 * (d : ℤ) → b • W.x j = W.x j := by
    refine smul_range_of_mem_centralizer hd2 hd hbC hb_xd ?_ ?_
    · rw [← hq_dm]
      exact hb_dm
    · rw [← hq'_dp]
      exact hb_dp
  obtain ⟨y, hy_adj, hy_ne, hy_fix⟩ := (hL (W.x 0)).oddFix (W.x 1) (W.adj 0)
    (Subgroup.zpowers b) (by
      refine le_inf ?_ ?_
      · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hb_range 0 (by norm_num) (by omega)
      · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hb_range 1 (by norm_num) (by omega)) (by
      refine Odd.of_dvd_nat ?_ (Subgroup.relIndex_dvd_card _ _)
      rwa [Nat.card_zpowers])
  have hby : b • y = y := hy_fix b (Subgroup.mem_zpowers b)
  have hQtrans : ∀ y y' : V, Γ.Adj (W.x 0) y → Γ.Adj (W.x 0) y' → y ≠ W.x 1 →
      y' ≠ W.x 1 → ∃ q ∈ pathRootGroup H Γ (W.window 0 n), q • y = y' := by
    intro y' z hy' hz hy'1 hz1
    have hp_end : (W.window 0 n).rev n = W.x 0 := by
      rw [GPath.rev_apply (p := W.window 0 n) (i := n) le_rfl, show n - n = 0 by omega,
        ClosedGoodPath.window_apply W 0 (Nat.zero_le n)]
      simp
    have hp_pen : (W.window 0 n).rev (n - 1) = W.x 1 := by
      rw [GPath.rev_apply (p := W.window 0 n) (i := n - 1) (by omega),
        show n - (n - 1) = 1 by omega, ClosedGoodPath.window_apply W 0 (by omega)]
      norm_num
    obtain ⟨⟨q, hq⟩, hqy⟩ := (pathRootGroup_regular_of_weissFree hn hM hW
      (p := (W.window 0 n).rev) (W.window_noBack 0 n).rev (y := y') (y' := z)
      (by rw [hp_end]; exact hy') (by rw [hp_end]; exact hz) (by rw [hp_pen]; exact hy'1)
      (by rw [hp_pen]; exact hz1)).exists
    exact ⟨q, by rwa [pathRootGroup_rev_eq] at hq, hqy⟩
  have hP_Q : pathRootGroup H Γ (W.window (-(d : ℤ)) n) ≤
      Subgroup.centralizer (pathRootGroup H Γ (W.window 0 n) : Set H) := by
    intro u hu'
    rw [Subgroup.mem_centralizer_iff]
    intro q hq'
    exact (commute_window_neg hn hnd hW hd hd2 hu' hq' (hPle hu') (hQle hq')).symm
  have hP'_Q : pathRootGroup H Γ (W.window (d : ℤ) n) ≤
      Subgroup.centralizer (pathRootGroup H Γ (W.window 0 n) : Set H) := by
    intro u hu'
    rw [Subgroup.mem_centralizer_iff]
    intro q hq'
    exact (commute_window_pos hn hnd hW hd hd2 hu' hq' (hP'le hu') (hQle hq')).symm
  have hbQ : b ∈ Subgroup.centralizer (pathRootGroup H Γ (W.window 0 n) : Set H) :=
    (sup_le hP_Q hP'_Q) hbU'
  have hbG10 : b ∈ fixingSubgroup H (Γ.neighborSet (W.x 0)) := by
    rw [mem_fixingSubgroup_iff]
    intro z hz
    by_cases hz1 : z = W.x 1
    · rw [hz1]
      exact hb_range 1 (by norm_num) (by omega)
    · obtain ⟨q, hqQ, hqy⟩ := hQtrans y z hy_adj hz hy_ne hz1
      have hqb : q * b = b * q := (Subgroup.mem_centralizer_iff.mp hbQ) q hqQ
      calc b • z = b • (q • y) := by rw [hqy]
        _ = (b * q) • y := by rw [mul_smul]
        _ = (q * b) • y := by rw [hqb]
        _ = q • (b • y) := by rw [mul_smul]
        _ = q • y := by rw [hby]
        _ = z := hqy
  have hb_stab : b ∈ W.stab := by
    rw [← ClosedGoodPath.stabPath_window (n := n) hn hW hL W (-1)]
    rw [GPath.mem_stabPath_iff]
    intro i hi
    rw [ClosedGoodPath.window_apply W (-1) hi]
    rcases (show -1 + (i : ℤ) = -1 ∨ 0 ≤ -1 + (i : ℤ) by omega) with h | h
    · rw [h]
      exact (mem_fixingSubgroup_iff H).mp hbG10 (W.x (-1)) (by
        simpa using (W.adj (-1)).symm)
    · exact hb_range (-1 + (i : ℤ)) h (by omega)
  exact hb_notG1 (hfull (Subgroup.mem_inf.mpr ⟨hbG10, hb_stab⟩))

end CFSG.Quasithin.Stroth.WeissDelta

end

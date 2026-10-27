module

public import CFSG.Timmesfeld.Transvection.AssembleGen

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H]

theorem exists_conjSub_eq_of_lineOf {Δ : Set (Subgroup H)} {A D M U V : Subgroup H}
    (hU : U ≤ M) (hV : V ≤ M) (hUt : ∀ C ∈ lineOf Δ A D, C ≠ D → ∃ x ∈ U, conjSub A x = C)
    (hVt : ∀ C ∈ lineOf Δ A D, C ≠ A → ∃ y ∈ V, conjSub D y = C) {B : Subgroup H}
    (hB : B ∈ lineOf Δ A D) (hBA : B ≠ A) (hBD : B ≠ D) {W : Subgroup H}
    (hW : W ∈ lineOf Δ A D) : ∃ g ∈ M, conjSub A g = W := by
  by_cases hWD : W = D
  · obtain ⟨x, hx, hxB⟩ := hUt B hB hBD
    obtain ⟨y, hy, hyB⟩ := hVt B hB hBA
    refine ⟨y⁻¹ * x, mul_mem (inv_mem (hV hy)) (hU hx), ?_⟩
    rw [conjSub_mul, hxB, ← hyB, Aux.conjSub_conjSub_inv, hWD]
  · obtain ⟨x, hx, hxW⟩ := hUt W hW hWD
    exact ⟨x, hU hx, hxW⟩

theorem exists_conjSub_eq_of_lineOf_of_thickLines {Δ : Set (Subgroup H)} (hthick : ThickLines Δ)
    {A D M U V : Subgroup H} (hA : A ∈ Δ) (hD : D ∈ Δ) (hAD : A ≠ D) (hc : Commuting A D)
    (hU : U ≤ M) (hV : V ≤ M) (hUt : ∀ C ∈ lineOf Δ A D, C ≠ D → ∃ x ∈ U, conjSub A x = C)
    (hVt : ∀ C ∈ lineOf Δ A D, C ≠ A → ∃ y ∈ V, conjSub D y = C) {W : Subgroup H}
    (hW : W ∈ lineOf Δ A D) : ∃ g ∈ M, conjSub A g = W := by
  obtain ⟨B, hB, hBA, hBD⟩ := thickLines_iff.1 hthick A hA D hD hAD hc
  exact exists_conjSub_eq_of_lineOf hU hV hUt hVt hB hBA hBD hW

variable [Finite H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}

private theorem exists_conjSub_eq_of_mem_perpSet_step (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hfr : IsFrame Δ P Q)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (hfix : ∀ j, j < r → ∀ i : Fin r, i.val < j → ∀ g ∈ M j,
      conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r), ∀ W ∈ lineOf Δ (P ⟨j, by omega⟩) (P ⟨j + 1, hj⟩),
      ∃ g ∈ M j, conjSub (P ⟨j, by omega⟩) g = W)
    {d : ℕ} (ih : ∀ (j : ℕ), j + d + 1 = r → ∀ (hj : j < r),
      ∀ X ∈ perpSet Δ P Q j, ∃ m ∈ M j, conjSub (P ⟨j, hj⟩) m = X)
    {j : ℕ} (hjd : j + (d + 1) + 1 = r) (hj : j < r) {X : Subgroup H}
    (hX : X ∈ perpSet Δ P Q j) : ∃ m ∈ M j, conjSub (P ⟨j, hj⟩) m = X := by
  have hPm := hfr.memP
  have hQm := hfr.memQ
  have hcomm : ∀ i i' : Fin r, i ≠ i' → Commuting (P i) (P i') ∧ Commuting (P i) (Q i') ∧
      Commuting (Q i) (P i') ∧ Commuting (Q i) (Q i') := fun i i' h => by
    have hc := hfr.commuting i i' h
    exact ⟨hc.mono le_sup_left le_sup_left, hc.mono le_sup_left le_sup_right,
      hc.mono le_sup_right le_sup_left, hc.mono le_sup_right le_sup_right⟩
  have hopp : ∀ i, ¬ Commuting (P i) (Q i) := fun i =>
    (hfr.opposite i).not_commuting (hΔ.root.ne_bot _ (hPm i))
  have hj1 : j + 1 < r := by omega
  have hab : (⟨j, hj⟩ : Fin r) ≠ ⟨j + 1, hj1⟩ := fun h => by simp [Fin.ext_iff] at h
  have hPab : Commuting (P ⟨j, hj⟩) (P ⟨j + 1, hj1⟩) := (hcomm _ _ hab).1
  have hPab' : P ⟨j, hj⟩ ≠ P ⟨j + 1, hj1⟩ := fun h =>
    hopp ⟨j, hj⟩ (by rw [h]; exact (hcomm _ _ hab.symm).2.1)
  obtain ⟨W, hWl, hXW⟩ := hml _ (hPm _) _ (hPm _) hPab' hPab X hX.1
  obtain ⟨g, hg, rfl⟩ := htrans j hj1 W hWl
  have hX'Δ : conjSub X g⁻¹ ∈ Δ := hΔ.root.conjSub_mem hX.1 g⁻¹
  have hX'perp : conjSub X g⁻¹ ∈ perpSet Δ P Q j := by
    refine ⟨hX'Δ, fun i hi => ⟨?_, ?_⟩⟩
    · have := (hX.2 i hi).1.conjSub g⁻¹
      rwa [(hfix j hj i hi _ (inv_mem hg)).1] at this
    · have := (hX.2 i hi).2.conjSub g⁻¹
      rwa [(hfix j hj i hi _ (inv_mem hg)).2] at this
  have hX'P : Commuting (conjSub X g⁻¹) (P ⟨j, hj⟩) := by
    have := hXW.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  suffices h' : ∃ m ∈ M j, conjSub (P ⟨j, hj⟩) m = conjSub X g⁻¹ by
    obtain ⟨m, hm, hmX⟩ := h'
    refine ⟨g * m, mul_mem hg hm, ?_⟩
    rw [conjSub_mul, hmX, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  by_cases hX'a : conjSub X g⁻¹ = P ⟨j, hj⟩
  · exact ⟨1, one_mem _, by rw [conjSub_one, hX'a]⟩
  obtain ⟨W', hW'l, hQW'⟩ := hml _ (hPm _) _ hX'Δ (Ne.symm hX'a) hX'P.symm _ (hQm ⟨j, hj⟩)
  have hW'a : W' ≠ P ⟨j, hj⟩ := fun h => hopp ⟨j, hj⟩ (h ▸ hQW'.symm)
  have hW'perp : W' ∈ perpSet Δ P Q (j + 1) := by
    refine ⟨hW'l.1, fun i hi => ?_⟩
    by_cases hij : i.val < j
    · have hia : i ≠ ⟨j, hj⟩ := Fin.ne_of_val_ne (by simp only; omega)
      exact ⟨(hW'l.2 (P i) (hPm i) (hcomm _ _ hia).1 (hX'perp.2 i hij).1.symm).symm,
        (hW'l.2 (Q i) (hQm i) (hcomm _ _ hia).2.2.1 (hX'perp.2 i hij).2.symm).symm⟩
    · obtain rfl : i = ⟨j, hj⟩ := Fin.ext (by simp only; omega)
      exact ⟨(commuting_of_mem_lineOf' hΔ (hPm _) hX'Δ hX'P.symm hW'l).1.symm, hQW'.symm⟩
  obtain ⟨m', hm', rfl⟩ := ih (j + 1) (by omega) hj1 W' hW'perp
  have hPa : conjSub (P ⟨j, hj⟩) m'⁻¹ = P ⟨j, hj⟩ := by
    conv_lhs => rw [← (hfix (j + 1) hj1 ⟨j, hj⟩ (by simp only; omega) m' hm').1]
    exact Aux.conjSub_conjSub_inv _ _
  have hline := lineOf_eq_of_mem_of_ne hΔ hpts (hPm _) hX'Δ (Ne.symm hX'a) hX'P.symm hW'l hW'a
  have hX'l : conjSub X g⁻¹ ∈ lineOf Δ (P ⟨j, hj⟩) (conjSub (P ⟨j + 1, hj1⟩) m') := by
    rw [hline]
    exact right_mem_lineOf hX'Δ
  have hX''l := conjSub_mem_lineOf hΔ.root hX'l m'⁻¹
  rw [hPa, Aux.conjSub_conjSub_inv] at hX''l
  obtain ⟨g', hg', hg'X⟩ := htrans j hj1 _ hX''l
  refine ⟨m' * g', mul_mem (hmono j hj1 hm') hg', ?_⟩
  rw [conjSub_mul, hg'X, ← conjSub_mul, mul_inv_cancel, conjSub_one]

private theorem exists_conjSub_eq_of_mem_perpSet_of_base (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hr : 1 ≤ r) (hfr : IsFrame Δ P Q)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (hfix : ∀ j, j < r → ∀ i : Fin r, i.val < j → ∀ g ∈ M j,
      conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r), ∀ W ∈ lineOf Δ (P ⟨j, by omega⟩) (P ⟨j + 1, hj⟩),
      ∃ g ∈ M j, conjSub (P ⟨j, by omega⟩) g = W)
    (hbase : ∀ X ∈ perpSet Δ P Q (r - 1),
      ∃ g ∈ M (r - 1), conjSub (P ⟨r - 1, by omega⟩) g = X)
    (hlast : P ⟨r - 1, by omega⟩ ≤ M (r - 1)) {j : ℕ} (hj : j < r)
    {X : Subgroup H} (hX : X ∈ perpSet Δ P Q j) : ∃ m ∈ M j, conjSub (P ⟨j, hj⟩) m = X := by
  suffices key : ∀ d j, j + d + 1 = r → ∀ (hj : j < r), ∀ X ∈ perpSet Δ P Q j,
      ∃ m ∈ M j, conjSub (P ⟨j, hj⟩) m = X from key (r - 1 - j) j (by omega) hj X hX
  intro d
  induction d with
  | zero =>
    intro j hjd hj X hX
    obtain rfl : j = r - 1 := by omega
    exact hbase X hX
  | succ d ih =>
    intro j hjd hj X hX
    exact exists_conjSub_eq_of_mem_perpSet_step hΔ hpts hml hfr hmono hfix htrans ih hjd hj hX

private theorem exists_conjSub_eq_of_mem_perpSet_last (hΔ : IsTransvectionClass Δ) (hr : 1 ≤ r)
    (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩) {M : ℕ → Subgroup H}
    (hlast : P ⟨r - 1, by omega⟩ ⊔ Q ⟨r - 1, by omega⟩ ≤ M (r - 1))
    {X : Subgroup H} (hX : X ∈ perpSet Δ P Q (r - 1)) :
    ∃ g ∈ M (r - 1), conjSub (P ⟨r - 1, by omega⟩) g = X := by
  have hle : X ≤ P ⟨r - 1, by omega⟩ ⊔ Q ⟨r - 1, by omega⟩ :=
    hfr.residue X hX.1 fun i hik => hX.2 i (by
      have : i.val ≠ r - 1 := fun h => hik (Fin.ext h)
      omega)
  obtain ⟨x, hx, rfl⟩ :=
    exists_conjSub_eq_of_le hΔ.root hX.1 (hfr.memP _) (hfr.opposite _) hle
  exact ⟨x, hlast hx, rfl⟩

omit [Finite H] in
private theorem le_of_forall_lineOf_of_base (hr : 1 ≤ r) (hfr : IsFrame Δ P Q)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r), ∀ W ∈ lineOf Δ (P ⟨j, by omega⟩) (P ⟨j + 1, hj⟩),
      ∃ g ∈ M j, conjSub (P ⟨j, by omega⟩) g = W)
    (hlast : P ⟨r - 1, by omega⟩ ≤ M (r - 1)) {j : ℕ} (hj : j < r) :
    P ⟨j, hj⟩ ≤ M j := by
  suffices key : ∀ d j (hj : j < r), j + d + 1 = r → P ⟨j, hj⟩ ≤ M j from
    key (r - 1 - j) j hj (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj hjd
    obtain rfl : j = r - 1 := by omega
    exact hlast
  | succ d ih =>
    intro j hj hjd
    have hj1 : j + 1 < r := by omega
    obtain ⟨g, hg, hgP⟩ := htrans j hj1 _ (right_mem_lineOf (hfr.memP _))
    have h1 := conjSub_le ((ih (j + 1) hj1 (by omega)).trans (hmono j hj1)) (inv_mem hg)
    rwa [← hgP, Aux.conjSub_conjSub_inv] at h1

private theorem le_of_mem_of_forall_lineOf_of_base (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hr : 1 ≤ r) (hfr : IsFrame Δ P Q)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (hfix : ∀ j, j < r → ∀ i : Fin r, i.val < j → ∀ g ∈ M j,
      conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r), ∀ W ∈ lineOf Δ (P ⟨j, by omega⟩) (P ⟨j + 1, hj⟩),
      ∃ g ∈ M j, conjSub (P ⟨j, by omega⟩) g = W)
    (hbase : ∀ X ∈ perpSet Δ P Q (r - 1),
      ∃ g ∈ M (r - 1), conjSub (P ⟨r - 1, by omega⟩) g = X)
    (hlast : P ⟨r - 1, by omega⟩ ≤ M (r - 1)) {X : Subgroup H} (hX : X ∈ Δ) : X ≤ M 0 := by
  obtain ⟨m, hm, rfl⟩ := exists_conjSub_eq_of_mem_perpSet_of_base hΔ hpts hml hr hfr hmono hfix
    htrans hbase hlast (j := 0) (by omega) ⟨hX, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  exact conjSub_le (le_of_forall_lineOf_of_base hr hfr hmono htrans hlast (by omega)) hm

theorem eq_top_of_forall_lineOf_of_base (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hr : 1 ≤ r) (hfr : IsFrame Δ P Q)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (hfix : ∀ j, j < r → ∀ i : Fin r, i.val < j → ∀ g ∈ M j,
      conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r),
      ∀ W ∈ lineOf Δ (P ⟨j, Nat.lt_of_succ_lt hj⟩) (P ⟨j + 1, hj⟩),
        ∃ g ∈ M j, conjSub (P ⟨j, Nat.lt_of_succ_lt hj⟩) g = W)
    (hbase : ∀ X ∈ perpSet Δ P Q (r - 1),
      ∃ g ∈ M (r - 1), conjSub (P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩) g = X)
    (hlast : P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ ≤ M (r - 1)) : M 0 = ⊤ := by
  rw [eq_top_iff, ← hΔ.root.gen]
  exact iSup₂_le fun X hX =>
    le_of_mem_of_forall_lineOf_of_base hΔ hpts hml hr hfr hmono hfix htrans hbase hlast hX

theorem eq_top_of_forall_lineOf (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hml : MeetsLines Δ) (hr : 1 ≤ r) (hfr : IsSmallFrame Δ P Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩)
    {M : ℕ → Subgroup H} (hmono : ∀ j, j + 1 < r → M (j + 1) ≤ M j)
    (hfix : ∀ j, j < r → ∀ i : Fin r, i.val < j → ∀ g ∈ M j,
      conjSub (P i) g = P i ∧ conjSub (Q i) g = Q i)
    (htrans : ∀ (j : ℕ) (hj : j + 1 < r),
      ∀ W ∈ lineOf Δ (P ⟨j, Nat.lt_of_succ_lt hj⟩) (P ⟨j + 1, hj⟩),
        ∃ g ∈ M j, conjSub (P ⟨j, Nat.lt_of_succ_lt hj⟩) g = W)
    (hlast : P ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ ⊔ Q ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ ≤
      M (r - 1)) : M 0 = ⊤ :=
  eq_top_of_forall_lineOf_of_base hΔ hpts hml hr hfr.toIsFrame hmono hfix htrans
    (fun _ hX => exists_conjSub_eq_of_mem_perpSet_last hΔ hr hfr hlast hX)
    (le_sup_left.trans hlast)

end CFSG.Timmesfeld.Transvection

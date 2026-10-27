module

public import CFSG.Timmesfeld.Transvection.Frame
public import CFSG.Timmesfeld.Transvection.LineSpan

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H]

@[expose] def deltaIn (Δ : Set (Subgroup H)) (M : Subgroup H) : Set (Subgroup H) :=
  {X | X ∈ Δ ∧ X ≤ M}

@[expose] def perpSet (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) (j : ℕ) :
    Set (Subgroup H) :=
  {X | X ∈ Δ ∧ ∀ i : Fin r, i.val < j → Commuting X (P i) ∧ Commuting X (Q i)}

theorem conjSub_mem_lineOf {Δ : Set (Subgroup H)} (hΔ : IsRootClass Δ) {A B D : Subgroup H}
    (hD : D ∈ lineOf Δ A B) (g : H) : conjSub D g ∈ lineOf Δ (conjSub A g) (conjSub B g) := by
  refine ⟨hΔ.conjSub_mem hD.1 g, fun Y hY hYA hYB => ?_⟩
  have hY' : conjSub (conjSub Y g⁻¹) g = Y := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  have h1 : Commuting (conjSub Y g⁻¹) A := by
    have := hYA.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h2 : Commuting (conjSub Y g⁻¹) B := by
    have := hYB.conjSub g⁻¹
    rwa [Aux.conjSub_conjSub_inv] at this
  have h3 := (hD.2 _ (hΔ.conjSub_mem hY g⁻¹) h1 h2).conjSub g
  rwa [hY'] at h3

variable [Finite H]

theorem eq_top_of_isSmallFrame {Δ : Set (Subgroup H)} (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) {r : ℕ} (hr : 1 ≤ r)
    {P Q : Fin r → Subgroup H} (hfr : IsSmallFrame Δ P Q ⟨r - 1, by omega⟩) {M : Subgroup H}
    (ha : ∀ i, P i ≤ M ∧ Q i ≤ M)
    (hb : ∀ (j : ℕ) (hj : j + 1 < r),
      lineOf Δ (P ⟨j, by omega⟩) (P ⟨j + 1, hj⟩) ⊆ deltaIn Δ M)
    (hc : ∀ j : ℕ, j < r → ∀ W ∈ deltaIn Δ M ∩ perpSet Δ P Q j,
      ∀ W' ∈ deltaIn Δ M ∩ perpSet Δ P Q j, ∃ m ∈ M,
        (∀ i : Fin r, i.val < j → conjSub (P i) m = P i ∧ conjSub (Q i) m = Q i) ∧
          conjSub W m = W') :
    M = ⊤ := by
  have hPm := hfr.memP
  have hQm := hfr.memQ
  have hcomm : ∀ i i' : Fin r, i ≠ i' → Commuting (P i) (P i') ∧ Commuting (P i) (Q i') ∧
      Commuting (Q i) (P i') ∧ Commuting (Q i) (Q i') := fun i i' h => by
    have hc := hfr.commuting i i' h
    exact ⟨hc.mono le_sup_left le_sup_left, hc.mono le_sup_left le_sup_right,
      hc.mono le_sup_right le_sup_left, hc.mono le_sup_right le_sup_right⟩
  have hopp : ∀ i, ¬ Commuting (P i) (Q i) := fun i h => by
    obtain ⟨hne, h1, -⟩ := hfr.opposite i
    obtain ⟨a, ha, ha1⟩ := hΔ.root.exists_ne_one (hPm i)
    obtain ⟨b, hb, -, e⟩ := h1 a ha ha1
    rw [conjSub_of_forall_commute (fun x hx => (h x hx b hb).symm),
      conjSub_of_forall_commute (fun y hy => h a ha y hy)] at e
    exact hne e
  have hPperp : ∀ (j : ℕ) (i : Fin r), j ≤ i.val → P i ∈ perpSet Δ P Q j := fun j i hji =>
    ⟨hPm i, fun i' hi' => ⟨(hcomm i i' (fun h => by rw [h] at hji; omega)).1,
      (hcomm i i' (fun h => by rw [h] at hji; omega)).2.1⟩⟩
  have key : ∀ d j : ℕ, j + d + 1 = r → perpSet Δ P Q j ⊆ deltaIn Δ M := by
    intro d
    induction d with
    | zero =>
      intro j hj X hX
      refine ⟨hX.1, ?_⟩
      refine (hfr.residue X hX.1 fun i hik => hX.2 i ?_).trans (sup_le (ha _).1 (ha _).2)
      have : i.val ≠ r - 1 := fun h => hik (Fin.ext h)
      omega
    | succ d ih =>
      intro j hj X hX
      have hj1 : j + 1 < r := by omega
      have ihj := ih (j + 1) (by omega)
      have hab : (⟨j, by omega⟩ : Fin r) ≠ ⟨j + 1, hj1⟩ := fun h => by simp [Fin.ext_iff] at h
      have hPab : Commuting (P ⟨j, by omega⟩) (P ⟨j + 1, hj1⟩) := (hcomm _ _ hab).1
      have hPab' : P ⟨j, by omega⟩ ≠ P ⟨j + 1, hj1⟩ := fun h =>
        hopp ⟨j, by omega⟩ (by rw [h]; exact (hcomm _ _ hab.symm).2.1)
      obtain ⟨W, hWl, hXW⟩ := hml _ (hPm _) _ (hPm _) hPab' hPab X hX.1
      have hWperp : W ∈ perpSet Δ P Q j := by
        refine ⟨hWl.1, fun i hi => ⟨?_, ?_⟩⟩
        · have hia : i ≠ ⟨j, by omega⟩ := Fin.ne_of_val_ne (by simp only; omega)
          have hib : i ≠ ⟨j + 1, hj1⟩ := Fin.ne_of_val_ne (by simp only; omega)
          exact (hWl.2 (P i) (hPm i) (hcomm _ _ hia).1 (hcomm _ _ hib).1).symm
        · have hia : i ≠ ⟨j, by omega⟩ := Fin.ne_of_val_ne (by simp only; omega)
          have hib : i ≠ ⟨j + 1, hj1⟩ := Fin.ne_of_val_ne (by simp only; omega)
          exact (hWl.2 (Q i) (hQm i) (hcomm _ _ hia).2.2.1 (hcomm _ _ hib).2.2.1).symm
      obtain ⟨m, hm, hmfix, hWm⟩ := hc j (by omega) W ⟨hb j hj1 hWl, hWperp⟩ _
        ⟨⟨hPm _, (ha _).1⟩, hPperp j ⟨j, by omega⟩ le_rfl⟩
      have hX'Δ : conjSub X m ∈ Δ := hΔ.root.conjSub_mem hX.1 m
      have hX'perp : conjSub X m ∈ perpSet Δ P Q j := by
        refine ⟨hX'Δ, fun i hi => ⟨?_, ?_⟩⟩
        · have := (hX.2 i hi).1.conjSub m
          rwa [(hmfix i hi).1] at this
        · have := (hX.2 i hi).2.conjSub m
          rwa [(hmfix i hi).2] at this
      have hX'P : Commuting (conjSub X m) (P ⟨j, by omega⟩) := by
        have := hXW.conjSub m
        rwa [hWm] at this
      suffices hX'M : conjSub X m ≤ M by
        refine ⟨hX.1, ?_⟩
        have := conjSub_le hX'M (M.inv_mem hm)
        rwa [Aux.conjSub_conjSub_inv] at this
      by_cases hX'a : conjSub X m = P ⟨j, by omega⟩
      · rw [hX'a]
        exact (ha _).1
      obtain ⟨W', hW'l, hQW'⟩ := hml _ (hPm _) _ hX'Δ (Ne.symm hX'a) hX'P.symm _ (hQm ⟨j, by omega⟩)
      have hW'a : W' ≠ P ⟨j, by omega⟩ := fun h => hopp ⟨j, by omega⟩ (by
        rw [← h]
        exact hQW'.symm)
      have hW'perp : W' ∈ perpSet Δ P Q (j + 1) := by
        refine ⟨hW'l.1, fun i hi => ?_⟩
        by_cases hij : i.val < j
        · have hia : i ≠ ⟨j, by omega⟩ := Fin.ne_of_val_ne (by simp only; omega)
          exact ⟨(hW'l.2 (P i) (hPm i) (hcomm _ _ hia).1 (hX'perp.2 i hij).1.symm).symm,
            (hW'l.2 (Q i) (hQm i) (hcomm _ _ hia).2.2.1 (hX'perp.2 i hij).2.symm).symm⟩
        · have hia : i = ⟨j, by omega⟩ := Fin.ext (by simp only; omega)
          rw [hia]
          exact ⟨(commuting_of_mem_lineOf' hΔ (hPm _) hX'Δ hX'P.symm hW'l).1.symm, hQW'.symm⟩
      obtain ⟨m', hm', hm'fix, hW'm'⟩ := hc (j + 1) hj1 _
        ⟨⟨hPm _, (ha _).1⟩, hPperp (j + 1) ⟨j + 1, hj1⟩ le_rfl⟩ W' ⟨ihj hW'perp, hW'perp⟩
      have hPa : conjSub (P ⟨j, by omega⟩) m'⁻¹ = P ⟨j, by omega⟩ := by
        conv_lhs => rw [← (hm'fix ⟨j, by omega⟩ (by simp only; omega)).1]
        exact Aux.conjSub_conjSub_inv _ _
      have hPb : conjSub W' m'⁻¹ = P ⟨j + 1, hj1⟩ := by
        rw [← hW'm', Aux.conjSub_conjSub_inv]
      have hline := lineOf_eq_of_mem_of_ne hΔ hpts (hPm _) hX'Δ (Ne.symm hX'a) hX'P.symm hW'l hW'a
      have hX'l : conjSub X m ∈ lineOf Δ (P ⟨j, by omega⟩) W' := by
        rw [hline]
        exact right_mem_lineOf hX'Δ
      have hX''l := conjSub_mem_lineOf hΔ.root hX'l m'⁻¹
      rw [hPa, hPb] at hX''l
      have h2 := conjSub_le (hb j hj1 hX''l).2 hm'
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h2
  have hall := key (r - 1) 0 (by omega)
  rw [eq_top_iff, ← hΔ.root.gen]
  exact iSup₂_le fun A hA => (hall ⟨hA, fun i hi => absurd hi (Nat.not_lt_zero _)⟩).2

end CFSG.Timmesfeld.Transvection

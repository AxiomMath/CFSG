module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTable
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private local instance (priority := high) ltrv4d1_decEqLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltrv4d1_decEqOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private def ltrv4d1_id : List ℕ := [0, 1, 2, 3, 4, 5, 6]

private def ltrv4d1_sList : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 3], [0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 1],
   [0, 0, 1, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0, 2], [0, 2, 0, 0, 0, 0, 1], [1, 1, 0, 0, 0, 0, 1]]

private def ltrv4d1_stab (s : List ℕ) : List (List ℕ) :=
  (k0DiagOf (GGKacType.E6)).omega.filter (fun w => decide (k0pAct w s = s))

private structure Ltrv4d1Cand where
  d : ℕ
  s : List ℕ
  rho : List ℕ
  fam : LargeEvenLieTag
  rank : ℕ
  twv : ℕ
  k : ℕ
  deriving DecidableEq

private def ltrv4d1_candsOf (d : ℕ) : List Ltrv4d1Cand :=
  ltrv4d1_sList.flatMap (fun s =>
    (k0Reps (ltrv4d1_stab s) ltrv4d1_id).flatMap (fun rho =>
      (ggKacShShapes (k0DiagOf (GGKacType.E6)) s rho d).map (fun x =>
        ⟨d, s, rho, x.1, x.2.1, x.2.2.1, x.2.2.2⟩)))

private def ltrv4d1_cands : List Ltrv4d1Cand := ltrv4d1_candsOf 1 ++ ltrv4d1_candsOf 2

private def ltrv4d1_good (t : LargeEvenLieTag) (r : ℕ) (c : Ltrv4d1Cand) : Bool :=
  match t, r with
  | .D, 5 => decide (c.s = [0, 1, 0, 0, 0, 0, 2] ∨ c.s = [0, 2, 0, 0, 0, 0, 1]) &&
      decide (c.rho = ltrv4d1_id)
  | .twD, 5 => decide (c.s = [0, 1, 0, 0, 0, 0, 2] ∨ c.s = [0, 2, 0, 0, 0, 0, 1]) &&
      decide (c.rho = ltrv4d1_id)
  | .A, 5 => decide (c.s = [0, 0, 0, 0, 0, 1, 1]) && decide (c.rho = ltrv4d1_id)
  | .twA, 5 => decide (c.s = [0, 0, 0, 0, 0, 1, 1]) && decide (c.rho = ltrv4d1_id)
  | _, _ => false

private def ltrv4d1_check (n₀ : ℕ) (t : LargeEvenLieTag) (r : ℕ) : Bool :=
  ltrv4d1_cands.all (fun c =>
    if (k0LabelOf c.fam c.rank c.twv (c.k * n₀)).lab = ⟨t, r, n₀⟩ then
      ltrv4d1_good t r c
    else true)

private theorem ltrv4d1_check_1_D5 : ltrv4d1_check 1 .D 5 = true := by decide

private theorem ltrv4d1_check_2_D5 : ltrv4d1_check 2 .D 5 = true := by decide

private theorem ltrv4d1_check_1_twD5 : ltrv4d1_check 1 .twD 5 = true := by decide

private theorem ltrv4d1_check_2_twD5 : ltrv4d1_check 2 .twD 5 = true := by decide

private theorem ltrv4d1_check_1_A5 : ltrv4d1_check 1 .A 5 = true := by decide

private theorem ltrv4d1_check_2_A5 : ltrv4d1_check 2 .A 5 = true := by decide

private theorem ltrv4d1_check_1_twA5 : ltrv4d1_check 1 .twA 5 = true := by decide

private theorem ltrv4d1_check_2_twA5 : ltrv4d1_check 2 .twA 5 = true := by decide

private lemma ltrv4d1_mul_eq_self {k n : ℕ} (hn : 1 ≤ n) (h : k * n = n) : k = 1 := by
  have h' : k * n = 1 * n := by rw [one_mul]; exact h
  exact Nat.mul_right_cancel (by omega) h'

private lemma ltrv4d1_not_dvd_neg {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : ¬ 3 ∣ 2 ^ n - 1 := by
  intro h'
  have hsub : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h h'
  have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [heq] at hsub
  obtain ⟨c, hc⟩ := hsub
  omega

private lemma ltrv4d1_label_lab (fam : LargeEvenLieTag) (rank twv m : ℕ) (hm : m ≠ 1) :
    (k0LabelOf fam rank twv m).lab =
      ⟨(k0LabelOf fam rank twv 2).lab.tag, (k0LabelOf fam rank twv 2).lab.rank, m⟩ := by
  cases fam <;> simp only [k0LabelOf] <;> split_ifs <;> simp_all

private lemma ltrv4d1_label_transfer (fam : LargeEvenLieTag) (rank twv k n : ℕ) (hn : 2 ≤ n)
    (t : LargeEvenLieTag) (r : ℕ) :
    (k0LabelOf fam rank twv (k * n)).lab = ⟨t, r, n⟩ ↔
      (k0LabelOf fam rank twv (k * 2)).lab = ⟨t, r, 2⟩ := by
  have h2 : k * 2 ≠ 1 := by omega
  have hn1 : k * n ≠ 1 := by
    intro h
    have hdiv : n ∣ 1 := ⟨k, by rw [mul_comm]; exact h.symm⟩
    have hle : n ≤ 1 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  rw [ltrv4d1_label_lab fam rank twv (k * n) hn1,
    ltrv4d1_label_lab fam rank twv (k * 2) h2]
  constructor
  · intro h
    injection h with h1 h2' h3
    have hk : k = 1 := ltrv4d1_mul_eq_self (by omega) h3
    subst hk
    rw [h1, h2']
  · intro h
    injection h with h1 h2' h3
    have hk : k = 1 := by omega
    subst hk
    rw [h1, h2']
    rw [one_mul]

private lemma ltrv4d1_s_mem {s : List ℕ}
    (hmem : s ∈ k0VecsAux (k0DiagOf (GGKacType.E6)).marks 3)
    (hmin : k0OrbMin (k0DiagOf (GGKacType.E6)) s = s) : s ∈ ltrv4d1_sList := by
  have h : (k0VecsAux (k0DiagOf (GGKacType.E6)).marks 3).filter
      (fun s => decide (k0OrbMin (k0DiagOf (GGKacType.E6)) s = s)) = ltrv4d1_sList := by
    decide
  rw [← h]
  exact List.mem_filter.mpr ⟨hmem, by simpa using hmin⟩

private lemma ltrv4d1_base {s : List ℕ} (hs : s ∈ ltrv4d1_sList) {tw : Bool} {d : ℕ}
    (hd : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)) :
    k0KacBase (k0DiagOf (GGKacType.E6)) (k0Rho0 (k0DiagOf (GGKacType.E6)) tw d) s =
      some ltrv4d1_id := by
  simp only [ltrv4d1_sList, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private lemma ltrv4d1_extract1 {t : LargeEvenLieTag} {r n : ℕ} {c : Ltrv4d1Cand}
    (hn : n = 1) (hc : c ∈ ltrv4d1_cands)
    (hdesc : (k0LabelOf c.fam c.rank c.twv (c.k * n)).lab = ⟨t, r, n⟩)
    (hchk : ltrv4d1_check 1 t r = true) : ltrv4d1_good t r c = true := by
  subst hn
  have h := List.all_eq_true.mp hchk c hc
  rw [if_pos hdesc] at h
  exact h

private lemma ltrv4d1_extract2 {t : LargeEvenLieTag} {r n : ℕ} {c : Ltrv4d1Cand}
    (hn : 2 ≤ n) (hc : c ∈ ltrv4d1_cands)
    (hdesc : (k0LabelOf c.fam c.rank c.twv (c.k * n)).lab = ⟨t, r, n⟩)
    (hchk : ltrv4d1_check 2 t r = true) : ltrv4d1_good t r c = true := by
  have hdesc2 : (k0LabelOf c.fam c.rank c.twv (c.k * 2)).lab = ⟨t, r, 2⟩ :=
    (ltrv4d1_label_transfer c.fam c.rank c.twv c.k n hn t r).mp hdesc
  have h := List.all_eq_true.mp hchk c hc
  rw [if_pos hdesc2] at h
  exact h

private lemma ltrv4d1_good_of_row
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length)
    {t : LargeEvenLieTag} {r : ℕ}
    (hT : ρ.row.T = .E6)
    (htw : (ρ.row.tw = false ∧ ρ.row.d = 1) ∨ (ρ.row.tw = true ∧ ρ.row.d = 2))
    (hlabJ : ρ.row.D.orbits[j].lab = (⟨t, r, lab.n⟩ : LargeEvenLabel))
    (hΛ : 1 ≤ lab.n)
    (hchk1 : ltrv4d1_check 1 t r = true) (hchk2 : ltrv4d1_check 2 t r = true) :
    ltrv4d1_good t r (⟨ρ.row.d, ρ.row.s, ρ.row.rho, .A, 0, 0, 0⟩ : Ltrv4d1Cand) = true := by
  have hdiag : k0DiagOf ρ.row.T = k0DiagOf (GGKacType.E6) := by rw [hT]
  have hs_mem : ρ.row.s ∈ k0VecsAux (k0DiagOf (GGKacType.E6)).marks 3 := by
    have h := ρ.row.s_mem
    rw [hdiag] at h
    exact h
  have hs_min : k0OrbMin (k0DiagOf (GGKacType.E6)) ρ.row.s = ρ.row.s := by
    have h := ρ.row.s_min
    rw [hdiag] at h
    exact h
  have hs_list : ρ.row.s ∈ ltrv4d1_sList := ltrv4d1_s_mem hs_mem hs_min
  have hbase_id : ρ.row.base = ltrv4d1_id := by
    have hb := ρ.row.base_eq
    rw [hdiag] at hb
    have hb' := ltrv4d1_base hs_list htw
    rw [hb'] at hb
    exact (Option.some.inj hb).symm
  have hrho : ρ.row.rho ∈ k0Reps (ltrv4d1_stab ρ.row.s) ltrv4d1_id := by
    have h := ρ.row.rho_mem
    rw [hdiag] at h
    change ρ.row.rho ∈ k0Reps
      ((k0DiagOf (GGKacType.E6)).omega.filter
        (fun w => decide (k0pAct w ρ.row.s = ρ.row.s))) ρ.row.base at h
    rw [hbase_id] at h
    exact h
  have hD : ρ.row.D = k0Datum (k0DiagOf (GGKacType.E6)) ρ.row.s ρ.row.rho ρ.row.d lab.n
      (((k0DiagOf (GGKacType.E6)).omega.filter
        (fun w => decide (k0pAct w ρ.row.s = ρ.row.s))).length) := by
    have h := ρ.row.D_eq
    rw [hdiag] at h
    exact h
  have ho : ρ.row.D.orbits[j] ∈ (k0Datum (k0DiagOf (GGKacType.E6)) ρ.row.s ρ.row.rho
      ρ.row.d lab.n (((k0DiagOf (GGKacType.E6)).omega.filter
        (fun w => decide (k0pAct w ρ.row.s = ρ.row.s))).length)).orbits := by
    rw [← hD]
    exact List.get_mem _ _
  obtain ⟨x, hx, hxo⟩ := ggKacSh_orbit_mem_shapes ho
  have hdesc : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab =
      (⟨t, r, lab.n⟩ : LargeEvenLabel) := by
    rw [hxo] at hlabJ
    exact hlabJ
  have hcOf : (⟨ρ.row.d, ρ.row.s, ρ.row.rho, x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : Ltrv4d1Cand) ∈
      ltrv4d1_candsOf ρ.row.d := by
    simp only [ltrv4d1_candsOf, List.mem_flatMap, List.mem_map]
    exact ⟨ρ.row.s, hs_list, ρ.row.rho, hrho, x, hx, rfl⟩
  have hc : (⟨ρ.row.d, ρ.row.s, ρ.row.rho, x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : Ltrv4d1Cand) ∈
      ltrv4d1_cands := by
    rw [ltrv4d1_cands]
    rcases htw with ⟨-, hdb⟩ | ⟨-, hdb⟩
    · exact List.mem_append_left _ (hdb ▸ hcOf)
    · exact List.mem_append_right _ (hdb ▸ hcOf)
  have hgood : ltrv4d1_good t r
      (⟨ρ.row.d, ρ.row.s, ρ.row.rho, x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : Ltrv4d1Cand) = true := by
    rcases eq_or_lt_of_le hΛ with hn1 | hn2
    · exact ltrv4d1_extract1 (n := lab.n) hn1.symm hc hdesc hchk1
    · exact ltrv4d1_extract2 (n := lab.n) (by omega) hc hdesc hchk2
  exact hgood

theorem e6RowTableR1_holds : E6RowTableR1 := by
  intro Omega _ _ _ lab R _ I phi ρ j hΛ hsingle hqs hrow
  obtain ⟨lt, lr, ln⟩ := lab
  have hΛn : 1 ≤ ln := hΛ.1
  unfold GGE6ThreeR1Labels1585 at hrow
  dsimp only at hrow
  rcases hrow with ⟨htag, h3, hlabJ⟩ | ⟨htag, h3, hlabJ⟩
  · subst htag
    have hreq := ρ.row.type_eq
    simp only [ggKacTypeOfLabel, Option.some.injEq, Prod.mk.injEq] at hreq
    have hT : ρ.row.T = .E6 := hreq.1.symm
    have htwb : ρ.row.tw = false := hreq.2.symm
    have hd : ρ.row.d = 1 := by rw [ρ.row.d_eq, if_pos h3]
    have hgood := ltrv4d1_good_of_row ρ j hT (Or.inl ⟨htwb, hd⟩) hlabJ hΛn
      ltrv4d1_check_1_D5 ltrv4d1_check_2_D5
    simp only [ltrv4d1_good, Bool.and_eq_true, decide_eq_true_eq, ltrv4d1_id] at hgood
    refine ⟨hT, ?_⟩
    unfold E6RowDataR1
    exact ⟨hgood.1, of_decide_eq_true hgood.2⟩
  · subst htag
    have hreq := ρ.row.type_eq
    simp only [ggKacTypeOfLabel, Option.some.injEq, Prod.mk.injEq] at hreq
    have hT : ρ.row.T = .E6 := hreq.1.symm
    have htwb : ρ.row.tw = true := hreq.2.symm
    have hd : ρ.row.d = 2 := by
      rw [ρ.row.d_eq, if_neg (ltrv4d1_not_dvd_neg h3)]
    have hgood := ltrv4d1_good_of_row ρ j hT (Or.inr ⟨htwb, hd⟩) hlabJ hΛn
      ltrv4d1_check_1_twD5 ltrv4d1_check_2_twD5
    simp only [ltrv4d1_good, Bool.and_eq_true, decide_eq_true_eq, ltrv4d1_id] at hgood
    refine ⟨hT, ?_⟩
    unfold E6RowDataR1
    exact ⟨hgood.1, of_decide_eq_true hgood.2⟩

theorem e6RowTableR4_holds : E6RowTableR4 := by
  intro Omega _ _ _ lab R _ I phi ρ j hΛ hsingle hqs hrow
  obtain ⟨lt, lr, ln⟩ := lab
  have hΛn : 1 ≤ ln := hΛ.1
  unfold GGE6ThreeR4Labels1585 at hrow
  dsimp only at hrow
  rcases hrow with ⟨htag, h3, hlabJ⟩ | ⟨htag, h3, hlabJ⟩
  · subst htag
    have hreq := ρ.row.type_eq
    simp only [ggKacTypeOfLabel, Option.some.injEq, Prod.mk.injEq] at hreq
    have hT : ρ.row.T = .E6 := hreq.1.symm
    have htwb : ρ.row.tw = false := hreq.2.symm
    have hd : ρ.row.d = 1 := by rw [ρ.row.d_eq, if_pos h3]
    have hgood := ltrv4d1_good_of_row ρ j hT (Or.inl ⟨htwb, hd⟩) hlabJ hΛn
      ltrv4d1_check_1_A5 ltrv4d1_check_2_A5
    simp only [ltrv4d1_good, Bool.and_eq_true, decide_eq_true_eq, ltrv4d1_id] at hgood
    refine ⟨hT, ?_⟩
    unfold E6RowDataR4
    exact ⟨hgood.1, of_decide_eq_true hgood.2⟩
  · subst htag
    have hreq := ρ.row.type_eq
    simp only [ggKacTypeOfLabel, Option.some.injEq, Prod.mk.injEq] at hreq
    have hT : ρ.row.T = .E6 := hreq.1.symm
    have htwb : ρ.row.tw = true := hreq.2.symm
    have hd : ρ.row.d = 2 := by
      rw [ρ.row.d_eq, if_neg (ltrv4d1_not_dvd_neg h3)]
    have hgood := ltrv4d1_good_of_row ρ j hT (Or.inr ⟨htwb, hd⟩) hlabJ hΛn
      ltrv4d1_check_1_twA5 ltrv4d1_check_2_twA5
    simp only [ltrv4d1_good, Bool.and_eq_true, decide_eq_true_eq, ltrv4d1_id] at hgood
    refine ⟨hT, ?_⟩
    unfold E6RowDataR4
    exact ⟨hgood.1, of_decide_eq_true hgood.2⟩

end CFSG.StandardType.E6Centralizer1585

end

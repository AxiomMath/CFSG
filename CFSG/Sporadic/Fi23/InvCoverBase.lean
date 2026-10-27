
module

public import CFSG.Sporadic.Fi23.Classes
public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Fi23.InvCertInputs

@[expose] public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem isConj_of_pow_odd {G : Type*} [Group G] {s r : G} (hs : s ^ 2 = 1) (hr : r ^ 2 = 1)
    {m : ℕ} (hm : m % 2 = 1) (h : (s * r) ^ m = 1) : IsConj r s := by
  have hr2 : r * r = 1 := by rw [← pow_two, hr]
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs])
  have h1 : r * (s * r)⁻¹ = s * r * r := by
    rw [mul_inv_rev, hri, hsi, ← mul_assoc, hr2, one_mul, mul_assoc, hr2, mul_one]
  have h2 : ∀ j : ℕ, r * ((s * r)⁻¹) ^ j = (s * r) ^ j * r := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
    | succ j ih =>
      calc r * ((s * r)⁻¹) ^ (j + 1) = r * (s * r)⁻¹ * ((s * r)⁻¹) ^ j := by
            rw [pow_succ', mul_assoc]
        _ = s * r * (r * ((s * r)⁻¹) ^ j) := by rw [h1, mul_assoc]
        _ = (s * r) ^ (j + 1) * r := by rw [ih, ← mul_assoc, ← pow_succ']
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  refine isConj_iff.2 ⟨(s * r) ^ (k + 1), ?_⟩
  rw [mul_assoc, ← inv_pow, h2, ← mul_assoc, ← pow_add,
    show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, h, one_mul, mul_assoc, hr2, mul_one]

theorem mul_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (h : x * y = y * x) : (x * y) ^ 2 = 1 := by
  have hc : Commute x y := h
  rw [hc.mul_pow, hx, hy, one_mul]

theorem mul_comm_of_sq {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (h : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hx])
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hy])
  have e : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← pow_two, h])
  rw [← e, mul_inv_rev, hxi, hyi]

theorem iterPR_eq
    {P R : Table} {s r : J} (hP : Rep 31671 P s) (hR : Rep 31671 R r) (m : ℕ)
    {x : ℕ} (hx : x < 31671) : iterPR P R m x = idx 31671 ((s * r) ^ m) x := by
  induction m with
  | zero => rw [pow_zero, idx_one]; rfl
  | succ m ih =>
    have e : iterPR P R (m + 1) x = ap P (ap R (iterPR P R m x)) := rfl
    have h1 := idx_lt ((s * r) ^ m) hx
    rw [e, ih, hR _ h1, hP _ (idx_lt r h1), ← idx_mul, ← idx_mul, pow_succ']

theorem pow_eq_one_of_fixQ
    {P R : Table} {s r : J} (hP : Rep 31671 P s) (hR : Rep 31671 R r)
    {m : ℕ} (h : fixQ P R m = true) : (s * r) ^ m = 1 := by
  apply sep
  intro t ht
  unfold fixQ at h
  rw [Array.all_eq_true] at h
  have e := h t ht
  simp only [beq_iff_eq] at e
  rw [← getElem!_pos chainQ t ht] at e
  rw [← iterPR_eq hP hR m (chainQ_lt ht)]
  exact e

theorem isConj_of_oddOK
    {P R : Table} {s r : J} (hP : Rep 31671 P s) (hR : Rep 31671 R r)
    (hs : s ^ 2 = 1) (hr : r ^ 2 = 1) (h : oddOK P R = true) : IsConj r s := by
  unfold oddOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact isConj_of_pow_odd hs hr h.1 (pow_eq_one_of_fixQ hP hR h.2)

theorem rep_conjsOf
    {X : Table} {x : J} (hX : Rep 31671 X x) {ws : Array (List ℤ)}
    {W : Table × Table × Table} (hW : W ∈ conjsOf orb X ws)
    (hinv : invOK 31671 W.1 W.2.1 = true) : ∃ w : J, Rep 31671 W.2.2 (w * x * w⁻¹) := by
  unfold conjsOf at hW
  obtain ⟨u, -, rfl⟩ := Array.mem_map.1 hW
  dsimp only at hinv ⊢
  have h1 : Rep 31671 (wordT 31671 (genTables orb) u) (wordG genG u) :=
    Rep.wordT (by norm_num) _ fun l _ => rep_gen l
  have h2 := Rep.inv_of_invOK h1 hinv
  refine ⟨wordG genG u, ?_⟩
  rw [mul_assoc]
  exact Rep.compT h1 (Rep.compT hX h2)

theorem rep_genTables_neg_two :
    Rep 31671 (genTables orb (-2)) b⁻¹ := by
  have h := rep_gen (-2)
  have e : genG (-2) = b⁻¹ := by
    unfold genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rw [e] at h
  exact h

noncomputable abbrev ptT (k : ℕ) : Table := treeActTab orb (dTab orb) (genTables orb (-2)) k

theorem rep_ptT (k : ℕ) : Rep 31671 (ptT k) (conjPt k) := by
  have hspec := treeAct_spec rep_alpha rep_beta rep_genTables_neg_two rep_dTab a_inv conjPt
    conjPt_eq
  intro m hm
  have h := hspec k m hm
  have hlt : treeAct orb.par orb.lab orb.alpha orb.beta (dTab orb) (genTables orb (-2)) k m <
      2 ^ 32 := by
    rw [h]; exact (idx_lt _ hm).trans (by norm_num)
  show ap (treeActTab orb (dTab orb) (genTables orb (-2)) k) m = _
  unfold treeActTab
  rw [ap_ofFn _ hm, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, h]

@[expose] noncomputable def d1 : J := conjPt 1

@[expose] noncomputable def c39 : J := conjPt 39

@[expose] noncomputable def t2 : J := d * d1 * c39

noncomputable abbrev XBT : Table := compT 31671 (dTab orb) (ptT 1)

noncomputable abbrev XCT : Table := compT 31671 XBT (ptT 39)

theorem rep_XBT :
    Rep 31671 XBT (d * d1) := Rep.compT rep_dTab (rep_ptT 1)

theorem rep_XCT : Rep 31671 XCT t2 := Rep.compT rep_XBT (rep_ptT 39)

noncomputable abbrev RAT : Array (Table × Table × Table) := conjsOf orb (dTab orb) wordsA

noncomputable abbrev RBT : Array (Table × Table × Table) := conjsOf orb XBT wordsB

noncomputable abbrev RCT : Array (Table × Table × Table) := conjsOf orb XCT wordsC

structure InvParts : Prop where
  d_fix : ap (dTab orb) 39 = 39
  d1_fix : ap (ptT 1) 39 = 39
  fix_d : fixCount (dTab orb) = 3511
  fix_B : fixCount XBT = 695
  fix_C : fixCount XCT = 183
  C_ne : isIdT XCT = false
  invA : ∀ W ∈ RAT, invOK 31671 W.1 W.2.1 = true
  invB : ∀ W ∈ RBT, invOK 31671 W.1 W.2.1 = true
  invC : ∀ W ∈ RCT, invOK 31671 W.1 W.2.1 = true
  common : allIn 0 31671 (fun k => k == 0 || k == 1 || ap (dTab orb) k != k ||
    ap (ptT 1) k != k || fixCount (compT 31671 XBT (ptT k)) == 183) = true
  pairs : ∀ k < (tabS 0).size, ∀ B ∈ tabS 1, coverPair RAT RBT RCT (tabS 0)[k]! B = true

theorem conjPt_sq {k : ℕ} (hk : k < 31671) : conjPt k ^ 2 = 1 := by
  rw [← orderOf_of_isConj ((isConj_d_iff _).2 ⟨⟨k, hk⟩, rfl⟩)]
  exact pow_orderOf_eq_one _

theorem d_sq' : d ^ 2 = 1 := by rw [pow_two]; exact d_sq

theorem d1_sq : d1 ^ 2 = 1 := conjPt_sq (by norm_num)

theorem c39_sq : c39 ^ 2 = 1 := conjPt_sq (by norm_num)

theorem d1_commute : d1 * d = d * d1 := by
  have h : (d * d1) ^ 2 = 1 := by
    rw [← orderOf_d_mul_conjPt_one]
    exact pow_orderOf_eq_one _
  exact (mul_comm_of_sq d_sq' d1_sq h).symm

theorem d1_mem_localClass : d1 ∈ LocalClass D23 d := by
  refine ⟨(isConj_d_iff _).2 ⟨⟨1, by norm_num⟩, rfl⟩, fun h => ?_, d1_commute⟩
  have h' : conjPt 1 = conjPt 0 := by rw [conjPt_zero]; exact h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem d_mul_d1_sq : (d * d1) ^ 2 = 1 := by
  have h := mul_sq_eq_one d_sq' d1_sq d1_commute.symm
  exact h

theorem d_mul_d1_ne_one : d * d1 ≠ 1 := by
  intro h
  apply d1_mem_localClass.2.1
  rw [← mul_left_cancel_iff (a := d), h, d_sq]

theorem mem_orbit_iff_mem_D23
    (x : J) : x ∈ MulAction.orbit (ConjAct J) d ↔ x ∈ D23 := by
  show _ ↔ IsConj d x
  rw [isConj_iff, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.ofConjAct g, by rw [ConjAct.smul_def]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, by rw [toConjAct_smul_eq]⟩

@[expose] noncomputable def ptD : Fin 31671 ≃ D23 :=
  ptEquiv.trans (Equiv.subtypeEquivRight mem_orbit_iff_mem_D23)

theorem ptD_val (i : Fin 31671) : (ptD i : J) = conjPt i.val := rfl

theorem card_fixed_eq {X : Table} {g : J} (hX : Rep 31671 X g) :
    Nat.card {x : D23 // g * x * g⁻¹ = x} = fixCount X := by
  have e1 : {i : Fin 31671 // ap X i.val = i.val} ≃ {x : D23 // g * x * g⁻¹ = x} :=
    Equiv.subtypeEquiv ptD fun i => by
      rw [hX i.val i.isLt, idx_eq_iff i.isLt i.isLt, ptD_val]
  have e2 : {i : Fin 31671 // ap X i.val = i.val} ≃
      ((Finset.range 31671).filter fun k => ap X k = k) :=
    { toFun := fun i => ⟨i.1.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 i.1.2, i.2⟩⟩
      invFun := fun k => ⟨⟨k.1, Finset.mem_range.1 (Finset.mem_filter.1 k.2).1⟩,
        (Finset.mem_filter.1 k.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e1, Nat.card_congr e2, Nat.card_eq_finsetCard,
    ← Nat.count_eq_card_filter_range]
  unfold fixCount Nat.count
  exact List.countP_congr fun i _ => by simp

theorem conj_mem_D23 (c z : J) (hz : z ∈ D23) : c * z * c⁻¹ ∈ D23 :=
  (hz : IsConj d z).trans (isConj_iff.2 ⟨c, rfl⟩)

theorem card_fixed_conj {x y : J} (h : IsConj x y) :
    Nat.card {z : D23 // x * z * x⁻¹ = z} = Nat.card {z : D23 // y * z * y⁻¹ = z} := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  let f : D23 ≃ D23 :=
    { toFun := fun z => ⟨c * z * c⁻¹, conj_mem_D23 c z z.2⟩
      invFun := fun z => ⟨c⁻¹ * z * c⁻¹⁻¹, conj_mem_D23 c⁻¹ z z.2⟩
      left_inv := fun z => Subtype.ext (by dsimp only; group)
      right_inv := fun z => Subtype.ext (by dsimp only; group) }
  refine Nat.card_congr (Equiv.subtypeEquiv f fun z => ?_)
  show x * z * x⁻¹ = z ↔ c * x * c⁻¹ * (c * z * c⁻¹) * (c * x * c⁻¹)⁻¹ = c * z * c⁻¹
  have e : c * x * c⁻¹ * (c * z * c⁻¹) * (c * x * c⁻¹)⁻¹ = c * (x * z * x⁻¹) * c⁻¹ := by group
  rw [e]
  constructor
  · intro h
    rw [h]
  · intro h
    calc x * z * x⁻¹ = c⁻¹ * (c * (x * z * x⁻¹) * c⁻¹) * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [h]
      _ = z := by group

theorem exists_conj_pair
    {x y : J} (hx : x ∈ D23) (hy : y ∈ LocalClass D23 x) :
    ∃ h : J, h * d * h⁻¹ = x ∧ h * d1 * h⁻¹ = y := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (show IsConj d x from hx)
  obtain ⟨hyD, hyx, hyc⟩ := hy
  have hy' : g⁻¹ * y * g ∈ star := by
    refine ⟨?_, fun e => hyx ?_, ?_⟩
    · have := conj_mem_D23 g⁻¹ y hyD
      rwa [inv_inv] at this
    · rw [← e]; group
    · calc g⁻¹ * y * g * d = g⁻¹ * (y * (g * d * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹ * y) * g := by rw [hyc]
        _ = d * (g⁻¹ * y * g) := by group
  obtain ⟨c, hc⟩ := star_transitive ⟨d1, d1_mem_localClass⟩ ⟨_, hy'⟩
  have hc1 : (c : J) * d1 * (c : J)⁻¹ = g⁻¹ * y * g := by
    have := congrArg Subtype.val hc
    rw [starAction_val] at this
    exact this
  have hcd : (c : J) * d * (c : J)⁻¹ = d := by rw [mem_Cd.1 c.2, mul_inv_cancel_right]
  refine ⟨g * (c : J), ?_, ?_⟩
  · calc g * (c : J) * d * (g * (c : J))⁻¹ = g * ((c : J) * d * (c : J)⁻¹) * g⁻¹ := by group
      _ = g * d * g⁻¹ := by rw [hcd]
  · calc g * (c : J) * d1 * (g * (c : J))⁻¹ = g * ((c : J) * d1 * (c : J)⁻¹) * g⁻¹ := by group
      _ = y := by rw [hc1]; group

theorem isConj_d_mul_d1_of_mem
    {x y : J} (hx : x ∈ D23) (hy : y ∈ LocalClass D23 x) :
    IsConj (d * d1) (x * y) := by
  obtain ⟨h, hd, hd1⟩ := exists_conj_pair hx hy
  refine isConj_iff.2 ⟨h, ?_⟩
  rw [← hd, ← hd1]
  group

theorem ap_eq_of_commute
    {X : Table} {x : J} (hX : Rep 31671 X x) {k : ℕ} (hk : k < 31671)
    (h : conjPt k * x = x * conjPt k) : ap X k = k := by
  rw [hX k hk, idx_eq_iff hk hk, ← h, mul_inv_cancel_right]

end CFSG.Sporadic.Fi23

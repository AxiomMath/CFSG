
module

public import CFSG.Sporadic.J4.QT2LocX0Check
public import CFSG.Sporadic.J4.QT2AMod
public import CFSG.Sporadic.J4.QT2LocFiveProofBase
public import CFSG.Sporadic.J4.QT2LocCntProofBase
public import CFSG.Sporadic.J4.QT2LocHGen

@[expose] public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

noncomputable def x0Gen (i : ℕ) : J :=
  if i < 8 then QT2A.el5 (x0Words.getD i []) else (QT2A.el5 (x0Words.getD (i - 8) []))⁻¹

noncomputable def X0Sub : Subgroup J := Subgroup.closure (x0Gen '' {i | i < 16})

theorem x0Gen_mem {i : ℕ} (hi : i < 16) : x0Gen i ∈ X0Sub :=
  Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem x0Gen_inv {i : ℕ} (hi : i < 16) : (x0Gen i)⁻¹ = x0Gen ((i + 8) % 16) := by
  unfold x0Gen
  by_cases h : i < 8
  · have h1 : (i + 8) % 16 = i + 8 := by omega
    have h2 : ¬ (i + 8 < 8) := by omega
    rw [h1, ite_eq_left h, ite_eq_right h2, show i + 8 - 8 = i by omega]
  · have h1 : (i + 8) % 16 = i - 8 := by omega
    have h2 : i - 8 < 8 := by omega
    rw [h1, ite_eq_right h, ite_eq_left h2, inv_inv]

private theorem gens_facts :
    x0Words.length = 8 ∧ x0GenRows.size = 8 ∧ x0InvRows.size = 8 ∧
    eqRows (x0GenRows[0]!) (QT2A.wR [1, 2, -3, 1, 2, -3]) = true ∧
    ∀ i < 8, wfRows x0GenRows[i]! = true ∧ wfRows x0InvRows[i]! = true ∧
      eqRows (mulRows x0GenRows[i]! x0InvRows[i]!) idRows = true ∧
      eqRows (mulRows x0InvRows[i]! x0GenRows[i]!) idRows = true ∧
      eqRows (mulRows x0GenRows[i]! x0GenRows[0]!) (mulRows x0GenRows[0]! x0GenRows[i]!) =
        true := by
  have h := chkX0Gens_true
  unfold chkX0Gens at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun i hi => by
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h5 i hi
    exact ⟨a, b, c, d, e⟩⟩

private theorem x0GenRows_get {i : ℕ} (hi : i < 8) :
    x0GenRows[i]! = QT2A.wR (x0Words.getD i []) := by
  obtain ⟨h1, -⟩ := gens_facts
  have hi' : i < x0Words.length := by omega
  unfold x0GenRows
  simp [hi']

private theorem x0AllRows_get_lt
    {i : ℕ} (hi : i < 8) : x0AllRows[i]! = x0GenRows[i]! := by
  obtain ⟨-, h2, -⟩ := gens_facts
  have hi' : i < x0GenRows.size := by omega
  rw [getElem!_pos x0AllRows i (by simp [x0AllRows, h2, x0InvRows]; omega),
    getElem!_pos x0GenRows i hi']
  unfold x0AllRows
  exact Array.getElem_append_left hi'

private theorem x0AllRows_get_ge
    {i : ℕ} (hi : 8 ≤ i) (hi2 : i < 16) :
    x0AllRows[i]! = x0InvRows[i - 8]! := by
  obtain ⟨-, h2, h3, -⟩ := gens_facts
  have hi' : i - 8 < x0InvRows.size := by omega
  rw [getElem!_pos x0AllRows i (by simp [x0AllRows, h2, x0InvRows]; omega),
    getElem!_pos x0InvRows (i - 8) hi']
  unfold x0AllRows
  rw [Array.getElem_append_right (by omega)]
  congr 1

theorem Mx_x0Gen_lt (hM : MatFacts) {i : ℕ} (hi : i < 8) :
    Mx (x0Gen i) = rowsMatrix (x0AllRows[i]!) := by
  rw [x0AllRows_get_lt hi, x0GenRows_get hi, x0Gen, ite_eq_left hi]
  exact QT2A.Mx_el5 hM _

theorem Mx_x0Gen (hM : MatFacts) {i : ℕ} (hi : i < 16) :
    Mx (x0Gen i) = rowsMatrix (x0AllRows[i]!) := by
  by_cases h : i < 8
  · exact Mx_x0Gen_lt hM h
  · have h8 : 8 ≤ i := by omega
    obtain ⟨-, -, -, -, hf⟩ := gens_facts
    obtain ⟨-, -, hc, hd, -⟩ := hf (i - 8) (by omega)
    have hg : Mx (x0Gen (i - 8)) = rowsMatrix (x0GenRows[i - 8]!) := by
      have := Mx_x0Gen_lt hM (i := i - 8) (by omega)
      rwa [x0AllRows_get_lt (by omega)] at this
    have hinv : x0Gen i = (x0Gen (i - 8))⁻¹ := by
      unfold x0Gen
      rw [ite_eq_right h, ite_eq_left (by omega)]
    rw [x0AllRows_get_ge h8 hi, hinv]
    have e2 : rowsMatrix x0InvRows[i - 8]! * rowsMatrix x0GenRows[i - 8]! = 1 := by
      rw [← rowsMatrix_mulRows, eqRows_iff.1 hd, rowsMatrix_idRows]
    have e3 : Mx (x0Gen (i - 8)) * Mx (x0Gen (i - 8))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    calc Mx (x0Gen (i - 8))⁻¹ = (rowsMatrix x0InvRows[i - 8]! * rowsMatrix x0GenRows[i - 8]!) *
          Mx (x0Gen (i - 8))⁻¹ := by rw [e2, one_mul]
      _ = rowsMatrix x0InvRows[i - 8]! * (Mx (x0Gen (i - 8)) * Mx (x0Gen (i - 8))⁻¹) := by
          rw [mul_assoc, ← hg]
      _ = rowsMatrix x0InvRows[i - 8]! := by rw [e3, mul_one]

private theorem orb_facts :
    x0Orb.mats.size = 6720 ∧ 0 < 6720 ∧ x0Orb.mats[0]! = idRows ∧
    ∀ q < 6720, oOrbAt x0Step 16 x0Orb q = true := by
  have h := chkX0Orb_true
  unfold chkX0Orb oOrbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h4, eqRows_iff.1 h5, h6⟩

theorem oOrbAt_facts {step : Array V2 → Nat → Array V2} {nl : ℕ} {O : MOrb} {q : ℕ}
    (h : oOrbAt step nl O q = true) :
    wfRows O.mats[q]! = true ∧ mfind O.mats O.slots O.bits O.mats[q]! = q + 1 ∧
      (∀ g < nl, ∃ e, e ≠ 0 ∧ e ≤ O.mats.size ∧ O.mats[e - 1]! = step O.mats[q]! g) ∧
      (q = 0 ∨ (O.par[q]! < q ∧ O.lab[q]! < nl ∧
        step O.mats[O.par[q]!]! O.lab[q]! = O.mats[q]!)) := by
  unfold oOrbAt at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq,
    decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun g hg => ?_, ?_⟩
  · obtain ⟨⟨h31, h32⟩, h33⟩ := h3 g hg
    exact ⟨_, h31, h32, eqRows_iff.1 h33⟩
  · rcases h4 with h4 | ⟨⟨h41, h42⟩, h43⟩
    · exact Or.inl h4
    · exact Or.inr ⟨h41, h42, eqRows_iff.1 h43⟩

theorem eq_of_rowsMatrix_eq {X Y : Array V2} (hX : wfRows X = true) (hY : wfRows Y = true)
    (h : rowsMatrix X = rowsMatrix Y) : X = Y := by
  unfold wfRows at hX hY
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at hX hY
  obtain ⟨hXs, hXw⟩ := hX
  obtain ⟨hYs, hYw⟩ := hY
  refine Array.ext (hXs.trans hYs.symm) fun i h1 h2 => ?_
  have hi : i < 112 := by omega
  have e := congrFun (congrFun h ⟨i, hi⟩)
  have hXi := hXw i h1
  have hYi := hYw i h2
  refine (V2.toVec_inj hXi hYi).1 ?_
  funext j
  have := e j
  simp only [rowsMatrix_apply, Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2,
    Option.getD_some] at this
  exact this

def X0S : Set J := {g | ∃ q < 6720, Mx g = rowsMatrix (x0Orb.mats[q]!)}

theorem X0S_one : (1 : J) ∈ X0S := by
  refine ⟨0, by norm_num, ?_⟩
  rw [orb_facts.2.2.1, map_one, rowsMatrix_idRows]

theorem X0S_mul_gen
    (hM : MatFacts) {g : J} (hg : g ∈ X0S) {i : ℕ} (hi : i < 16) :
    g * x0Gen i ∈ X0S := by
  obtain ⟨q, hq, hgq⟩ := hg
  obtain ⟨-, -, hstep, -⟩ := oOrbAt_facts (orb_facts.2.2.2 q hq)
  obtain ⟨e, he0, hesz, hee⟩ := hstep i hi
  have hsz := orb_facts.1
  refine ⟨e - 1, by omega, ?_⟩
  rw [hee, map_mul, hgq, Mx_x0Gen hM hi]
  simp only [x0Step]
  rw [rowsMatrix_mulRows]

theorem closure_le_S (hM : MatFacts) {k : J}
    (hk : k ∈ Submonoid.closure (x0Gen '' {i | i < 16})) : ∀ g ∈ X0S, g * k ∈ X0S := by
  induction hk using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact fun g hg => X0S_mul_gen hM hg hi
  | one => intro g hg; simpa using hg
  | mul x y _ _ hx hy => intro g hg; rw [← mul_assoc]; exact hy _ (hx g hg)

theorem X0Sub_le_S
    (hM : MatFacts) : ∀ k ∈ X0Sub, ∀ g ∈ X0S, g * k ∈ X0S := by
  intro k hk
  have hk' : k ∈ (X0Sub : Subgroup J).toSubmonoid := hk
  rw [X0Sub, Subgroup.closure_toSubmonoid_of_finite] at hk'
  exact closure_le_S hM hk'

theorem mem_X0Sub_of_lt (hM : MatFacts) :
    ∀ q < 6720, ∃ g ∈ X0Sub, Mx g = rowsMatrix (x0Orb.mats[q]!) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    obtain ⟨-, -, -, hpar⟩ := oOrbAt_facts (orb_facts.2.2.2 q hq)
    rcases hpar with h0 | ⟨hp, hl, hst⟩
    · refine ⟨1, X0Sub.one_mem, ?_⟩
      subst h0
      rw [orb_facts.2.2.1, map_one, rowsMatrix_idRows]
    · obtain ⟨g, hg, hgM⟩ := ih _ hp (lt_trans hp hq)
      refine ⟨_, X0Sub.mul_mem hg (x0Gen_mem hl), ?_⟩
      rw [← hst, map_mul, hgM, Mx_x0Gen hM hl]
      simp only [x0Step]
      rw [rowsMatrix_mulRows]

theorem mem_X0Sub_iff (hM : MatFacts) {g : J} :
    g ∈ X0Sub ↔ ∃ q < 6720, Mx g = rowsMatrix (x0Orb.mats[q]!) := by
  constructor
  · intro hg
    have := X0Sub_le_S hM g hg 1 X0S_one
    rw [one_mul] at this
    exact this
  · rintro ⟨q, hq, hgq⟩
    obtain ⟨g', hg', hg'q⟩ := mem_X0Sub_of_lt hM q hq
    have : g = g' := Mx_injective (hgq.trans hg'q.symm)
    rwa [this]

theorem x0Orb_inj {q q' : ℕ} (hq : q < 6720) (hq' : q' < 6720)
    (h : rowsMatrix (x0Orb.mats[q]!) = rowsMatrix (x0Orb.mats[q']!)) : q = q' := by
  obtain ⟨hw, hf, -⟩ := oOrbAt_facts (orb_facts.2.2.2 q hq)
  obtain ⟨hw', hf', -⟩ := oOrbAt_facts (orb_facts.2.2.2 q' hq')
  have := eq_of_rowsMatrix_eq hw hw' h
  rw [this] at hf
  omega

theorem card_X0Sub (hM : MatFacts) : Nat.card X0Sub = 6720 := by
  let f : Fin 6720 → X0Sub := fun q =>
    ⟨(mem_X0Sub_of_lt hM q q.2).choose, (mem_X0Sub_of_lt hM q q.2).choose_spec.1⟩
  have hspec : ∀ q : Fin 6720, Mx (f q : J) = rowsMatrix (x0Orb.mats[q.val]!) := fun q =>
    (mem_X0Sub_of_lt hM q q.2).choose_spec.2
  have hbij : Function.Bijective f := by
    constructor
    · intro q q' h
      have h1 : Mx (f q : J) = Mx (f q' : J) := by rw [h]
      rw [hspec, hspec] at h1
      exact Fin.ext (x0Orb_inj q.2 q'.2 h1)
    · intro g
      obtain ⟨q, hq, hgq⟩ := (mem_X0Sub_iff hM).1 g.2
      refine ⟨⟨q, hq⟩, ?_⟩
      apply Subtype.ext
      apply Mx_injective
      rw [hspec]
      exact hgq.symm
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp

theorem gen5_eq_xJ {k : ℕ} (hk : k < 3) : QT2A.gen5 k = xJ k := by
  simp [QT2A.gen5, hk]

theorem wordProd_gen5_xJ : ∀ w : List ℤ, (∀ l ∈ w, l ∈ letters) →
    wordProd QT2A.gen5 w = wordProd xJ w
  | [], _ => rfl
  | l :: w, h => by
    have hl := h l (List.mem_cons_self ..)
    have ih := wordProd_gen5_xJ w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    unfold wordProd at ih ⊢
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    congr 1
    simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gen5_eq_xJ]

theorem el5_fiveWord : QT2A.el5 fiveWord = fiveElt :=
  wordProd_gen5_xJ fiveWord fiveWord_letters

theorem x0Gen_zero (hM : MatFacts) : x0Gen 0 = fiveElt := by
  apply Mx_injective
  rw [Mx_x0Gen hM (by norm_num), x0AllRows_get_lt (by norm_num)]
  obtain ⟨-, -, -, h0, -⟩ := gens_facts
  rw [eqRows_iff.1 h0, ← el5_fiveWord]
  exact (QT2A.Mx_el5 hM _).symm

theorem fiveElt_mem_X0Sub (hM : MatFacts) : fiveElt ∈ X0Sub := by
  rw [← x0Gen_zero hM]
  exact x0Gen_mem (by norm_num)

theorem x0Gen_comm_lt (hM : MatFacts) {i : ℕ} (hi : i < 8) :
    x0Gen i * fiveElt = fiveElt * x0Gen i := by
  apply Mx_injective
  obtain ⟨-, -, -, -, hf⟩ := gens_facts
  have h := eqRows_iff.1 (hf i hi).2.2.2.2
  rw [map_mul, map_mul, ← x0Gen_zero hM, Mx_x0Gen hM (by omega), Mx_x0Gen hM (by norm_num),
    x0AllRows_get_lt hi, x0AllRows_get_lt (by norm_num), ← rowsMatrix_mulRows,
    ← rowsMatrix_mulRows, h]

theorem x0Gen_comm (hM : MatFacts) {i : ℕ} (hi : i < 16) :
    x0Gen i * fiveElt = fiveElt * x0Gen i := by
  by_cases h : i < 8
  · exact x0Gen_comm_lt hM h
  · have hinv : x0Gen i = (x0Gen (i - 8))⁻¹ := by
      unfold x0Gen
      rw [ite_eq_right h, ite_eq_left (by omega)]
    rw [hinv]
    exact (Commute.inv_left (show Commute (x0Gen (i - 8)) fiveElt from
      x0Gen_comm_lt hM (by omega)))

theorem closure_le_centralizer_of_comm {G : Type*} [Group G] {S : Set G} {x : G}
    (h : ∀ s ∈ S, s * x = x * s) : Subgroup.closure S ≤ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact h s hs

theorem X0Sub_le_centralizer (hM : MatFacts) :
    X0Sub ≤ Subgroup.centralizer ({fiveElt} : Set J) :=
  closure_le_centralizer_of_comm (by
    rintro _ ⟨i, hi, rfl⟩
    exact x0Gen_comm hM hi)

theorem smul_w₀_eq {g : J} {M : Array V2} (hg : Mx g⁻¹ = rowsMatrix M) :
    g • w₀ = toRow (frApply (frTable M) rootV).toVec := by
  rw [← ofRow_inj, smul_row, frApply_toVec_eq_vecMul, ← hg]
  rfl

theorem wfRows_mem {M : Array V2} (h : wfRows M = true) : ∀ x ∈ M, x.wf = true := by
  unfold wfRows at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact h.2 i hi

theorem mats_wf
    {q : ℕ} (hq : q < 6720) : wfRows x0Orb.mats[q]! = true :=
  (oOrbAt_facts (orb_facts.2.2.2 q hq)).1

private theorem pts_len : x0Pts.eraseDups.length = 14 := by
  have h := chkX0Pts_true
  unfold chkX0Pts at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact h.1.1

theorem mem_x0Pts {p : V2} :
    p ∈ x0Pts ↔ ∃ q < 6720, p = frApply (frTable x0Orb.mats[q]!) rootV := by
  unfold x0Pts
  rw [List.mem_map]
  constructor
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_toList_iff.1 hM)
    have hsz := orb_facts.1
    exact ⟨q, by omega, by rw [getElem!_pos _ q hq]⟩
  · rintro ⟨q, hq, rfl⟩
    have hsz := orb_facts.1
    refine ⟨x0Orb.mats[q]!, Array.mem_toList_iff.2 ?_, rfl⟩
    rw [getElem!_pos _ q (by omega)]
    exact Array.getElem_mem _

theorem x0Pts_wf {p : V2} (hp : p ∈ x0Pts) : p.wf = true := by
  obtain ⟨q, hq, rfl⟩ := mem_x0Pts.1 hp
  exact frApply_frTable_wf (wfRows_mem (mats_wf hq)) rootV

noncomputable def x0PtSet : Finset Row :=
  (x0Pts.eraseDups.map fun p => toRow p.toVec).toFinset

theorem card_x0PtSet : x0PtSet.card = 14 := by
  unfold x0PtSet
  have hnd : x0Pts.eraseDups.Nodup := eraseDups_nodup x0Pts.length x0Pts le_rfl
  rw [List.toFinset_card_of_nodup, List.length_map, pts_len]
  refine hnd.map_on ?_
  intro x hx y hy hxy
  have hx' := x0Pts_wf (List.mem_eraseDups.1 hx)
  have hy' := x0Pts_wf (List.mem_eraseDups.1 hy)
  exact (V2.toVec_inj hx' hy').1 hxy

theorem smul_mem_pts
    (hM : MatFacts) {g : J} (hg : g ∈ X0Sub) : g • w₀ ∈ x0PtSet := by
  obtain ⟨q, hq, hgq⟩ := (mem_X0Sub_iff hM).1 (X0Sub.inv_mem hg)
  rw [smul_w₀_eq hgq]
  unfold x0PtSet
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨_, List.mem_eraseDups.2 (mem_x0Pts.2 ⟨q, hq, rfl⟩), rfl⟩

theorem exists_of_mem_pts
    (hM : MatFacts) {p : Row} (hp : p ∈ x0PtSet) :
    ∃ g ∈ X0Sub, g • w₀ = p := by
  unfold x0PtSet at hp
  rw [List.mem_toFinset, List.mem_map] at hp
  obtain ⟨d, hd, rfl⟩ := hp
  obtain ⟨q, hq, rfl⟩ := mem_x0Pts.1 (List.mem_eraseDups.1 hd)
  obtain ⟨g', hg', hg'q⟩ := mem_X0Sub_of_lt hM q hq
  refine ⟨g'⁻¹, X0Sub.inv_mem hg', ?_⟩
  exact smul_w₀_eq (by rw [inv_inv]; exact hg'q)

theorem x0_fixed_points
    (hM : MatFacts) :
    ∃ P : Finset Row, P.card = 14 ∧ (∀ p ∈ P, fiveElt • p = p) ∧
      (∀ g ∈ X0Sub, g • w₀ ∈ P) ∧ ∀ p ∈ P, ∃ g ∈ X0Sub, g • w₀ = p := by
  refine ⟨x0PtSet, card_x0PtSet, fun p hp => ?_, fun g hg => smul_mem_pts hM hg,
    fun p hp => exists_of_mem_pts hM hp⟩
  obtain ⟨g, hg, rfl⟩ := exists_of_mem_pts hM hp
  have hc : fiveElt * g = g * fiveElt :=
    (Subgroup.mem_centralizer_singleton_iff.1 (X0Sub_le_centralizer hM hg)).symm
  rw [← mul_smul, hc, mul_smul, smul_root_of_mem_Hj hM fiveElt_mem_Hj]

theorem orbit_X0Sub_w₀ (hM : MatFacts) :
    MulAction.orbit X0Sub w₀ = (x0PtSet : Set Row) := by
  ext p
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact Finset.mem_coe.2 (smul_mem_pts hM hg)
  · intro hp
    obtain ⟨g, hg, rfl⟩ := exists_of_mem_pts hM (Finset.mem_coe.1 hp)
    exact ⟨⟨g, hg⟩, rfl⟩

theorem card_X0Sub_stabilizer (hM : MatFacts) :
    Nat.card (MulAction.stabilizer X0Sub w₀) = 480 := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer X0Sub w₀)
  rw [MulAction.index_stabilizer, orbit_X0Sub_w₀ hM, Set.ncard_coe_finset, card_x0PtSet,
    card_X0Sub hM] at h1
  omega

theorem conj_assoc {G : Type*} [Group G] (a b e : G) :
    (a⁻¹ * b) * e * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * e * b⁻¹) * a := by
  group

private theorem conj_facts {c m : ℕ} {O : MOrb}
    (h : oOrbOK x0CStep 16 (x0Eta c) O m = true) :
    O.mats.size = m ∧ O.mats[0]! = x0Eta c ∧ ∀ q < m, oOrbAt x0CStep 16 O q = true := by
  unfold oOrbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, eqRows_iff.1 h5, h6⟩

theorem conj_spec (hM : MatFacts) {c m : ℕ} {O : MOrb}
    (h : oOrbOK x0CStep 16 (x0Eta c) O m = true) :
    ∀ q < m, ∃ g ∈ X0Sub, Mx (g * eta uJ 11 c * g⁻¹) = rowsMatrix (O.mats[q]!) := by
  obtain ⟨-, hroot, hat⟩ := conj_facts h
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    obtain ⟨-, -, -, hpar⟩ := oOrbAt_facts (hat q hq)
    rcases hpar with h0 | ⟨hp, hl, hst⟩
    · refine ⟨1, X0Sub.one_mem, ?_⟩
      subst h0
      rw [hroot, inv_one, one_mul, mul_one, Mx_eta hM 11 le_rfl c]
      rfl
    · obtain ⟨g, hg, hgM⟩ := ih _ hp (lt_trans hp hq)
      refine ⟨(x0Gen O.lab[q]!)⁻¹ * g, X0Sub.mul_mem (X0Sub.inv_mem (x0Gen_mem hl)) hg, ?_⟩
      rw [conj_assoc, ← hst]
      simp only [x0CStep]
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hgM, ← Mx_x0Gen hM hl,
        ← Mx_x0Gen hM (by omega : (O.lab[q]! + 8) % 16 < 16), ← x0Gen_inv hl, map_mul, map_mul]

theorem wfRows_size {X : Array V2} (h : wfRows X = true) : X.size = 112 := by
  simp only [wfRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  exact h.1

theorem wfRows_of {X : Array V2} (hs : X.size = 112) (hw : ∀ x ∈ X, x.wf = true) :
    wfRows X = true := by
  simp only [wfRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  exact ⟨hs, fun i hi => hw _ (Array.getElem_mem hi)⟩

private theorem inv_facts : x0Invs.length = 91 ∧ ∀ M ∈ x0Invs,
    (∃ i, ∃ (h : i < x0ConjT.mats.size), eqRows M x0ConjT.mats[i] = true) ∨
      (∃ i, ∃ (h : i < x0ConjZ.mats.size), eqRows M x0ConjZ.mats[i] = true) := by
  have h := chkX0Invs_true
  unfold chkX0Invs at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
    Array.any_eq_true] at h
  exact h

private theorem conj_ok :
    oOrbOK x0CStep 16 (x0Eta 178) x0ConjT 84 = true ∧
    oOrbOK x0CStep 16 (x0Eta 407) x0ConjZ 7 = true := by
  have h := chkX0Conj_true
  unfold chkX0Conj at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem X0Sub_involutions
    (hM : MatFacts) {y : J} (hy : y ∈ X0Sub) (hy2 : y * y = 1)
    (hne : y ≠ 1) :
    (∃ g ∈ X0Sub, y = g * eta uJ 11 178 * g⁻¹) ∨ (∃ g ∈ X0Sub, y = g * eta uJ 11 407 * g⁻¹) := by
  obtain ⟨q, hq, hyq⟩ := (mem_X0Sub_iff hM).1 hy
  have hsz := orb_facts.1
  have hwf : wfRows x0Orb.mats[q]! = true := mats_wf hq
  have hid : eqRows x0Orb.mats[q]! idRows = false := by
    by_contra hcon
    rw [Bool.not_eq_false, eqRows_iff] at hcon
    apply hne
    apply Mx_injective
    rw [hyq, hcon, rowsMatrix_idRows, map_one]
  have hsq : eqRows (mulRows x0Orb.mats[q]! x0Orb.mats[q]!) idRows = true := by
    rw [eqRows_iff]
    refine eq_of_rowsMatrix_eq ?_ (wfRows_of idRows_size idRows_wf) ?_
    · refine wfRows_of ?_ ?_
      · rw [mulRows_size]
        exact wfRows_size hwf
      · exact mulRows_wf _ (wfRows_mem hwf)
    · rw [rowsMatrix_mulRows, ← hyq, ← map_mul, hy2, map_one, rowsMatrix_idRows]
  have hmem : x0Orb.mats[q]! ∈ x0Invs := by
    unfold x0Invs
    rw [List.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Array.mem_toList_iff, getElem!_pos _ q (by omega)]
      exact Array.getElem_mem _
    · rw [Bool.and_eq_true]
      exact ⟨by simp [hid], hsq⟩
  obtain ⟨-, hcl⟩ := inv_facts
  obtain ⟨hT, hZ⟩ := conj_ok
  rcases hcl _ hmem with ⟨i, hi, he⟩ | ⟨i, hi, he⟩
  · left
    have hsz' := (conj_facts hT).1
    obtain ⟨g, hg, hgM⟩ := conj_spec hM hT i (by omega)
    refine ⟨g, hg, Mx_injective ?_⟩
    rw [hyq, hgM, eqRows_iff.1 he, getElem!_pos _ i hi]
  · right
    have hsz' := (conj_facts hZ).1
    obtain ⟨g, hg, hgM⟩ := conj_spec hM hZ i (by omega)
    refine ⟨g, hg, Mx_injective ?_⟩
    rw [hyq, hgM, eqRows_iff.1 he, getElem!_pos _ i hi]

theorem x0Invs_length : x0Invs.length = 91 := inv_facts.1

theorem x0ConjT_size :
    x0ConjT.mats.size = 84 := (conj_facts conj_ok.1).1

theorem x0ConjZ_size :
    x0ConjZ.mats.size = 7 := (conj_facts conj_ok.2).1

end CFSG.Sporadic.J4.QT2

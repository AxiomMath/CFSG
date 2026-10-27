module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexGraph
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLayers
public import Certificates.Data.D4HexGeoCheck
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Quasithin CFSG.Quasithin.H13.F45Ru CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

theorem hexPtsOK_spec {pts : Array ℕ} (h : hexPtsOK pts = true) :
    ∀ v < 2457, pts[3 * v]! < pts[3 * v + 1]! ∧ pts[3 * v + 1]! < pts[3 * v + 2]! ∧
      pts[3 * v + 2]! < 819 := by
  intro v hv
  simp only [hexPtsOK, Bool.and_eq_true, beq_iff_eq] at h
  have := allLt_spec h.2 hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem hexPtsOK_lt {pts : Array ℕ} (h : hexPtsOK pts = true) {v k : ℕ} (hv : v < 2457)
    (hk : k < 3) : pts[3 * v + k]! < 819 := by
  obtain ⟨h1, h2, h3⟩ := hexPtsOK_spec h v hv
  interval_cases k
  · exact (h1.trans h2).trans h3
  · exact h2.trans h3
  · exact h3

theorem hexIncOK_spec {pts ptL : Array ℕ} (h : hexIncOK pts ptL = true) :
    (∀ x < 819, ∀ k < 9, ptL[9 * x + k]! < 2457 ∧ hexOnLine pts x ptL[9 * x + k]! = true) ∧
      (∀ v < 2457, ∀ k < 3, ∃ j < 9, ptL[9 * pts[3 * v + k]! + j]! = v) := by
  simp only [hexIncOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx k hk => ?_, fun v hv k hk => ?_⟩
  · have := allLt_spec (allLt_spec h1 hx) hk
    simpa [Bool.and_eq_true] using this
  · have := allLt_spec (allLt_spec h2 hv) hk
    simp only [List.any_eq_true, beq_iff_eq, List.mem_range] at this
    obtain ⟨j, hj, hjv⟩ := this
    exact ⟨j, hj, hjv⟩

theorem hexOnLine_iff {pts : Array ℕ} {p v : ℕ} :
    hexOnLine pts p v = true ↔ ∃ k < 3, pts[3 * v + k]! = p := by
  simp only [hexOnLine, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, by norm_num, h⟩
    · exact ⟨1, by norm_num, h⟩
    · exact ⟨2, by norm_num, h⟩
  · rintro ⟨k, hk, h⟩
    interval_cases k
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

theorem mem_hexLine_iff (p : Fin 819) (v : Fin 2457) :
    p ∈ hexLine v ↔ hexOnLine lineTab p v = true :=
  hexOnLine_iff.symm

theorem hexMeetOK_spec {pts ptL : Array ℕ} (hp : hexPtsOK pts = true)
    (hi : hexIncOK pts ptL = true) (h : hexMeetOK pts ptL = true) {v w p q : ℕ} (hv : v < 2457)
    (hw : w < 2457) (hvw : v ≠ w) (hpq : p ≠ q) (hpv : hexOnLine pts p v = true)
    (hqv : hexOnLine pts q v = true) (hpw : hexOnLine pts p w = true)
    (hqw : hexOnLine pts q w = true) : False := by
  obtain ⟨-, hinc⟩ := hexIncOK_spec hi
  obtain ⟨kp, hkp, hpe⟩ := hexOnLine_iff.1 hpv
  obtain ⟨kq, hkq, hqe⟩ := hexOnLine_iff.1 hqv
  obtain ⟨kp', hkp', hpe'⟩ := hexOnLine_iff.1 hpw
  obtain ⟨kq', hkq', hqe'⟩ := hexOnLine_iff.1 hqw
  have hp819 : p < 819 := hpe ▸ hexPtsOK_lt hp hv hkp
  obtain ⟨i, hi9, hiv⟩ := hinc v hv kp hkp
  obtain ⟨j, hj9, hjw⟩ := hinc w hw kp' hkp'
  rw [hpe] at hiv
  rw [hpe'] at hjw
  have hij : i ≠ j := fun e => hvw (by rw [← hiv, ← hjw, e])
  have h1 := allLt_spec (allLt_spec (allLt_spec h hp819) hi9) hj9
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · exact hij h1
  have h2 := allLt_spec (allLt_spec h1 hkq) hkq'
  rw [hiv, hjw, hqe, hqe'] at h2
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_true_eq_false, or_false,
    or_self] at h2
  exact hpq h2.symm

@[expose] def LineMeet : Prop :=
  ∀ v w : Fin 2457, ∀ p q : Fin 819, p ≠ q → p ∈ hexLine v → q ∈ hexLine v → p ∈ hexLine w →
    q ∈ hexLine w → v = w

theorem lineMeet_of_check {ptL : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (h : hexMeetOK lineTab ptL = true) : LineMeet := by
  intro v w p q hpq hpv hqv hpw hqw
  by_contra hvw
  refine hexMeetOK_spec hp hi h v.2 w.2 (fun e => hvw (Fin.ext e)) (fun e => hpq (Fin.ext e))
    ((mem_hexLine_iff p v).1 hpv) ((mem_hexLine_iff q v).1 hqv) ((mem_hexLine_iff p w).1 hpw)
    ((mem_hexLine_iff q w).1 hqw)

theorem mem_hexNbr_point {pts ptL : Array ℕ} {p n : ℕ} (hp : p < 819) :
    n ∈ hexNbr pts ptL p ↔ ∃ k < 9, ptL[9 * p + k]! + 819 = n := by
  simp [hexNbr, hp, List.mem_map, List.mem_range]

theorem mem_hexNbr_line {pts ptL : Array ℕ} {v n : ℕ} :
    n ∈ hexNbr pts ptL (819 + v) ↔ ∃ k < 3, pts[3 * v + k]! = n := by
  have h : ¬ (819 + v < 819) := by omega
  simp [hexNbr, h, List.mem_map, List.mem_range]

theorem hexAdj_iff_nbr {ptL : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (x y : HexVtx) :
    hexGraph.Adj x y ↔ hexCode y ∈ hexNbr lineTab ptL (hexCode x) := by
  obtain ⟨hs, hc⟩ := hexIncOK_spec hi
  have hpp := hexPtsOK_spec hp
  cases x with
  | inl p =>
    cases y with
    | inl q =>
      constructor
      · intro h
        exact h.elim
      · intro h
        obtain ⟨k, hk, hk'⟩ := (mem_hexNbr_point (pts := lineTab) p.2).1 h
        have := q.2
        simp only [hexCode] at hk'
        omega
    | inr v =>
      simp only [hexCode]
      rw [hexGraph_adj_inl_inr, mem_hexLine_iff, hexOnLine_iff,
        mem_hexNbr_point (pts := lineTab) p.2]
      constructor
      · rintro ⟨k, hk, hkp⟩
        obtain ⟨j, hj, hjv⟩ := hc v v.2 k hk
        rw [hkp] at hjv
        exact ⟨j, hj, by omega⟩
      · rintro ⟨k, hk, hkv⟩
        obtain ⟨-, hon⟩ := hs p p.2 k hk
        have h2 : ptL[9 * (p : ℕ) + k]! = v := by omega
        rw [h2] at hon
        exact hexOnLine_iff.1 hon
  | inr v =>
    cases y with
    | inl q =>
      simp only [hexCode]
      rw [hexGraph_adj_inr_inl, mem_hexLine_iff, hexOnLine_iff, mem_hexNbr_line]
    | inr w =>
      constructor
      · intro h
        exact h.elim
      · intro h
        simp only [hexCode] at h
        obtain ⟨k, hk, hk'⟩ := mem_hexNbr_line.1 h
        obtain ⟨h1, h2, h3⟩ := hpp v v.2
        interval_cases k
        · simp only [Nat.add_zero] at hk'
          omega
        · omega
        · omega

theorem hexLayOK_spec {pts ptL : Array ℕ} {b : ℕ} {lay par : Array ℕ}
    (h : hexLayOK pts ptL b lay par = true) :
    b < 3276 ∧ lay[b]! = 0 ∧ ∀ x < 3276, lay[x]! ≤ 6 ∧
      (x = b ∨ (par[x]! < 3276 ∧ par[x]! ∈ hexNbr pts ptL x ∧ lay[par[x]!]! + 1 = lay[x]!)) ∧
      (∀ y ∈ hexNbr pts ptL x, lay[y]! ≤ lay[x]! + 1) ∧
      (lay[x]! = 0 ∨ 5 < lay[x]! ∨
        ∀ y ∈ hexNbr pts ptL x, lay[y]! + 1 ≠ lay[x]! ∨ y = par[x]!) := by
  simp only [hexLayOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hb, hl0⟩, hall⟩ := h
  refine ⟨hb, hl0, fun x hx => ?_⟩
  have := allLt_spec hall hx
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem, List.all_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨h1, ?_, h3, ?_⟩
  · rcases h2 with h2 | ⟨⟨h2a, h2b⟩, h2c⟩
    · exact Or.inl h2
    · exact Or.inr ⟨h2a, h2b, h2c⟩
  · rcases h4 with (h4 | h4) | h4
    · exact Or.inl h4
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr fun y hy => h4 y hy)

theorem layers_of_hexLayOK {ptL : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) {b : ℕ} {lay par : Array ℕ}
    (h : hexLayOK lineTab ptL b lay par = true) :
    Layers hexGraph 6 (hexOfCode b) (fun x => lay[hexCode x]!) := by
  obtain ⟨hb, hl0, hx⟩ := hexLayOK_spec h
  have hadj := hexAdj_iff_nbr hp hi
  have hcode : ∀ x y : HexVtx, hexGraph.Adj x y →
      hexCode y ∈ hexNbr lineTab ptL (hexCode x) := fun x y h => (hadj x y).1 h
  refine ⟨?_, fun x => (hx _ (hexCode_lt x)).1, ?_, ?_, ?_⟩
  · show lay[hexCode (hexOfCode b)]! = 0
    rw [hexCode_hexOfCode hb]
    exact hl0
  · intro x hxb
    have hne : hexCode x ≠ b := fun e => hxb (by rw [← hexOfCode_hexCode x, e])
    obtain ⟨-, h2, -⟩ := hx _ (hexCode_lt x)
    rcases h2 with h2 | ⟨h2a, h2b, h2c⟩
    · exact absurd h2 hne
    · refine ⟨hexOfCode (par[hexCode x]!), (hadj x _).2 ?_, ?_⟩
      · rw [hexCode_hexOfCode h2a]
        exact h2b
      · show lay[hexCode (hexOfCode par[hexCode x]!)]! + 1 = lay[hexCode x]!
        rw [hexCode_hexOfCode h2a]
        exact h2c
  · intro x y hxy
    obtain ⟨-, -, h3, -⟩ := hx _ (hexCode_lt x)
    exact h3 _ (hcode x y hxy)
  · intro x y z h1 h2 hxy hxz hy hz
    have h1' : 1 ≤ lay[hexCode x]! := h1
    have h2' : lay[hexCode x]! < 6 := h2
    have hy' : lay[hexCode y]! + 1 = lay[hexCode x]! := hy
    have hz' : lay[hexCode z]! + 1 = lay[hexCode x]! := hz
    obtain ⟨-, -, -, h4⟩ := hx _ (hexCode_lt x)
    rcases h4 with h4 | h4 | h4
    · omega
    · omega
    · rcases h4 _ (hcode x y hxy) with e1 | e1
      · exact absurd hy' e1
      rcases h4 _ (hcode x z hxz) with e2 | e2
      · exact absurd hz' e2
      exact hexCode_injective (e1.trans e2.symm)

theorem mem_hexNbr_lt {pts ptL : Array ℕ} (hp : hexPtsOK pts = true)
    (hi : hexIncOK pts ptL = true) {x n : ℕ} (hx : x < 3276) (h : n ∈ hexNbr pts ptL x) :
    n < 3276 := by
  by_cases hx1 : x < 819
  · obtain ⟨k, hk, hkn⟩ := (mem_hexNbr_point (pts := pts) (ptL := ptL) hx1).1 h
    have := ((hexIncOK_spec hi).1 x hx1 k hk).1
    omega
  · obtain ⟨v, rfl⟩ : ∃ v, x = 819 + v := ⟨x - 819, by omega⟩
    obtain ⟨k, hk, hkn⟩ := mem_hexNbr_line.1 h
    have := hexPtsOK_lt hp (v := v) (by omega) hk
    omega

theorem ncard_neighborSet_eq {ptL : Array ℕ} (hp : hexPtsOK lineTab = true)
    (hi : hexIncOK lineTab ptL = true) (x : HexVtx)
    (hnd : (hexNbr lineTab ptL (hexCode x)).Nodup) :
    (hexGraph.neighborSet x).ncard = (hexNbr lineTab ptL (hexCode x)).length := by
  have hset : hexCode '' (hexGraph.neighborSet x) =
      ↑((hexNbr lineTab ptL (hexCode x)).toFinset) := by
    ext n
    simp only [Set.mem_image, SimpleGraph.mem_neighborSet, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hexAdj_iff_nbr hp hi x y).1 hy
    · intro hn
      have hlt := mem_hexNbr_lt hp hi (hexCode_lt x) hn
      refine ⟨hexOfCode n, ?_, hexCode_hexOfCode hlt⟩
      rw [hexAdj_iff_nbr hp hi, hexCode_hexOfCode hlt]
      exact hn
  rw [← Set.ncard_image_of_injective _ hexCode_injective, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end CFSG.Quasithin.D4Hex

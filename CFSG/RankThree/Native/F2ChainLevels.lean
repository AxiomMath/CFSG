module

public import CFSG.RankThree.Native.F2Tail
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.LevelTrSound

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates.ChainArrays

@[expose] def PosOK (n : ℕ) (L : Level) : Prop := ∀ z < n, L.pos[z]! = n ∨ L.pos[z]! < L.pts.size

theorem posOK_of_st {n root : ℕ} {steps : Array (Array ℕ)}
    {st : Array ℕ × Array ℕ × Array ℕ × Array ℕ × Array (Array ℕ)}
    (h : ∃ a, st.2.1.size ≤ a ∧ Orb.Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1) :
    PosOK n ⟨st.2.1, st.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2, st.2.2.2.2.map (invCand n)⟩ := by
  obtain ⟨a, -, hI⟩ := h
  exact fun z hz => (hI.posz z hz).imp id (·.1)

theorem bfs_posOK {n root : ℕ} {steps : Array (Array ℕ)} (hr : root < n)
    (hs : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n) :
    PosOK n (CFSG.Monster.B.Co2.Native.bfs n root steps) := by
  unfold CFSG.Monster.B.Co2.Native.bfs
  simp only [Id.run_bind, Id.run_pure]
  refine posOK_of_st (forIn_range_idx n _ _
        (fun a (st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat)) =>
          Orb.Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        (fun st => ∃ a, st.2.1.size ≤ a ∧ Orb.Inv n root steps a 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        ?_ ?_ (fun b hb => ⟨n, hb.le, hb⟩))
  · exact inv_init hr
  · intro a _ b hb
    split
    · rename_i hab
      simp only [Id.run_bind, Id.run_pure]
      refine stepP_yield_of (forIn_range_idx steps.size _ _
        (fun j (st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat)) =>
          Orb.Inv n root steps a j st.1 st.2.1 st.2.2.1 st.2.2.2.1 ∧ a < st.2.1.size ∧
            st.2.1[a]! = b.2.1[a]!)
        (fun st => Orb.Inv n root steps (a + 1) 0 st.1 st.2.1 st.2.2.1 st.2.2.2.1)
        ⟨hb, hab, rfl⟩ ?_ (fun st hst => inv_next hst.1 hst.2.1))
      intro j hj st hst
      obtain ⟨hI, ha, hx⟩ := hst
      have hxn : st.2.1[a]! < n := (hI.pt a ha).1
      split
      · rename_i hy
        dsimp only [StepP]
        rw [← hx]
        rw [← hx, beq_iff_eq] at hy
        refine ⟨inv_push hI ha hj (hs j hj) hy, by simp; omega, ?_⟩
        rw [push_get_lt ha]
      · rename_i hy
        dsimp only [StepP]
        rw [← hx, beq_iff_eq] at hy
        exact ⟨inv_skip hI (hs j hj _ hxn) hy, ha, hx⟩
    · rename_i hab
      exact ⟨a, Nat.le_of_not_lt hab, hb⟩

theorem bfs_trInv_eq (n root : ℕ) (steps : Array (Array ℕ)) :
    (CFSG.Monster.B.Co2.Native.bfs n root steps).trInv =
      (CFSG.Monster.B.Co2.Native.bfs n root steps).tr.map (invCand n) := rfl

theorem recOK_levelM {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {I root m r : ℕ}
    {PT PO PA LB : ℕ → ℕ} {ED : ℕ → ℕ → ℕ} {SM SIM TM TIM : ℕ → ℕ}
    (h : levelM vm mm I V.size VG root m r PT PO PA LB ED SM SIM TM TIM = true) :
    RecOK V.size root r (fun j x => vidx V (vmul d V[x]! (SM j))) m PT PO PA LB ∧
      (∀ z < V.size, PO z = V.size ∨ PO z < m) := by
  simp only [levelM, levelHd, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm0, hmn⟩, hroot⟩, -⟩, -⟩, -⟩, -⟩, hpt⟩, hpo⟩, hpar⟩, hmono⟩, hedge⟩ := h
  have hpt' : ∀ k < m, PT k < V.size ∧ PO (PT k) = k := fun k hk => by
    have := allN_spec hpt k hk
    simpa only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using this
  have hpo' : ∀ z < V.size, (PO z < m ∧ PT (PO z) = z) ∨ PO z = V.size := fun z hz => by
    have := allN_spec hpo z hz
    simpa only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] using this
  have hst : ∀ x < V.size, ∀ j, vidx V (vmul d V[x]! (SM j)) = vidx V (vm (VG x) (SM j)) :=
    fun x hx j => by rw [hs.vg x hx, hvm]
  have hloc : ∀ k < m, vidx V (VG (PT k)) = PT k := fun k hk => hs.vidx_eq (hpt' k hk).1
  have hpar' : ∀ k < m, 0 < k → PA k < k ∧ LB k < r ∧
      VG (PT k) = vm (VG (PT (PA k))) (SM (LB k)) := fun k hk hk0 => by
    have := allN_spec hpar k hk
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at this
    rcases this with h0 | ⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩
    · omega
    · exact ⟨h1, h2, h3⟩
  have hedge' : ∀ h < m, ∀ j < r, ED h j < m ∧ VG (PT (ED h j)) = vm (VG (PT h)) (SM j) ∧
      (ED h j = 0 ∨ lexLtN h j (PA (ED h j)) (LB (ED h j)) = false) := fun h hh j hj => by
    have := allN_spec (allN_spec hedge h hh) j hj
    simp only [edgeM, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hlex : ∀ a b c e, lexLtN a b c e = true ↔ LexLt a b c e := fun a b c e => by
    simp [lexLtN, LexLt]
  refine ⟨⟨hm0, hroot, hpt', fun z hz hq => ?_, fun k hk hk0 => (hpar' k hk hk0).1,
    fun k hk hk0 => (hpar' k hk hk0).2.1, fun k hk hk0 => ?_, fun k hk hk0 hk1 => ?_,
    fun h hh j hj => ?_⟩, fun z hz => (hpo' z hz).elim (fun h => Or.inr h.1) Or.inl⟩
  · rcases hpo' z hz with h | h
    · exact h.2
    · omega
  · obtain ⟨h1, -, h3⟩ := hpar' k hk hk0
    rw [hst _ (hpt' _ (by omega)).1, ← h3, hloc k hk]
  · have := allN_spec hmono k hk
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true', Nat.blt_eq] at this
    rcases this with (h | h) | h
    · omega
    · rw [Nat.blt_eq.mpr hk1] at h
      simp at h
    · exact (hlex _ _ _ _).1 h
  · obtain ⟨e1, e2, e3⟩ := hedge' h hh j hj
    rw [hst _ (hpt' h hh).1, ← e2, hloc _ e1, (hpt' _ e1).2]
    refine ⟨e1, e3.imp id fun e => fun hl => ?_⟩
    rw [← hlex] at hl
    rw [hl] at e
    simp at e

theorem fixesFirst_permOfMat {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {M : ℕ}
    (hM : ∀ v ∈ V, vmul d v M ∈ V) {base : Array ℕ} {BS : ℕ → ℕ} {i : ℕ}
    (hBS : ∀ t < i, base[t]! = BS t) (hb : ∀ t < i, BS t < V.size) :
    fixesFirst base (permOfMat d V M) i = allN i fun t => Nat.beq (vm (VG (BS t)) M) (VG (BS t)) := by
  have key : ∀ t < i, ((permOfMat d V M)[base[t]!]! == base[t]!) =
      Nat.beq (vm (VG (BS t)) M) (VG (BS t)) := fun t ht => by
    rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, hBS t ht, permOfMat_get (hb t ht),
      hs.vg _ (hb t ht), hvm]
    have hm := hM _ (hs.mem (hb t ht))
    constructor
    · intro e
      rw [← (getElem_vidx hm).2, e, hs.vg _ (hb t ht)]
    · intro e
      rw [e]
      exact hs.vidx_eq (hb t ht)
  rw [Bool.eq_iff_iff, fixesFirst, allLt_iff]
  constructor
  · intro h
    exact CFSG.KS.PackFld.allN_of_forall fun t ht => (key t ht) ▸ h t ht
  · intro h t ht
    rw [key t ht]
    exact allN_spec h t ht

theorem stepsM_eq {vm : ℕ → ℕ → ℕ} {VG MS : ℕ → ℕ} {kS : ℕ} {BS : ℕ → ℕ} {i c : ℕ}
    {IX : ℕ → ℕ} (h : stepsM vm VG MS kS BS i c IX = true) :
    (List.range kS).filter (fun j => allN i fun t => Nat.beq (vm (VG (BS t)) (MS j)) (VG (BS t))) =
      (List.range c).map IX :=
  eq_of_beq h

theorem stepsIdx_lt {vm : ℕ → ℕ → ℕ} {VG MS : ℕ → ℕ} {kS : ℕ} {BS : ℕ → ℕ} {i c : ℕ}
    {IX : ℕ → ℕ} (h : stepsM vm VG MS kS BS i c IX = true) {t : ℕ} (ht : t < c) : IX t < kS := by
  have hm : IX t ∈ (List.range c).map IX := List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩
  rw [← stepsM_eq h, List.mem_filter, List.mem_range] at hm
  exact hm.1

theorem rawSteps_eq {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M)
    {S : Array (Array ℕ)} {MS MSI : ℕ → ℕ}
    (hS : ∀ j < S.size, S[j]! = permOfMat d V (MS j)) (hSI : ∀ j < S.size, Inv d V (MS j) (MSI j))
    {base : Array ℕ} {BS : ℕ → ℕ} {i c : ℕ} {IX : ℕ → ℕ}
    (hBS : ∀ t < i, base[t]! = BS t) (hb : ∀ t < i, BS t < V.size)
    (hst : stepsM vm VG MS S.size BS i c IX = true) :
    (rawSteps V.size S base i).size = c + c ∧
      ∀ j < c + c, (rawSteps V.size S base i)[j]! = permOfMat d V (stepM MS MSI IX c j) := by
  have hL : levelIdx S base i = (List.range c).map IX := by
    rw [← stepsM_eq hst, levelIdx]
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [hS j hj']
    exact fixesFirst_permOfMat hs hvm (hSI j hj').1 hBS hb
  have hlt : ∀ t < c, IX t < S.size := fun t ht => stepsIdx_lt hst ht
  have e : rawSteps V.size S base i = (((List.range c).map fun t => S[IX t]!) ++
      ((List.range c).map fun t => (rawInvs V.size S)[IX t]!)).toArray := by
    rw [rawSteps, levelSteps, hL, List.map_map, List.map_map, ← List.append_toArray]
    rfl
  refine ⟨by rw [e]; simp, fun j hj => ?_⟩
  rw [e, getElem!_pos _ j (by simp; omega), List.getElem_toArray]
  by_cases hjc : j < c
  · rw [List.getElem_append_left (by simpa using hjc), List.getElem_map, List.getElem_range,
      stepM, if_pos hjc, hS _ (hlt j hjc)]
  · rw [List.getElem_append_right (by simpa using hjc)]
    simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
    have hk := hlt (j - c) (by omega)
    rw [stepM, if_neg hjc, rawInvs, getElem!_pos _ _ (by simpa using hk), Array.getElem_map,
      ← getElem!_pos S _ hk, hS _ hk, invCand_permOfMat hs.hd hs.nodup hs.lt (hSI _ hk)]

theorem arr_eq_of_rep' {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : t.size = n)
    (hu : u.size = n) (hgt : Rep n t g) (hgu : Rep n u g) : t = u := by
  apply Array.ext (by rw [ht, hu])
  intro i h1 h2
  rw [← getElem!_pos t i h1, ← getElem!_pos u i h2, hgt.apply (ht ▸ h1), hgu.apply (ht ▸ h1)]

theorem sigma_idM' {d : ℕ} {V : Array ℕ} (hd : 0 < d) (hV : V.toList.Nodup)
    (hVd : ∀ v ∈ V, v < 2 ^ d) : sigma d V (idM d) = 1 := by
  have h := rep_permOfMat hd hV hVd (inv_idM hd hVd)
  rw [permOfMat_idM hd hV hVd] at h
  exact h.unique rep_idA

theorem level_agree {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {I : ℕ} (hI : I = idM d)
    {S : Array (Array ℕ)} {MS MSI : ℕ → ℕ}
    (hS : ∀ j < S.size, S[j]! = permOfMat d V (MS j)) (hSI : ∀ j < S.size, Inv d V (MS j) (MSI j))
    {base : Array ℕ} {i root : ℕ} (hroot : base[i]! = root) (hr : root < V.size)
    {BS : ℕ → ℕ} (hBS : ∀ t < i, base[t]! = BS t) (hb : ∀ t < i, BS t < V.size)
    {m c : ℕ} {IX PT PO PA LB TM TIM : ℕ → ℕ} {ED : ℕ → ℕ → ℕ}
    (hst : stepsM vm VG MS S.size BS i c IX = true)
    (hl : levelM vm mm I V.size VG root m (c + c) PT PO PA LB ED (stepM MS MSI IX c)
      (stepIM MS MSI IX c) TM TIM = true)
    (hinv : ∀ k < m, Inv d V (TM k) (TIM k)) (hi : i < base.size) :
    (rawLevels V.size S base)[i]!.pts.size = m ∧
      (∀ k < m, (rawLevels V.size S base)[i]!.pts[k]! = PT k) ∧
      (∀ x < V.size, (rawLevels V.size S base)[i]!.pos[x]! = PO x) ∧
      (∀ k < m, (rawLevels V.size S base)[i]!.tr[k]! = permOfMat d V (TM k)) ∧
      (∀ k < m, (rawLevels V.size S base)[i]!.trInv[k]! = permOfMat d V (TIM k)) := by
  have hd := hs.hd
  obtain ⟨hsz, hstep⟩ := rawSteps_eq hs hvm hS hSI hBS hb hst
  set n := V.size with hn
  set SM := stepM MS MSI IX c
  set steps := rawSteps n S base i
  have hlt : ∀ t < c, IX t < S.size := fun t ht => stepsIdx_lt hst ht
  have hSMi : ∀ j < c + c, Inv d V (SM j) (stepIM MS MSI IX c j) := fun j hj => by
    simp only [SM, stepM, stepIM]
    split
    · exact hSI _ (hlt j (by omega))
    · exact (hSI _ (hlt (j - c) (by omega))).symm
  have hSIM : ∀ j < c + c, ∃ M', Inv d V (SM j) M' := fun j hj => ⟨_, hSMi j hj⟩
  have hrep : ∀ j < steps.size, Rep n steps[j]! (sigma d V (SM j)) := fun j hj => by
    rw [hstep j (hsz ▸ hj)]
    exact rep_permOfMat hd hs.nodup hs.lt (hSMi j (hsz ▸ hj))
  have hcl : ∀ j < steps.size, ∀ x < n, (steps[j]!)[x]! < n := fun j hj x hx => (hrep j hj).lt hx
  have hL : (rawLevels n S base)[i]! = CFSG.Monster.B.Co2.Native.bfs n root steps := by
    rw [rawLevels_get hi, hroot]
  rw [hL]
  set L := CFSG.Monster.B.Co2.Native.bfs n root steps
  have F : LevelFacts n root steps L :=
    levelFacts_of_levelOK (levelOK_of (levelOKT_bfs hr hcl)
      (levelTrOK_bfs fun j hj => ⟨_, hrep j hj⟩))
  have NR := recOK_native F
  obtain ⟨KR0, hPOn⟩ := recOK_levelM hs hvm hl
  have KR := KR0.congr (st' := fun j x => (steps[j]!)[x]!) fun j hj x hx => by
    rw [hstep j hj, permOfMat_get hx]
  rw [← hsz] at KR
  have hσ : ∀ j < steps.size, ∀ x : Fin n, (steps[j]!)[(x : ℕ)]! = (sigma d V (SM j) x : ℕ) :=
    fun j hj x => hrep j hj x
  have hT0 : sigma d V (TM 0) = 1 := by
    have h0 : TM 0 = I := by
      simp only [levelM, levelHd, Bool.and_eq_true, Nat.beq_eq] at hl
      exact hl.1.1.1.1.1.1.2
    rw [h0, hI]
    exact sigma_idM' hd hs.nodup hs.lt
  have hT : ∀ k < m, 0 < k → sigma d V (TM k) = sigma d V (SM (LB k)) * sigma d V (TM (PA k)) := by
    intro k hk hk0
    have hp := KR0.par_lt k hk hk0
    have hlb := KR0.lab_lt k hk hk0
    have e : TM k = mm (TM (PA k)) (SM (LB k)) := by
      simp only [levelM, levelHd, Bool.and_eq_true] at hl
      have := allN_spec hl.1.1.2 k hk
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at this
      rcases this with h0 | ⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩
      · omega
      · exact h4
    rw [e, hmm]
    exact sigma_mmul hd hs.nodup hs.lt (hinv _ (by omega)) (hSMi _ hlb)
      ((hinv _ (by omega)).mul hd (hSMi _ hlb))
  obtain ⟨T0N, TSN⟩ := native_T F (fun j hj => hrep j hj)
  obtain ⟨hc, hPT, hQ⟩ := rec_agree (T := fun k => sigma d V (TM k))
    (T' := fun k => permOfArr n L.tr[k]!) (by omega) hr KR NR hσ hT0 hT T0N TSN
  have hpos := bfs_posOK (n := n) hr hcl
  refine ⟨hc.symm, fun k hk => (hPT k hk).1.symm, fun x hx => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · by_cases hq : PO x < m
    · exact ((hQ x hx).2 hq).symm
    · have h1 : PO x = n := (hPOn x hx).resolve_right hq
      have h2 : ¬ L.pos[x]! < L.pts.size := fun h => hq ((hQ x hx).1.2 h)
      rw [h1]
      exact (hpos x hx).resolve_right h2
  · have hk' : k < L.pts.size := by omega
    have r1 : Rep n L.tr[k]! (sigma d V (TM k)) := by
      rw [(hPT k hk).2]
      exact (rep_permOfArr (F.tr_inv k hk')).1
    exact arr_eq_of_rep' (bfs_tr_size hk') (permOfMat_size _ _) r1
      (rep_permOfMat hd hs.nodup hs.lt (hinv k hk))
  · have hk' : k < L.pts.size := by omega
    have r1 : Rep n L.tr[k]! (sigma d V (TM k)) := by
      rw [(hPT k hk).2]
      exact (rep_permOfArr (F.tr_inv k hk')).1
    have etr : L.tr[k]! = permOfMat d V (TM k) := arr_eq_of_rep' (bfs_tr_size hk')
      (permOfMat_size _ _) r1 (rep_permOfMat hd hs.nodup hs.lt (hinv k hk))
    have htrs : k < L.tr.size := by
      by_contra hc'
      have h := bfs_tr_size (n := n) (root := root) (steps := steps) hk'
      have e : L.tr[k]! = default := getElem!_neg L.tr k hc'
      rw [e] at h
      have hn0 : 0 < n := by omega
      have h0 : (default : Array ℕ).size = 0 := rfl
      omega
    rw [bfs_trInv_eq, getElem!_pos _ k (by simpa using htrs), Array.getElem_map,
      ← getElem!_pos _ k htrs, etr, invCand_permOfMat hd hs.nodup hs.lt (hinv k hk)]

theorem levFacts_rawLevels {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {I : ℕ} (hI : I = idM d)
    {S : Array (Array ℕ)} {MS MSI : ℕ → ℕ}
    (hS : ∀ j < S.size, S[j]! = permOfMat d V (MS j)) (hSI : ∀ j < S.size, Inv d V (MS j) (MSI j))
    {base : Array ℕ} {BS : ℕ → ℕ} (hBS : ∀ i < base.size, base[i]! = BS i)
    (hb : ∀ i < base.size, BS i < V.size)
    {m c : ℕ → ℕ} {IX PT PO PA LB TM TIM : ℕ → ℕ → ℕ} {ED : ℕ → ℕ → ℕ → ℕ}
    (hsteps : ∀ i < base.size, stepsM vm VG MS S.size BS i (c i) (IX i) = true)
    (hlev : ∀ i < base.size, levelM vm mm I V.size VG (BS i) (m i) (c i + c i) (PT i) (PO i)
      (PA i) (LB i) (ED i) (stepM MS MSI (IX i) (c i)) (stepIM MS MSI (IX i) (c i)) (TM i)
      (TIM i) = true) :
    LevFacts d V (rawLevels V.size S base) base.size m PT PO TM TIM := by
  have hd := hs.hd
  have hlv : ∀ l < base.size, ∀ k < m l, Inv d V (TM l k) (TIM l k) := fun l hl =>
    levelM_inv hd hs.lt hmm hI (fun j hj => by
      unfold stepM stepIM
      split
      · exact hSI _ (stepsIdx_lt (hsteps l hl) (by omega))
      · exact (hSI _ (stepsIdx_lt (hsteps l hl) (by omega))).symm) (hlev l hl)
  have H : ∀ l < base.size, (rawLevels V.size S base)[l]!.pts.size = m l ∧
      (∀ k < m l, (rawLevels V.size S base)[l]!.pts[k]! = PT l k) ∧
      (∀ x < V.size, (rawLevels V.size S base)[l]!.pos[x]! = PO l x) ∧
      (∀ k < m l, (rawLevels V.size S base)[l]!.tr[k]! = permOfMat d V (TM l k)) ∧
      (∀ k < m l, (rawLevels V.size S base)[l]!.trInv[k]! = permOfMat d V (TIM l k)) :=
    fun l hl => level_agree hs hvm hmm hI hS hSI (hBS l hl) (hb l hl)
      (fun t ht => hBS t (by omega)) (fun t ht => hb t (by omega)) (hsteps l hl) (hlev l hl)
      (hlv l hl) hl
  refine ⟨by simp [rawLevels], fun l hl => (H l hl).1, fun l hl => (H l hl).2.1,
    fun l hl k hk => (levelM_pts (hlev l hl) k hk).1,
    fun l hl k hk => (levelM_pts (hlev l hl) k hk).2, fun l hl => (H l hl).2.2.1,
    fun l hl => (H l hl).2.2.2.1, fun l hl => (H l hl).2.2.2.2, hlv⟩

end CFSG.RankThree.Native.F2

end

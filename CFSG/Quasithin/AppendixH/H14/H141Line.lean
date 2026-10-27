module

public import CFSG.Quasithin.AppendixH.H14.H141T1
public import CFSG.Quasithin.AppendixH.H14.H141Transport
public import CFSG.Quasithin.AppendixH.H14.H141S2
public import CFSG.Quasithin.AppendixH.Common.OctadTwoCore

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.GH74.KGroups CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H158T CFSG.ASVolI.ChH
  CFSG.ASVolI.AppH CFSG.Monster.Code CFSG.Open CFSG.Quasithin

@[expose] def lineCodes : List ℕ := [0, 17, 34, 51]

@[expose] def fixesO2 (n : ℕ) : Bool :=
  (List.range 24).all fun i => !(9857280 : ℕ).testBit i || (tabS[n]!)[i]! == i

lemma lineCodes_lt : ∀ n ∈ lineCodes, n < 64 := by decide

lemma lineCodes_nodup : lineCodes.Nodup := by decide

lemma testBit_mask_o2F (i : Fin 24) : (9857280 : ℕ).testBit (i : ℕ) = true ↔ i ∈ o2F := by
  fin_cases i <;> decide

theorem fixesO2_iff : ∀ n < 64, fixesO2 n = true ↔ n ∈ lineCodes := by
  decide +kernel

theorem psi_mem_octFix_iff {n : ℕ} (hn : n < 64) :
    tab64Perm tabS n ∈ octFix o2F ↔ n ∈ lineCodes := by
  have hM : tab64Perm tabS n ∈ M24g := tab64Perm_mem_M24g tabS_ok hn
  have harr : HasArr (tab64Perm tabS n) tabS[n]! := hasArr_tab64Perm tabS_ok hn
  have hfix : (∀ i ∈ o2F, tab64Perm tabS n i = i) ↔ fixesO2 n = true := by
    rw [fixesO2, List.all_eq_true]
    constructor
    · intro h i hi
      rw [List.mem_range] at hi
      by_cases hb : (9857280 : ℕ).testBit i = true
      · have hmem : (⟨i, hi⟩ : Fin 24) ∈ o2F := (testBit_mask_o2F ⟨i, hi⟩).mp hb
        have hnat : (tabS[n]!)[i]! = i := by
          have h1 := congrArg Fin.val (h ⟨i, hi⟩ hmem)
          rw [harr ⟨i, hi⟩] at h1
          exact h1
        simp only [hb, Bool.not_true, Bool.false_or, beq_iff_eq, hnat]
      · have hb' : (9857280 : ℕ).testBit i = false := Bool.eq_false_iff.mpr hb
        simp only [hb', Bool.not_false, Bool.true_or]
    · intro h i hi
      have hbit : (9857280 : ℕ).testBit (i : ℕ) = true := (testBit_mask_o2F i).mpr hi
      have hc := h (i : ℕ) (List.mem_range.mpr i.isLt)
      rw [hbit, Bool.not_true, Bool.false_or] at hc
      have hnat : (tabS[n]!)[(i : ℕ)]! = (i : ℕ) := beq_iff_eq.mp hc
      exact Fin.ext (by rw [harr i, hnat])
  rw [mem_octFix_iff]
  constructor
  · rintro ⟨-, hf⟩
    exact (fixesO2_iff n hn).mp (hfix.mp hf)
  · intro hline
    exact ⟨hM, hfix.mpr ((fixesO2_iff n hn).mpr hline)⟩

theorem mem_line_iff {x : S24} :
    x ∈ octFix o2F ⊓ tab64Sub tabS tabS_ok ↔ ∃ n ∈ lineCodes, x = tab64Perm tabS n := by
  constructor
  · intro hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxO, hxK⟩ := hx
    obtain ⟨n, hn, rfl⟩ := (mem_tab64Sub tabS_ok).mp hxK
    exact ⟨n, (psi_mem_octFix_iff hn).mp hxO, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    rw [Subgroup.mem_inf, mem_tab64Sub tabS_ok]
    exact ⟨(psi_mem_octFix_iff (lineCodes_lt n hn)).mpr hn,
      ⟨n, lineCodes_lt n hn, rfl⟩⟩

theorem isE2k_line : IsE2k 2 (octFix o2F ⊓ tab64Sub tabS tabS_ok) := by
  set A : Subgroup S24 := octFix o2F ⊓ tab64Sub tabS tabS_ok with hA
  have hAK : A ≤ tab64Sub tabS tabS_ok := hA ▸ inf_le_right
  unfold IsE2k IsElemAbelian
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    show (x : S24) * (y : S24) = (y : S24) * (x : S24)
    obtain ⟨n, hn, hxn⟩ := (mem_tab64Sub tabS_ok).mp (hAK x.2)
    obtain ⟨m, hm, hym⟩ := (mem_tab64Sub tabS_ok).mp (hAK y.2)
    rw [hxn, hym]
    exact tab64Perm_comm tabS_ok hn hm
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := (mem_tab64Sub tabS_ok).mp (hAK hx)
    rw [hxn]
    simpa [pow_two] using tab64Perm_mul_self tabS_ok hn
  · let f : Fin lineCodes.length → ↥A := fun i =>
      ⟨tab64Perm tabS (lineCodes.get i), by
        rw [hA]
        exact mem_line_iff.mpr ⟨lineCodes.get i, List.get_mem _ _, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        have h1 : tab64Perm tabS (lineCodes.get i) = tab64Perm tabS (lineCodes.get j) :=
          congrArg Subtype.val hij
        have h2 := tab64Perm_inj tabS_ok (lineCodes_lt _ (List.get_mem _ _))
          (lineCodes_lt _ (List.get_mem _ _)) h1
        exact (List.Nodup.get_inj_iff lineCodes_nodup).mp h2
      · intro y
        obtain ⟨n, hn, hy⟩ := mem_line_iff.mp (by rw [← hA]; exact y.2)
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hn
        refine ⟨i, ?_⟩
        apply Subtype.ext
        show tab64Perm tabS (lineCodes.get i) = (y : S24)
        rw [hi]
        exact hy.symm
    calc Nat.card ↥A = Nat.card (Fin lineCodes.length) :=
          (Nat.card_congr (Equiv.ofBijective f hf)).symm
      _ = 4 := by simp [lineCodes]

lemma wOfCode3_ne_zero_17 : wOfCode3 17 ≠ 0 := by
  intro h
  have h' : wOfCode3 17 = wOfCode3 0 := by rw [h, wOfCode3_zero]
  have hlt1 : (17 : ℕ) ∈ {n : ℕ | n < 64} := by norm_num
  have hlt0 : (0 : ℕ) ∈ {n : ℕ | n < 64} := by norm_num
  have := wOfCode3_injOn hlt1 hlt0 h'
  norm_num at this

lemma lineCodes_iff_smul {n : ℕ} (hn : n < 64) :
    n ∈ lineCodes ↔ ∃ c : GF4, wOfCode3 n = c • wOfCode3 17 := by
  rw [lineCodes]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by rw [wOfCode3_zero, zero_smul]⟩
    · exact ⟨1, by rw [one_smul]⟩
    · refine ⟨GF4.ofNat' 2, ?_⟩
      have h : (34 : ℕ) = smulCode3 2 17 := by decide +kernel
      rw [h, wOfCode3_smulCode3 (by norm_num) (by norm_num)]
    · refine ⟨GF4.ofNat' 3, ?_⟩
      have h : (51 : ℕ) = smulCode3 3 17 := by decide +kernel
      rw [h, wOfCode3_smulCode3 (by norm_num) (by norm_num)]
  · rintro ⟨c, hc⟩
    have hd : c.toNat < 4 := c.val.isLt
    have h1 : wOfCode3 n = wOfCode3 (smulCode3 c.toNat 17) := by
      rw [wOfCode3_smulCode3 hd (by norm_num), gf4_ofNat_toNat]
      exact hc
    have h2 : n = smulCode3 c.toNat 17 :=
      wOfCode3_injOn hn (smulCode3_lt c.toNat 17 hd (by norm_num)) h1
    rw [h2]
    interval_cases c.toNat <;> decide +kernel

theorem line_isF4line : ∃ w : Fin 3 → GF4, w ≠ 0 ∧ ∀ k : ↥(tab64Sub tabS tabS_ok),
    (k : S24) ∈ octFix o2F ⊓ tab64Sub tabS tabS_ok ↔
      ∃ c : GF4, Multiplicative.toAdd (tab64Equiv tabS_ok coordF4 k) = c • w := by
  refine ⟨wOfCode3 17, wOfCode3_ne_zero_17, ?_⟩
  intro k
  obtain ⟨n, hn, hkn⟩ := (mem_tab64Sub tabS_ok).mp k.2
  have hkeq : k = ⟨tab64Perm tabS n, tab64Perm_mem_tab64Sub tabS_ok hn⟩ := Subtype.ext hkn
  have hcoord : Multiplicative.toAdd (tab64Equiv tabS_ok coordF4 k) = wOfCode3 n := by
    rw [hkeq, tab64Equiv_apply tabS_ok coordF4 hn]
    rfl
  have hLHS : (k : S24) ∈ octFix o2F ⊓ tab64Sub tabS tabS_ok ↔ n ∈ lineCodes := by
    rw [hkn, Subgroup.mem_inf, mem_tab64Sub tabS_ok]
    constructor
    · rintro ⟨h1, -⟩
      exact (psi_mem_octFix_iff hn).mp h1
    · intro h
      exact ⟨(psi_mem_octFix_iff hn).mpr h, ⟨n, hn, rfl⟩⟩
  rw [hcoord, hLHS]
  exact lineCodes_iff_smul hn

@[expose] def lineOfSt (st : ℕ) : List ℕ := [0, linAct st 17, linAct st 34, linAct st 51]

@[expose] def sameLine (s t : ℕ) : Bool :=
  (lineOfSt s).all (fun x => (lineOfSt t).contains x) &&
    (lineOfSt t).all (fun x => (lineOfSt s).contains x)

lemma lineOfSt_lt {st n : ℕ} (hn : n ∈ lineOfSt st) : n < 64 := by
  rw [lineOfSt] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · norm_num
  · exact linAct_lt st 17
  · exact linAct_lt st 34
  · exact linAct_lt st 51

lemma linAct_mem_lineOfSt (st : ℕ) {m : ℕ} (hm : m ∈ lineCodes) : linAct st m ∈ lineOfSt st := by
  rw [lineCodes] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · rw [linAct_zero]; simp [lineOfSt]
  · simp [lineOfSt]
  · simp [lineOfSt]
  · simp [lineOfSt]

lemma exists_code_of_mem_lineOfSt {st n : ℕ} (hn : n ∈ lineOfSt st) :
    ∃ m ∈ lineCodes, n = linAct st m := by
  rw [lineOfSt] at hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, by rw [linAct_zero]⟩
  · exact ⟨17, by decide, rfl⟩
  · exact ⟨34, by decide, rfl⟩
  · exact ⟨51, by decide, rfl⟩

lemma sameLine_comm (s t : ℕ) : sameLine s t = sameLine t s := by
  unfold sameLine
  rw [Bool.and_comm]

lemma mem_lineOfSt_iff_of_sameLine {s t n : ℕ} (h : sameLine s t = true) :
    n ∈ lineOfSt s ↔ n ∈ lineOfSt t := by
  unfold sameLine at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hn
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h1 n hn)
  · intro hn
    exact List.contains_iff_mem.mp (List.all_eq_true.mp h2 n hn)

@[expose] def repStates : List ℕ :=
  [34630287489, 2205840132, 58437191728, 13033463399, 34644861196, 45457576065, 1126190509,
    2210466297, 32883169328, 51810189378, 13019396955, 34640083605, 58749747329, 48773483552,
    61707685845]

theorem repStates_length : repStates.length = 15 := by
  decide +kernel

theorem repStates_sub : repStates.all (fun s => (bfsS.map Prod.fst).contains s) = true := by
  decide +kernel

theorem repStates_cover : bfsS.all (fun e => repStates.any (sameLine e.1)) = true := by
  decide +kernel

theorem repStates_distinct : repStates.Pairwise (fun s t => sameLine s t = false) := by
  decide +kernel

theorem mem_conjSubg_line_iff {g : S24} {st : ℕ}
    (hst : ∀ n < 64, g * tab64Perm tabS n * g⁻¹ = tab64Perm tabS (linAct st n)) {n : ℕ}
    (hn : n < 64) :
    tab64Perm tabS n ∈ conjSubg g (octFix o2F ⊓ tab64Sub tabS tabS_ok) ↔ n ∈ lineOfSt st := by
  constructor
  · intro hx
    rw [conjSubg, Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    obtain ⟨m, hm, hym⟩ := mem_line_iff.mp hy
    rw [hym] at hyx
    have hm64 : m < 64 := lineCodes_lt m hm
    have hconj := hst m hm64
    have hψ : tab64Perm tabS (linAct st m) = tab64Perm tabS n := by rw [← hconj]; exact hyx
    have hm_eq : linAct st m = n := tab64Perm_inj tabS_ok (linAct_lt st m) hn hψ
    rw [← hm_eq]
    exact linAct_mem_lineOfSt st hm
  · intro hx
    rw [conjSubg, Subgroup.mem_map]
    obtain ⟨m, hm, hnm⟩ := exists_code_of_mem_lineOfSt hx
    refine ⟨tab64Perm tabS m, mem_line_iff.mpr ⟨m, hm, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hnm]
    exact hst m (lineCodes_lt m hm)

theorem eq_of_psi_mem_iff {A B : Subgroup S24} (hA : A ≤ tab64Sub tabS tabS_ok)
    (hB : B ≤ tab64Sub tabS tabS_ok)
    (h : ∀ n < 64, tab64Perm tabS n ∈ A ↔ tab64Perm tabS n ∈ B) : A = B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := (mem_tab64Sub tabS_ok).mp (hA hx)
    exact (h n hn).mp hx
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := (mem_tab64Sub tabS_ok).mp (hB hx)
    exact (h n hn).mpr hx

theorem ncard_conjugates_line :
    Set.ncard {C : Subgroup S24 | ∃ g ∈ MY M24g stdS,
      C = conjSubg g (octFix o2F ⊓ tab64Sub tabS tabS_ok)} = 15 := by
  classical
  set LS : Subgroup S24 := octFix o2F ⊓ tab64Sub tabS tabS_ok with hLS
  set G : Subgroup S24 := MY M24g stdS with hG
  have hLK : LS ≤ tab64Sub tabS tabS_ok := hLS ▸ inf_le_right
  have hconj_le : ∀ g ∈ G, conjSubg g LS ≤ tab64Sub tabS tabS_ok := by
    intro g hg y hy
    rw [conjSubg, Subgroup.mem_map] at hy
    obtain ⟨l, hl, hly⟩ := hy
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hly
    rw [← hly]
    exact engine_S.normal g (hG ▸ hg) l (hLK hl)
  have rep_mem : ∀ i : Fin repStates.length, repStates.get i ∈ bfsS.map Prod.fst := by
    intro i
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp repStates_sub (repStates.get i) (List.get_mem _ i))
  let x : Fin repStates.length → S24 := fun i =>
    Classical.choose (engine_S.realize (repStates.get i) (rep_mem i))
  have x_spec : ∀ i, x i ∈ G ∧
      ∀ n < 64, x i * tab64Perm tabS n * (x i)⁻¹ =
        tab64Perm tabS (linAct (repStates.get i) n) :=
    fun i => Classical.choose_spec (engine_S.realize (repStates.get i) (rep_mem i))
  have cover : ∀ s ∈ bfsS.map Prod.fst, ∃ i : Fin repStates.length,
      sameLine s (repStates.get i) = true := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    have hall := List.all_eq_true.mp repStates_cover e he
    obtain ⟨a, ha, hsa⟩ := List.any_eq_true.mp hall
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    exact ⟨i, by rwa [← hi] at hsa⟩
  let f : Fin repStates.length → Subgroup S24 := fun i => conjSubg (x i) LS
  have hPf : {C : Subgroup S24 | ∃ g ∈ G, C = conjSubg g LS} = Set.range f := by
    ext C
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨st, hst, hact⟩ := engine_S.action g (hG ▸ hg)
      obtain ⟨i, hi⟩ := cover st hst
      refine ⟨i, ?_⟩
      change conjSubg (x i) LS = conjSubg g LS
      apply eq_of_psi_mem_iff (hconj_le (x i) (x_spec i).1) (hconj_le g hg)
      intro n hn
      rw [mem_conjSubg_line_iff (g := x i) (st := repStates.get i) (x_spec i).2 hn,
        mem_conjSubg_line_iff (g := g) (st := st) hact hn]
      exact (mem_lineOfSt_iff_of_sameLine hi).symm
    · rintro ⟨i, rfl⟩
      exact ⟨x i, (x_spec i).1, rfl⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hij' : conjSubg (x i) LS = conjSubg (x j) LS := hij
    have hiffn : ∀ n < 64, n ∈ lineOfSt (repStates.get i) ↔ n ∈ lineOfSt (repStates.get j) := by
      intro n hn
      have hmid : tab64Perm tabS n ∈ conjSubg (x i) LS ↔
          tab64Perm tabS n ∈ conjSubg (x j) LS := by rw [hij']
      exact (mem_conjSubg_line_iff (x_spec i).2 hn).symm.trans
        (hmid.trans (mem_conjSubg_line_iff (x_spec j).2 hn))
    have hsame : sameLine (repStates.get i) (repStates.get j) = true := by
      unfold sameLine
      rw [Bool.and_eq_true]
      constructor
      · rw [List.all_eq_true]
        intro n hn
        exact List.contains_iff_mem.mpr ((hiffn n (lineOfSt_lt hn)).mp hn)
      · rw [List.all_eq_true]
        intro n hn
        exact List.contains_iff_mem.mpr ((hiffn n (lineOfSt_lt hn)).mpr hn)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hfalse := repStates_distinct.rel_get_of_lt hlt
      rw [hfalse] at hsame
      exact Bool.false_ne_true hsame
    · have hfalse := repStates_distinct.rel_get_of_lt hgt
      rw [sameLine_comm] at hsame
      rw [hfalse] at hsame
      exact Bool.false_ne_true hsame
  rw [hPf, Set.ncard_range_of_injective hf_inj, Nat.card_fin, repStates_length]

theorem clause26_std :
    Clause26 (MY M24g stdS) (KY M24g stdS) (KY M24g o2F) := by
  have hO2 : IsOctad o2F := by
    rw [o2F_eq_mask]
    exact isOctad_maskSetOf 9857280 (by decide) (by decide +kernel)
  have hKO : KY M24g o2F = octFix o2F := by
    unfold KY
    rw [show MY M24g o2F = octStab o2F from rfl]
    exact pCoreOf_octStab hO2
  rw [pCore_S, hKO]
  unfold Clause26
  exact ⟨GF4, inferInstance, card_gf4, OmegaH, tab64Equiv tabS_ok coordF4, actS,
    isHyperoval_OmegaH, stdMS_conjIso, actS_perfectCore_linear, isE2k_line, line_isF4line,
    ncard_conjugates_line⟩

end CFSG.Quasithin.AppendixH.H14

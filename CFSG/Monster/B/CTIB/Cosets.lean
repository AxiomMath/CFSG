module

public import CFSG.Monster.B.CTIB.Orbits
public import CFSG.Monster.B.CTIB.CosetCert
public import Certificates.Certificate3111
public import Certificates.Certificate3100
public import Certificates.Certificate3110
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native ConjAct Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def cosetCount (k : ℕ) : ℕ := if k = 6 then 67584 else if k = 8 then 18432 else 6144

theorem cosetOK_of {k : ℕ} (hk : IsRank k) : cosetOK k (cosetCount k)
    = true := by
  have h := cosetCheck_eq_true
  simp only [cosetCheck, Bool.and_eq_true] at h
  rcases hk with rfl | rfl | rfl
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2

theorem liftImgsN_eq (k : ℕ) : liftImgsN k = liftImgsK k := rfl

theorem liftRowsN_eq (k : ℕ) : liftRowsN k = liftRowsK k := rfl

@[expose] def centAuts (k : ℕ) : Array (Array ℕ) :=
  ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN k j)).toArray

@[expose] def deltas (k : ℕ) : Array ℕ := ((List.range 15).map fun j => deltaN k j).toArray

theorem centAuts_getD {k j : ℕ} (hj : j < 15) :
    (centAuts k).getD j #[] = wordAut (genInvImgs ()) (centWordN k j) := by
  rw [centAuts, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem deltas_getD {k j : ℕ} (hj : j < 15) : (deltas k).getD j 0 = deltaN k j := by
  rw [deltas, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

@[expose] def validK (k : ℕ) (n : ℕ) : Bool :=
  decide (n < 2 ^ 23) && isInv gArr (liftImgsK k).toArray (sqCode k) n

@[expose] def fuseCert (k : ℕ) (r : ℕ × ℕ × ℕ) : Array ℕ × Array (Array ℕ) × Array ℕ × Array ℕ :=
  natBfs (fuseAct (liftImgsK k).toArray (centAuts k) (deltas k)) 37 r.2.2 (r.2.1 + 1)

theorem cosetOK_parts {k : ℕ} (hk : IsRank k) :
    countInv gArr (liftImgsK k).toArray (liftRowsK k).toArray (sqCode k) = cosetCount k ∧
    (∀ r ∈ orbitRecs k, orbitOK (qconj gArr (liftImgsK k).toArray) 22 (validK k) r.1 r.2 = true) ∧
    chainLt ((orbitRecs k).map (·.1)) = true ∧ ((orbitRecs k).map (·.2)).sum = cosetCount k ∧
    chainLt ((fusionRecsN k).map (·.2.2)) = true ∧
    ((fusionRecsN k).map (·.2.1)).sum = cosetCount k ∧
    (∀ r ∈ fusionRecsN k,
      natCertOK (fuseAct (liftImgsK k).toArray (centAuts k) (deltas k)) 37 (validK k) r.2.2
        (fuseCert k r).1 (fuseCert k r).2.1 (fuseCert k r).2.2.1 (fuseCert k r).2.2.2 = true ∧
      (fuseCert k r).1.size = r.2.1 ∧ (fuseCert k r).1.all (r.2.2 ≤ ·) = true ∧
      ((orbitRecs k).filter fun q => (fuseCert k r).1.contains q.1).length = r.1) ∧
    (∀ j < 15, deltaAutOK (genInvImgs ()) (liftImgsK k).toArray
      (wordAut (genInvImgs ()) (centWordN k j)) (centWordN k j) (deltaN k j) = true) := by
  have h := cosetOK_of hk
  simp only [cosetOK, repsIncreasing, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun r hr => ?_, fun j hj => ?_⟩
  · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h7 r hr
    exact ⟨a, b, c, d⟩
  · have := h8 j hj
    have e := centAuts_getD (k := k) hj
    unfold centAuts at e
    rwa [e] at this

theorem delta_eq
    {k j : ℕ}
    (hk : IsRank k) (hj : j < 15)
    (hok : deltaAutOK (genInvImgs ()) (liftImgsK k).toArray (wordAut (genInvImgs ())
      (centWordN k j)) (centWordN k j) (deltaN k j) = true) :
    deltaElt k j = qS (deltaN k j) := by
  refine eq_of_row0 (delta_cases hk hj hok) ?_
  have hoff : rankOff k + j < 45 := by
    rcases hk with rfl | rfl | rfl <;> simp only [rankOff] <;> split_ifs <;> omega
  have hd := factDelta (rankOff k + j) hoff
  rw [deltaElt_eq_word hk hj, beta_wordS' (deltaWord_letters hk hj), hd, beta_qSK]
  rfl

theorem fuse_act
    {k : ℕ}
    (hk : IsRank k) {j : ℕ} (hj : j < 15)
    (hok : deltaAutOK (genInvImgs ()) (liftImgsK k).toArray (wordAut (genInvImgs ())
      (centWordN k j)) (centWordN k j) (deltaN k j) = true) (a : ℕ) :
    cosetElt k (fuse gArr (wordAut (genInvImgs ()) (centWordN k j)) (deltaN k j) a) =
      toConjAct (centElt k j)⁻¹ • cosetElt k a := by
  have hc := (conj_wordS' (centWordN_letters hk hj)).1
  rw [toConjAct_smul, inv_inv, cosetElt, cosetElt, fuse, ← qS_mul, ← delta_eq hk hj hok,
    ← conj_qS (centElt_mem_Jbar hk hj) hc a, deltaElt]
  simp only [centElt]
  group

section Family

variable {G X : Type*} [Group G] [MulAction G X]

theorem orbit_disjoint_of_ne {H : Subgroup G} {a b : X}
    (h : MulAction.orbit H a ≠ MulAction.orbit H b) :
    Disjoint (MulAction.orbit H a) (MulAction.orbit H b) := by
  rw [Set.disjoint_left]
  intro x ha hb
  exact h ((MulAction.orbit_eq_iff.2 ha).symm.trans (MulAction.orbit_eq_iff.2 hb))

theorem orbits_pairwise_disjoint (H : Subgroup G) {dec : ℕ → X} {valid : ℕ → Bool}
    (hinj : ∀ a b, valid a = true → valid b = true → dec a = dec b → a = b) {reps : List ℕ}
    (hmin : ∀ r ∈ reps, valid r = true ∧
      ∀ x ∈ MulAction.orbit H (dec r), ∃ n, valid n = true ∧ r ≤ n ∧ x = dec n)
    (hinc : reps.Pairwise (· < ·)) :
    (reps.map fun r => MulAction.orbit H (dec r)).Pairwise Disjoint := by
  rw [List.pairwise_map]
  refine hinc.imp_of_mem fun {r r'} hr hr' hlt => orbit_disjoint_of_ne fun heq => ?_
  have hm : dec r ∈ MulAction.orbit H (dec r') := heq ▸ MulAction.mem_orbit_self (dec r)
  obtain ⟨n, hn, hle, hx⟩ := (hmin r' hr').2 _ hm
  have := hinj r n (hmin r hr).1 hn hx
  omega

theorem ncard_biUnion_list {Y : Type*} : ∀ (O : List (Set Y)), (∀ o ∈ O, o.Finite) →
    O.Pairwise Disjoint → (⋃ o ∈ O, o).ncard = (O.map Set.ncard).sum
  | [], _, _ => by simp
  | o :: O, hf, hd => by
    rw [List.pairwise_cons] at hd
    have hU : (⋃ o' ∈ o :: O, o') = o ∪ ⋃ o' ∈ O, o' := by
      ext y; simp
    have hfin : (⋃ o' ∈ O, o').Finite :=
      Set.Finite.biUnion (List.finite_toSet O) fun o' ho' => hf o' (List.mem_cons_of_mem _ ho')
    have hdisj : Disjoint o (⋃ o' ∈ O, o') := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun o' ho' => hd.1 o' ho'
    rw [hU, Set.ncard_union_eq hdisj (hf o (List.mem_cons_self ..)) hfin,
      ncard_biUnion_list O (fun o' ho' => hf o' (List.mem_cons_of_mem _ ho')) hd.2,
      List.map_cons, List.sum_cons]

theorem subset_biUnion_of_ncard {Y : Type*} {S : Set Y} (hS : S.Finite) (O : List (Set Y))
    (hf : ∀ o ∈ O, o.Finite) (hsub : ∀ o ∈ O, o ⊆ S) (hd : O.Pairwise Disjoint)
    (hsum : (O.map Set.ncard).sum = S.ncard) : S ⊆ ⋃ o ∈ O, o := by
  have hU : (⋃ o ∈ O, o) ⊆ S := Set.iUnion₂_subset hsub
  have heq := Set.eq_of_subset_of_ncard_le hU (by rw [ncard_biUnion_list O hf hd, hsum]) hS
  rw [heq]

end Family

theorem validK_mem
    {k : ℕ} (hk : IsRank k) {a : ℕ}
    (h : validK k a = true) :
    cosetElt k a ∈ cosetInv k := by
  simp only [validK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨⟨qS a, qS_mem a, rfl⟩, (cosetElt_sq_eq_one_iff hk).2 h.2⟩

theorem validK_inj
    (k : ℕ) {a b : ℕ} (ha : validK k a = true)
    (hb : validK k b = true)
    (h : cosetElt k a = cosetElt k b) : a = b := by
  simp only [validK, Bool.and_eq_true, decide_eq_true_eq] at ha hb
  exact cosetElt_injOn k ha.1 hb.1 h

@[expose] noncomputable def gensQ (m : ℕ) : ConjAct Sbp := toConjAct (es m)

theorem hactQ
    {k : ℕ} (hk : IsRank k) :
    ∀ m < 22, ∀ a, validK k a = true →
      cosetElt k (qconj gArr (liftImgsK k).toArray m a) = gensQ m • cosetElt k a :=
  fun _ hm a _ => qconj_act hk hm a

theorem hactF
    {k : ℕ} (hk : IsRank k)
    (hok : ∀ j < 15, deltaAutOK (genInvImgs ()) (liftImgsK k).toArray
      (wordAut (genInvImgs ()) (centWordN k j)) (centWordN k j) (deltaN k j) = true) :
    ∀ m < 37, ∀ a, validK k a = true →
      cosetElt k (fuseAct (liftImgsK k).toArray (centAuts k) (deltas k) m a) =
        gensF k m • cosetElt k a := by
  intro m hm a _
  rw [fuseAct, gensF]
  by_cases h : m < 22
  · rw [ite_eq_left h, ite_eq_left h]
    exact qconj_act hk h a
  · rw [ite_eq_right h, ite_eq_right h, centAuts_getD (by omega), deltas_getD (by omega)]
    exact fuse_act hk (by omega) (hok _ (by omega)) a

theorem qClass_eq_orbit'
    (t : Sbp) :
    qClass t = MulAction.orbit (Subgroup.closure (gensQ '' {m | m < 22})) t := qClass_eq_orbit t

theorem qOrbit_facts
    {k : ℕ} (hk : IsRank k) {r : ℕ × ℕ}
    (hr : r ∈ orbitRecs k) :
    validK k r.1 = true ∧ (qClass (cosetElt k r.1)).ncard = r.2 ∧
    ∀ x ∈ qClass (cosetElt k r.1), ∃ n, validK k n = true ∧ r.1 ≤ n ∧ x = cosetElt k n := by
  obtain ⟨-, hq, -⟩ := cosetOK_parts hk
  obtain ⟨pts, -, hval, horb, hnc, hroot⟩ := orbit_of_orbitOK (hq r hr) (hactQ hk)
    (fun a b ha hb h => validK_inj k ha hb h)
  rw [qClass_eq_orbit']
  refine ⟨hroot, hnc, fun x hx => ?_⟩
  rw [horb] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨pts[i]!, (hval i hi).1, (hval i hi).2, rfl⟩

theorem fOrbit_facts
    {k : ℕ}
    (hk : IsRank k) {r : ℕ × ℕ × ℕ} (hr : r ∈ fusionRecsN k) :
    validK k r.2.2 = true ∧ (fClass k (cosetElt k r.2.2)).ncard = r.2.1 ∧
    (∀ x ∈ fClass k (cosetElt k r.2.2), ∃ n, validK k n = true ∧ r.2.2 ≤ n ∧
      x = cosetElt k n) ∧
    ∀ n, validK k n = true →
      (cosetElt k n ∈ fClass k (cosetElt k r.2.2) ↔ (fuseCert k r).1.contains n = true) := by
  obtain ⟨-, -, -, -, -, -, hf, hdel⟩ := cosetOK_parts hk
  obtain ⟨hc, hsz, hall, -⟩ := hf r hr
  obtain ⟨horb, hnc, hroot, hval⟩ := orbit_of_nativeCert hc (hactF hk hdel)
    (fun a b ha hb h => validK_inj k ha hb h)
  rw [fClass_eq_orbit]
  have hmin : ∀ i < (fuseCert k r).1.size, r.2.2 ≤ (fuseCert k r).1[i]! := by
    rw [Array.all_eq_true] at hall
    intro i hi
    rw [getElem!_pos _ i hi]
    exact of_decide_eq_true (hall i hi)
  refine ⟨hroot, hnc.trans hsz, fun x hx => ?_, fun n hn => ?_⟩
  · rw [horb] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨_, hval i hi, hmin i hi, rfl⟩
  · rw [horb, Array.contains_iff_mem, Array.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, e⟩
      have hi' : i < (fuseCert k r).1.size := hi
      refine ⟨i, hi', ?_⟩
      rw [← getElem!_pos _ i hi']
      exact validK_inj k (hval i hi') hn e
    · rintro ⟨i, hi, e⟩
      refine ⟨i, (show i < (fuseCert k r).1.size from hi), ?_⟩
      show cosetElt k (fuseCert k r).1[i]! = cosetElt k n
      rw [getElem!_pos _ i hi, e]

theorem cosetInv_finite
    (k : ℕ) : (cosetInv k).Finite := Set.toFinite _

@[expose] noncomputable def qClassList
    (k : ℕ) : List (Set Sbp) :=
  ((orbitRecs k).map (·.1)).map fun n => qClass (cosetElt k n)

theorem reps_pairwise {k : ℕ} (hk : IsRank k) :
    ((orbitRecs k).map (·.1)).Pairwise (· < ·) :=
  (chainLt_iff _).1 (cosetOK_parts hk).2.2.1

theorem qClassList_disjoint
    {k : ℕ} (hk : IsRank k) :
    (qClassList k).Pairwise Disjoint := by
  have h := orbits_pairwise_disjoint (Subgroup.closure (gensQ '' {m | m < 22}))
    (dec := cosetElt k) (valid := validK k) (fun a b ha hb e => validK_inj k ha hb e)
    (reps := (orbitRecs k).map (·.1)) (fun n hn => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
      obtain ⟨h1, -, h3⟩ := qOrbit_facts hk hr
      exact ⟨h1, fun x hx => h3 x (by rw [qClass_eq_orbit']; exact hx)⟩) (reps_pairwise hk)
  rw [qClassList]
  convert h using 2
  funext n
  exact qClass_eq_orbit' _

theorem qClassList_sum
    {k : ℕ} (hk : IsRank k) :
    ((qClassList k).map Set.ncard).sum = (cosetInv k).ncard := by
  rw [ncard_cosetInv hk, (cosetOK_parts hk).1, ← (cosetOK_parts hk).2.2.2.1, qClassList,
    List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  exact (qOrbit_facts hk hr).2.1

theorem cover_qClass
    {k : ℕ} (hk : IsRank k) {t : Sbp}
    (ht : t ∈ cosetInv k) :
    ∃ r ∈ orbitRecs k, t ∈ qClass (cosetElt k r.1) := by
  have h := subset_biUnion_of_ncard (cosetInv_finite k) (qClassList k)
    (fun o _ => Set.toFinite o) (fun o ho => by
      rw [qClassList, List.map_map, List.mem_map] at ho
      obtain ⟨r, hr, rfl⟩ := ho
      intro x hx
      obtain ⟨n, hn, -, rfl⟩ := (qOrbit_facts hk hr).2.2 x hx
      exact validK_mem hk hn) (qClassList_disjoint hk) (qClassList_sum hk) ht
  simp only [Set.mem_iUnion] at h
  obtain ⟨o, ho, hto⟩ := h
  rw [qClassList, List.map_map, List.mem_map] at ho
  obtain ⟨r, hr, rfl⟩ := ho
  exact ⟨r, hr, hto⟩

theorem mem_qClass_self (t : Sbp) : t ∈ qClass t := ⟨1, Qs.one_mem, by group⟩

theorem mem_fClass_self
    (k : ℕ) (t : Sbp) : t ∈ fClass k t := ⟨1, (fuseGroup k).one_mem, by group⟩

theorem nodup_of_disjoint {α : Type*} {L : List (Set α)} (hd : L.Pairwise Disjoint)
    (hne : ∀ o ∈ L, o.Nonempty) : L.Nodup := by
  refine hd.imp_of_mem fun {a b} ha _ hab heq => ?_
  subst heq
  obtain ⟨x, hx⟩ := hne a ha
  exact Set.disjoint_left.1 hab hx hx

theorem ncard_mem_list {α : Type*} {L : List (Set α)} (h : L.Nodup) :
    {C | C ∈ L}.ncard = L.length := by
  rw [← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

theorem qClass_eq_of_mem
    {t u : Sbp} (h : t ∈ qClass u) : qClass t = qClass u := by
  rw [qClass_eq_orbit', qClass_eq_orbit'] at *
  exact MulAction.orbit_eq_iff.2 h

theorem qClassList_nodup
    {k : ℕ} (hk : IsRank k) :
    (qClassList k).Nodup :=
  nodup_of_disjoint (qClassList_disjoint hk) fun o ho => by
    rw [qClassList, List.mem_map] at ho
    obtain ⟨n, -, rfl⟩ := ho
    exact ⟨_, mem_qClass_self _⟩

theorem ncard_qClasses
    {k : ℕ} (hk : IsRank k) :
    {C : Set Sbp | ∃ t ∈ cosetInv k, C = qClass t}.ncard = (orbitRecs k).length := by
  have hset : {C : Set Sbp | ∃ t ∈ cosetInv k, C = qClass t} = {C | C ∈ qClassList k} := by
    ext C
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨r, hr, htr⟩ := cover_qClass hk ht
      rw [qClass_eq_of_mem htr]
      show qClass (cosetElt k r.1) ∈ qClassList k
      rw [qClassList, List.map_map, List.mem_map]
      exact ⟨r, hr, rfl⟩
    · intro hC
      simp only [Set.mem_ofPred_eq, qClassList, List.map_map, List.mem_map] at hC
      obtain ⟨r, hr, rfl⟩ := hC
      exact ⟨_, validK_mem hk (qOrbit_facts hk hr).1, rfl⟩
  rw [hset, ncard_mem_list (qClassList_nodup hk), qClassList, List.length_map, List.length_map]

@[expose] noncomputable def fClassList
    (k : ℕ) : List (Set Sbp) :=
  (fusionRecsN k).map fun r => fClass k (cosetElt k r.2.2)

theorem fClassList_disjoint
    {k : ℕ}
    (hk : IsRank k) : (fClassList k).Pairwise Disjoint := by
  have h := orbits_pairwise_disjoint (Subgroup.closure (gensF k '' {m | m < 37}))
    (dec := cosetElt k) (valid := validK k) (fun a b ha hb e => validK_inj k ha hb e)
    (reps := (fusionRecsN k).map (·.2.2)) (fun n hn => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hn
      obtain ⟨h1, -, h3, -⟩ := fOrbit_facts hk hr
      exact ⟨h1, fun x hx => h3 x (by rw [fClass_eq_orbit]; exact hx)⟩)
    ((chainLt_iff _).1 (cosetOK_parts hk).2.2.2.2.1)
  rw [fClassList, show (fun r : ℕ × ℕ × ℕ => fClass k (cosetElt k r.2.2)) =
    (fun n => MulAction.orbit (Subgroup.closure (gensF k '' {m | m < 37})) (cosetElt k n)) ∘
      (·.2.2) from funext fun r => fClass_eq_orbit k _, ← List.map_map]
  exact h

theorem cover_fClass
    {k : ℕ}
    (hk : IsRank k) {t : Sbp} (ht : t ∈ cosetInv k) :
    ∃ r ∈ fusionRecsN k, t ∈ fClass k (cosetElt k r.2.2) := by
  have hsum : ((fClassList k).map Set.ncard).sum = (cosetInv k).ncard := by
    rw [ncard_cosetInv hk, (cosetOK_parts hk).1, ← (cosetOK_parts hk).2.2.2.2.2.1, fClassList,
      List.map_map]
    congr 1
    exact List.map_congr_left fun r hr => (fOrbit_facts hk hr).2.1
  have h := subset_biUnion_of_ncard (cosetInv_finite k) (fClassList k)
    (fun o _ => Set.toFinite o) (fun o ho => by
      rw [fClassList, List.mem_map] at ho
      obtain ⟨r, hr, rfl⟩ := ho
      intro x hx
      obtain ⟨n, hn, -, rfl⟩ := (fOrbit_facts hk hr).2.2.1 x hx
      exact validK_mem hk hn) (fClassList_disjoint hk) hsum ht
  simp only [Set.mem_iUnion] at h
  obtain ⟨o, ho, hto⟩ := h
  rw [fClassList, List.mem_map] at ho
  obtain ⟨r, hr, rfl⟩ := ho
  exact ⟨r, hr, hto⟩

theorem fClass_subset
    {k : ℕ}
    (hk : IsRank k) {r : ℕ × ℕ × ℕ} (hr : r ∈ fusionRecsN k) :
    fClass k (cosetElt k r.2.2) ⊆ cosetInv k := fun x hx => by
  obtain ⟨n, hn, -, rfl⟩ := (fOrbit_facts hk hr).2.2.1 x hx
  exact validK_mem hk hn

theorem qClass_subset_fClass
    {k : ℕ} {t u : Sbp} (h : t ∈ fClass k u) : qClass t ⊆ fClass k u := by
  rintro x ⟨e, he, rfl⟩
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨f * e, (fuseGroup k).mul_mem hf (Qs_le_fuseGroup k he), by group⟩

theorem ncard_qClasses_in
    {k : ℕ}
    (hk : IsRank k) {R : ℕ × ℕ × ℕ} (hR : R ∈ fusionRecsN k) :
    {C : Set Sbp | ∃ t ∈ cosetInv k, C = qClass t ∧ C ⊆ fClass k (cosetElt k R.2.2)}.ncard =
      R.1 := by
  set L := ((orbitRecs k).filter fun q => (fuseCert k R).1.contains q.1).map
    fun q => qClass (cosetElt k q.1) with hL
  have hmem := (fOrbit_facts hk hR).2.2.2
  have hset : {C : Set Sbp | ∃ t ∈ cosetInv k, C = qClass t ∧
      C ⊆ fClass k (cosetElt k R.2.2)} = {C | C ∈ L} := by
    ext C
    constructor
    · rintro ⟨t, ht, rfl, hsub⟩
      obtain ⟨q, hq, htq⟩ := cover_qClass hk ht
      rw [qClass_eq_of_mem htq] at hsub ⊢
      have hv := (qOrbit_facts hk hq).1
      have hin := (hmem q.1 hv).1 (hsub (mem_qClass_self _))
      exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, hin⟩, rfl⟩
    · intro hC
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
      obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
      have hv := (qOrbit_facts hk hq1).1
      exact ⟨_, validK_mem hk hv, rfl, qClass_subset_fClass ((hmem q.1 hv).2 hq2)⟩
  have hnd : L.Nodup := by
    have hsub : L.Sublist (qClassList k) := by
      rw [hL, qClassList, List.map_map]
      exact List.filter_sublist.map _
    exact hsub.nodup (qClassList_nodup hk)
  rw [hset, ncard_mem_list hnd, hL, List.length_map]
  exact ((cosetOK_parts hk).2.2.2.2.2.2.1 R hR).2.2.2

theorem orbitRecs_lengths :
    (orbitRecs 6).length = 529 ∧ (orbitRecs 8).length = 37 ∧ (orbitRecs 10).length = 3 :=
  Certificates.certificate3111

theorem fusionRecs_eq :
    fusionRecsN 6 = [(270, 34560, 43), (256, 32768, 61), (1, 64, 10541), (1, 128, 26925),
      (1, 64, 46090)] ∧
    fusionRecsN 8 = [(1, 256, 0), (35, 17920, 128), (1, 256, 35764)] ∧
    fusionRecsN 10 = [(2, 4096, 107), (1, 2048, 66038)] := ⟨rfl, rfl, rfl⟩

theorem conj_of_fClass
    {k : ℕ} (hk : IsRank k) {t u : Sbp} (h : t ∈ fClass k u) :
    ∃ g ∈ Jbar.op, g⁻¹ * t * g = u := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨f⁻¹, Jbar.op.inv_mem (fuseGroup_le k hk hf), by group⟩

theorem native_three_coset_involution_cover :
    (∀ t ∈ cosetInv 6, ∃ g ∈ Jbar.op, ∃ i ∈ ({4, 5, 6, 7, 8} : Finset ℕ), g⁻¹ * t * g = rs i) ∧
    (∀ t ∈ cosetInv 8, ∃ g ∈ Jbar.op, ∃ i ∈ ({9, 10, 11} : Finset ℕ), g⁻¹ * t * g = rs i) ∧
    (∀ t ∈ cosetInv 10, ∃ g ∈ Jbar.op, ∃ i ∈ ({12, 13} : Finset ℕ), g⁻¹ * t * g = rs i) ∧
    (cosetInv 6).ncard = 67584 ∧ (cosetInv 8).ncard = 18432 ∧ (cosetInv 10).ncard = 6144 ∧
    {C : Set Sbp | ∃ t ∈ cosetInv 6, C = qClass t}.ncard = 529 ∧
    {C : Set Sbp | ∃ t ∈ cosetInv 8, C = qClass t}.ncard = 37 ∧
    {C : Set Sbp | ∃ t ∈ cosetInv 10, C = qClass t}.ncard = 3 ∧
    (∀ k, IsRank k → ∀ j < 15, centElt k j = wordS' (centWordN k j) ∧ (centElt k j).unop ∈ Jbar ∧
      (hs k)⁻¹ * (centElt k j)⁻¹ * hs k * centElt k j = qS (deltaN k j)) ∧
    fusionRecsN 6 = [(270, 34560, 43), (256, 32768, 61), (1, 64, 10541), (1, 128, 26925),
      (1, 64, 46090)] ∧
    fusionRecsN 8 = [(1, 256, 0), (35, 17920, 128), (1, 256, 35764)] ∧
    fusionRecsN 10 = [(2, 4096, 107), (1, 2048, 66038)] ∧
    (∀ k, IsRank k → fuseGroup k ≤ Jbar.op ∧
      (∀ r ∈ fusionRecsN k, fClass k (cosetElt k r.2.2) ⊆ cosetInv k ∧
        (fClass k (cosetElt k r.2.2)).ncard = r.2.1 ∧
        {C : Set Sbp | ∃ t ∈ cosetInv k, C = qClass t ∧
          C ⊆ fClass k (cosetElt k r.2.2)}.ncard = r.1) ∧
      (∀ t ∈ cosetInv k, ∃ r ∈ fusionRecsN k, t ∈ fClass k (cosetElt k r.2.2)) ∧
      ((fusionRecsN k).map fun r => fClass k (cosetElt k r.2.2)).Pairwise Disjoint) := by
  have h6 : IsRank 6 := Or.inl rfl
  have h8 : IsRank 8 := Or.inr (Or.inl rfl)
  have h10 : IsRank 10 := Or.inr (Or.inr rfl)
  obtain ⟨l6, l8, l10⟩ := orbitRecs_lengths
  obtain ⟨f6, f8, f10⟩ := fusionRecs_eq
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    (by rw [ncard_cosetInv h6, (cosetOK_parts h6).1]; rfl),
    (by rw [ncard_cosetInv h8, (cosetOK_parts h8).1]; rfl),
    (by rw [ncard_cosetInv h10, (cosetOK_parts h10).1]; rfl), (by rw [ncard_qClasses h6, l6]),
    (by rw [ncard_qClasses h8, l8]), (by rw [ncard_qClasses h10, l10]),
    fun k hk j hj => ⟨rfl, centElt_mem_Jbar hk hj,
      delta_eq hk hj ((cosetOK_parts hk).2.2.2.2.2.2.2 j hj)⟩,
    f6, f8, f10, fun k hk => ⟨fuseGroup_le k hk, fun r hr => ⟨fClass_subset hk hr,
      (fOrbit_facts hk hr).2.1, ncard_qClasses_in hk hr⟩, fun t ht => cover_fClass hk ht,
      fClassList_disjoint hk⟩⟩
  · obtain ⟨r, hr, htr⟩ := cover_fClass h6 ht
    obtain ⟨g, hg, e⟩ := conj_of_fClass h6 htr
    rw [f6] at hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨g, hg, 4, by decide, e⟩
    · exact ⟨g, hg, 5, by decide, e⟩
    · exact ⟨g, hg, 6, by decide, e⟩
    · exact ⟨g, hg, 7, by decide, e⟩
    · exact ⟨g, hg, 8, by decide, e⟩
  · obtain ⟨r, hr, htr⟩ := cover_fClass h8 ht
    obtain ⟨g, hg, e⟩ := conj_of_fClass h8 htr
    rw [f8] at hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨g, hg, 9, by decide, e⟩
    · exact ⟨g, hg, 10, by decide, e⟩
    · exact ⟨g, hg, 11, by decide, e⟩
  · obtain ⟨r, hr, htr⟩ := cover_fClass h10 ht
    obtain ⟨g, hg, e⟩ := conj_of_fClass h10 htr
    rw [f10] at hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨g, hg, 12, by decide, e⟩
    · exact ⟨g, hg, 13, by decide, e⟩

end CFSG.Monster.B.CTIB

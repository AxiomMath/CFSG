module

public import CFSG.Monster.B.TwoA.Census.PermClassesInputs
public import Certificates.Kernel.MonsterB.Perm3018K
public import Certificates.Kernel.MonsterB.Chain3018
public import CFSG.Certificates.Kernel.MonsterB.PermGroupBfs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSound

public section

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KC.Bfs CFSG.KLie.CT CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Certificates.Native CertificateChecks.Perm3018

namespace CertificateChecks.Batch3018

open CFSG.Monster.B.TwoA.Census CFSG.KC.SortTree CFSG.KC.Bfs CFSG.KLie.CT CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Certificates.Native CertificateChecks.Perm3018

set_option maxRecDepth 100000

theorem kSizes : sylowGens.size = 10 ∧ abGens.size = 2 ∧ c1Gens.size = 5 ∧ c2Gens.size = 5 := by
  decide +kernel

theorem kPerm : (∀ k < 10, PermArr sylowGens[k]! = true) ∧ (∀ k < 2, PermArr abGens[k]! = true) ∧
    (∀ k < 5, PermArr c1Gens[k]! = true) ∧ (∀ k < 5, PermArr c2Gens[k]! = true) ∧
    PermArr (seedArr.getD 1 #[]) = true ∧ PermArr (seedArr.getD 2 #[]) = true := by
  decide +kernel

theorem kGS : ∀ k < 10, fget GS k 120 = keyP sylowGens[k]! := by decide +kernel

theorem kGA : ∀ k < 2, fget GA k 120 = keyP abGens[k]! ∧
    fget GAI k 120 = keyP (ainv abGens[k]!) := by
  decide +kernel

theorem permC : CFSG.KC.Enum.allN 12 (fun j => permOK 24 5 (mask 5) (24 * 5) (Chain3018.C1C.S j)
    (Chain3018.C1C.SI j)) = true ∧
    CFSG.KC.Enum.allN 9 (fun j => permOK 24 5 (mask 5) (24 * 5) (Chain3018.C2C.S j)
      (Chain3018.C2C.SI j)) =
      true := by
  constructor <;> quickRfl

@[expose] noncomputable def SA1 : Array (Array Nat) :=
  Array.ofFn (n := 12) fun j => unpack 24 5 (Chain3018.C1C.S j.val)

@[expose] noncomputable def SA2 : Array (Array Nat) :=
  Array.ofFn (n := 9) fun j => unpack 24 5 (Chain3018.C2C.S j.val)

theorem binds1 : Binds 24 5 Chain3018.C1C.S 12 5 Chain3018.C1C.BP SA1 Chain3018.c1Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA1], fun j hj => ?_, rfl, ?_⟩
  · rw [SA1, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem binds2 : Binds 24 5 Chain3018.C2C.S 9 3 Chain3018.C2C.BP SA2 Chain3018.c2Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA2], fun j hj => ?_, rfl, ?_⟩
  · rw [SA2, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem gens1 : ∀ i < 5, SA1[i]! = c1Gens[i]! := by decide +kernel

theorem gens2 : ∀ i < 5, SA2[i]! = c2Gens[i]! := by decide +kernel

theorem card1 : Nat.card (genH c1Gens) = 21504 := by
  have hb : ([0, 1, 8, 2, 3] : List (Fin 24)).Nodup := by decide
  have hbase : (([0, 1, 8, 2, 3] : List (Fin 24)).map Fin.val).toArray = Chain3018.c1Base := rfl
  have hs := kSizes.2.2.1
  have raw : rawChainOK 24 (SA1.extract 0 5) SA1 Chain3018.c1Base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 12 Chain3018.c1Der) 1 = true :=
    rawChainK_sound (NS := 1) (CH := 24) binds1 Chain3018.C1C.head Chain3018.C1C.hl (by norm_num)
      Chain3018.C1C.hs
  have orb : rawOrbitSizes 24 SA1 Chain3018.c1Base = [8, 7, 16, 6, 4] := by
    rw [rawOrbitSizesK_sound binds1 permC.1 Chain3018.C1C.hl]
    decide
  rw [card_genH_of_rawChainOK (fun k hk => kPerm.2.2.1 k (hs ▸ hk)) hb
    (by rw [hs]; simp [SA1]) (fun i hi => gens1 i (hs ▸ hi)) (by rw [hs, hbase]; exact raw),
    hbase, orb]
  rfl

theorem card2 : Nat.card (genH c2Gens) = 7680 := by
  have hb : ([0, 8, 1] : List (Fin 24)).Nodup := by decide
  have hbase : (([0, 8, 1] : List (Fin 24)).map Fin.val).toArray = Chain3018.c2Base := rfl
  have hs := kSizes.2.2.2
  have raw : rawChainOK 24 (SA2.extract 0 5) SA2 Chain3018.c2Base
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 9 Chain3018.c2Der) 1 = true :=
    rawChainK_sound (NS := 1) (CH := 24) binds2 Chain3018.C2C.head Chain3018.C2C.hl (by norm_num)
      Chain3018.C2C.hs
  have orb : rawOrbitSizes 24 SA2 Chain3018.c2Base = [24, 20, 16] := by
    rw [rawOrbitSizesK_sound binds2 permC.2 Chain3018.C2C.hl]
    decide
  rw [card_genH_of_rawChainOK (fun k hk => kPerm.2.2.2.1 k (hs ▸ hk)) hb
    (by rw [hs]; simp [SA2]) (fun i hi => gens2 i (hs ▸ hi)) (by rw [hs, hbase]; exact raw),
    hbase, orb]
  rfl

theorem cent1 : certOK amul c1Gens idArr cent1Cert = true ∧ cent1Cert.pts.size = 21504 := by
  have h := bfsCert_amul_card (fuel := 30000) (fun k hk => kPerm.2.2.1 k (kSizes.2.2.1 ▸ hk))
    (by rw [card1]; norm_num)
  rw [card1] at h
  exact h

theorem cent2 : certOK amul c2Gens idArr cent2Cert = true ∧ cent2Cert.pts.size = 7680 := by
  have h := bfsCert_amul_card (fuel := 10000) (fun k hk => kPerm.2.2.2.1 k (kSizes.2.2.2 ▸ hk))
    (by rw [card2]; norm_num)
  rw [card2] at h
  exact h

@[expose] def TreeFacts (c : TreeCert) (n : ℕ) (v : ℕ → ℕ) : Prop :=
  (∀ x, x ∈ c.pts ↔ PermArr x = true ∧ ∃ i < n, v i = keyP x) ∧
    (c.pts.toList.map akey).Nodup ∧
    (∀ i < n, PermArr (decP (v i)) = true ∧ keyP (decP (v i)) = v i) ∧
    ∀ i j, i < j → j < n → v i < v j

theorem sylowF : certOK amul sylowGens idArr sylowCert = true ∧ sylowCert.pts.size = 1024 ∧
    TreeFacts sylowCert 1024 fun i => valF 120 (recS i) := by
  have hs := kSizes.1
  have T := sT
  have E := sE
  rw [← hs] at T E
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bfsCert_treeP_mem (act := amul) (gens := sylowGens)
    (root := idArr) (actN := actS) (fuel := 2000)
    (fun k hk x hx => PermArr_amul (kPerm.1 k (hs ▸ hk)) hx)
    (fun k hk x hx => by
      rw [actS, kGS k (hs ▸ hk)]
      exact amulP_eq (kPerm.1 k (hs ▸ hk)) hx)
    PermArr_idArr (by norm_num) (by norm_num) T E
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem actO_code {k : ℕ} (hk : k < abGens.size) {x : Array ℕ} (hx : PermArr x = true) :
    actO k (keyP x) = keyP (aconj abGens[k]! x) := by
  have hk' : k < 2 := kSizes.2.1 ▸ hk
  rw [actO, (kGA k hk').1, (kGA k hk').2]
  exact conjP_eq (kPerm.2.1 k hk') hx

theorem orb1F : certOK aconj abGens (seedArr.getD 1 #[]) orb1Cert = true ∧
    orb1Cert.pts.size = 11385 ∧ TreeFacts orb1Cert 11385 fun i => valF 120 (recO1 i) := by
  have hs := kSizes.2.1
  have T : treeOK actO 2 (fun _ => true) root1 recO1 11385 120 6 14 64 178 = true :=
    treeOK_of_chunks (by decide) (sl_add (sl_add none_lt a1 rfl) a2 rfl)
  have E : closeOK actO 2 recO1 edgeO1 11385 120 64 178 = true :=
    closeOK_of_chunks (by decide) (sl_add (sl_add none_lt b1 rfl) b2 rfl)
  rw [← hs] at T E
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bfsCert_treeP_mem (act := aconj) (gens := abGens)
    (root := seedArr.getD 1 #[]) (actN := actO) (fuel := 20000)
    (fun k hk x hx => PermArr_aconj (kPerm.2.1 k (hs ▸ hk)) hx) (fun k hk x hx => actO_code hk hx)
    kPerm.2.2.2.2.1 (by norm_num) (by norm_num) T E
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem orb2F : certOK aconj abGens (seedArr.getD 2 #[]) orb2Cert = true ∧
    orb2Cert.pts.size = 31878 ∧ TreeFacts orb2Cert 31878 fun i => valF 120 (recO2 i) := by
  have hs := kSizes.2.1
  have T : treeOK actO 2 (fun _ => true) root2 recO2 31878 120 6 15 64 499 = true :=
    treeOK_of_chunks (by decide) (sl_add (sl_add (sl_add (sl_add (sl_add none_lt p1 rfl) p2 rfl)
      p3 rfl) p4 rfl) p5 rfl)
  have E : closeOK actO 2 recO2 edgeO2 31878 120 64 499 = true :=
    closeOK_of_chunks (by decide) (sl_add (sl_add (sl_add (sl_add (sl_add none_lt q1 rfl) q2 rfl)
      q3 rfl) q4 rfl) q5 rfl)
  rw [← hs] at T E
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := bfsCert_treeP_mem (act := aconj) (gens := abGens)
    (root := seedArr.getD 2 #[]) (actN := actO) (fuel := 40000)
    (fun k hk x hx => PermArr_aconj (kPerm.2.1 k (hs ▸ hk)) hx) (fun k hk x hx => actO_code hk hx)
    kPerm.2.2.2.2.2 (by norm_num) (by norm_num) T E
  exact ⟨h1, h2, h3, h4, h5, h6⟩

@[expose] noncomputable def invK (c : ℕ) : Bool :=
  andB (Nat.beq (amulP c c) (keyP idArr)) (notB (Nat.beq c (keyP idArr)))

@[expose] noncomputable def witOK (w v : ℕ) : Bool :=
  bIf(Nat.beq (Nat.mod w 2) 0,
    andB (Nat.blt (Nat.div w 2) 11385) (Nat.beq (valF 120 (recO1 (Nat.div w 2))) v),
    andB (Nat.blt (Nat.div w 2) 31878) (Nat.beq (valF 120 (recO2 (Nat.div w 2))) v))

theorem kCnt : sumN 1024 (fun i => Bool.rec (motive := fun _ => ℕ) 0 1
    (invK (valF 120 (recS i)))) = 191 := by
  apply Nat.eq_of_beq_eq_true
  quickRfl

theorem kWit : CFSG.KLie.CT.allN 1024 (fun i => orB (notB (invK (valF 120 (recS i))))
    (witOK (fget W i 16) (valF 120 (recS i)))) = true := by quickRfl

theorem keyP_beq {x y : Array ℕ} (hx : PermArr x = true) (hy : PermArr y = true) :
    Nat.beq (keyP x) (keyP y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff, beq_iff_eq]
  exact ⟨keyP_inj hx hy, fun h => h ▸ rfl⟩

theorem invK_keyP {x : Array ℕ} (hx : PermArr x = true) :
    invK (keyP x) = (amul x x == idArr && x != idArr) := by
  rw [invK, amulP_eq hx hx, keyP_beq (PermArr_amul hx hx) PermArr_idArr,
    keyP_beq hx PermArr_idArr]
  cases amul x x == idArr <;> cases h : x == idArr <;> simp [bne, h, andB, notB]

theorem sumN_card (n : ℕ) (p : ℕ → Bool) :
    sumN n (fun j => Bool.rec (motive := fun _ => ℕ) 0 1 (p j)) =
      ((Finset.range n).filter fun j => p j = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => ℕ) 0 1 (p n) + sumN n _ = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases h : p n
    · simp
    · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Finset.card_insert_of_notMem (by simp)]
      change 1 + _ = _
      omega

theorem invIdx_length (c : TreeCert) (P : Array ℕ → Bool)
    (hP : ∀ i : ℕ, (amul c.pts[i]! c.pts[i]! == idArr && c.pts[i]! != idArr) = P c.pts[i]!) :
    (invIdx c).length = (c.pts.toList.filter P).length := by
  have e : c.pts.toList = (List.range c.pts.size).map fun i => c.pts[i]! := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [List.getElem_map, List.getElem_range, Array.getElem_toList,
      getElem!_pos c.pts i (by simpa using h1)]
  rw [invIdx, e, List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun i _ => hP i

theorem invLen : (invIdx sylowCert).length = 191 := by
  obtain ⟨hm, hnd, hrec, hlt⟩ := sylowF.2.2
  rw [invIdx_length sylowCert (fun x => amul x x == idArr && x != idArr) (fun _ => rfl),
    filter_length_pts _ hm hnd hrec hlt, ← kCnt, sumN_card]
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [← invK_keyP (hrec i (Finset.mem_range.1 hi)).1, (hrec i (Finset.mem_range.1 hi)).2]

theorem foldl_get_none (k : ℕ → ℕ) (key : ℕ) : ∀ (L : List ℕ) (m : Std.HashMap ℕ ℕ),
    (∀ i ∈ L, k i ≠ key) → (L.foldl (fun m i => m.insert (k i) i) m).get? key = m.get? key
  | [], _, _ => rfl
  | a :: L, m, h => by
    rw [List.foldl_cons, foldl_get_none k key L _ fun i hi => h i (by simp [hi]),
      Std.HashMap.get?_insert]
    have : (k a == key) = false := by
      rw [beq_eq_false_iff_ne]
      exact h a (by simp)
    rw [this]
    rfl

theorem foldl_get (k : ℕ → ℕ) : ∀ (L : List ℕ) (m : Std.HashMap ℕ ℕ), L.Nodup →
    ∀ t ∈ L, (∀ i ∈ L, k i = k t → i = t) →
      (L.foldl (fun m i => m.insert (k i) i) m).get? (k t) = some t
  | [], _, _, t, ht, _ => absurd ht (List.not_mem_nil)
  | a :: L, m, hnd, t, ht, hinj => by
    rw [List.foldl_cons]
    obtain ⟨ha, hL⟩ := List.nodup_cons.1 hnd
    by_cases hta : t = a
    · subst hta
      rw [foldl_get_none k (k t) L _ fun i hi e => ha (hinj i (by simp [hi]) e ▸ hi),
        Std.HashMap.get?_insert, beq_self_eq_true]
      rfl
    · have htL : t ∈ L := by
        rcases List.mem_cons.1 ht with h | h
        · exact absurd h hta
        · exact h
      exact foldl_get k L _ hL t htL fun i hi e => hinj i (by simp [hi]) e

theorem keyIndex_get {c : TreeCert} (hnd : (c.pts.toList.map akey).Nodup) {t : ℕ}
    (ht : t < c.pts.size) : (keyIndex c).get? (akey c.pts[t]!) = some t := by
  rw [keyIndex]
  refine foldl_get (fun i => akey c.pts[i]!) _ _ List.nodup_range t (List.mem_range.2 ht)
    fun i hi e => ?_
  have hi' := List.mem_range.1 hi
  have hl : (c.pts.toList.map akey).length = c.pts.size := by simp
  have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := t) (hi := by rw [hl]; exact hi')
    (hj := by rw [hl]; exact ht)).1
  simp only [List.getElem_map, Array.getElem_toList] at this
  rw [getElem!_pos c.pts i hi', getElem!_pos c.pts t ht] at e
  exact this e

theorem found {c : TreeCert} (hnd : (c.pts.toList.map akey).Nodup) {s : Array ℕ}
    (hs : s ∈ c.pts) :
    ∃ t, (keyIndex c).get? (akey s) = some t ∧ t < c.pts.size ∧ c.pts[t]! = s := by
  obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.1 hs
  rw [← getElem!_pos c.pts t ht]
  exact ⟨t, keyIndex_get hnd ht, ht, rfl⟩

theorem covered : invCovered = true := by
  obtain ⟨hm, -, -, -⟩ := sylowF.2.2
  obtain ⟨hm1, hnd1, -, -⟩ := orb1F.2.2
  obtain ⟨hm2, hnd2, -, -⟩ := orb2F.2.2
  rw [invCovered, List.all_eq_true]
  intro i hi
  rw [invIdx, List.mem_filter, List.mem_range] at hi
  obtain ⟨hi, hP⟩ := hi
  have hs : sylowCert.pts[i]! ∈ sylowCert.pts := by
    rw [getElem!_pos sylowCert.pts i hi]
    exact Array.getElem_mem hi
  generalize sylowCert.pts[i]! = s at hs hP ⊢
  obtain ⟨hps, r, hr, e⟩ := (hm s).1 hs
  have e' : valF 120 (recS r) = keyP s := e
  have hw := (CFSG.KC.SortTree.allN_iff _ _).1 kWit r hr
  rw [e', invK_keyP hps, hP] at hw
  change witOK (fget W r 16) (keyP s) = true at hw
  rw [witOK] at hw
  cases h2 : Nat.beq (Nat.mod (fget W r 16) 2) 0 <;> rw [h2] at hw <;>
    simp only [andB_true_iff, blt_iff, beq_iff] at hw
  · have hs2 : s ∈ orb2Cert.pts := (hm2 s).2 ⟨hps, _, hw.1, hw.2⟩
    obtain ⟨t, h1, h2, h3⟩ := found hnd2 hs2
    have h3' : orb2Cert.pts[t] = s := by rw [← getElem!_pos _ t h2]; exact h3
    rw [h1]
    simp [h2, h3']
  · have hs1 : s ∈ orb1Cert.pts := (hm1 s).2 ⟨hps, _, hw.1, hw.2⟩
    obtain ⟨t, h1, h2, h3⟩ := found hnd1 hs1
    have h3' : orb1Cert.pts[t] = s := by rw [← getElem!_pos _ t h2]; exact h3
    rw [h1]
    simp [h2, h3']

theorem aut1 : ∀ a ∈ sylowGenArr, AutArr a := by decide +kernel

theorem aut2 : ∀ j < 3, ∀ a ∈ centGenArrs j, AutArr a := by decide +kernel

theorem aut3 : ∀ a ∈ seedArr, AutArr a := by decide +kernel

theorem comm : ∀ j ∈ [1, 2], ∀ a ∈ centGenArrs j,
    amul a (seedArr.getD j #[]) = amul (seedArr.getD j #[]) a := by decide +kernel

end CertificateChecks.Batch3018

namespace Certificates

open CertificateChecks

open CertificateChecks.Batch3018 in
open CFSG.Monster.B.TwoA.Census in
theorem certificate3018 : (certOK amul sylowGens idArr sylowCert = true)
    ∧ (certOK amul c1Gens idArr cent1Cert = true)
    ∧ (certOK amul c2Gens idArr cent2Cert = true)
    ∧ (certOK aconj abGens (seedArr.getD 1 #[]) orb1Cert = true)
    ∧ (certOK aconj abGens (seedArr.getD 2 #[]) orb2Cert = true)
    ∧ (sylowCert.pts.size = 1024)
    ∧ (cent1Cert.pts.size = 21504)
    ∧ (cent2Cert.pts.size = 7680)
    ∧ (orb1Cert.pts.size = 11385)
    ∧ (orb2Cert.pts.size = 31878)
    ∧ ((invIdx sylowCert).length = 191)
    ∧ (invCovered = true)
    ∧ (∀ a ∈ sylowGenArr, AutArr a)
    ∧ (∀ j < 3, ∀ a ∈ centGenArrs j, AutArr a)
    ∧ (∀ a ∈ seedArr, AutArr a)
    ∧ (∀ j ∈ [1, 2], ∀ a ∈ centGenArrs j,
       amul a (seedArr.getD j #[]) = amul (seedArr.getD j #[]) a) :=
  ⟨sylowF.1, cent1.1, cent2.1, orb1F.1, orb2F.1, sylowF.2.1, cent1.2, cent2.2, orb1F.2.1,
    orb2F.2.1, invLen, covered, aut1, aut2, aut3, comm⟩

end Certificates

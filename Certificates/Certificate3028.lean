
module

public import Certificates.Certificate3028Base

public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import Certificates.Kernel.MonsterB.Co2Perms
public import Certificates.Kernel.MonsterB.Mat3028Tabs
public import CFSG.Certificates.Kernel.MonsterB.Co2MatSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import Certificates.Certificate3131

public section

open CFSG.Monster.B.Co2 CFSG.Monster.VisCert.Native CFSG.KC.Co2Mem CFSG.KC.U6Orb CFSG.KLie.CT
  CFSG.KS.Raw CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3028

open CFSG.Monster.B.Co2 CFSG.Monster.VisCert.Native CFSG.KC.Co2Mem CFSG.KC.U6Orb CFSG.KLie.CT
  CFSG.KS.Raw CertificateChecks.KernelMonB

set_option maxRecDepth 100000

@[expose] def FI1 : Array Nat := #[13407452, 12978240, 8496943, 4793655, 571, 12721280, 8055318,
  922424, 5209100, 8496896, 14674188, 16194068, 32768, 65536, 13230080, 4096, 8192, 5976064,
  11243520, 11911168, 8388608, 16400384, 7163904, 1048576]

@[expose] def FI2 : Array Nat := #[8, 12960139, 14198861, 615966, 1335513, 28470, 14198985,
  12960201, 10442679, 4717815, 7926775, 12402295, 11243520, 7163904, 5976064, 4096, 65536, 131072,
  16384, 524288, 8192, 2097152, 13230080, 8388608]

@[expose] def finvK (k : Nat) : Array Nat :=
  if k = 1 then FI1 else if k = 2 then FI2 else (Native.frameInv ())[k]!

theorem kInv1 : (Native.invMat 24 (frameRows ())[1]!).toList = FI1.toList := by
  simp only [Native.invMat, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  decide +kernel

theorem kInv2 : (Native.invMat 24 (frameRows ())[2]!).toList = FI2.toList := by
  simp only [Native.invMat, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size]
  decide +kernel

theorem frameInv_eq {k : Nat} (hk : k < 15) :
    (Native.frameInv ())[k]! = Native.invMat 24 (frameRows ())[k]! := by
  have hs : (frameRows ()).size = 15 := by decide +kernel
  rw [Native.frameInv, getElem!_pos _ _ (by simpa [hs] using hk), Array.getElem_map,
    ← getElem!_pos]

theorem frameInv_get (k : Nat) : (Native.frameInv ())[k]! = finvK k := by
  unfold finvK
  split
  · subst_vars
    rw [frameInv_eq (by norm_num)]
    exact Array.toList_inj.1 kInv1
  · split
    · subst_vars
      rw [frameInv_eq (by norm_num)]
      exact Array.toList_inj.1 kInv2
    · rfl

@[expose] def pairLetterActK (l : Int) (x : Nat) : Nat :=
  if 0 < l then actRows (frameRows ())[l.natAbs]! x else actRows (finvK l.natAbs) x

@[expose] def pairWordActK : List Int → Nat → Nat
  | [], x => x
  | l :: w, x => pairWordActK w (pairLetterActK l x)

@[expose] def recordActK (r : Native.GenRecord) (x : Nat) : Nat :=
  match r.kind with
  | .pairStabilizer => pairWordActK r.word x
  | _ => Native.frameWordAct r.word x

theorem pairWordAct_eq : ∀ (w : List Int) (x : Nat), Native.pairWordAct w x = pairWordActK w x
  | [], _ => rfl
  | l :: w, x => by
    rw [Native.pairWordAct, pairWordActK, ← pairWordAct_eq w]
    congr 1
    unfold Native.pairLetterAct pairLetterActK
    rw [frameInv_get]

theorem recordAct_eq (r : Native.GenRecord) (x : Nat) : Native.recordAct r x = recordActK r x := by
  rcases r with ⟨k, w, m, q⟩
  cases k <;> simp [Native.recordAct, recordActK, pairWordAct_eq]

theorem kFrame : Native.allLt 2 (fun j => Native.allLt 24 fun i =>
    actRows (frameRows ())[j + 1]! (finvK (j + 1))[i]! == 1 <<< i) = true := by
  simp only [allLt_iff]
  decide +kernel

theorem kRecords : Native.allLt 24 (fun r => Native.allLt 24 fun k =>
    recordActK (Native.genRecords ())[r]! (1 <<< k) == ((Native.genRecords ())[r]!.matrix)[k]!) =
      true := by
  simp only [allLt_iff]
  decide +kernel

theorem kSeed : Native.allLt 24 (fun r =>
    actRows (Native.genRecords ())[r]!.matrix (Native.vSeed ()) == Native.vSeed ()) = true := by
  simp only [allLt_iff]
  decide +kernel

theorem kQuot : Native.allLt 24 (fun r => Native.allLt 22 fun t =>
    decide (((Native.genRecords ())[r]!.quotientMatrix)[t]! < 2 ^ 22) &&
      ((actRows (Native.genRecords ())[r]!.matrix Native.quotientBasis[t]! ^^^
          Native.actD 22 Native.quotientBasis ((Native.genRecords ())[r]!.quotientMatrix)[t]!) ==
            0 ||
        (actRows (Native.genRecords ())[r]!.matrix Native.quotientBasis[t]! ^^^
          Native.actD 22 Native.quotientBasis ((Native.genRecords ())[r]!.quotientMatrix)[t]!) ==
            Native.vSeed ())) = true := by
  simp only [allLt_iff]
  decide +kernel

theorem kSpanIdx : Native.spanIdx.size = 22 ∧ ∀ t < 22, Native.spanIdx[t]! < 2300 := by
  decide +kernel

theorem kSpan : Native.allLt 22 (fun t => Native.actD 22 (Native.spanIdx.toList.map vecF).toArray
    Native.spanInv[t]! == 1 <<< t) = true := by
  simp only [allLt_iff]
  decide +kernel

theorem kWords : ∀ i < 2, ∀ l ∈ (Native.pairWords ())[i]!, 0 < l.natAbs ∧ l.natAbs ≤ 24 := by
  decide +kernel

theorem kSortPerm : permF 2300 Co2S 2300 0 = true := by quickRfl

theorem kSort : allN 2299 (fun k => Nat.blt (vecF (Co2S k)) (vecF (Co2S (Nat.succ k)))) = true := by
  quickRfl

theorem kPI : allN 24 (fun k => allN 2300 fun y =>
    andB (Nat.blt (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2PI k) y) 2300)
      (Nat.beq (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2P.F k)
        (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2PI k) y)) y)) =
    true := by
  quickRfl

theorem kQM : allN 24 (fun r =>
    andB (shapeL 22 (pw2 22) [((Native.genRecords ())[r]!.quotientMatrix)])
    (Nat.beq (packL 22 ((Native.genRecords ())[r]!.quotientMatrix).toList) (Co2QM r))) = true := by
  quickRfl

@[expose] noncomputable def recK (r : Nat) : Bool :=
  allN 2300 fun j => Nat.beq (actK (Co2QM r) (vecF j))
    (vecF (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2P.F r) j))

@[expose] noncomputable def kHF (r : Nat) : Bool := recK r

#kc_each_unfold kHF 0 24 as CertificateChecks.Batch3028.kH

#kc_forall_chunks kHK (fun r => recK r = true) 24 CertificateChecks.Batch3028.kH 1

theorem kH : ∀ r < 24, recK r = true := kHK

@[expose] noncomputable def pairK (i : Nat) : Bool :=
  allN 2300 fun x => Nat.beq (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2Q.F i) x)
    (wordK Co2P.F Co2PI (Native.pairWords ())[i]! x)

theorem kI0 : pairK 0 = true := by quickRfl

theorem kI1 : pairK 1 = true := by quickRfl

@[expose] noncomputable def pa (y : Nat) : Nat := CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2Q.F 0) y

@[expose] noncomputable def pb (y : Nat) : Nat := CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2Q.F 1) y

theorem kPow : andB (allN 2300 fun x => Nat.beq (iterK pa 2 x) x)
    (andB (allN 2300 fun x => Nat.beq (iterK pb 5 x) x)
      (allN 2300 fun x => Nat.beq (iterK (fun y => pa (pb y)) 23 x) x)) = true := by
  quickRfl

theorem kNe : andB (notB (Nat.beq (pa 0) 0)) (andB (notB (Nat.beq (pb 0) 0))
    (notB (Nat.beq (pa (pb 0)) 0))) = true := by
  quickRfl

theorem vec_lt {j : Nat} (hj : j < 2300) : vecF j < 2 ^ 22 := by
  have := (allN_iff _ _).1 CertificateChecks.Batch3131.kBound j hj
  rwa [Nat.blt_eq, pw2_eq] at this

theorem vec_inj : ∀ a b, a < 2300 → b < 2300 → vecF a = vecF b → a = b := by
  obtain ⟨h1, h2⟩ := permF_sound 2300 Co2S 2300 0 kSortPerm
  refine inj_of_sorted (S := Co2S) (fun k hk => (h1 k hk).1) h2 fun k hk => ?_
  have := (allN_iff _ _).1 kSort k (by omega)
  rwa [Nat.blt_eq] at this

theorem vecPos_get {j : Nat} (hj : j < 2300) :
    (Native.vecPos ())[(Native.vectors ())[j]!]! = j := by
  have e : Native.vecPos () = (List.range' 0 2300).foldl
      (fun r i => r.set! (Native.vectors ())[i]! i) (Array.replicate (2 ^ 22) 2300) := by
    simp [Native.vecPos, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
      List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size]
    rfl
  rw [e]
  refine (foldl_set_spec (g := fun i => (Native.vectors ())[i]!) (n := 2300) (fun i hi => ?_)
    (fun a b ha hb h => ?_) 2300 le_rfl).2 j hj
  · rw [vectors_getElem! hi]
    exact vec_lt hi
  · rw [vectors_getElem! ha, vectors_getElem! hb] at h
    exact vec_inj a b ha hb h

theorem perm_get {r j : Nat} (hr : r < 24) (hj : j < 2300) :
    ((Native.permutations ())[r]!)[j]! = CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2P.F r) j ∧
      CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2P.F r) j < 2300 := by
  have := (permutations_perm hr).1 j hj
  rw [permutations_getElem! hr, unpack_getElem! hj] at this ⊢
  exact ⟨rfl, this⟩

theorem act_get {r : Nat} (hr : r < 24) (v : Nat) :
    Native.actD 22 (Native.genRecords ())[r]!.quotientMatrix v = actK (Co2QM r) v := by
  obtain ⟨h1, h2⟩ := andB_eq_true.1 ((allN_iff _ _).1 kQM r hr)
  obtain ⟨hs, hb⟩ := (shapeL_iff 22 (pw2 22) _).1 h1 _ (List.mem_singleton_self _)
  rw [actD_eq_actK hs (fun x hx => (hb x hx).trans_eq (pw2_eq 22)), Nat.eq_of_beq_eq_true h2]

theorem letter_get {l : Int} (hl : 0 < l.natAbs ∧ l.natAbs ≤ 24) {y : Nat} (hy : y < 2300) :
    CFSG.KC.Co2Mem.letterK Co2P.F Co2PI l y = (Native.permLetter l)[y]! ∧
      (Native.permLetter l)[y]! < 2300 := by
  have hk : l.natAbs - 1 < 24 := by omega
  unfold CFSG.KC.Co2Mem.letterK Native.permLetter
  by_cases h0 : 0 < l
  · simp only [h0, decide_true, ite_true]
    obtain ⟨e, hlt⟩ := perm_get hk hy
    rw [Nat.sub_eq, e]
    exact ⟨rfl, hlt⟩
  · simp only [h0, decide_false, ite_false]
    obtain ⟨b1, b2⟩ := andB_eq_true.1 ((allN_iff _ _).1 ((allN_iff _ _).1 kPI _ hk) y hy)
    rw [Nat.blt_eq] at b1
    rw [Nat.beq_eq] at b2
    have hperm := permutations_perm hk
    have hinv : (Native.permInv ())[l.natAbs - 1]! =
        Native.invCand (Native.deg ()) (Native.permutations ())[l.natAbs - 1]! := by
      have hs : (Native.permutations ()).size = 24 := by simp [Native.permutations]
      rw [Native.permInv, getElem!_pos _ _ (by simpa [hs] using hk), Array.getElem_map,
        ← getElem!_pos]
    have hy' : ((Native.permutations ())[l.natAbs - 1]!)[CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12)
        (Co2PI (l.natAbs - 1)) y]! = y := by
      rw [(perm_get hk b1).1]
      exact b2
    have := invCand_spec (n := 2300) hperm.1 hperm.2 _ b1
    rw [hy'] at this
    rw [hinv, Nat.sub_eq]
    change CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2PI (l.natAbs - 1)) y =
      (Native.invCand 2300 (Native.permutations ())[l.natAbs - 1]!)[y]! ∧
        (Native.invCand 2300 (Native.permutations ())[l.natAbs - 1]!)[y]! < 2300
    rw [this]
    exact ⟨rfl, b1⟩

theorem pair_get {i : Nat} (hi : i < 2) {x : Nat} (hx : x < 2300) :
    ((Native.pairPerms ())[i]!)[x]! = CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2Q.F i) x ∧
      CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) (Co2Q.F i) x < 2300 := by
  have := (pairPerms_perm hi).1 x hx
  rw [pairPerms_getElem! hi, unpack_getElem! hx] at this ⊢
  exact ⟨rfl, this⟩

theorem word_ok {i : Nat} (hi : i < 2) :
    Native.eqA (Native.deg ()) (Native.pairPerms ())[i]!
      (Native.wordPermA (Native.pairWords ())[i]!) = true := by
  rw [CFSG.KC.Co2Mem.eqA_iff]
  intro x hx
  have hl := fun l hl y hy => letter_get (kWords i hi l hl) (y := y) hy
  rw [(wordPermA_get _ (fun l h y hy => (hl l h y hy).2) x hx).1,
    ← wordK_eq _ hl x hx, (pair_get hi hx).1]
  have hK : pairK i = true := by
    rcases i with _ | _ | i
    · exact kI0
    · exact kI1
    · omega
  exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 hK x hx)

theorem pa_get {y : Nat} (hy : y < 2300) : ((Native.pairPerms ())[0]!)[y]! = pa y ∧ pa y < 2300 :=
  pair_get (by norm_num) hy

theorem pb_get {y : Nat} (hy : y < 2300) : ((Native.pairPerms ())[1]!)[y]! = pb y ∧ pb y < 2300 :=
  pair_get (by norm_num) hy

theorem pow_ok {t : Array Nat} {f : Nat → Nat} (ht : ∀ y < 2300, t[y]! = f y ∧ f y < 2300)
    {e : Nat} (hk : allN 2300 (fun x => Nat.beq (iterK f e x) x) = true) :
    Native.eqA (Native.deg ()) (Native.powA t e) (Native.idA (Native.deg ())) = true := by
  rw [CFSG.KC.Co2Mem.eqA_iff]
  intro x hx
  have hb : ∀ y < 2300, t[y]! < 2300 := fun y hy => (ht y hy).1 ▸ (ht y hy).2
  rw [(CFSG.KC.Co2Mem.powA_get hb e x hx).1, CFSG.KC.Co2Mem.idA_get hx,
    (iterK_congr (fun y hy => ⟨(ht y hy).1, hb y hy⟩) e x hx).1]
  exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 hk x hx)

theorem ne_ok {t : Array Nat} {f : Nat → Nat} (ht : t[0]! = f 0)
    (hk : notB (Nat.beq (f 0) 0) = true) :
    (!Native.eqA (Native.deg ()) t (Native.idA (Native.deg ()))) = true := by
  rw [Bool.not_eq_true']
  by_contra h
  rw [Bool.not_eq_false, CFSG.KC.Co2Mem.eqA_iff] at h
  have := h 0 (by decide)
  rw [ht, CFSG.KC.Co2Mem.idA_get (by decide)] at this
  rw [notB_eq, this] at hk
  exact absurd hk (by decide)

theorem ab_get {y : Nat} (hy : y < 2300) :
    (Native.compA (Native.deg ()) (Native.pairPerms ())[0]! (Native.pairPerms ())[1]!)[y]! =
      pa (pb y) ∧ pa (pb y) < 2300 := by
  rw [CFSG.KC.Co2Mem.compA_get (n := Native.deg ()) hy, (pb_get hy).1]
  exact pa_get (pb_get hy).2

theorem matCheck_eq_true : Native.matCheck = true := by
  obtain ⟨p1, hp⟩ := andB_eq_true.1 kPow
  obtain ⟨p2, p3⟩ := andB_eq_true.1 hp
  obtain ⟨n1, hn⟩ := andB_eq_true.1 kNe
  obtain ⟨n2, n3⟩ := andB_eq_true.1 hn
  obtain ⟨s1, s2⟩ := kSpanIdx
  have hspan : Native.spanIdx.map (fun j => (Native.vectors ())[j]!) =
      (Native.spanIdx.toList.map vecF).toArray := by
    apply Array.toList_inj.1
    rw [Array.toList_map, List.toList_toArray]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 22 := by simpa [s1] using hi
    have := s2 i hi'
    rw [getElem!_pos _ _ (by simpa [s1] using hi'), ← Array.getElem_toList] at this
    exact vectors_getElem! this
  unfold Native.matCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩
  · simp only [frameInv_get]
    exact kFrame
  · simp only [recordAct_eq]
    exact kRecords
  · exact kSeed
  · exact kQuot
  · rw [allLt_iff]
    intro j hj
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, vecPos_get hj, vectors_getElem! hj]
    exact ⟨vec_lt hj, rfl⟩
  · rw [beq_iff_eq]
    exact s1
  · rw [allLt_iff]
    intro t ht
    exact decide_eq_true (s2 t ht)
  · rw [hspan]
    exact kSpan
  · rw [allLt_iff]
    intro r hr
    rw [allLt_iff]
    intro j hj
    obtain ⟨e1, e2⟩ := perm_get hr hj
    rw [beq_iff_eq, act_get hr, vectors_getElem! hj, e1, vectors_getElem! e2]
    exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 (kH r hr) j hj)
  · rw [allLt_iff]
    intro i hi
    exact word_ok hi
  · exact pow_ok (fun y hy => pa_get hy) p1
  · exact pow_ok (fun y hy => pb_get hy) p2
  · exact pow_ok (fun y hy => ab_get hy) p3
  · exact ne_ok (pa_get (by decide)).1 n1
  · exact ne_ok (pb_get (by decide)).1 n2
  · exact ne_ok (f := fun y => pa (pb y)) (ab_get (by decide)).1 n3

end CertificateChecks.Batch3028

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 in
theorem certificate3028 : Native.matCheck = true := CertificateChecks.Batch3028.matCheck_eq_true

end Certificates

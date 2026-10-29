module

public import Certificates.Kernel.Co3T.ChecksA
public import Certificates.Kernel.Co3T.ChecksH
public import Certificates.Kernel.Co3T.ChecksC
public import Certificates.Kernel.Co3T.ChecksT0
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.Misc.ChainTailOrbSound
public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Certificates.Kernel.Spor.RebuildSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Sporadic.Schreier.Co3Restrict
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeInputs
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.BfsReplay
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Co3TK CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CertificateChecks.KernelSpor
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne
open CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hw : szOK 276 9 = true := by quickRfl

theorem bq {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem bqf {a b : Nat} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, bq]

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem perm_eq {k : Nat} (hk : k < 36) : perm k = unpack 276 9 (TT.L k) := by
  unfold perm
  rw [TT.eq]
  have := CFSG.KS.Text.hexBind_sound TT.all k hk
  rwa [Nat.zero_add] at this

theorem pP {k : Nat} (hk : k < 36) : permB 276 9 (TT.L k) = true := Orb.allN_iff.1 kPerm k hk

theorem sAll_spec {G : Nat} (h : sAll G = true) :
    Nat.beq (Nat.shiftRight G (276 * 9)) 0 = true ∧
      allN 276 (fun t => Nat.blt (pg 9 (mask 9) G t) 276) = true ∧
      siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3C.LR Co3C.TRI Co3C.BP 7 0 G = true :=
  and3 h

theorem inP_of {G : Nat} (h : sAll G = true) : inP (levels ()) (unpack 276 9 G) = true :=
  siftA_of Co3C.binds Co3C.perm Co3C.hl (sAll_spec h)

theorem keys_eq : keys = co3ChainBaseArr.toList := by decide +kernel

theorem hkeys : ∀ p ∈ co3ChainBaseArr.toList, p < 276 := by decide +kernel

theorem eQ : Nat.beq EQ.ng 4 = true ∧ Nat.beq EQ.N 2187 = true ∧
    allN 4 (fun k => Nat.beq (EQ.G k) (TT.L k)) = true := and3 kEQ

theorem eC : Nat.beq EC.ng 3 = true ∧ Nat.beq EC.N 4536 = true ∧
    allN 3 (fun k => Nat.beq (EC.G k) (TT.L (9 + k))) = true := and3 kEC

theorem bindQ : BindA 276 9 (qGens ()) EQ.ng EQ.G := by
  rw [Nat.eq_of_beq_eq_true eQ.1]
  refine ⟨by simp [qGens], fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eQ.2.2 j hj)]
  unfold qGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem bindC : BindA 276 9 (cGens ()) EC.ng EC.G := by
  rw [Nat.eq_of_beq_eq_true eC.1]
  refine ⟨by simp [cGens], fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eC.2.2 j hj)]
  unfold cGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem pQG : ∀ k < EQ.ng, permB 276 9 (EQ.G k) = true := by
  intro k hk
  rw [Nat.eq_of_beq_eq_true eQ.1] at hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eQ.2.2 k hk)]
  exact pP (by omega)

theorem pCG : ∀ k < EC.ng, permB 276 9 (EC.G k) = true := by
  intro k hk
  rw [Nat.eq_of_beq_eq_true eC.1] at hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eC.2.2 k hk)]
  exact pP (by omega)

theorem enumQ : enumOK 276 (qGens ()) co3ChainBaseArr.toList
      (enumBfs 276 (qGens ()) co3ChainBaseArr.toList 2200) = true ∧
    (enumBfs 276 (qGens ()) co3ChainBaseArr.toList 2200).pts.size = EQ.N ∧
    ∀ i < EQ.N, (enumBfs 276 (qGens ()) co3ChainBaseArr.toList 2200).pts[i]! =
      unpack 276 9 (EQ.T i) :=
  enum_of bindQ pQG EQ.ok hkeys EQ.keys (by rw [Nat.eq_of_beq_eq_true eQ.2.1]; norm_num)

theorem enumC : enumOK 276 (cGens ()) co3ChainBaseArr.toList
      (enumBfs 276 (cGens ()) co3ChainBaseArr.toList 4600) = true ∧
    (enumBfs 276 (cGens ()) co3ChainBaseArr.toList 4600).pts.size = EC.N ∧
    ∀ i < EC.N, (enumBfs 276 (cGens ()) co3ChainBaseArr.toList 4600).pts[i]! =
      unpack 276 9 (EC.T i) :=
  enum_of bindC pCG EC.ok hkeys kECkeys (by rw [Nat.eq_of_beq_eq_true eC.2.1]; norm_num)

theorem nQ : EQ.N = 2187 := Nat.eq_of_beq_eq_true eQ.2.1
theorem nC : EC.N = 4536 := Nat.eq_of_beq_eq_true eC.2.1

theorem qPts_get {k : Nat} (hk : k < 2187) : (qCert ()).pts[k]! = unpack 276 9 (EQ.T k) := by
  unfold qCert
  rw [keys_eq]
  exact enumQ.2.2 k (by rw [nQ]; exact hk)

theorem cPts_get {k : Nat} (hk : k < 4536) : (cCert ()).pts[k]! = unpack 276 9 (EC.T k) := by
  unfold cCert
  rw [keys_eq]
  exact enumC.2.2 k (by rw [nC]; exact hk)

theorem qSize : (qCert ()).pts.size = 2187 := by
  unfold qCert
  rw [keys_eq, enumQ.2.1, nQ]

theorem cSize : (cCert ()).pts.size = 4536 := by
  unfold cCert
  rw [keys_eq, enumC.2.1, nC]

theorem pQT {k : Nat} (hk : k < 2187) : permB 276 9 (EQ.T k) = true :=
  Orb.allN_iff.1 EQ.perm k (by rw [nQ]; exact hk)

theorem pCT {k : Nat} (hk : k < 4536) : permB 276 9 (EC.T k) = true :=
  permB_of_pp (CFSG.KC.BfsPin.PP_pts EC.ok (fun j hj => pCG j hj) k (by rw [nC]; exact hk))

theorem qCheck_eq : qCheck () = true := by
  unfold qCheck qCert
  dsimp only
  rw [keys_eq, enumQ.1]
  have hs : (enumBfs 276 (qGens ()) co3ChainBaseArr.toList 2200).pts.size = 2187 := by
    rw [enumQ.2.1, nQ]
  simp only [hs, Bool.true_and, beq_self_eq_true, allLt_iff]
  intro k hk
  rw [bindQ.2 k (by rw [Nat.eq_of_beq_eq_true eQ.1]; exact hk),
    Nat.eq_of_beq_eq_true (Orb.allN_iff.1 eQ.2.2 k hk)]
  exact inP_of (Orb.allN_iff.1 kSiftQ k hk)

theorem cu {p q : Nat} (hp : permB 276 9 p = true) (hq : permB 276 9 q = true) :
    compA 276 (unpack 276 9 p) (unpack 276 9 q) = unpack 276 9 (cm 276 9 p q) :=
  comp_unpack' hw hp hq

theorem pu {p : Nat} (hp : permB 276 9 p = true) (e : Nat) :
    powArr 276 (unpack 276 9 p) e = unpack 276 9 (pw 276 9 p e) := pow_unpack' hw hp e

theorem pcm {p q : Nat} (hp : permB 276 9 p = true) (hq : permB 276 9 q = true) :
    permB 276 9 (cm 276 9 p q) = true := permB_pcomp hw hp hq

theorem ppw {p : Nat} (hp : permB 276 9 p = true) (e : Nat) : permB 276 9 (pw 276 9 p e) = true :=
  permB_ppow hw hp e

theorem pcj {p q : Nat} (hp : permB 276 9 p = true) (hq : permB 276 9 q = true) :
    permB 276 9 (cj 276 9 p q) = true := pcm hp (pcm hq (permB_pinvS hw hp))

theorem eqU {p q : Nat} (hp : permB 276 9 p = true) (hq : permB 276 9 q = true) :
    eqA 276 (unpack 276 9 p) (unpack 276 9 q) = Nat.beq p q := eqA_unpack' hw hp hq

theorem getU {p i : Nat} (hi : i < 276) : (unpack 276 9 p)[i]! = pg 9 (mask 9) p i :=
  Orb.unpack_get hi

theorem kD4 : ((allN 5 (fun i => permB 276 9 (TT.L (4 + i)) &&
      Nat.beq (pw 276 9 (TT.L (4 + i)) 3) (pidn 276 9)) = true ∧
    allN 5 (fun i => allN 5 fun j => Nat.beq (cm 276 9 (TT.L (4 + i)) (TT.L (4 + j)))
      (cm 276 9 (TT.L (4 + j)) (TT.L (4 + i)))) = true) ∧
    allN 243 (fun k => Nat.beq (DE k) (dProdK TT.L k)) = true) ∧
    allN 243 (fun k => allN 243 fun k' => Nat.beq k k' || !Nat.beq (DE k) (DE k')) = true := by
  have h := kD
  unfold dK at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem DE_eq {k : Nat} (hk : k < 243) : DE k = dProdK TT.L k :=
  Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kD4.1.2 k hk)

theorem dg_get {i : Nat} (hi : i < 5) : (dGens ())[i]! = unpack 276 9 (TT.L (4 + i)) := by
  unfold dGens
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem pDP (k : Nat) : permB 276 9 (dProdK TT.L k) = true := by
  unfold dProdK
  exact pcm (ppw (pP (by norm_num)) _) (pcm (ppw (pP (by norm_num)) _) (pcm (ppw (pP (by norm_num)) _)
    (pcm (ppw (pP (by norm_num)) _) (ppw (pP (by norm_num)) _))))

theorem pDE {k : Nat} (hk : k < 243) : permB 276 9 (DE k) = true := by
  rw [DE_eq hk]
  exact pDP k

theorem E_get {k : Nat} (hk : k < 243) : (dElts ())[k]! = unpack 276 9 (DE k) := by
  unfold dElts
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, DE_eq hk]
  unfold dProd dProdK
  rw [dg_get (by norm_num : 0 < 5), dg_get (by norm_num : 1 < 5), dg_get (by norm_num : 2 < 5),
    dg_get (by norm_num : 3 < 5), dg_get (by norm_num : 4 < 5)]
  have p4 := pP (k := 4 + 0) (by norm_num)
  have p5 := pP (k := 4 + 1) (by norm_num)
  have p6 := pP (k := 4 + 2) (by norm_num)
  have p7 := pP (k := 4 + 3) (by norm_num)
  have p8 := pP (k := 4 + 4) (by norm_num)
  rw [pu p4, pu p5, pu p6, pu p7, pu p8, cu (ppw p7 _) (ppw p8 _),
    cu (ppw p6 _) (pcm (ppw p7 _) (ppw p8 _)),
    cu (ppw p5 _) (pcm (ppw p6 _) (pcm (ppw p7 _) (ppw p8 _))),
    cu (ppw p4 _) (pcm (ppw p5 _) (pcm (ppw p6 _) (pcm (ppw p7 _) (ppw p8 _))))]
  rfl

theorem dCheck_eq : dCheck () = true := by
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := kD4
  unfold dCheck
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨fun i hi => ?_, fun i hi j hj => ?_⟩, fun k hk k' hk' => ?_⟩
  · have hi' := and3 (by simpa [Bool.and_assoc] using Orb.allN_iff.1 h1 i hi :
      (permB 276 9 (TT.L (4 + i)) && Nat.beq (pw 276 9 (TT.L (4 + i)) 3) (pidn 276 9) && true) = true)
    rw [dg_get hi, validA_of hi'.1, inP_of (Orb.allN_iff.1 kSiftD i hi), powEq_id hw hi'.1]
    simpa using hi'.2.1
  · have pi := pP (k := 4 + i) (by omega)
    have pj := pP (k := 4 + j) (by omega)
    rw [dg_get hi, dg_get hj]
    unfold CFSG.RankThree.Native.commA
    rw [cu pi pj, cu pj pi, eqU (pcm pi pj) (pcm pj pi)]
    exact Orb.allN_iff.1 (Orb.allN_iff.1 h2 i hi) j hj
  · have h := Orb.allN_iff.1 (Orb.allN_iff.1 h4 k hk) k' hk'
    by_cases e : k = k'
    · simp [e]
    · rw [E_get hk, E_get hk', eqU (pDE hk) (pDE hk')]
      simp only [Bool.or_eq_true, bq, Bool.not_eq_true', bqf] at h
      rw [Bool.or_eq_true]
      right
      rw [Bool.not_eq_true', bqf]
      rcases h with h | h
      · exact absurd h e
      · exact h

theorem hbl : ∀ t < 7, co3ChainBaseArr[t]! < 276 := Orb.base_lt_of_levels Co3C.binds Co3C.hl

theorem reb_succ (B : Nat → Nat) (j : Nat) :
    rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI B (j + 1) =
      rebStep 276 9 Co3C.LR Co3C.TR Co3C.TRI B (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI B j) j := by
  simp [rebK, List.range_succ, List.foldl_append]

theorem reb_ok (B : Nat → Nat) (h : (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI B 7).2.2 = true) :
    ∀ j < 7, B j < 276 ∧ rpos 9 (mask 9) (276 * 9) (Co3C.LR j)
      (pg 9 (mask 9) (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI B j).2.1 (B j)) < rcnt (Co3C.LR j) := by
  have down : ∀ d, d ≤ 7 → (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI B (7 - d)).2.2 = true := by
    intro d
    induction d with
    | zero => intro _; exact h
    | succ d ih =>
      intro hd
      have h' := ih (by omega)
      rw [show 7 - d = (7 - (d + 1)) + 1 by omega, reb_succ] at h'
      unfold rebStep at h'
      simp only [Bool.and_eq_true] at h'
      exact h'.1.1
  intro j hj
  have h' := down (6 - j) (by omega)
  rw [show 7 - (6 - j) = j + 1 by omega, reb_succ] at h'
  unfold rebStep at h'
  simp only [Bool.and_eq_true, Nat.blt_eq] at h'
  exact ⟨h'.1.2, h'.2⟩

theorem rebuild_eq {beta : Array Nat}
    (h : (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => beta[l]!) 7).2.2 = true) :
    rebuild (levels ()) beta =
      unpack 276 9 (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => beta[l]!) 7).1 := by
  have hok := reb_ok _ h
  have key := CFSG.KS.BfsReplay.forIn_range'_yield 7 0 (idA 276, idA 276)
    (fun i (s : Array Nat × Array Nat) =>
      (pure (ForInStep.yield (compA 276 s.1 (levels ())[i]!.tr[(levels ())[i]!.pos[s.2[beta[i]!]!]!]!,
        compA 276 (levels ())[i]!.trInv[(levels ())[i]!.pos[s.2[beta[i]!]!]!]! s.2)) :
          Id (ForInStep (Array Nat × Array Nat))))
    (fun j s => Orb.RebSt 276 9 s.1 s.2 (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => beta[l]!) j).1
      (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => beta[l]!) j).2.1)
    (fun j hj s hs => by
      refine ⟨_, rfl, ?_⟩
      rw [Nat.zero_add, reb_succ]
      obtain ⟨hb, hk⟩ := hok j hj
      obtain ⟨A, hT⟩ := Orb.agree_levelK Co3C.binds Co3C.perm hbl hj (Co3C.hl j hj)
      exact (Orb.rebStep_spec (by norm_num) A hT hs hb hk).2)
    (Orb.rebSt_init (by norm_num) (by norm_num))
  obtain ⟨hs, -, γ, ha, -, hA, -⟩ := key
  unfold rebuild
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  exact Orb.rep_eq_unpack hs ha hA

theorem find_range {p : Nat → Bool} {c : Nat} (hp : p c = true) (hlt : ∀ k < c, p k = false) :
    ∀ N, c < N → (List.range N).find? p = some c := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro hc
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge c N with h | h
    · rw [ih h]
      rfl
    · have e : c = N := by omega
      subst e
      have hn : (List.range c).find? p = none := by
        rw [List.find?_eq_none]
        intro k hk
        rw [hlt k (List.mem_range.1 hk)]
        simp
      rw [hn]
      simp [hp]

theorem pp_lt {G i : Nat} (hG : permB 276 9 G = true) (hi : i < 276) : pg 9 (mask 9) G i < 276 :=
  (pp_of_permB hw hG).2.1 i hi

theorem coordOf_eq {G l c : Nat} (hG : permB 276 9 G = true) (hl : l < 276)
    (h : coordK DE G l c = true) : coordOf (dElts ()) (unpack 276 9 G) l = c := by
  unfold coordK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hc, he⟩, hlt⟩ := h
  have h0 : (unpack 276 9 G)[0]! = pg 9 (mask 9) G 0 := getU (by norm_num)
  have hl' : (unpack 276 9 G)[l]! = pg 9 (mask 9) G l := getU hl
  unfold coordOf
  have hE : ∀ k < 243, ((dElts ())[k]!)[(unpack 276 9 G)[0]!]! = pg 9 (mask 9) (DE k)
      (pg 9 (mask 9) G 0) := fun k hk => by
    rw [E_get hk, h0, getU (pp_lt hG (by norm_num))]
  rw [find_range (c := c) ?_ ?_ 243 hc]
  · rfl
  · rw [hE c hc, hl']
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true he)
  · intro k hk
    have := Orb.allN_iff.1 hlt k hk
    rw [hE k (by omega), hl']
    rw [Bool.not_eq_true', bqf] at this
    simpa using this

theorem hyp_parts {j : Nat} (hj : j < 121) :
    (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => (hypTuples[j]!)[l]!) 7).2.2 = true ∧
      (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => (hypTuples[j]!)[l]!) 7).1 = GJ j ∧
      permB 276 9 (GJ j) = true ∧ sAll (GJ j) = true ∧
      ∀ l < 7, coordK DE (GJ j) l (CK (7 * j + l)) = true := by
  have h := Orb.allN_iff.1 kHyp j hj
  unfold hypK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, Nat.eq_of_beq_eq_true h.1.1.1.2, h.1.1.2, h.1.2, Orb.allN_iff.1 h.2⟩

theorem hyp_size : hypTuples.size = 121 := by decide

theorem G_get {j : Nat} (hj : j < 121) :
    (hypTuples.map (rebuild (levels ())))[j]! = unpack 276 9 (GJ j) := by
  rw [getElem!_pos _ j (by simpa [hyp_size] using hj), Array.getElem_map,
    ← getElem!_pos hypTuples j (by simpa [hyp_size] using hj), rebuild_eq (hyp_parts hj).1,
    (hyp_parts hj).2.1]

theorem C_get {j l : Nat} (hj : j < 121) (hl : l < 7) :
    (((hypTuples.map (rebuild (levels ()))).map fun g =>
      Array.ofFn (n := 7) fun l => coordOf (dElts ()) g l.val)[j]!)[l]! = CK (7 * j + l) := by
  rw [getElem!_pos _ j (by simpa [hyp_size] using hj), Array.getElem_map,
    ← getElem!_pos _ j (by simpa [hyp_size] using hj), G_get hj,
    getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]
  exact coordOf_eq (hyp_parts hj).2.2.1 (by omega) ((hyp_parts hj).2.2.2.2 l hl)

theorem hypCheck_eq : hypCheck () = true := by
  unfold hypCheck
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff, Array.size_map, hyp_size, true_and]
  refine ⟨fun j hj => ?_, fun m hm => ?_⟩
  · obtain ⟨-, -, hp, hs, hc⟩ := hyp_parts hj
    rw [G_get hj, validA_of hp, inP_of hs]
    refine ⟨⟨rfl, rfl⟩, fun l hl => ?_⟩
    rw [C_get hj hl]
    have h := hc l hl
    unfold coordK at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨h.1.1, ?_⟩
    rw [E_get h.1.1, getU (p := GJ j) (i := 0) (by norm_num),
      getU (p := DE (CK (7 * j + l))) (pp_lt hp (by norm_num)), getU (p := GJ j) (i := l) (by omega)]
    exact Nat.eq_of_beq_eq_true h.1.2
  · have h := Orb.allN_iff.1 kOrth m hm
    simp only [Bool.or_eq_true, bq, Bool.not_eq_true'] at h
    simp only [Bool.or_eq_true, beq_iff_eq]
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [anyLt_iff]
      by_contra hn
      push Not at hn
      have : allN 121 (fun j => !(allN 7 fun l => Nat.beq (dot3K m (CK (7 * j + l))) 0)) = true := by
        rw [Orb.allN_iff]
        intro j hj
        have hj' := hn j hj
        rw [Bool.not_eq_true', Bool.eq_false_iff]
        intro hall
        apply hj'
        rw [allLt_iff]
        intro l hl
        rw [C_get hj hl]
        have := Orb.allN_iff.1 hall l hl
        rw [bq] at this
        simpa [dot3, dot3K, digit3, dig3] using this
      rw [this] at h
      exact absurd h (by decide)

theorem line_get {j : Nat} (hj : j < 12) :
    (Array.ofFn (n := 12) fun j => lineArr j.val)[j]! = unpack 276 9 (TT.L (12 + j)) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact perm_eq (by omega)

theorem fusCheck_eq : fusCheck () = true := by
  unfold fusCheck
  dsimp only
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff, qSize, true_and]
  intro k hk
  have pT := pQT hk
  rw [qPts_get hk, powEq_id hw pT, eqA_id hw pT]
  have h := Orb.allN_iff.1 kFus k (by omega)
  unfold fusK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  simp only [Bool.or_eq_true]
  rcases h with ((h | h) | ⟨⟨-, ha⟩, hd⟩) | ⟨⟨⟨-, ha⟩, hb⟩, hx⟩
  · exact Or.inl (Or.inl (Or.inl (by rw [h]; rfl)))
  · exact Or.inl (Or.inl (Or.inr h))
  · refine Or.inl (Or.inr ?_)
    unfold inD
    rw [anyLt_iff]
    refine ⟨_, ha, ?_⟩
    rw [E_get ha, eqU pT (pDE ha)]
    exact hd
  · refine Or.inr ?_
    rw [anyLt_iff]
    refine ⟨_, ha, ?_⟩
    rw [qPts_get ha, conj_unpack' hw (pQT ha) pT, anyLt_iff]
    have pc := pcj (pQT ha) pT
    by_cases hb12 : FB k < 12
    · rw [if_pos hb12] at hx
      refine ⟨FB k, hb12, ?_⟩
      rw [Bool.or_eq_true]
      left
      rw [line_get hb12]
      have e := eqU pc (pP (k := 12 + FB k) (by omega))
      unfold cj cm at e hx
      rw [e]
      exact hx
    · rw [if_neg hb12] at hx
      refine ⟨FB k - 12, by omega, ?_⟩
      have pl := pP (k := 12 + (FB k - 12)) (by omega)
      rw [Bool.or_eq_true]
      right
      rw [getElem!_pos (Array.map _ _) (FB k - 12) (by simp; omega), Array.getElem_map,
        ← getElem!_pos (Array.ofFn _) (FB k - 12) (by simp; omega), line_get (by omega), cu pl pl]
      have e := eqU pc (pcm pl pl)
      unfold cj cm at e hx
      unfold cm
      rw [e]
      exact hx

theorem transCheck_eq : transCheck () = true := by
  unfold transCheck
  rw [allLt_iff]
  intro j hj
  have h := Orb.allN_iff.1 kTr j hj
  unfold trK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨ph, px⟩, hs⟩, hz⟩ := h
  unfold transArr lineArr yArr
  dsimp only
  rw [perm_eq (k := 24 + j) (by omega), perm_eq (k := 12 + j) (by omega), perm_eq (k := 9) (by norm_num),
    validA_of ph, validA_of px, inP_of hs, conj_unpack' hw ph px]
  have pc := pcj ph px
  simp only [Bool.true_and]
  split
  · rename_i hd
    rw [if_pos hd] at hz
    simp only [Bool.and_eq_true, Nat.blt_eq] at hz
    unfold inD
    rw [anyLt_iff]
    refine ⟨_, hz.1, ?_⟩
    rw [E_get hz.1]
    have e := eqU pc (pDE hz.1)
    unfold cj cm at e hz
    rw [e]
    exact hz.2
  · rename_i hd
    rw [if_neg hd] at hz
    have p9 := pP (k := 9) (by norm_num)
    rw [cu p9 p9]
    have e1 := eqU pc p9
    have e2 := eqU pc (pcm p9 p9)
    unfold cj cm at e1 e2 hz
    unfold cm
    rw [e1, e2]
    exact hz

theorem orbFacts : ∀ k < rcnt (Co3C.LR 0), RK k < rcnt (Co3C.LR 0) ∧ EK k < EC.N ∧
    pg 9 (mask 9) (EC.T (EK k)) (rpt 9 (mask 9) (Co3C.LR 0) (RK k)) =
      rpt 9 (mask 9) (Co3C.LR 0) k ∧
    ptailBranchK 276 9 Co3C.LR Co3C.TR Co3C.BP (TT.L 9) (pw 276 9 (TT.L 9)) yRels EC.N EC.T 7
      (RK k) = true := by
  rw [Nat.eq_of_beq_eq_true kRc]
  intro k hk
  have h := Orb.allN_iff.1 kOrb k hk
  unfold orbK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq,
    Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h3, Nat.eq_of_beq_eq_true h4, ?_⟩
  rcases h2 with h2 | h2 <;> rw [Nat.eq_of_beq_eq_true h2]
  · exact tpR0
  · exact tpR1

theorem yRels0 : ∀ r ∈ yRels, Nat.max r.1 r.2.1 ≠ 0 := by decide

theorem cCheck_eq : cCheck () = true := by
  have p9 := pP (k := 9) (by norm_num)
  have hy := kY
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hy
  unfold cCheck yArr cCert
  dsimp only
  rw [perm_eq (k := 9) (by norm_num), validA_of p9, inP_of kSiftY, powEq_id hw p9, eqA_id hw p9,
    keys_eq]
  have hc := centOKP_of_orb hw Co3C.binds Co3C.perm Co3C.hl co3ChainArrays (by norm_num)
    co3Order_check.1 p9 kRels yRels0 bindC kComm
    (fun k hk => by
      rw [Nat.eq_of_beq_eq_true eC.1] at hk
      exact inP_of (Orb.allN_iff.1 kSiftC k hk))
    hkeys enumC.1 (enumC.2.1.trans nC) (fun i hi => enumC.2.2 i (by rw [nC]; exact hi))
    (fun i hi => pCT hi) (by norm_num) (by have t := orbFacts; rw [nC] at t; exact t)
    (p := 3) (ps := co3ChainBaseArr.toList) (N := 4536)
  rw [hc]
  simp [hy.1, hy.2]

theorem apN_eq {W c : Nat} (hc : c < 276) : ∀ e, pg 9 (mask 9) (pw 276 9 W e) c = apN W e c
  | 0 => CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hc
  | e + 1 => by
    have e1 : pw 276 9 W (e + 1) = pcomp 276 9 (mask 9) W (pw 276 9 W e) :=
      CFSG.KS.PF.strictN_eqP (ppow 276 9 (mask 9) (pidn 276 9) W e) (fun q => pcomp 276 9 (mask 9) W q)
    rw [e1, CFSG.KS.PF.pg_pcomp (by norm_num) hc, apN_eq hc e]
    rfl

theorem card_filter_cntN (f : Nat → Bool) :
    ∀ N, ((Finset.range N).filter fun j => f j = true).card = cntN N f
  | 0 => rfl
  | N + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert]
    change _ = Nat.add (cntN N f) (cond (f N) 1 0)
    rw [← card_filter_cntN f N]
    cases hf : f N
    · simp
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      rfl

theorem commA_eq {A B : Nat} (hA : permB 276 9 A = true) (hB : permB 276 9 B = true) :
    CFSG.RankThree.Native.commA 276 (unpack 276 9 A) (unpack 276 9 B) = commPt A B := by
  unfold CFSG.RankThree.Native.commA
  rw [cu hA hB, cu hB hA]
  apply Bool.eq_iff_iff.2
  unfold commPt
  rw [Orb.allN_iff]
  unfold eqA
  rw [allLt_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  unfold cm
  rw [getU hi, getU hi, CFSG.KS.PF.pg_pcomp (by norm_num) hi, CFSG.KS.PF.pg_pcomp (by norm_num) hi,
    bq]
  simp

theorem classCheck_eq : classCheck () = true := by
  unfold classCheck
  dsimp only
  rw [cSize, allLt_iff]
  intro i hi
  have pw' := pCT hi
  have e : ∀ lo l, Nat.add lo l = lo + l := fun _ _ => rfl
  have key : ∀ c < 9, classB (504 * c) = true := by
    intro c hc
    interval_cases c
    exacts [kC0, kC1, kC2, kC3, kC4, kC5, kC6, kC7, kC8]
  have h := allBlk_spec (key (i / 504) (by omega)) (i % 504) (Nat.mod_lt _ (by norm_num))
  rw [e, Nat.div_add_mod] at h
  unfold classK at h
  rw [cPts_get hi, eqA_id hw pw', powEq_id hw pw', powEq_id hw pw']
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', bqf] at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  rcases h with (h | ⟨⟨⟨⟨-, h2⟩, h7⟩, n2⟩, n7⟩) | h
  · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inr ?_)
    simp only [Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [Bool.eq_false_iff]
      intro hc
      apply n2
      rw [← apN_eq h2, Nat.eq_of_beq_eq_true hc]
      exact CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) h2
    · rw [Bool.eq_false_iff]
      intro hc
      apply n7
      rw [← apN_eq h7, Nat.eq_of_beq_eq_true hc]
      exact CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) h7
  · refine Or.inr ?_
    unfold commCount
    rw [cSize]
    have hcf : ((Finset.range 4536).filter fun j =>
        CFSG.RankThree.Native.commA 276 (cCert ()).pts[j]! (unpack 276 9 (EC.T i)) = true) =
        (Finset.range 4536).filter fun j => commPt (EC.T j) (EC.T i) = true := by
      apply Finset.filter_congr
      intro j hj
      rw [cPts_get (Finset.mem_range.1 hj), commA_eq (pCT (Finset.mem_range.1 hj)) pw']
    rw [hcf, card_filter_cntN, ← nC]
    exact h

theorem facts : qCheck () = true ∧ dCheck () = true ∧ hypCheck () = true ∧ fusCheck () = true ∧
    transCheck () = true ∧ cCheck () = true ∧ classCheck () = true :=
  ⟨qCheck_eq, dCheck_eq, hypCheck_eq, fusCheck_eq, transCheck_eq, cCheck_eq, classCheck_eq⟩

end CertificateChecks.KernelCo3T

end

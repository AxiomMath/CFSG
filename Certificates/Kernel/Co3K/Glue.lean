module

public import Certificates.Kernel.Co3K.Checks
public import Certificates.Kernel.Sporadic.Co3.FirstFacts
public import CFSG.Certificates.Kernel.Co3KSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Co3K CFSG.KC.Misc.ArrEnum
open CFSG.KC.BfsPin CFSG.KC.PermTool CertificateChecks.KernelSpor
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co3K
open CertificateChecks.KernelSpor.Co3Single (z_eq)

private theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

private theorem notT {a : Bool} (ha : a = false) : (!a) = true := by
  rw [ha]
  rfl

private theorem beqF {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · rw [e] at h
    exact absurd h Bool.false_ne_true

theorem arr_eq (L : Nat) (hL : L < 28) : co3KArr L = unpack 276 9 (KT.L L) := by
  unfold co3KArr co3KBytes
  rw [KT.eq]
  have := CFSG.KS.Text.hexBind_sound KT.all L hL
  rwa [Nat.zero_add] at this

theorem pL (L : Nat) (hL : L < 28) : permB 276 9 (KT.L L) = true :=
  ((bAnd_iff _ _).1 (allN_spec perms L hL)).1

theorem cL (L : Nat) (hL : L < 28) : Cn (KT.L L) := ((bAnd_iff _ _).1 (allN_spec perms L hL)).2

theorem hiL (L : Nat) (hL : L < 5) : Nat.shiftRight (KT.L L) (276 * 9) = 0 :=
  Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (allN_spec hiR L hL)).1

theorem rL (L : Nat) (hL : L < 5) : allN 276 (fun i => Nat.blt (pg 9 (mask 9) (KT.L L) i) 276) =
    true := ((bAnd_iff _ _).1 (allN_spec hiR L hL)).2

theorem c1 : (allLt 28 fun L => isInvA 276 (co3KArr L) (invCand 276 (co3KArr L))) = true := by
  rw [allLt_iff]
  intro L hL
  rw [arr_eq L hL]
  obtain ⟨h1, h2⟩ := invEqK_sound (p := KT.L L) (r := pinvS 276 9 (mask 9) (KT.L L)) (pL L hL)
  rw [h1]
  exact h2

theorem hE : co3KE = unpack 276 9 (KT.L 0) := arr_eq 0 (by norm_num)
theorem hT1 : co3KT1 = unpack 276 9 (KT.L 1) := arr_eq 1 (by norm_num)
theorem hG1 : co3KG1 = unpack 276 9 (KT.L 2) := arr_eq 2 (by norm_num)
theorem hX5 : co3KX5 = unpack 276 9 (KT.L 3) := arr_eq 3 (by norm_num)
theorem hX7 : co3KX7 = unpack 276 9 (KT.L 4) := arr_eq 4 (by norm_num)

theorem cE : Cn (KT.L 0) := cL 0 (by norm_num)
theorem cT1 : Cn (KT.L 1) := cL 1 (by norm_num)
theorem cG1 : Cn (KT.L 2) := cL 2 (by norm_num)
theorem cX5 : Cn (KT.L 3) := cL 3 (by norm_num)
theorem cX7 : Cn (KT.L 4) := cL 4 (by norm_num)

theorem hId : idA 276 = unpack 276 9 idk := idU kId

theorem siftE : siftA 276 co3TLevels co3TBaseArr 0 co3KE = true :=
  siftK_soundR Co3T.binds Co3T.perm Co3T.hl hE (hiL 0 (by norm_num)) (rL 0 (by norm_num)) sE

theorem siftT1 : siftA 276 co3TLevels co3TBaseArr 0 co3KT1 = true :=
  siftK_soundR Co3T.binds Co3T.perm Co3T.hl hT1 (hiL 1 (by norm_num)) (rL 1 (by norm_num)) sT1

theorem siftG1 : siftA 276 co3ChainLevels co3ChainBaseArr 0 co3KG1 = true :=
  siftK_soundR Co3C.binds Co3C.perm Co3C.hl hG1 (hiL 2 (by norm_num)) (rL 2 (by norm_num)) sG1

theorem siftX5 : siftA 276 co3MLevels co3MBaseArr 0 co3KX5 = true :=
  siftK_soundR Co3M.binds Co3M.perm Co3M.hl hX5 (hiL 3 (by norm_num)) (rL 3 (by norm_num)) sX5

theorem siftX7 : siftA 276 co3MLevels co3MBaseArr 0 co3KX7 = true :=
  siftK_soundR Co3M.binds Co3M.perm Co3M.hl hX7 (hiL 4 (by norm_num)) (rL 4 (by norm_num)) sX7

theorem eSqA : eqA 276 (compA 276 co3KE co3KE) (idA 276) = true := by
  rw [hE, hId, compU cE cE, eqU (cnPk cE cE) cId]
  exact eSq

theorem eNeA : eqA 276 co3KE (idA 276) = false := by
  rw [hE, hId, eqU cE cId]
  exact beqF eNe

theorem eNzA : eqA 276 co3KE co3ZArr = false := by
  rw [hE, z_eq, eqU cE cZ]
  exact beqF eNz

theorem t1EA : eqA 276 (compA 276 co3KT1 co3KE) (compA 276 (compA 276 co3KE co3ZArr) co3KT1) =
    true := by
  rw [hT1, hE, z_eq, compU cT1 cE, compU cE cZ, compU (cnPk cE cZ) cT1,
    eqU (cnPk cT1 cE) (cnPk (cnPk cE cZ) cT1)]
  exact t1E

theorem g1EA : eqA 276 (compA 276 co3KG1 co3KE) (compA 276 co3ZArr co3KG1) = true := by
  rw [hG1, hE, z_eq, compU cG1 cE, compU cZ cG1, eqU (cnPk cG1 cE) (cnPk cZ cG1)]
  exact g1E

theorem cPow {X : Nat} (hX : Cn X) : ∀ k, Cn (powK X k)
  | 0 => cId
  | k + 1 => cnPk hX (cPow hX k)

theorem pow_eq {X : Nat} (hX : Cn X) : ∀ k, co3KPow (unpack 276 9 X) k = unpack 276 9 (powK X k)
  | 0 => by rw [co3KPow, hId]; rfl
  | k + 1 => by
    rw [co3KPow, pow_eq hX k, compU hX (cPow hX k)]
    rfl

theorem x5PA : eqA 276 (co3KPow co3KX5 5) (idA 276) = true := by
  rw [hX5, pow_eq cX5, hId, eqU (cPow cX5 5) cId]
  exact x5P

theorem x7PA : eqA 276 (co3KPow co3KX7 7) (idA 276) = true := by
  rw [hX7, pow_eq cX7, hId, eqU (cPow cX7 7) cId]
  exact x7P

theorem x5NeA : eqA 276 co3KX5 (idA 276) = false := by
  rw [hX5, hId, eqU cX5 cId]
  exact beqF x5Ne

theorem x7NeA : eqA 276 co3KX7 (idA 276) = false := by
  rw [hX7, hId, eqU cX7 cId]
  exact beqF x7Ne

@[expose] noncomputable def kap (X : Nat) : Nat :=
  pcomp 36 6 (mask 6) (pcomp 36 6 (mask 6) Co3First.Csp (restrictK 9 6 co3IzNat X))
    (pinvS 36 6 (mask 6) Co3First.Csp)

theorem kapC : allN 2 (fun j => canonK 36 6 (mask 6) (36 * 6)
    (restrictK 9 6 co3IzNat (KT.L (Nat.add 3 j)))) = true := by quickRfl

theorem fx5 : fix1K (kap (KT.L 3)) = true := by quickRfl
theorem fx7 : fix1K (kap (KT.L 4)) = true := by quickRfl

theorem kappa_eq {X : Nat} (cS : Cn X) (cR : canonK 36 6 (mask 6) (36 * 6) (restrictK 9 6 co3IzNat X) =
    true) : co3KKappa (unpack 276 9 X) = unpack 36 6 (kap X) := by
  obtain ⟨cC, cCI, pC⟩ := (by simpa only [bAnd_iff] using Co3First.cspOK :
    canonK 36 6 (mask 6) (36 * 6) Co3First.Csp = true ∧
      canonK 36 6 (mask 6) (36 * 6) (pinvS 36 6 (mask 6) Co3First.Csp) = true ∧
      permOK 36 6 (mask 6) (36 * 6) Co3First.Csp (pinvS 36 6 (mask 6) Co3First.Csp) = true)
  unfold co3KKappa
  rw [Co3First.csp_eq]
  have hL : ∀ x ∈ co3IzNat, x < 276 := by decide
  have hlen : co3IzNat.length = 36 := rfl
  have e := restrictArr_unpack (w' := 6) cS hL (by rw [hlen]; norm_num)
  rw [hlen] at e
  rw [co3IzArr, Co3First.restrictA_toArray, e]
  unfold renameA
  rw [compA_unpack cC cR, invCand_unpack pC, compA_unpack (canonK_pcomp cC cR) cCI]
  rfl

theorem fix5 : co3KFix1 (co3KKappa co3KX5) = true := by
  rw [hX5, kappa_eq cX5 (allN_spec kapC 0 (by norm_num))]
  exact fix1K_of fx5

theorem fix7 : co3KFix1 (co3KKappa co3KX7) = true := by
  rw [hX7, kappa_eq cX7 (allN_spec kapC 1 (by norm_num))]
  exact fix1K_of fx7

theorem hc : ∀ i < 3, ∀ k < rcnt (Co3T.LR i), Cn (Co3T.TR (roff 276 (276 * 9) (Co3T.LR i) + k)) :=
  fun i hi k hk => allN_spec (allN_spec trs i hi) k hk

theorem slices {f : Nat → Bool} (h : ∀ q < 8, allN 16 (fun a => f (Nat.add (16 * q) a)) = true) :
    ∀ a < rcnt (Co3T.LR 0), f a = true := by
  intro a ha
  rw [Nat.eq_of_beq_eq_true cnt0] at ha
  have e : 16 * (a / 16) + a % 16 = a := by omega
  have := allN_spec (h (a / 16) (by omega)) (a % 16) (by omega)
  rw [← e]
  exact this

theorem eAll : ∀ q < 8, eS (16 * q) = true := by
  intro q hq
  interval_cases q
  · exact eS0
  · exact eS1
  · exact eS2
  · exact eS3
  · exact eS4
  · exact eS5
  · exact eS6
  · exact eS7

theorem kAll : ∀ q < 8, kS (16 * q) = true := by
  intro q hq
  interval_cases q
  · exact kS0
  · exact kS1
  · exact kS2
  · exact kS3
  · exact kS4
  · exact kS5
  · exact kS6
  · exact kS7

theorem eCheck : co3KECheck co3TLevels co3KE co3ZArr = true := by
  rw [hE, z_eq]
  unfold co3KECheck co3TLevels
  refine prod3_of Co3T.binds Co3T.perm Co3T.hl hc (P := eK (KT.L 0) (pk (KT.L 0) Co3Z))
    (fun G hG hP => eK_of cE cZ hG hP) (slices fun q hq => ?_)
  have := eAll q hq
  unfold eS at this
  rwa [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq] at this

theorem gens_eq (k : Nat) (hk : k < 8) : co3KGens[k]! = unpack 276 9 (Co3T.S k) := by
  have hS : co3TArrs.size = 10 := Co3T.binds.2.2.2.1
  unfold co3KGens
  rw [getElem!_pos _ k (by simp [hS]; omega), Array.getElem_extract, ← getElem!_pos co3TArrs (0 + k)
    (by omega), Nat.zero_add, Co3T.arr_eq k (by omega)]

theorem gens_size : co3KGens.size = 8 := by
  have hS : co3TArrs.size = 10 := Co3T.binds.2.2.2.1
  unfold co3KGens
  simp [hS]

theorem cS (k : Nat) (hk : k < 8) : Cn (Co3T.S k) := ((bAnd_iff _ _).1 (allN_spec gens k hk)).1
theorem cSI (k : Nat) (hk : k < 8) : Cn (Co3T.SI k) := ((bAnd_iff _ _).1 (allN_spec gens k hk)).2

theorem inv_eq (k : Nat) (hk : k < 8) : co3KGensInv[k]! = unpack 276 9 (Co3T.SI k) := by
  unfold co3KGensInv
  rw [getElem!_pos _ k (by simp [gens_size]; exact hk), Array.getElem_map, ← getElem!_pos co3KGens k
    (by rw [gens_size]; exact hk), gens_eq k hk]
  exact (invEqK_sound (allN_spec Co3T.perm k (by omega))).1

theorem d_size : co3KD.size = 23 := Array.size_ofFn

theorem d_eq (i : Nat) (hi : i < 23) : co3KD[i]! = unpack 276 9 (KT.L (Nat.add 5 i)) := by
  unfold co3KD
  rw [getElem!_pos _ i (by simp; omega), Array.getElem_ofFn]
  exact arr_eq (5 + i) (by omega)

theorem cD (i : Nat) (hi : i < 23) : Cn (KT.L (Nat.add 5 i)) := cL (5 + i) (by omega)

theorem k3Check : co3KK3Check co3TLevels co3KGens co3KGensInv co3KD = true := by
  unfold co3KK3Check co3TLevels
  refine prod3_of Co3T.binds Co3T.perm Co3T.hl hc
    (P := k3K Co3T.S Co3T.SI (fun i => KT.L (Nat.add 5 i)))
    (fun G hG hP => k3K_of cS cSI cD hId cId hG gens_size gens_eq inv_eq d_size d_eq hP)
    (slices fun q hq => ?_)
  have := kAll q hq
  unfold kS at this
  exact this

theorem wt_spec (k : Nat) (hk : k < 72) : lane WT k = wK Co3T.S Co3T.SI k ∧ Cn (lane WT k) := by
  have h := wt
  rw [Raw.Orb.strictB_eq] at h
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h k hk)
  exact ⟨Nat.eq_of_beq_eq_true a, b⟩

theorem w_size : co3KW.size = 72 := Array.size_ofFn

theorem w_eq (k : Nat) (hk : k < 72) : co3KW[k]! = unpack 276 9 (lane WT k) := by
  rw [(wt_spec k hk).1]
  unfold co3KW
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_ofFn]
  beta_reduce
  unfold wK
  rw [Raw.Orb.nIf_eq]
  by_cases h64 : k < 64
  · have hb : Nat.blt k 64 = true := Nat.blt_eq.mpr h64
    rw [if_pos h64, if_pos hb]
    have e7 : Nat.land k 7 = k % 8 := Nat.and_two_pow_sub_one_eq_mod k 3
    have e3 : Nat.shiftRight k 3 = k / 8 := Nat.shiftRight_eq_div_pow k 3
    rw [e7, e3]
    have hi : k / 8 < 8 := by omega
    have hj : k % 8 < 8 := by omega
    unfold commA
    rw [gens_eq _ hj, gens_eq _ hi,
      (invEqK_sound (allN_spec Co3T.perm (k % 8) (by omega))).1,
      (invEqK_sound (allN_spec Co3T.perm (k / 8) (by omega))).1,
      compU (cS _ hj) (cS _ hi), compU (cnPk (cS _ hj) (cS _ hi)) (cSI _ hj),
      compU (cnPk (cnPk (cS _ hj) (cS _ hi)) (cSI _ hj)) (cSI _ hi)]
  · have hb : Nat.blt k 64 = false := by
      cases e : Nat.blt k 64
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h64
    rw [if_neg h64, hb]
    have hk' : k - 64 < 8 := by omega
    rw [if_neg Bool.false_ne_true, gens_eq _ hk', pow_eq (cS _ hk')]
    rfl

theorem k5Check : co3KK5Check co3KD co3KW co3ZArr = true := by
  unfold co3KK5Check
  rw [allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro j hj
  rw [d_size] at hi hj
  have hrow : k5RowK (fun i => KT.L (Nat.add 5 i)) WT Co3Z i = true := by
    by_cases h12 : i < 12
    · have h := k5a
      unfold k5 at h
      rw [Raw.Orb.strictB_eq] at h
      have := allN_spec h i h12
      have e : Nat.add 0 i = i := Nat.zero_add i
      rwa [e] at this
    · have h := k5b
      unfold k5 at h
      rw [Raw.Orb.strictB_eq] at h
      have hlt : i - 12 < 11 := by omega
      have := allN_spec h (i - 12) hlt
      have e : Nat.add 12 (i - 12) = i := by
        change 12 + (i - 12) = i
        omega
      rwa [e] at this
  have hp := k5RowK_spec hrow j hj
  rw [d_eq i hi, d_eq j hj, z_eq]
  exact pairK_of (cD i hi) (cD j hj) cZ (fun k hk => (wt_spec k hk).2) w_size w_eq hp

theorem check : co3KCheck = true := by
  unfold co3KCheck
  have h5 := andT (andT (andT (andT c1 siftE) eSqA) (notT eNeA)) (notT eNzA)
  have h10 := andT (andT (andT (andT (andT h5 eCheck) siftT1) t1EA) siftG1) g1EA
  have h15 := andT (andT (andT (andT (andT h10 siftX5) x5PA) (notT x5NeA)) fix5) siftX7
  exact andT (andT (andT (andT (andT h15 x7PA) (notT x7NeA)) fix7) k3Check) k5Check

end CertificateChecks.KernelCo3K

end

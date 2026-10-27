
module

public import Certificates.Kernel.Co1B.TriG2045
public import Certificates.Kernel.Co1B.OrbK2045
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Tri2045

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
  CFSG.KC.Co1T CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSporSch.Co1Packed
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem vlt {m : Nat} (h : Nat.blt (TB.V m) 16777216 = true) : TB.V m < 2 ^ 24 := by
  have := lt_of_blt h
  norm_num
  exact this

theorem eqA_refl (n : Nat) (t : Array Nat) : eqA n t t = true := by
  rw [eqA, allLt_iff]
  intro i _
  simp

theorem four_le {G : Type*} [Group G] [Finite G] {K : Subgroup G} {a z : G} (ha : a ∈ K)
    (hz : z ∈ K) (h1 : a ≠ 1) (h2 : z ≠ 1) (h3 : z ≠ a) (h4 : a * z ≠ 1) : 4 ≤ Nat.card K := by
  let f : Fin 4 → K := ![1, ⟨a, ha⟩, ⟨z, hz⟩, ⟨a * z, K.mul_mem ha hz⟩]
  have h1' : (1 : G) ≠ a := Ne.symm h1
  have h2' : (1 : G) ≠ z := Ne.symm h2
  have h3' : a ≠ z := Ne.symm h3
  have h4' : (1 : G) ≠ a * z := Ne.symm h4
  have hf : Function.Injective f := by
    intro i j hij
    have e := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Subtype.ext_iff]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

section Card

theorem zrep : MRep (unpack 24 24 (mpowK (Cent2045.D2.M 2) 14)) ((zE : twoBE) : GL24) := by
  have := rep_mpow (bG_rep (j := 2) (by norm_num)) 14
  simpa using this

theorem hA1 : A₁ ≠ 1 := act_ne repA kTA' (vlt (m := 0) (by quickRfl)) (ne1K_sound kV0)

theorem hZ1 : ((zE : twoBE) : GL24) ≠ 1 :=
  act_ne zrep kTZ' (vlt (m := 1) (by quickRfl)) (ne1K_sound kV1)

theorem hZA : ((zE : twoBE) : GL24) ≠ A₁ := act_ne2 zrep repA kTZ' kTA' (neK2_sound kV2)

theorem hAZ : A₁ * ((zE : twoBE) : GL24) ≠ 1 :=
  act_ne12 repA zrep kTA' kTZ' (vlt (m := 3) (by quickRfl)) (ne1K2_sound kV3)

theorem card_ker_ge : 4 ≤ Nat.card φE.ker := by
  have ha : aE ∈ φE.ker := MonoidHom.mem_ker.2 φE_a
  have hz : zE ∈ φE.ker := MonoidHom.mem_ker.2 φE_z
  have hmA : A₁ ∈ φE.ker.map twoBE.subtype := ⟨aE, ha, by rw [Subgroup.coe_subtype]⟩
  have hmZ : ((zE : twoBE) : GL24) ∈ φE.ker.map twoBE.subtype :=
    ⟨zE, hz, by rw [Subgroup.coe_subtype]⟩
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective twoBE)]
  exact four_le hmA hmZ hA1 hZ1 hZA hAZ

abbrev xE : twoBE := ⟨dG 19, dG_mem 19⟩

abbrev yE : twoBE := ⟨dG 21, dG_mem 21⟩

theorem rep_xE : Rep 1365 (unpack 1365 11 (TB.P 10)) (φE xE) :=
  rep_φE (m := 10) (by norm_num) (dG_rep (j := 19) (by norm_num))

theorem rep_yE : Rep 1365 (unpack 1365 11 (TB.P 11)) (φE yE) :=
  rep_φE (m := 11) (by norm_num) (dG_rep (j := 21) (by norm_num))

theorem rep_bE {j : Nat} (hj : j < 10) : Rep 1365 (unpack 1365 11 (TB.P j)) (φE (bE j)) :=
  rep_φE (by omega) (by rw [matIdx_lt hj]; exact bG_rep hj)

abbrev DD : Subgroup (Equiv.Perm (Fin 1365)) := Subgroup.closure {φE xE, φE yE}

theorem sign_rep {P T k : Nat} {g : Equiv.Perm (Fin 1365)} (hg : Rep 1365 (unpack 1365 11 P) g)
    (h : CFSG.KC.Pack.signK 1365 11 (mask 11) P T k = true) : Equiv.Perm.sign g = (-1) ^ k :=
  CFSG.KC.Pack.sign_of_signK h (fun i => by rw [← hg i, unpack_get' i.2])

theorem sign_x : Equiv.Perm.sign (φE xE) = 1 := by
  rw [sign_rep rep_xE kSX]
  exact Even.neg_one_pow (Nat.even_iff.2 (beq_of_true kKX))

theorem sign_y : Equiv.Perm.sign (φE yE) = 1 := by
  rw [sign_rep rep_yE kSY]
  exact Even.neg_one_pow (Nat.even_iff.2 (beq_of_true kKY))

theorem sign_b5 : Equiv.Perm.sign (φE (bE 5)) = -1 := by
  rw [sign_rep (rep_bE (by norm_num)) kS5]
  exact Odd.neg_one_pow (Nat.odd_iff.2 (beq_of_true kK5))

theorem DD_le_alt : DD ≤ alternatingGroup (Fin 1365) := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact Equiv.Perm.mem_alternatingGroup.2 sign_x
  · exact Equiv.Perm.mem_alternatingGroup.2 sign_y

theorem DD_le_range : DD ≤ φE.range := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem b5_not_mem : φE (bE 5) ∉ DD := fun h => by
  have := Equiv.Perm.mem_alternatingGroup.1 (DD_le_alt h)
  rw [sign_b5] at this
  exact absurd this (by decide)

theorem card_DD_dvd : ∃ q, Nat.card φE.range = Nat.card DD * q ∧ 2 ≤ q := by
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le DD_le_range
  refine ⟨q, hq, ?_⟩
  have hpos : 0 < Nat.card φE.range := Nat.card_pos
  rcases q with _ | _ | q
  · rw [Nat.mul_zero] at hq
    omega
  · rw [Nat.mul_one] at hq
    have hb5 : φE (bE 5) ∈ φE.range := ⟨_, rfl⟩
    rw [← Subgroup.eq_of_le_of_card_ge DD_le_range hq.le] at hb5
    exact absurd hb5 b5_not_mem
  · omega

end Card

theorem rx_eq : twoBXYRows.1 = unpack 24 24 (Cent2045.D2.M 19) := by
  have e : twoBXYRows.1 = (CFSG.Sporadic.Co1Schreier.Native.dag
      (CFSG.Sporadic.Co1Block.Native.brayElts
        (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1)
        twoBBray) twoBD2).1.getD 19 CFSG.Sporadic.Co1Schreier.Native.one := rfl
  rw [e, dag2_rows, rows_getD (by norm_num)]

theorem ry_eq : twoBXYRows.2 = unpack 24 24 (Cent2045.D2.M 21) := by
  have e : twoBXYRows.2 = (CFSG.Sporadic.Co1Schreier.Native.dag
      (CFSG.Sporadic.Co1Block.Native.brayElts
        (CFSG.Sporadic.Co1Block.Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1)
        twoBBray) twoBD2).1.getD 21 CFSG.Sporadic.Co1Schreier.Native.one := rfl
  rw [e, dag2_rows, rows_getD (by norm_num)]

theorem okX : CFSG.Sporadic.Co1Block.Native.triOK (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris twoBXYRows.1 = true ∧
    CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris twoBXYRows.1 = unpack 1365 11 (TB.P 10) := by
  rw [rx_eq]
  exact triOK_of (hTr (m := 10) (by norm_num)) (kW (by norm_num))

theorem okY : CFSG.Sporadic.Co1Block.Native.triOK (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris twoBXYRows.2 = true ∧
    CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris twoBXYRows.2 = unpack 1365 11 (TB.P 11) := by
  rw [ry_eq]
  exact triOK_of (hTr (m := 11) (by norm_num)) (kW (by norm_num))

theorem okB {j : Nat} (hj : j < 10) :
    CFSG.Sporadic.Co1Block.Native.triOK (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris (unpack 24 24 (Cent2045.D2.M j)) = true ∧
    CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
      twoBTris (unpack 24 24 (Cent2045.D2.M j)) = unpack 1365 11 (TB.P j) := by
  have := triOK_of (hTr (m := j) (by omega)) (kW (m := j) (by omega))
  rwa [matIdx_lt hj] at this

theorem getElem!_push_lt {A : Array (Array Nat)} {x : Array Nat} {j : Nat} (hj : j < A.size) :
    (A.push x)[j]! = A[j]! := by
  rw [getElem!_pos (A.push x) j (by simp; omega), getElem!_pos A j hj, Array.getElem_push_lt]

theorem getElem!_push_eq {A : Array (Array Nat)} {x : Array Nat} : (A.push x)[A.size]! = x := by
  rw [getElem!_pos (A.push x) A.size (by simp), Array.getElem_push_eq]

theorem ext_all {n w : Nat} {PS PSI : Nat → Nat} : ∀ (ds : List (List Int))
    (A : Array (Array Nat)) (kS : Nat), A.size = kS → (∀ j < kS, A[j]! = unpack n w (PS j)) →
    (∀ i < ds.length, allN (kS + i) (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true ∧
      CFSG.KS.Prim.wordEqK n w (mask w) (pidn n w) PS PSI (kS + i) (ds.getD i []) (PS (kS + i)) =
        true) →
    (CFSG.Sporadic.Co2Schreier.extendArrsN n A ds).size = kS + ds.length ∧
      ∀ j < kS + ds.length, (CFSG.Sporadic.Co2Schreier.extendArrsN n A ds)[j]! = unpack n w (PS j)
  | [], A, kS, hs, hA, _ => ⟨by simp [CFSG.Sporadic.Co2Schreier.extendArrsN, hs],
      fun j hj => by
        simp only [CFSG.Sporadic.Co2Schreier.extendArrsN, List.foldl_nil]
        exact hA j (by simpa using hj)⟩
  | d :: ds, A, kS, hs, hA, hw => by
    obtain ⟨hp, hwd⟩ := hw 0 (by simp)
    have hv := (CFSG.KS.Prim.wordEqK_sound ⟨hs, hA⟩ (by simpa using hp) (by simpa using hwd)).1
    have e : CFSG.Sporadic.Co2Schreier.extendArrsN n A (d :: ds) =
        CFSG.Sporadic.Co2Schreier.extendArrsN n
          (A.push (CFSG.Sporadic.Co2Schreier.wordArrN n A d)) ds := rfl
    have hA' : ∀ j < kS + 1, (A.push (CFSG.Sporadic.Co2Schreier.wordArrN n A d))[j]! =
        unpack n w (PS j) := by
      intro j hj
      rcases Nat.lt_or_ge j kS with h | h
      · rw [getElem!_push_lt (by omega)]
        exact hA j h
      · obtain rfl : j = kS := by omega
        rw [← hs, getElem!_push_eq, hs]
        exact hv
    have ih := ext_all ds (A.push (CFSG.Sporadic.Co2Schreier.wordArrN n A d)) (kS + 1)
      (by simp [hs]) hA' (fun i hi => by
        have := hw (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    rw [e]
    refine ⟨by rw [ih.1]; simp; omega, fun j hj => ih.2 j (by simp at hj ⊢; omega)⟩

theorem strong_eq : twoBStrong = CFSG.Sporadic.Co2Schreier.extendArrsN 1365
    #[unpack 1365 11 (RO.S 0), unpack 1365 11 (RO.S 1)] twoBChainWords := by
  have e : twoBStrong = CFSG.Sporadic.Co1Block.Native.extendTri
      (CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
        twoBTris twoBXYRows.1)
      (CFSG.Sporadic.Co1Block.Native.triPerm (CFSG.Sporadic.Co1Block.Native.triTable twoBTris)
        twoBTris twoBXYRows.2) twoBChainWords := rfl
  rw [e, okX.2, okY.2, beq_of_true kS0, beq_of_true kS1]
  rfl

theorem strong_facts : twoBStrong.size = 6 ∧ ∀ j < 6, twoBStrong[j]! = unpack 1365 11 (RO.S j) := by
  rw [strong_eq]
  have := ext_all (n := 1365) (w := 11) (PS := RO.S) (PSI := RO.SI) twoBChainWords
    #[unpack 1365 11 (RO.S 0), unpack 1365 11 (RO.S 1)] 2 rfl
    (fun j hj => by interval_cases j <;> simp)
    (fun i hi => by
      have := WK.all i (by simpa [twoBChainWords] using hi)
      exact ⟨(CFSG.KC.Pack.band_iff.1 this).1, (CFSG.KC.Pack.band_iff.1 this).2⟩)
  simpa [twoBChainWords] using this

theorem binds : Binds 1365 11 RO.S 6 3 RO.BP twoBStrong twoBChainBase.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, strong_facts.1, strong_facts.2,
    by simp [twoBChainBase], fun t ht => ?_⟩
  interval_cases t
  · rw [beq_of_true kB0]
    rfl
  · rw [beq_of_true kB1]
    rfl
  · rw [beq_of_true kB2]
    rfl

theorem strong_perm {j : Nat} (hj : j < 6) :
    invCand 1365 (unpack 1365 11 (RO.S j)) = unpack 1365 11 (RO.SI j) ∧
      isInvA 1365 (unpack 1365 11 (RO.S j)) (unpack 1365 11 (RO.SI j)) = true :=
  CFSG.KS.Prim.invEqK_sound (CFSG.KC.Pack.allN_spec kP6 j hj)

theorem allPerms : CFSG.Sporadic.Schreier.Tits.allPermsOK 1365 twoBStrong = true := by
  rw [CFSG.Sporadic.Schreier.Tits.allPermsOK, allLt_iff, strong_facts.1]
  intro j hj
  rw [strong_facts.2 j hj, (strong_perm hj).1]
  exact (strong_perm hj).2

theorem orbits : rawOrbitSizes 1365 twoBStrong twoBChainBase.toArray = [1365, 1024, 180] := by
  rw [rawOrbitSizesK_orb binds kP6 RO.ho (by norm_num)]
  rw [show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil, beq_of_true kR0, beq_of_true kR1, beq_of_true kR2]

theorem base_eq' : CFSG.Sporadic.Schreier.Tits.baseArr 1365 twoBChainBase =
    twoBChainBase.toArray := by decide

theorem hn1 : 1 ≤ 1365 := by norm_num

theorem hk2 : 2 ≤ twoBStrong.size := by
  rw [strong_facts.1]
  norm_num

theorem hnd : (CFSG.Sporadic.Schreier.Tits.finList 1365 twoBChainBase).Nodup := by decide

section Chain

theorem strong_rep {j : Nat} (hj : j < 6) :
    Rep 1365 twoBStrong[j]! (permOfArr 1365 twoBStrong[j]!) :=
  CFSG.Sporadic.Schreier.Tits.rep_of_allPermsOK allPerms (by rw [strong_facts.1]; exact hj)

theorem perm0 : permOfArr 1365 twoBStrong[0]! = φE xE := by
  have h' := rep_xE
  rw [← beq_of_true kS0, ← strong_facts.2 0 (by norm_num)] at h'
  exact (strong_rep (j := 0) (by norm_num)).unique h'

theorem perm1 : permOfArr 1365 twoBStrong[1]! = φE yE := by
  have h' := rep_yE
  rw [← beq_of_true kS1, ← strong_facts.2 1 (by norm_num)] at h'
  exact (strong_rep (j := 1) (by norm_num)).unique h'

theorem range_eq : Set.range (fun j : Fin 2 => permOfArr 1365 twoBStrong[(j : ℕ)]!) =
    {φE xE, φE yE} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    match i with
    | ⟨0, _⟩ => exact Or.inl perm0
    | ⟨1, _⟩ => exact Or.inr perm1
  · rintro (rfl | rfl)
    · exact ⟨0, perm0⟩
    · exact ⟨1, perm1⟩

theorem orig_eq : (CFSG.Certificates.RawSchreierDatum.ofArrays 1365 hn1 twoBStrong 2 hk2
    (CFSG.Sporadic.Schreier.Tits.finList 1365 twoBChainBase) hnd
    (CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords)).originalSubgroup = DD := by
  rw [CFSG.Sporadic.Schreier.Tits.originalSubgroup_ofArrays, range_eq]

end Chain

theorem isPrime_of {P p : Nat} {g : Equiv.Perm (Fin 1365)} (hg : Rep 1365 (unpack 1365 11 P) g)
    (hpow : CFSG.KS.Prim.powEqK 1365 11 (mask 11) (1365 * 11) (pidn 1365 11) P p (pidn 1365 11) =
      true)
    (hne : CFSG.KS.Prim.neK 1365 11 (mask 11) (1365 * 11) P (pidn 1365 11) = true) :
    CFSG.Sporadic.Co1Block.Native.isPrimeOrderA 1365 (unpack 1365 11 P) p = true := by
  have rp : ∀ k, Rep 1365 (CFSG.Sporadic.Co1Block.Native.powTri 1365 (unpack 1365 11 P) k)
      (g ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [CFSG.Sporadic.Co1Block.Native.powTri, pow_zero]
      exact rep_idA
    | succ k ih =>
      simp only [CFSG.Sporadic.Co1Block.Native.powTri, pow_succ]
      exact rep_compA ih hg
  have h1 : g ^ p = 1 := pow_eq_one_of hg hpow
  have h2 := CFSG.KS.Prim.neK_sound hne
  rw [idA_eq] at h2
  unfold CFSG.Sporadic.Co1Block.Native.isPrimeOrderA
  rw [(eqA_iff (rp p) rep_idA).2 h1, h2]
  rfl

end CertificateChecks.KernelCo1B.Tri2045

end

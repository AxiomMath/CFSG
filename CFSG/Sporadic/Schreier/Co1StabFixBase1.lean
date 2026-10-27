
module

public import CFSG.Sporadic.Schreier.Co1StabFixBase

public import CFSG.Sporadic.Schreier.Co1StabCheck
public import CFSG.Sporadic.Schreier.Co1FullOrbitsBase
public import CFSG.Sporadic.Schreier.Co1Propagate
public import CFSG.Sporadic.Schreier.Co1SplitMono
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Schreier.Co1StabCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import Certificates.Data.CFSGNative.Co1.Data

@[expose] public section

namespace CFSG.Sporadic.Co1Schreier

open CFSG.Sporadic.SmallF2 (toVecD toVecD_apply toVecD_xor toVecD_injective rowsMatrix)
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

theorem stab_facts :
    Native.mul Native.hRows0 (Native.inv Native.hRows0) = Native.one ∧
    Native.mul Native.hRows1 (Native.inv Native.hRows1) = Native.one ∧
    Native.wf Native.hRows0 = true ∧ Native.wf Native.hRows1 = true ∧
    ∀ k < 4, Native.enumOK (transposeRows 24 Native.hRows0) (transposeRows 24 Native.hRows1)
      (Native.stabVec k) (Native.stabSize k) (Native.stabOrb k) = true := by
  have h := stab_orb_check
  simp only [Native.stabOrbCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  exact h

theorem stab_listRep :
    ListRep [Native.hRows0, Native.hRows1]
    [Native.inv Native.hRows0, Native.inv Native.hRows1] [stabH0, stabH1] :=
  ⟨.cons stabH0_rep (.cons stabH1_rep .nil),
    .cons (stabH0_rep.inv stab_facts.1) (.cons (stabH1_rep.inv stab_facts.2.1) .nil)⟩

theorem kOrbit_stabH
    {k : ℕ} (hk : k < 4) :
    kOrbit stabH (stabVecOf k) = enumSet (Native.stabOrb k) (Native.stabSize k) :=
  kOrbit_eq_enumSet (MRep.actsBy stabH0_rep) (MRep.actsBy stabH1_rep)
    (stab_facts.2.2.2.2 k hk) (by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)

theorem ncard_kOrbit_stabH
    {k : ℕ} (hk : k < 4) :
    (kOrbit stabH (stabVecOf k)).ncard = Native.stabSize k := by
  rw [kOrbit_stabH hk, ncard_enumSet (stab_facts.2.2.2.2 k hk)]

theorem kOrbit_stabH_zero :
    kOrbit stabH (stabVecOf 0) = {stabVecOf 0} := by
  rw [kOrbit_stabH (by norm_num)]
  obtain ⟨-, -, h0, -⟩ := enumOK_parts (stab_facts.2.2.2.2 0 (by norm_num))
  ext w
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 := by
      have : Native.stabSize 0 = 1 := rfl
      omega
    subst this
    rw [h0]
    rfl
  · intro hw
    rw [Set.mem_singleton_iff.mp hw]
    exact ⟨0, by decide, by rw [h0]; rfl⟩

theorem stabH_fix_z
    {h : GL24} (hh : h ∈ stabH) :
    ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 = stabVecOf 0 := by
  have : ((h : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf 0 ∈
      kOrbit stabH (stabVecOf 0) := ⟨h, hh, rfl⟩
  rw [kOrbit_stabH_zero] at this
  exact this

theorem kOrbit_stabH_disjoint
    {j k : ℕ} (hj : j < 4) (hk : k < 4) (hjk : j ≠ k) :
    Disjoint (kOrbit stabH (stabVecOf j)) (kOrbit stabH (stabVecOf k)) := by
  rw [Set.disjoint_left]
  intro w hwj hwk
  have h := (kOrbit_eq_of_mem hwj).symm.trans (kOrbit_eq_of_mem hwk)
  have hc := congrArg Set.ncard h
  rw [ncard_kOrbit_stabH hj, ncard_kOrbit_stabH hk] at hc
  apply hjk
  revert hc
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem witRows_rep
    (m : ℕ) : List.Forall₂ MRep (Native.witRows m) (witMats m) := by
  unfold Native.witRows witMats
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun w _ => MRep.word stab_listRep w

theorem wit_facts {m : ℕ} (hm : m < 3) : ∀ s ∈ Native.witRows m,
    Native.act s (Native.stabVec 0) = Native.stabVec 0 ∧
      Native.act s (Native.stabVec (m + 1)) = Native.stabVec (m + 1) := by
  have h := wit_check
  simp only [Native.witCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  intro s hs
  exact ⟨(h m hm s hs).1.1, (h m hm s hs).1.2⟩

theorem witMats_fix
    {m : ℕ} (hm : m < 3) (i : ℕ) (k : ℕ) (hk : k = 0 ∨ k = m + 1) :
    (((witMats m).getD i 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ stabVecOf k =
      stabVecOf k := by
  have hrep := getD_rep (witRows_rep m) MRep.one i
  rw [stabVecOf, MRep.mulVec hrep]
  by_cases hi : i < (Native.witRows m).length
  · have hmem : (Native.witRows m).getD i Native.one ∈ Native.witRows m := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    rcases hk with rfl | rfl
    · rw [(wit_facts hm _ hmem).1]
    · rw [(wit_facts hm _ hmem).2]
  · rw [List.getD_eq_default _ _ (by omega)]
    have h1 := MRep.mulVec MRep.one (Native.stabVec k)
    rw [Units.val_one, one_mulVec] at h1
    rw [← h1]

theorem fix_facts {m : ℕ} (hm : m < 3) :
    (Native.fixFreeOf m).1 < 24 ∧ (Native.fixFreeOf m).2 < 24 ∧
    ((Native.stabVec 0).testBit (Native.fixFreeOf m).1 &&
        (Native.stabVec (m + 1)).testBit (Native.fixFreeOf m).2) ≠
      ((Native.stabVec 0).testBit (Native.fixFreeOf m).2 &&
        (Native.stabVec (m + 1)).testBit (Native.fixFreeOf m).1) ∧
    ∀ u < 24, Native.nonFree m u = true →
      Native.fixComb (Native.witRows m) (Native.fixStepsOf m u) u = true ∧
      ∀ v < 24, v ≠ u → Native.nonFree m v = true →
        Native.fixComb (Native.witRows m) (Native.fixStepsOf m u) v = false := by
  have h := fix_check
  simp only [Native.fixCheck, Native.fixCheckOf, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h m hm
  refine ⟨h1, h2, h3, fun u hu hnu => ?_⟩
  rcases h4 u hu with h | ⟨hc, hall, -⟩
  · rw [h] at hnu
    exact absurd hnu (by decide)
  · refine ⟨hc, fun v hv hvu hnv => ?_⟩
    rcases hall v hv with (h | h) | h
    · exact absurd h hvu
    · rw [h] at hnv
      exact absurd hnv (by decide)
    · exact h

theorem fixN_eq
    (m c : ℕ) (v : Fin 24) : fixN m c v =
    (((witMats m).getD (c / 24) 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))
        (Fin.ofNat 24 c) v + if v = Fin.ofNat 24 c then 1 else 0 := by
  have hrep := getD_rep (witRows_rep m) MRep.one (c / 24)
  rw [← hrep, CFSG.Sporadic.SmallF2.rowsMatrix_apply, toVecD_apply, fixN, Native.fixCoef,
    Nat.testBit_xor, Nat.testBit_shiftLeft, Fin.val_ofNat, ← Array.getD_eq_getD_getElem?]
  have key : (decide (v.val ≥ c % 24) && Nat.testBit 1 (v.val - c % 24)) =
      decide (v = Fin.ofNat 24 c) := by
    by_cases hv : v.val = c % 24
    · have hvc : v = Fin.ofNat 24 c := Fin.ext (by rw [hv, Fin.val_ofNat])
      rw [hv, Nat.sub_self, decide_eq_true hvc, decide_eq_true (le_refl _), Bool.true_and]
      decide
    · have hne : v ≠ Fin.ofNat 24 c := fun h => hv (by rw [h, Fin.val_ofNat])
      rw [decide_eq_false hne]
      by_cases hle : c % 24 ≤ v.val
      · have hlt : 1 < 2 ^ (v.val - c % 24) := Nat.one_lt_two_pow (by omega)
        rw [Nat.testBit_lt_two_pow hlt, Bool.and_false]
      · rw [decide_eq_false (by omega), Bool.false_and]
  rw [key]
  generalize (((Native.witRows m).getD (c / 24) Native.one).getD (c % 24) 0).testBit v.val = b
  by_cases hv : v = Fin.ofNat 24 c
  · rw [decide_eq_true hv]
    cases b <;> simp only [hv, ↓reduceIte] <;> decide
  · rw [decide_eq_false hv]
    cases b <;> simp only [hv, ↓reduceIte] <;> decide

theorem mem_span_of_fixed
    {m : ℕ} (hm : m < 3) {u : Vec24}
    (hu : ∀ i, (((witMats m).getD i 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ u = u) :
    u ∈ Submodule.span (ZMod 2) {stabVecOf 0, stabVecOf (m + 1)} := by
  obtain ⟨hf1, hf2, hdet, hsteps⟩ := fix_facts hm
  set f₁ : Fin 24 := ⟨(Native.fixFreeOf m).1, hf1⟩ with hf₁
  set f₂ : Fin 24 := ⟨(Native.fixFreeOf m).2, hf2⟩ with hf₂
  have hdet' : stabVecOf 0 f₁ * stabVecOf (m + 1) f₂ ≠ stabVecOf 0 f₂ * stabVecOf (m + 1) f₁ := by
    simp only [stabVecOf, toVecD_testBit, hf₁, hf₂]
    revert hdet
    cases (Native.stabVec 0).testBit (Native.fixFreeOf m).1 <;>
      cases (Native.stabVec 0).testBit (Native.fixFreeOf m).2 <;>
      cases (Native.stabVec (m + 1)).testBit (Native.fixFreeOf m).1 <;>
      cases (Native.stabVec (m + 1)).testBit (Native.fixFreeOf m).2 <;> decide
  obtain ⟨a, b, ha, hb⟩ := exists_ab _ _ _ _ (u f₁) (u f₂) hdet'
  refine Submodule.mem_span_pair.mpr ⟨a, b, ?_⟩
  have ht : u - (a • stabVecOf 0 + b • stabVecOf (m + 1)) = 0 := by
    have hfix : ∀ i, (((witMats m).getD i 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (u - (a • stabVecOf 0 + b • stabVecOf (m + 1))) =
        u - (a • stabVecOf 0 + b • stabVecOf (m + 1)) := fun i => by
      rw [mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul, hu i,
        witMats_fix hm i 0 (Or.inl rfl), witMats_fix hm i (m + 1) (Or.inr rfl)]
    refine Propagate.eq_zero_of_steps (fixN m) (fun v => if Native.nonFree m v.val then 1 else 0)
      (fun v => Native.fixStepsOf m v.val) (fun w hw => ?_) (fun c => ?_) (fun w hw => ?_)
    · have hnw : Native.nonFree m w.val = true := by
        by_contra h
        simp only [h, ↓reduceIte, lt_self_iff_false] at hw
      obtain ⟨hc, hall⟩ := hsteps w.val w.isLt hnw
      refine ⟨?_, fun v hvw hr => ?_⟩
      · have h := Propagate.xor_sum (fun c => Native.fixCoef (Native.witRows m) c w.val)
          (Native.fixStepsOf m w.val) false
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
        unfold fixN
        rw [h]
        simp only [Native.fixComb] at hc
        rw [hc]
        rfl
      · have hnv : Native.nonFree m v.val = true := by
          by_contra h
          simp only [hnw, ↓reduceIte, h, nonpos_iff_eq_zero, one_ne_zero] at hr
        have hv := hall v.val v.isLt (fun h => hvw (Fin.ext h)) hnv
        have h := Propagate.xor_sum (fun c => Native.fixCoef (Native.witRows m) c v.val)
          (Native.fixStepsOf m w.val) false
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
        unfold fixN
        rw [h]
        simp only [Native.fixComb] at hv
        rw [hv]
        rfl
    · obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 24) (Fin 24) (ZMod 2),
          M = (((witMats m).getD (c / 24) 1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) :=
        ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : Vec24, t = u - (a • stabVecOf 0 + b • stabVecOf (m + 1)) := ⟨_, rfl⟩
      have hrow := congrFun (hfix (c / 24)) (Fin.ofNat 24 c)
      rw [← hM, ← ht] at hrow
      rw [← ht]
      have hN : ∀ v, fixN m c v = M (Fin.ofNat 24 c) v + if v = Fin.ofNat 24 c then 1 else 0 :=
        fun v => by rw [fixN_eq, hM]
      simp only [hN, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hsum : ∑ v, t v * M (Fin.ofNat 24 c) v = (M *ᵥ t) (Fin.ofNat 24 c) := by
        rw [mulVec, dotProduct]
        exact Finset.sum_congr rfl fun v _ => mul_comm _ _
      rw [hsum, hrow]
      generalize t (Fin.ofNat 24 c) = x
      revert x
      decide
    · have hw' : Native.nonFree m w.val = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        simp only [h, ↓reduceIte, one_ne_zero] at hw
      simp only [Native.nonFree, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hw'
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hw' with h | h
      · have : w = f₁ := Fin.ext h
        rw [this, ha]
        ring
      · have : w = f₂ := Fin.ext h
        rw [this, hb]
        ring
  rw [sub_eq_zero] at ht
  exact ht.symm

theorem fixSpace_eq
    {m : ℕ} (hm : m < 3) : fixSpace (stabVecOf (m + 1)) =
    ↑(Submodule.span (ZMod 2) {stabVecOf 0, stabVecOf (m + 1)}) := by
  ext u
  constructor
  · intro hu
    exact mem_span_of_fixed hm fun i => hu _ (witMats_mem m i) (witMats_fix hm i (m + 1)
      (Or.inr rfl))
  · intro hu h hh hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
    rw [mulVec_add, mulVec_smul, mulVec_smul, stabH_fix_z hh, hv]

theorem mem_facts {m : ℕ} (hm : m < 3) :
    Native.inEnum (Native.stabOrb (m + 1)) (Native.stabSize (m + 1)) 0 = false ∧
    Native.inEnum (Native.stabOrb (m + 1)) (Native.stabSize (m + 1)) (Native.stabVec 0) = false ∧
    (Native.inEnum (Native.stabOrb (m + 1)) (Native.stabSize (m + 1))
      (Native.stabVec 0 ^^^ Native.stabVec (m + 1)) = true ↔ m = 2) := by
  have h := mem_check
  simp only [Native.memCheck, Native.memCheckOf, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h m hm
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  exact beq_iff_eq

theorem fixPts_eq
    {m : ℕ} (hm : m < 3) : fixPts (stabVecOf (m + 1)) =
    if m = 2 then {stabVecOf (m + 1), stabVecOf 0 + stabVecOf (m + 1)}
    else {stabVecOf (m + 1)} := by
  have henum := stab_facts.2.2.2.2 (m + 1) (by omega)
  obtain ⟨h0, hz, hzv⟩ := mem_facts hm
  have hz' : stabVecOf 0 ∉ kOrbit stabH (stabVecOf (m + 1)) := by
    rw [kOrbit_stabH (by omega), stabVecOf, mem_enumSet_iff henum (stabVec_lt 0 (by norm_num)), hz]
    decide
  have h0' : (0 : Vec24) ∉ kOrbit stabH (stabVecOf (m + 1)) := by
    rw [kOrbit_stabH (by omega), ← CFSG.Sporadic.SmallF2.toVecD_zero 24,
      mem_enumSet_iff henum (by norm_num), h0]
    decide
  have hzv' : stabVecOf 0 + stabVecOf (m + 1) ∈ kOrbit stabH (stabVecOf (m + 1)) ↔ m = 2 := by
    rw [kOrbit_stabH (by omega), stabVecOf, stabVecOf, ← toVecD_xor,
      mem_enumSet_iff henum (Nat.xor_lt_two_pow (stabVec_lt 0 (by norm_num))
        (stabVec_lt (m + 1) (by omega))), hzv]
  have hself : stabVecOf (m + 1) ∈ fixPts (stabVecOf (m + 1)) :=
    ⟨mem_kOrbit_self _ _, fun h _ hv => hv⟩
  ext u
  constructor
  · rintro ⟨hu, hfix⟩
    rw [fixSpace_eq hm, SetLike.mem_coe, mem_span_pair_iff] at hfix
    rcases hfix with rfl | rfl | rfl | rfl
    · exact absurd hu h0'
    · exact absurd hu hz'
    · split_ifs
      · exact Set.mem_insert _ _
      · exact Set.mem_singleton _
    · have := hzv'.mp hu
      simp only [this, ↓reduceIte]
      exact Set.mem_insert_of_mem _ rfl
  · intro hu
    split_ifs at hu with h2
    · rcases hu with rfl | hu
      · exact hself
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]
        refine ⟨hzv'.mpr h2, ?_⟩
        rw [fixSpace_eq hm, SetLike.mem_coe, mem_span_pair_iff]
        exact Or.inr (Or.inr (Or.inr rfl))
    · rw [Set.mem_singleton_iff.mp hu]
      exact hself

end CFSG.Sporadic.Co1Schreier

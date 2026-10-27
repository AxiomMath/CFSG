
module

public import CFSG.Sporadic.Co1Block.PermCheckInputs
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Kernel.Co1B.Act2043
public import Certificates.Kernel.Co1B.Chk2043
public import Certificates.Kernel.Co1B.Iota
public import CFSG.Certificates.Kernel.Co1BActSound
public import CFSG.Certificates.Kernel.Co1BTrSound
public import CFSG.Certificates.Kernel.Misc.HexDropSound
public import CFSG.Certificates.Kernel.PosTableSound
public import CFSG.Sporadic.Co1Block.PermBase
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit
public import Certificates.Kernel.SporSch.Co1.OrbX2
public import Certificates.Data.CFSGNative.Co1.Data

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CertificateChecks.KernelCo1Cover
open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SmallF2 (toVecD toVecD_injective)
open CFSG.Sporadic.SmallF2.Native Matrix

theorem vecs_get {j k : Nat} (hj : j < 117) (hk : k < 840) :
    certVecs[840 * j + k]! = CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) (CV.F j) k := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound CV.all j hj
  rw [← CV.eq] at h
  have e1 : certVecs[840 * j + k]! = (hexTable 6 840 (840 * j) certVecHex)[k]! := by
    unfold certVecs
    rw [getElem!_pos _ _ (by simp [hexTable]; omega), getElem!_pos _ _ (by simp [hexTable]; omega)]
    simp only [hexTable, Array.getElem_ofFn, Nat.zero_add]
  rw [e1, h, getElem!_pos _ _ (by simp [CFSG.KS.Raw.unpack]; omega)]
  simp [CFSG.KS.Raw.unpack]

theorem act0_get {j k : Nat} (hj : j < 117) (hk : k < 840) :
    (certAct 0)[840 * j + k]! = CFSG.KC.Enum.pg 20 (CFSG.KS.mask 20) (AC.F j) k := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound AC.all j hj
  rw [← AC.eq] at h
  have e1 : (certAct 0)[840 * j + k]! = (hexTable 5 840 (840 * j) certActHex)[k]! := by
    unfold certAct
    rw [getElem!_pos _ _ (by simp [hexTable]; omega), getElem!_pos _ _ (by simp [hexTable]; omega)]
    simp only [hexTable, Array.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  rw [e1, h, getElem!_pos _ _ (by simp [CFSG.KS.Raw.unpack]; omega)]
  simp [CFSG.KS.Raw.unpack]

theorem act1_get {j k : Nat} (hj : j < 117) (hk : k < 840) :
    (certAct 1)[840 * j + k]! = CFSG.KC.Enum.pg 20 (CFSG.KS.mask 20) (AC1.F j) k := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_drop_sound (N₀ := 117) AC.all AC1.all j hj
  rw [← AC.eq] at h
  have e1 : (certAct 1)[840 * j + k]! = (hexTable 5 840 (840 * (117 + j)) certActHex)[k]! := by
    unfold certAct
    rw [getElem!_pos _ _ (by simp [hexTable]; omega), getElem!_pos _ _ (by simp [hexTable]; omega)]
    simp only [hexTable, Array.getElem_ofFn]
    congr 2
    omega
  rw [e1, h, getElem!_pos _ _ (by simp [CFSG.KS.Raw.unpack]; omega)]
  simp [CFSG.KS.Raw.unpack]

theorem certVecs_size : certVecs.size = 98280 := by
  unfold certVecs
  simp [hexTable]

theorem certAct_size (k : Nat) : (certAct k).size = 98280 := by
  unfold certAct
  simp [hexTable]

theorem divmod {i : Nat} (hi : i < 98280) : i / 840 < 117 ∧ i % 840 < 840 ∧
    840 * (i / 840) + i % 840 = i :=
  ⟨by omega, Nat.mod_lt _ (by norm_num), Nat.div_add_mod i 840⟩

theorem vAt_eq {a : Nat} (ha : a < 98280) : vAt CV.F a = certVecs[a]! := by
  obtain ⟨h1, h2, h3⟩ := divmod ha
  change CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) (CV.F (a / 840)) (a % 840) = _
  rw [← vecs_get h1 h2, h3]

theorem pg24_lt (P k : Nat) : CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) P k < 2 ^ 24 := by
  have h : CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) P k ≤ CFSG.KS.mask 24 := Nat.and_le_right
  have e : CFSG.KS.mask 24 = 2 ^ 24 - 1 := rfl
  omega

theorem act_facts {i : Nat} (hi : i < 98280) :
    0 < certVecs[i]! ∧ certVecs[i]! < 2 ^ 24 ∧ (certAct 0)[i]! < 98280 ∧ (certAct 1)[i]! < 98280 ∧
      Native.act Native.aR certVecs[i]! = certVecs[(certAct 0)[i]!]! ∧
      Native.act Native.bR certVecs[i]! = certVecs[(certAct 1)[i]!]! := by
  obtain ⟨h1, h2, h3⟩ := divmod hi
  have hc := actChunk_sound (Act.all _ h1) h2
  rw [← h3, vecs_get h1 h2, act0_get h1 h2, act1_get h1 h2]
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc
  refine ⟨c1, pg24_lt _ _, c2, c3, ?_, ?_⟩
  · rw [aR_eq, CFSG.KC.F2W.act_unpackR (Nat.eq_of_beq_eq_true trA_chk'), ← vAt_eq c2]
    exact c4
  · rw [bR_eq, CFSG.KC.F2W.act_unpackR (Nat.eq_of_beq_eq_true trB_chk), ← vAt_eq c3]
    exact c5

theorem A₁_mulVec' {i : Nat} (hi : i < 98280) :
    ((A₁ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i = certVec (certAct 0)[i]! := by
  rw [certVec, MRep.mulVec rep_A₁, (act_facts hi).2.2.2.2.1]
  rfl

theorem A₂_mulVec' {i : Nat} (hi : i < 98280) :
    ((A₂ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ certVec i = certVec (certAct 1)[i]! := by
  rw [certVec, MRep.mulVec rep_A₂, (act_facts hi).2.2.2.2.2]
  rfl

theorem v0_eq : certVecs[0]! = Native.stabVec 0 := by
  have h := vecs_get (j := 0) (k := 0) (by norm_num) (by norm_num)
  rw [Nat.eq_of_beq_eq_true v0_chk] at h
  exact h

theorem orbit_sub : kOrbit GA (stabVecOf 0) ⊆ certX := by
  rintro _ ⟨g, hg, rfl⟩
  refine mulVec_mem_of_closure certX_finite ?_ g hg _ ⟨0, by norm_num, ?_⟩
  · intro x hx v hv
    obtain ⟨i, hi, rfl⟩ := hv
    rcases Set.mem_insert_iff.1 hx with h | h
    · rw [h, A₁_mulVec' hi]
      exact ⟨_, (act_facts hi).2.2.1, rfl⟩
    · rw [Set.mem_singleton_iff.1 h, A₂_mulVec' hi]
      exact ⟨_, (act_facts hi).2.2.2.1, rfl⟩
  · rw [stabVecOf, certVec, v0_eq]

theorem inj_of_ncard {α : Type*} {n : Nat} (f : Fin n → α) (h : n ≤ (Set.range f).ncard) :
    Function.Injective f := by
  classical
  have e : Set.range f = ((Finset.univ.image f : Finset α) : Set α) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [e, Set.ncard_coe_finset] at h
  have hc : (Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin]; exact h)
  have := Finset.card_image_iff.1 hc
  exact fun a b hab => this (Finset.mem_coe.2 (Finset.mem_univ a))
    (Finset.mem_coe.2 (Finset.mem_univ b)) hab

theorem ncard_orbit : (kOrbit GA (stabVecOf 0)).ncard = 98280 := by
  rw [kOrbit_eq_of_mem KernelSporSch.Co1Full2135.z_mem]
  exact KernelSporSch.Co1Full2135.ncard_X

theorem certVec_inj {i j : Nat} (hi : i < 98280) (hj : j < 98280)
    (h : certVec i = certVec j) : i = j := by
  have hle : 98280 ≤ (Set.range fun i : Fin 98280 => certVec i).ncard := by
    rw [← certX_eq_range, ← ncard_orbit]
    exact Set.ncard_le_ncard orbit_sub certX_finite
  have := inj_of_ncard _ hle (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
  exact congrArg Fin.val this

theorem certVecs_inj {i j : Nat} (hi : i < 98280) (hj : j < 98280)
    (h : certVecs[i]! = certVecs[j]!) : i = j :=
  certVec_inj hi hj (by rw [certVec, certVec, h])

theorem mulVec_inj (g : GL24) {x y : Vec24}
    (h : ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x =
      ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ y) : x = y := by
  have := congrArg (fun v => ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) h
  simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] using this

theorem act0_inj {i j : Nat} (hi : i < 98280) (hj : j < 98280)
    (h : (certAct 0)[i]! = (certAct 0)[j]!) : i = j := by
  refine certVec_inj hi hj (mulVec_inj A₁ ?_)
  rw [A₁_mulVec' hi, A₁_mulVec' hj, h]

theorem act1_inj {i j : Nat} (hi : i < 98280) (hj : j < 98280)
    (h : (certAct 1)[i]! = (certAct 1)[j]!) : i = j := by
  refine certVec_inj hi hj (mulVec_inj A₂ ?_)
  rw [A₂_mulVec' hi, A₂_mulVec' hj, h]

theorem isInvA_of_inj {n : Nat} {t : Array Nat} (hlt : ∀ i < n, t[i]! < n)
    (hinj : ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j) : isInvA n t (invCand n t) = true := by
  let g : Equiv.Perm (Fin n) := Equiv.ofBijective (fun i : Fin n => (⟨t[(i : Nat)]!, hlt i i.2⟩ : Fin n))
    (Finite.injective_iff_bijective.1 fun i j hij =>
      Fin.ext (hinj i i.2 j j.2 (congrArg Fin.val hij)))
  have hg : Rep n t g := fun _ => rfl
  have hr := CFSG.Sporadic.SuzRecog.ModelGroups.rep_invCand hg
  unfold isInvA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  have e : t[i]! = (g ⟨i, hi⟩ : Nat) := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨hlt i hi, ?_⟩
  rw [e, hr.apply (g ⟨i, hi⟩).2]
  simp

theorem basisIdx_lt : ∀ t < 24, certBasisIdx.getD t 0 < 840 := by
  decide

theorem basisRows_eq : certBasisRows certVecs = unpackR 24 BR := by
  have hb := recAll_spec _ _ basis_chk
  apply Array.ext
  · rw [certBasisRows_size]
    simp [unpackR]
  · intro t h1 _
    have ht : t < 24 := by rwa [certBasisRows_size] at h1
    have hl : certBasisIdx.getD t 0 < 840 := basisIdx_lt t ht
    rw [← getElem!_pos (certBasisRows certVecs) t h1, certBasisRows_get _ ht]
    have hv := vecs_get (j := 0) (by norm_num) hl
    rw [Nat.mul_zero, Nat.zero_add] at hv
    rw [hv, ← getL_eq, ← Nat.eq_of_beq_eq_true (hb t ht), CFSG.KC.F2W.rowF_eq]
    simp [unpackR]

theorem basis_inv : mulRows 24 (Native.inv (certBasisRows certVecs)) (certBasisRows certVecs) =
    idRows 24 := by
  rw [basisRows_eq, inv_sound' basisInv_chk]
  change Native.mul (unpackR 24 BI) (unpackR 24 BR) = Native.one
  rw [mul_unpack, Nat.eq_of_beq_eq_true basisLeft_chk, one_eq]

theorem perm_check_kernel :
    permCheckOf certVecs (certAct 0) (certAct 1) Native.aR Native.bR = true := by
  simp only [permCheckOf, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨certVecs_size, certAct_size 0⟩, certAct_size 1⟩, v0_eq⟩, basis_inv⟩,
    fun i hi => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨f1, f2, _, _, f5, f6⟩ := act_facts hi
    refine ⟨⟨⟨⟨f2, by omega⟩, ?_⟩, f5⟩, f6⟩
    exact CFSG.KC.PosTable.posTable_get (fun i hi => (act_facts (certVecs_size ▸ hi)).2.1)
      (fun i hi j hj => certVecs_inj (certVecs_size ▸ hi) (certVecs_size ▸ hj))
      (by rw [certVecs_size]; norm_num) (by rw [certVecs_size]; exact hi)
  · exact isInvA_of_inj (fun i hi => (act_facts hi).2.2.1) fun i hi j hj => act0_inj hi hj
  · exact isInvA_of_inj (fun i hi => (act_facts hi).2.2.2.1) fun i hi j hj => act1_inj hi hj

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2.Native in
open CFSG.Monster.B.Co2.Native in
theorem c2043 : permCheckOf certVecs (certAct 0) (certAct 1)
    CFSG.Sporadic.Co1Schreier.Native.aR CFSG.Sporadic.Co1Schreier.Native.bR = true := perm_check_kernel

end CertificateChecks.KernelCo1B

end

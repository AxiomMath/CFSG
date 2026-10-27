module

public import CFSG.Monster.Existence.ELevelBits
import CFSG.Monster.Existence.ELevelCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.B.Short

namespace CertificateChecks.Batch6020

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.B.Short

@[expose] def kapA (x : ℕ) : ℕ :=
  packP (Model.Pauli.mul (alphaN 1 (false, x % 4096, 0)) (alphaN 1 (false, 0, (x >>> 12) % 4096)))

@[expose] def pairsOK (zs ys : List ℕ) (n : ℕ) : Bool :=
  (List.range n).all fun m => (List.range n).all fun j => bX (zs.getD m 0) (ys.getD j 0) == decide (m = j)

@[expose] def fixC : List ℕ := [3, 12, 20, 36, 1024, 2048, 12288, 49152, 81920, 147456, 262144,
  524288, 1048576, 2097152, 4194304, 8388608]

@[expose] def fixD : List ℕ := [4096, 32768, 65536, 114688, 4194304, 8388608, 1, 8, 16, 28, 64, 128,
  256, 512, 1024, 2048]

@[expose] def rankX : List ℕ := [16385, 4097, 4, 1, 128, 64, 512, 256]

@[expose] def rankZ : List ℕ := [4097, 16385, 1, 4, 64, 128, 256, 512]

@[expose] def fixOK : Bool := fixC.all (fun f => kapA f == f) && pairsOK fixD fixC 16

@[expose] def rankOK : Bool := pairsOK rankZ (rankX.map fun x => x ^^^ kapA x) 8

theorem fixOK_eq : fixOK = true := by decide +kernel

theorem rankOK_eq : rankOK = true := by decide +kernel

theorem permArr_one : PermArr (cosetArr 1) = true := by decide +kernel

theorem autArr_one : AutArr (cosetArr 1) := by decide +kernel

noncomputable def pA : AutPerm := ⟨decode (cosetArr 1), mem_AutPerm_of_arr permArr_one autArr_one⟩

noncomputable def gA : Pvis :=
  ⟨(YU ⟨toC (cosetA 1), 0⟩, gO (toC (cosetA 1))), YU_gO_mem_Pvis _⟩ *
    ⟨(sU pA, PO pA), sU_PO_mem_Pvis _⟩

theorem conjQ_gA (y : Model.Pauli) : conjQ gA (pauliQ y) = pauliQ (alphaN 1 y) := by
  rw [gA, conjQ_mul, conjQ_sign_toQ, conjQ_perm_toQ _ (fun k => decode_apply permArr_one k)]
  rfl

theorem conjQ_gA_pauliOf (x : ℕ) :
    conjQ gA (pauliQ (pauliOf x)) = pauliQ (actP (tT 1) (tD 1) x) := by
  have e0 : pauliQ (pauliOf x) = pauliQ (false, 0, 0) * pauliQ (false, x % 2 ^ 12, 0) *
      pauliQ (false, 0, (x >>> 12) % 2 ^ 12) := by
    rw [pauliQ_mod_a false x 0, pauliQ_mod_d false 0 (x >>> 12)]
    exact pauliQ_split false x (x >>> 12)
  have h1 : conjQ gA (pauliQ (false, x % 2 ^ 12, 0)) = pauliQ ((tT 1)[x % 2 ^ 12]!) := by
    rw [conjQ_gA, tT_get 1 (Nat.mod_lt _ (by norm_num))]
  have h2 : conjQ gA (pauliQ (false, 0, (x >>> 12) % 2 ^ 12)) =
      pauliQ ((tD 1)[(x >>> 12) % 2 ^ 12]!) := by
    rw [conjQ_gA, tD_get 1 (Nat.mod_lt _ (by norm_num))]
  rw [e0, map_mul, map_mul]
  simp only [pauliQ_false_zero, map_one, one_mul, h1, h2]
  rw [← pauliQ_mul]
  rfl

theorem kapX_eq_kapA (x : ℕ) : kapX (tT 1) (tD 1) x = kapA x := by
  have h1 : x % 4096 < 2 ^ 12 := Nat.mod_lt _ (by norm_num)
  have h2 : (x >>> 12) % 4096 < 2 ^ 12 := Nat.mod_lt _ (by norm_num)
  rw [kapX, actP, tT_get 1 h1, tD_get 1 h2, kapA]

noncomputable def kap : Module.End (ZMod 2) L2 := modTwoEnd gA.1.2

theorem kap_vecX (x : ℕ) : kap (vecX x) = vecX (kapA x) := by
  have h := phi0_conjQ gA (pauliQ (pauliOf x))
  rw [conjQ_gA_pauliOf, phi0_coordOf_pauliOf, coordOf_pauliQ] at h
  rw [kap, ← h, ← kapX_eq_kapA, kapX, vecX_packP]

theorem sub_one_vecX (x : ℕ) :
    (kap - 1 : Module.End (ZMod 2) L2) (vecX x) = vecX (x ^^^ kapA x) := by
  rw [vecX_xor, ← kap_vecX, LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg,
    ZModModule.neg_eq_self, add_comm]

theorem le_finrank_of_pairsOK {S : Submodule (ZMod 2) L2} {zs ys : List ℕ} {n : ℕ}
    (h : pairsOK zs ys n = true) (hy : ∀ j < n, vecX (ys.getD j 0) ∈ S) :
    n ≤ Module.finrank (ZMod 2) S := by
  let y : Fin n → L2 := fun j => vecX (ys.getD j 0)
  let z : Fin n → L2 := fun m => vecX (zs.getD m 0)
  have hpair : ∀ m j : Fin n, bL (z m) (y j) = if m = j then 1 else 0 := by
    intro m j
    have h1 := List.all_eq_true.1 h (m : ℕ) (List.mem_range.2 m.2)
    have h2 := List.all_eq_true.1 h1 (j : ℕ) (List.mem_range.2 j.2)
    rw [beq_iff_eq] at h2
    change bL (vecX _) (vecX _) = _
    rw [bL_vecX, h2, boolZ_decide]
    simp only [Fin.ext_iff]
  have hli : LinearIndependent (ZMod 2) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have := congrArg (bL (z m)) hg
    rw [map_sum, map_zero] at this
    simp only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] at this
    exact this
  have hli' : LinearIndependent (ZMod 2) (fun j => (⟨y j, hy j j.2⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hli
  simpa using hli'.fintype_card_le_finrank

theorem finrank_ker : Module.finrank (ZMod 2) (LinearMap.ker (kap - 1 : Module.End (ZMod 2) L2)) =
    16 := by
  have hf := fixOK_eq
  rw [fixOK, Bool.and_eq_true, List.all_eq_true] at hf
  have hk : 16 ≤ Module.finrank (ZMod 2) (LinearMap.ker (kap - 1 : Module.End (ZMod 2) L2)) := by
    refine le_finrank_of_pairsOK hf.2 fun j hj => ?_
    rw [LinearMap.mem_ker, sub_one_vecX]
    have hj' : j < fixC.length := by simpa [fixC] using hj
    rw [List.getD_eq_getElem _ _ hj']
    have e := beq_iff_eq.1 (hf.1 _ (List.getElem_mem hj'))
    rw [e, Nat.xor_self, vecX_zero]
  have hr : 8 ≤ Module.finrank (ZMod 2) (LinearMap.range (kap - 1 : Module.End (ZMod 2) L2)) := by
    refine le_finrank_of_pairsOK rankOK_eq fun j hj => ?_
    have hj' : j < rankX.length := by simpa [rankX] using hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map, ← sub_one_vecX]
    exact LinearMap.mem_range_self _ _
  have hsum := LinearMap.finrank_range_add_finrank_ker (kap - 1 : Module.End (ZMod 2) L2)
  rw [finrank_L2] at hsum
  omega

theorem kapA_eq_iff {x : ℕ} (hx : x < 2 ^ 24) :
    kapA x = x ↔ vecX x ∈ LinearMap.ker (kap - 1 : Module.End (ZMod 2) L2) := by
  rw [LinearMap.mem_ker, sub_one_vecX]
  constructor
  · intro e
    rw [e, Nat.xor_self, vecX_zero]
  · intro e
    rw [← vecX_zero] at e
    have := vecX_injective_lt (Nat.xor_lt_two_pow hx (kapX_eq_kapA x ▸ kapX_lt _ _ x))
      (by positivity) e
    have h2 := congrArg (x ^^^ ·) this
    simpa [← Nat.xor_assoc] using h2

theorem fix_count : ((Finset.range (2 ^ 24)).filter fun x => kapX (tT 1) (tD 1) x = x).card =
    2 ^ 16 := by
  set K := LinearMap.ker (kap - 1 : Module.End (ZMod 2) L2)
  set F := (Finset.range (2 ^ 24)).filter fun x => kapX (tT 1) (tD 1) x = x
  have hinj : Set.InjOn vecX (F : Set ℕ) := fun a ha b hb h =>
    vecX_injective_lt (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hb).1) h
  have himg : vecX '' (F : Set ℕ) = (K : Set L2) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      exact (kapA_eq_iff (Finset.mem_range.1 hx1)).1 (kapX_eq_kapA x ▸ hx2)
    · intro hv
      obtain ⟨x, hx, rfl⟩ := exists_packed v
      refine ⟨x, Finset.mem_filter.2 ⟨Finset.mem_range.2 hx, ?_⟩, rfl⟩
      rw [kapX_eq_kapA]
      exact (kapA_eq_iff hx).2 hv
  have hcard : F.card = Nat.card K := by
    rw [← Set.ncard_coe_finset, ← hinj.ncard_image, himg]
    exact (Nat.card_coe_set_eq (K : Set L2)).symm
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_ker]

end CertificateChecks.Batch6020

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census in
theorem certificate6020 : ((Finset.range (2 ^ 24)).filter fun x => kapX (tT 1) (tD 1) x = x).card = 2 ^ 16 := CertificateChecks.Batch6020.fix_count

end Certificates

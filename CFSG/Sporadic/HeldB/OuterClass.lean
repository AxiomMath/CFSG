
module

public import CFSG.Sporadic.HeldB.OuterClassBase

public import CFSG.Sporadic.HeldB.OuterClassCheck
public import CFSG.Sporadic.HeldB.BaseTests
public import CFSG.Sporadic.HeldB.OuterArith
public import CFSG.Sporadic.HeldB.FixCount
public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native

theorem heAutU_zero : heAutU 0 = 0 :=
  Fin.ext ((rep_heU 0).symm.trans heUArr_fix0)

theorem fixCard_heAutU :
    fixCard heAutU = 98 :=
  (fixCard_eq_countP rep_heU).trans heUArr_fixCount

theorem fixCard_heA0 :
    fixCard (heGenPerm 0) = 346 :=
  (fixCard_eq_countP (rep_heGen (by norm_num))).trans heGen0_fixCount

theorem sign_heAutU :
    Equiv.Perm.sign heAutU = 1 := by
  rw [sign_of_fixCard heAutU_sq fixCard_heAutU]
  exact Even.neg_one_pow ⟨2058, by norm_num⟩

theorem heGen0_sq :
    heGenPerm 0 ^ 2 = 1 :=
  (eqA_iff (rep_hePowA (rep_heGen (by norm_num)) 2) rep_idA).1 heGen0_pow2

theorem sign_heGen0 :
    Equiv.Perm.sign (heGenPerm 0) = 1 := by
  rw [sign_of_fixCard heGen0_sq fixCard_heA0]
  exact Even.neg_one_pow ⟨1996, by norm_num⟩

theorem heGen1_pow_seven :
    heGenPerm 1 ^ 7 = 1 :=
  (eqA_iff (rep_hePowA (rep_heGen (by norm_num)) 7) rep_idA).1 heGen1_pow7

theorem sign_heGen1 :
    Equiv.Perm.sign (heGenPerm 1) = 1 := by
  have h := congrArg Equiv.Perm.sign heGen1_pow_seven
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (heGenPerm 1)) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem heP_le_alternating :
    heP ≤ alternatingGroup (Fin 8330) := by
  rw [heP, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Equiv.Perm.mem_alternatingGroup.2 sign_heGen0
  · exact Equiv.Perm.mem_alternatingGroup.2 sign_heGen1

theorem heAutGroup_le_alternating :
    heAutGroup ≤ alternatingGroup (Fin 8330) := by
  rw [heAutGroup]
  exact sup_le heP_le_alternating
    (Subgroup.zpowers_le.2 (Equiv.Perm.mem_alternatingGroup.2 sign_heAutU))

theorem exists_fix_of_mem_heAutGroup
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup)
    (h2 : x ^ 2 = 1) : ∃ q, x q = q :=
  exists_fix_of_sign (by norm_num) h2
    (Equiv.Perm.mem_alternatingGroup.1 (heAutGroup_le_alternating hx))

theorem heBlock12_fix0
    {t1 t2 : Array ℕ} (h1 : t1 ∈ heBlock1) (h2 : t2 ∈ heBlock2) :
    t1[0]! = 0 ∧ t2[0]! = 0 := by
  have h := heBlocks_fix0
  rw [Bool.and_eq_true, Array.all_eq_true', Array.all_eq_true'] at h
  exact ⟨beq_iff_eq.1 (h.1 t1 h1), beq_iff_eq.1 (h.2 t2 h2)⟩

theorem card_heP_centralizer_heAutU :
    Nat.card (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) =
      15120 := by
  rw [card_inf_centralizer]
  refine (card_heP_eq_count_filter (f := commB heUArr heBase) (g := commB heUArr heBase)
    (fun x => heAutU * x = x * heAutU) _ (by norm_num)
    (fun w x hw hx => commB_iff heP_baseFaithful rep_heU hw heBase_lt (heAutU_comm_mem hx))
    fun t0 _ t1 h1 t2 h2 => commB_prune heUArr_fix0 (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans heOuterCent_count

theorem card_heP_twist0 :
    Nat.card {x : heP // (heAutU * x) ^ 2 = 1 ∧ (x : Equiv.Perm (Fin 8330)) 0 = 0} = 3136 :=
  (card_heP_eq_count_filter (f := twistInvB heUArr heBase)
    (g := fun w => twistInvB heUArr heBase w && (evR w 0 == 0))
    (fun x => (heAutU * x) ^ 2 = 1 ∧ x 0 = 0) _ (by norm_num)
    (fun w x hw hx => by
      rw [Bool.and_eq_true, twistInvB_iff heP_baseFaithful rep_heU hw heBase_lt
        (heAutU_twist_sq_mem hx), evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune _ (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans heOuterInv0_count

theorem ncard_heOuterInvs_zero :
    {x | x ∈ heOuterInvs ∧ x 0 = 0}.ncard = 3136 := by
  rw [← card_heP_twist0, ← Nat.card_coe_set_eq]
  symm
  refine Nat.card_congr {
    toFun := fun x => ⟨heAutU * (x.1 : Equiv.Perm (Fin 8330)),
      ⟨heAutGroup.mul_mem heAutU_mem_heAutGroup (heP_le_heAutGroup x.1.2),
        heAutU_mul_not_mem x.1.2,
        orderOf_eq_prime x.2.1 fun h => heAutU_mul_not_mem x.1.2 (by rw [h]; exact heP.one_mem)⟩,
      by rw [Equiv.Perm.mul_apply, x.2.2, heAutU_zero]⟩
    invFun := fun y => ⟨⟨heAutU * (y : Equiv.Perm (Fin 8330)),
      heAutU_mul_mem_of_outer y.2.1.1 y.2.1.2.1⟩, ?_, ?_⟩
    left_inv := fun x => Subtype.ext (Subtype.ext (heAutU_mul_heAutU_mul _))
    right_inv := fun y => Subtype.ext (heAutU_mul_heAutU_mul _) }
  · show (heAutU * (heAutU * (y : Equiv.Perm (Fin 8330)))) ^ 2 = 1
    have h := pow_orderOf_eq_one (y : Equiv.Perm (Fin 8330))
    rwa [y.2.1.2.2, ← heAutU_mul_heAutU_mul (y : Equiv.Perm (Fin 8330))] at h
  · show (heAutU * (y : Equiv.Perm (Fin 8330))) 0 = 0
    rw [Equiv.Perm.mul_apply, y.2.2, heAutU_zero]

theorem ctbh_outer_involution_class_exhaustion :
    {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2}.ncard = 266560 ∧
    {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} =
      {x | ∃ g ∈ heP, x = g * heAutU * g⁻¹} ∧
    Nat.card (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) =
      15120 := by
  have hcl : (conjClass heP heAutU).ncard = 266560 := by
    have h := ncard_conjClass_mul_card heP heAutU
    rw [centralizerIn, card_heP_centralizer_heAutU, card_heP] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))
  have hsub : conjClass heP heAutU ⊆ heOuterInvs := by
    rintro x ⟨g, hg, rfl⟩
    exact heOuterInvs_conj ⟨heAutU_mem_heAutGroup, heAutU_not_mem, orderOf_heAutU⟩ hg
  have hXf := Set.toFinite heOuterInvs
  have hYf := Set.toFinite (conjClass heP heAutU)
  have hYX : hYf.toFinset ⊆ hXf.toFinset := Set.Finite.toFinset_subset_toFinset.2 hsub
  have hfilter : (hXf.toFinset.filter fun x => x 0 = 0).card = 3136 := by
    rw [← ncard_heOuterInvs_zero, ← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsumX : ∑ x ∈ hXf.toFinset, fixCard x = 8330 * 3136 := by
    rw [sum_fixCard_eq (G := heP) 0 (fun q => ?_) hXf.toFinset (fun x hx h hh => ?_), hfilter]
    · have := heP_pretransitive
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq heP (0 : Fin 8330) q
      exact ⟨g, g.2, hg⟩
    · rw [Set.Finite.mem_toFinset] at hx ⊢
      exact heOuterInvs_conj hx hh
  have hsumY : ∑ x ∈ hYf.toFinset, fixCard x = 266560 * 98 := by
    rw [Finset.sum_congr rfl (g := fun _ => 98) fun x hx => ?_]
    · rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card _ hYf, hcl]
    · rw [Set.Finite.mem_toFinset] at hx
      obtain ⟨g, -, rfl⟩ := hx
      rw [fixCard_conj, fixCard_heAutU]
  have hrest : ∑ x ∈ hXf.toFinset \ hYf.toFinset, fixCard x = 0 := by
    have h := Finset.sum_sdiff hYX (f := fixCard)
    omega
  have hXY : hXf.toFinset = hYf.toFinset := by
    refine le_antisymm (fun x hx => ?_) hYX
    by_contra hy
    have hx0 := (Finset.sum_eq_zero_iff.1 hrest) x (Finset.mem_sdiff.2 ⟨hx, hy⟩)
    rw [Set.Finite.mem_toFinset] at hx
    obtain ⟨q, hq⟩ := exists_fix_of_mem_heAutGroup hx.1 (by
      rw [← hx.2.2]
      exact pow_orderOf_eq_one x)
    rw [fixCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx0
    exact hx0 (Finset.mem_univ q) hq
  have hset : heOuterInvs = conjClass heP heAutU := Set.Finite.toFinset_inj.1 hXY
  refine ⟨?_, hset.trans ?_, card_heP_centralizer_heAutU⟩
  · change heOuterInvs.ncard = 266560
    rw [hset, hcl]
  · ext x
    exact Iff.rfl

theorem exists_conj_heAutU
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heAutGroup) (hxP : x ∉ heP)
    (hx2 : orderOf x = 2) : ∃ g ∈ heP, x = g * heAutU * g⁻¹ := by
  have h : x ∈ {x : Equiv.Perm (Fin 8330) | x ∈ heAutGroup ∧ x ∉ heP ∧ orderOf x = 2} :=
    ⟨hx, hxP, hx2⟩
  rw [ctbh_outer_involution_class_exhaustion.2.1] at h
  exact h

end CFSG.Sporadic.HeldB

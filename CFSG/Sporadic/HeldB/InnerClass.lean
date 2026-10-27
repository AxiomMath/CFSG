
module

public import CFSG.Sporadic.HeldB.InnerClassBase

public import CFSG.Sporadic.HeldB.InnerClassCheck
public import CFSG.Sporadic.HeldB.OuterClass
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.CertPBridgeCheckInputs
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.He.Certificate

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB.Native

theorem fixCard_heT1 :
    fixCard heT1P = 42 :=
  (fixCard_eq_countP rep_heT1).trans heT1Arr_fixCount

theorem card_heP_cent0 :
    Nat.card (centralizerIn heP (heGenPerm 0)) = 161280 := by
  rw [centralizerIn, card_inf_centralizer]
  exact (card_heP_eq_count_filter (f := commB (heGen 0) heBase) (g := commB (heGen 0) heBase)
    (fun x => heGenPerm 0 * x = x * heGenPerm 0) _ (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_heGen (by norm_num)) (heGenPerm_mem (by norm_num)) hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune heGen0_fix0 (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans heCent0_count

theorem card_heP_cent1c :
    Nat.card (centralizerIn heP heT1cP) = 21504 := by
  rw [centralizerIn, card_inf_centralizer]
  exact (card_heP_eq_count_filter (f := commB heT1cArr heBase) (g := commB heT1cArr heBase)
    (fun x => heT1cP * x = x * heT1cP) _ (by norm_num)
    (fun w x hw hx => commB_iff_heP rep_heT1c heT1cP_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune heT1cArr_fix0 (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans heCent1_count

theorem card_heP_cent1 :
    Nat.card (centralizerIn heP heT1P) = 21504 := by
  rw [← card_heP_cent1c, centralizerIn, centralizerIn, heT1cP]
  exact (Nat.card_congr (infCentralizerConjEquiv (heGenPerm_mem (by norm_num)) heT1P).toEquiv).symm

theorem card_heP_sq0 :
    Nat.card {x : heP // (x : Equiv.Perm (Fin 8330)) ^ 2 = 1 ∧ (x : Equiv.Perm (Fin 8330)) 0 = 0} =
      1984 :=
  (card_heP_eq_count_filter (f := twistInvB (idA 8330) heBase)
    (g := fun w => twistInvB (idA 8330) heBase w && (evR w 0 == 0))
    (fun x => x ^ 2 = 1 ∧ x 0 = 0) _ (by norm_num)
    (fun w x hw hx => by
      have h := twistInvB_iff heP_baseFaithful (rep_idA (n := 8330)) hw heBase_lt
        (by rw [one_mul]; exact heP.pow_mem hx 2)
      rw [one_mul] at h
      rw [Bool.and_eq_true, h, evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune _ (heBlock12_fix0 h1 h2).1
      (heBlock12_fix0 h1 h2).2).trans heSq0_count

theorem ncard_heInvs_zero :
    {x | x ∈ heInvs ∧ x 0 = 0}.ncard = 1983 := by
  have h1 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 2 = 1 ∧ x 0 = 0}.ncard = 1984 := by
    rw [← card_heP_sq0, ← Nat.card_coe_set_eq]
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x, x.2.1⟩, x.2.2⟩
      invFun := fun x => ⟨x.1, x.1.2, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h2 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 2 = 1 ∧ x 0 = 0} =
      insert 1 {x | x ∈ heInvs ∧ x 0 = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hx, hx2, hx0⟩
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr ⟨⟨hx, orderOf_eq_prime hx2 h⟩, hx0⟩
    · rintro (rfl | ⟨⟨hx, hx2⟩, hx0⟩)
      · exact ⟨heP.one_mem, one_pow 2, rfl⟩
      · refine ⟨hx, ?_, hx0⟩
        rw [← hx2]
        exact pow_orderOf_eq_one x
  have h3 : (1 : Equiv.Perm (Fin 8330)) ∉ {x | x ∈ heInvs ∧ x 0 = 0} := fun h => by
    have := h.1.2
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  rw [h2, Set.ncard_insert_of_notMem h3 (Set.toFinite _)] at h1
  omega

theorem ncard_conjClass_heA0 :
    (conjClass heP (heGenPerm 0)).ncard = 24990 := by
  have h := ncard_conjClass_mul_card heP (heGenPerm 0)
  rw [card_heP_cent0, card_heP] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem ncard_conjClass_heT1 :
    (conjClass heP heT1P).ncard = 187425 := by
  have h := ncard_conjClass_mul_card heP heT1P
  rw [card_heP_cent1, card_heP] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

theorem involution_conj_cases
    {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP) (hs2 : orderOf s = 2) :
    s ∈ conjClass heP (heGenPerm 0) ∨ s ∈ conjClass heP heT1P := by
  have hXf := Set.toFinite heInvs
  have h0f := Set.toFinite (conjClass heP (heGenPerm 0))
  have h1f := Set.toFinite (conjClass heP heT1P)
  have hdisj : Disjoint h0f.toFinset h1f.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rw [Set.Finite.mem_toFinset] at hx0 hx1
    obtain ⟨c, hc, rfl⟩ := hx0
    obtain ⟨d, hd, hx⟩ := hx1
    have hmem : heT1P ∈ conjClass heP (heGenPerm 0) :=
      ⟨d⁻¹ * c, heP.mul_mem (heP.inv_mem hd) hc, by
        rw [show heT1P = d⁻¹ * (d * heT1P * d⁻¹) * d by group, ← hx]
        group⟩
    have hle := Set.ncard_le_ncard (conjClass_subset_of_mem hmem) (Set.toFinite _)
    rw [ncard_conjClass_heA0, ncard_conjClass_heT1] at hle
    omega
  have hYX : h0f.toFinset ∪ h1f.toFinset ⊆ hXf.toFinset := by
    rw [Finset.union_subset_iff, Set.Finite.toFinset_subset_toFinset,
      Set.Finite.toFinset_subset_toFinset]
    exact ⟨conjClass_subset_heInvs (heGenPerm_mem (by norm_num)) orderOf_heA0,
      conjClass_subset_heInvs heT1P_mem orderOf_heT1P⟩
  have hfilter : (hXf.toFinset.filter fun x => x 0 = 0).card = 1983 := by
    rw [← ncard_heInvs_zero, ← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hsumX : ∑ x ∈ hXf.toFinset, fixCard x = 8330 * 1983 := by
    rw [sum_fixCard_eq (G := heP) 0 (fun q => ?_) hXf.toFinset (fun x hx h hh => ?_), hfilter]
    · have := heP_pretransitive
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq heP (0 : Fin 8330) q
      exact ⟨g, g.2, hg⟩
    · rw [Set.Finite.mem_toFinset] at hx ⊢
      exact heInvs_conj hx hh
  have hsumY : ∑ x ∈ h0f.toFinset ∪ h1f.toFinset, fixCard x = 24990 * 346 + 187425 * 42 := by
    rw [Finset.sum_union hdisj, sum_fixCard_conjClass, sum_fixCard_conjClass,
      ncard_conjClass_heA0, ncard_conjClass_heT1, fixCard_heA0, fixCard_heT1]
  have hrest : ∑ x ∈ hXf.toFinset \ (h0f.toFinset ∪ h1f.toFinset), fixCard x = 0 := by
    have h := Finset.sum_sdiff hYX (f := fixCard)
    omega
  have hsX : s ∈ hXf.toFinset := (Set.Finite.mem_toFinset _).2 ⟨hs, hs2⟩
  by_contra hno
  rw [not_or] at hno
  have hsY : s ∉ h0f.toFinset ∪ h1f.toFinset := by
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact fun h => h.elim hno.1 hno.2
  have hx0 := (Finset.sum_eq_zero_iff.1 hrest) s (Finset.mem_sdiff.2 ⟨hsX, hsY⟩)
  obtain ⟨q, hq⟩ := exists_fix_of_mem_heAutGroup (heP_le_heAutGroup hs) (by
    rw [← hs2]
    exact pow_orderOf_eq_one s)
  rw [fixCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx0
  exact hx0 (Finset.mem_univ q) hq

theorem heP_centralizerIn_oddCore
    {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP)
    (hs2 : orderOf s = 2) : CFSG.oddCore (centralizerIn heP s) = ⊥ := by
  rcases involution_conj_cases hs hs2 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact oddCore_eq_bot_of_mulEquiv (infCentralizerConjEquiv hc _)
      (heInner0_oddCore card_heP_cent0)
  · exact oddCore_eq_bot_of_mulEquiv (infCentralizerConjEquiv hc _)
      (heInner1_oddCore card_heP_cent1)

theorem ctbhi_held_inner_involution_centralizers_odd_core :
    (∀ t : Blueprint.NativeSporadic.He, orderOf t = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set Blueprint.NativeSporadic.He)) = ⊥) ∧
    ∀ s : heP, orderOf s = 2 → CFSG.pPrimeCore 2 (Subgroup.centralizer ({s} : Set heP)) = ⊥ := by
  have hP : ∀ s : heP, orderOf s = 2 →
      CFSG.oddCore (Subgroup.centralizer ({s} : Set heP)) = ⊥ := fun s hs2 =>
    oddCore_eq_bot_of_mulEquiv (heCentralizerEquiv s)
      (heP_centralizerIn_oddCore s.2 (by rw [Subgroup.orderOf_coe]; exact hs2))
  refine ⟨fun t ht2 => ?_, fun s hs2 => by rw [← oddCore_eq_pPrimeCore_two']; exact hP s hs2⟩
  have ht2' : orderOf (heEquivP t) = 2 :=
    (@orderOf_mulEquiv_apply _ _ Units.instGroup _ heEquivP t).trans ht2
  rw [← oddCore_eq_pPrimeCore_two']
  exact oddCore_eq_bot_of_mulEquiv (@centralizerEquiv _ _ Units.instGroup _ heEquivP t)
    (hP (heEquivP t) ht2')

end CFSG.Sporadic.HeldB

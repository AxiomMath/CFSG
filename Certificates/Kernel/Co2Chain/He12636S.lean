
module

public import Certificates.Kernel.Co2Chain.He12636
public import Certificates.Kernel.Co2Chain.He12636Syl
public import CFSG.Certificates.Kernel.SporSch.HeSylSound
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeBase
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He12636

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Sporadic.HeldB.Native CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.HeO16 CertificateChecks.KernelSporSch.HeCn
open CertificateChecks.KernelCo2Chain CertificateChecks.KernelCo2Chain.He12636Syl

noncomputable abbrev T (i : Nat) : Equiv.Perm (Fin 8330) := E (sylF80 NF i)

noncomputable abbrev Cj (i : Nat) : Equiv.Perm (Fin 8330) := E (sylF80 CJ i)

theorem repT {i : Nat} (hi : i < 27) : RepF 8330 (HeTc.nfp (sylF80 NF i)) (T i) :=
  E_rep (sylValB_spec kVal i hi).1

theorem repC {i : Nat} (hi : i < 27) : RepF 8330 (HeTc.nfp (sylF80 CJ i)) (Cj i) :=
  E_rep (sylValB_spec kVal i hi).2

theorem memE {F : Nat} (hF : nfValidK 5 HeC.LR F = true) : E F ∈ heP := by
  rw [heP_eq_originalSubgroup]
  exact E_mem hF

theorem memT {i : Nat} (hi : i < 27) : T i ∈ heP := memE (sylValB_spec kVal i hi).1

theorem memC {i : Nat} (hi : i < 27) : Cj i ∈ heP := memE (sylValB_spec kVal i hi).2

theorem kMul {j : Nat} (hj : j < 3) : sylMulB HeTc.nfp heBase 27 NF MT GI j = true := by
  interval_cases j
  exacts [kMul0, kMul1, kMul2]

theorem mulT {j : Nat} (hj : j < 3) {i : Nat} (hi : i < 27) :
    T i * T (sylF5 GI j) = T (sylF5 MT (27 * j + i)) := by
  have hk := (sylRngB_spec kRng).1 (27 * j + i) (by omega)
  have hg := (sylRngB_spec kRng).2.2.1 j hj
  exact (eq_of_eqOnL heP_baseFaithful (repT hk) ((repT hi).comp (repT hg)) (memT hk)
    (heP.mul_mem (memT hi) (memT hg)) (sylMulB_spec (kMul hj) i hi)).symm

theorem T_root : T He12636Syl.R = 1 :=
  eq_of_eqOnL heP_baseFaithful (repT (sylRngB_spec kRng).2.2.2) RepF.one
    (memT (sylRngB_spec kRng).2.2.2) heP.one_mem (sylRootB_spec kRoot)

theorem T_inj {i j : Nat} (hi : i < 27) (hj : j < 27) (h : T i = T j) : i = j := by
  have hk : ∀ {a b : Nat}, a < 27 → b < 27 → T a = T b →
      sylKey heBase (HeTc.nfp (sylF80 NF a)) = sylKey heBase (HeTc.nfp (sylF80 NF b)) :=
    fun {a b} ha hb e => sylKey_congr fun x hx => by
      have hx' := heBase_lt x hx
      rw [repT ha x hx', repT hb x hx', e]
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd (hk hi hj h) (sylKeyB_lt kKey hij (by omega)).ne
  · rfl
  · exact absurd (hk hi hj h) (sylKeyB_lt kKey hij (by omega)).ne'

theorem tree {i : Nat} (hi : i < 27) (hR : i ≠ He12636Syl.R) :
    sylF5 PAR i < 27 ∧ sylF5 GEN i < 3 ∧ sylF5 DEP (sylF5 PAR i) < sylF5 DEP i ∧
      T i = T (sylF5 PAR i) * T (sylF5 GI (sylF5 GEN i)) := by
  obtain ⟨hp, hg⟩ := (sylRngB_spec kRng).2.1 i hi
  obtain ⟨hd, he⟩ := sylTreeB_spec kTree i hi hR
  refine ⟨hp, hg, hd, ?_⟩
  rw [mulT hg hp, he]

theorem exists_S : ∃ S : Subgroup (Equiv.Perm (Fin 8330)), ∀ x, x ∈ S ↔ ∃ i < 27, T i = x :=
  exists_subgroup_of_tab (g := fun j => sylF5 GI j) (M := fun j i => sylF5 MT (27 * j + i))
    (fun j hj i hi => ⟨(sylRngB_spec kRng).1 _ (by omega), mulT hj hi⟩)
    (sylRngB_spec kRng).2.2.2 T_root fun i hi hR => tree hi hR

theorem card_three_part : (Nat.card heP).factorization 3 = 3 := by
  rw [card_heP, show (4030387200 : Nat) = 3 ^ 3 * 149273600 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem conj_T {i : Nat} (hi : i < 27) (hR : i ≠ He12636Syl.R) :
    T i ∈ conjClass heP (bOf heThreeWordsA) ∨ T i ∈ conjClass heP (bOf heThreeWordsB) := by
  have key : ∀ {b : Equiv.Perm (Fin 8330)} {Y : Nat → Nat}, RepF 8330 Y b → b ∈ heP →
      eqOnL heBase (fun x => HeTc.nfp (sylF80 CJ i) (HeTc.nfp (sylF80 NF i) x))
        (fun x => Y (HeTc.nfp (sylF80 CJ i) x)) = true → T i ∈ conjClass heP b := by
    intro b Y hY hb h
    have e := eq_of_eqOnL heP_baseFaithful ((repC hi).comp (repT hi)) (hY.comp (repC hi))
      (heP.mul_mem (memC hi) (memT hi)) (heP.mul_mem hb (memC hi)) h
    refine ⟨(Cj i)⁻¹, heP.inv_mem (memC hi), ?_⟩
    rw [inv_inv, mul_assoc, ← e]
    group
  rcases sylConjB_spec kConj i hi hR with h | h
  · exact Or.inl (key repYA bOf_mem h)
  · exact Or.inr (key repYB bOf_mem h)

theorem three_conj_S {s : Equiv.Perm (Fin 8330)} (hs : s ∈ heP) (hs3 : orderOf s = 3) :
    s ∈ conjClass heP (bOf heThreeWordsA) ∨ s ∈ conjClass heP (bOf heThreeWordsB) := by
  obtain ⟨S, hS⟩ := exists_S
  have hle : S ≤ heP := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := (hS x).1 hx
    exact memT hi
  have hcard : Nat.card (S.subgroupOf heP) = 3 ^ (Nat.card heP).factorization 3 := by
    rw [card_three_part, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      card_of_tab hS fun i hi j hj => T_inj hi hj]
    rfl
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp : IsPGroup 3 (Subgroup.zpowers (⟨s, hs⟩ : heP)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hs3]; norm_num)
  obtain ⟨g, hg⟩ := CFSG.KC.OrbGroup.exists_conj_mem_of_card _ hcard hp
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨i, hi, hT⟩ := (hS _).1 hg
  have hR : i ≠ He12636Syl.R := by
    rintro rfl
    rw [T_root] at hT
    have h1 : s = 1 := by
      have e : s = (g : Equiv.Perm (Fin 8330)) * ((g⁻¹ * ⟨s, hs⟩ * g : heP) :
        Equiv.Perm (Fin 8330)) * (g : Equiv.Perm (Fin 8330))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e, ← hT]
      group
    rw [h1, orderOf_one] at hs3
    exact absurd hs3 (by norm_num)
  have e : s = (g : Equiv.Perm (Fin 8330)) * T i * (g : Equiv.Perm (Fin 8330))⁻¹ := by
    rw [hT]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  rcases conj_T hi hR with h | h
  · obtain ⟨d, hd, e'⟩ := conj_mem_of_conj g.2 h
    exact Or.inl ⟨d, hd, e'⟩
  · obtain ⟨d, hd, e'⟩ := conj_mem_of_conj g.2 h
    exact Or.inr ⟨d, hd, e'⟩

theorem ncard_A : (conjClass heP (bOf heThreeWordsA)).ncard = 533120 := by
  have h := ncard_conjClass_mul_card heP (bOf heThreeWordsA)
  rw [centralizerIn, card_inf_centralizer, cardA, card_heP] at h
  omega

theorem ncard_B : (conjClass heP (bOf heThreeWordsB)).ncard = 7996800 := by
  have h := ncard_conjClass_mul_card heP (bOf heThreeWordsB)
  rw [centralizerIn, card_inf_centralizer, cardB, card_heP] at h
  omega

theorem ncard_threes_zero : {x | x ∈ heThrees ∧ x 0 = 0}.ncard = 12608 := by
  have hXf := Set.toFinite heThrees
  have h0f := Set.toFinite (conjClass heP (bOf heThreeWordsA))
  have h1f := Set.toFinite (conjClass heP (bOf heThreeWordsB))
  have hdisj : Disjoint h0f.toFinset h1f.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rw [Set.Finite.mem_toFinset] at hx0 hx1
    obtain ⟨c, hc, rfl⟩ := hx0
    obtain ⟨d, hd, hx⟩ := hx1
    have hmem : bOf heThreeWordsB ∈ conjClass heP (bOf heThreeWordsA) :=
      ⟨d⁻¹ * c, heP.mul_mem (heP.inv_mem hd) hc, by
        rw [show bOf heThreeWordsB = d⁻¹ * (d * bOf heThreeWordsB * d⁻¹) * d by group, ← hx]
        group⟩
    have hle := Set.ncard_le_ncard (CFSG.Sporadic.HeldB.conjClass_subset_of_mem hmem)
      (Set.toFinite _)
    rw [ncard_A, ncard_B] at hle
    omega
  have hXY : hXf.toFinset = h0f.toFinset ∪ h1f.toFinset := by
    ext x
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset]
    constructor
    · intro hx
      exact three_conj_S hx.1 hx.2
    · rintro (h | h)
      · exact conjClass_subset_heThrees bOf_mem (orderOf_bOf bigDataA) h
      · exact conjClass_subset_heThrees bOf_mem (orderOf_bOf bigDataB) h
  have hsumX : ∑ x ∈ hXf.toFinset, fixCard x =
      8330 * (hXf.toFinset.filter fun x => x 0 = 0).card := by
    rw [sum_fixCard_eq (G := heP) 0 (fun q => ?_) hXf.toFinset (fun x hx h hh => ?_)]
    · have := heP_pretransitive
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq heP (0 : Fin 8330) q
      exact ⟨g, g.2, hg⟩
    · rw [Set.Finite.mem_toFinset] at hx ⊢
      exact heThrees_conj hx hh
  have hsumY : ∑ x ∈ hXf.toFinset, fixCard x = 533120 * 77 + 7996800 * 8 := by
    rw [hXY, Finset.sum_union hdisj, CFSG.Sporadic.HeldB.sum_fixCard_conjClass,
      CFSG.Sporadic.HeldB.sum_fixCard_conjClass,
      ncard_A, ncard_B, fixCard_bOf bigDataA, fixCard_bOf bigDataB]
  have hfilter : (hXf.toFinset.filter fun x => x 0 = 0).card =
      {x | x ∈ heThrees ∧ x 0 = 0}.ncard := by
    rw [← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  omega

theorem cardC : Nat.card {x : heP // (x : Equiv.Perm (Fin 8330)) ^ 3 = 1 ∧
    (x : Equiv.Perm (Fin 8330)) 0 = 0} = 12609 := by
  have h2 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 3 = 1 ∧ x 0 = 0} =
      insert 1 {x | x ∈ heThrees ∧ x 0 = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨hx, hx3, hx0⟩
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr ⟨⟨hx, orderOf_eq_prime hx3 h⟩, hx0⟩
    · rintro (rfl | ⟨⟨hx, hx3⟩, hx0⟩)
      · exact ⟨heP.one_mem, one_pow 3, rfl⟩
      · refine ⟨hx, ?_, hx0⟩
        rw [← hx3]
        exact pow_orderOf_eq_one x
  have h3 : (1 : Equiv.Perm (Fin 8330)) ∉ {x | x ∈ heThrees ∧ x 0 = 0} := fun h => by
    have := h.1.2
    rw [orderOf_one] at this
    exact absurd this (by norm_num)
  have h1 : {x : Equiv.Perm (Fin 8330) | x ∈ heP ∧ x ^ 3 = 1 ∧ x 0 = 0}.ncard = 12609 := by
    rw [h2, Set.ncard_insert_of_notMem h3 (Set.toFinite _), ncard_threes_zero]
  rw [← h1, ← Nat.card_coe_set_eq]
  exact Nat.card_congr {
    toFun := fun x => ⟨x.1, x.1.2, x.2⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem blocks :
    (countWPar 1 (commB heThreeBA heBase)
        (heBlock0.filter fun t0 => heThreeBA[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 7560 &&
      countWPar 1 (commB heThreeBB heBase)
        (heBlock0.filter fun t0 => heThreeBB[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 504 &&
      countWPar 1 (fun w => fixB heBase w 3) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 12609) = true := by
  have hA := (card_heP_eq_count_filter (f := commB heThreeBA heBase) (g := commB heThreeBA heBase)
    (fun x => bOf heThreeWordsA * x = x * bOf heThreeWordsA) _ (sz := 1) (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_bOf bigDataA) bOf_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune bigDataA.zero (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardA
  have hB := (card_heP_eq_count_filter (f := commB heThreeBB heBase) (g := commB heThreeBB heBase)
    (fun x => bOf heThreeWordsB * x = x * bOf heThreeWordsB) _ (sz := 1) (by norm_num)
    (fun w x hw hx => commB_iff_heP (rep_bOf bigDataB) bOf_mem hw hx)
    fun t0 _ t1 h1 t2 h2 => commB_prune bigDataB.zero (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardB
  have hC := (card_heP_eq_count_filter (f := fun w => fixB heBase w 3)
    (g := fun w => fixB heBase w 3 && (evR w 0 == 0))
    (fun x => x ^ 3 = 1 ∧ x 0 = 0) _ (sz := 1) (by norm_num)
    (fun w x hw hx => by
      have h := CFSG.Sporadic.Schreier.fixB_iff_eq_one heP_baseFaithful heBase_lt hw hx 3
      rw [Bool.and_eq_true, h, evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune (fun w => fixB heBase w 3) (t0 := t0)
      (heBlock12_fix0' h1 h2).1 (heBlock12_fix0' h1 h2).2).symm.trans cardC
  rw [hA, hB, hC]
  rfl

end CertificateChecks.KernelCo2Chain.He12636

end

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Sp
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Sc
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Frat
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Cyc
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3W
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BBar
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.GroupTheory.BarImageConj
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c4_sp_of_facts {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {s r : ℕ} (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p % 3 ≠ 1)
    {A₀ : Subgroup G} (hA₀M : A₀ ≤ D.M) (hA₀ : IsElemAbelian p A₀) (hA₀c : Nat.card A₀ = p ^ 4)
    (hA₀N : ∀ K ∈ conjSetOf D.M L, A₀ ≤ normalizer (K : Set G))
    (hcyc : ∀ K ∈ conjSetOf D.M L, ∀ S : Subgroup (Bar2 D.M),
      IsSylowOf r S (barImage D.M K) → IsCyclic S)
    (hKS : ∀ K ∈ conjSetOf D.M L, ∀ S : Subgroup (Bar2 D.M), IsSylowOf r S (barImage D.M K) →
      ∀ y ∈ barImage D.M K, y ∈ normalizer (S : Set (Bar2 D.M)) → orderOf y ≠ p)
    (hinf : ∀ K ∈ conjSetOf D.M L, ∀ B : Subgroup (Bar2 D.M), IsElemAbelian p B →
      Nat.card (B ⊓ barImage D.M K : Subgroup (Bar2 D.M)) ≤ p)
    (hpK : ∀ K ∈ conjSetOf D.M L, p ∣ Nat.card (barImage D.M K)) :
    IsStronglyPEmbedded r D.M := by
  refine uc22r899c4_sp_of_scalar hSg h614 h76 hL hc3 hLS hs hsn hr hrs hp ?_
  intro K₁ h1S K₂ h2S hne a₁ a₂ ha₁ ha₂ ha₁o ha₂o
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22ine229_ne_two hs hrs
  obtain ⟨K₃, h3S, h31, h32⟩ := uc22r899c3_exists_third (K₁ := K₁) (K₂ := K₂) hc3
  set Kf : Fin 3 → Subgroup G := ![K₁, K₂, K₃] with hKf
  have hKfS : ∀ i, Kf i ∈ conjSetOf D.M L := by
    intro i
    fin_cases i
    exacts [h1S, h2S, h3S]
  have hKfne : ∀ i j, i ≠ j → Kf i ≠ Kf j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    exacts [hne, h31.symm, hne.symm, h32.symm, h31, h32]
  have hKfC : ∀ i, Kf i ∈ calC D.M := fun i => uc22p2214_calC_of_mem_conjSetOf hL (hKfS i)
  have hKfM : ∀ i, Kf i ≤ D.M := fun i => uc22p22a_le_of_isSubnormal (hKfC i).1
  set Kb : Fin 3 → Subgroup (Bar2 D.M) := fun i => barImage D.M (Kf i) with hKb
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Kb i, ∀ y ∈ Kb j, x * y = y * x := fun i j hij =>
    uc22p22l_barImage_commute (hKfC i) (hKfC j) (hKfne i j hij)
  obtain ⟨w, hwM, hw1, hw2, hw3⟩ :=
    uc22r899c4_exists_cycle hc3 h1S h2S h3S hne h31.symm h32.symm
  have hwK : ∀ i, (Kf i).map (MulAut.conj w).toMonoidHom = Kf (i + 1) := by
    intro i
    fin_cases i
    exacts [hw1, hw2, hw3]
  have hwKb : ∀ i,
      (Kb i).map (MulAut.conj (uc22p21cPi D.M ⟨w, hwM⟩)).toMonoidHom = Kb (i + 1) := by
    intro i
    have h := CFSG.GroupTheory.barImage_map_conj D.M (Kf i) (hKfM i) hwM
    rw [hwK i] at h
    exact h.symm
  have hord : ∀ x : ↥D.M, orderOf (x : G) = r → orderOf (uc22p21cPi D.M x) = r := by
    intro x hx
    rw [Subgroup.orderOf_coe] at hx
    have hxr : x ^ r = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    refine orderOf_eq_prime (by rw [← map_pow, hxr, map_one]) fun h1 => ?_
    have h2 := uc22r8100b_eq_one_of_mem_pCore ((QuotientGroup.eq_one_iff _).1 h1)
      (hr.odd_of_ne_two hr2) hxr
    rw [h2, orderOf_one] at hx
    exact hr.one_lt.ne hx
  have ht₁ : uc22p21cPi D.M a₁ ∈ Kb 0 := uc22p21c_mem_barImage.2 ⟨a₁, ha₁, rfl⟩
  have ht₂ : uc22p21cPi D.M a₂ ∈ Kb 1 := uc22p21c_mem_barImage.2 ⟨a₂, ha₂, rfl⟩
  obtain ⟨S₁, hS₁, ht₁S⟩ := uc22r8100b_exists_sylow_mem ht₁ (hord a₁ ha₁o)
  obtain ⟨S₂, hS₂, ht₂S⟩ := uc22r8100b_exists_sylow_mem ht₂ (hord a₂ ha₂o)
  obtain ⟨S₃, hS₃⟩ := exists_isSylowOf r (Kb 2)
  set Sf : Fin 3 → Subgroup (Bar2 D.M) := ![S₁, S₂, S₃] with hSf
  have hSfS : ∀ i, IsSylowOf r (Sf i) (Kb i) := by
    intro i
    fin_cases i
    exacts [hS₁, hS₂, hS₃]
  obtain ⟨w', hw'K, hw'S⟩ := uc22r899c4_exists_shift hSfS hcomm hwKb
  set tf : Fin 3 → Bar2 D.M :=
    ![uc22p21cPi D.M a₁, uc22p21cPi D.M a₂, w' * uc22p21cPi D.M a₂ * w'⁻¹] with htf
  have htS : ∀ i, tf i ∈ Sf i := by
    intro i
    fin_cases i
    · exact ht₁S
    · exact ht₂S
    · have h : S₂.map (MulAut.conj w').toMonoidHom = S₃ := hw'S 1
      show w' * uc22p21cPi D.M a₂ * w'⁻¹ ∈ S₃
      rw [← h]
      exact ⟨_, ht₂S, rfl⟩
  have hto : ∀ i, orderOf (tf i) = r := by
    intro i
    fin_cases i
    · exact hord a₁ ha₁o
    · exact hord a₂ ha₂o
    · exact (MulEquiv.orderOf_eq (MulAut.conj w') _).trans (hord a₂ ha₂o)
  have hdisj : Disjoint (A₀.subgroupOf D.M) (uc22p21cPi D.M).ker := by
    refine Subgroup.disjoint_def.2 fun {x} hxA hxk => ?_
    exact uc22r8100b_eq_one_of_mem_pCore
      ((QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxk)) (hpp.odd_of_ne_two hp2)
      (Subtype.ext (hA₀.2 (x : G) hxA))
  have hA₀el : IsElemAbelian p (barImage D.M A₀) := (hA₀.subgroupOf D.M).map (uc22p21cPi D.M)
  have hA₀card : Nat.card (barImage D.M A₀) = p ^ 4 := by
    rw [← hA₀c, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀M).toEquiv]
    exact UC6S846.card_map_of_disjoint_ker (uc22p21cPi D.M) (A₀.subgroupOf D.M) hdisj
  have hKSf : ∀ i, ∀ y ∈ Kb i, y ∈ normalizer (Sf i : Set (Bar2 D.M)) → orderOf y ≠ p :=
    fun i => hKS (Kf i) (hKfS i) (Sf i) (hSfS i)
  obtain ⟨d, hdo, hdN⟩ := uc22r899c4_exists_frattini3 hpp hr hSfS hKSf
    (fun i B hB => hinf (Kf i) (hKfS i) B hB) hcomm hA₀el hA₀card
    (fun i => uc22r8100b_barImage_le_normalizer (hA₀N (Kf i) (hKfS i)))
  have e0 : tf 0 = uc22p21cPi D.M a₁ := rfl
  have e1 : tf 1 = uc22p21cPi D.M a₂ := rfl
  have hsc := uc22r899c4_exists_scalar (K := Kb) (S := Sf) (t := tf) hpp hr hp3
    (fun i => hcyc (Kf i) (hKfS i) (Sf i) (hSfS i)) (fun i => (hSfS i).le) htS hto hcomm hw'K
    hw'S hdo (fun i => (hdN i).1) (fun i => (hdN i).2) (hKSf 2) (hpK K₃ h3S)
  rw [e0, e1] at hsc
  exact hsc

end CFSG.LocalAnalysis.UniquenessCase.UC22

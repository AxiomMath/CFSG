module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartTwo.Sec14.Item147
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import Certificates.Certificate2326
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3171
public import Certificates.Certificate3171Base
public import Certificates.Certificate43
public import Certificates.Certificate8166
public import Certificates.Certificate8169

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem eq_bot_of_le_center {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    [hQ : Group.IsPerfect Q] (P : Sylow p Q) (hP : (P : Subgroup Q) ≤ Subgroup.center Q) :
    (P : Subgroup Q) = ⊥ := by
  have hPc : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_center_iff.mp (hP hy) x).symm
  set φ := MonoidHom.transferSylow P hPc with hφ
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hQ.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hP (φ b).2) (φ a : Q))
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hPc
  rw [← hφ, hker] at hcompl
  have hcard := hcompl.card_mul_card
  rw [Subgroup.card_top] at hcard
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h1 : Nat.card (P : Subgroup Q) = 1 := by
    have : Nat.card Q * Nat.card (P : Subgroup Q) = Nat.card Q * 1 := by rw [hcard, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact Subgroup.eq_bot_of_card_eq _ h1

variable {H : Type} [Group H] [Finite H]

theorem false_of_le_sup_of_ne {K X O J L₀ : Subgroup H} (hK : K ∈ thetaComponents 3 H)
    (hX : X ∈ thetaComponents 3 H) (hKX : K ≠ X) (hL₀X : L₀ ≤ X) (hO : O.Normal)
    (hO3 : ¬ 3 ∣ Nat.card O) (hJ3 : ¬ 3 ∣ Nat.card J)
    (hJL₀ : J ≤ Subgroup.normalizer (L₀ : Set H)) (hKle : K ≤ O ⊔ J ⊔ L₀)
    (hK3 : 3 ∣ Nat.card K) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 H with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective θ
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK
  have hXc := isComponent_map_of_mem_thetaComponents Nat.prime_three hX
  have hne : K.map π ≠ X.map π := fun h => hKX (hbij.injOn hK hX h)
  have hKX' : ⁅K.map π, X.map π⁆ = ⊥ :=
    (LocalCores.distinct_components_commute hKc hXc).resolve_left hne
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 hK3
  have hk3 : orderOf (k : H) = 3 := by rw [Subgroup.orderOf_coe, hk]
  have hπk : orderOf (π k) = 3 := by
    have hdvd : orderOf (π k) ∣ 3 := by
      have := orderOf_map_dvd π (k : H)
      rwa [hk3] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      rw [orderOf_eq_one_iff, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have := Subgroup.orderOf_dvd_natCard θ h1
      rw [hk3] at this
      exact hθ3 this
    · exact h3
  have hπkK : π k ∈ K.map π := Subgroup.mem_map_of_mem π k.2
  have hK3' : 3 ∣ Nat.card (K.map π) := by
    have := Subgroup.orderOf_dvd_natCard _ hπkK
    rwa [hπk] at this
  have hOn : (O.map π).Normal := hO.map π hπs
  have hKO : ⁅K.map π, O.map π⁆ = ⊥ := by
    refine (LocalCores.component_normal_subgroup hKc hOn).resolve_left fun hle => ?_
    have h1 : 3 ∣ Nat.card (O.map π) := by
      have := Subgroup.orderOf_dvd_natCard _ (hle hπkK)
      rwa [hπk] at this
    exact hO3 (h1.trans (Subgroup.card_map_dvd O π))
  set N := O.map π ⊔ L₀.map π with hN
  have hKL : ⁅K.map π, L₀.map π⁆ = ⊥ :=
    le_bot_iff.mp (hKX' ▸ Subgroup.commutator_mono le_rfl (Subgroup.map_mono hL₀X))
  have hNC : N ≤ Subgroup.centralizer (K.map π : Set (H ⧸ θ)) := by
    refine sup_le ?_ ?_
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hKO
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hKL
  have hJ3' : ¬ 3 ∣ Nat.card (J.map π) := fun h => hJ3 (h.trans (Subgroup.card_map_dvd J π))
  have hJN : J.map π ≤ Subgroup.normalizer (N : Set (H ⧸ θ)) := by
    refine Sec14.le_normalizer_sup ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr hOn]
      exact le_top
    · exact (Subgroup.map_mono hJL₀).trans (Subgroup.le_normalizer_map π)
  have hKJN : K.map π ≤ J.map π ⊔ N := by
    refine (Subgroup.map_mono hKle).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup, hN]
    exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
      (le_sup_right.trans le_sup_right)
  have hKperf : Group.IsPerfect ↥(K.map π) := hKc.1.1
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥(K.map π)))
  have hPZ : (P : Subgroup ↥(K.map π)) ≤ Subgroup.center ↥(K.map π) := by
    intro x hx
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
    have hxn : (x : H ⧸ θ) ^ 3 ^ n = 1 := by
      have := congrArg (fun y : ↥(P : Subgroup ↥(K.map π)) => ((y : ↥(K.map π)) : H ⧸ θ)) hn
      simpa using this
    have hxN : (x : H ⧸ θ) ∈ N :=
      Proof176Steps.mem_of_three_element_sup hJN hJ3' (hKJN x.2) hxn
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hNC hxN) (y : H ⧸ θ) y.2)
  have hPbot := eq_bot_of_le_center P hPZ
  exact Sylow.ne_bot_of_dvd_card P hK3' hPbot

end CFSG.RankThree.PartTwo.Sec17.Proof17Res9

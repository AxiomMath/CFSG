module

public import CFSG.RankThree.PartOne.Q1327S.Count
public import CFSG.RankThree.PartOne.KS.J2

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  Subgroup

variable {Q : Type} [Group Q] [Finite Q]

theorem j2_centralizer_Q_le :
    ∀ g ∈ j2P, (∀ q ∈ j2FiveQ, g * q = q * g) → g ∈ j2FiveQ := by
  obtain ⟨-, -, hC, -⟩ := R3E_J2_full_five_centralizer_structure
  intro g hgP hg
  have h0 := (hC 0).1
  have h3 := (hC 0).2.2.1
  have hx0 : j2FiveLine 0 ∈ j2FiveQ := j2FiveLine_mem_Q 0
  have hgR : g ∈ j2R := Subgroup.mem_sup_left hgP
  have hgC : g ∈ j2FiveC ((0 : Fin 6) : ℕ) := by
    rw [h0]
    refine Subgroup.mem_inf.2 ⟨hgR, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact hg _ hx0
  rw [← h3]
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun q hq => (hg q hq).symm, hgC⟩

theorem not_perm3_J2
    (e : Q ≃* NativeSporadic.Carrier .J2) {Ē : Subgroup Q}
    (hEcard : Nat.card Ē = 5 ^ 2) : ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨⟨hQP, -, -, hQcard, S, hS⟩, -, -, -⟩ := R3E_J2_full_five_centralizer_structure
  have hcard : Nat.card Q = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  let f : Q ≃* ↥j2P := e.trans j2PermEquiv
  have hcardP : Nat.card ↥j2P = 604800 := by rw [← Nat.card_congr f.toEquiv, hcard]
  have hQ : ¬ 5 ^ 3 ∣ Nat.card Q := by rw [hcard]; norm_num
  have hfac : (Nat.card ↥j2P).factorization 5 = 2 :=
    factorization_eq_two Nat.prime_five (by rw [hcardP]; norm_num)
      (by rw [hcardP]; norm_num) (by rw [hcardP]; norm_num)
  have hS₀ : Nat.card (S : Subgroup ↥j2P) = 5 ^ (Nat.card ↥j2P).factorization 5 :=
    Sylow.card_eq_multiplicity S
  have hSC : Subgroup.centralizer ((S : Subgroup ↥j2P) : Set ↥j2P) ≤ (S : Subgroup ↥j2P) := by
    intro g hg
    rw [hS, Subgroup.mem_subgroupOf]
    refine j2_centralizer_Q_le (g : Equiv.Perm (Fin 315)) g.2 fun q hq => ?_
    have hq' : (⟨q, hQP hq⟩ : ↥j2P) ∈ (S : Subgroup ↥j2P) := by
      rw [hS, Subgroup.mem_subgroupOf]
      exact hq
    have := Subgroup.mem_centralizer_iff.1 hg _ hq'
    exact congrArg Subtype.val this.symm
  have hC : Subgroup.centralizer (Ē : Set Q) ≤ Ē :=
    centralizer_le_of_sylow_equiv f (by rw [hfac, hEcard]) hS₀ hSC
  refine not_perm3_of_sylow_count hEcard hQ hC fun n hn => ?_
  have hn4032 : n = 4032 := by omega
  subst hn4032
  decide

end CFSG.RankThree.PartOne.Q1327S

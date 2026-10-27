module

public import Certificates.Certificate14963
public import Certificates.Certificate14964
public import Certificates.Certificate14965

public section

namespace CFSG.RankThree.PartOne.SPOR

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

@[expose] def HNClassFacts (y : RH)
    (N n : ℕ) : Prop :=
  ∃ (Q : Subgroup JH) (xs : ℕ → JH),
    (∀ q ∈ Q, jR q * y = y * jR q) ∧ Nat.card Q = N ∧
    (∀ z ∈ Q, orderOf z = 5 → ∃ i < n, ∃ g : JH, jR g * y = y * jR g ∧
        Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
    (∀ i < n, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
        5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR y * (MulAut.conj k)⁻¹).prod))

theorem hn_class_a_check :
    HNClassFacts (jR aJ) 125 7 :=
  Certificates.certificate14963

theorem hn_class_b_check :
    HNClassFacts (jR t4J) 25 5 :=
  Certificates.certificate14964

theorem hn_class_c_check :
    HNClassFacts t1R 25 3 :=
  Certificates.certificate14965

end CFSG.RankThree.PartOne.SPOR

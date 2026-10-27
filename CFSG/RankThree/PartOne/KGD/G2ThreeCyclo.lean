module

public import CFSG.RankThree.PartOne.KGD.G2Abstract
public import CFSG.RankThree.Chevalley.G2CyclotomicTori

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank CFSG.RankThree.Chevalley
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

theorem solvable_normal_cyclotomic (K : Type) [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) (x : adjointGroup .G2 K) (hxp : orderOf x = p) :
    ∀ V : Subgroup (centralizer ({x} : Set (adjointGroup .G2 K))), V.Normal →
      Group.IsSolvable V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  intro V _ _
  obtain ⟨T, -, -, -, -, hcent⟩ :=
    odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hKodd ε hε d hd hp hp3 hpd
  obtain ⟨-, -, hcyc, hcard, hdodd⟩ := hcent x hxp
  have : IsCyclic (centralizer ({x} : Set (adjointGroup .G2 K))) := hcyc
  refine ⟨fun v _ w _ => (IsCyclic.commGroup :
    CommGroup (centralizer ({x} : Set (adjointGroup .G2 K)))).mul_comm v w, ?_⟩
  have hsub : Subsingleton {v : V // v ^ 2 = 1} := by
    refine ⟨fun a b => ?_⟩
    have h1 : ∀ c : {v : V // v ^ 2 = 1}, c = ⟨1, by simp⟩ := by
      intro c
      apply Subtype.ext
      have hc2 : orderOf ((c.1 : V) : centralizer ({x} : Set (adjointGroup .G2 K))) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by
          have := congrArg (fun z : V => (z : centralizer ({x} : Set (adjointGroup .G2 K)))) c.2
          simpa using this)
      have hcd : orderOf ((c.1 : V) : centralizer ({x} : Set (adjointGroup .G2 K))) ∣ d := by
        rw [← hcard]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime 2 d := Nat.coprime_two_left.2 hdodd
      have h2 : orderOf ((c.1 : V) : centralizer ({x} : Set (adjointGroup .G2 K))) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hc2 hcd
      have h3 := orderOf_eq_one_iff.1 h2
      exact Subtype.ext h3
    rw [h1 a, h1 b]
  have : Nat.card {v : V // v ^ 2 = 1} ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
  omega

theorem false_of_plane_cyclotomic (K : Type) [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) (A : Subgroup (MulAut (adjointGroup .G2 K)))
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hAinn : A ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    False := by
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨T, -, -, -, hcyc, -⟩ :=
    odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hKodd ε hε d hd hp hp3 hpd
  obtain ⟨P, -, hPcard, hPp, hPpow⟩ := plane_comap_conj hinj hp hA hAcard hAinn
  exact not_isCyclic_of_exponent_sq hp (fun u => Subtype.ext (hPpow u.1 u.2)) hPcard (hcyc P hPp)

end CFSG.RankThree.PartOne.KGD

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentU3Core
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UG
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3U3Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Subgroup Matrix CFSG.Open CFSG.Blueprint CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem isCyclic_and_card_centralizer_of_lieModel_psu {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hq : p ^ f % 3 = 1) (hU : CFSG.Blueprint.LieModel J .PSU 3 p f) {x : J} (hx : orderOf x = 3) :
    IsCyclic (centralizer ({x} : Set J)) ∧
      Nat.card (centralizer ({x} : Set J)) = (p ^ f) ^ 2 - 1 := by
  have hadm := hU.admissible
  have hUmodel : CFSG.Blueprint.LieModel J .PSU 3 p f := hU
  rcases hU with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K p :=
      charP_of_card_eq_prime_pow (f := 2 * f)
        (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    let e₁ : J ≃* StatedSU 3 (p ^ f) K :=
      (e.trans (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.scalars_subgroupOf_statedSU_eq_bot
          hK hq))).trans QuotientGroup.quotientBot
    let e' : J ≃* SU (unitaryInvolution K p f) 3 := e₁.trans (equivStatedSU hK 3).symm
    let d : SU (unitaryInvolution K p f) 3 := e' x
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hd3 : d ^ 3 = 1 := by
      dsimp only [d]
      rw [← map_pow, hx3, map_one]
    have hd1 : d ≠ 1 := by
      intro h
      have hx1 : x = 1 := e'.injective (by
        dsimp only [d] at h
        rw [h, map_one])
      rw [hx1, orderOf_one] at hx
      omega
    have hcard := card_centralizer_singleton_mulEquiv (G := J)
      (H := SU (unitaryInvolution K p f) 3) e' x
    have hle : Nat.card (centralizer ({d} : Set (SU (unitaryInvolution K p f) 3))) ≤
        (p ^ f) ^ 2 - 1 :=
      card_centralizer_su_three_le (K := K) (p := p) (f := f) (unitaryInvolution K p f)
        (unitaryInvolution_apply K p f) (unitaryInvolution_involutive hK) hf hK hq hd3 hd1
    let D : Subgroup J := Subgroup.zpowers x
    have hD : Nat.card D = 3 := by
      dsimp only [D]
      rw [Nat.card_zpowers, hx]
    obtain ⟨C, hCle, hCcyc, hCcard⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.exists_cyclic_le_centralizer_of_card_three
        (Or.inr ⟨hq, hUmodel⟩) (D := D) hD
    have hcent : centralizer (D : Set J) = centralizer ({x} : Set J) := by
      have hDc : D = Subgroup.closure ({x} : Set J) := by
        dsimp only [D]
        exact Subgroup.zpowers_eq_closure x
      rw [hDc]
      exact Subgroup.centralizer_closure ({x} : Set J)
    have hCle' : C ≤ centralizer ({x} : Set J) := hcent ▸ hCle
    have hupp : Nat.card (centralizer ({x} : Set J)) ≤ (p ^ f) ^ 2 - 1 := by
      rw [← hcard]
      exact hle
    have hCge : Nat.card (centralizer ({x} : Set J)) ≤ Nat.card C := by
      rw [hCcard]
      exact hupp
    have hCeq : C = centralizer ({x} : Set J) := eq_of_le_of_card_ge hCle' hCge
    exact ⟨hCeq ▸ hCcyc, hCeq ▸ hCcard⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

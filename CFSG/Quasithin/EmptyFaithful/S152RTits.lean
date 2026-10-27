module

public import CFSG.Quasithin.EmptyFaithful.S152RDef
public import CFSG.LieType.BorelTits.Tits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.Assembly.LowTwoRank

theorem noE9CentralizedByInvolution_of_reeTitsModel_tits
    {X : Type} [Group X] [Finite X] (h : ReeTitsModel X .Tits 2 1) :
    NoE9CentralizedByInvolution X := by
  intro l hl2 hl1 E hEl hE9 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : HoldsTits X 2 := holdsTits_of_reeTitsModel_tits h
  have hord : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hl2) hl1
  have hUbot : Subgroup.zpowers l ≠ ⊥ := by
    intro hb
    apply hl1
    have : l ∈ Subgroup.zpowers l := Subgroup.mem_zpowers l
    rw [hb, Subgroup.mem_bot] at this
    exact this
  have hUp : IsPGroup 2 (Subgroup.zpowers l) := by
    have hc : Nat.card (Subgroup.zpowers l) = 2 := by rw [Nat.card_zpowers, hord]
    exact IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  obtain ⟨S, P, hPtop, hN, -, -, hSP⟩ := hBT _ hUbot hUp
  have hEP : E ≤ P := fun x hx => hN (centralizer_singleton_le_normalizer_zpowers l (hEl hx))
  have hSsyl : IsSylowTwoOf (S : Subgroup X) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    rw [show ((S : Subgroup X).subgroupOf ⊤).index = (S : Subgroup X).index from
      Subgroup.relIndex_top_right _]
    exact S.not_dvd_index
  obtain ⟨H, N, hU, -, -, hH, hN6, hlat, -, -⟩ :=
    titsSylowOvergroupLattice X h (S : Subgroup X) hSsyl
  have h9P : 9 ∣ Nat.card P := hE9 ▸ Subgroup.card_dvd_of_le hEP
  rcases hlat P hSP with hP | hP | hP | hP
  · rw [hP, hU] at h9P
    omega
  · rw [hP, hH] at h9P
    omega
  · rw [hP, hN6] at h9P
    omega
  · exact hPtop hP

end CFSG.Quasithin

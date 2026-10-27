module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin

variable {G : Type} [Group G]

theorem twoPrimeResidual_le_of_odd {K M : Subgroup G} (hK : K ≤ M)
    (hN : M ≤ Subgroup.normalizer (K : Set G)) (hodd : ¬ 2 ∣ K.relIndex M) :
    twoPrimeResidual M ≤ K :=
  iInf₂_le K ⟨hK, hN, hodd⟩

theorem mem_of_mem_twoPrimeResidual {K M : Subgroup G} (hK : K ≤ M)
    (hN : M ≤ Subgroup.normalizer (K : Set G)) (hodd : ¬ 2 ∣ K.relIndex M) {z : G}
    (hz : z ∈ twoPrimeResidual M) : z ∈ K :=
  twoPrimeResidual_le_of_odd hK hN hodd hz

theorem twoPrimeResidual_le (M : Subgroup G) : twoPrimeResidual M ≤ M :=
  twoPrimeResidual_le_of_odd le_rfl Subgroup.le_normalizer
    (by rw [Subgroup.relIndex_self]; norm_num)

theorem le_twoPrimeResidual_of_isPGroup [Finite G] {M S : Subgroup G} (hSM : S ≤ M)
    (hS : IsPGroup 2 S) : S ≤ twoPrimeResidual M := by
  intro x hx
  refine Subgroup.mem_iInf.mpr fun N => Subgroup.mem_iInf.mpr fun hN => ?_
  exact B6.le_of_isPGroup_of_odd_relIndex hSM hS hN.1 hN.2.1 hN.2.2 hx

theorem mem_twoPrimeResidual_of_orderOf [Finite G] {M : Subgroup G} {s : G} (hs : s ∈ M)
    (ho : ∃ k : ℕ, orderOf s = 2 ^ k) : s ∈ twoPrimeResidual M := by
  obtain ⟨k, hk⟩ := ho
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(Subgroup.zpowers s) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  exact le_twoPrimeResidual_of_isPGroup (Subgroup.zpowers_le.mpr hs) hP (Subgroup.mem_zpowers s)

theorem central_commutes_pgroup [Finite G] {M : Subgroup G} {z s : G}
    (hz : z ∈ Subgroup.centralizer (twoPrimeResidual M : Set G)) (hs : s ∈ M)
    (ho : ∃ k : ℕ, orderOf s = 2 ^ k) : z * s = s * z :=
  (Subgroup.mem_centralizer_iff.1 hz s (mem_twoPrimeResidual_of_orderOf hs ho)).symm

end CFSG.Quasithin.H13.F431

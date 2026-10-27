module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Quot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_le {S P I : Subgroup G} (hS : IsSylowTwoOf S I) (hSP : S ≤ P)
    (hPI : P ≤ I) (hP : IsPGroup 2 P) : P = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hidx⟩ := hS
  have h1 : S.relIndex P * P.relIndex I = S.relIndex I :=
    Subgroup.relIndex_mul_relIndex S P I hSP hPI
  have hodd : ¬ 2 ∣ S.relIndex P := fun h => hidx (by
    have := h.mul_right (P.relIndex I)
    rw [h1] at this
    exact this)
  obtain ⟨n, hn⟩ := hP.index (S.subgroupOf P)
  have hn' : S.relIndex P = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    exact hodd (hn' ▸ dvd_pow_self 2 hne)
  rw [hn0, pow_zero] at hn'
  exact le_antisymm ((Subgroup.relIndex_eq_one.mp hn')) hSP

theorem le_normalizer_of_sylow_index_two {S T Q I X : Subgroup G} (hSyl : IsSylowTwoOf S I)
    (hST : S ≤ T) (hrel : S.relIndex T = 2) (hQT : Q ≤ T) (hQ2 : IsPGroup 2 Q)
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hXI : X ≤ I) (hIX : I ≤ Subgroup.normalizer (X : Set G)) (hX : X = oPrimeResidualOf 3 X) :
    Q ≤ Subgroup.normalizer (X : Set G) := by
  have hSI : S ≤ I := hSyl.1
  have hSN : S ≤ Subgroup.normalizer ((Q ⊓ I : Subgroup G) : Set G) :=
    le_normalizer_inf_of_both (hST.trans hTQ) (hSI.trans Subgroup.le_normalizer)
  have hQIS : Q ⊓ I ≤ S := by
    have h2 : IsPGroup 2 ↥(S ⊔ (Q ⊓ I)) :=
      hSyl.2.1.to_sup_of_normal_right' (hQ2.to_inf_left) hSN
    have := eq_of_isSylowTwoOf_le hSyl le_sup_left (sup_le hSI inf_le_right) h2
    rw [← this]
    exact le_sup_right
  have hNeq : Q ⊓ I = S ⊓ Q := le_antisymm (le_inf hQIS inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans hSI))
  have hrelN : (Q ⊓ I).relIndex Q = 1 ∨ (Q ⊓ I).relIndex Q = 2 := by
    have h1 : (Q ⊓ I).relIndex Q = S.relIndex Q := by
      rw [hNeq, Subgroup.inf_relIndex_right]
    have h2 := Subgroup.relIndex_le_of_le_right (H := S) hQT (by rw [hrel]; norm_num)
    rw [hrel] at h2
    have h3 : S.relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [h1]
    omega
  have hXN : X ≤ Subgroup.normalizer ((Q ⊓ I : Subgroup G) : Set G) :=
    le_normalizer_inf_of_both hXQ (hXI.trans Subgroup.le_normalizer)
  refine le_normalizer_of_eq_oPrimeResidual hX (hQ2.to_inf_left) (inf_le_right.trans hIX) ?_
  intro x hx q hq
  have hc := commutator_mem_of_relIndex_le_two hrelN (hXN hx) (hXQ hx) hq
  have e : q * x * q⁻¹ * x⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by group
  rw [e]
  exact (Q ⊓ I).inv_mem hc

end S15223

end CFSG.Quasithin

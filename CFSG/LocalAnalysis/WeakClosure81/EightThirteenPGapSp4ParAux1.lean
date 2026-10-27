module

public import CFSG.Quasithin.MS93.MSPQuad
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2)
open CFSG.Quasithin.MS93.MSP

private def wcgapsq_oddSet {Y : Type} [Group Y] (N P : Subgroup Y) : Set (Subgroup Y) :=
  {Q | N ≤ Q ∧ Q ≤ P ∧ (Q.subgroupOf P).Normal ∧ Odd (Q.relIndex P)}

private theorem wcgapsq_oTwo_normal {Y : Type} [Group Y] (H : Subgroup Y) :
    ((oTwo H).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (oTwo_le H)]
  refine Subgroup.le_normalizer_iff.mpr fun h hh k hk => ?_
  have hconj : (oTwo H).map (MulAut.conj h).toMonoidHom = oTwo H := by
    rw [oTwo_map_conj]
    congr 1
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact H.mul_mem (H.mul_mem hh hz) (H.inv_mem hh)
    · intro hy
      refine ⟨h⁻¹ * y * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh, ?_⟩
      group
  have : MulAut.conj h k ∈ (oTwo H).map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hk
  rw [hconj] at this
  simpa only [MulAut.conj_apply] using this

theorem wcgapsq_oddResMod_bot_eq_oTwoPrime {Y : Type} [Group Y] [Finite Y]
    (P : Subgroup Y) : oddResMod (⊥ : Subgroup Y) P = oTwo P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    have hmem : oTwo P ∈ wcgapsq_oddSet (⊥ : Subgroup Y) P := by
      refine ⟨bot_le, oTwo_le P, wcgapsq_oTwo_normal P, ?_⟩
      obtain ⟨T, hT, -⟩ := exists_isSylowIn_ge (G := Y) 2 (H := P) (P := ⊥) bot_le
        IsPGroup.of_bot
      have hTo : T ≤ oTwo P := le_oTwo hT.1 hT.2.1
      have hoddT : Odd (T.relIndex P) := by
        rw [← Nat.not_even_iff_odd]
        exact fun h => hT.2.2 (even_iff_two_dvd.mp h)
      have hmul : T.relIndex P = T.relIndex (oTwo P) * (oTwo P).relIndex P :=
        (Subgroup.relIndex_mul_relIndex (H := T) (K := oTwo P) (L := P) hTo (oTwo_le P)).symm
      rw [hmul] at hoddT
      exact Nat.Odd.of_mul_right hoddT
    exact (iInf_le (fun Q => ⨅ (_ : Q ∈ wcgapsq_oddSet (⊥ : Subgroup Y) P), Q)
      (oTwo P)).trans (iInf_le (fun _ => oTwo P) hmem)
  ·
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, n, hn⟩
    rw [oddResMod]
    refine Subgroup.mem_iInf.mpr fun Q => Subgroup.mem_iInf.mpr fun hQ => ?_
    haveI : (Q.subgroupOf P).Normal := hQ.2.2.1
    have hgP : g ∈ P := hg
    let π : ↥P →* (↥P ⧸ Q.subgroupOf P) := QuotientGroup.mk' (Q.subgroupOf P)
    have hpow : (⟨g, hgP⟩ : ↥P) ^ 2 ^ n = 1 := Subtype.ext hn
    have hdvd2 : orderOf (π ⟨g, hgP⟩) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
    have hdvdQ : orderOf (π ⟨g, hgP⟩) ∣ Q.relIndex P := by
      change orderOf (π ⟨g, hgP⟩) ∣ (Q.subgroupOf P).index
      rw [Subgroup.index_eq_card]
      exact orderOf_dvd_natCard _
    have hodd : Odd (orderOf (π ⟨g, hgP⟩)) :=
      Odd.of_dvd_nat hQ.2.2.2 hdvdQ
    have horder1 : orderOf (π ⟨g, hgP⟩) = 1 := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
      rw [hk] at hodd
      have hk0 : k = 0 := by
        by_contra hkne
        exact (Nat.not_even_iff_odd.mpr hodd) (Even.pow_of_ne_zero even_two hkne)
      rw [hk0] at hk
      simpa using hk
    have h1 : π ⟨g, hgP⟩ = 1 := orderOf_eq_one_iff.mp horder1
    have hmemQ : (⟨g, hgP⟩ : ↥P) ∈ Q.subgroupOf P :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf P) ⟨g, hgP⟩).mp h1
    exact Subgroup.mem_subgroupOf.mp hmemQ

end CFSG.LocalAnalysis.WeakClosure81

end

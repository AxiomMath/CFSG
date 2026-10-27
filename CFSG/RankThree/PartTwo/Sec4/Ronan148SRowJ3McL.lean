module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SNoCQ
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem map_centralizer_inf_conj {G : Type*} [Group G] {P : Subgroup G} {y k : G} (hk : k ∈ P)
    (hy : y ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2) :
    (Subgroup.centralizer {y} ⊓ P : Subgroup G).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer {k * y ^ e * k⁻¹} ⊓ P := by
  rw [← KFacts.K426Rest.centralizer_pow_eq hy he]
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
    refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
    calc k * z * k⁻¹ * (k * y ^ e * k⁻¹) = k * (z * y ^ e) * k⁻¹ := by group
      _ = k * (y ^ e * z) * k⁻¹ := by rw [hzc]
      _ = k * y ^ e * k⁻¹ * (k * z * k⁻¹) := by group
  · rintro ⟨hwc, hwP⟩
    refine ⟨k⁻¹ * w * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hwP) hk⟩, by group⟩
    calc k⁻¹ * w * k * y ^ e = k⁻¹ * (w * (k * y ^ e * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y ^ e * k⁻¹) * w) * k := by rw [hwc]
      _ = y ^ e * (k⁻¹ * w * k) := by group

theorem card_comm_j3P_le
    {x : Equiv.Perm (Fin 6156)} (hx : x ∈ CFSG.Sporadic.Schreier.j3P)
    (hxo : orderOf x = 3)
    (hA : Nat.card (Subgroup.centralizer {x} ⊓ CFSG.Sporadic.Schreier.j3P :
      Subgroup (Equiv.Perm (Fin 6156))) = 1080) :
    Nat.card ↥(⁅Subgroup.centralizer {x} ⊓ CFSG.Sporadic.Schreier.j3P,
      Subgroup.centralizer {x} ⊓ CFSG.Sporadic.Schreier.j3P⁆ : Subgroup (Equiv.Perm (Fin 6156))) ≤
      360 := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := KFacts.K426.j3t_fusion hx hxo
  have hA3 : KFacts.K426.j3tXA ^ 3 = 1 := (KFacts.K426.j3tReps_spec (c := 0) (by norm_num)).2
  have hB3 : KFacts.K426.j3tXB ^ 3 = 1 := (KFacts.K426.j3tReps_spec (c := 1) (by norm_num)).2
  rcases hc with rfl | rfl
  · rw [← map_centralizer_inf_conj hk hA3 he, ← Subgroup.map_commutator,
      Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective]
    exact (Subgroup.card_le_of_le KFacts.K426.j3t_derived.1).trans KFacts.K426.j3t_derived.2.le
  · exfalso
    rw [KFacts.K426Rest.card_centralizer_conj hk hB3 he, ← KFacts.K426.j3t_caseB.1,
      KFacts.K426.j3t_caseB.2] at hA
    norm_num at hA

theorem card_comm_le_of_mulEquiv {G G' : Type*} [Group G] [Group G'] {P : Subgroup G'}
    (e : G ≃* P) (x : G) {N : ℕ}
    (h : Nat.card ↥(⁅Subgroup.centralizer {(e x : G')} ⊓ P,
      Subgroup.centralizer {(e x : G')} ⊓ P⁆ : Subgroup G') ≤ N) :
    Nat.card ↥(⁅Subgroup.centralizer {x}, Subgroup.centralizer {x}⁆ : Subgroup G) ≤ N := by
  have hι : Function.Injective (P.subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  have hmap : (Subgroup.centralizer {x}).map (P.subtype.comp e.toMonoidHom) =
      Subgroup.centralizer {(e x : G')} ⊓ P := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
      refine Subgroup.mem_inf.2 ⟨?_, (e z).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ((e z : P) : G') * (e x : P) = (e x : P) * (e z : P)
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hz']
    · intro hw
      obtain ⟨hwc, hwP⟩ := Subgroup.mem_inf.1 hw
      rw [Subgroup.mem_centralizer_singleton_iff] at hwc
      refine ⟨e.symm ⟨w, hwP⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · apply e.injective
        apply Subtype.ext
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_mul]
        exact hwc
      · change ((e (e.symm ⟨w, hwP⟩) : P) : G') = w
        rw [MulEquiv.apply_symm_apply]
  rw [← Subgroup.card_map_of_injective (K := ⁅Subgroup.centralizer {x},
      Subgroup.centralizer {x}⁆) hι, Subgroup.map_commutator, hmap]
  exact h

theorem card_comm_J3_le
    (t : Blueprint.NativeSporadic.Carrier .J3) (ht : orderOf t = 3)
    (hC : Nat.card (Subgroup.centralizer ({t} : Set (Blueprint.NativeSporadic.Carrier .J3))) =
      1080) :
    Nat.card ↥(⁅Subgroup.centralizer ({t} : Set (Blueprint.NativeSporadic.Carrier .J3)),
      Subgroup.centralizer ({t} : Set (Blueprint.NativeSporadic.Carrier .J3))⁆ :
      Subgroup (Blueprint.NativeSporadic.Carrier .J3)) ≤ 360 := by
  have hord : orderOf ((Sec21.Item228CensusProof.j3CarrierEquiv t :
      CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ht
  have hA : Nat.card (Subgroup.centralizer {((Sec21.Item228CensusProof.j3CarrierEquiv t :
      CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156))} ⊓ CFSG.Sporadic.Schreier.j3P :
      Subgroup (Equiv.Perm (Fin 6156))) = 1080 :=
    Eq.trans (KFacts.K426Rest.card_centralizer_of_mulEquiv
      Sec21.Item228CensusProof.j3CarrierEquiv t).symm hC
  exact card_comm_le_of_mulEquiv Sec21.Item228CensusProof.j3CarrierEquiv t
    (card_comm_j3P_le (Sec21.Item228CensusProof.j3CarrierEquiv t).2 hord hA)

theorem noCQOf_mcl :
    NoCQOf (Spor .McL) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .McL ≃* Spor .McL := b
  let f : S ≃* Blueprint.NativeSporadic.Carrier .McL := e.trans b'.symm
  haveI : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv S f.toEquiv
  refine noCQ425_of_at_mulEquiv f fun t ht => ?_
  have hC : Nat.card (Subgroup.centralizer ({t} : Set (Blueprint.NativeSporadic.Carrier .McL))) ∣
      29160 := by
    rcases KFacts.K426Rest.mclThreeCentralizerCard t ht with h | h
    · exact dvd_of_eq h
    · exact (dvd_of_eq h).trans (by norm_num)
  exact noCQAt_of_noA6 (B := 31) hC (by norm_num) (by norm_num) (by decide +kernel)
    fun H hH g => KFacts.K426.mclThreeCentralizer t ht H hH g

theorem noCQOf_j3 :
    NoCQOf (Spor .J3) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .J3 ≃* Spor .J3 := b
  let f : S ≃* Blueprint.NativeSporadic.Carrier .J3 := e.trans b'.symm
  haveI : Finite (Blueprint.NativeSporadic.Carrier .J3) := Finite.of_equiv S f.toEquiv
  refine noCQ425_of_at_mulEquiv f fun t ht => ?_
  rcases Sec21.Item228CensusProof.j3ThreeCentralizerCard t ht with hC | hC
  · refine noCQAt_of_card_eq (B := 11) hC (by norm_num) (by norm_num) (by decide +kernel) ?_
    intro h
    have hle := card_comm_J3_le t ht hC
    rw [h, hC] at hle
    norm_num at hle
  · exact noCQAt_of_card_dvd (B := 7) (dvd_of_eq hC) (by norm_num) (by norm_num)
      (by decide +kernel)

section RowsMcLJ3


theorem rowOf425_mcl :
    RowOf425 (Spor .McL) :=
  rowOf425_of_noCQ noCQOf_mcl

theorem rowOf425_j3 :
    RowOf425 (Spor .J3) :=
  rowOf425_of_noCQ noCQOf_j3

end RowsMcLJ3

end CFSG.RankThree.PartTwo.Sec4.Ronan148S

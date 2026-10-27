module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMap
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv CFSG.LocalAnalysis.UniquenessCase.UC22

namespace ThreeOne

open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

private theorem isSylowTwoOf_D7 :
    CFSG.QuasithinUnique.IsSylowTwoOf D7 A7s := by
  have hT := isSylowTwoOf_T7
  refine ⟨D7_le_A7s, hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe D7_le_A7s), ?_⟩
  intro h2
  have hcard := Subgroup.card_mul_index (D7.subgroupOf A7s)
  have hcardD : Nat.card (D7.subgroupOf A7s) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_A7s).toEquiv, card_D7]
  rw [hcardD, card_A7s] at hcard
  obtain ⟨k, hk⟩ := h2
  rw [hk] at hcard
  omega

private theorem exists_conj_eq_Z
    {S K : Subgroup (Perm (Fin 7))}
    (hK : K ≤ alternatingGroup (Fin 7)) (hS : IsSylowIn 2 S (alternatingGroup (Fin 7)))
    (hSK : S ≤ K) :
    ∃ (g : Perm (Fin 7)) (i : ℕ), i < 12 ∧ B6.conjSub g K = Z i := by
  have hSsyl : CFSG.QuasithinUnique.IsSylowTwoOf S A7s := hS
  have hDsyl : CFSG.QuasithinUnique.IsSylowTwoOf D7 A7s := isSylowTwoOf_D7
  obtain ⟨g, hgA, hg⟩ := B6.isSylowTwoOf_exists_conj hSsyl hDsyl
  refine ⟨g, ?_⟩
  have hDle : D7 ≤ B6.conjSub g K := by
    rw [hg]
    exact Subgroup.map_mono hSK
  have hKleA : B6.conjSub g K ≤ A7s := by
    intro x hx
    obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hx
    rw [← hkx]
    show g * k * g⁻¹ ∈ A7s
    exact A7s.mul_mem (A7s.mul_mem hgA (hK hkK)) (A7s.inv_mem hgA)
  obtain ⟨i, hi, hZi⟩ := overgroups_A7 hDle
    (fun y hy => Equiv.Perm.mem_alternatingGroup.mp (hKleA hy))
  exact ⟨i, hi, hZi⟩

theorem card_mem_of_le_alternatingGroup_seven
    {S K : Subgroup (Perm (Fin 7))}
    (hK : K ≤ alternatingGroup (Fin 7)) (hS : IsSylowIn 2 S (alternatingGroup (Fin 7)))
    (hSK : S ≤ K) :
    Nat.card K = 8 ∨ Nat.card K = 24 ∨ Nat.card K = 72 ∨ Nat.card K = 120 ∨
      Nat.card K = 168 ∨ Nat.card K = 360 ∨ Nat.card K = 2520 := by
  obtain ⟨g, i, hi, hKi⟩ := exists_conj_eq_Z hK hS hSK
  have hcard : Nat.card K = Nat.card (Z i) := by
    rw [← hKi]
    exact (Subgroup.card_map_of_injective (K := K) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm
  rw [hcard, card_Z hi]
  interval_cases i <;> decide

theorem isL3_of_card_eq_168
    {S K : Subgroup (Perm (Fin 7))}
    (hK : K ≤ alternatingGroup (Fin 7)) (hS : IsSylowIn 2 S (alternatingGroup (Fin 7)))
    (hSK : S ≤ K) (h168 : Nat.card K = 168) : IsL3 ↥K 1 := by
  obtain ⟨g, i, hi, hKi⟩ := exists_conj_eq_Z hK hS hSK
  have hcardZ : Nat.card (Z i) = 168 := by
    rw [← hKi]
    exact (Subgroup.card_map_of_injective (K := K) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).trans h168
  rw [card_Z hi] at hcardZ
  have hcases : i = 8 ∨ i = 9 := by
    interval_cases i <;> simp_all [List.getD]
  rcases hcases with rfl | rfl
  · refine isL3_of_mulEquiv ?_
    exact (MulEquiv.subgroupMap (MulAut.conj g) K).trans
      ((MulEquiv.subgroupCongr hKi).trans z8Equiv.symm)
  · refine isL3_of_mulEquiv ?_
    exact (MulEquiv.subgroupMap (MulAut.conj g) K).trans
      ((MulEquiv.subgroupCongr hKi).trans z9Equiv.symm)

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end

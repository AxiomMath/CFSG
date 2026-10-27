module

public import CFSG.Permutation.FiveTransitive.Degree60ThreeOrbitCount
public import CFSG.Permutation.FiveTransitive.Degree60ThreeFixedBound
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeNineBound

open MulAction

theorem card_le_243
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 12)
    (x : X) (hx : Nat.card (orbit Q x) = 9)
    (horbit : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 3) :
    Nat.card Q ≤ 243 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let O : SubMulAction Q X :=
    { carrier := orbit Q x
      smul_mem' := by
        intro q y hy
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hy
        exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩ }
  let rho : Q →* Equiv.Perm O := toPermHom Q O
  let R : Subgroup Q := rho.ker
  have hO : Nat.card O = 9 := hx
  have hindex : R.index ≤ 81 := by
    change rho.ker.index ≤ 81
    rw [Subgroup.index_ker]
    have hgroup : IsPGroup 3 rho.range := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
    obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hgroup
    have hd := Subgroup.card_subgroup_dvd_card rho.range
    rw [Nat.card_perm,hO,he] at hd
    have he4 : e ≤ 4 := by
      by_contra hn
      have h243 : 243 ∣ 3 ^ e := pow_dvd_pow 3 (by omega : 5 ≤ e)
      have hh := h243.trans hd
      norm_num [Nat.factorial] at hh
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) he4
  have hRfixO (r : R) (y : X) (hy : y ∈ orbit Q x) : r • y = y := by
    have h := DFunLike.congr_fun (show rho r.val = 1 from r.property) (⟨y,hy⟩ : O)
    exact congrArg Subtype.val h
  have hxF : x ∉ fixedPoints Q X := by
    intro hxF
    let _ : Fintype (orbit Q x) := Fintype.ofFinite _
    have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hxF
    rw [← Nat.card_eq_fintype_card,hx] at h
    omega
  let A : Set X := fixedPoints Q X ∪ orbit Q x
  have hA : A.ncard = 21 := by
    rw [Set.ncard_union_eq (AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x hxF),
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed,hx]
  let sf := A.toFinite.toFinset
  have hsf : sf.card = 21 := by
    rw [← Set.ncard_coe_finset,A.toFinite.coe_toFinset]
    exact hA
  have hRfixed : ∀ r : R, ∀ y ∈ sf, r • y = y := by
    intro r y hy
    have h : y ∈ A := by simpa only [sf,Set.Finite.mem_toFinset] using hy
    rcases h with h | h
    · exact h r.val
    · exact hRfixO r y h
  have hRorbit : ∀ y : X, Nat.card (orbit R y) ≤ 3 := by
    intro y
    by_cases hy : y ∈ orbit Q x
    · let _ : Fintype (orbit R y) := Fintype.ofFinite _
      have h : y ∈ fixedPoints R X := fun r => hRfixO r y hy
      have he := mem_fixedPoints_iff_card_orbit_eq_one.mp h
      rw [← Nat.card_eq_fintype_card] at he
      omega
    · have hsub : orbit R y ⊆ orbit Q y := by
        intro z hz
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hz
        exact mem_orbit_iff.mpr ⟨r.val,hr⟩
      have hle := Set.ncard_le_ncard hsub
      rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hle
      exact hle.trans (horbit y hy)
  have hRbound : ∀ r : R, r ≠ 1 → Nat.card (fixedBy X r) ≤ 30 := by
    intro r hr
    by_contra hn
    have he : r.val = 1 := Degree60ThreeFixedBound.eq_one_of_thirtyOne_fixed
      P hcard h5 hnotAlt Q r.val (by
        change 31 ≤ (fixedBy X r).ncard
        rw [← Nat.card_coe_set_eq]
        omega)
    exact hr (Subtype.ext he)
  have hRseven := Degree60ThreeOrbitCount.card_le_seven hcard sf hsf hRfixed hRorbit hRbound
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup R)
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh : 9 ≤ 3 ^ e := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ e)
    omega
  have hRthree : Nat.card R ≤ 3 := by
    rw [he]
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 3) he1
  have hm := R.index_mul_card
  have hmul := Nat.mul_le_mul hindex hRthree
  rw [hm] at hmul
  exact hmul

end FiveTransitive.Degree60ThreeNineBound

end CFSG

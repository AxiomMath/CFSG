module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2SplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2NonsplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwo

namespace CFSG
end CFSG
open CFSG

/-!
# The low-2-part reflected torus in odd `PGL₂`

Of the split and nonsplit tori, exactly one has order twice an odd number.
Its involution lies outside the derived `PSL₂` subgroup, while its reflector
can be chosen inside that derived subgroup.  This is the orientation used in
the reflected-torus step of Gorenstein--Walter Theorem 2.6.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- In a finite cyclic subgroup of order `2 * m` with `m` odd, the
nonidentity involution is unique. -/
private lemma involution_unique_of_cyclic_odd_half {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (hUcyc : IsCyclic U) {m : ℕ} (hmOdd : Odd m)
    (hUcard : Nat.card U = 2 * m) {a b : G}
    (haU : a ∈ U) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hbU : b ∈ U) (hb2 : b * b = 1) (hb1 : b ≠ 1) : a = b := by
  let : IsCyclic U := hUcyc
  let : Fintype U := Fintype.ofFinite U
  have hUcard' : Fintype.card U = 2 * m := by
    simpa [Nat.card_eq_fintype_card] using hUcard
  have h2dvd : 2 ∣ Fintype.card U := by
    rw [hUcard']
    exact dvd_mul_right 2 m
  have haU2 : orderOf (⟨a, haU⟩ : U) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · change (⟨a, haU⟩ : U) ^ 2 = 1
      apply Subtype.ext
      simpa [pow_two] using ha2
    · intro h
      apply ha1
      exact congrArg Subtype.val h
  have hbU2 : orderOf (⟨b, hbU⟩ : U) = 2 := by
    apply orderOf_eq_prime (p := 2)
    · change (⟨b, hbU⟩ : U) ^ 2 = 1
      apply Subtype.ext
      simpa [pow_two] using hb2
    · intro h
      apply hb1
      exact congrArg Subtype.val h
  have h := IsCyclic.card_orderOf_eq_totient (α := U) h2dvd
  have h1 : (2 : ℕ).totient = 1 := by norm_num
  rw [h1] at h
  let s : Finset U := Finset.univ.filter (fun x : U => orderOf x = 2)
  have hs : s.card = 1 := by simpa [s] using h
  rcases Finset.card_eq_one.mp hs with ⟨u, hu⟩
  have hau : (⟨a, haU⟩ : U) = u := by
    have : (⟨a, haU⟩ : U) ∈ s := by
      simp [s, haU2]
    simpa [hu] using this
  have hbu : (⟨b, hbU⟩ : U) = u := by
    have : (⟨b, hbU⟩ : U) ∈ s := by
      simp [s, hbU2]
    simpa [hu] using this
  exact congrArg Subtype.val (hau.trans hbu.symm)

/-- In odd `PGL₂(K)`, there is a split or nonsplit cyclic torus whose
two-part has order exactly two.  Its nontrivial torus involution `s` is
outside `PGL₂(K)'`, a reflecting involution `t` lies inside `PGL₂(K)'`,
and the torus involution has dihedral centralizer `U ⊔ ⟨w⟩`. -/
public theorem pgl2_low_two_part_torus_reflection_data
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) :
    ∃ U : Subgroup (PGL2 K), ∃ s t w : PGL2 K,
      IsCyclic U ∧ Odd (Nat.card U / 2) ∧
      (Nat.card U = Nat.card K - 1 ∨
        Nat.card U = Nat.card K + 1) ∧
      s ∈ U ∧ s ∉ commutator (PGL2 K) ∧ s ≠ 1 ∧ s * s = 1 ∧
      t ∈ commutator (PGL2 K) ∧ t ∉ U ∧ t * t = 1 ∧
      (∀ x : PGL2 K, x ∈ U → t * x * t⁻¹ = x⁻¹) ∧
      (t = w ∨ t = w * s) ∧
      w ∉ U ∧ w * w = 1 ∧
      (∀ x : PGL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({s} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w := by
  let : Fintype K := Fintype.ofFinite K
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  rcases hK with ⟨p, f, hp, hpOdd, hf, hKcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hK' : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpOdd, hf, hKcard⟩
  have hqOdd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hpOdd.pow
  let H : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hcomm : H =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
    dsimp [H]
    exact pgl2_commutator_eq_psl2_range_of_card_gt_three K hK' hcard
  have hHindex : H.index = 2 := by
    rw [hcomm]
    exact pgl2_psl2Range_index_eq_two K hK'
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with
      hhalfEven | hhalfOdd
  · obtain ⟨U, s0, w, hUcyc, hUcard, hs0U, hssq0, hs0ne, hwU, hwsq, hwinv,
        hcent, hUcross⟩ :=
      pgl2_nonsplit_torus_centralizer_data K hqOdd
    have hhalfOdd' : Odd ((Nat.card K + 1) / 2) := by
      rcases hqOdd with ⟨k, hk⟩
      rcases hhalfEven with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      omega
    have hUtwo : Nat.card U = 2 * ((Nat.card K + 1) / 2) := by
      rw [hUcard]
      rcases hqOdd with ⟨k, hk⟩
      omega
    have hUnot : ¬ U ≤ H := by
      rw [hcomm]
      exact hUcross hqOdd
    obtain ⟨s, t, hsU, hsH, hsne, hssq, htH, htU, htsq, htinv, htrel⟩ :=
      exists_aligned_involutions_of_cyclic_reflection_index_two
        H U hHindex hUcyc ((Nat.card K + 1) / 2) hhalfOdd'
          hUtwo hUnot w hwU hwsq hwinv
    have hs_eq : s = s0 :=
      involution_unique_of_cyclic_odd_half U hUcyc hhalfOdd' hUtwo
        hsU hssq hsne hs0U hssq0 hs0ne
    have hcent' : Subgroup.centralizer ({s} : Set (PGL2 K)) =
        U ⊔ Subgroup.zpowers w := by
      simpa [hs_eq] using hcent
    exact ⟨U, s, t, w, hUcyc, by simpa [hUcard] using hhalfOdd',
      Or.inr hUcard, hsU, hsH, hsne, hssq, htH, htU, htsq, htinv,
      htrel, hwU, hwsq, hwinv, hcent'⟩
  · obtain ⟨U, s0, w, hUcyc, hUcard, hs0U, hssq0, hs0ne, hwU, hwsq, hwinv,
        hcent, hUcross⟩ :=
      pgl2_split_torus_centralizer_data K hqOdd
    have hUtwo : Nat.card U = 2 * ((Nat.card K - 1) / 2) := by
      rw [hUcard]
      rcases hqOdd with ⟨k, hk⟩
      omega
    have hUnot : ¬ U ≤ H := by
      rw [hcomm]
      exact hUcross hqOdd
    obtain ⟨s, t, hsU, hsH, hsne, hssq, htH, htU, htsq, htinv, htrel⟩ :=
      exists_aligned_involutions_of_cyclic_reflection_index_two
        H U hHindex hUcyc ((Nat.card K - 1) / 2) hhalfOdd
          hUtwo hUnot w hwU hwsq hwinv
    have hs_eq : s = s0 :=
      involution_unique_of_cyclic_odd_half U hUcyc hhalfOdd hUtwo
        hsU hssq hsne hs0U hssq0 hs0ne
    have hcent' : Subgroup.centralizer ({s} : Set (PGL2 K)) =
        U ⊔ Subgroup.zpowers w := by
      simpa [hs_eq] using hcent
    exact ⟨U, s, t, w, hUcyc, by simpa [hUcard] using hhalfOdd,
      Or.inl hUcard, hsU, hsH, hsne, hssq, htH, htU, htsq, htinv,
      htrel, hwU, hwsq, hwinv, hcent'⟩

end CFSG.GorensteinWalter

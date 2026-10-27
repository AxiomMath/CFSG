module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The high-torus involution lies in the derived PSL₂ subgroup

If a cyclic subgroup of odd `PGL₂` crosses the derived subgroup of index two
and has order `2m` with `m` even, its unique involution belongs to the
derived subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

private lemma pgl2_unique_involution_cyclic
    {U : Type u} [Group U] [Finite U] [IsCyclic U] {s : U}
    (hs : s ^ 2 = 1) (hsne : s ≠ 1) :
    ∀ x : U, x ^ 2 = 1 → x ≠ 1 → x = s := by
  classical
  let : Fintype U := Fintype.ofFinite U
  let A : Finset U := Finset.univ.filter (fun a => a ^ 2 = 1)
  have hle : A.card ≤ 2 := by
    simpa [A] using
      (IsCyclic.card_pow_eq_one_le (α := U) (n := 2) (by norm_num))
  have hge : 2 ≤ A.card := by
    let B : Finset U := {1, s}
    have hBsub : B ⊆ A := by
      intro a ha
      dsimp [B] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · simp [A]
      · simp [A, hs]
    have hBcard : B.card = 2 := by
      dsimp [B]
      rw [Finset.card_eq_two]
      exact ⟨1, s, Ne.symm hsne, rfl⟩
    rw [← hBcard]
    exact Finset.card_le_card hBsub
  have hcard : A.card = 2 := le_antisymm hle hge
  intro x hx hxne
  by_contra hxs
  have hdistinct : ({1, s, x} : Finset U).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, s, x, Ne.symm hsne, hxne.symm, Ne.symm hxs, rfl⟩
  have hsub : ({1, s, x} : Finset U) ⊆ A := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp [A]
    · simp [A, hs]
    · simp [A, hx]
  have hle3 : 3 ≤ A.card := by
    rw [← hdistinct]
    exact Finset.card_le_card hsub
  omega

public lemma pgl2_unique_involution_of_cyclic_subgroup
    {G : Type u} [Group G] [Finite G] (U : Subgroup G) (hUcyc : IsCyclic U)
    {s : G} (hsU : s ∈ U) (hssq : s * s = 1) (hsne : s ≠ 1)
    {x : G} (hxU : x ∈ U) (hxsq : x * x = 1) (hxne : x ≠ 1) : x = s := by
  let sU : U := ⟨s, hsU⟩
  let xU : U := ⟨x, hxU⟩
  have hsU2 : sU ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hssq
  have hsUne : sU ≠ 1 := by
    intro h
    exact hsne (congrArg Subtype.val h)
  have hxU2 : xU ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hxsq
  have hxUne : xU ≠ 1 := by
    intro h
    exact hxne (congrArg Subtype.val h)
  have hEq : xU = sU :=
    pgl2_unique_involution_cyclic hsU2 hsUne xU hxU2 hxUne
  exact congrArg Subtype.val hEq

/-- Let `J = PGL₂(K)'` have index two.  If a cyclic torus `U` crosses `J`,
has order `2m` with `m` even, and `s` is its nontrivial involution, then
`s ∈ J`. -/
public theorem pgl2_torus_involution_mem_commutator
    {K : Type u} [Field K] [Finite K]
    (hJindex : (commutator (PGL2 K)).index = 2)
    (U : Subgroup (PGL2 K)) (hUcyc : IsCyclic U)
    {s : PGL2 K} (hsU : s ∈ U) (hssq : s * s = 1) (hsne : s ≠ 1)
    {m : ℕ} (hUcard : Nat.card U = 2 * m) (hmeven : Even m)
    (hUJ : ¬ U ≤ commutator (PGL2 K)) :
    s ∈ commutator (PGL2 K) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : IsCyclic U := hUcyc
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  let UJ : Subgroup (PGL2 K) := U ⊓ J
  let UJU : Subgroup U := UJ.subgroupOf U
  have hUJ' : ∃ a : PGL2 K, a ∈ U ∧ a ∉ J := by
    by_contra h
    apply hUJ
    intro x hx
    by_contra hxJ
    exact h ⟨x, hx, hxJ⟩
  rcases hUJ' with ⟨a, haU, haJ⟩
  have hUJUindex : UJU.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨a, haU⟩, ?_, ?_⟩
    · intro h
      exact haJ (Subgroup.mem_subgroupOf.mp h).2
    · intro b
      by_cases hb : (b : PGL2 K) ∈ J
      · right
        exact Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩
      · left
        apply Subgroup.mem_subgroupOf.mpr
        have hiff := Subgroup.mul_mem_iff_of_index_two hJindex
          (a := (b : PGL2 K)) (b := a)
        exact ⟨U.mul_mem b.2 haU,
          hiff.mpr ⟨fun hbJ => False.elim (hb hbJ),
            fun haJmem => False.elim (haJ haJmem)⟩⟩
  have hUJUcard : Nat.card UJU = Nat.card UJ := by
    let e : UJU ≃ UJ :=
      { toFun := fun x => ⟨(x : PGL2 K), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y => ⟨⟨(y : PGL2 K), y.2.1⟩,
          Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro y; rfl }
    exact Nat.card_congr e
  have hUJcard : Nat.card UJ = m := by
    have hmul := UJU.card_mul_index
    rw [hUJUindex, hUJUcard, hUcard] at hmul
    omega
  have h2dvd : 2 ∣ Nat.card UJ := by
    rw [hUJcard]
    exact even_iff_two_dvd.mp hmeven
  let : Fintype UJ := Fintype.ofFinite UJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card (G := UJ) (p := 2)
    (by simpa [Nat.card_eq_fintype_card] using h2dvd)
  let xG : PGL2 K := (x : UJ)
  have hxUJ : xG ∈ UJ := x.2
  have hxU : xG ∈ U := (inf_le_left : UJ ≤ U) hxUJ
  have hxJ : xG ∈ J := (inf_le_right : UJ ≤ J) hxUJ
  have hxpow : xG * xG = 1 := by
    have hxpow' : (x : UJ) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one x
      rwa [hxord] at h
    simpa [xG, pow_two] using congrArg Subtype.val hxpow'
  have hxne : xG ≠ 1 := by
    intro hx1
    have hx1' : x = 1 := by
      apply Subtype.ext
      exact hx1
    have : (1 : ℕ) = 2 := by simpa [hx1'] using hxord
    norm_num at this
  have hxeq : xG = s :=
    pgl2_unique_involution_of_cyclic_subgroup U hUcyc hsU hssq hsne
      hxU hxpow hxne
  rw [← hxeq]
  exact hxJ

end CFSG.GorensteinWalter

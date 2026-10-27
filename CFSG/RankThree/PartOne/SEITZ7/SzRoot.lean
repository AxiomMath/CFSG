module

public import CFSG.LieType.Chevalley.EvenRootCommutatorTransport
public import CFSG.LieType.Ree.LargeReeBlockData

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

@[expose] def evenRow (τ : Tag) (r : ℕ) : Bool :=
  (((pairTable τ).getD r (0, 0, 0, [])).2.2.2).all fun f => f.2.2.2 % 2 == 0

theorem commute_pinnedX_of_label
    {τ : Tag} {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {m n : ℕ}
    (hm : m < τ.rootCertificate.roots.length) (hn : n < τ.rootCertificate.roots.length)
    (hl : pairLab τ m n < (repsOf τ).length) (he : evenRow τ (pairLab τ m n) = true)
    (x y : R) :
    Commute (pinnedX τ R (τ.rootCertificate.root m) x)
      (pinnedX τ R (τ.rootCertificate.root n) y) := by
  set r := pairLab τ m n with hr
  have hrow : r < (pairTable τ).length := (length_pairTable (τ := τ)).symm ▸ hl
  obtain ⟨h1, h2', h3⟩ := pairTable_getElem_eq hrow
  have hmem : (τ.rootCertificate.root m, τ.rootCertificate.root n) ∈
      MulAction.orbit (WeylGroup τ)
        (τ.rootCertificate.root (repsOf τ)[r].1, τ.rootCertificate.root (repsOf τ)[r].2.1) := by
    rw [orbit_rep_eq hl]
    exact ⟨(m, n), by rw [Set.mem_ofPred_eq, mem_labPairs]; exact ⟨hm, hn, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := MulAction.mem_orbit_iff.1 hmem
  have hpos := lt_length_of_mem_repsOf (List.getElem_mem hl)
  have hα : w • orbitCertRoot τ (pairTable τ)[r].1 = τ.rootCertificate.root m := by
    rw [h1, orbitCertRoot_certWitnessPos hpos.1]
    exact (Prod.ext_iff.1 hw).1
  have hβ : w • orbitCertRoot τ (pairTable τ)[r].2.1 = τ.rootCertificate.root n := by
    rw [h2', orbitCertRoot_certWitnessPos hpos.2]
    exact (Prod.ext_iff.1 hw).2
  have hc := commutatorElement_pinnedX_of_two_eq_zero h2 (List.getElem_mem hrow) w hα hβ x y
  have hone : ((pairTable τ)[r].2.2.2.map fun f => pinnedX τ R (w • orbitCertRoot τ f.2.2.1)
      ((f.2.2.2 : R) * x ^ f.1 * y ^ f.2.1)).prod = 1 := by
    refine List.prod_eq_one fun g hg => ?_
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hg
    have hev : f.2.2.2 % 2 = 0 := by
      have := he
      simp only [evenRow, List.getD_eq_getElem _ _ hrow, List.all_eq_true, beq_iff_eq] at this
      exact this f hf
    obtain ⟨k, hk⟩ : ∃ k : ℤ, f.2.2.2 = 2 * k := ⟨f.2.2.2 / 2, by omega⟩
    have h0 : ((f.2.2.2 : ℤ) : R) = 0 := by
      rw [hk]; push_cast; rw [h2, zero_mul]
    rw [h0, zero_mul, zero_mul, pinnedX_zero]
  rw [hone] at hc
  exact commutatorElement_eq_one_iff_commute.1 hc

@[expose] def szRootsA : List (Fin Tag.F4.rank → ℤ) :=
  ReeTag.largeReeBlockTable 1 ++ ReeTag.largeReeBlockTable 5

@[expose] def szRootsB : List (Fin Tag.F4.rank → ℤ) :=
  ReeTag.largeReeBlockTable 11 ++ ReeTag.largeReeBlockTable 14

@[expose] def szRcCheck : Bool :=
  (List.range Tag.F4.rootCertificate.roots.length).all fun m =>
    (List.range Tag.F4.rootCertificate.roots.length).all fun n =>
      !(decide (Tag.F4.rootCertificate.root m ∈ szRootsA)) ||
        !(decide (Tag.F4.rootCertificate.root n ∈ szRootsB)) ||
          (Nat.blt (pairLab Tag.F4 m n) (repsOf Tag.F4).length &&
            evenRow Tag.F4 (pairLab Tag.F4 m n))

theorem szRcCheck_true : szRcCheck = true := by decide +kernel

theorem szRootsA_pos : ∀ γ ∈ szRootsA, ∃ m < Tag.F4.rootCertificate.roots.length,
    Tag.F4.rootCertificate.root m = γ := by decide +kernel

theorem szRootsB_pos : ∀ γ ∈ szRootsB, ∃ m < Tag.F4.rootCertificate.roots.length,
    Tag.F4.rootCertificate.root m = γ := by decide +kernel

theorem commute_pinnedX_szRoots
    {R : Type*} [CommRing R] (h2 : (2 : R) = 0) {γ δ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ szRootsA) (hδ : δ ∈ szRootsB) (x y : R) :
    Commute (pinnedX Tag.F4 R γ x) (pinnedX Tag.F4 R δ y) := by
  obtain ⟨m, hm, rfl⟩ := szRootsA_pos γ hγ
  obtain ⟨n, hn, rfl⟩ := szRootsB_pos δ hδ
  have h := szRcCheck_true
  simp only [szRcCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, Nat.blt_eq] at h
  rcases h m hm n hn with (h | h) | h
  · exact absurd hγ h
  · exact absurd hδ h
  · exact commute_pinnedX_of_label h2 hm hn h.1 h.2 x y

end CFSG.RankThree.PartOne.SEITZ7

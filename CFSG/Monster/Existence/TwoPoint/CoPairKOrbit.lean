module

public import CFSG.Monster.Existence.TwoPoint.CoPairOrbit
public import CFSG.Certificates.Kernel.CoPairSound

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.CoPair

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.VisCert CFSG.Monster.VisQuot
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge
  CFSG.Monster.Existence.CoPair.Native CFSG.KC.CoPair

attribute [local instance] kvLeft

theorem mem_orbit_of_reach2
    {seed x : ℕ}
    (h : Reach2 (actLetters xWordN) (actLetters yWordN) seed x) :
    dec x ∈ MulAction.orbit (Kstab v0) (dec seed) := by
  induction h with
  | base => exact MulAction.mem_orbit_self _
  | left _ ih =>
    rw [← genXY_zero, dec_genXY_zero]
    exact MulAction.mem_orbit_of_mem_orbit _ ih
  | right _ ih =>
    rw [← genXY_one, dec_genXY_one]
    exact MulAction.mem_orbit_of_mem_orbit _ ih

theorem ncard_orbit_of_orbOK
    {seed N : ℕ} {D : OrbData}
    (h : orbOK xWordN yWordN seed N D = true) :
    (MulAction.orbit (Kstab v0) (dec seed)).ncard = N := by
  obtain ⟨hs, hseed, hmono, hX, hY, hreach⟩ := orbOK_sound h
  let F : Finset ℕ := (Finset.range N).image (f24 D.P)
  have hmem : ∀ x, x ∈ F ↔ ∃ i < N, f24 D.P i = x := by simp [F]
  have hFlt : ∀ x ∈ F, x < 2 ^ 24 := fun x hx => by
    obtain ⟨i, -, rfl⟩ := (hmem x).1 hx
    exact f24_lt _ _
  have hFfin : (dec '' (F : Set ℕ)).Finite := F.finite_toSet.image dec
  have hseedF : seed ∈ (F : Set ℕ) := (hmem seed).2 ⟨D.s, hs, hseed⟩
  have hXF : ∀ v ∈ (F : Set ℕ), genXY 0 v ∈ (F : Set ℕ) := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := (hmem v).1 hv
    obtain ⟨j, hj, hji⟩ := hX i hi
    exact (hmem _).2 ⟨j, hj, by rw [hji, genXY_zero]⟩
  have hYF : ∀ v ∈ (F : Set ℕ), genXY 1 v ∈ (F : Set ℕ) := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := (hmem v).1 hv
    obtain ⟨j, hj, hji⟩ := hY i hi
    exact (hmem _).2 ⟨j, hj, by rw [hji, genXY_one]⟩
  have horb : MulAction.orbit (Kstab v0) (dec seed) = dec '' (F : Set ℕ) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      have hg : g ∈ Subgroup.closure ({xK⁻¹, yK⁻¹} : Set (Kstab v0)) := by
        rw [closure_inv_eq_top]
        trivial
      refine VisCert.orbit_closure_subset (S := ({xK⁻¹, yK⁻¹} : Set (Kstab v0))) hFfin ?_
        (x := dec seed) ⟨seed, hseedF, rfl⟩ ⟨⟨g, hg⟩, rfl⟩
      rintro s (rfl | rfl) _ ⟨v, hv, rfl⟩
      · exact ⟨genXY 0 v, hXF v hv, dec_genXY_zero v⟩
      · exact ⟨genXY 1 v, hYF v hv, dec_genXY_one v⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (hmem v).1 hv
      exact mem_orbit_of_reach2 (hreach i hi)
  have hinjP : Set.InjOn (f24 D.P) (Finset.range N : Set ℕ) := fun i hi j hj hij => by
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd hij (Nat.ne_of_lt (hmono i j h' hj))
    · exact absurd hij (Nat.ne_of_gt (hmono j i h' hi))
  have hcard : F.card = N := by
    rw [Finset.card_image_of_injOn hinjP, Finset.card_range]
  have hinj : Set.InjOn dec (F : Set ℕ) := fun a ha b hb hab =>
    dec_injective (hFlt a ha) (hFlt b hb) hab
  rw [horb, hinj.ncard_image, Set.ncard_coe_finset, hcard]

end CFSG.Monster.Existence.CoPair

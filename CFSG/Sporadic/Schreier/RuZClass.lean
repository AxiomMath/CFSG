module

public import CFSG.Sporadic.Schreier.RuInvClasses

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

abbrev ruTS (j : ℕ) : Set (Fin 4060) := finSet 4060 ruTreeSets[j]!

theorem ruTS_spec
    {j : ℕ} (hj : j < 593775) :
    PointList 4060 ruTreeSets[j]! ∧ ∃ g ∈ ruP, ruTS j = g • ruFixSet := by
  have h := translates_spec (H := ruP) rep_ruTreeGens ruTreeGens_mem (pointList_fixedList ruZA)
    ruTree_check.2.2.2.1 j (by rw [ruTree_check.2.1]; exact hj)
  rw [finSet_fixedList rep_ruZ] at h
  exact h

theorem ruTS_inj
    {j k : ℕ} (hj : j < 593775) (hk : k < 593775) (h : ruTS j = ruTS k) :
    j = k := by
  have hl := (ruTS_spec hj).1.eq_of_finSet_eq (ruTS_spec hk).1 h
  have hs := ruTree_check.2.1
  rw [getElem!_pos ruTreeSets j (by omega), getElem!_pos ruTreeSets k (by omega),
    ← Array.getElem_toList, ← Array.getElem_toList] at hl
  exact (ruTreeSets_nodup.getElem_inj_iff).1 hl

abbrev ruOrbFix : Set (Set (Fin 4060)) :=
  Set.range fun g : ruP => (g : Equiv.Perm (Fin 4060)) • ruFixSet

theorem ruOrbFix_eq_image : ruOrbFix = fixSet '' ruZP := by
  ext s
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, g.2, rfl⟩, fixSet_conj (g : Equiv.Perm (Fin 4060)) ruZ⟩
  · rintro ⟨t, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨g, hg⟩, (fixSet_conj g ruZ).symm⟩

theorem ruTS_injective :
    Function.Injective fun j : Fin 593775 => ruTS j :=
  fun i j h => Fin.ext (ruTS_inj i.2 j.2 h)

theorem ruTS_range_eq :
    Set.range (fun j : Fin 593775 => ruTS j) = ruOrbFix := by
  apply Set.eq_of_subset_of_ncard_le
  · rintro _ ⟨j, rfl⟩
    obtain ⟨-, g, hg, he⟩ := ruTS_spec j.2
    exact ⟨⟨g, hg⟩, he.symm⟩
  · rw [Set.ncard_range_of_injective ruTS_injective, Nat.card_fin, ruOrbFix_eq_image,
      ← ncard_ruZP]
    exact Set.ncard_image_le (Set.toFinite _)
  · exact Set.toFinite _

theorem exists_ruTS
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruZP) :
    ∃ j < 593775, ruTS j = fixSet t := by
  have : fixSet t ∈ ruOrbFix := by
    rw [ruOrbFix_eq_image]
    exact ⟨t, ht, rfl⟩
  rw [← ruTS_range_eq] at this
  obtain ⟨j, hj⟩ := this
  exact ⟨j, j.2, hj⟩

theorem fixSet_injOn :
    Set.InjOn fixSet ruZP := by
  apply Set.injOn_of_ncard_image_eq _ (Set.toFinite _)
  rw [← ruOrbFix_eq_image, ← ruTS_range_eq, Set.ncard_range_of_injective ruTS_injective,
    Nat.card_fin, ncard_ruZP]

@[expose] def ruZIdxP (t : Equiv.Perm (Fin 4060)) : ℕ := by
  classical
  exact if h : ∃ j < 593775, ruTS j = fixSet t then Classical.choose h else 0

theorem ruZIdxP_spec
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruZP) :
    ruZIdxP t < 593775 ∧ ruTS (ruZIdxP t) = fixSet t := by
  have h := exists_ruTS ht
  unfold ruZIdxP
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem ruZIdxP_eq
    {t : Equiv.Perm (Fin 4060)} (ht : t ∈ ruZP) {j : ℕ} (hj : j < 593775)
    (h : ruTS j = fixSet t) : ruZIdxP t = j :=
  ruTS_inj (ruZIdxP_spec ht).1 hj ((ruZIdxP_spec ht).2.trans h.symm)

end CFSG.Sporadic.RuSchreier

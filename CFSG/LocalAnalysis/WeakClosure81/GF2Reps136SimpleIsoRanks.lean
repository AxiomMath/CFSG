module

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoGraph

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

lemma w1369_ta_rk_eq_of_secIsoOn {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (h : SecIsoOn Λ A ⊥ B ⊥) : rk ↥A = rk ↥B := by
  obtain ⟨e, -⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn h
  unfold rk
  rw [Nat.card_congr e.toEquiv]

lemma w1369_ta_inf_eq_bot {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hA : w1369_ta_IsSimple Λ A) (hB : w1369_ta_IsSimple Λ B) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  rcases hA.2.2 (A ⊓ B) (stableUnder_inf hA.2.1 hB.2.1) inf_le_left with h | h
  · exact h
  · exfalso
    have hle : A ≤ B := by rw [← h]; exact inf_le_right
    rcases hB.2.2 A hA.2.1 hle with h' | h'
    · exact hA.1 h'
    · exact hne h'

lemma w1369_ta_rk_sup_three [Finite Q] {I : Fin 3 → Subgroup Q}
    (hspan : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), I j) = ⊥) :
    rk ↥(⊤ : Subgroup Q) = rk ↥(I 0) + rk ↥(I 1) + rk ↥(I 2) := by
  have h01 : I 0 ⊓ I 1 = ⊥ := by
    have hle : I 1 ≤ ⨆ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), I j :=
      le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
    exact le_bot_iff.mp ((inf_le_inf_left (I 0) hle).trans (le_of_eq (hind 0)))
  have h2 : (⨆ (j : Fin 3) (_ : j ≠ (2 : Fin 3)), I j) = I 0 ⊔ I 1 := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun j => iSup_le fun hj => ?_
      fin_cases j
      · exact le_sup_left
      · exact le_sup_right
      · exact absurd rfl hj
    · refine sup_le ?_ ?_
      · exact le_iSup_of_le 0 (le_iSup_of_le (by decide) le_rfl)
      · exact le_iSup_of_le 1 (le_iSup_of_le (by decide) le_rfl)
  have htop : (⊤ : Subgroup Q) = I 0 ⊔ I 1 ⊔ I 2 := by
    rw [← hspan]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · refine sup_le ?_ ?_
      · refine sup_le ?_ ?_
        · exact le_iSup (fun i : Fin 3 => I i) 0
        · exact le_iSup (fun i : Fin 3 => I i) 1
      · exact le_iSup (fun i : Fin 3 => I i) 2
  have h12 : (I 0 ⊔ I 1) ⊓ I 2 = ⊥ := by
    rw [inf_comm, ← h2]
    exact hind 2
  have hsup01 : rk ↥(I 0 ⊔ I 1) = rk ↥(I 0) + rk ↥(I 1) := by
    have h := rk_sup_add_rk_inf (I 0) (I 1)
    rw [h01, rk_bot, add_zero] at h
    exact h
  calc rk ↥(⊤ : Subgroup Q) = rk ↥(I 0 ⊔ I 1 ⊔ I 2) := by rw [htop]
    _ = rk ↥(I 0 ⊔ I 1) + rk ↥(I 2) := by
        have h := rk_sup_add_rk_inf (I 0 ⊔ I 1) (I 2)
        rw [h12, rk_bot, add_zero] at h
        exact h
    _ = rk ↥(I 0) + rk ↥(I 1) + rk ↥(I 2) := by rw [hsup01]


lemma w1369_ta_transitive_of_orbit_bound {α β G : Type*} [Group G] [MulAction G α]
    [Finite α] [Finite β] (w : α → β) (hw : Function.Injective w) {N m : ℕ}
    (hN : Nat.card β ≤ N) (hm : ∀ a : α, m ≤ (MulAction.orbit G a).ncard) (hNm : N < 2 * m) :
    ∀ a b : α, ∃ g : G, g • a = b := by
  intro a b
  by_contra hcon
  have hb : b ∉ MulAction.orbit G a := by
    intro hb
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hb
    exact hcon ⟨g, hg⟩
  have hdisj : Disjoint (MulAction.orbit G a) (MulAction.orbit G b) := by
    rw [Set.disjoint_left]
    intro x hxa hxb
    have h1 : MulAction.orbit G x = MulAction.orbit G a := MulAction.orbit_eq_iff.mpr hxa
    have h2 : MulAction.orbit G x = MulAction.orbit G b := MulAction.orbit_eq_iff.mpr hxb
    have hmem : b ∈ MulAction.orbit G a := by
      rw [← h1]
      rw [h2]
      exact MulAction.mem_orbit_self b
    exact hb hmem
  have hcard : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard =
      (MulAction.orbit G a).ncard + (MulAction.orbit G b).ncard :=
    Set.ncard_union_eq hdisj
  have hge : 2 * m ≤ (MulAction.orbit G a ∪ MulAction.orbit G b).ncard := by
    rw [hcard]
    have h1 := hm a
    have h2 := hm b
    omega
  have hle : (MulAction.orbit G a ∪ MulAction.orbit G b).ncard ≤ Nat.card β := by
    calc (MulAction.orbit G a ∪ MulAction.orbit G b).ncard
        = (w '' (MulAction.orbit G a ∪ MulAction.orbit G b)).ncard :=
          (Set.ncard_image_of_injective _ hw).symm
      _ ≤ (Set.univ : Set β).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card β := Set.ncard_univ β
  omega

lemma w1369_ta_top_not_simple {Λ : Subgroup (MulAut Q)} {k : ℕ} (hk2 : 2 ≤ k)
    {I : Fin k → Subgroup Q} (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    ¬ w1369_ta_IsSimple Λ (⊤ : Subgroup Q) := by
  haveI : NeZero k := ⟨by omega⟩
  intro htop
  rcases htop.2.2 (I 0) (hstab 0) le_top with h0 | h0
  · exact (hsimple 0).1 h0
  · have h2k : 1 < Fintype.card (Fin k) := by rw [Fintype.card_fin]; omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h2k 0
    have hIj : I j ≤ I 0 := by rw [h0]; exact le_top
    have h0j : I 0 ⊓ I j = ⊥ := by
      have hle : I j ≤ ⨆ (l : Fin k) (_ : l ≠ (0 : Fin k)), I l :=
        le_iSup_of_le j (le_iSup_of_le hj le_rfl)
      exact le_bot_iff.mp ((inf_le_inf_left (I 0) hle).trans (le_of_eq (hind 0)))
    have h1 : I j = ⊥ := by
      rw [inf_eq_right.mpr hIj] at h0j
      exact h0j
    exact (hsimple j).1 h1

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

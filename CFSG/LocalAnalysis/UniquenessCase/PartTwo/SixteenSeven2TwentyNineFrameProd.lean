module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c167_frame_odd_normal_le_center {F Z S : Type*} [Group F] [CommGroup Z] [Group S]
    (hS : ∀ K : Subgroup S, K.Normal → K = ⊥ ∨ K = ⊤) (hev : Even (Nat.card S))
    (e : F ≃* Z × S × S) {N : Subgroup F} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ Subgroup.center F := by
  intro n hn
  let π₁ : F →* S := (MonoidHom.fst S S).comp ((MonoidHom.snd Z (S × S)).comp e.toMonoidHom)
  let π₂ : F →* S := (MonoidHom.snd S S).comp ((MonoidHom.snd Z (S × S)).comp e.toMonoidHom)
  have hπ₁ : Function.Surjective π₁ := fun s => ⟨e.symm (1, s, 1), by simp [π₁]⟩
  have hπ₂ : Function.Surjective π₂ := fun s => ⟨e.symm (1, 1, s), by simp [π₂]⟩
  have hmap₁ : N.map π₁ = ⊥ := by
    rcases hS (N.map π₁) (hN.map π₁ hπ₁) with h | h
    · exact h
    · exfalso
      have hodd₁ : Odd (Nat.card (N.map π₁)) :=
        Odd.of_dvd_nat hodd (Subgroup.card_map_dvd N π₁)
      rw [h, Subgroup.card_top] at hodd₁
      exact (Nat.not_even_iff_odd.mpr hodd₁) hev
  have hmap₂ : N.map π₂ = ⊥ := by
    rcases hS (N.map π₂) (hN.map π₂ hπ₂) with h | h
    · exact h
    · exfalso
      have hodd₂ : Odd (Nat.card (N.map π₂)) :=
        Odd.of_dvd_nat hodd (Subgroup.card_map_dvd N π₂)
      rw [h, Subgroup.card_top] at hodd₂
      exact (Nat.not_even_iff_odd.mpr hodd₂) hev
  have hn₁ : π₁ n = 1 := by
    have hmem : π₁ n ∈ N.map π₁ := Subgroup.mem_map_of_mem π₁ hn
    rwa [hmap₁, Subgroup.mem_bot] at hmem
  have hn₂ : π₂ n = 1 := by
    have hmem : π₂ n ∈ N.map π₂ := Subgroup.mem_map_of_mem π₂ hn
    rwa [hmap₂, Subgroup.mem_bot] at hmem
  obtain ⟨z, hz⟩ : ∃ z : Z, e n = (z, 1, 1) := by
    refine ⟨(e n).1, ?_⟩
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simpa [π₁] using hn₁
    · simpa [π₂] using hn₂
  rw [Subgroup.mem_center_iff]
  intro g
  apply e.injective
  simp only [map_mul, hz]
  refine Prod.ext (mul_comm _ _) ?_
  show (e g).2 * 1 = 1 * (e g).2
  rw [mul_one, one_mul]

private lemma s16c167_frame_commutator_prod {Z S : Type*} [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) :
    commutator (Z × S × S) = (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
  rw [_root_.commutator_def]
  simp only [← Subgroup.top_prod_top]
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_prod_prod]
  simp only [show ⁅(⊤ : Subgroup Z), ⊤⁆ = ⊥ from commutator_eq_bot Z,
    show ⁅(⊤ : Subgroup S), ⊤⁆ = ⊤ from hperf.commutator_eq_top]

theorem s16c167_frame_center_sup_commutator {F Z S : Type*} [Group F] [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) (hS : ∀ s : S, (∀ t : S, s * t = t * s) → s = 1)
    (e : F ≃* Z × S × S) :
    Subgroup.center F ⊔ commutator F = ⊤ ∧ Subgroup.center F ⊓ commutator F = ⊥ := by
  have hcenterS : Subgroup.center S = ⊥ :=
    (Subgroup.eq_bot_iff_forall (Subgroup.center S)).mpr fun s hs =>
      hS s fun t => (Subgroup.mem_center_iff.mp hs t).symm
  have hcenter : (Subgroup.center F).map (e : F →* Z × S × S) =
      (⊤ : Subgroup Z).prod ((⊥ : Subgroup S).prod (⊥ : Subgroup S)) := by
    simp only [Subgroup.map_center_eq e, Subgroup.center_prod, Subgroup.center_eq_top, hcenterS]
  have hcomm : (commutator F).map (e : F →* Z × S × S) =
      (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : F →* Z × S × S) e.surjective]
    exact s16c167_frame_commutator_prod hperf
  constructor
  · refine Subgroup.map_injective (f := (e : F →* Z × S × S)) e.injective ?_
    rw [Subgroup.map_sup, hcenter, hcomm,
      Subgroup.map_top_of_surjective (e : F →* Z × S × S) e.surjective]
    ext x
    constructor
    · intro _; trivial
    · intro _
      rcases x with ⟨z, s, t⟩
      have h1 : (z, 1, 1) ∈ (⊤ : Subgroup Z).prod ((⊥ : Subgroup S).prod (⊥ : Subgroup S)) :=
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_top z,
          Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_bot.mpr rfl⟩⟩
      have h2 : (1, s, t) ∈ (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) :=
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl,
          Subgroup.mem_prod.mpr ⟨Subgroup.mem_top s, Subgroup.mem_top t⟩⟩
      have h := Subgroup.mul_mem_sup h1 h2
      simpa using h
  · refine Subgroup.map_injective (f := (e : F →* Z × S × S)) e.injective ?_
    rw [Subgroup.map_inf_eq (Subgroup.center F) (commutator F) (e : F →* Z × S × S) e.injective,
      hcenter, hcomm, Subgroup.map_bot]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      have hxA : x ∈ (⊤ : Subgroup Z).prod ((⊥ : Subgroup S).prod (⊥ : Subgroup S)) :=
        (Subgroup.mem_inf.mp hx).1
      have hxB : x ∈ (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) :=
        (Subgroup.mem_inf.mp hx).2
      have hx2 : x.2 ∈ (⊥ : Subgroup S).prod (⊥ : Subgroup S) := (Subgroup.mem_prod.mp hxA).2
      have hx1 : x.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hxB).1
      have hx2a : x.2.1 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx2).1
      have hx2b : x.2.2 = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx2).2
      exact Prod.ext hx1 (Prod.ext hx2a hx2b)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

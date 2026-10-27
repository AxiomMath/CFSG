module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.GM22.CaseA3

open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_of_commutator_eq {V L : Subgroup G} (hc : ⁅V, L⁆ = V)
    (hVN : V ≤ Subgroup.normalizer (L : Set G)) : V ≤ L := by
  rw [← hc]
  refine Subgroup.commutator_le.mpr fun v hv l hl => ?_
  have h1 : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hVN hv) l).mp hl
  have e : ⁅v, l⁆ = (v * l * v⁻¹) * l⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [e]
  exact L.mul_mem h1 (L.inv_mem hl)

theorem mem_L_iff_sign {N V L : Subgroup G} (φ : ↥N →* Equiv.Perm (Fin 5))
    (hφ : Function.Surjective φ) (hker : ∀ x : ↥N, φ x = 1 ↔ (x : G) ∈ V) (hLN : L ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (L : Set G)) (hVL : V ≤ L) (hO2 : oTwoUpper N = L)
    (hnle : ¬ L ≤ V) (x : ↥N) : (x : G) ∈ L ↔ Equiv.Perm.sign (φ x) = 1 := by
  have hfwd : ∀ x : ↥N, (x : G) ∈ L → Equiv.Perm.sign (φ x) = 1 := by
    intro x hx
    rw [← hO2] at hx
    have hle : oTwoUpper N ≤ ((Equiv.Perm.sign.comp φ).ker).map N.subtype := by
      refine oTwoUpper_le_of_pow_mem fun y hy => ⟨1, ?_⟩
      refine Subgroup.mem_map.mpr ⟨⟨y, hy⟩ ^ 2, ?_, by simp⟩
      show Equiv.Perm.sign (φ (⟨y, hy⟩ ^ 2)) = 1
      rw [map_pow, map_pow]
      exact Int.units_pow_two _
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp (hle hx)
    have : x' = x := Subtype.ext hxx'
    subst this
    simpa using hx'
  refine ⟨hfwd x, fun hx => ?_⟩
  let Y : Subgroup (Equiv.Perm (Fin 5)) := (L.subgroupOf N).map φ
  have hYA : Y ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨l, hl, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mpr (hfwd l (Subgroup.mem_subgroupOf.mp hl))
  have hYn : Y.Normal := ⟨by
    rintro _ ⟨l, hl, rfl⟩ σ
    obtain ⟨n, rfl⟩ := hφ σ
    refine ⟨n * l * n⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp (hnorm n.2) l).mp (Subgroup.mem_subgroupOf.mp hl)⟩
  have hY1 : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hnle
    intro l hl
    exact (hker ⟨l, hLN hl⟩).mp (hcon _ ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hYA' : alternatingGroup (Fin 5) ≤ Y := by
    have hN' : (Y.subgroupOf (alternatingGroup (Fin 5))).Normal := Subgroup.Normal.subgroupOf hYn _
    rcases hsimple.eq_bot_or_eq_top_of_normal (Y.subgroupOf (alternatingGroup (Fin 5))) with h0 | h1
    · exfalso
      obtain ⟨y, hy, hy1⟩ := hY1
      have : (⟨y, hYA hy⟩ : alternatingGroup (Fin 5)) ∈ Y.subgroupOf (alternatingGroup (Fin 5)) :=
        Subgroup.mem_subgroupOf.mpr hy
      rw [h0, Subgroup.mem_bot] at this
      exact hy1 (congrArg Subtype.val this)
    · intro a ha
      have : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ Y.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h1]
        trivial
      exact Subgroup.mem_subgroupOf.mp this
  have hxA : φ x ∈ Y := hYA' (Equiv.Perm.mem_alternatingGroup.mpr hx)
  obtain ⟨l, hl, hlx⟩ := hxA
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hV : ((l⁻¹ * x : ↥N) : G) ∈ V := (hker _).mp (by rw [map_mul, map_inv, hlx, inv_mul_cancel])
  have e : (x : G) = l * ((l⁻¹ * x : ↥N) : G) := by simp
  rw [e]
  exact L.mul_mem hlL (hVL hV)

end CFSG.Quasithin.H13.GM22.CaseA3

module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.Abel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k12_neg_sub_self {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (x : U) :
    -x - x = x := by
  have hneg2 : (-2 : ZMod 3) = 1 := by decide
  have h1 : -x - x = (-2 : ZMod 3) • x := by
    rw [sub_eq_add_neg, ← neg_one_smul (ZMod 3) x, ← add_smul]
    rfl
  rw [h1, hneg2, one_smul]

theorem ggQ2s08core_absIrred_of_irred {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (A : Subgroup (U ≃ₗ[ZMod 3] U)) (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hex : ∃ r ∈ A, GGLinRefl r)
    (hirr : ∀ S : Submodule (ZMod 3) U, (∀ a ∈ A, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤) :
    ZS.AbsIrred 3 A := by
  refine ⟨hirr, ?_⟩
  intro T hT
  obtain ⟨r, hrA, hrefl⟩ := hex
  obtain ⟨hr2, hrrank⟩ := hrefl
  have hne : ggLinMove r ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod 3) (ggLinMove r) = 0 := by
      rw [hbot, finrank_bot]
    rw [hrrank] at h0
    exact one_ne_zero h0
  obtain ⟨c, hc_mem, hc_ne⟩ := (Submodule.ne_bot_iff (ggLinMove r)).mp hne
  have hspan : ggLinMove r = Submodule.span (ZMod 3) {c} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrrank hc_mem hc_ne
  have hc_range : c ∈ LinearMap.range ((r : U →ₗ[ZMod 3] U) - LinearMap.id) := hc_mem
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hc_range
  have hv' : r v - v = c := by simpa using hv
  have hrv : r v = v + c := sub_eq_iff_eq_add'.mp hv'
  have hrr : r (r v) = v := by
    have h := congrArg (fun e : U ≃ₗ[ZMod 3] U => e v) hr2
    simpa using h
  have hrc : r c = -c := by
    have hcv : c = r v - v := hv'.symm
    rw [hcv, map_sub, hrr, hrv]
    abel
  have hTcomm : T (r c) = r (T c) := by
    have h := congrArg (fun f : U →ₗ[ZMod 3] U => f c) (hT r hrA)
    simpa [LinearMap.comp_apply] using h
  have hrTc : r (T c) = -T c := by
    calc r (T c) = T (r c) := hTcomm.symm
      _ = T (-c) := by rw [hrc]
      _ = -T c := by rw [map_neg]
  have hmem : T c ∈ ggLinMove r := by
    unfold ggLinMove
    refine LinearMap.mem_range.mpr ⟨T c, ?_⟩
    change r (T c) - T c = T c
    rw [hrTc]
    exact ggQ2s08k12_neg_sub_self (T c)
  obtain ⟨lam, hlam⟩ :=
    Submodule.mem_span_singleton.mp (show T c ∈ Submodule.span (ZMod 3) {c} by rwa [← hspan])
  let S : Submodule (ZMod 3) U := LinearMap.ker (T - lam • LinearMap.id)
  have hcS : c ∈ S := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hlam,
      sub_self]
  have hSne : S ≠ ⊥ := (Submodule.ne_bot_iff S).mpr ⟨c, hcS, hc_ne⟩
  have hinv : ∀ a ∈ A, ∀ u ∈ S, a u ∈ S := by
    intro a ha u hu
    have hu' : T u = lam • u := by
      have h := hu
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
      exact sub_eq_zero.mp h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hcomm := congrArg (fun f : U →ₗ[ZMod 3] U => f u) (hT a ha)
    have hcomm' : T (a u) = a (T u) := by simpa [LinearMap.comp_apply] using hcomm
    rw [hcomm', hu', map_smul, sub_self]
  have hS : S = ⊤ := by
    rcases hirr S hinv with h | h
    · exact absurd h hSne
    · exact h
  refine ⟨lam, ?_⟩
  ext u
  rw [LinearMap.smul_apply, LinearMap.id_apply]
  have hu : u ∈ S := by rw [hS]; exact Submodule.mem_top
  have h := hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  exact sub_eq_zero.mp h

end CFSG.StandardType

end

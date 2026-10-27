module

public import CFSG.Quasithin.AppendixH.H9.H93.A2Basic.A2Hom
public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

theorem A2vec_rankOne_check :
    ∀ ε : Fin 4 → ZMod 2, ε 3 = 0 → ∀ u f : Fin 4 → ZMod 2, u ≠ 0 → f ≠ 0 →
      (∀ a, A2vec ε a = a + (f ⬝ᵥ a) • u) →
      ε = Pi.single 0 1 ∨ ε = Pi.single 1 1 ∨ ε = Pi.single 2 1 := by
  decide +kernel

theorem A2vec_single_zero_rankOne : ∀ a : Fin 4 → ZMod 2,
    A2vec (Pi.single 0 1) a = a + (![1, 1, 0, 0] ⬝ᵥ a) • ![1, 1, 0, 0] := by
  decide +kernel

theorem A2vec_single_one_rankOne : ∀ a : Fin 4 → ZMod 2,
    A2vec (Pi.single 1 1) a = a + (![0, 0, 1, 1] ⬝ᵥ a) • ![0, 0, 1, 1] := by
  decide +kernel

theorem A2vec_single_two_rankOne : ∀ a : Fin 4 → ZMod 2,
    A2vec (Pi.single 2 1) a = a + (![1, 1, 1, 1] ⬝ᵥ a) • ![1, 1, 1, 1] := by
  decide +kernel

theorem a2Hom_pairVec_zero {ε : Fin 4 → ZMod 2} (h3 : ε 3 = 0) (a : Fin 4 → ZMod 2) :
    a2Hom (Multiplicative.ofAdd ε) (pairVec a 0) = pairVec (A2vec ε a) 0 := by
  rw [a2Hom_apply]
  simp [A2fst, A2snd, h3, A2vec_zero_vec]

theorem isTvElt_a2Hom_iff (ε : Fin 4 → ZMod 2) :
    IsTvElt (a2Hom (Multiplicative.ofAdd ε)) ↔
      ε = Pi.single 0 1 ∨ ε = Pi.single 1 1 ∨ ε = Pi.single 2 1 := by
  constructor
  · intro hT
    have hL := hT.1
    have h3 : ε 3 = 0 := (a2Hom_mem_Lg_iff ε).mp hL
    obtain ⟨u, f, hu, hf, hvec⟩ := (isTvElt_iff_vec hL).mp hT
    refine A2vec_rankOne_check ε h3 u f hu hf (fun a => ?_)
    have h := hvec a
    rw [a2Hom_pairVec_zero h3] at h
    exact (pairVec_inj.mp h).1
  · intro h
    have h3 : ε 3 = 0 := by
      rcases h with rfl | rfl | rfl <;> decide
    have hL : a2Hom (Multiplicative.ofAdd ε) ∈ Lg 4 := (a2Hom_mem_Lg_iff ε).mpr h3
    refine (isTvElt_iff_vec hL).mpr ?_
    rcases h with rfl | rfl | rfl
    · refine ⟨![1, 1, 0, 0], ![1, 1, 0, 0], by decide, by decide, fun a => ?_⟩
      rw [a2Hom_pairVec_zero h3, A2vec_single_zero_rankOne a]
    · refine ⟨![0, 0, 1, 1], ![0, 0, 1, 1], by decide, by decide, fun a => ?_⟩
      rw [a2Hom_pairVec_zero h3, A2vec_single_one_rankOne a]
    · refine ⟨![1, 1, 1, 1], ![1, 1, 1, 1], by decide, by decide, fun a => ?_⟩
      rw [a2Hom_pairVec_zero h3, A2vec_single_two_rankOne a]

end CFSG.ASVolI.ChH

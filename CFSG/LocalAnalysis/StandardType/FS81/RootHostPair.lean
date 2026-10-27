module

public import CFSG.LocalAnalysis.StandardType.FS81.RootHost
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

private def cubeSL : SL(3, ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by rw [Matrix.det_fin_three]; decide⟩

private theorem cubeSL_pow : cubeSL ^ 3 = 1 := by decide

private theorem cubeSL_ne_one : cubeSL ≠ 1 := by decide

theorem sl3Two_le_closure_cube :
    (⊤ : Subgroup SL(3, ZMod 2)) ≤ Subgroup.closure {A : SL(3, ZMod 2) | A ^ 3 = 1} := by
  have hs : IsSimpleGroup SL(3, ZMod 2) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  set S : Set SL(3, ZMod 2) := {A | A ^ 3 = 1} with hS
  have hN : (Subgroup.closure S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hmap : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨a, ha, rfl⟩
      show (g * a * g⁻¹) ^ 3 = 1
      rw [conj_pow, show a ^ 3 = 1 from ha, mul_one, mul_inv_cancel]
    exact hmap ⟨n, hn, rfl⟩
  haveI := hs
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure S) with h | h
  · exfalso
    have hc : cubeSL ∈ Subgroup.closure S := Subgroup.subset_closure cubeSL_pow
    rw [h, Subgroup.mem_bot] at hc
    exact cubeSL_ne_one hc
  · rw [h]

theorem le_of_rootHost_of_pair {G : Type} [Group G] {x : G} {L : Subgroup G}
    (h : RootHost x L) {W U V : Subgroup G} (hp : LinearBlockStandardPair (ZMod 2) W U V)
    (hU : U ≤ Subgroup.centralizer ({x} : Set G))
    (hV : V ≤ Subgroup.centralizer ({x} : Set G)) : U ≤ L ∧ V ≤ L := by
  have hWsup : W = U ⊔ V := CFSG.StandardType.linearBlockStandardPair_eq_sup hp
  obtain ⟨θ, c, hrange, -, -⟩ := hp
  have hWC : W ≤ Subgroup.centralizer ({x} : Set G) := hWsup ▸ sup_le hU hV
  have hperf : ⁅W, W⁆ = W := by
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (K := ZMod 2) (n := 3)
      le_rfl
  have hgen : W ≤ Subgroup.closure {y : G | y ∈ W ∧ y ^ 3 = 1} := by
    rw [← hrange, MonoidHom.range_eq_map]
    refine le_trans (Subgroup.map_mono sl3Two_le_closure_cube) ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨⟨A, Subgroup.mem_top A, rfl⟩, by rw [← map_pow, show A ^ 3 = 1 from hA, map_one]⟩
  have hWL : W ≤ L := h.le_of_perfect hWC hperf hgen
  exact ⟨le_trans le_sup_left (hWsup ▸ hWL), le_trans le_sup_right (hWsup ▸ hWL)⟩

end CFSG.StandardType.FrameRoute.FS81

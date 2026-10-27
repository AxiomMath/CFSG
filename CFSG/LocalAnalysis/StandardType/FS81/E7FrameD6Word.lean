module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeCentralizer

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
open CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.RankThree.PartOne.KA5L
open scoped MatrixGroups

@[expose] def d6Word : List (Fin (Tag.rank .E7)) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 1, 3, 2, 0]

theorem d6Word_smul :
    (coxeterSystem .E7).wordProd d6Word • (Pi.single 1 1 : Fin (Tag.rank .E7) → ℤ) = mu ∧
      (coxeterSystem .E7).wordProd d6Word • (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 1 1 ∧
      (coxeterSystem .E7).wordProd d6Word • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 6 1 ∧
      (coxeterSystem .E7).wordProd d6Word • (Pi.single 6 1 : Fin (Tag.rank .E7) → ℤ) =
        Pi.single 5 1 := by
  simp only [d6Word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem exists_conj_mem_jn_zero_of_commute {x : ModGL .E7 (ZMod 2)} (hx : x ∈ L7)
    (h1 : ∀ a ∈ Jn 1, x * a = a * x) (h2 : ∀ a ∈ Jn 2, x * a = a * x)
    (h5 : ∀ a ∈ Jn 5, x * a = a * x) (h6 : ∀ a ∈ Jn 6, x * a = a * x) :
    ∃ n ∈ L7, n * x * n⁻¹ ∈ Jn 0 := by
  obtain ⟨hw1, hw2, hw5, hw6⟩ := d6Word_smul
  set n : ModGL .E7 (ZMod 2) := (wordRepE7 (ZMod 2) d6Word : ModGL .E7 (ZMod 2)) with hn
  have hnL : n ∈ L7 := (wordRepE7 (ZMod 2) d6Word).2
  have hcomm : ∀ {X : Subgroup (ModGL .E7 (ZMod 2))}, (∀ a ∈ X, x * a = a * x) →
      ∀ y ∈ X.map (MulAut.conj n).toMonoidHom,
        n * x * n⁻¹ * y = y * (n * x * n⁻¹) := by
    rintro X hX _ ⟨a, ha, rfl⟩
    have hax : x * a = a * x := hX a ha
    have h := congrArg (MulAut.conj n) hax
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hJ : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, IsRoot .E7 γ →
      (J γ).map (MulAut.conj n).toMonoidHom =
        J ((coxeterSystem .E7).wordProd d6Word • γ) :=
    fun hγ => by rw [hn]; exact map_conj_wordRepE7_J d6Word hγ
  have hJ1 : (Jn 2).map (MulAut.conj n).toMonoidHom = Jn 1 := by
    have h := hJ (isRoot_single .E7 (2 : Fin (Tag.rank .E7)))
    rw [hw2] at h
    exact h
  have hJ5 : (Jn 6).map (MulAut.conj n).toMonoidHom = Jn 5 := by
    have h := hJ (isRoot_single .E7 (6 : Fin (Tag.rank .E7)))
    rw [hw6] at h
    exact h
  have hJ6 : (Jn 5).map (MulAut.conj n).toMonoidHom = Jn 6 := by
    have h := hJ (isRoot_single .E7 (5 : Fin (Tag.rank .E7)))
    rw [hw5] at h
    exact h
  have hJmu : (Jn 1).map (MulAut.conj n).toMonoidHom = J mu := by
    have h := hJ (isRoot_single .E7 (1 : Fin (Tag.rank .E7)))
    rw [hw1] at h
    exact h
  refine ⟨n, hnL, mem_jn_zero_of_commute ?_ ?_ ?_ ?_ ?_⟩
  · exact L7.mul_mem (L7.mul_mem hnL hx) (L7.inv_mem hnL)
  · intro y hy
    rw [← hJ1] at hy
    exact hcomm h2 y hy
  · intro y hy
    rw [← hJ5] at hy
    exact hcomm h6 y hy
  · intro y hy
    rw [← hJ6] at hy
    exact hcomm h5 y hy
  · intro y hy
    rw [← hJmu] at hy
    exact hcomm h1 y hy

end CFSG.StandardType.FrameRoute.FS81.E7Frame

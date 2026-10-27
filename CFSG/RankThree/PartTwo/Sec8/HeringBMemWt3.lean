module

public import CFSG.RankThree.PartTwo.Sec8.HeringBMemIrred

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open Subgroup CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec8.Item812Res12
  CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

@[expose] def sgnPat : Fin 4 → (Fin 3 → ZMod 3) :=
  ![![1, 1, 1], ![2, 2, 1], ![1, 2, 2], ![2, 1, 2]]

@[expose] def gAct (j : Fin 4) (w : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  sgnPat j * rotV (sgnPat j * w)

@[expose] def rotInv (w : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  ![w 1, w 2, w 0]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem wt3_checks :
    (∀ j w, sgnPat j * (sgnPat j * w) = w) ∧
    (∀ x : Fin 3 → ZMod 3, x 0 ≠ 0 → x 1 ≠ 0 → x 2 ≠ 0 → ∃ j, gAct j x = x) ∧
    (∀ j, gAct j (Pi.single 0 1) ≠ Pi.single 0 1) ∧
    (∀ w, rotV (rotInv w) = w) ∧ (∀ w, rotInv (rotV w) = w) ∧
    (∀ w, id w = sgnPat 0 * w) ∧ (∀ w, sgnV w = sgnPat 1 * w) ∧
    (∀ w, rotV (sgnV (rotInv w)) = sgnPat 2 * w) ∧
    (∀ w, rotV (rotV (sgnV (rotInv (rotInv w)))) = sgnPat 3 * w) := by
  decide +kernel


def Act (h : H6) (φ : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)) : Prop :=
  ∀ w, h * vecElt zH w * h⁻¹ = vecElt zH (φ w)

theorem Act.one : Act 1 id := fun w => by simp

theorem Act.mul {h₁ h₂ : H6} {φ₁ φ₂ : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)} (a₁ : Act h₁ φ₁)
    (a₂ : Act h₂ φ₂) : Act (h₁ * h₂) (fun w => φ₁ (φ₂ w)) := fun w => by
  have e : h₁ * h₂ * vecElt zH w * (h₁ * h₂)⁻¹ = h₁ * (h₂ * vecElt zH w * h₂⁻¹) * h₁⁻¹ := by
    group
  rw [e, a₂ w, a₁]

theorem Act.inv {h : H6} {φ ψ : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)} (a : Act h φ)
    (hψ : ∀ w, φ (ψ w) = w) : Act h⁻¹ ψ := fun w => by
  have e := a (ψ w)
  rw [hψ] at e
  rw [inv_inv, ← e]
  group

theorem Act.congr {h : H6} {φ ψ : (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3)} (a : Act h φ)
    (hφψ : ∀ w, φ w = ψ w) : Act h ψ := fun w => by
  rw [a w, hφψ]

theorem act_t : Act CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH rotV := fun w => conj_vecElt wreathFacts_zH w

theorem act_s : Act sH6 sgnV := sH6_conj

noncomputable def dEl : Fin 4 → H6 :=
  ![1, sH6, Sec4.Item434SmallTwoIII.tH * sH6 * Sec4.Item434SmallTwoIII.tH⁻¹, Sec4.Item434SmallTwoIII.tH * Sec4.Item434SmallTwoIII.tH * sH6 * (Sec4.Item434SmallTwoIII.tH * Sec4.Item434SmallTwoIII.tH)⁻¹]

theorem act_d (j : Fin 4) : Act (dEl j) (fun w => sgnPat j * w) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := wt3_checks
  fin_cases j
  · exact Act.one.congr c6
  · exact act_s.congr c7
  · have a := (act_t.mul act_s).mul (act_t.inv c4)
    exact a.congr c8
  · have a := ((act_t.mul act_t).mul act_s).mul ((act_t.mul act_t).inv
      (ψ := fun w => rotInv (rotInv w)) (fun w => by simp only [c4]))
    exact a.congr c9

theorem dEl_mem_normalizer (j : Fin 4) : dEl j ∈ Subgroup.normalizer (baseA zH : Set H6) := by
  have hf := wreathFacts_zH
  have htN : CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ∈ Subgroup.normalizer (baseA zH : Set H6) := t_mem_normalizer hf
  have hsN : sH6 ∈ Subgroup.normalizer (baseA zH : Set H6) :=
    mem_normalizer_baseA_of_sgn hf sH6_conj
  fin_cases j
  · exact Subgroup.one_mem _
  · exact hsN
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hsN) (Subgroup.inv_mem _ htN)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htN htN) hsN)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ htN htN))

theorem exists_g_wt3 {x : Fin 3 → ZMod 3} (h0 : x 0 ≠ 0) (h1 : x 1 ≠ 0) (h2 : x 2 ≠ 0) :
    ∃ g ∈ Subgroup.normalizer (baseA zH : Set H6), g * vecElt zH x = vecElt zH x * g ∧
      g ^ 3 = 1 ∧ ∃ e ∈ baseA zH, g * e * g⁻¹ ≠ e := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := wt3_checks
  have hf := wreathFacts_zH
  obtain ⟨j, hj⟩ := c2 x h0 h1 h2
  have hdinv : Act (dEl j)⁻¹ (fun w => sgnPat j * w) := (act_d j).inv (fun w => c1 j w)
  have hg : Act (dEl j * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (dEl j)⁻¹) (gAct j) := ((act_d j).mul act_t).mul hdinv
  refine ⟨dEl j * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (dEl j)⁻¹, ?_, ?_, ?_, vecElt zH (Pi.single 0 1),
    vecElt_mem_baseA hf _, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (dEl_mem_normalizer j) (t_mem_normalizer hf))
      (Subgroup.inv_mem _ (dEl_mem_normalizer j))
  · have e1 : dEl j * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (dEl j)⁻¹ * vecElt zH x * (dEl j * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH * (dEl j)⁻¹)⁻¹ =
        vecElt zH x := by
      rw [hg x, hj]
    exact mul_inv_eq_iff_eq_mul.mp e1
  · have h := map_pow (MulAut.conj (dEl j)) CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH 3
    rw [hf.pow_t, map_one, MulAut.conj_apply] at h
    exact h.symm
  · intro hcon
    rw [hg] at hcon
    exact c3 j (vecElt_injective hf hcon)

end CFSG.RankThree.PartTwo.Sec8.HeringBMem

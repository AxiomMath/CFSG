module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR33Aux2

public section

namespace CFSG.StandardType.ZS

open Subgroup

attribute [-instance] Nat.fact_prime_three

theorem owR33_not_absIrred {W : Fin 3 → ZMod 3} (E : Fin 3 → ZMod 3) (hE : E ≠ 0)
    (hEtop : ¬ Submodule.span (ZMod 3) {E} = ⊤)
    (hinv : ∀ a : Fin 3 → ZMod 3, (∑ k, W k * (a k * a k)) = 1 →
      ∃ c : ZMod 3, owR33_form W a E = c • E) :
    ¬ AbsIrred 3 (closure (ClassRefl 3 (owR33_Qw 3 3 W) 1)) := by
  intro hai
  let L : Submodule (ZMod 3) (Fin 3 → ZMod 3) := Submodule.span (ZMod 3) {E}
  have hEL : E ∈ L := Submodule.subset_span (by simp)
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hEL
    exact hE hEL
  have hP : ∀ g ∈ closure (ClassRefl 3 (owR33_Qw 3 3 W) 1), ∀ r ∈ L, g r ∈ L ∧ g⁻¹ r ∈ L := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      intro r hr
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht.1.1
      rw [Submodule.mem_span_singleton] at hr
      obtain ⟨d, hd⟩ := hr
      have htE : t E ∈ L := by
        rw [show owR33_Qw 3 3 W = QuadraticMap.weightedSumSquares (ZMod 3) W from rfl] at ht
        rw [wit_coord_classRefl_iff (by norm_num : Nat.Prime 3) (by norm_num : (3:ℕ) ≠ 2) W 1
          (by decide +kernel)] at ht
        obtain ⟨a, ha, hta⟩ := ht
        obtain ⟨c, hc⟩ := hinv a ha
        have : t E = c • E := by
          rw [hta E, ← hc]
          simp [owR33_form, owR33_alphaVal, ZMod.inv_one]
        rw [this]
        exact L.smul_mem c hEL
      refine ⟨?_, ?_⟩
      · rw [← hd, map_smul]; exact L.smul_mem d htE
      · rw [htinv, ← hd, map_smul]; exact L.smul_mem d htE
    | one => intro r hr; exact ⟨by simpa using hr, by simpa using hr⟩
    | mul x y hx hy ihx ihy =>
      intro r hr
      refine ⟨?_, ?_⟩
      · show x (y r) ∈ L; exact (ihx (y r) (ihy r hr).1).1
      · rw [mul_inv_rev]; show y⁻¹ (x⁻¹ r) ∈ L; exact (ihy (x⁻¹ r) (ihx r hr).2).2
    | inv x hx ih =>
      intro r hr
      obtain ⟨h1, h2⟩ := ih r hr
      exact ⟨h2, by simpa only [inv_inv] using h1⟩
  have hL := hai.1 L (fun g hg r hr => (hP g hg r hr).1)
  rcases hL with h | h
  · exact hLne h
  · exact hEtop h

theorem owR33_span_ne_top {i j : Fin 3} (hij : i ≠ j) :
    ¬ Submodule.span (ZMod 3) {(fun k : Fin 3 => if k = i then (1 : ZMod 3) else 0)} = ⊤ := by
  intro h
  have hmem : (fun k : Fin 3 => if k = j then (1 : ZMod 3) else 0)
      ∈ Submodule.span (ZMod 3) {(fun k : Fin 3 => if k = i then (1 : ZMod 3) else 0)} := by
    rw [h]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have := congrFun hc j
  simp [hij.symm] at this
  exact absurd this (by decide +kernel : (0 : ZMod 3) ≠ 1)

theorem owR33_E111_ne_top : ¬ Submodule.span (ZMod 3) {owR33_E111} = ⊤ := by
  have h : owR33_E111 = (fun k : Fin 3 => if k = 0 then (1 : ZMod 3) else 0) := by
    funext k; fin_cases k <;> simp [owR33_E111]
  rw [h]; exact owR33_span_ne_top (by decide : (0 : Fin 3) ≠ 1)

theorem owR33_E122_ne_top : ¬ Submodule.span (ZMod 3) {owR33_E122} = ⊤ := by
  have h : owR33_E122 = (fun k : Fin 3 => if k = 0 then (1 : ZMod 3) else 0) := by
    funext k; fin_cases k <;> simp [owR33_E122]
  rw [h]; exact owR33_span_ne_top (by decide : (0 : Fin 3) ≠ 1)

theorem owR33_E212_ne_top : ¬ Submodule.span (ZMod 3) {owR33_E212} = ⊤ := by
  have h : owR33_E212 = (fun k : Fin 3 => if k = 1 then (1 : ZMod 3) else 0) := by
    funext k; fin_cases k <;> simp [owR33_E212]
  rw [h]; exact owR33_span_ne_top (by decide : (1 : Fin 3) ≠ 0)

theorem owR33_E221_ne_top : ¬ Submodule.span (ZMod 3) {owR33_E221} = ⊤ := by
  have h : owR33_E221 = (fun k : Fin 3 => if k = 2 then (1 : ZMod 3) else 0) := by
    funext k; fin_cases k <;> simp [owR33_E221]
  rw [h]; exact owR33_span_ne_top (by decide : (2 : Fin 3) ≠ 0)

theorem owR33_red111_absurd
    (hai : AbsIrred 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W111) 1))) : False :=
  owR33_not_absIrred owR33_E111 owR33_red111.1 owR33_E111_ne_top owR33_red111.2 hai

theorem owR33_red122_absurd
    (hai : AbsIrred 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W122) 1))) : False :=
  owR33_not_absIrred owR33_E122 owR33_red122.1 owR33_E122_ne_top owR33_red122.2 hai

theorem owR33_red212_absurd
    (hai : AbsIrred 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W212) 1))) : False :=
  owR33_not_absIrred owR33_E212 owR33_red212.1 owR33_E212_ne_top owR33_red212.2 hai

theorem owR33_red221_absurd
    (hai : AbsIrred 3 (closure (ClassRefl 3 (owR33_Qw 3 3 owR33_W221) 1))) : False :=
  owR33_not_absIrred owR33_E221 owR33_red221.1 owR33_E221_ne_top owR33_red221.2 hai

end CFSG.StandardType.ZS

end

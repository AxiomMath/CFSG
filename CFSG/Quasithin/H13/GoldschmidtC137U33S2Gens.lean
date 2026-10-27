module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2R
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2ACertData
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Rk

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem S_le_of_three (H : Subgroup Gam)
    (hl : ∀ x ∈ [wd [0], wd [2], wd [1, 0, 2, 0, 1]], x ∈ H) : sSubG ≤ H := by
  intro s hs
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hs
  obtain ⟨hw, hlt⟩ := sWords_spec i hi
  have hcodes : ([wd [0], wd [2], wd [1, 0, 2, 0, 1]].map fun x => matCode x.1) = sGens := by
    simp only [List.map_cons, List.map_nil, matCode_wd (by decide : ∀ j ∈ [0], j < 4),
      matCode_wd (by decide : ∀ j ∈ [2], j < 4),
      matCode_wd (by decide : ∀ j ∈ [1, 0, 2, 0, 1], j < 4)]
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ (congrArg₂ _ ?_ rfl))
    all_goals decide +kernel
  have hlen : ∀ j ∈ sWords.getD i [],
      j < ([wd [0], wd [2], wd [1, 0, 2, 0, 1]] : List Gam).length :=
    fun j hj => by simpa using hlt j hj
  have : sEltG i = gprod [wd [0], wd [2], wd [1, 0, 2, 0, 1]] (sWords.getD i []) :=
    eq_of_code (by rw [matCode_gprod _ _ hlen, hcodes, matCode_sEltG hi]; exact hw.symm)
  rw [this]
  exact gprod_mem hl _

theorem top_of_gens (H : Subgroup Gam) (gl : List Gam) (hgl : ∀ x ∈ gl, x ∈ H)
    (wT wX wW wb : List ℕ) (steps : List (ℕ × ℕ × ℕ))
    (hlen : ∀ j ∈ wT ++ wX ++ wW ++ wb, j < gl.length)
    (hT : gcode (gl.map fun x => matCode x.1) wT = matT01)
    (hX : gcode (gl.map fun x => matCode x.1) wX = matX)
    (hW : gcode (gl.map fun x => matCode x.1) wW = matW)
    (hb : gcode (gl.map fun x => matCode x.1) wb = bCode)
    (hch : chainCovers (gl.map fun x => matCode x.1) steps omegaL = true) : H = ⊤ := by
  have hl : ∀ j ∈ wT, j < gl.length := fun j hj => hlen j (by simp [hj])
  have hl' : ∀ j ∈ wX, j < gl.length := fun j hj => hlen j (by simp [hj])
  have hl'' : ∀ j ∈ wW, j < gl.length := fun j hj => hlen j (by simp [hj])
  have hl''' : ∀ j ∈ wb, j < gl.length := fun j hj => hlen j (by simp [hj])
  have hS : sSubG ≤ H := by
    refine S_le_of_three H ?_
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have : wd [0] = gprod gl wT :=
        eq_of_code (by rw [matCode_gprod gl wT hl, hT, matCode_wd (by decide)]; decide +kernel)
      rw [this]
      exact gprod_mem hgl _
    · have : wd [2] = gprod gl wX :=
        eq_of_code (by rw [matCode_gprod gl wX hl', hX, matCode_wd (by decide)]; decide +kernel)
      rw [this]
      exact gprod_mem hgl _
    · have : wd [1, 0, 2, 0, 1] = gprod gl wW :=
        eq_of_code (by rw [matCode_gprod gl wW hl'', hW, matCode_wd (by decide)]; decide +kernel)
      rw [this]
      exact gprod_mem hgl _
  have hbH : b₀ ∈ H := by
    have : b₀ = gprod gl wb := eq_of_code (by rw [matCode_gprod gl wb hl''', hb, matCode_b₀])
    rw [this]
    exact gprod_mem hgl _
  exact eq_top_of_cert H hS hbH (chainCovers_sound H gl hgl steps omegaL hch)

@[expose] def cG : Gam := wd acw

theorem cG_mem : cG ∈ g2Derived (ZMod 2) := by
  have h : acw = [3, 2, 3, 2] ++ [0, 1, 0, 1] ++ [3, 2, 3, 2] ++ [0, 1, 0, 1] ++ [3, 2, 3, 2] :=
    by decide
  rw [cG, h, wd_append, wd_append, wd_append, wd_append]
  exact mul_mem (mul_mem (mul_mem (mul_mem (wd_mem_derived 3 2) (wd_mem_derived 0 1))
    (wd_mem_derived 3 2)) (wd_mem_derived 0 1)) (wd_mem_derived 3 2)

theorem acw_lt : ∀ j ∈ acw, j < 4 := by
  decide

theorem matCode_cG_conj (i : ℕ) (hi : i < 64) :
    matCode (cG * sEltG i * cG⁻¹).1 = mmul (mmul (wcode acw) (sM i)) (wcode acw.reverse) := by
  have hr : ∀ j ∈ acw.reverse, j < 4 := fun j hj => acw_lt j (List.mem_reverse.1 hj)
  rw [show cG⁻¹ = wd acw.reverse from (wd_reverse acw).symm]
  simp only [matCode_mulG, cG, matCode_wd acw_lt, matCode_wd hr, matCode_sEltG hi]

theorem A_sup_conj_eq_top : Asub ⊔ Asub.map (MulAut.conj cG).toMonoidHom = ⊤ := by
  set H := Asub ⊔ Asub.map (MulAut.conj cG).toMonoidHom with hH
  let gl : List Gam := [sEltG 2, sEltG 4, sEltG 8, cG * sEltG 2 * cG⁻¹, cG * sEltG 4 * cG⁻¹,
    cG * sEltG 8 * cG⁻¹]
  have hA : ∀ i ∈ Alist, sEltG i ∈ H := fun i hi => Subgroup.mem_sup_left ⟨i, hi, rfl⟩
  have hAc : ∀ i ∈ Alist, cG * sEltG i * cG⁻¹ ∈ H := fun i hi =>
    Subgroup.mem_sup_right ⟨sEltG i, ⟨i, hi, rfl⟩, by simp [MulAut.conj_apply]⟩
  have hgl : ∀ x ∈ gl, x ∈ H := by
    intro x hx
    simp only [gl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hA 2 (by decide)
    · exact hA 4 (by decide)
    · exact hA 8 (by decide)
    · exact hAc 2 (by decide)
    · exact hAc 4 (by decide)
    · exact hAc 8 (by decide)
  have hcodes : (gl.map fun x => matCode x.1) = [sM 2, sM 4, sM 8,
      mmul (mmul (wcode acw) (sM 2)) (wcode acw.reverse),
      mmul (mmul (wcode acw) (sM 4)) (wcode acw.reverse),
      mmul (mmul (wcode acw) (sM 8)) (wcode acw.reverse)] := by
    simp only [gl, List.map_cons, List.map_nil, matCode_sEltG (by norm_num : 2 < 64),
      matCode_sEltG (by norm_num : 4 < 64), matCode_sEltG (by norm_num : 8 < 64),
      matCode_cG_conj 2 (by norm_num), matCode_cG_conj 4 (by norm_num),
      matCode_cG_conj 8 (by norm_num)]
  have hlen : ∀ j ∈ awT ++ awX ++ awW ++ awb, j < gl.length := by
    have : gl.length = 6 := rfl
    rw [this]
    decide
  refine top_of_gens H gl hgl awT awX awW awb asteps hlen ?_ ?_ ?_ ?_ ?_
  all_goals rw [hcodes]
  all_goals decide +kernel

end CFSG.Quasithin.H13.U3.GC137.S2

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42F48Chk
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Cover

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431

@[expose] def f48Coll0 (m : Fin 45) : Prop :=
  ∃ k < 27, (lnTab.getD k []).contains 0 = true ∧ (lnTab.getD k []).contains m.val = true

@[expose] def f48W (w : List ℕ) : Y := ⟨wordP w, wordP_mem w⟩

theorem f48W_coe (w : List ℕ) : ((f48W w : Y) : P45) = wordP w := rfl

theorem f48W_mem_P1 {w : List ℕ} (h : applyW w 0 = 0) : f48W w ∈ P1 := by
  rw [mem_P1_iff]
  apply Fin.ext
  rw [f48W_coe]
  exact (applyW_eq w 0).trans h

theorem f48W_mem_B0 {w : List ℕ} (h : inB (evalW w) = true) :
    f48W w ∈ B0 := inB_mem h

theorem f48W_append (a b : List ℕ) : f48W (a ++ b) = f48W a * f48W b :=
  Subtype.ext (wordP_append a b)

theorem f48W_invW (w : List ℕ) : f48W (invW w) = (f48W w)⁻¹ := Subtype.ext (wordP_invW w)

theorem f48W_Cj (w : List ℕ) : f48W (f48Cj w) = f48W f48N1 * f48W w * (f48W f48N1)⁻¹ := by
  rw [f48Cj, f48W_append, f48W_append, f48W_invW]

@[expose] def f48f0 : Fin 45 := 1

theorem f48f0_val : (f48f0 : ℕ) = f48F0 := rfl

theorem f48_comm_apply {σ τ : P45} (h : σ * τ = τ * σ) (x : Fin 45) : σ (τ x) = τ (σ x) :=
  congrArg (fun g : P45 => g x) h

theorem f48_wordP_apply_f0 {w : List ℕ} {m : ℕ} (hm : m < 45) (h : applyW w f48F0 = m) :
    (wordP w) f48f0 = ⟨m, hm⟩ := by
  apply Fin.ext
  exact (applyW_eq w f48f0).trans (by rw [f48f0_val]; exact h)

theorem f48_mem_B0_of_image_eq {g y : Y} (hg : (g : P45) 0 = 0) (hy : (y : P45) 0 = 0)
    (h : (y : P45) '' L0S = (g : P45) '' L0S) : g⁻¹ * y ∈ B0 := by
  rw [mem_B0_iff]
  refine ⟨?_, ?_⟩
  · show ((g : P45)⁻¹ * (y : P45)) 0 = 0
    rw [Equiv.Perm.mul_apply, hy, Equiv.Perm.inv_eq_iff_eq, hg]
  · show ((g : P45)⁻¹ * (y : P45)) '' L0S = L0S
    rw [Equiv.Perm.coe_mul, Set.image_comp, h, ← Set.image_comp]
    simp

theorem f48_P1_cases (y : ↥P1) :
    (y : Y) ∈ B0 ∨ (f48W f48N1)⁻¹ * (y : Y) ∈ B0 ∨ (f48W (f48B2 ++ f48N1))⁻¹ * (y : Y) ∈ B0 := by
  have hy0 : ((y : Y) : P45) 0 = 0 := (mem_P1_iff _).1 y.2
  obtain ⟨k, hk, hgk⟩ := line_stable (y : Y).2 (k := 0) (by norm_num)
  rw [lnS_zero] at hgk
  have hmem : (0 : Fin 45) ∈ lnS k := by
    rw [← hgk]
    exact ⟨0, zero_mem_L0S, hy0⟩
  have hc : (lnTab.getD k []).contains 0 = true := List.contains_iff_mem.2 hmem
  have hn1 : ((f48W f48N1 : Y) : P45) 0 = 0 := (mem_P1_iff _).1 (f48W_mem_P1 f48_n1_fix)
  have hb2 : (f48W f48B2 : Y) ∈ P1 := B0_le_P1 (f48W_mem_B0 f48_rel_spec.2.1)
  have hlin : ∀ w : List ℕ, sameSet (lnTab.getD k []) (imgSet (evalW w) L0) = true →
      lnS k = ((f48W w : Y) : P45) '' L0S := by
    intro w hw
    rw [L0S, f48W_coe, image_lineSet (repL_wordP w) L0_lt, lnS]
    exact lineSet_eq_of_sameSet hw
  rcases f48_linesCheck k hk hc with h | h | h
  · left
    have h1 : lnS k = L0S := by
      rw [lnS, L0S]
      exact lineSet_eq_of_sameSet h
    rw [mem_B0_iff]
    exact ⟨hy0, hgk.trans h1⟩
  · right; left
    exact f48_mem_B0_of_image_eq hn1 hy0 (hgk.trans (hlin f48N1 (by simpa using h)))
  · right; right
    have hb : ((f48W (f48B2 ++ f48N1) : Y) : P45) 0 = 0 := by
      rw [f48W_append, show ((f48W f48B2 * f48W f48N1 : Y) : P45) =
        (f48W f48B2 : P45) * (f48W f48N1 : P45) from rfl, Equiv.Perm.mul_apply, hn1]
      exact (mem_P1_iff _).1 hb2
    exact f48_mem_B0_of_image_eq hb hy0 (hgk.trans (hlin (f48B2 ++ f48N1) h))

end CFSG.Quasithin.H13.F431.U42

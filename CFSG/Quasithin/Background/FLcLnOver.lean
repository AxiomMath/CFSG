module

public import CFSG.Quasithin.Background.S1549EA
public import CFSG.Quasithin.Background.FLcLnSetup

public section

namespace CFSG.Quasithin

namespace S1549E

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lnParabolicOvergroups_holds : LnParabolicOvergroups := by
  intro n hn A _ _ L X S P₀ hiso hLX hLn hS hXLS hO2 hpar hP₀n
  have hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨iso⟩ := hiso
  obtain ⟨D, hBP₀, hP₀L, x₀, hx₀, hx₀P, hx₀u⟩ := FLc.ln_setup (by omega)
    (iso.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).symm)
    hLX hLn hS hpar hP₀n
  have hBL : S ⊓ L ≤ L := inf_le_right
  obtain ⟨i, j, hi, hj, hij, hix, hjx⟩ := FLc.exists_two_nodes x₀ hn4
  have hiP : i ∈ D.cutsOf P₀ := by
    by_contra h
    exact hix (hx₀u i hi h)
  have hjP : j ∈ D.cutsOf P₀ := by
    by_contra h
    exact hjx (hx₀u j hj h)
  have hSn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl => hLn s (hS.1 hs) l hl
  by_cases hSLe : S ≤ L
  ·
    left
    have hXL : X = L := le_antisymm (hXLS.trans (sup_eq_left.2 hSLe).le) hLX
    have hSP₀ : S ≤ P₀ := fun x hx => hBP₀ ⟨hx, hSLe hx⟩
    have hPS : P₀ ⊔ S = P₀ := sup_eq_left.2 hSP₀
    have hmk : ∀ z, FLc.IsNode n z → ∃ K : Subgroup A, S ⊓ L ≤ K ∧ K ≤ L ∧ D.cutsOf K = {z} := by
      intro z hz
      exact D.exists_cutsOf_eq hBL (I := {z}) (by rintro i rfl; exact hz)
    have hmax : ∀ K z, S ⊓ L ≤ K → K ≤ L → D.cutsOf K = {z} → IsMaxSubgroupIn L K := by
      intro K z hBK hKL hK
      refine D.isMax_of_cuts_insert hBL hBL le_rfl hBK hKL (x := z)
        (by rw [D.cutsOf_L]; exact Set.notMem_empty z) ?_
      rw [hK, D.cutsOf_L]
      simp
    obtain ⟨Ki, hBKi, hKiL, hKi⟩ := hmk i hi
    obtain ⟨Kj, hBKj, hKjL, hKj⟩ := hmk j hj
    refine ⟨Ki, Kj, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hXL]
      exact hmax Ki i hBKi hKiL hKi
    · rw [hXL]
      exact hmax Kj j hBKj hKjL hKj
    · intro h
      have := congrArg D.cutsOf h
      rw [hKi, hKj] at this
      exact hij (Set.singleton_eq_singleton_iff.1 this)
    · rw [hPS]
      exact (D.cutsOf_le_iff hBL hBP₀ hP₀L hBKi).2 (by
        rw [hKi]
        exact Set.singleton_subset_iff.2 hiP)
    · rw [hPS]
      exact (D.cutsOf_le_iff hBL hBP₀ hP₀L hBKj).2 (by
        rw [hKj]
        exact Set.singleton_subset_iff.2 hjP)
  ·
    right
    obtain ⟨s, hsS, hsL⟩ : ∃ s ∈ S, s ∉ L := by
      by_contra h
      push Not at h
      exact hSLe h
    have hf₀ := FLc.cutsOf_flip_invariant (by omega) D hLX hLn hS hXLS hO2 hsS hsL hBP₀ hP₀n
    have h₀ := FLc.two_mul_eq_of_flip (fun i hi => D.isNode_of_mem_cutsOf hi) hf₀ hx₀ hx₀P hx₀u
    have hn4' : n = 4 := by
      rcases hn with h | h
      · exact h
      · omega
    subst hn4'
    have hx2 : x₀ = 2 := by omega
    subst hx2
    refine ⟨rfl, ?_, ?_⟩
    · intro h
      apply hsL
      rw [h]
      exact hS.1 hsS
    · have hP₀S : P₀ ⊔ S ≤ X := sup_le (hP₀L.trans hLX) hS.1
      have hPSL : ∀ l ∈ L, l ∈ P₀ ⊔ S → l ∈ P₀ := by
        intro l hl hlPS
        obtain ⟨p, hp, t, ht, rfl⟩ := FLc.mem_sup_prod_of_conj hP₀n l hlPS
        have htL : t ∈ L := by
          have := L.mul_mem (L.inv_mem (hP₀L hp)) hl
          simpa [mul_assoc] using this
        exact P₀.mul_mem hp (hBP₀ ⟨ht, htL⟩)
      refine ⟨lt_of_le_of_ne hP₀S ?_, fun K hlt hKX => ?_⟩
      · intro hEq
        have hLP₀ : L ≤ P₀ := fun l hl => hPSL l hl (by rw [hEq]; exact hLX hl)
        have hLeq : P₀ = L := le_antisymm hP₀L hLP₀
        have h1 := congrArg D.cutsOf hLeq
        rw [D.cutsOf_L] at h1
        have h2 : i ∈ (∅ : Set ℕ) := h1 ▸ hiP
        exact Set.notMem_empty i h2
      · have hP₀K : P₀ ≤ K := le_sup_left.trans hlt.le
        have hSK : S ≤ K := le_sup_right.trans hlt.le
        have hBK' : S ⊓ L ≤ K ⊓ L := le_inf (inf_le_left.trans hSK) inf_le_right
        have hK'L : K ⊓ L ≤ L := inf_le_right
        have hP₀K' : P₀ ≤ K ⊓ L := le_inf hP₀K hP₀L
        have hK'n : ∀ s ∈ S, ∀ q ∈ K ⊓ L, s * q * s⁻¹ ∈ K ⊓ L := fun s hs q hq =>
          ⟨K.mul_mem (K.mul_mem (hSK hs) hq.1) (K.inv_mem (hSK hs)), hSn s hs q hq.2⟩
        have hf := FLc.cutsOf_flip_invariant (by omega) D hLX hLn hS hXLS hO2 hsS hsL hBK' hK'n
        have hsub : D.cutsOf (K ⊓ L) ⊆ D.cutsOf P₀ :=
          (D.cutsOf_le_iff hBL hBP₀ hP₀L hBK').1 hP₀K'
        have hcP : ∀ y, y ∈ D.cutsOf P₀ ↔ (FLc.IsNode 4 y ∧ y ≠ 2) := by
          intro y
          constructor
          · intro hy
            exact ⟨D.isNode_of_mem_cutsOf hy, fun h => hx₀P (h ▸ hy)⟩
          · rintro ⟨hyn, hy2⟩
            by_contra hy
            exact hy2 (hx₀u y hyn hy)
        by_cases h1 : 1 ∈ D.cutsOf (K ⊓ L)
        · have h3 : 3 ∈ D.cutsOf (K ⊓ L) := by
            have : 3 ∈ FLc.flipNodes 4 (D.cutsOf (K ⊓ L)) := ⟨1, h1, rfl⟩
            rwa [← hf] at this
          have hEq : D.cutsOf (K ⊓ L) = D.cutsOf P₀ := by
            refine Set.Subset.antisymm hsub fun y hy => ?_
            obtain ⟨hyn, hy2⟩ := (hcP y).1 hy
            have : y = 1 ∨ y = 3 := by
              obtain ⟨_, _⟩ := hyn
              omega
            rcases this with rfl | rfl <;> assumption
          have hK'P₀ : K ⊓ L = P₀ := D.eq_of_cutsOf_eq hBL hBK' hK'L hBP₀ hP₀L hEq
          exfalso
          apply hlt.not_ge
          intro x hx
          obtain ⟨l, hl, t, ht, rfl⟩ := FLc.mem_sup_prod_of_conj hSn x (hXLS (hKX hx))
          have hlK : l ∈ K := by
            have := K.mul_mem hx (K.inv_mem (hSK ht))
            simpa [mul_assoc] using this
          have hlP₀ : l ∈ P₀ := by
            rw [← hK'P₀]
            exact ⟨hlK, hl⟩
          exact (P₀ ⊔ S).mul_mem ((le_sup_left : P₀ ≤ P₀ ⊔ S) hlP₀) ((le_sup_right : S ≤ P₀ ⊔ S) ht)
        · have h3 : 3 ∉ D.cutsOf (K ⊓ L) := by
            intro h3
            apply h1
            have : 1 ∈ FLc.flipNodes 4 (D.cutsOf (K ⊓ L)) := ⟨3, h3, rfl⟩
            rwa [← hf] at this
          have hEq : D.cutsOf (K ⊓ L) = D.cutsOf L := by
            rw [D.cutsOf_L]
            ext y
            constructor
            · intro hy
              obtain ⟨hyn, hy2⟩ := (hcP y).1 (hsub hy)
              have : y = 1 ∨ y = 3 := by
                obtain ⟨_, _⟩ := hyn
                omega
              rcases this with rfl | rfl
              · exact absurd hy h1
              · exact absurd hy h3
            · intro h
              exact absurd h (Set.notMem_empty y)
          have hK'L' : K ⊓ L = L := D.eq_of_cutsOf_eq hBL hBK' hK'L hBL le_rfl hEq
          have hLK : L ≤ K := by
            rw [← hK'L']
            exact inf_le_left
          exact le_antisymm hKX (hXLS.trans (sup_le hLK hSK))

end S1549E

end CFSG.Quasithin

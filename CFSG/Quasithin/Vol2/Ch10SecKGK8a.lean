module

public import CFSG.Quasithin.Vol2.Ch10SecCFacts
public import CFSG.Quasithin.Vol2.Ch10SecQ6O4d
public import CFSG.Quasithin.Vol2.Ch10SecQ6O4b
public import CFSG.Quasithin.Vol2.Ch10SecKGIrr

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch10.SecD.C10P06 Matrix

namespace C10KG

variable {F : Type} [Field F] [CharP F 2] [Finite F] {n : ℕ}

omit [Finite F] in
theorem ut_conj_add (t : F) (X : Matrix (Fin 2) (Fin 2) F) :
    ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * X *
        (frobPow n ((ut t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))ᵀ + X =
      !![X 0 1 * sig n t + t * X 1 0 + t * X 1 1 * sig n t, t * X 1 1;
        X 1 1 * sig n t, 0] := by
  ext i j
  rw [Matrix.add_apply, conj_entry, coe_ut]
  fin_cases i <;> fin_cases j <;> simp [sig_zero, sig_one] <;> ring_nf <;>
    simp [CharTwo.two_eq_zero]

theorem exists_E11_mem (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n)
    {S : Set (Matrix (Fin 2) (Fin 2) F)} (hadd : ∀ X ∈ S, ∀ Y ∈ S, X + Y ∈ S)
    (hinv : ∀ (γ : SpecialLinearGroup (Fin 2) F), ∀ X ∈ S,
      (γ : Matrix (Fin 2) (Fin 2) F) * X * (frobPow n (γ : Matrix (Fin 2) (Fin 2) F))ᵀ ∈ S)
    (hS : ∀ X ∈ S, IsHerm n X) {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ S) (hX0 : X ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ sig n c = c ∧ !![c, 0; 0, 0] ∈ S := by
  have key : ∀ Y ∈ S, Y 1 1 = 0 → Y 0 1 ≠ 0 →
      ∃ c : F, c ≠ 0 ∧ sig n c = c ∧ !![c, 0; 0, 0] ∈ S := by
    intro Y hY hY11 hY01
    obtain ⟨-, -, h01, -⟩ := isHerm_iff.mp (hS Y hY)
    obtain ⟨s, hs⟩ : ∃ s : F, s * sig n (Y 0 1) + sig n s * Y 0 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hY01 (eq_zero_of_trace hF hn hcon)
    refine ⟨s * sig n (Y 0 1) + sig n s * Y 0 1, hs, ?_, ?_⟩
    · rw [sig_add, sig_mul, sig_mul, sig_sig hF, sig_sig hF]
      ring
    · have hmem := hadd _ (hinv (ut s) Y hY) Y hY
      rw [ut_conj_add, hY11, ← h01] at hmem
      convert hmem using 2
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      ring
  obtain ⟨h00, -, h01, -⟩ := isHerm_iff.mp (hS X hX)
  by_cases h11 : X 1 1 = 0
  · by_cases h01' : X 0 1 = 0
    · refine ⟨X 0 0, fun h => hX0 ?_, h00, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [h, h11, h01', ← h01, sig_zero]
      · convert hX using 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h11, h01', ← h01, sig_zero]
    · exact key X hX h11 h01'
  · have hY := hadd _ (hinv (ut 1) X hX) X hX
    refine key _ hY ?_ ?_
    · rw [ut_conj_add]
      simp
    · rw [ut_conj_add]
      simpa using h11

theorem herm_mem_of_ne (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n)
    {S : Set (Matrix (Fin 2) (Fin 2) F)} (hadd : ∀ X ∈ S, ∀ Y ∈ S, X + Y ∈ S)
    (hinv : ∀ (γ : SpecialLinearGroup (Fin 2) F), ∀ X ∈ S,
      (γ : Matrix (Fin 2) (Fin 2) F) * X * (frobPow n (γ : Matrix (Fin 2) (Fin 2) F))ᵀ ∈ S)
    (hS : ∀ X ∈ S, IsHerm n X) {X : Matrix (Fin 2) (Fin 2) F} (hX : X ∈ S) (hX0 : X ≠ 0)
    {Y : Matrix (Fin 2) (Fin 2) F} (hY : IsHerm n Y) : Y ∈ S := by
  obtain ⟨c, hc0, hcs, hcS⟩ := exists_E11_mem hF hn hadd hinv hS hX hX0
  have h0 : (0 : Matrix (Fin 2) (Fin 2) F) ∈ S := by
    have := hadd X hX X hX
    rwa [CharTwo.add_self_eq_zero] at this
  have hK0 : ∀ b : F, sig n b = b → !![b, 0; 0, 0] ∈ S := by
    intro b hb
    by_cases hb0 : b = 0
    · convert h0 using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb0]
    · have hq : sig n (b / c) = b / c := by
        unfold sig at hb hcs ⊢
        rw [div_pow, hb, hcs]
      obtain ⟨l, hl⟩ := exists_norm_eq hF hn hq (div_ne_zero hb0 hc0)
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hl
        exact div_ne_zero hb0 hc0 hl.symm
      have hmem := hinv (dg l hl0) _ hcS
      rw [conj_dg, hl, div_mul_cancel₀ b hc0] at hmem
      exact hmem
  exact herm_induction hF (P := (· ∈ S)) (fun A B hA hB => hadd A hA B hB)
    (fun g c' hc' => hinv g _ (hK0 c' hc')) hY

end C10KG

theorem factK8a_holds : FactK8a := by
  intro V _ _ Hm U Z n hn h
  obtain ⟨K, _, _, _, hK, π, hRV⟩ := h
  have hF : Nat.card K = 4 ^ n := by rw [hK, pow_mul]; norm_num
  refine C10KG.isIrrSec_of_realizesVia hRV rfl
    ⟨Multiplicative.ofAdd !![(1 : K), 0; 0, 0], ?_, ?_⟩ ?_
  · change (frobPow n !![(1 : K), 0; 0, 0])ᵀ = !![(1 : K), 0; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frobPow]
  · intro h1
    have h1' : (Multiplicative.ofAdd !![(1 : K), 0; 0, 0] :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) = 1 := h1
    have h2 := congrArg Multiplicative.toAdd h1'
    rw [toAdd_ofAdd, toAdd_one] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp at h3
  · intro S hS hSinv
    by_cases hbot : S = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨⟨m₀', hm₀S⟩, hm₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    let m₀ : Multiplicative (Matrix (Fin 2) (Fin 2) K) := m₀'
    let T : Set (Matrix (Fin 2) (Fin 2) K) := {X | Multiplicative.ofAdd X ∈ S}
    have hadd : ∀ X ∈ T, ∀ Y ∈ T, X + Y ∈ T := fun X hX Y hY => S.mul_mem hX hY
    have hinv : ∀ (γ : SpecialLinearGroup (Fin 2) K), ∀ X ∈ T,
        (γ : Matrix (Fin 2) (Fin 2) K) * X * (frobPow n (γ : Matrix (Fin 2) (Fin 2) K))ᵀ ∈ T :=
      fun γ X hX => hSinv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K γ) _ hX
    have hT : ∀ X ∈ T, IsHerm n X := fun X hX => hS hX
    have hX0 : Multiplicative.toAdd m₀ ≠ 0 := fun h0 => hm₀1 (Subtype.ext (by
      change m₀ = 1
      rw [← ofAdd_toAdd m₀, h0, ofAdd_zero]))
    have hX : Multiplicative.toAdd m₀ ∈ T := by
      change Multiplicative.ofAdd (Multiplicative.toAdd m₀) ∈ S
      rw [ofAdd_toAdd]
      exact hm₀S
    refine le_antisymm hS fun m hm => ?_
    let m' : Multiplicative (Matrix (Fin 2) (Fin 2) K) := m
    have hm' := C10KG.herm_mem_of_ne hF hn hadd hinv hT hX hX0
      (Y := Multiplicative.toAdd m') hm
    change Multiplicative.ofAdd (Multiplicative.toAdd m') ∈ S at hm'
    rwa [ofAdd_toAdd] at hm'

end CFSG.Quasithin.Vol2.Ch10.SecC

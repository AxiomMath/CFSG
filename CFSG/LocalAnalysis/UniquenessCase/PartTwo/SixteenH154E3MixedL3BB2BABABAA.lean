module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3ParaA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Stellmacher.L3YC
open CFSG.Quasithin.H13.A6.A6L76Of

private theorem s16h_orders9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 4 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 7 = 1 := by
  decide

private theorem s16h_mat_orders (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : M.det = 1) :
    M ^ 4 = 1 ∨ M ^ 3 = 1 ∨ M ^ 7 = 1 := by
  have := s16h_orders9 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2)
    (M 2 0) (M 2 1) (M 2 2)
  rw [← Matrix.eta_fin_three M] at this
  exact this h

private theorem s16h_det_GL32 (g : GL (Fin 3) (ZMod 2)) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

private theorem s16h_orders_GL32 (g : GL (Fin 3) (ZMod 2)) :
    g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases s16h_mat_orders (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (s16h_det_GL32 g) with h | h | h
  · exact Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl))
  · exact Or.inr (Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))
  · exact Or.inr (Or.inr (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))

private theorem s16h_orders_of_mulEquiv {R : Type*} [Group R]
    (ψ : R ≃* GL (Fin 3) (ZMod 2)) (g : R) :
    g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases s16h_orders_GL32 (ψ g) with h | h | h
  · exact Or.inl (ψ.injective (by rw [map_pow, h, map_one]))
  · exact Or.inr (Or.inl (ψ.injective (by rw [map_pow, h, map_one])))
  · exact Or.inr (Or.inr (ψ.injective (by rw [map_pow, h, map_one])))

private theorem s16h_stabAct_pow_twelve {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {w : Fin 3 → F} (hw : w ≠ 0) :
    ∀ g ∈ stabAct w, g ^ 12 = 1 := by
  haveI : CharP F 2 := charP_of_card_eq_prime (p := 2) hF
  intro g hg
  rcases s16h_orders_of_mulEquiv (glZ2 hF) g with h4 | h3 | h7
  · calc g ^ 12 = (g ^ 4) ^ 3 := by rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul]
      _ = 1 := by rw [h4, one_pow]
  · calc g ^ 12 = (g ^ 3) ^ 4 := by rw [show (12 : ℕ) = 3 * 4 by norm_num, pow_mul]
      _ = 1 := by rw [h3, one_pow]
  · have hcard : Nat.card (stabAct w : Subgroup (GL (Fin 3) F)) = 24 := card_stabAct hF hw
    have hdvd7 : orderOf g ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr h7
    have hdvd24 : orderOf g ∣ 24 := by
      rw [← hcard, ← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    have h1 : orderOf g = 1 := by
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact h
      · rw [h] at hdvd24
        omega
    rw [orderOf_eq_one_iff.mp h1]
    exact one_pow 12

theorem s16h_stabSL_pow_twelve {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (m : Multiplicative (Fin 3 → K)) (hm : m ≠ 1) :
    ∀ γ ∈ s1611e3_stabSL m, γ ^ 12 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hKf2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hw : Multiplicative.toAdd m ≠ 0 := by
    intro h0
    apply hm
    have h1 : Multiplicative.ofAdd (Multiplicative.toAdd m) = Multiplicative.ofAdd 0 := by
      rw [h0]
    simpa using h1
  intro γ hγ
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply s16h_stabAct_pow_twelve hKf2 hw
  rw [mem_stabAct]
  have h1 := congrArg Multiplicative.toAdd hγ
  rwa [natHom_apply] at h1

theorem s16h_e3_sl3_parabolic {X : Type} [Group X] (h : IsSLn X 3 1) :
    ∃ P : Subgroup X, Nat.card ↥P = 24 ∧ ∀ p ∈ P, p ^ 12 = 1 := by
  obtain ⟨K, hfield, hfin, hcard, ⟨e⟩⟩ := h
  letI : Field K := hfield
  letI : Finite K := hfin
  have hK : Nat.card K = 2 := by simpa using hcard
  let m : Multiplicative (Fin 3 → K) :=
    Multiplicative.ofAdd (fun i : Fin 3 => if i = 0 then (1 : K) else 0)
  have hm : m ≠ 1 := by
    intro h1
    have h2 : (fun i : Fin 3 => if i = 0 then (1 : K) else 0) = (0 : Fin 3 → K) := by
      have := congrArg Multiplicative.toAdd h1
      simpa [m] using this
    have h3 := congrFun h2 0
    exact one_ne_zero h3
  let Q : Subgroup ↥(StatedSL 3 K) := s1611e3_stabSL m
  have hQcard : Nat.card ↥Q = 24 := s1611e3_stabSL_card hK hm
  have hQexp : ∀ q ∈ Q, q ^ 12 = 1 := s16h_stabSL_pow_twelve hK m hm
  refine ⟨Q.map e.symm.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, hQcard]
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    rw [← map_pow, hQexp q hq, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

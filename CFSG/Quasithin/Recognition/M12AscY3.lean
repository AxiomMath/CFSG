module

public import CFSG.Quasithin.Recognition.M12AscY2
public import CFSG.Quasithin.Recognition.M12AscS6c

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscModel

variable {m : AscModel z}

theorem rho_evalWord (c : AscCox m) (T : Fin 5 → Perm (Fin 6)) (w : List (Fin 5)) :
    c.ρ (evalWord T w) = evalWord (fun i => c.ρ (T i)) w := by
  unfold evalWord
  rw [map_list_prod, List.map_map]
  rfl

theorem conj_word {y : G} {c : AscCox m} {T : Fin 5 → Perm (Fin 6)}
    (hT : ∀ i, y * c.ρ (swapGen i) * y⁻¹ = c.ρ (T i)) {σ : Perm (Fin 6)} {w : List (Fin 5)}
    (hw : evalWord swapGen w = σ) : y * c.ρ σ * y⁻¹ = c.ρ (evalWord T w) := by
  let h : Perm (Fin 6) →* G := (MulAut.conj y).toMonoidHom.comp c.ρ
  have h1 : h σ = evalWord (fun i => h (swapGen i)) w := hom_apply_word h hw
  have h2 : (fun i => h (swapGen i)) = fun i => c.ρ (T i) := by
    funext i
    exact hT i
  rw [h2] at h1
  rw [rho_evalWord]
  exact h1

theorem alpha_sq {y : G} {c : AscCox m} {T : Fin 5 → Perm (Fin 6)}
    (hT : ∀ i, y * c.ρ (swapGen i) * y⁻¹ = c.ρ (T i)) (hy : y * y = m.ψ mA)
    {w : List (Fin 5)} (hw : evalWord swapGen w = T 1) :
    evalWord T w = pa * swap 1 2 * pa := by
  have h1 : y * c.ρ (T 1) * y⁻¹ = c.ρ (evalWord T w) := by
    rw [← hw]
    exact conj_word hT rfl
  have h2 : y * c.ρ (swapGen 1) * y⁻¹ = c.ρ (T 1) := hT 1
  have h3 : y * c.ρ (T 1) * y⁻¹ = m.ψ mA * c.ρ (swap 1 2) * (m.ψ mA)⁻¹ := by
    rw [← h2]
    calc y * (y * c.ρ (swapGen 1) * y⁻¹) * y⁻¹ = (y * y) * c.ρ (swapGen 1) * (y * y)⁻¹ := by group
      _ = m.ψ mA * c.ρ (swap 1 2) * (m.ψ mA)⁻¹ := by rw [hy]; rfl
  have hai : (m.ψ mA)⁻¹ = m.ψ mA := inv_eq_of_mul_eq_one_right AscModel.a_sq
  rw [hai, ← c.ρ_pa] at h3
  rw [h3] at h1
  apply c.ρ_inj
  rw [← h1, map_mul, map_mul]

theorem conj_inv_y {y : G} (hy : y * y = m.ψ mA) (x : G) :
    y⁻¹ * x * y = (m.ψ mA)⁻¹ * (y * x * y⁻¹) * m.ψ mA := by
  have hai : (m.ψ mA)⁻¹ * m.ψ mA = 1 := inv_mul_cancel _
  have h1 : y⁻¹ = (m.ψ mA)⁻¹ * y := by
    rw [← hy]
    group
  have h2 : y = y⁻¹ * m.ψ mA := by
    rw [← hy]
    group
  calc y⁻¹ * x * y = ((m.ψ mA)⁻¹ * y) * x * (y⁻¹ * m.ψ mA) := by rw [← h1, ← h2]
    _ = (m.ψ mA)⁻¹ * (y * x * y⁻¹) * m.ψ mA := by group

theorem exists_outer
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (c : AscCox m) :
    ∃ y : G, y * y = m.ψ mA ∧ ∀ i : Fin 5, y * c.ρ (swapGen i) * y⁻¹ = c.ρ (TA i) := by
  classical
  obtain ⟨y, hyy, hyz, hycp, hyu⟩ := exists_y0 hyp c
  have hy : YRel c y := ⟨hyy, hyz, hycp, hyu⟩
  have hnorm := y_normalizes hy
  have hex : ∀ i : Fin 5, ∃ τ : Perm (Fin 6), c.ρ τ = y * c.ρ (swapGen i) * y⁻¹ := fun i =>
    MonoidHom.mem_range.1 (hnorm (swapGen i))
  choose T hT using hex
  have hT' : ∀ i, y * c.ρ (swapGen i) * y⁻¹ = c.ρ (T i) := fun i => (hT i).symm
  let φ : Perm (Fin 6) →* G := (MulAut.conj y).toMonoidHom.comp c.ρ
  have hφ : ∀ σ, φ σ = y * c.ρ σ * y⁻¹ := fun σ => rfl
  have hφT : ∀ i, φ (swapGen i) = c.ρ (T i) := fun i => (hφ _).trans (hT' i)
  have hsqT : ∀ i, T i * T i = 1 := by
    intro i
    apply c.ρ_inj
    rw [map_mul, ← hφT i, ← map_mul, show swapGen i * swapGen i = 1 from Equiv.swap_mul_self _ _,
      map_one, map_one]
  have hrelT : ∀ i j : Fin 5, i.val < j.val → (T i * T j) ^ coxExp i j = 1 := by
    intro i j hij
    apply c.ρ_inj
    have h := swap_coxeter_five.2 i j hij
    rw [map_pow, map_mul, ← hφT i, ← hφT j, ← map_mul, ← map_pow,
      show (swapGen i * swapGen j) ^ coxExp i j = 1 from h, map_one, map_one]
  have hT0 : T 0 = tA1 := by
    apply c.ρ_inj
    rw [← hφT 0]
    show y * c.ρ (swap 0 1) * y⁻¹ = c.ρ tA1
    rw [c.ρ_z, hy.conj_z, tA1_eq_ps, c.ρ_ps]
  have hT4 : T 4 = tA5 := by
    apply c.ρ_inj
    rw [← hφT 4]
    show y * c.ρ (swap 4 5) * y⁻¹ = c.ρ tA5
    rw [c.ρ_u, hy.conj_u, ← tA5_eq, map_mul, c.ρ_z]
  have hT2 : T 2 = tA3 := by
    apply c.ρ_inj
    rw [← hφT 2]
    show y * c.ρ (swap 2 3) * y⁻¹ = c.ρ tA3
    rw [c.ρ_au, ← tA3_eq, map_mul, map_mul, c.ρ_pa, c.ρ_z]
    calc y * (m.ψ mA * c.u') * y⁻¹ = (y * m.ψ mA * y⁻¹) * (y * c.u' * y⁻¹) := by group
      _ = m.ψ mA * (z * c.ρ pcp) := by rw [hy.conj_a, hy.conj_u]
  have hφa : φ pa = c.ρ pa := by
    rw [hφ, c.ρ_pa, hy.conj_a]
  have hT3c : T 3 * pa * T 3 = pa * pb := by
    apply c.ρ_inj
    have h1 : φ pcp = c.ρ (pa * pb) := by
      rw [hφ, map_mul, c.ρ_pa, c.ρ_pb, hy.conj_cp]
    have h2 : φ pcp = c.ρ (T 3 * pa * T 3) := by
      conv_lhs => rw [pcp_eq]
      rw [map_mul, map_mul, hφa, map_mul, map_mul]
      have := hφT 3
      rw [show swapGen 3 = swap 3 4 from rfl] at this
      rw [this]
    rw [← h2, h1]
  have e01 : coxExp (0 : Fin 5) 1 = 3 := by decide
  have e03 : coxExp (0 : Fin 5) 3 = 2 := by decide
  have e12 : coxExp (1 : Fin 5) 2 = 3 := by decide
  have e13 : coxExp (1 : Fin 5) 3 = 2 := by decide
  have e14 : coxExp (1 : Fin 5) 4 = 2 := by decide
  have e23 : coxExp (2 : Fin 5) 3 = 3 := by decide
  have e34 : coxExp (3 : Fin 5) 4 = 3 := by decide
  have r01 := hrelT 0 1 (by decide)
  have r03 := hrelT 0 3 (by decide)
  have r12 := hrelT 1 2 (by decide)
  have r13 := hrelT 1 3 (by decide)
  have r14 := hrelT 1 4 (by decide)
  have r23 := hrelT 2 3 (by decide)
  have r34 := hrelT 3 4 (by decide)
  rw [e01, hT0] at r01
  rw [e03, hT0] at r03
  rw [e12, hT2] at r12
  rw [e14, hT4] at r14
  rw [e23, hT2] at r23
  rw [e34, hT4] at r34
  rw [e13] at r13
  have hT3c' : T 3 * (tA3 * tA5) * T 3 = pa * pb := by rw [tA3_mul_tA5]; exact hT3c
  have hcases := enum_tau (T 3) ⟨hsqT 3, r23, r34, r03, hT3c'⟩ (T 1) ⟨hsqT 1, r01, r12, r13, r14⟩
  have hTfun : ∀ t2 t4, T 1 = t2 → T 3 = t4 → T = candTuple t2 t4 := by
    intro t2 t4 h1 h3
    funext i
    fin_cases i
    · exact hT0
    · exact h1
    · exact hT2
    · exact h3
    · exact hT4
  rcases hcases with ⟨h2, h4⟩ | ⟨h2, h4⟩ | ⟨h2, h4⟩ | ⟨h2, h4⟩
  ·
    refine ⟨y, hyy, fun i => ?_⟩
    rw [hT' i, hTfun _ _ h2 h4]
    rfl
  ·
    have hTD : T = TD := hTfun _ _ h2 h4
    have hai : (m.ψ mA)⁻¹ = m.ψ mA := inv_eq_of_mul_eq_one_right AscModel.a_sq
    refine ⟨y⁻¹, ?_, fun i => ?_⟩
    · rw [← mul_inv_rev, hyy, hai]
    · rw [inv_inv, conj_inv_y hyy, hT' i, hTD, hai, ← c.ρ_pa, ← map_mul, ← map_mul,
        TD_conj_TA i]
  ·
    exfalso
    have hTE : T = TE := hTfun _ _ h2 h4
    have hw : evalWord swapGen [0, 1, 0, 3, 2, 1, 0, 4, 3] = T 1 := by rw [h2]; exact word_E2
    have := alpha_sq (T := T) hT' hyy hw
    rw [hTE] at this
    exact alpha2_E this
  ·
    exfalso
    have hTF : T = TF := hTfun _ _ h2 h4
    have hw : evalWord swapGen [0, 1, 2, 1, 0, 3, 2, 1, 4, 3, 2, 1, 0] = T 1 := by
      rw [h2]; exact word_F2
    have := alpha_sq (T := T) hT' hyy hw
    rw [hTF] at this
    exact alpha2_F this

end AscModel

end CFSG.Quasithin

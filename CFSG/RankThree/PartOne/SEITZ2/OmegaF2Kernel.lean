module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaF2Aff
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ2

namespace AffKernel

open Matrix CFSG.RankThree.PartOne.CTP Aff

variable {K : Type} [Field K]

@[expose] def kerDiag (s : K) (hs : s ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩

theorem kerDiag_coe (s : K) (hs : s ≠ 0) :
    (kerDiag s hs : Matrix (Fin 2) (Fin 2) K) = !![s, 0; 0, s⁻¹] := rfl

theorem kerDiag_inv_coe (s : K) (hs : s ≠ 0) :
    (((kerDiag s hs)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![s⁻¹, 0; 0, s] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, kerDiag_coe, Matrix.adjugate_fin_two]
  simp

theorem kerDiag_mul_u2_mul_inv (s a : K) (hs : s ≠ 0) :
    kerDiag s hs * u2 a * (kerDiag s hs)⁻¹ = u2 (s ^ 2 * a) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, kerDiag_coe, kerDiag_inv_coe]
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  all_goals ring

theorem kerDiag_comm (s s' : K) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    kerDiag s hs * kerDiag s' hs' = kerDiag s' hs' * kerDiag s hs := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kerDiag_coe, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem exists_sq_mul_eq_one [Finite K] [CharP K 2] {a : K} (ha : a ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ s ^ 2 * a = 1 := by
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a⁻¹
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact ha (by simpa using hs)
  refine ⟨s, hs0, ?_⟩
  rw [sq, ← hs]
  exact inv_mul_cancel₀ ha

theorem u2_mul_eq (t : K) (c : Matrix (Fin 2) (Fin 2) K) :
    (u2 t : Matrix (Fin 2) (Fin 2) K) * c =
      !![c 0 0 + t * c 1 0, c 0 1 + t * c 1 1; c 1 0, c 1 1] := by
  rw [u2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem l2_mul_eq (t : K) (c : Matrix (Fin 2) (Fin 2) K) :
    (l2 t : Matrix (Fin 2) (Fin 2) K) * c =
      !![c 0 0, c 0 1; t * c 0 0 + c 1 0, t * c 0 1 + c 1 1] := by
  rw [l2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem kerDiag_mul_eq (s : K) (hs : s ≠ 0) (c : Matrix (Fin 2) (Fin 2) K) :
    (kerDiag s hs : Matrix (Fin 2) (Fin 2) K) * c =
      !![s * c 0 0, s * c 0 1; s⁻¹ * c 1 0, s⁻¹ * c 1 1] := by
  rw [kerDiag_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem uniq {M : Subgroup (Aff K)} (hN : ∀ b, (⟨1, b⟩ : Aff K) ∈ M → b = 0) {x y : Aff K}
    (hx : x ∈ M) (hy : y ∈ M) (hxy : x.m = y.m) : x.b = y.b := by
  have hm : (x * y⁻¹).m = 1 := by simp [hxy]
  have hmem : (⟨1, (x * y⁻¹).b⟩ : Aff K) ∈ M := by
    have : x * y⁻¹ = ⟨1, (x * y⁻¹).b⟩ := by
      ext1
      · exact hm
      · rfl
    rw [← this]
    exact M.mul_mem hx (M.inv_mem hy)
  have h := hN _ hmem
  simp only [mul_b, inv_b, hxy] at h
  have h2 : (y.m : Matrix (Fin 2) (Fin 2) K) * ((y.m⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, h2, Matrix.one_mul] at h
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

theorem exists_lift {M : Subgroup (Aff K)} (htop : M.map Aff.proj = ⊤)
    (m : SpecialLinearGroup (Fin 2) K) : ∃ β, (⟨m, β⟩ : Aff K) ∈ M := by
  have hm : m ∈ M.map Aff.proj := htop ▸ Subgroup.mem_top m
  obtain ⟨x, hx, hxm⟩ := Subgroup.mem_map.mp hm
  refine ⟨x.b, ?_⟩
  have : (⟨m, x.b⟩ : Aff K) = x := by
    ext1
    · exact hxm.symm
    · rfl
  rw [this]
  exact hx

theorem conj_eq {M : Subgroup (Aff K)} (hN : ∀ b, (⟨1, b⟩ : Aff K) ∈ M → b = 0)
    {n : SpecialLinearGroup (Fin 2) K} {β B : Matrix (Fin 2) (Fin 2) K} {a : K}
    (hn : (⟨n, β⟩ : Aff K) ∈ M) (hg : (⟨u2 a, B⟩ : Aff K) ∈ M)
    (h1 : (⟨u2 1, 0⟩ : Aff K) ∈ M) (hc : n * u2 a * n⁻¹ = u2 1) :
    β + (n : Matrix (Fin 2) (Fin 2) K) * B =
      ((u2 (1 : K) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * β := by
  have hx : (⟨n, β⟩ * ⟨u2 a, B⟩ * ⟨n, β⟩⁻¹ : Aff K) ∈ M :=
    M.mul_mem (M.mul_mem hn hg) (M.inv_mem hn)
  have hxm : (⟨n, β⟩ * ⟨u2 a, B⟩ * ⟨n, β⟩⁻¹ : Aff K).m = (⟨u2 1, 0⟩ : Aff K).m := by
    simpa using hc
  have h := uniq hN hx h1 hxm
  simp only [mul_b, mul_m, inv_b, Matrix.SpecialLinearGroup.coe_mul] at h
  have h2 : ((n : Matrix (Fin 2) (Fin 2) K) * (u2 a : Matrix (Fin 2) (Fin 2) K)) *
      (-((n⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * β) =
        -(((u2 (1 : K) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * β) := by
    rw [← hc]
    simp [Matrix.mul_assoc]
  rw [h2] at h
  exact add_neg_eq_zero.mp h

theorem lift_row {M : Subgroup (Aff K)} (hN : ∀ b, (⟨1, b⟩ : Aff K) ∈ M → b = 0)
    {s a x y : K} (hs : s ≠ 0) (hsa : s ^ 2 * a = 1) {β : Matrix (Fin 2) (Fin 2) K}
    (hn : (⟨kerDiag s hs, β⟩ : Aff K) ∈ M) (hg : (⟨u2 a, !![x, y; 0, 0]⟩ : Aff K) ∈ M)
    (h1 : (⟨u2 1, 0⟩ : Aff K) ∈ M) : β 1 0 = s * x ∧ β 1 1 = s * y := by
  have hc : kerDiag s hs * u2 a * (kerDiag s hs)⁻¹ = u2 1 := by
    rw [kerDiag_mul_u2_mul_inv, hsa]
  have h := conj_eq hN hn hg h1 hc
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp [kerDiag_coe, u2_coe, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  exact ⟨e00.symm, e01.symm⟩

theorem lift_comm {M : Subgroup (Aff K)} (hN : ∀ b, (⟨1, b⟩ : Aff K) ∈ M → b = 0)
    {s s' : K} (hs : s ≠ 0) (hs' : s' ≠ 0) {β β' : Matrix (Fin 2) (Fin 2) K}
    (hn : (⟨kerDiag s hs, β⟩ : Aff K) ∈ M) (hn' : (⟨kerDiag s' hs', β'⟩ : Aff K) ∈ M) :
    β + (kerDiag s hs : Matrix (Fin 2) (Fin 2) K) * β' =
      β' + (kerDiag s' hs' : Matrix (Fin 2) (Fin 2) K) * β := by
  have h := uniq hN (M.mul_mem hn hn') (M.mul_mem hn' hn) (by simp [kerDiag_comm s s' hs hs'])
  simpa using h

theorem kernel_line_of_ne [CharP K 2] {M : Subgroup (Aff K)}
    (hL : ∀ m : SpecialLinearGroup (Fin 2) K, ∃ β, (⟨m, β⟩ : Aff K) ∈ M)
    {b : Matrix (Fin 2) (Fin 2) K} (hb : (⟨1, b⟩ : Aff K) ∈ M) (hb0 : b ≠ 0) :
    ∃ β₀ β₁ : K, (β₀ ≠ 0 ∨ β₁ ≠ 0) ∧
      ∀ t : K, (⟨1, !![t * β₀, t * β₁; 0, 0]⟩ : Aff K) ∈ M := by
  have hconj : ∀ (m : SpecialLinearGroup (Fin 2) K) (c : Matrix (Fin 2) (Fin 2) K),
      (⟨1, c⟩ : Aff K) ∈ M → (⟨1, (m : Matrix (Fin 2) (Fin 2) K) * c⟩ : Aff K) ∈ M := by
    intro m c hc
    obtain ⟨β, hβ⟩ := hL m
    have := M.mul_mem (M.mul_mem hβ hc) (M.inv_mem hβ)
    rwa [conj_translation] at this
  have hadd : ∀ c c' : Matrix (Fin 2) (Fin 2) K, (⟨1, c⟩ : Aff K) ∈ M → (⟨1, c'⟩ : Aff K) ∈ M →
      (⟨1, c + c'⟩ : Aff K) ∈ M := fun c c' hc hc' => by
    rw [← mk_one_mul]
    exact M.mul_mem hc hc'
  have first : ∀ c : Matrix (Fin 2) (Fin 2) K, (⟨1, c⟩ : Aff K) ∈ M → (c 1 0 ≠ 0 ∨ c 1 1 ≠ 0) →
      ∃ β₀ β₁ : K, (β₀ ≠ 0 ∨ β₁ ≠ 0) ∧
        ∀ t : K, (⟨1, !![t * β₀, t * β₁; 0, 0]⟩ : Aff K) ∈ M := by
    intro c hc hne
    refine ⟨c 1 0, c 1 1, hne, fun t => ?_⟩
    have h := hadd _ _ hc (hconj (u2 t) c hc)
    have e : c + (u2 t : Matrix (Fin 2) (Fin 2) K) * c = !![t * c 1 0, t * c 1 1; 0, 0] := by
      rw [u2_mul_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← add_assoc, CharTwo.add_self_eq_zero]
    rwa [e] at h
  by_cases h : b 1 0 ≠ 0 ∨ b 1 1 ≠ 0
  · exact first b hb h
  · have h0 : b 1 0 = 0 := not_not.mp (not_or.mp h).1
    have h1 : b 1 1 = 0 := not_not.mp (not_or.mp h).2
    have hb' : b 0 0 ≠ 0 ∨ b 0 1 ≠ 0 := by
      by_contra hcon
      have h00 : b 0 0 = 0 := not_not.mp (not_or.mp hcon).1
      have h01 : b 0 1 = 0 := not_not.mp (not_or.mp hcon).2
      apply hb0
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, h00, h01]
    have hc := hadd _ _ hb (hconj (l2 1) b hb)
    have e : b + ((l2 (1 : K) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * b =
        !![0, 0; b 0 0, b 0 1] := by
      rw [l2_mul_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h0, h1, CharTwo.add_self_eq_zero]
    rw [e] at hc
    exact first _ hc (by simpa using hb')

theorem proj_eq_top [Finite K] [CharP K 2] {k : Subfield K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    (hk : ∀ x ∈ k, x = 0 ∨ x = 1) {δ a : K} (hδ : δ ≠ 0) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    {M : Subgroup (SpecialLinearGroup (Fin 2) K)} (h1 : u2 (1 : K) ∈ M) (h2 : l2 δ ∈ M)
    (h3 : u2 a ∈ M) : M = ⊤ := by
  refine sl2_eq_top_of_root_groups hp hp2 hK (a₁ := 1) (a₂ := a) (b₀ := δ) one_ne_zero ?_ hδ
    ?_ h2
  · intro hmem
    rw [div_one] at hmem
    rcases hk a hmem with h | h
    · exact ha0 h
    · exact ha1 h
  · intro c₁ hc₁ c₂ hc₂
    rcases hk c₁ hc₁ with rfl | rfl <;> rcases hk c₂ hc₂ with rfl | rfl
    · simp [u2_zero]
    · simpa using h3
    · simpa using h1
    · rw [one_mul, one_mul, u2_add]
      exact M.mul_mem h1 h3

theorem exists_translation_ne_zero [Finite K] [CharP K 2] {M : Subgroup (Aff K)}
    (hL : ∀ m : SpecialLinearGroup (Fin 2) K, ∃ β, (⟨m, β⟩ : Aff K) ∈ M)
    {δ a₂ a₃ : K} (hδ : δ ≠ 0) (ha : ¬ ((a₂ = 0 ∨ a₂ = 1) ∧ (a₃ = 0 ∨ a₃ = 1)))
    (h1 : (⟨u2 1, 0⟩ : Aff K) ∈ M)
    (h3 : (⟨u2 a₂, !![0, δ⁻¹; 0, 0]⟩ : Aff K) ∈ M)
    (h4 : (⟨u2 a₃, !![δ⁻¹, 0; 0, 0]⟩ : Aff K) ∈ M) :
    ∃ b : Matrix (Fin 2) (Fin 2) K, (⟨1, b⟩ : Aff K) ∈ M ∧ b ≠ 0 := by
  by_contra hcon
  have hN : ∀ b : Matrix (Fin 2) (Fin 2) K, (⟨1, b⟩ : Aff K) ∈ M → b = 0 := fun b hb =>
    by_contra fun hb0 => hcon ⟨b, hb, hb0⟩
  have ha₂ : a₂ ≠ 0 := by
    rintro rfl
    rw [u2_zero] at h3
    have := congrFun (congrFun (hN _ h3) 0) 1
    simp at this
    exact hδ this
  have ha₃ : a₃ ≠ 0 := by
    rintro rfl
    rw [u2_zero] at h4
    have := congrFun (congrFun (hN _ h4) 0) 0
    simp at this
    exact hδ this
  obtain ⟨s, hs, hsa⟩ := exists_sq_mul_eq_one ha₂
  obtain ⟨s', hs', hsa'⟩ := exists_sq_mul_eq_one ha₃
  obtain ⟨β, hβ⟩ := hL (kerDiag s hs)
  obtain ⟨β', hβ'⟩ := hL (kerDiag s' hs')
  obtain ⟨e10, e11⟩ := lift_row hN hs hsa hβ h3 h1
  obtain ⟨e10', e11'⟩ := lift_row hN hs' hsa' hβ' h4 h1
  have hcomm := lift_comm hN hs hs' hβ hβ'
  rw [kerDiag_mul_eq, kerDiag_mul_eq] at hcomm
  have c10 : β 1 0 + s⁻¹ * β' 1 0 = β' 1 0 + s'⁻¹ * β 1 0 := by
    simpa using congrFun (congrFun hcomm 1) 0
  have c11 : β 1 1 + s⁻¹ * β' 1 1 = β' 1 1 + s'⁻¹ * β 1 1 := by
    simpa using congrFun (congrFun hcomm 1) 1
  have hX : s' * δ⁻¹ ≠ 0 := mul_ne_zero hs' (inv_ne_zero hδ)
  have hY : s * δ⁻¹ ≠ 0 := mul_ne_zero hs (inv_ne_zero hδ)
  have hs1 : s⁻¹ = 1 :=
    mul_right_cancel₀ hX (by linear_combination c10 - (1 - s'⁻¹) * e10 - (s⁻¹ - 1) * e10')
  have hs1' : s'⁻¹ = 1 :=
    mul_right_cancel₀ hY (by linear_combination -c11 + (1 - s'⁻¹) * e11 + (s⁻¹ - 1) * e11')
  have hs2 : s = 1 := inv_eq_one.mp hs1
  have hs2' : s' = 1 := inv_eq_one.mp hs1'
  have ha₂1 : a₂ = 1 := by simpa [hs2] using hsa
  have ha₃1 : a₃ = 1 := by simpa [hs2'] using hsa'
  exact ha ⟨Or.inr ha₂1, Or.inr ha₃1⟩

end AffKernel

open Matrix CFSG.RankThree.PartOne.CTP in
theorem aff_kernel_line {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : Subfield K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hk : ∀ x ∈ k, x = 0 ∨ x = 1)
    {δ a₂ a₃ : K} (hδ : δ ≠ 0) (ha : ¬ ((a₂ = 0 ∨ a₂ = 1) ∧ (a₃ = 0 ∨ a₃ = 1)))
    (M : Subgroup (Aff K))
    (h1 : (⟨u2 1, 0⟩ : Aff K) ∈ M) (h2 : (⟨l2 δ, 0⟩ : Aff K) ∈ M)
    (h3 : (⟨u2 a₂, !![0, δ⁻¹; 0, 0]⟩ : Aff K) ∈ M)
    (h4 : (⟨u2 a₃, !![δ⁻¹, 0; 0, 0]⟩ : Aff K) ∈ M) :
    ∃ β₀ β₁ : K, (β₀ ≠ 0 ∨ β₁ ≠ 0) ∧ ∀ t : K, (⟨1, !![t * β₀, t * β₁; 0, 0]⟩ : Aff K) ∈ M := by
  have hp1 : u2 (1 : K) ∈ M.map Aff.proj := ⟨_, h1, rfl⟩
  have hpl : l2 δ ∈ M.map Aff.proj := ⟨_, h2, rfl⟩
  have hp2' : u2 a₂ ∈ M.map Aff.proj := ⟨_, h3, rfl⟩
  have hp3' : u2 a₃ ∈ M.map Aff.proj := ⟨_, h4, rfl⟩
  have htop : M.map Aff.proj = ⊤ := by
    by_cases hb : a₂ = 0 ∨ a₂ = 1
    · have hb' : ¬ (a₃ = 0 ∨ a₃ = 1) := fun hb' => ha ⟨hb, hb'⟩
      exact AffKernel.proj_eq_top hp hp2 hK hk hδ (not_or.mp hb').1 (not_or.mp hb').2 hp1 hpl hp3'
    · exact AffKernel.proj_eq_top hp hp2 hK hk hδ (not_or.mp hb).1 (not_or.mp hb).2 hp1 hpl hp2'
  have hL := AffKernel.exists_lift htop
  obtain ⟨b, hb, hb0⟩ := AffKernel.exists_translation_ne_zero hL hδ ha h1 h3 h4
  exact AffKernel.kernel_line_of_ne hL hb hb0

end CFSG.RankThree.PartOne.SEITZ2

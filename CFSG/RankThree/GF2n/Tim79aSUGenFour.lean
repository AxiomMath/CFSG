module

public import CFSG.RankThree.GF2n.Tim79aSUGenCriterion

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.ARS
  CFSG.LieType.BorelTits

variable {F : Type} [Field F]

theorem uForm_fin_four (σ : F ≃+* F) (x y : Fin 4 → F) :
    uForm σ x y = σ (x 0) * y 3 + σ (x 1) * y 2 + σ (x 2) * y 1 + σ (x 3) * y 0 := by
  rw [uForm_eq, Fin.sum_univ_four]
  rfl

theorem uTransLe_of_eq_uTrans {σ : F ≃+* F} {m : ℕ} (hσ : ∀ c, σ (σ c) = c)
    {L : Subgroup (SU σ m)} {u v w : Fin m → F} (hu : UTransLe L u) (hv : UTransLe L v)
    (huu : uForm σ u u = 0) {c : F} (hc : c + σ c = 0) (hw : w = v + (c * uForm σ u v) • u) :
    UTransLe L w :=
  hw ▸ uTransLe_uTrans hσ hu hv huu hc

variable [CharP F 2]

theorem uTransLe_four_aux {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {l : F} (hl : l + σ l = 1)
    {L : Subgroup (SU σ 4)} (ha : UTransLe L ![1, 0, 0, 0]) (hd : UTransLe L ![0, 0, 0, 1])
    (he : UTransLe L ![0, 1, 0, 0]) (hae : UTransLe L ![1, 1, 0, 0])
    (hv : UTransLe L ![0, 0, l, 1]) :
    UTransLe L ![0, 0, 1, 0] ∧ UTransLe L ![1, 0, 1, 0] ∧ UTransLe L ![1, 0, l, 0] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨N, hN⟩ : ∃ N, N = l * σ l := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, add_zero] at hl
    exact zero_ne_one hl
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact mul_ne_zero hl0 ((map_ne_zero σ).2 hl0)
  have hNN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN0
  have hσN : σ N = N := by rw [hN, map_mul, hσ, mul_comm]
  have hσNi : σ N⁻¹ = N⁻¹ := by rw [map_inv₀, hσN]
  have h1tr : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hNtr : N + σ N = 0 := by rw [hσN]; exact CharTwo.add_self_eq_zero N
  have hNitr : N⁻¹ + σ N⁻¹ = 0 := by rw [hσNi]; exact CharTwo.add_self_eq_zero N⁻¹
  have iso_a : uForm σ (![1, 0, 0, 0] : Fin 4 → F) ![1, 0, 0, 0] = 0 := by
    simp [uForm_fin_four]
  have iso_d : uForm σ (![0, 0, 0, 1] : Fin 4 → F) ![0, 0, 0, 1] = 0 := by
    simp [uForm_fin_four]
  have iso_e : uForm σ (![0, 1, 0, 0] : Fin 4 → F) ![0, 1, 0, 0] = 0 := by
    simp [uForm_fin_four]
  have iso_f : uForm σ (![0, 0, 1, 0] : Fin 4 → F) ![0, 0, 1, 0] = 0 := by
    simp [uForm_fin_four]
  have iso_ae : uForm σ (![1, 1, 0, 0] : Fin 4 → F) ![1, 1, 0, 0] = 0 := by
    simp [uForm_fin_four]
  have s1 : UTransLe L ![1 + l, 1 + l, l, 1] := by
    refine uTransLe_of_eq_uTrans hσ hae hv iso_ae h1tr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind
  have s2 : UTransLe L ![1 + l + N, 1 + l, l, 1] := by
    refine uTransLe_of_eq_uTrans hσ ha s1 iso_a hNtr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind
  have s3 : UTransLe L ![1, 1, 0, N⁻¹] := by
    refine uTransLe_of_eq_uTrans hσ hd hae iso_d hNitr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind
  have s4 : UTransLe L ![0, N * l, l, 1] := by
    refine uTransLe_of_eq_uTrans hσ he hv iso_e hNtr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind
  have iso_z : uForm σ (![1, 1, 0, N⁻¹] : Fin 4 → F) ![1, 1, 0, N⁻¹] = 0 := by
    simp only [uForm_fin_four]
    simp [hσNi]
    grind
  have s5 : UTransLe L ![N + N * l, N, l, l] := by
    refine uTransLe_of_eq_uTrans hσ s3 s4 iso_z hNtr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four, hσNi] <;> grind
  have iso_x : uForm σ (![1 + l + N, 1 + l, l, 1] : Fin 4 → F) ![1 + l + N, 1 + l, l, 1] = 0 := by
    simp only [uForm_fin_four]
    simp [hσN, hσ]
    grind
  have s6 : UTransLe L ![0, 0, N, 0] := by
    refine uTransLe_of_eq_uTrans hσ s2 s5 iso_x hNitr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four, hσN, hσ] <;> grind
  have hf : UTransLe L ![0, 0, 1, 0] := by
    refine uTransLe_of_smul hσ hN0 ?_
    convert s6 using 1
    ext i
    fin_cases i <;> simp
  refine ⟨hf, ?_, ?_⟩
  ·
    have t1 : UTransLe L ![1, 1, 1, 0] := by
      refine uTransLe_of_eq_uTrans hσ hf hae iso_f h1tr ?_
      ext i
      fin_cases i <;> simp [uForm_fin_four] <;> grind
    refine uTransLe_of_eq_uTrans hσ he t1 iso_e h1tr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind
  ·
    have t1 : UTransLe L ![1, 0, l, 1] := by
      refine uTransLe_of_eq_uTrans hσ ha hv iso_a h1tr ?_
      ext i
      fin_cases i <;> simp [uForm_fin_four] <;> grind
    refine uTransLe_of_eq_uTrans hσ hd t1 iso_d h1tr ?_
    ext i
    fin_cases i <;> simp [uForm_fin_four] <;> grind

@[expose] def SUFrameGen (σ : F ≃+* F) (m k : ℕ) : Prop :=
  ∃ U : List (Fin m → F), U.length ≤ k ∧ (∀ u ∈ U, u ≠ 0 ∧ uForm σ u u = 0) ∧
    ∀ L : Subgroup (SU σ m), (∀ u ∈ U, UTransLe L u) → L = ⊤

section Finite

variable [Finite F] {f : ℕ}

theorem eq_top_of_uTransLe_four (hF : Nat.card F = (2 ^ f) ^ 2) {l : F}
    (hl : l + unitaryInvolution F 2 f l = 1) {L : Subgroup (SU (unitaryInvolution F 2 f) 4)}
    (ha : UTransLe L ![1, 0, 0, 0]) (hd : UTransLe L ![0, 0, 0, 1])
    (he : UTransLe L ![0, 1, 0, 0]) (hae : UTransLe L ![1, 1, 0, 0])
    (hv : UTransLe L ![0, 0, l, 1]) : L = ⊤ := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨hf, haf, hal⟩ := uTransLe_four_aux hσ hl ha hd he hae hv
  have iso_a : uForm (unitaryInvolution F 2 f) (![1, 0, 0, 0] : Fin 4 → F) ![1, 0, 0, 0] = 0 := by
    simp [uForm_fin_four]
  have iso_d : uForm (unitaryInvolution F 2 f) (![0, 0, 0, 1] : Fin 4 → F) ![0, 0, 0, 1] = 0 := by
    simp [uForm_fin_four]
  have iso_e : uForm (unitaryInvolution F 2 f) (![0, 1, 0, 0] : Fin 4 → F) ![0, 1, 0, 0] = 0 := by
    simp [uForm_fin_four]
  have iso_f : uForm (unitaryInvolution F 2 f) (![0, 0, 1, 0] : Fin 4 → F) ![0, 0, 1, 0] = 0 := by
    simp [uForm_fin_four]
  have had : uForm (unitaryInvolution F 2 f) (![1, 0, 0, 0] : Fin 4 → F) ![0, 0, 0, 1] = 1 := by
    simp [uForm_fin_four]
  have hw₀ : (![0, 0, 1, 0] : Fin 4 → F) ∈
      perpPair (unitaryInvolution F 2 f) ![1, 0, 0, 0] ![0, 0, 0, 1] :=
    ⟨by simp [uForm_fin_four], by simp [uForm_fin_four]⟩
  have hw₀0 : (![0, 0, 1, 0] : Fin 4 → F) ≠ 0 := by
    intro h
    have := congrFun h 2
    simp at this
  have h1tr : (1 : F) + unitaryInvolution F 2 f 1 = 0 := by
    rw [map_one]; exact CharTwo.add_self_eq_zero 1
  refine eq_top_of_uTransLe_pair hF le_rfl iso_a iso_d had hw₀ hw₀0 iso_f ha hd ?_ ?_
  ·
    intro v hv hvv
    have hv3 : v 3 = 0 := by simpa [uForm_fin_four] using hv.1
    have hv0 : v 0 = 0 := by simpa [uForm_fin_four] using hv.2
    rw [uForm_fin_four, hv3, hv0] at hvv
    simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add] at hvv
    by_cases hv2 : v 2 = 0
    · have hveq : v = v 1 • (![0, 1, 0, 0] : Fin 4 → F) := by
        ext i
        fin_cases i <;> simp [hv0, hv2, hv3]
      rw [hveq]
      exact uTransLe_smul hσ he _
    · set c := v 1 / v 2 with hcdef
      have hσ2 : unitaryInvolution F 2 f (v 2) ≠ 0 := (map_ne_zero _).2 hv2
      have hσc : unitaryInvolution F 2 f c = c := by
        rw [hcdef, map_div₀, div_eq_div_iff hσ2 hv2]
        grind
      have hc : c + unitaryInvolution F 2 f c = 0 := by
        rw [hσc]; exact CharTwo.add_self_eq_zero c
      have ht := uTransLe_smul hσ (uTransLe_uTrans hσ he hf iso_e hc) (v 2)
      convert ht using 1
      ext i
      fin_cases i <;> simp [uForm_fin_four, hv0, hv3, hcdef] <;> field_simp
  ·
    intro ν
    obtain ⟨c₂, hc₂def⟩ : ∃ c : F, c = ν + unitaryInvolution F 2 f ν := ⟨_, rfl⟩
    obtain ⟨c₁, hc₁def⟩ : ∃ c : F, c = ν + c₂ * l := ⟨_, rfl⟩
    have hσc₂ : unitaryInvolution F 2 f c₂ = c₂ := by rw [hc₂def, map_add, hσ, add_comm]
    have hc₂ : c₂ + unitaryInvolution F 2 f c₂ = 0 := by
      rw [hσc₂]; exact CharTwo.add_self_eq_zero c₂
    have hc₁ : c₁ + unitaryInvolution F 2 f c₁ = 0 := by
      rw [hc₁def, map_add, map_mul, hσc₂]
      grind
    have haf' : UTransLe L (![1, 0, 0, 0] + (1 : F) • ![0, 0, 1, 0]) := by
      convert haf using 1
      ext i
      fin_cases i <;> simp
    have hal' : UTransLe L (![1, 0, 0, 0] + l • ![0, 0, 1, 0]) := by
      convert hal using 1
      ext i
      fin_cases i <;> simp
    have haw : uForm (unitaryInvolution F 2 f) (![1, 0, 0, 0] : Fin 4 → F) ![0, 0, 1, 0] = 0 := by
      simp [uForm_fin_four]
    obtain ⟨z₁, hz₁L, hz₁⟩ := exists_mem_eichler_of_uTransLe hσ iso_a iso_f haw ha hf haf' hc₁
    obtain ⟨z₂, hz₂L, hz₂⟩ := exists_mem_eichler_of_uTransLe hσ iso_a iso_f haw ha hf hal' hc₂
    obtain ⟨hz₁R, hz₁v⟩ := eichler_mem_uRad_radVec hσ iso_a iso_d had hw₀ hz₁
    obtain ⟨hz₂R, hz₂v⟩ := eichler_mem_uRad_radVec hσ iso_a iso_d had hw₀ hz₂
    refine ⟨z₁ * z₂, L.mul_mem hz₁L hz₂L, (uRad _ _).mul_mem hz₁R hz₂R, ?_⟩
    rw [radVec_mul_of_mem_uRad hσ iso_a iso_d had hz₁R hz₂R, hz₁v, hz₂v, ← add_smul]
    congr 1
    rw [hc₁def]
    grind

theorem suFrameGen_four (hF : Nat.card F = (2 ^ f) ^ 2) :
    SUFrameGen (unitaryInvolution F 2 f) 4 5 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨l, hl⟩ := exists_add_unitaryInvolution_eq hF (a := 1) (map_one _)
  refine ⟨[![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 0, l, 1]],
    by simp, ?_, fun L hL => ?_⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    all_goals refine ⟨fun h => ?_, ?_⟩
    all_goals first
      | (simp only [uForm_fin_four]; simp; done)
      | (simp only [uForm_fin_four]; simp; grind)
      | (have := congrFun h 0; simp at this; done)
      | (have := congrFun h 1; simp at this; done)
      | (have := congrFun h 3; simp at this; done)
  · exact eq_top_of_uTransLe_four hF hl (hL _ (by simp)) (hL _ (by simp)) (hL _ (by simp))
      (hL _ (by simp)) (hL _ (by simp))

end Finite

end CFSG.Timmesfeld.Transvection.ModelRank

module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.Quasithin.Background.B6Defs
import CFSG.Quasithin.EmptyFaithful.SBd6Tw

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace SBc7

section Centralizer

set_option maxRecDepth 100000 in
private theorem zmod2_cent_exact : ∀ σ A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
    σ ^ 3 = 1 → σ ≠ 1 → σ * A = A * σ → A = 1 ∨ A = σ ∨ A = σ ^ 2 := by
  decide +kernel

theorem cent_exact {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (σ A : Matrix.SpecialLinearGroup (Fin 3) F) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1)
    (hc : σ * A = A * σ) : A = 1 ∨ A = σ ∨ A = σ ^ 2 := by
  let f : Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    Matrix.SpecialLinearGroup.map (SBd6.eZ2 hF : F →+* ZMod 2)
  have hinj : Function.Injective f := SBd6.map_eZ2_injective hF
  rcases zmod2_cent_exact (f σ) (f A) (by rw [← map_pow, h3, map_one])
      (fun h => h1 (hinj (by rw [h, map_one]))) (by rw [← map_mul, ← map_mul, hc]) with
    h | h | h
  · exact Or.inl (hinj (by rw [h, map_one]))
  · exact Or.inr (Or.inl (hinj h))
  · exact Or.inr (Or.inr (hinj (by rw [h, map_pow])))

end Centralizer

section Sylow

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem isSylowTwoOf_unitriangular_three {F : Type} [Field F] [Finite F] [CharP F 2] :
    IsSylowTwoOf (unitriangular 3 F) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  rw [← hP]
  refine ⟨le_top, P.isPGroup', ?_⟩
  show ¬ 2 ∣ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact P.not_dvd_index

private theorem exists_unitriangular_sq_ne_one {F : Type} [Field F] :
    ∃ t ∈ unitriangular 3 F, t ^ 2 ≠ 1 := by
  have hdet : (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    simp [Matrix.det_fin_three]
  refine ⟨⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], hdet⟩, ?_, ?_⟩
  · refine mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> simp
  · intro h
    have hM : (!![1, 1, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) ^ 2 = 1 :=
      congrArg Subtype.val h
    rw [pow_two] at hM
    have h02 := congrFun (congrFun hM 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h02

theorem exists_sq_ne_one_of_sylow {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hT : IsSylowTwoOf T ⊤) :
    ∃ τ ∈ T, τ ^ 2 ≠ 1 := by
  have : CharP F 2 := charP_of_card_eq_prime hF
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj (isSylowTwoOf_unitriangular_three (F := F)) hT
  obtain ⟨t, ht, ht2⟩ := exists_unitriangular_sq_ne_one (F := F)
  refine ⟨g * t * g⁻¹, ?_, fun h => ht2 (conj_eq_one_iff.mp (by rw [← conj_pow]; exact h))⟩
  rw [hg, B6.mem_conjSub]
  simpa [mul_assoc] using ht

end Sylow

section Normalized

private theorem sq_eq_one_of_pow_six_eq_one {G : Type} [Group G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {τ : G} (hτ : τ ∈ T) (h6 : τ ^ 6 = 1) : τ ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨τ, hτ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk6 : 2 ^ k ∣ 6 := hk ▸ orderOf_dvd_of_pow_eq_one h6
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h46 := h4.trans hk6
    norm_num at h46
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [hk]
  simpa using pow_dvd_pow 2 hk1

theorem eq_one_of_centralizes {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {Y T : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ τ ∈ T, ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y)
    {σ : Matrix.SpecialLinearGroup (Fin 3) F} (hσY : σ ∈ Y) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {A : Matrix.SpecialLinearGroup (Fin 3) F} (hA : ∀ y ∈ Y, y * A = A * y) : A = 1 := by
  by_contra hA1
  have hσinv : σ ^ 2 = σ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact hσ3
  have hAσ : A = σ ∨ A = σ⁻¹ := by
    rcases cent_exact hF σ A hσ3 hσ1 (hA σ hσY) with h | h | h
    · exact absurd h hA1
    · exact Or.inl h
    · exact Or.inr (h.trans hσinv)
  have hcσ : ∀ B : Matrix.SpecialLinearGroup (Fin 3) F, A * B = B * A → σ * B = B * σ := by
    intro B hB
    rcases hAσ with h | h
    · rw [h] at hB
      exact hB
    · rw [h] at hB
      exact (Commute.inv_left_iff (a := σ) (b := B)).mp hB
  have hsq : ∀ τ ∈ T, τ ^ 2 = 1 := by
    intro τ hτ
    have hB : ∀ y ∈ Y, y * (τ * A * τ⁻¹) = (τ * A * τ⁻¹) * y := by
      intro y hy
      have hy' : τ⁻¹ * y * τ ∈ Y := by simpa using hN τ⁻¹ (T.inv_mem hτ) y hy
      have h := hA _ hy'
      calc y * (τ * A * τ⁻¹) = τ * (τ⁻¹ * y * τ * A) * τ⁻¹ := by group
        _ = τ * (A * (τ⁻¹ * y * τ)) * τ⁻¹ := by rw [h]
        _ = (τ * A * τ⁻¹) * y := by group
    have hBne : τ * A * τ⁻¹ ≠ 1 := fun h => hA1 (conj_eq_one_iff.mp h)
    have hBσ : τ * A * τ⁻¹ = σ ∨ τ * A * τ⁻¹ = σ⁻¹ := by
      rcases cent_exact hF σ _ hσ3 hσ1 (hB σ hσY) with h | h | h
      · exact absurd h hBne
      · exact Or.inl h
      · exact Or.inr (h.trans hσinv)
    have hAB : τ * A * τ⁻¹ = A ∨ τ * A * τ⁻¹ = A⁻¹ := by
      rcases hAσ with hA' | hA' <;> rcases hBσ with hB' | hB'
      · exact Or.inl (hB'.trans hA'.symm)
      · exact Or.inr (hB'.trans (by rw [hA']))
      · exact Or.inr (hB'.trans (by rw [hA', inv_inv]))
      · exact Or.inl (hB'.trans hA'.symm)
    have hτA : τ * τ * A * (τ * τ)⁻¹ = A := by
      rcases hAB with h | h
      · calc τ * τ * A * (τ * τ)⁻¹ = τ * (τ * A * τ⁻¹) * τ⁻¹ := by group
          _ = A := by rw [h, h]
      · calc τ * τ * A * (τ * τ)⁻¹ = τ * (τ * A * τ⁻¹) * τ⁻¹ := by group
          _ = τ * A⁻¹ * τ⁻¹ := by rw [h]
          _ = (τ * A * τ⁻¹)⁻¹ := by group
          _ = A := by rw [h, inv_inv]
    have hτA' : A * τ ^ 2 = τ ^ 2 * A := by
      rw [pow_two]
      exact (mul_inv_eq_iff_eq_mul.mp hτA).symm
    have h6 : τ ^ 6 = 1 := by
      have h2 : (τ ^ 2) ^ 3 = 1 := by
        rcases cent_exact hF σ (τ ^ 2) hσ3 hσ1 (hcσ _ hτA') with h | h | h
        · rw [h, one_pow]
        · rw [h, hσ3]
        · rw [h, pow_right_comm, hσ3, one_pow]
      rw [← pow_mul] at h2
      exact h2
    exact sq_eq_one_of_pow_six_eq_one hT.2.1 hτ h6
  obtain ⟨τ, hτT, hτ2⟩ := exists_sq_ne_one_of_sylow hF hT
  exact hτ2 (hsq τ hτT)

end Normalized

end SBc7

end CFSG.Quasithin

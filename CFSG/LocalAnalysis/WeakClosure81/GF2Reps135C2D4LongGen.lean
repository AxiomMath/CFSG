module

public import CFSG.Quasithin.Background.SmithB42D4Main
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4Basis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4LongConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42D4

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

local notation "Xr" => pinnedX TwistTag.D4.tag K
local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom

include hf hK hσ in
theorem trialityLongRoot_gen :
    ∃ T : Finset (ModGL TwistTag.D4.tag K), T.card ≤ 7 * f ∧
      (∀ y ∈ T, ConjC σ (Xr d4H 1) y) ∧
      C₀ ≤ Subgroup.closure (T : Set (ModGL TwistTag.D4.tag K)) := by
  classical
  haveI := charP_two_of_card hf hK
  have hσ3 := sigma_cube hK σ hσ
  have hk := card_fixedField hf hK σ hσ
  obtain ⟨t₁, t₂, t₃, hspan⟩ := exists_spanning hf hK σ hσ
  have hσ1 := exists_sigma_ne hf hK σ hσ
  obtain ⟨b, hbσ, hb0, hbcl⟩ := exists_fixedField_basis σ hk
  let gi : Fin 3 → K := ![t₁, t₂, t₃]
  let y₁ : Fin f → ModGL TwistTag.D4.tag K := fun j => Xr d4H (b j)
  let y₂ : Fin f → ModGL TwistTag.D4.tag K := fun j => Xr d4P (b j)
  let y₃ : Fin f → ModGL TwistTag.D4.tag K := fun j => nW0 K * Xr d4P (b j) * (nW0 K)⁻¹
  let y₄ : Fin f → ModGL TwistTag.D4.tag K := fun j => nW0 K * Xr d4H (b j) * (nW0 K)⁻¹
  let z : Fin 3 → Fin f → ModGL TwistTag.D4.tag K := fun i j =>
    (ox₁ σ (gi i) * nA K) * Xr d4P (b j) * (ox₁ σ (gi i) * nA K)⁻¹
  let A : Finset (ModGL TwistTag.D4.tag K) := Finset.univ.image y₁
  let B : Finset (ModGL TwistTag.D4.tag K) := Finset.univ.image y₂
  let C : Finset (ModGL TwistTag.D4.tag K) := Finset.univ.image y₃
  let D : Finset (ModGL TwistTag.D4.tag K) := Finset.univ.image y₄
  let E : Finset (ModGL TwistTag.D4.tag K) :=
    Finset.univ.image (fun p : Fin 3 × Fin f => z p.1 p.2)
  let T : Finset (ModGL TwistTag.D4.tag K) := ((((A ∪ B) ∪ C) ∪ D) ∪ E)
  have hTdef : T = ((((A ∪ B) ∪ C) ∪ D) ∪ E) := rfl
  have hcard : T.card ≤ 7 * f := by
    have hA : A.card ≤ f := by
      dsimp only [A]
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin f))) (f := y₁))
    have hB : B.card ≤ f := by
      dsimp only [B]
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin f))) (f := y₂))
    have hC : C.card ≤ f := by
      dsimp only [C]
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin f))) (f := y₃))
    have hD : D.card ≤ f := by
      dsimp only [D]
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin f))) (f := y₄))
    have hE : E.card ≤ 3 * f := by
      dsimp only [E]
      calc (Finset.univ.image (fun p : Fin 3 × Fin f => z p.1 p.2)).card
          ≤ (Finset.univ : Finset (Fin 3 × Fin f)).card := Finset.card_image_le
        _ = 3 * f := by simp [Fintype.card_prod]
    rw [hTdef]
    have h1 := Finset.card_union_le (((A ∪ B) ∪ C) ∪ D) E
    have h2 := Finset.card_union_le ((A ∪ B) ∪ C) D
    have h3 := Finset.card_union_le (A ∪ B) C
    have h4 := Finset.card_union_le A B
    omega
  have hconj : ∀ y ∈ T, ConjC σ (Xr d4H 1) y := by
    intro y hy
    rw [hTdef] at hy
    dsimp only [A, B, C, D, E] at hy
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, or_assoc] at hy
    rcases hy with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨p, rfl⟩
    · exact trialityLongRoot_conj_H σ hσ3 (hbσ j) (hb0 j)
    · exact trialityLongRoot_conj_P σ hσ3 (hbσ j) (hb0 j)
    · exact trialityLongRoot_conj_nW0P σ hσ3 (hbσ j) (hb0 j)
    · exact trialityLongRoot_conj_nW0H σ hσ3 (hbσ j) (hb0 j)
    · exact trialityLongRoot_conj_line σ hσ3 (hbσ p.2) (hb0 p.2) (gi p.1)
  refine ⟨T, hcard, hconj, ?_⟩
  let H : Subgroup (ModGL TwistTag.D4.tag K) := Subgroup.closure (T : Set _)
  have hTsub : ∀ x ∈ T, x ∈ H := fun x hx => Subgroup.subset_closure hx
  have memT1 : ∀ j, y₁ j ∈ T := fun j => by
    rw [hTdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))))
  have memT2 : ∀ j, y₂ j ∈ T := fun j => by
    rw [hTdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))))
  have memT3 : ∀ j, y₃ j ∈ T := fun j => by
    rw [hTdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)))
  have memT4 : ∀ j, y₄ j ∈ T := fun j => by
    rw [hTdef]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  have memTz : ∀ i j, z i j ∈ T := fun i j => by
    rw [hTdef]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  have hP : ∀ e : K, σ e = e → Xr d4P e ∈ H := fun e he =>
    family_mem_of_closure (X := fun e => Xr d4P e)
      (fun a c => pinnedX_add TwistTag.D4.tag K d4P a c) H
      (fun a ha => by rcases ha with ⟨j, rfl⟩; exact hTsub _ (memT2 j)) (hbcl e he)
  have hH : ∀ x : K, σ x = x → Xr d4H x ∈ H := fun x hx =>
    family_mem_of_closure (X := fun x => Xr d4H x)
      (fun a c => pinnedX_add TwistTag.D4.tag K d4H a c) H
      (fun a ha => by rcases ha with ⟨j, rfl⟩; exact hTsub _ (memT1 j)) (hbcl x hx)
  have hΛ : ∀ e x : K, σ e = e → σ x = x → Xr d4P e * Xr d4H x ∈ H :=
    fun e x he hx => H.mul_mem (hP e he) (hH x hx)
  have hP0 : ∀ e : K, σ e = e → nW0 K * Xr d4P e * (nW0 K)⁻¹ ∈ H := fun e he =>
    family_mem_of_closure (X := fun e => nW0 K * Xr d4P e * (nW0 K)⁻¹)
      (fun a c => by rw [pinnedX_add TwistTag.D4.tag K d4P a c]; group) H
      (fun a ha => by rcases ha with ⟨j, rfl⟩; exact hTsub _ (memT3 j)) (hbcl e he)
  have hH0 : ∀ x : K, σ x = x → nW0 K * Xr d4H x * (nW0 K)⁻¹ ∈ H := fun x hx =>
    family_mem_of_closure (X := fun x => nW0 K * Xr d4H x * (nW0 K)⁻¹)
      (fun a c => by rw [pinnedX_add TwistTag.D4.tag K d4H a c]; group) H
      (fun a ha => by rcases ha with ⟨j, rfl⟩; exact hTsub _ (memT4 j)) (hbcl x hx)
  have hΛ₀ : ∀ e x : K, σ e = e → σ x = x →
      nW0 K * (Xr d4P e * Xr d4H x) * (nW0 K)⁻¹ ∈ H := by
    intro e x he hx
    rw [show nW0 K * (Xr d4P e * Xr d4H x) * (nW0 K)⁻¹ =
        (nW0 K * Xr d4P e * (nW0 K)⁻¹) * (nW0 K * Xr d4H x * (nW0 K)⁻¹) from by group]
    exact H.mul_mem (hP0 e he) (hH0 x hx)
  have hPi : ∀ i : Fin 3, ∀ e : K, σ e = e →
      (ox₁ σ (gi i) * nA K) * Xr d4P e * (ox₁ σ (gi i) * nA K)⁻¹ ∈ H := fun i e he =>
    family_mem_of_closure
      (X := fun e => (ox₁ σ (gi i) * nA K) * Xr d4P e * (ox₁ σ (gi i) * nA K)⁻¹)
      (fun a c => by rw [pinnedX_add TwistTag.D4.tag K d4P a c]; group) H
      (fun a ha => by rcases ha with ⟨j, rfl⟩; exact hTsub _ (memTz i j)) (hbcl e he)
  have hΛᵢ : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ e x : K, σ e = e → σ x = x →
      (ox₁ σ t * nA K) * (Xr d4P e * Xr d4H x) * (ox₁ σ t * nA K)⁻¹ ∈ H := by
    intro t ht e x he hx
    have hA : (ox₁ σ t * nA K) * Xr d4P e * (ox₁ σ t * nA K)⁻¹ ∈ H := by
      rw [Set.mem_insert_iff] at ht
      rcases ht with h | ht
      · subst h; exact hPi 0 e he
      · rw [Set.mem_insert_iff] at ht
        rcases ht with h | ht
        · subst h; exact hPi 1 e he
        · rw [Set.mem_singleton_iff] at ht
          subst ht; exact hPi 2 e he
    have hB : (ox₁ σ t * nA K) * Xr d4H x * (ox₁ σ t * nA K)⁻¹ ∈ H := by
      rw [trialityLine_conj_H σ hσ3 t x]; exact hH x hx
    rw [show (ox₁ σ t * nA K) * (Xr d4P e * Xr d4H x) * (ox₁ σ t * nA K)⁻¹ =
        ((ox₁ σ t * nA K) * Xr d4P e * (ox₁ σ t * nA K)⁻¹) *
        ((ox₁ σ t * nA K) * Xr d4H x * (ox₁ σ t * nA K)⁻¹) from by group]
    exact H.mul_mem hA hB
  exact five_lines_generate σ hσ3 hσ1 hspan hΛ hΛ₀ hΛᵢ

end CFSG.LocalAnalysis.WeakClosure81

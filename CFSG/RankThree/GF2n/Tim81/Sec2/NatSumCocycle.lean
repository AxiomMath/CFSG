module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5
import CFSG.CGT.PushingUpLit.T2KR.MMCoord
public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups

open Matrix
open CFSG.Quasithin.JonesParshall
open CFSG.CGT.Timmesfeld75

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

private theorem uMat_eq_utriElt (t : F) : uMat t = (utriElt t : SL(2, F)) := rfl

private theorem conj_cocycle_mem_Z1A {k : ℕ} {σ : Representation (ZMod 2) SL(2, F) N}
    {f : SL(2, F) → N} (hf : ∀ g h, f (g * h) = f g + σ g (f h)) (x : SL(2, F))
    (i : Fin k) (φ : N ≃+ (Fin k → Fin 2 → F))
    (hφ : ∀ g w i, φ (σ g w) i = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ φ w i) :
    (fun g => mu2 x⁻¹ (φ (f (x * g * x⁻¹)) i)) ∈ Z1A (mu2 (F := F)) := by
  rw [mem_Z1A]
  intro g h
  set a := x * g * x⁻¹
  set b := x * h * x⁻¹
  have hgh : x * (g * h) * x⁻¹ = a * b := by simp only [a, b]; group
  rw [hgh, hf]
  have h1 : φ (f a + σ a (f b)) i = φ (f a) i + φ (σ a (f b)) i := by
    rw [map_add, Pi.add_apply]
  have h2 : φ (σ a (f b)) i = mu2 a (φ (f b) i) :=
    (hφ a (f b) i).trans (mu2_apply a (φ (f b) i))
  have h3 : mu2 x⁻¹ (mu2 a (φ (f b) i)) = mu2 (g * x⁻¹) (φ (f b) i) := by
    change (mu2 x⁻¹ * mu2 a) (φ (f b) i) = mu2 (g * x⁻¹) (φ (f b) i)
    rw [← map_mul]
    congr 1
    simp only [a]
    group
  rw [h1, h2, map_add, h3, map_mul]
  rfl

private theorem eval_uMat {f' : SL(2, F) → Fin 2 → F} {B : F} {m : Fin 2 → F}
    (h : f' = B • f0 + coboundaryA (mu2 (F := F)) m) (t : F) :
    f' (uMat t) = ![B * sqrtF t + t * m 1, 0] := by
  have hmv : mu2 (uMat t) m = ![m 0 + t * m 1, m 1] := by
    funext i
    fin_cases i <;>
      simp [mu2_apply, mulVec_two_zero, mulVec_two_one, uMat_coe]
  rw [h, Pi.add_apply, Pi.smul_apply, f0_uMat, coboundaryA_apply, hmv]
  funext i
  fin_cases i <;>
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, smul_eq_mul] <;>
    ring

private theorem eq_zero_on_utri_of_eq_zero_on_subgroup {f' : SL(2, F) → Fin 2 → F}
    (hf' : f' ∈ Z1A (mu2 (F := F))) {a : ℕ} (hF : Fintype.card F = 2 ^ a) (ha : 1 < a)
    {T : Subgroup SL(2, F)} (hT : T ≤ utri F) (hTcard : 2 < Nat.card T)
    (hTvan : ∀ g ∈ T, f' g = 0) : ∀ t : F, f' (uMat t) = 0 := by
  classical
  have hcard : 2 < Fintype.card T := by rwa [Nat.card_eq_fintype_card] at hTcard
  have herase : 1 < ((Finset.univ : Finset T).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ]
    omega
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ := Finset.one_lt_card.mp herase
  have hg₁1 : g₁ ≠ 1 := (Finset.mem_erase.mp hg₁).1
  have hg₂1 : g₂ ≠ 1 := (Finset.mem_erase.mp hg₂).1
  obtain ⟨t₁, ht₁⟩ := mem_utri_iff.mp (hT g₁.2)
  obtain ⟨t₂, ht₂⟩ := mem_utri_iff.mp (hT g₂.2)
  have ht₁0 : t₁ ≠ 0 := by
    intro h0
    refine hg₁1 (Subtype.ext ?_)
    rw [ht₁, h0, utriElt_zero]
    rfl
  have ht₂0 : t₂ ≠ 0 := by
    intro h0
    refine hg₂1 (Subtype.ext ?_)
    rw [ht₂, h0, utriElt_zero]
    rfl
  have htne : t₁ ≠ t₂ := by
    intro h
    refine hne (Subtype.ext ?_)
    rw [ht₁, ht₂, h]
  have hvan₁ : f' (uMat t₁) = 0 := by
    rw [uMat_eq_utriElt, ← ht₁]
    exact hTvan g₁ g₁.2
  have hvan₂ : f' (uMat t₂) = 0 := by
    rw [uMat_eq_utriElt, ← ht₂]
    exact hTvan g₂ g₂.2
  obtain ⟨B, hB⟩ := exists_sub_mem_B1A hF ha hf'
  obtain ⟨m, hm⟩ := hB
  have hrepr : f' = B • f0 + coboundaryA (mu2 (F := F)) m := by
    rw [hm]
    abel
  have heq := eval_uMat hrepr
  have hroot₁ : t₁ * m 1 + B * sqrtF t₁ = 0 := by
    have h := congrFun (hvan₁.symm.trans (heq t₁)) 0
    simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
    rw [add_comm]
    exact h.symm
  have hroot₂ : t₂ * m 1 + B * sqrtF t₂ = 0 := by
    have h := congrFun (hvan₂.symm.trans (heq t₂)) 0
    simp only [Pi.zero_apply, Matrix.cons_val_zero] at h
    rw [add_comm]
    exact h.symm
  obtain ⟨hm1, hB0⟩ :=
    CFSG.CGT.PushingUpLit.T2KR.two_roots_algebra ht₁0 ht₂0 htne hroot₁ hroot₂
  intro t
  rw [heq t, hm1, hB0]
  funext i
  fin_cases i <;> simp

theorem IsNatSumModule.cocycle_eq_zero_of_le {σ : Representation (ZMod 2) SL(2, F) N}
    (hσ : IsNatSumModule σ) {a : ℕ}
    (hF : Fintype.card F = 2 ^ a) (ha : 1 < a) {f : SL(2, F) → N}
    (hf : ∀ g h, f (g * h) = f g + σ g (f h)) {A A₁ : Subgroup SL(2, F)}
    (hA2 : ∀ x ∈ A, x * x = 1) (hA : Nat.card A = Fintype.card F) (hA₁A : A₁ ≤ A)
    (hA₁ : 2 < Nat.card A₁) (hf₁ : ∀ x ∈ A₁, f x = 0) : ∀ x ∈ A, f x = 0 := by
  classical
  obtain ⟨k, φ, hφ⟩ := hσ
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  have hTle : conjSubgroup x⁻¹ A₁ ≤ utri F := by
    intro g hg
    have h1 : x * g * x⁻¹ ∈ A₁ := by simpa using (mem_conjSubgroup.mp hg)
    have h2 : x * g * x⁻¹ ∈ conjSubgroup x (utri F) := by
      rw [← hAx]
      exact hA₁A h1
    have h3 := mem_conjSubgroup.mp h2
    rwa [show x⁻¹ * (x * g * x⁻¹) * x = g by group] at h3
  have hTcard : 2 < Nat.card (conjSubgroup x⁻¹ A₁) := by
    show 2 < Nat.card (A₁.map (MulAut.conj x⁻¹).toMonoidHom)
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hA₁
  have hvan : ∀ i : Fin k, ∀ t : F,
      mu2 x⁻¹ (φ (f (x * uMat t * x⁻¹)) i) = 0 := by
    intro i
    refine eq_zero_on_utri_of_eq_zero_on_subgroup (f' := fun g =>
      mu2 x⁻¹ (φ (f (x * g * x⁻¹)) i)) ?_ hF ha hTle hTcard ?_
    · exact conj_cocycle_mem_Z1A hf x i φ hφ
    · intro g hg
      have h1 : x * g * x⁻¹ ∈ A₁ := by simpa using (mem_conjSubgroup.mp hg)
      simp [hf₁ _ h1]
  intro y hy
  have hy' : x⁻¹ * y * x ∈ utri F := mem_conjSubgroup.mp (hAx ▸ hy)
  obtain ⟨t, ht⟩ := mem_utri_iff.mp hy'
  have hyeq : y = x * uMat t * x⁻¹ := by
    rw [show y = x * (x⁻¹ * y * x) * x⁻¹ by group, ht, uMat_eq_utriElt]
  have hφ0 : φ (f y) = 0 := by
    funext i
    have h := hvan i t
    rw [← hyeq] at h
    have hxx : mu2 x (mu2 x⁻¹ (φ (f y) i)) = φ (f y) i := by
      change (mu2 x * mu2 x⁻¹) (φ (f y) i) = φ (f y) i
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    calc φ (f y) i = mu2 x (mu2 x⁻¹ (φ (f y) i)) := hxx.symm
      _ = mu2 x 0 := by rw [h]
      _ = 0 := map_zero _
  exact φ.injective (by rw [hφ0, map_zero])

end CFSG.RankThree.GF2n.Tim81.Sec2


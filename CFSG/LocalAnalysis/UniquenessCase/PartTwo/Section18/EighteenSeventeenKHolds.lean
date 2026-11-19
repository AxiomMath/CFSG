module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Norm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NormIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Matrix CFSG.Open Subgroup CFSG.Quasithin
open CFSG.LocalAnalysis.RankThreeUC

theorem k_K_SU4_minComm_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      2 ≤ n → IsSUn ↥H 4 n → NatSUn H ⊤ ⊥ 4 n →
        ∀ t : MulAut W, t ∈ Subgroup.normalizer (H : Set (MulAut W)) →
          (∃ k : ℕ, orderOf t = 2 ^ k) → t ≠ 1 →
            2 ^ (2 * n) * Nat.card (fixV (Subgroup.zpowers t)) ≤ Nat.card W := by
  intro W _ _ H n hn2 _hSUn hNat t htN _ht2 htne
  classical
  obtain ⟨F, _, _, hFcard, ε, ψ, hψ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_natCoords_of_natSUn hNat
  let e : W ≃ (Fin 4 → F) := ψ.toEquiv.trans Multiplicative.toAdd
  have he_mul : ∀ a b : W, e (a * b) = e a + e b := fun a b => by
    simp [e, toAdd_mul]
  let α : (Fin 4 → F) ≃+ (Fin 4 → F) :=
    { toFun := fun x => e (t (e.symm x))
      invFun := fun x => e (t⁻¹ (e.symm x))
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun x y => by
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        simp only [Equiv.symm_apply_apply]
        rw [← he_mul a b, Equiv.symm_apply_apply, map_mul, he_mul] }
  have hαsymm : ∀ x : Fin 4 → F, α.symm x = e (t⁻¹ (e.symm x)) := fun x => rfl
  have hαapply : ∀ x : W, α (e x) = e (t x) := fun x => by
    show e (t (e.symm (e x))) = e (t x)
    simp
  have hcoord : ∀ (l : ↥H) (s : W),
      e ((l : MulAut W) s) =
        ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := by
    intro l s
    have h := hψ l s
    calc e ((l : MulAut W) s)
        = Multiplicative.toAdd (ψ ((l : MulAut W) s)) := rfl
      _ = Multiplicative.toAdd (Multiplicative.ofAdd
            (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
              Multiplicative.toAdd (ψ s))) := by rw [h]
      _ = ((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ e s := rfl
  have hsem : ∃ θ : F →+* F, ∀ (c : F) (x : Fin 4 → F), α (c • x) = θ c • α x := by
    refine CFSG.LocalAnalysis.RankThreeUC.exists_semilinear_statedSU hFcard α ?_
    intro g hg
    let ℓ : ↥H := ε.symm ⟨g, hg⟩
    have hmem : t⁻¹ * (ℓ : MulAut W) * t ∈ H := by
      refine (Subgroup.mem_normalizer_iff.1 htN (t⁻¹ * (ℓ : MulAut W) * t)).2 ?_
      have hcalc : t * (t⁻¹ * (ℓ : MulAut W) * t) * t⁻¹ = (ℓ : MulAut W) := by group
      rw [hcalc]
      exact ℓ.2
    let h' : ↥H := ⟨t⁻¹ * (ℓ : MulAut W) * t, hmem⟩
    refine ⟨((ε h' : ↥(StatedSU 4 (2 ^ n) F)) : GL (Fin 4) F), (ε h').2, ?_⟩
    intro x
    calc α.symm (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x)
        = e (t⁻¹ (e.symm (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x))) :=
            hαsymm _
      _ = e (t⁻¹ ((ℓ : MulAut W) (e.symm x))) := by
            congr 2
            have hgx : (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x) =
                e ((ℓ : MulAut W) (e.symm x)) := by
              have hc := hcoord ℓ (e.symm x)
              rw [MulEquiv.apply_symm_apply] at hc
              simpa using hc.symm
            rw [hgx, Equiv.symm_apply_apply]
      _ = e ((t⁻¹ * (ℓ : MulAut W) * t) (t⁻¹ (e.symm x))) := by
            congr 1
            simp [MulAut.mul_apply]
      _ = e (((h' : ↥H) : MulAut W) (t⁻¹ (e.symm x))) := rfl
      _ = ((ε h' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ
            e (t⁻¹ (e.symm x)) := hcoord h' (t⁻¹ (e.symm x))
      _ = ((ε h' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ α.symm x := by
            rw [hαsymm]
  obtain ⟨θ, hθ⟩ := hsem
  have hne : ∃ x : Fin 4 → F, α x ≠ x := by
    obtain ⟨w, hw⟩ : ∃ w : W, t w ≠ w := by
      by_contra h
      push Not at h
      exact htne (MulEquiv.ext h)
    refine ⟨e w, ?_⟩
    rw [hαapply]
    intro hx
    exact hw (e.injective hx)
  have hmain := CFSG.LocalAnalysis.RankThreeUC.card_fix_mul_le α hθ hne
  have hcardfix : Nat.card (fixV (Subgroup.zpowers t)) =
      Nat.card {x : Fin 4 → F // α x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e ?_)
    intro w
    show w ∈ fixV (Subgroup.zpowers t) ↔ α (e w) = e w
    rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply, hαapply, e.injective.eq_iff]
  have hcardW : Nat.card W = Nat.card (Fin 4 → F) := Nat.card_congr e
  have hpow : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  calc 2 ^ (2 * n) * Nat.card (fixV (Subgroup.zpowers t))
      = Nat.card F * Nat.card {x : Fin 4 → F // α x = x} := by
          rw [hpow, ← hFcard, hcardfix]
    _ = Nat.card {x : Fin 4 → F // α x = x} * Nat.card F := mul_comm _ _
    _ ≤ Nat.card (Fin 4 → F) := hmain
    _ = Nat.card W := hcardW.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

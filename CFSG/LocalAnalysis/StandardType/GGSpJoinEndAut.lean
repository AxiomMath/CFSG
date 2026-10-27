module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]

private theorem spLeviBlock_twice_elt_zero {k : ℕ} (c : F) :
    spLeviBlock (k + 2) F (spLeviBlock (k + 1) F
        (elt (RootSubgroupIndex.positiveLong (0 : Fin (k + 1))) c)) =
      elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c := by
  rw [spLeviBlock_elt, spLeviBlock_elt]
  rfl

private theorem single_eq_smul_single {N : Type} [DecidableEq N] (i j : N) (x : F) :
    Matrix.single i j x = x • Matrix.single i j (1 : F) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem spEnd_exists_conj_lam_lam_of_embeddings {k : ℕ} (hk : 1 ≤ k)
    (ρ φ : StatedSp (k + 2 + 1) F →* G) (hρ : Function.Injective ρ) (hφ : Function.Injective φ)
    (hr : ρ.range = φ.range) {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    (h0 : ρ (lam (0 : Fin (k + 2 + 1)) g) = φ (lam (0 : Fin (k + 2 + 1)) g))
    (h1 : ρ (lam (1 : Fin (k + 2 + 1)) g) = φ (lam (1 : Fin (k + 2 + 1)) g))
    (hM : ∀ h : StatedSp (k + 1) F,
      ρ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) =
        φ (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h))) :
    ∃ s t : SpecialLinearGroup (Fin 2) F, s * g = g * s ∧ t * g = g * t ∧
      ∀ w, ρ w = φ ((lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) * w *
        (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t)⁻¹) := by
  let e : StatedSp (k + 2 + 1) F ≃* φ.range := MonoidHom.ofInjective hφ
  let e' : StatedSp (k + 2 + 1) F ≃* ρ.range := MonoidHom.ofInjective hρ
  let α : MulAut (StatedSp (k + 2 + 1) F) := (e'.trans (MulEquiv.subgroupCongr hr)).trans e.symm
  have hα : ∀ w, φ (α w) = ρ w := fun w => by
    have h1' : ((e (α w) : φ.range) : G) = φ (α w) := MonoidHom.ofInjective_apply hφ
    have h2' : e (α w) = MulEquiv.subgroupCongr hr (e' w) := MulEquiv.apply_symm_apply e _
    have h3' : ((e' w : ρ.range) : G) = ρ w := MonoidHom.ofInjective_apply hρ
    rw [← h1', h2', ← h3']
    rfl
  obtain ⟨B, σ, hB⟩ := exists_spConj_fieldSp_of_mulAut (r := k + 2 + 1) (K := F) (by omega) α
  have hfix : ∀ w, ρ w = φ w → α w = w := fun w hw => hφ (by rw [hα w, hw])
  have hfix0 : α (lam (0 : Fin (k + 2 + 1)) g) = lam (0 : Fin (k + 2 + 1)) g := hfix _ h0
  have hfix1 : α (lam (1 : Fin (k + 2 + 1)) g) = lam (1 : Fin (k + 2 + 1)) g := hfix _ h1
  have hfixM : ∀ h : StatedSp (k + 1) F,
      α (spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h)) =
        spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) := fun h => hfix _ (hM h)
  have hσ : σ = 1 := by
    have hmat : ∀ c : F,
        (σ c) • (mat (k + 2 + 1) F B *
            Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1) =
          c • (Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1 *
            mat (k + 2 + 1) F B) := by
      intro c
      have hfixE : α (elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c) =
          elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c := by
        have h := hfixM (elt (RootSubgroupIndex.positiveLong (0 : Fin (k + 1))) c)
        rwa [spLeviBlock_twice_elt_zero] at h
      have heq : B * elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) (σ c) * B⁻¹ =
          elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c := by
        have h1' : α (elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c) =
            B * elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) (σ c) * B⁻¹ := by
          rw [hB (elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c), spFieldSp_elt]
        exact h1'.symm.trans hfixE
      have heq' : B * elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) (σ c) =
          elt (RootSubgroupIndex.positiveLong (2 : Fin (k + 2 + 1))) c * B := by
        have h := congrArg (· * B) heq
        simpa [mul_assoc] using h
      have hm := congrArg (mat (k + 2 + 1) F) heq'
      simp only [map_mul] at hm
      rw [mat_elt_positiveLong, mat_elt_positiveLong] at hm
      rw [Matrix.transvection, Matrix.transvection, Matrix.mul_add, Matrix.mul_one,
          Matrix.add_mul, Matrix.one_mul] at hm
      rw [single_eq_smul_single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (σ c),
          Matrix.mul_smul,
          single_eq_smul_single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) c,
          Matrix.smul_mul] at hm
      exact add_left_cancel hm
    have hME_comm : mat (k + 2 + 1) F B *
        Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1 =
        Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1 *
          mat (k + 2 + 1) F B := by
      have h := hmat 1
      simpa using h
    ext c
    have hzero : (σ c - c) • (mat (k + 2 + 1) F B *
        Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1) = 0 := by
      rw [sub_smul, hmat c, hME_comm, sub_self]
    have hNM : mat (k + 2 + 1) F B⁻¹ * mat (k + 2 + 1) F B = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hMEnz : mat (k + 2 + 1) F B *
        Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) 1 ≠ 0 := by
      intro h0'
      have hE0 : (Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F) :
          Matrix (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)) (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)) F) = 0 := by
        calc Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F)
            = 1 * Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F) :=
              (one_mul _).symm
          _ = (mat (k + 2 + 1) F B⁻¹ * mat (k + 2 + 1) F B) *
                Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F) := by
              rw [hNM]
          _ = mat (k + 2 + 1) F B⁻¹ * (mat (k + 2 + 1) F B *
                Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F)) := by
              rw [Matrix.mul_assoc]
          _ = mat (k + 2 + 1) F B⁻¹ * 0 := by rw [h0']
          _ = 0 := Matrix.mul_zero _
      have hEne : (Matrix.single (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1))) (1 : F) :
          Matrix (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)) (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)) F) ≠ 0 := by
        intro h
        have h' := congrArg (fun M : Matrix (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1))
            (Fin (k + 2 + 1) ⊕ Fin (k + 2 + 1)) F =>
          M (Sum.inl (2 : Fin (k + 2 + 1))) (Sum.inr (2 : Fin (k + 2 + 1)))) h
        simp [Matrix.single_apply] at h'
      exact hEne hE0
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hMEnz)
  have hαB : ∀ w, α w = B * w * B⁻¹ := by
    intro w
    rw [hB w, hσ, map_one, MulAut.one_apply]
  have hfix0' : B * lam (0 : Fin (k + 2 + 1)) g * B⁻¹ = lam (0 : Fin (k + 2 + 1)) g := by
    rw [← hαB (lam (0 : Fin (k + 2 + 1)) g), hfix0]
  have hB0 : B * lam (0 : Fin (k + 2 + 1)) g = lam (0 : Fin (k + 2 + 1)) g * B := by
    have h := congrArg (· * B) hfix0'
    simpa [mul_assoc] using h
  have hBM : ∀ h : StatedSp (k + 1) F,
      B * spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) =
        spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) * B := by
    intro h
    have hfix' : B * spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) * B⁻¹ =
        spLeviBlock (k + 2) F (spLeviBlock (k + 1) F h) := by
      rw [← hαB, hfixM h]
    have h2 := congrArg (· * B) hfix'
    simpa [mul_assoc] using h2
  obtain ⟨s, t, hs, hBst⟩ := spEnd_exists_lam_lam_of_commute hk htr hB0 hBM
  have hfix1' : B * lam (1 : Fin (k + 2 + 1)) g * B⁻¹ = lam (1 : Fin (k + 2 + 1)) g := by
    rw [← hαB (lam (1 : Fin (k + 2 + 1)) g), hfix1]
  have hsub : B * lam (1 : Fin (k + 2 + 1)) g = lam (1 : Fin (k + 2 + 1)) g * B := by
    have h := congrArg (· * B) hfix1'
    simpa [mul_assoc] using h
  have ht : t * g = g * t := by
    have hcancel : lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (t * g) =
        lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (g * t) := by
      calc lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (t * g)
          = (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) *
              lam (1 : Fin (k + 2 + 1)) g := by rw [map_mul]; group
        _ = lam (1 : Fin (k + 2 + 1)) g *
              (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) t) := by
              rw [← hBst, hsub, hBst]
        _ = (lam (1 : Fin (k + 2 + 1)) g * lam (0 : Fin (k + 2 + 1)) s) *
              lam (1 : Fin (k + 2 + 1)) t := by group
        _ = (lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) g) *
              lam (1 : Fin (k + 2 + 1)) t := by
              rw [(commute_lam_lam (by simp : (0 : Fin (k + 2 + 1)) ≠ 1) s g).eq]
        _ = lam (0 : Fin (k + 2 + 1)) s *
              (lam (1 : Fin (k + 2 + 1)) g * lam (1 : Fin (k + 2 + 1)) t) := by group
        _ = lam (0 : Fin (k + 2 + 1)) s * lam (1 : Fin (k + 2 + 1)) (g * t) := by rw [map_mul]
    exact lam_injective (1 : Fin (k + 2 + 1)) (mul_left_cancel hcancel)
  refine ⟨s, t, hs, ht, fun w => ?_⟩
  have h := hα w
  rw [hαB w, hBst] at h
  exact h.symm

end CFSG.StandardType

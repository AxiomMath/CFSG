module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.Blueprint.SourceClassicalTransportOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaTwoPart
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDescent

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalBlocks Matrix

private lemma ggOmW4_conj_scalar {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (A : GL ι K) (c : Kˣ) :
    A * (Matrix.GeneralLinearGroup.scalar ι c).map σ.toRingHom * A⁻¹ =
      Matrix.GeneralLinearGroup.scalar ι (Units.map σ.toRingHom c) := by
  rw [Matrix.GeneralLinearGroup.map_scalar, ← Matrix.GeneralLinearGroup.scalar_commute,
    mul_assoc, mul_inv_cancel, mul_one]

private lemma ggOmW4_scalar_injective {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Nonempty ι] (a b : Kˣ)
    (hab : Matrix.GeneralLinearGroup.scalar ι a = Matrix.GeneralLinearGroup.scalar ι b) :
    a = b := by
  apply Units.ext
  have hmat := congrArg (fun w : GL ι K => (w : Matrix ι ι K)) hab
  let i : ι := Classical.arbitrary ι
  have hi := congrFun (congrFun hmat i) i
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hi

private lemma ggOmW4_sigma_sq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Nonempty ι]
    (σ : K ≃+* K) (A : GL ι K)
    (hinv : ∀ g : GL ι K, A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g) :
    ∀ x : K, σ (σ x) = x := by
  intro x
  by_cases hx : x = 0
  · subst hx
    simp
  · let u : Kˣ := Units.mk0 x hx
    have hinner : A * (Matrix.GeneralLinearGroup.scalar ι u).map σ.toRingHom * A⁻¹ =
        Matrix.GeneralLinearGroup.scalar ι (Units.map σ.toRingHom u) :=
      ggOmW4_conj_scalar σ A u
    have h := hinv (Matrix.GeneralLinearGroup.scalar ι u)
    rw [hinner] at h
    rw [ggOmW4_conj_scalar σ A (Units.map σ.toRingHom u)] at h
    let σu : Kˣ →* Kˣ := Units.map (σ.toRingHom : K →* K)
    have h2 : σu (σu u) = u := ggOmW4_scalar_injective (σu (σu u)) u h
    have hval := congrArg (fun w : Kˣ => (w : K)) h2
    simpa [u, σu, Units.coe_map] using hval

private lemma ggOmW4_central {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (A : GL ι K)
    (hinv : ∀ g : GL ι K, A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (hσ2 : ∀ x, σ (σ x) = x) (g : GL ι K) :
    (A * A.map σ.toRingHom) * g = g * (A * A.map σ.toRingHom) := by
  have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id K := by
    ext x
    exact hσ2 x
  have hmap2 : (g.map σ.toRingHom).map σ.toRingHom = g := by
    have h := congrArg (fun f : GL ι K →* GL ι K => f g)
      (Matrix.GeneralLinearGroup.map_comp σ.toRingHom σ.toRingHom)
    rw [hcomp, Matrix.GeneralLinearGroup.map_id] at h
    simpa using h.symm
  have h1 : (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom =
      A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹ := by
    simp only [Matrix.GeneralLinearGroup.map_mul, Matrix.GeneralLinearGroup.map_inv, hmap2]
  have h2 : A * (A.map σ.toRingHom * g * (A.map σ.toRingHom)⁻¹) * A⁻¹ =
      (A * A.map σ.toRingHom) * g * (A * A.map σ.toRingHom)⁻¹ := by
    group
  have h := hinv g
  rw [h1, h2] at h
  calc (A * A.map σ.toRingHom) * g
      = ((A * A.map σ.toRingHom) * g * (A * A.map σ.toRingHom)⁻¹) *
          (A * A.map σ.toRingHom) := by group
    _ = g * (A * A.map σ.toRingHom) := by rw [h]

private lemma ggOmW4_apply_twice {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K ≃+* K) (hσ2 : ∀ x, σ (σ x) = x) (A : GL ι K) (v : ι → K) :
    (A : Matrix ι ι K) *ᵥ (fun i => σ (((A : Matrix ι ι K) *ᵥ (fun j => σ (v j))) i))
      = ((A : Matrix ι ι K) * (A : Matrix ι ι K).map σ.toRingHom) *ᵥ v := by
  have h1 : (fun i => σ (((A : Matrix ι ι K) *ᵥ (fun j => σ (v j))) i))
      = (A : Matrix ι ι K).map σ.toRingHom *ᵥ v := by
    funext i
    have h3 : σ (((A : Matrix ι ι K) *ᵥ (fun j => σ (v j))) i)
        = ((A : Matrix ι ι K).map σ.toRingHom *ᵥ
            (σ.toRingHom ∘ (fun j => σ (v j)))) i :=
      RingHom.map_mulVec σ.toRingHom (A : Matrix ι ι K) (fun j => σ (v j)) i
    have hfun : (σ.toRingHom ∘ (fun j => σ (v j))) = v := by
      funext j
      exact hσ2 (v j)
    rw [h3, hfun]
  rw [h1, Matrix.mulVec_mulVec]

private lemma ggOmW4_exists_Phi_ne_zero {ι K : Type} [DecidableEq ι] [Field K]
    [Nonempty ι] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) : ∃ v, Φ v ≠ 0 := by
  classical
  by_contra h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hw : (Pi.single i (1 : K) : ι → K) ≠ 0 := by
    intro hh
    have h1 := congrFun hh i
    rw [Pi.single_eq_same] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (ι → K) := ⟨Pi.single i (1 : K), 0, hw⟩
  have h0 : ∀ v : ι → K, Φ v = 0 := fun v => by
    by_contra hv
    exact h ⟨v, hv⟩
  have hB : QuadraticMap.polarBilin Φ = 0 := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h0 (x + y), h0 x, h0 y]
    simp
  exact hΦ.1.ne_zero hB

private lemma ggOmW4_AA {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 2]
    [Nonempty ι] (σ : K ≃+* K) (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (A : GL ι K)
    (hAΦ : ∀ v : ι → K, Φ ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = σ (Φ v))
    (hinv : ∀ g : GL ι K, A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (hσ2 : ∀ x, σ (σ x) = x) :
    A * A.map σ.toRingHom = 1 := by
  have hcentral := ggOmW4_central σ A hinv hσ2
  have hcenter : A * A.map σ.toRingHom ∈ Subgroup.center (GL ι K) :=
    Subgroup.mem_center_iff.mpr (fun g => (hcentral g).symm)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨c, hc⟩ := hcenter
  have hcmat : (A : Matrix ι ι K) * (A : Matrix ι ι K).map σ.toRingHom =
      Matrix.scalar ι (c : K) := by
    have h := congrArg (fun w : GL ι K => (w : Matrix ι ι K)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul] using h.symm
  have hscalar : ∀ v : ι → K,
      ((A : Matrix ι ι K) * (A : Matrix ι ι K).map σ.toRingHom) *ᵥ v = (c : K) • v := by
    intro v
    rw [hcmat, Matrix.scalar_apply]
    ext i
    simp [Matrix.mulVec_diagonal]
  have hmain : ∀ v : ι → K, (c : K) * (c : K) * Φ v = Φ v := by
    intro v
    have h1 : Φ ((A : Matrix ι ι K) *ᵥ
        (fun i => σ (((A : Matrix ι ι K) *ᵥ (fun j => σ (v j))) i))) = Φ v := by
      rw [hAΦ ((A : Matrix ι ι K) *ᵥ (fun j => σ (v j))), hAΦ v]
      exact hσ2 (Φ v)
    rw [ggOmW4_apply_twice σ hσ2 A v, hscalar v, QuadraticMap.map_smul] at h1
    simpa [smul_eq_mul] using h1
  obtain ⟨v, hv⟩ := ggOmW4_exists_Phi_ne_zero Φ hΦ
  have hc2 : (c : K) * (c : K) = 1 := by
    have h := hmain v
    have h' : ((c : K) * (c : K) - 1) * Φ v = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hv
  have hc1 : c = 1 := by
    apply Units.ext
    have h3 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
      have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc ((c : K) - 1) * ((c : K) - 1)
          = (c : K) * (c : K) - 2 * (c : K) + 1 := by ring
        _ = 1 - 2 * (c : K) + 1 := by rw [hc2]
        _ = 2 - 2 * (c : K) := by ring
        _ = 2 * (1 - (c : K)) := by ring
        _ = 0 := by rw [hchar, zero_mul]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  rw [← hc, hc1, map_one]

private lemma ggOmW4_arith {f f₀ N : ℕ} (hf : f = 2 * f₀) (hf₀ : 0 < f₀)
    (h : f * N = f₀ * N) : N = 0 := by
  have h1 : f₀ * N = 0 := by
    have h2 : f₀ * N + f₀ * N = f₀ * N + 0 := by
      rw [← two_mul, ← mul_assoc, add_zero, ← hf]
      exact h
    exact Nat.add_left_cancel h2
  rcases Nat.mul_eq_zero.mp h1 with h' | h'
  · exact absurd h' (Nat.ne_of_gt hf₀)
  · exact h'

theorem isMulCommutative_centralizer_of_fieldInv_Omega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ≠ RingEquiv.refl K)
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) (A : GL ι K)
    (hAΦ : ∀ v : ι → K, Φ ((A : Matrix ι ι K) *ᵥ fun i => σ (v i)) = σ (Φ v))
    (hinv : ∀ g : GL ι K, A * (A * g.map σ.toRingHom * A⁻¹).map σ.toRingHom * A⁻¹ = g)
    (b : GL ι K) (hb : b ∈ StatedOmega ⇑Φ) (hodd : Odd (orderOf b))
    (hfix : ∀ g ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ,
      A * g.map σ.toRingHom * A⁻¹ = g) :
    ∀ x ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ,
      ∀ y ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ, x * y = y * x := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hσ2 : ∀ x : K, σ (σ x) = x := ggOmW4_sigma_sq σ A hinv
  have hAA : A * A.map σ.toRingHom = 1 := ggOmW4_AA σ Φ hΦ A hAΦ hinv hσ2
  have hfix' : ∀ g ∈ (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype,
      A * (g : GL ι K).map σ.toRingHom * A⁻¹ = g := by
    intro g hg
    have hgGL : (g : GL ι K) ∈ Subgroup.centralizer {b} ⊓ StatedOmega ⇑Φ :=
      ⟨Subgroup.mem_comap.mp hg, g.2⟩
    exact hfix (g : GL ι K) hgGL
  obtain ⟨K₀, hK₀field, hK₀fin, hK₀char, Φ₀, b₀, hΦ₀, hb₀, hodd₀, hcard, hIso, hblockExp⟩ :=
    descent_centralizer_Omega σ hσ hσ2 Φ hΦ h8 A hAΦ hAA b hb hodd hfix'
  letI : Field K₀ := hK₀field
  letI : Fintype K₀ := hK₀fin
  letI : CharP K₀ 2 := hK₀char
  letI : Algebra (ZMod 2) K₀ := ZMod.algebra K₀ 2
  obtain ⟨e⟩ := hIso
  have hfK : Fintype.card K = 2 ^ Module.finrank (ZMod 2) K :=
    (FiniteField.pow_finrank_eq_card 2 K).symm
  have hfK₀ : Fintype.card K₀ = 2 ^ Module.finrank (ZMod 2) K₀ :=
    (FiniteField.pow_finrank_eq_card 2 K₀).symm
  have hf_eq : Module.finrank (ZMod 2) K = 2 * Module.finrank (ZMod 2) K₀ := by
    have h : 2 ^ Module.finrank (ZMod 2) K = 2 ^ (2 * Module.finrank (ZMod 2) K₀) := by
      have hc' := hcard
      rw [hfK, hfK₀] at hc'
      rw [hc', pow_mul']
    exact Nat.pow_right_injective (le_refl 2) h
  have hf₀pos : 0 < Module.finrank (ZMod 2) K₀ := by
    by_contra h
    have h0 : Module.finrank (ZMod 2) K₀ = 0 := Nat.eq_zero_of_not_pos h
    rw [h0] at hfK₀
    simp at hfK₀
    exact absurd hfK₀.symm (ne_of_lt Fintype.one_lt_card)
  have h2C := two_part_centralizer_Omega (K := K) hfK Φ hΦ h8 b hb hodd
  have h2C₀ := two_part_centralizer_Omega (K := K₀) hfK₀ Φ₀ hΦ₀ h8 b₀ hb₀ hodd₀
  let C : Subgroup ↥(StatedOmega ⇑Φ) :=
    (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype
  let C₀ : Subgroup ↥(StatedOmega ⇑Φ₀) :=
    (Subgroup.centralizer {b₀}).comap (StatedOmega ⇑Φ₀).subtype
  have hcardC : Nat.card ↥C = Nat.card ↥C₀ := Nat.card_congr e.toEquiv
  have hfac : (Nat.card ↥C).factorization 2 = (Nat.card ↥C₀).factorization 2 := by rw [hcardC]
  have heq : Module.finrank (ZMod 2) K * blockExp true (b : Matrix ι ι K) =
      Module.finrank (ZMod 2) K₀ * blockExp true (b₀ : Matrix ι ι K₀) := by
    rw [← h2C, ← h2C₀]
    exact hfac
  have heq' : Module.finrank (ZMod 2) K * blockExp true (b : Matrix ι ι K) =
      Module.finrank (ZMod 2) K₀ * blockExp true (b : Matrix ι ι K) := by
    rw [← hblockExp] at heq
    exact heq
  have hN : blockExp true (b : Matrix ι ι K) = 0 := ggOmW4_arith hf_eq hf₀pos heq'
  have hcomm := commutative_centralizer_of_blockExp_eq_zero_Omega Φ hΦ h8 b hb hodd hN
  intro x hx y hy
  have hx' : (⟨x, hx.2⟩ : ↥(StatedOmega ⇑Φ)) ∈
      (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype := by
    rw [Subgroup.mem_comap]
    exact hx.1
  have hy' : (⟨y, hy.2⟩ : ↥(StatedOmega ⇑Φ)) ∈
      (Subgroup.centralizer {b}).comap (StatedOmega ⇑Φ).subtype := by
    rw [Subgroup.mem_comap]
    exact hy.1
  have hc := hcomm ⟨x, hx.2⟩ hx' ⟨y, hy.2⟩ hy'
  simpa using congrArg (fun z : ↥(StatedOmega ⇑Φ) => (z : GL ι K)) hc

end CFSG.StandardType.ClassicalBlocks

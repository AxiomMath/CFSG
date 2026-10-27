module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMRestrict
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPOmegaPlus
public import CFSG.ClassicalGroups.Orthogonal.OddOrder

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.ClassicalPosition
open scoped Matrix

private lemma rckLiftHom_rho_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (hε : IsIdempotentElem ε) {x y : Matrix ι ι F}
    (hx : x * ε = ε * x) (hy : y * ε = ε * y) :
    (x * ε + (1 - ε)) * (y * ε + (1 - ε)) = (x * y) * ε + (1 - ε) := by
  have hε' : ε * ε = ε := hε.eq
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hε']
    abel
  have hx0 : x * ε * (1 - ε) = 0 := by
    rw [mul_assoc, hε.mul_one_sub_self, mul_zero]
  have hy0 : (1 - ε) * (y * ε) = 0 := by
    rw [hy, ← mul_assoc, hε.one_sub_mul_self, zero_mul]
  calc
    (x * ε + (1 - ε)) * (y * ε + (1 - ε))
        = x * ε * (y * ε) + x * ε * (1 - ε) + (1 - ε) * (y * ε) +
            (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * ε * (y * ε) + (1 - ε) * (1 - ε) := by simp [hx0, hy0]
    _ = x * (ε * y) * ε + (1 - ε) * (1 - ε) := by noncomm_ring
    _ = x * (y * ε) * ε + (1 - ε) * (1 - ε) := by rw [hy]
    _ = x * y * ε + (1 - ε) := by
      rw [mul_assoc x (y * ε) ε, mul_assoc y ε ε, hε', ← mul_assoc x y ε, h1]

private lemma rckLiftHom_s₁_mul {n f : ℕ} {B : Type} [Group B]
    {s' s₁ : B → GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hform : ∀ b : B, ((s₁ b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      ((s' b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε + (1 - ε))
    (hε : IsIdempotentElem ε)
    (hεcomm : ∀ b : B, ((s' b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε =
      ε * ((s' b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hs'_mul : ∀ b b' : B, s' (b * b') = s' b * s' b') :
    ∀ b b' : B, s₁ (b * b') = s₁ b * s₁ b' := by
  intro b b'
  apply Units.ext
  rw [Units.val_mul, hform (b * b'), hform b, hform b', hs'_mul b b']
  exact (rckLiftHom_rho_mul hε (hεcomm b) (hεcomm b')).symm

private lemma rckLiftHom_isUnit_det_polarGram {n f : ℕ} :
    IsUnit (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).det := by
  have h1 : (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))) =
      LinearMap.BilinForm.toMatrix'
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))) := rfl
  rw [h1]
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp
    ((LinearMap.BilinForm.nondegenerate_toMatrix'_iff).mpr
      (Spin.nondegenerate_polarBilin_quadPlus n (GaloisField 2 f))))

private lemma rckLiftHom_polar_eq_dot {n f : ℕ} (x y : Fin n ⊕ Fin n → GaloisField 2 f) :
    QuadraticMap.polar (Spin.quadPlus n (GaloisField 2 f)) x y =
      dotProduct x ((LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))) =
      LinearMap.BilinForm.toMatrix'
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix'
      (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma rckLiftHom_quad_add {n f : ℕ} (u v : Fin n ⊕ Fin n → GaloisField 2 f) :
    Spin.quadPlus n (GaloisField 2 f) (u + v) =
      Spin.quadPlus n (GaloisField 2 f) u + Spin.quadPlus n (GaloisField 2 f) v +
        dotProduct u ((LinearMap.toMatrix₂' (GaloisField 2 f)
          (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f)))).mulVec v) := by
  rw [QuadraticMap.map_add (Spin.quadPlus n (GaloisField 2 f)) u v,
    rckLiftHom_polar_eq_dot (n := n) (f := f) u v]

private lemma rckLiftHom_block_mem_omega {n f : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : Odd p)
    {s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hQ₁ : ∀ v : Fin n ⊕ Fin n → GaloisField 2 f,
      Spin.quadPlus n (GaloisField 2 f)
        (((s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
        Spin.quadPlus n (GaloisField 2 f) v)
    (hpow : s₁ ^ p = 1) :
    s₁ ∈ (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).range := by
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) (GaloisField 2 f) s₁ ∈
      TauCeti.QuadraticMap.orthogonalGroup (Spin.quadPlus n (GaloisField 2 f)) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Spin.quadPlus n (GaloisField 2 f)
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) (GaloisField 2 f) s₁ v) =
      Spin.quadPlus n (GaloisField 2 f) v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact hQ₁ v
  have hEl : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) (GaloisField 2 f) s₁ ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (Spin.quadPlus n (GaloisField 2 f)) := by
    refine CFSG.ClassicalGroups.Orthogonal.mem_elementaryGroup_quadPlus_of_odd_pow h2 hn hO hp ?_
    rw [← map_pow, hpow, map_one]
  have hΩ : s₁ ∈ CFSG.Open.StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f)) := by
    rw [Spin.coe_quadPlus]
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadPlus_eq_map hn]
    exact Subgroup.mem_map.mpr ⟨_, hEl, by simp⟩
  have hrange : (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).range =
      CFSG.Open.StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f)) := by
    rw [Spin.range_spinMatrix_quadPlus (K := GaloisField 2 f) hn, Spin.coe_quadPlus]
  rwa [hrange]

private lemma rckLiftHom_exists_blockRestrict_POmegaPlus {n f : ℕ} (hn : 3 ≤ n)
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v)
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {p : ℕ} (hp : Odd p) (s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hs'Q : ∀ v : Fin n ⊕ Fin n → GaloisField 2 f,
      Spin.quadPlus n (GaloisField 2 f)
        (((s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
        Spin.quadPlus n (GaloisField 2 f) v)
    (hs'p : s' ^ p = 1)
    (hcomm_s' : ∀ u ∈ S, Commute s' u) :
    ∃ s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      ((s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε =
        ε * ((s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∧
      ((s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        ((s' : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε + (1 - ε) ∧
      s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) ∧
      s₁ ∈ (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).range ∧
      (∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
        s' * g * s'⁻¹ = s₁ * g * s₁⁻¹) := by
  obtain ⟨hεcomm, s₁, hform, hmem, hord, hconj⟩ :=
    rckGLBlock_restrict hS hε.1 hε.2.1 s' hcomm_s'
  have hpow : s₁ ^ p = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord.trans (orderOf_dvd_iff_pow_eq_one.mpr hs'p))
  have hQ₁ : ∀ v : Fin n ⊕ Fin n → GaloisField 2 f,
      Spin.quadPlus n (GaloisField 2 f)
        (((s₁ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
        Spin.quadPlus n (GaloisField 2 f) v :=
    rckGLBlock_restrict_quad (rckLiftHom_isUnit_det_polarGram (n := n) (f := f))
      hε.2.2.2.1 hε.2.1 (rckLiftHom_quad_add (n := n) (f := f)) hs'Q hεcomm hform
  exact ⟨s₁, hεcomm, hform, hmem, rckLiftHom_block_mem_omega hn hp hQ₁ hpow, hconj⟩

private lemma rckLiftHom_exists_sb_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Spin.plusDatum n (GaloisField 2 f) hn) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      (∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
        ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) ∧
      (∀ b : ↥B, Commute (sb b) s) := by
  let sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f)) := fun b =>
    Classical.choose
      (exists_conj_eq_POmegaPlus n (GaloisField 2 f) hn ψ hker (hBID b b.2))
  have hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹) := fun b u =>
    Classical.choose_spec
      (exists_conj_eq_POmegaPlus n (GaloisField 2 f) hn ψ hker (hBID b b.2)) u
  refine ⟨sb, hsb_spec, fun b => ?_⟩
  exact conj_eq_commute_POmegaPlus n (GaloisField 2 f) hn ψ hker (hBe b b.2) (hsb_spec b) hs

private lemma rckLiftHom_sb_inv_mul_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹)) :
    ∀ b b' : ↥B,
      ((sb (b * b'))⁻¹ : spinGroup (Spin.quadPlus n (GaloisField 2 f))) =
        (sb b)⁻¹ * (sb b')⁻¹ := by
  intro b b'
  have hanti : sb (b * b') = sb b' * sb b := by
    refine conj_eq_unique_POmegaPlus n (GaloisField 2 f) hn ψ hker ?_
    intro u
    rw [← hsb_spec (b * b') u]
    calc ((b * b' : ↥B) : X)⁻¹ * ψ u * ((b * b' : ↥B) : X)
        = (b' : X)⁻¹ * ((b : X)⁻¹ * ψ u * (b : X)) * (b' : X) := by
          simp only [Subgroup.coe_mul]
          group
      _ = (b' : X)⁻¹ * ψ (sb b * u * (sb b)⁻¹) * (b' : X) := by rw [hsb_spec b u]
      _ = ψ (sb b' * (sb b * u * (sb b)⁻¹) * (sb b')⁻¹) := by
          rw [hsb_spec b' (sb b * u * (sb b)⁻¹)]
      _ = ψ ((sb b' * sb b) * u * (sb b' * sb b)⁻¹) := by
          congr 1
          group
  rw [hanti, mul_inv_rev]

private lemma rckLiftHom_conj_lift_POmegaPlus {n f : ℕ} {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    (b : ↥B) (y : spinGroup (Spin.quadPlus n (GaloisField 2 f))) :
    (b : X) * ψ y * (b : X)⁻¹ = ψ ((sb b)⁻¹ * y * (sb b)) := by
  have h := hsb_spec b ((sb b)⁻¹ * y * (sb b))
  have h' : (b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X) = ψ y := by
    rw [h, show sb b * ((sb b)⁻¹ * y * (sb b)) * (sb b)⁻¹ = y by group]
  calc (b : X) * ψ y * (b : X)⁻¹
      = (b : X) * ((b : X)⁻¹ * ψ ((sb b)⁻¹ * y * (sb b)) * (b : X)) *
          (b : X)⁻¹ := by rw [← h']
    _ = ψ ((sb b)⁻¹ * y * (sb b)) := by group

private lemma rckLiftHom_exists_s'_data {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {B : Subgroup X}
    {sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f))} {p : ℕ}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    (hcomm_s : ∀ b : ↥B, Commute (sb b) s) (hsb_pow : ∀ b : ↥B, sb b ^ p = 1) :
    ∃ s' : ↥B → GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      (∀ b : ↥B,
        s' b = Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹)) ∧
      (∀ (b : ↥B) (v : Fin n ⊕ Fin n → GaloisField 2 f),
        Spin.quadPlus n (GaloisField 2 f)
          (((s' b : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *ᵥ v) =
          Spin.quadPlus n (GaloisField 2 f) v) ∧
      (∀ b : ↥B, s' b ^ p = 1) ∧
      (∀ (b : ↥B) (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f)),
        u ∈ ({Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} :
          Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) → Commute (s' b) u) ∧
      (∀ b b' : ↥B, s' (b * b') = s' b * s' b') := by
  let s' : ↥B → GL (Fin n ⊕ Fin n) (GaloisField 2 f) := fun b =>
    Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹)
  have hs'def : ∀ b : ↥B,
      s' b = Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹) := fun _ => rfl
  refine ⟨s', hs'def, ?_, ?_, ?_, ?_⟩
  · intro b v
    exact Spin.spinMatrix_mem (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹) v
  · intro b
    have hj : (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) (sb b)) ^ p = 1 := by
      rw [← map_pow, hsb_pow b, map_one]
    rw [hs'def b, map_inv, inv_pow, hj, inv_one]
  · intro b u hu
    rw [Set.mem_singleton_iff] at hu
    subst u
    have hci := ((hcomm_s b).map (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))).inv_left
    simpa [s', map_inv] using hci
  · intro b b'
    rw [hs'def (b * b'), hs'def b, hs'def b',
      rckLiftHom_sb_inv_mul_POmegaPlus hn hker hsb_spec b b', map_mul]

private lemma rckLiftHom_blockAction_POmegaPlus {n f : ℕ} {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    {B : Subgroup X} {sb : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hsb_spec : ∀ (b : ↥B) (u : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      ((b : X)⁻¹ * ψ u * (b : X)) = ψ (sb b * u * (sb b)⁻¹))
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {s' s₁ : ↥B → GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    {t₁ : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f))}
    (hs'def : ∀ b : ↥B,
      s' b = Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹))
    (hconj : ∀ b : ↥B, ∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε),
      s' b * g * (s' b)⁻¹ = s₁ b * g * (s₁ b)⁻¹)
    (ht₁j : ∀ b : ↥B, Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) (t₁ b) = s₁ b) :
    ∀ (b : ↥B) (y : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
      y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) S ε →
      (b : X) * ψ y * (b : X)⁻¹ = ψ (t₁ b * y * (t₁ b)⁻¹) := by
  intro b y hy
  have hyGL : Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y ∈
      Subgroup.centralizer S ⊓ glFixing (1 - ε) := by
    have h : y ∈ (Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap
        (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) := by
      simpa [glBlockCentralizer] using hy
    exact Subgroup.mem_comap.mp h
  have hconj_y := hconj b (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y) hyGL
  have hmat : Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹ * y * (sb b)) =
      Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) (t₁ b * y * (t₁ b)⁻¹) := by
    calc Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹ * y * (sb b))
        = Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹) *
            Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y *
            (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) ((sb b)⁻¹))⁻¹ := by
          rw [map_mul, map_mul, map_inv, inv_inv]
      _ = s' b * Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y * (s' b)⁻¹ := by
          rw [hs'def b]
      _ = s₁ b * Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) y * (s₁ b)⁻¹ := hconj_y
      _ = Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) (t₁ b * y * (t₁ b)⁻¹) := by
          rw [map_mul, map_mul, map_inv, ht₁j b]
  rw [rckLiftHom_conj_lift_POmegaPlus hsb_spec b y]
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2))
  rw [hinj hmat]

theorem exists_rckRestrictLiftHom_POmegaPlus {n f : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    {ψ : spinGroup (Spin.quadPlus n (GaloisField 2 f)) →* X}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n (GaloisField 2 f))))
    {s : spinGroup (Spin.quadPlus n (GaloisField 2 f))} {e : X}
    (hs : ∀ u, e⁻¹ * ψ u * e = ψ (s * u * s⁻¹))
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus n (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s})) ε)
    {p : ℕ} (hp : Odd p) {B : Subgroup X} (hBp : ∀ b ∈ B, b ^ p = 1)
    (hBN : B ≤ Subgroup.normalizer (ψ.range : Set X))
    (hBID : ∀ b ∈ B, GGPsiInnerDiag (Spin.plusDatum n (GaloisField 2 f) hn) ψ b)
    (hBe : ∀ b ∈ B, Commute b e) :
    ∃ β : ↥B →* ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
        {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε),
      ∀ (b : ↥B) (y : spinGroup (Spin.quadPlus n (GaloisField 2 f))),
        y ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
          {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s} ε →
        (b : X) * ψ y * (b : X)⁻¹ =
          ψ ((β b : spinGroup (Spin.quadPlus n (GaloisField 2 f))) * y *
            (β b : spinGroup (Spin.quadPlus n (GaloisField 2 f)))⁻¹) := by
  let S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    {Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) s}
  have hS : ∀ u ∈ S, ∀ v ∈ S, Commute u v := by
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst u
    subst v
    exact Commute.refl _
  obtain ⟨sb, hsb_spec, hcomm_s⟩ :=
    rckLiftHom_exists_sb_POmegaPlus hn hker hs hBN hBID hBe
  have hsb_pow : ∀ b : ↥B, sb b ^ p = 1 := fun b =>
    spin_pow_eq_one_of_conj_POmegaPlus hn ψ hker (hBp b b.2) (hsb_spec b)
  obtain ⟨s', hs'def, hs'Q, hs'p, hcomm_s', hs'_mul⟩ :=
    rckLiftHom_exists_s'_data hn hker hsb_spec hcomm_s hsb_pow
  choose s₁ hεcomm hform hmem hrange hconj using fun b : ↥B =>
    rckLiftHom_exists_blockRestrict_POmegaPlus (S := S) hn hS hε hp (s' b) (hs'Q b) (hs'p b)
      (hcomm_s' b)
  let t₁ : ↥B → spinGroup (Spin.quadPlus n (GaloisField 2 f)) := fun b =>
    Classical.choose (MonoidHom.mem_range.mp (hrange b))
  have ht₁j : ∀ b : ↥B,
      Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)) (t₁ b) = s₁ b := fun b =>
    Classical.choose_spec (MonoidHom.mem_range.mp (hrange b))
  have ht₁mem : ∀ b : ↥B,
      t₁ b ∈ glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) S ε := by
    intro b
    have h : t₁ b ∈ ((Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap
        (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))) :=
      Subgroup.mem_comap.mpr (by rw [ht₁j b]; exact hmem b)
    simpa [glBlockCentralizer] using h
  let βfun : ↥B → ↥(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f)))
      S ε) := fun b => ⟨t₁ b, ht₁mem b⟩
  have hs₁_mul : ∀ b b' : ↥B, s₁ (b * b') = s₁ b * s₁ b' :=
    rckLiftHom_s₁_mul hform hε.2.1 hεcomm hs'_mul
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2))
  have hβmul : ∀ b b' : ↥B, βfun (b * b') = βfun b * βfun b' := by
    intro b b'
    have ht : t₁ (b * b') = t₁ b * t₁ b' :=
      hinj (by rw [ht₁j (b * b'), map_mul, ht₁j b, ht₁j b', hs₁_mul b b'])
    exact Subtype.ext ht
  refine ⟨MonoidHom.mk' βfun hβmul, ?_⟩
  intro b y hy
  simpa [βfun] using
    rckLiftHom_blockAction_POmegaPlus hsb_spec hs'def hconj ht₁j b y hy

end CFSG.StandardType.RCKRP

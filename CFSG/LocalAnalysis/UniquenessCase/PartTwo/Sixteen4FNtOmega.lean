module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtDual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtIndexTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtOmegaBig
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LieType.BorelTits

open LinearMap Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def w183_binForm (B : LinearMap.BilinForm K (ι → K))
    (l : K →ₗ[ZMod 2] ZMod 2) : LinearMap.BilinForm (ZMod 2) (ι → K) :=
  LinearMap.compr₂ (B.restrictScalars₁₂ (ZMod 2) (ZMod 2)) l

private theorem w183_binForm_apply (B : LinearMap.BilinForm K (ι → K))
    (l : K →ₗ[ZMod 2] ZMod 2) (x y : ι → K) : w183_binForm B l x y = l (B x y) := rfl

private theorem w183_binForm_nondegenerate (B : LinearMap.BilinForm K (ι → K))
    (hB : B.Nondegenerate) (l : K →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) :
    (w183_binForm B l).Nondegenerate := by
  have key : ∀ (x : ι → K), (∀ y, B x y = 0) → x = 0 := hB.1
  have key2 : ∀ (y : ι → K), (∀ x, B x y = 0) → y = 0 := hB.2
  constructor
  · intro x hx
    by_contra hx0
    refine hl (LinearMap.ext fun c => ?_)
    have h1 : ∃ y, B x y ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hx0 (key x h)
    obtain ⟨y0, hy0⟩ := h1
    have h2 : B x ((c / B x y0) • y0) = c := by
      rw [map_smul, smul_eq_mul]
      field_simp
    rw [show l c = l (B x ((c / B x y0) • y0)) by rw [h2]]
    exact hx _
  · intro y hy
    by_contra hy0
    refine hl (LinearMap.ext fun c => ?_)
    have h1 : ∃ x, B x y ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hy0 (key2 y h)
    obtain ⟨x0, hx0⟩ := h1
    have h2 : B ((c / B x0 y) • x0) y = c := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      field_simp
    rw [show l c = l (B ((c / B x0 y) • x0) y) by rw [h2]]
    exact hy _

private theorem w183_binForm_invariant (B : LinearMap.BilinForm K (ι → K))
    (g : Matrix.GeneralLinearGroup ι K) (x y : ι → K)
    (hB : B (Matrix.mulVec (g : Matrix ι ι K) x) (Matrix.mulVec (g : Matrix ι ι K) y) = B x y)
    (l : K →ₗ[ZMod 2] ZMod 2) :
    w183_binForm B l (Matrix.mulVec (g : Matrix ι ι K) x)
      (Matrix.mulVec (g : Matrix ι ι K) y) = w183_binForm B l x y := by
  rw [w183_binForm_apply, w183_binForm_apply, hB]

private theorem w183_exists_dual_ne_zero : ∃ l : K →ₗ[ZMod 2] ZMod 2, l ≠ 0 := by
  haveI : Nontrivial K := inferInstance
  haveI : Module.Projective (ZMod 2) K := Module.Projective.of_free
  haveI : Nontrivial (Module.Dual (ZMod 2) K) := inferInstance
  exact exists_ne 0

private theorem w183_polar_invariant {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) K) (hg : g ∈ orthGroup (StatedQuadPlus r K))
    (x y : Fin r ⊕ Fin r → K) :
    (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus r K))
        (Matrix.mulVec (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x)
        (Matrix.mulVec (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) y) =
      (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus r K)) x y := by
  let Q := CFSG.LieType.Universal.Spin.quadPlus r K
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
  let Φ := CFSG.RankThree.OrthogonalInvolutions.toQuadForm Q hQnd
  have hQeq : Φ.Q = StatedQuadPlus r K := by
    funext v
    rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q,
      CFSG.LieType.Universal.Spin.coe_quadPlus]
  have hpres : ∀ v, Φ.Q (Matrix.toLin' (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) v) =
      Φ.Q v := by
    intro v
    rw [hQeq, Matrix.toLin'_apply]
    exact orthGroup_preserves (StatedQuadPlus r K) hg v
  have hpol := Φ.polar_map_of_Q hpres x y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hpol
  simpa [Q, Φ, CFSG.RankThree.OrthogonalInvolutions.toQuadForm_polar_β,
    QuadraticMap.polarBilin_apply_apply] using hpol

private theorem w183_polar_invariant_minus {r : ℕ} {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K)
    (hg : g ∈ orthGroup (StatedQuadMinus r K b c))
    (x y : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) :
    (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus r K b c))
        (Matrix.mulVec (g : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2)
          (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K) x)
        (Matrix.mulVec (g : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2)
          (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K) y) =
      (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus r K b c)) x y := by
  let Q := CFSG.LieType.Universal.Spin.quadMinus r K b c
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
      (n := r) (K := K) hirr
  let Φ := CFSG.RankThree.OrthogonalInvolutions.toQuadForm Q hQnd
  have hQeq : Φ.Q = StatedQuadMinus r K b c := by
    funext v
    rw [CFSG.RankThree.OrthogonalInvolutions.toQuadForm_Q,
      CFSG.LieType.Universal.Spin.coe_quadMinus]
  have hpres : ∀ v, Φ.Q (Matrix.toLin' (g : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2)
      (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K) v) = Φ.Q v := by
    intro v
    rw [hQeq, Matrix.toLin'_apply]
    exact orthGroup_preserves (StatedQuadMinus r K b c) hg v
  have hpol := Φ.polar_map_of_Q hpres x y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hpol
  simpa [Q, Φ, CFSG.RankThree.OrthogonalInvolutions.toQuadForm_polar_β,
    QuadraticMap.polarBilin_apply_apply] using hpol

private theorem w183_normal_subgroupOf_omega (Q : (ι → K) → K) :
    (StatedOmega Q).subgroupOf (orthGroup Q) |>.Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (N := StatedOmega Q)
    (normalizer_commutator_ge_left (orthGroup Q) (orthGroup Q))

theorem s16nt_cover_omPlus {K : Type} [Field K] [Finite K] {r a : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2 ^ a) :
    S16BoundCover (FFModel.nat (StatedOmega (StatedQuadPlus r K))) (2 * a) := by
  have ha1 : 1 ≤ a := s16nt_one_le_of_card hK
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hF
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨l, hl⟩ := w183_exists_dual_ne_zero (K := K)
  let B : LinearMap.BilinForm K (Fin r ⊕ Fin r → K) :=
    QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus r K)
  have hB : B.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
  let β : LinearMap.BilinForm (ZMod 2) (Fin r ⊕ Fin r → K) := w183_binForm B l
  have hβ : β.Nondegenerate := w183_binForm_nondegenerate B hB l hl
  have hβinv : ∀ g ∈ StatedOmega (StatedQuadPlus r K), ∀ x y : Fin r ⊕ Fin r → K,
      β (Matrix.mulVec (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) x)
        (Matrix.mulVec (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) y) = β x y := by
    intro g hg x y
    have hgO : g ∈ orthGroup (StatedQuadPlus r K) := statedOmega_le_orthGroup _ hg
    have hBxy := w183_polar_invariant g hgO x y
    exact w183_binForm_invariant B g x y hBxy l
  have hdual : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1
        (Representation.dual (s16ntNatRep (StatedOmega (StatedQuadPlus r K))))) =
      Module.finrank (ZMod 2)
        (CFSG.Quasithin.JonesParshall.H1
          (s16ntNatRep (StatedOmega (StatedQuadPlus r K)))) :=
    s16nt_h1_dual_natRep _ β hβ hβinv
  have hbound : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1
        (Representation.dual (s16ntNatRep (StatedOmega (StatedQuadPlus r K))))) ≤ 2 * a := by
    rw [hdual]
    by_cases ha : 2 ≤ a
    · rw [s16nt_omega_h1_plus_big (K := K) hr ha hK]
      omega
    · have haeq : a = 1 := by omega
      subst haeq
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hΩO : StatedOmega (StatedQuadPlus r K) ≤ orthGroup (StatedQuadPlus r K) :=
        statedOmega_le_orthGroup _
      let H := (StatedOmega (StatedQuadPlus r K)).subgroupOf (orthGroup (StatedQuadPlus r K))
      haveI hHn : H.Normal := w183_normal_subgroupOf_omega (StatedQuadPlus r K)
      obtain ⟨s, hsO, hs2, hgen⟩ := s16nt_orth_index_two_plus_two (K := K) hr hK2
      have hs' : (⟨s, hsO⟩ : ↥(orthGroup (StatedQuadPlus r K))) ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hs2
      have hG : ∀ g : ↥(orthGroup (StatedQuadPlus r K)), g ∈ H ∨ g * ⟨s, hsO⟩ ∈ H := by
        intro g
        rcases hgen g g.2 with h | h
        · left; rw [Subgroup.mem_subgroupOf]; exact h
        · right; rw [Subgroup.mem_subgroupOf]; simpa using h
      have hfix : ∀ n : Fin r ⊕ Fin r → K,
          (∀ h : ↥H, (s16ntNatRep (orthGroup (StatedQuadPlus r K)) h) n = n) → n = 0 := by
        intro n hn
        apply s16nt_omega_fix_plus_two (K := K) hr hK2 n
        intro A hA
        have hhh := hn (⟨⟨A, hΩO hA⟩, hA⟩ : ↥H)
        simpa [s16ntNatRep, Matrix.mulVecLin_apply] using hhh
      have hidx := s16nt_h1_index_two
        (s16ntNatRep (orthGroup (StatedQuadPlus r K))) H hs' hG hfix
      have hcongr : Module.finrank (ZMod 2)
            (CFSG.Quasithin.JonesParshall.H1
              ((s16ntNatRep (orthGroup (StatedQuadPlus r K))).comp H.subtype)) =
          Module.finrank (ZMod 2)
            (CFSG.Quasithin.JonesParshall.H1
              (s16ntNatRep (StatedOmega (StatedQuadPlus r K)))) := by
        have hrep : (s16ntNatRep (StatedOmega (StatedQuadPlus r K))).comp
              (Subgroup.subgroupOfEquivOfLe hΩO).toMonoidHom =
            (s16ntNatRep (orthGroup (StatedQuadPlus r K))).comp H.subtype := by
          ext g x i
          simp [s16ntNatRep, Subgroup.subgroupOfEquivOfLe]
        rw [← hrep]
        exact s16nt_h1_congr (Subgroup.subgroupOfEquivOfLe hΩO)
          (s16ntNatRep (StatedOmega (StatedQuadPlus r K)))
      have horth := s16nt_orth_h1_plus_two (K := K) hr hK2
      rw [hcongr] at hidx
      omega
  exact s16nt_cover_of_h1 _ hbound

theorem s16nt_cover_omMinus {K : Type} [Field K] [Finite K] {r a : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2 ^ a) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    S16BoundCover (FFModel.nat (StatedOmega (StatedQuadMinus r K b c))) (2 * a) := by
  have ha1 : 1 ≤ a := s16nt_one_le_of_card hK
  haveI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ a := by rw [← Nat.card_eq_fintype_card]; exact hK
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hF
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨l, hl⟩ := w183_exists_dual_ne_zero (K := K)
  let B : LinearMap.BilinForm K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) :=
    QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus r K b c)
  have hB : B.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
      (n := r) (K := K) hirr
  let β : LinearMap.BilinForm (ZMod 2) (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) :=
    w183_binForm B l
  have hβ : β.Nondegenerate := w183_binForm_nondegenerate B hB l hl
  have hβinv : ∀ g ∈ StatedOmega (StatedQuadMinus r K b c),
      ∀ x y : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K,
      β (Matrix.mulVec (g : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2)
            (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K) x)
        (Matrix.mulVec (g : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2)
            (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K) y) = β x y := by
    intro g hg x y
    have hgO : g ∈ orthGroup (StatedQuadMinus r K b c) := statedOmega_le_orthGroup _ hg
    have hBxy := w183_polar_invariant_minus hirr g hgO x y
    exact w183_binForm_invariant B g x y hBxy l
  have hdual : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1
        (Representation.dual (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c))))) =
      Module.finrank (ZMod 2)
        (CFSG.Quasithin.JonesParshall.H1
          (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c)))) :=
    s16nt_h1_dual_natRep _ β hβ hβinv
  have hbound : Module.finrank (ZMod 2)
      (CFSG.Quasithin.JonesParshall.H1
        (Representation.dual (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c))))) ≤
        2 * a := by
    rw [hdual]
    by_cases ha : 2 ≤ a
    · rw [s16nt_omega_h1_minus_big (K := K) hr ha hK hirr]
      omega
    · have haeq : a = 1 := by omega
      subst haeq
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hΩO : StatedOmega (StatedQuadMinus r K b c) ≤
          orthGroup (StatedQuadMinus r K b c) :=
        statedOmega_le_orthGroup _
      let H := (StatedOmega (StatedQuadMinus r K b c)).subgroupOf
        (orthGroup (StatedQuadMinus r K b c))
      haveI hHn : H.Normal := w183_normal_subgroupOf_omega (StatedQuadMinus r K b c)
      obtain ⟨s, hsO, hs2, hgen⟩ := s16nt_orth_index_two_minus_two (K := K) hr hK2 hirr
      have hs' : (⟨s, hsO⟩ : ↥(orthGroup (StatedQuadMinus r K b c))) ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hs2
      have hG : ∀ g : ↥(orthGroup (StatedQuadMinus r K b c)), g ∈ H ∨ g * ⟨s, hsO⟩ ∈ H := by
        intro g
        rcases hgen g g.2 with h | h
        · left; rw [Subgroup.mem_subgroupOf]; exact h
        · right; rw [Subgroup.mem_subgroupOf]; simpa using h
      have hfix : ∀ n : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K,
          (∀ h : ↥H, (s16ntNatRep (orthGroup (StatedQuadMinus r K b c)) h) n = n) → n = 0 := by
        intro n hn
        apply s16nt_omega_fix_minus_two (K := K) hr hK2 hirr n
        intro A hA
        have hhh := hn (⟨⟨A, hΩO hA⟩, hA⟩ : ↥H)
        simpa [s16ntNatRep, Matrix.mulVecLin_apply] using hhh
      have hidx := s16nt_h1_index_two
        (s16ntNatRep (orthGroup (StatedQuadMinus r K b c))) H hs' hG hfix
      have hcongr : Module.finrank (ZMod 2)
            (CFSG.Quasithin.JonesParshall.H1
              ((s16ntNatRep (orthGroup (StatedQuadMinus r K b c))).comp H.subtype)) =
          Module.finrank (ZMod 2)
            (CFSG.Quasithin.JonesParshall.H1
              (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c)))) := by
        have hrep : (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c))).comp
              (Subgroup.subgroupOfEquivOfLe hΩO).toMonoidHom =
            (s16ntNatRep (orthGroup (StatedQuadMinus r K b c))).comp H.subtype := by
          ext g x i
          simp [s16ntNatRep, Subgroup.subgroupOfEquivOfLe]
        rw [← hrep]
        exact s16nt_h1_congr (Subgroup.subgroupOfEquivOfLe hΩO)
          (s16ntNatRep (StatedOmega (StatedQuadMinus r K b c)))
      have horth := s16nt_orth_h1_minus_two (K := K) hr hK2 hirr
      rw [hcongr, horth] at hidx
      omega
  exact s16nt_cover_of_h1 _ hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

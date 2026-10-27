module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagCore
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.RankThree.PartOne.K133C.SpForm
public import CFSG.RankThree.PartOne.K133C.FixedVectors
public import CFSG.RankThree.PartOne.K133C.LinearPlane

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.RankThree.PartOne.K133C
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {K : Type} [Field K] {n : ℕ}

private lemma rckFlagSp_form_self (u : Fin n ⊕ Fin n → K) : form (K := K) (n := n) u u = 0 := by
  rw [form_apply, Fintype.sum_sum_type]
  simp only [par_inl, par_inr, sgn_inl, sgn_inr]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i _ => by ring

private lemma rckFlagSp_gram_transpose [CharP K 2] :
    Matrix.transpose (gram K n) = gram K n := by
  rw [gram_eq_neg_J, Matrix.transpose_neg, Matrix.J_transpose, neg_neg]
  ext i j
  rw [Matrix.neg_apply]
  exact (CharTwo.neg_eq (Matrix.J (Fin n) K i j)).symm

private lemma rckFlagSp_exists_form_ne {x : Fin n ⊕ Fin n → K} (hx : x ≠ 0) :
    ∃ m : Fin n ⊕ Fin n → K, form (K := K) (n := n) x m ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine ⟨Pi.single (par a) 1, ?_⟩
  rw [form_single_right, par_par]
  exact mul_ne_zero ha (sgn_ne_zero a)

private theorem rckFlagSp_irredW_general [CharP K 2] (n : ℕ) :
    FlagIrredW (CFSG.Open.StatedSp n K).subtype
      (some fun u v => u ⬝ᵥ ((gram K n).mulVec v)) := by
  intro R' W H hWH hv hB r hr hr1 P hPW hInv
  by_cases hbot : P = ⊥
  · exact Or.inl hbot
  right
  by_cases hdimle : Module.finrank K W ≤ 1
  · haveI : FiniteDimensional K W := FiniteDimensional.finiteDimensional_submodule W
    haveI : FiniteDimensional K P := Submodule.finiteDimensional_of_le hPW
    have hP1 : 1 ≤ Module.finrank K P := (Submodule.one_le_finrank_iff).2 hbot
    have hle : Module.finrank K P ≤ Module.finrank K W := Submodule.finrank_mono hPW
    exact Submodule.eq_of_le_of_finrank_eq hPW (by omega)
  · have hdimne : Module.finrank K W ≠ 1 := fun h => hdimle (le_of_eq h)
    have hJ : Matrix.transpose (gram K n) = gram K n :=
      rckFlagSp_gram_transpose (K := K) (n := n)
    have hJa : ∀ y : Fin n ⊕ Fin n → K, y ⬝ᵥ ((gram K n).mulVec y) = 0 :=
      fun y => rckFlagSp_form_self (K := K) (n := n) y
    let R : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) := Matrix.toLin' (mat n K r)
    let N : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) := R - 1
    have hbf : ∀ y z : Fin n ⊕ Fin n → K, bf (gram K n) y z = form y z := fun _ _ => rfl
    have hN_eq : N = Matrix.toLin' (mat n K r - 1) := by
      show R - 1 = Matrix.toLin' (mat n K r - 1)
      rw [map_sub, Matrix.toLin'_one]
      rfl
    have hNrange : N.range = W := by rw [hN_eq]; exact (hv r hr hr1).1
    have hNker : N.ker = H := by rw [hN_eq]; exact (hv r hr hr1).2
    have hNalt : ∀ z : Fin n ⊕ Fin n → K, bf (gram K n) z (N z) = 0 := by
      intro z
      have h := (hB (fun u v => u ⬝ᵥ ((gram K n).mulVec v)) (by simp)).resolve_right hdimne
      have hz := h r hr z
      simpa [CFSG.RankThree.PartOne.K133C.bf, N, R, Matrix.toLin'_apply,
        Matrix.sub_mulVec, Matrix.one_mulVec, mat_apply] using hz
    have hF1 : ∀ x y : Fin n ⊕ Fin n → K,
        bf (gram K n) x (N y) = bf (gram K n) (N x) y := by
      intro x y
      have h := hNalt (x + y)
      simp only [map_add, bf_add_left, bf_add_right, hNalt, zero_add, add_zero] at h
      have hsym : bf (gram K n) y (N x) = bf (gram K n) (N x) y :=
        bf_comm (gram K n) hJ y (N x)
      rw [hsym] at h
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h - (bf (gram K n) (N x) y) * h2
    have hR : ∀ x y : Fin n ⊕ Fin n → K,
        bf (gram K n) (R x) (R y) = bf (gram K n) x y := by
      intro x y
      have h := form_mulVec (K := K) (n := n) r x y
      simpa [hbf, R, Matrix.toLin'_apply] using h
    have hF2 : ∀ x y : Fin n ⊕ Fin n → K, bf (gram K n) (N x) (N y) = 0 := by
      intro x y
      have hRxy := hR x y
      have hRx : R x = N x + x := by
        show R x = (R - 1) x + x
        rw [LinearMap.sub_apply]
        change R x = R x - x + x
        exact (sub_add_cancel (R x) x).symm
      have hRy : R y = N y + y := by
        show R y = (R - 1) y + y
        rw [LinearMap.sub_apply]
        change R y = R y - y + y
        exact (sub_add_cancel (R y) y).symm
      have hmain : bf (gram K n) (N x) (N y) + bf (gram K n) (N x) y +
          bf (gram K n) x (N y) + bf (gram K n) x y = bf (gram K n) x y := by
        have h := hRxy
        rw [hRx, hRy] at h
        simp only [bf_add_left, bf_add_right] at h
        linear_combination h
      have hlin : bf (gram K n) (N x) (N y) + bf (gram K n) (N x) y +
          bf (gram K n) x (N y) = 0 := by
        have h0 : bf (gram K n) (N x) (N y) + bf (gram K n) (N x) y +
            bf (gram K n) x (N y) + bf (gram K n) x y = 0 + bf (gram K n) x y := by
          rw [zero_add]; exact hmain
        exact add_right_cancel h0
      rw [hF1 x y] at hlin
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hlin - (bf (gram K n) (N x) y) * h2
    have hWiso : ∀ x ∈ W, ∀ y ∈ W, bf (gram K n) x y = 0 := by
      intro x hx y hy
      rw [← hNrange] at hx hy
      obtain ⟨x', rfl⟩ := LinearMap.mem_range.mp hx
      obtain ⟨y', rfl⟩ := LinearMap.mem_range.mp hy
      exact hF2 x' y'
    have hR_eq : R = N + 1 := (sub_add_cancel R 1).symm
    obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hbot
    have hxW : x ∈ W := hPW hxP
    obtain ⟨m, hxm⟩ := rckFlagSp_exists_form_ne (K := K) (n := n) hx0
    have hkey : ∀ m' : Fin n ⊕ Fin n → K, bf (gram K n) x m' ≠ 0 → N m' ∈ P := by
      intro m' hm'
      set u' : Fin n ⊕ Fin n → K := N m' with hu'
      have hu'mem : u' ∈ W := by
        rw [hu', ← hNrange]
        exact LinearMap.mem_range_self N m'
      have hNu' : N u' = 0 := by
        have : u' ∈ N.ker := by rw [hNker]; exact hWH hu'mem
        simpa using this
      have hmu' : bf (gram K n) m' u' = 0 := by
        rw [hu']; exact hNalt m'
      let Gmat : GL (Fin n ⊕ Fin n) K := sglGL (gram K n) hJ hJa m' u'
      have hGmem : Gmat ∈ CFSG.Open.StatedSp n K :=
        mem_statedSp_iff.2 (sglGL_mem_isoGrp (gram K n) hJ hJa hmu')
      let G : CFSG.Open.StatedSp n K := ⟨Gmat, hGmem⟩
      have hmatG : mat n K G = sglM (gram K n) m' u' := by
        change ((Gmat : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
          sglM (gram K n) m' u'
        exact coe_sglGL (gram K n) hJ hJa hmu'
      have hGcomm : G ∈ Subgroup.centralizer ({r} : Set (CFSG.Open.StatedSp n K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply mat_injective
        rw [map_mul, map_mul]
        have hcomm_lin : Matrix.toLin' (mat n K G) * R = R * Matrix.toLin' (mat n K G) := by
          have hMN_pt : ∀ z : Fin n ⊕ Fin n → K,
              Matrix.toLin' (mat n K G) (N z) = N (Matrix.toLin' (mat n K G) z) := by
            intro z
            have hz : Matrix.toLin' (mat n K G) z = sglM (gram K n) m' u' *ᵥ z := by
              rw [hmatG, Matrix.toLin'_apply]
            have hz' : Matrix.toLin' (mat n K G) (N z) =
                sglM (gram K n) m' u' *ᵥ (N z) := by
              rw [hmatG, Matrix.toLin'_apply]
            have h1 : bf (gram K n) (N z) u' = 0 := by rw [hu']; exact hF2 z m'
            have h2 : bf (gram K n) (N z) m' = bf (gram K n) z u' := by
              rw [← hF1 z m', hu']
            rw [hz, hz', sglM_mulVec, sglM_mulVec, map_add, map_add, map_smul, map_smul,
              h1, h2, hNu', ← hu']
            simp only [zero_smul, smul_zero, add_zero]
          have hMN : Matrix.toLin' (mat n K G) * N = N * Matrix.toLin' (mat n K G) := by
            apply LinearMap.ext
            intro z
            simpa only [Module.End.mul_apply] using hMN_pt z
          rw [hR_eq, mul_add, add_mul, mul_one, one_mul, hMN]
        apply Matrix.toLin'.injective
        rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
        exact hcomm_lin
      have hxG : mat n K G *ᵥ x = x + bf (gram K n) x m' • u' := by
        rw [hmatG, sglM_mulVec]
        have : bf (gram K n) x u' = 0 := hWiso x hxW u' hu'mem
        rw [this, zero_smul, add_zero]
      have hxP' : mat n K G *ᵥ x ∈ P := by
        have h := hInv G hGcomm x hxP
        change ((G : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x ∈ P
        exact h
      have hmem : bf (gram K n) x m' • u' ∈ P := by
        have h := Submodule.sub_mem P hxP' hxP
        rw [hxG] at h
        simpa using h
      have hup : u' ∈ P := by
        have h := P.smul_mem (bf (gram K n) x m')⁻¹ hmem
        simpa [smul_smul, inv_mul_cancel₀ hm'] using h
      simpa [hu'] using hup
    have hWleP : W ≤ P := by
      intro w hw
      rw [← hNrange] at hw
      obtain ⟨m'', rfl⟩ := LinearMap.mem_range.mp hw
      by_cases hm'' : bf (gram K n) x m'' = 0
      · have hsum : bf (gram K n) x (m'' + m) ≠ 0 := by
          rw [bf_add_right, hm'', zero_add]
          exact hxm
        have h1 : N (m'' + m) ∈ P := hkey (m'' + m) hsum
        have h2 : N m ∈ P := hkey m hxm
        have heq : N m'' = N (m'' + m) - N m := by rw [map_add]; abel
        rw [heq]
        exact Submodule.sub_mem P h1 h2
      · exact hkey m'' hm''
    exact le_antisymm hPW hWleP

theorem rckFlagIrredW_Sp (n g : ℕ) (hg : 1 ≤ g) :
    FlagIrredW (CFSG.Open.StatedSp n (GaloisField 2 g)).subtype
      (some fun u v => u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 g)).mulVec v)) := by
  simpa only [gram] using rckFlagSp_irredW_general (K := GaloisField 2 g) n

theorem rckFlagCent_Sp (n g : ℕ) (hg : 1 ≤ g) :
    FlagCentU (CFSG.Open.StatedSp n (GaloisField 2 g)).subtype
      (some fun u v => u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 g)).mulVec v)) := by
  exact flagCentU_of_irredW
    (CFSG.Open.StatedSp n (GaloisField 2 g)).subtype
    (some fun u v => u ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 g)).mulVec v))
    (Subgroup.subtype_injective _) (rckFlagIrredW_Sp n g hg)

end CFSG.StandardType.RCKFlag

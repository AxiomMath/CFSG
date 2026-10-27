module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Pair
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeTrans
import CFSG.HardMathSupport.Curtis.Coordinator.TorCenterSL3Order
import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure
import CFSG.HardMathSupport.RichardWeiss.Proving.ThreeCycleTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.Monomial
import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwoSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup Matrix CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

namespace L3Normal

theorem diagSL_coe_diagonal {F : Type} [Field F] (a b d : F) (h : a * b * d = 1) :
    ((diagSL a b d h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagSL]

theorem shiftSL_coe_matrix {F : Type} [Field F] :
    ((shiftSL : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shiftSL]

theorem shiftSL_matrix_pow_two {F : Type} [Field F] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) ^ 2 =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem mul_eq_mul_of_isDiag {F : Type} [Field F] {u v : SL(3, F)}
    (hu : ((u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hv : ((v : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag) :
    u * v = v * u := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← hu.diagonal_diag, ← hv.diagonal_diag, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem diagSL_mul_shift {F : Type} [Field F] {t0 t1 t2 : F} (ht : t0 * t1 * t2 = 1)
    {d : Fin 3 → F} (h02 : t0 * d 0 = t2) (h10 : t1 * d 1 = t0) (h21 : t2 * d 2 = t1)
    {b : SL(3, F)}
    (hb : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) :
    diagSL t0 t1 t2 ht * b = shiftSL * diagSL t0 t1 t2 ht := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hb,
    diagSL_coe_diagonal, shiftSL_coe_matrix]
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h02, h10, h21]

theorem diagSL_mul_shift_sq {F : Type} [Field F] {t0 t1 t2 : F} (ht : t0 * t1 * t2 = 1)
    {d : Fin 3 → F} (h01 : t0 * d 0 = t1) (h12 : t1 * d 1 = t2) (h20 : t2 * d 2 = t0)
    {b : SL(3, F)}
    (hb : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 1, 0; 0, 0, 1; 1, 0, 0]) :
    diagSL t0 t1 t2 ht * b = shiftSL ^ 2 * diagSL t0 t1 t2 ht := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hb,
    diagSL_coe_diagonal]
  rw [Matrix.SpecialLinearGroup.coe_pow, shiftSL_coe_matrix, shiftSL_matrix_pow_two]
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, h01, h12, h20]

theorem exists_mul_ne_mul_of_inf_centralizer_eq_bot {G : Type*} [Group G] {B R : Subgroup G}
    {b : G} (hb : B = Subgroup.zpowers b) (hRcard : Nat.card R = 49)
    (hinf : R ⊓ centralizer (B : Set G) = ⊥) : ∃ u ∈ R, b * u ≠ u * b := by
  by_contra h
  push Not at h
  have hRle : R ≤ Subgroup.centralizer (B : Set G) := by
    intro r hr
    rw [hb, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact h r hr
  have hbot : R ≤ (⊥ : Subgroup G) := by
    rw [← hinf]
    exact le_inf le_rfl hRle
  have hRbot : R = ⊥ := le_bot_iff.mp hbot
  rw [hRbot] at hRcard
  simp at hRcard

theorem exists_conj_diag_of_isElemAbelian {F : Type} [Field F] [Finite F]
    (h7 : 7 ∣ Nat.card F - 1) {R : Subgroup SL(3, F)} (hR : CFSG.Open.IsElemAbelian 7 R) :
    ∃ γ : SL(3, F), ∀ u ∈ R.map (MulAut.conj γ).toMonoidHom,
      ((u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
  obtain ⟨ζ, hζ⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.exists_primitiveRoot_of_dvd (d := 7) h7
  have hcommR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro x hx y hy
    have : IsMulCommutative R := hR.1
    simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : R) (⟨y, hy⟩ : R))
  obtain ⟨γ, hγ⟩ :=
    CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_sl_conj_diag R (m := 7) hζ
      hcommR (fun x hx => hR.2 x hx)
  refine ⟨γ, ?_⟩
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
  have hcoe : (((MulAut.conj γ).toMonoidHom x : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) = ((γ * x * γ⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    simp [MulAut.conj_apply]
  rw [hcoe]
  exact hγ x hx

theorem exists_separating_map_toGL {F : Type} [Field F] {R₁ : Subgroup SL(3, F)}
    (hcard : Nat.card R₁ = 49)
    (hdiag : ∀ u ∈ R₁, ((u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hexp : ∀ u ∈ R₁, u ^ 7 = 1) :
    ∀ i j : Fin 3, i ≠ j → ∃ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i ≠
        ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j := by
  intro i j hij
  have hcard' : Nat.card (R₁.map Matrix.SpecialLinearGroup.toGL) = 7 ^ 2 := by
    rw [Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective, hcard]
    norm_num
  have hdiag' : ∀ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    exact hdiag x hx
  have hdet' : ∀ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    simp
  have hexp' : ∀ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL, u ^ 7 = 1 := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_pow, hexp x hx, map_one]
  exact exists_diag_entry_ne_of_card (p := 7) (by norm_num) hdiag' hdet' hexp' hcard' hij

theorem exists_generator_shift_pow {F : Type} [Field F]
    {B R R₁ : Subgroup SL(3, F)} {γ : SL(3, F)}
    (hBR : IsKGenPair B R) (hR₁def : R₁ = R.map (MulAut.conj γ).toMonoidHom)
    (hdiag : ∀ u ∈ R₁, ((u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag)
    (hsep : ∀ i j : Fin 3, i ≠ j → ∃ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i ≠
        ((u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j) :
    ∃ (b₁ : SL(3, F)) (d : Fin 3 → F) (k : ℕ),
      B.map (MulAut.conj γ).toMonoidHom = Subgroup.zpowers b₁ ∧
      ((b₁ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k ∧ (k = 1 ∨ k = 2) := by
  obtain ⟨hBcard, hRelem, hRcard, hBRnorm, hRinf⟩ := hBR
  have hexp : ∀ u ∈ R₁, u ^ 7 = 1 := by
    intro u hu
    rw [hR₁def] at hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_pow, hRelem.2 x hx, map_one]
  obtain ⟨b, hbB, hborder, hbz⟩ :=
    CFSG.HardMathSupport.RichardWeiss.Proving.exists_zpowers_eq_of_card_three hBcard
  have hb3 : b ^ 3 = 1 := by
    simpa [hborder] using pow_orderOf_eq_one b
  set b₁ : SL(3, F) := (MulAut.conj γ).toMonoidHom b with hb₁def
  have hB₁eq : B.map (MulAut.conj γ).toMonoidHom = Subgroup.zpowers b₁ := by
    rw [← hbz, MonoidHom.map_zpowers, hb₁def]
  have hb₁3 : b₁ ^ 3 = 1 := by
    rw [hb₁def, ← map_pow, hb3, map_one]
  have hB₁norm : B.map (MulAut.conj γ).toMonoidHom ≤ normalizer (R₁ : Set SL(3, F)) := by
    have h := Subgroup.map_mono (f := (MulAut.conj γ).toMonoidHom) hBRnorm
    rwa [Subgroup.map_equiv_normalizer_eq, ← hR₁def] at h
  have hb₁norm : b₁ ∈ normalizer (R₁ : Set SL(3, F)) :=
    hB₁norm (by rw [hB₁eq]; exact Subgroup.mem_zpowers b₁)
  have hb₁R : ∀ u ∈ R₁, b₁ * u * b₁⁻¹ ∈ R₁ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hb₁norm u).mp hu
  have hbnc : ∃ u ∈ R, b * u ≠ u * b :=
    exists_mul_ne_mul_of_inf_centralizer_eq_bot hbz.symm hRcard hRinf
  have hb₁nc : ∃ u ∈ R₁, b₁ * u ≠ u * b₁ := by
    obtain ⟨r, hr, hbr⟩ := hbnc
    refine ⟨(MulAut.conj γ).toMonoidHom r, ?_, ?_⟩
    · rw [hR₁def]
      exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    · intro hconj
      have hmul : (MulAut.conj γ).toMonoidHom (b * r) =
          (MulAut.conj γ).toMonoidHom (r * b) := by
        rw [map_mul, map_mul]
        simpa [hb₁def] using hconj
      exact hbr ((MulAut.conj γ).injective hmul)
  have hb3g : Matrix.SpecialLinearGroup.toGL b₁ ^ 3 = 1 := by
    rw [← map_pow, hb₁3, map_one]
  have hbRg : ∀ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      Matrix.SpecialLinearGroup.toGL b₁ * u *
        (Matrix.SpecialLinearGroup.toGL b₁)⁻¹ ∈ R₁.map Matrix.SpecialLinearGroup.toGL := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    refine Subgroup.mem_map.mpr ⟨b₁ * x * b₁⁻¹, hb₁R x hx, ?_⟩
    simp
  have hbcRg : ∃ u ∈ R₁.map Matrix.SpecialLinearGroup.toGL,
      Matrix.SpecialLinearGroup.toGL b₁ * u ≠
        u * Matrix.SpecialLinearGroup.toGL b₁ := by
    obtain ⟨u, hu, hune⟩ := hb₁nc
    refine ⟨Matrix.SpecialLinearGroup.toGL u, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    · intro hcon
      exact hune (Matrix.SpecialLinearGroup.toGL_injective (by simpa using hcon))
  obtain ⟨d, k, hk, hbk⟩ :=
    exists_diagonal_mul_shift_pow (R := R₁.map Matrix.SpecialLinearGroup.toGL)
      (b := Matrix.SpecialLinearGroup.toGL b₁) (by
        intro u hu
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
        simpa using hdiag x hx) hsep hb3g hbRg hbcRg
  exact ⟨b₁, d, k, hB₁eq, hbk, hk⟩

theorem exists_diagSL_mul_shift_pow {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) {b : SL(3, F)} {d : Fin 3 → F} {k : ℕ}
    (hk : k = 1 ∨ k = 2)
    (hb : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k) :
    ∃ t : SL(3, F), ((t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag ∧
      t * b = (shiftSL : SL(3, F)) ^ k * t := by
  have hdetσ : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← shiftSL_coe_matrix]
    exact Matrix.SpecialLinearGroup.det_coe shiftSL
  have hd012 : d 0 * d 1 * d 2 = 1 := by
    have hdet : (diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ^ k).det = 1 := by
      rw [← hb]
      exact Matrix.SpecialLinearGroup.det_coe b
    rcases hk with rfl | rfl
    · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, pow_one, hdetσ,
        mul_one] at hdet
      simpa using hdet
    · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three, Matrix.det_pow, hdetσ,
        one_pow, mul_one] at hdet
      simpa using hdet
  have hd0 : d 0 ≠ 0 := by
    intro h0
    simp [h0] at hd012
  have hd1 : d 1 ≠ 0 := by
    intro h1
    simp [h1] at hd012
  have hd2 : d 2 ≠ 0 := by
    intro h2
    simp [h2] at hd012
  rcases hk with rfl | rfl
  · obtain ⟨s, hs⟩ :=
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.cube_bijective hq).2
        (((d 0) ^ 2 * d 2)⁻¹)
    have hs' : s ^ 3 = ((d 0) ^ 2 * d 2)⁻¹ := hs
    have ht : s * (s * d 0 * d 2) * (s * d 0) = 1 := by
      have h : s * (s * d 0 * d 2) * (s * d 0) = s ^ 3 * (d 0) ^ 2 * d 2 := by ring
      rw [h, hs', mul_assoc, inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 2 hd0) hd2)]
    refine ⟨diagSL s (s * d 0 * d 2) (s * d 0) ht, ?_, ?_⟩
    · rw [diagSL_coe_diagonal]
      exact Matrix.isDiag_diagonal _
    · have hb' : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
          diagonal d * !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
        simpa using hb
      have h := diagSL_mul_shift ht (by ring) (by
        rw [show s * d 0 * d 2 * d 1 = s * (d 0 * d 1 * d 2) by ring, hd012, mul_one])
        (by ring) hb'
      simpa using h
  · obtain ⟨s, hs⟩ :=
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.cube_bijective hq).2
        (((d 0) ^ 2 * d 1)⁻¹)
    have hs' : s ^ 3 = ((d 0) ^ 2 * d 1)⁻¹ := hs
    have ht : s * (s * d 0) * (s * d 0 * d 1) = 1 := by
      have h : s * (s * d 0) * (s * d 0 * d 1) = s ^ 3 * (d 0) ^ 2 * d 1 := by ring
      rw [h, hs', mul_assoc, inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero 2 hd0) hd1)]
    refine ⟨diagSL s (s * d 0) (s * d 0 * d 1) ht, ?_, ?_⟩
    · rw [diagSL_coe_diagonal]
      exact Matrix.isDiag_diagonal _
    · have hb' : ((b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
          diagonal d * !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
        simpa [shiftSL_matrix_pow_two] using hb
      have h := diagSL_mul_shift_sq ht (by ring) (by ring) (by
        rw [show s * d 0 * d 1 * d 2 = s * (d 0 * d 1 * d 2) by ring, hd012, mul_one]) hb'
      simpa using h

end L3Normal

theorem exists_conj_eq_zpowers_shiftSL {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) (h7 : 7 ∣ Nat.card F - 1) {B R : Subgroup SL(3, F)}
    (hBR : IsKGenPair B R) :
    ∃ g : SL(3, F), B.map (MulAut.conj g).toMonoidHom = zpowers shiftSL ∧
      ∀ (a b d : F) (h : a * b * d = 1),
        diagSL a b d h ∈ centralizer ((R.map (MulAut.conj g).toMonoidHom : Subgroup SL(3, F)) :
          Set SL(3, F)) := by
  obtain ⟨γ, hdiagγ⟩ := L3Normal.exists_conj_diag_of_isElemAbelian h7 hBR.2.1
  set R₁ : Subgroup SL(3, F) := R.map (MulAut.conj γ).toMonoidHom with hR₁def
  have hR₁card : Nat.card R₁ = 49 := by
    rw [hR₁def, Subgroup.card_map_of_injective (MulAut.conj γ).injective, hBR.2.2.1]
  have hdiag₁ : ∀ u ∈ R₁, ((u : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).IsDiag := by
    intro u hu
    rw [hR₁def] at hu
    exact hdiagγ u hu
  have hexp₁ : ∀ u ∈ R₁, u ^ 7 = 1 := by
    intro u hu
    rw [hR₁def] at hu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    rw [← map_pow, hBR.2.1.2 x hx, map_one]
  have hsep := L3Normal.exists_separating_map_toGL hR₁card hdiag₁ hexp₁
  obtain ⟨b₁, d, k, hB₁eq, hbk, hk⟩ :=
    L3Normal.exists_generator_shift_pow hBR hR₁def hdiag₁ hsep
  obtain ⟨t, htdiag, htc⟩ := L3Normal.exists_diagSL_mul_shift_pow hq hk hbk
  have htfix : ∀ u ∈ R₁, (MulAut.conj t).toMonoidHom u = u := by
    intro u hu
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      L3Normal.mul_eq_mul_of_isDiag htdiag (hdiag₁ u hu), mul_assoc, mul_inv_cancel, mul_one]
  have hRfix : R₁.map (MulAut.conj t).toMonoidHom = R₁ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [htfix u hu]
      exact hu
    · intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, htfix x hx⟩
  set g : SL(3, F) := t * γ with hg
  have hcomp : (MulAut.conj g).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp (MulAut.conj γ).toMonoidHom := by
    ext x
    simp [hg, MulAut.conj_apply, mul_assoc]
  have hBmap : B.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers shiftSL := by
    rw [hcomp, ← Subgroup.map_map, hB₁eq, MonoidHom.map_zpowers]
    have hconjb : (MulAut.conj t).toMonoidHom b₁ = (shiftSL : SL(3, F)) ^ k := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconjb]
    rcases hk with rfl | rfl
    · simp
    · have hsq : (shiftSL : SL(3, F)) ^ 2 = shiftSL⁻¹ :=
        eq_inv_of_mul_eq_one_left (by
          rw [← pow_succ]
          exact CFSG.RankThree.PartTwo.Sec17.Proof17Res10.shiftSL_pow_three)
      rw [hsq, Subgroup.zpowers_inv]
  have hRmap : R.map (MulAut.conj g).toMonoidHom = R₁ := by
    rw [hcomp, ← Subgroup.map_map, ← hR₁def, hRfix]
  refine ⟨g, hBmap, ?_⟩
  intro a b d h
  rw [hRmap, Subgroup.mem_centralizer_iff]
  intro u hu
  exact (L3Normal.mul_eq_mul_of_isDiag (u := diagSL a b d h) (v := u) (by
    rw [L3Normal.diagSL_coe_diagonal]
    exact Matrix.isDiag_diagonal _) (hdiag₁ u hu)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

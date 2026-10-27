module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylowParameter
import CFSG.HardMathSupport.Solomon.Proving.PSL2CommutantAffine
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralAut
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

private theorem isOddPrimePower189 [Finite F] (hF : Odd (Nat.card F)) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card] at hF ⊢
  rw [hn] at hF ⊢
  exact ⟨ringChar F, n, hp, (Nat.odd_pow_iff n.ne_zero).1 hF, n.pos, rfl⟩

theorem eq_one_of_mem_center_of_pow_three189 (h3 : ∀ a : Fˣ, a ^ 3 = 1 → a = 1)
    {c : GL (Fin 2) F} (hc : c ∈ Subgroup.center (GL (Fin 2) F)) (hc3 : c ^ 3 = 1) : c = 1 := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, rfl⟩ := hc
  have hu : u ^ 3 = 1 := by
    have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hc3
    simp only [← map_pow, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
      Units.val_one, one_apply_eq] at h
    exact Units.ext (by simpa using h)
  rw [h3 u hu, map_one]

theorem eq_of_mem_center_of_sq189 {g h : GL (Fin 2) F}
    (hg : g ∈ Subgroup.center (GL (Fin 2) F)) (hh : h ∈ Subgroup.center (GL (Fin 2) F))
    (hg2 : g ^ 2 = 1) (hh2 : h ^ 2 = 1) (hg1 : g ≠ 1) (hh1 : h ≠ 1) : g = h := by
  have key : ∀ k : GL (Fin 2) F, k ∈ Subgroup.center (GL (Fin 2) F) → k ^ 2 = 1 → k ≠ 1 →
      k = GeneralLinearGroup.scalar (Fin 2) (-1) := by
    intro k hk hk2 hk1
    rw [GeneralLinearGroup.center_eq_range_scalar] at hk
    obtain ⟨u, rfl⟩ := hk
    have hu : (u : F) * u = 1 := by
      have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) hk2
      simp only [← map_pow, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
        Units.val_one, one_apply_eq] at h
      simpa [sq] using h
    rcases mul_self_eq_one_iff.1 hu with h1 | h1
    · exact absurd (by rw [show u = 1 from Units.ext h1, map_one]) hk1
    · rw [show u = -1 from Units.ext (by simpa using h1)]
  rw [key g hg hg2 hg1, key h hh hh2 hh1]

theorem commute_of_not_mem_center189 {g a b : GL (Fin 2) F}
    (hg : g ∉ Subgroup.center (GL (Fin 2) F)) (ha : a * g = g * a) (hb : b * g = g * b) :
    a * b = b * a := by
  apply Units.ext
  simp only [Units.val_mul]
  refine CFSG.HardMathSupport.Solomon.Proving.PSL2Even.mul_comm_of_commute_nonscalar
    (g : Matrix (Fin 2) (Fin 2) F) a b ?_
    (by simpa only [Units.val_mul] using congrArg Units.val ha)
    (by simpa only [Units.val_mul] using congrArg Units.val hb)
  intro r hr
  apply hg
  rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  exact ⟨r, by rw [hr, scalar_apply, smul_one_eq_diagonal]⟩

theorem mulAut_eq_one_of_dihedral189 {D : Type*} [Group D] {m : ℕ} (hm : 2 ≤ m)
    (e : D ≃* DihedralGroup (2 ^ m)) (ψ : MulAut D) (hψ : ψ ^ 3 = 1) : ψ = 1 := by
  let ψ' : MulAut (DihedralGroup (2 ^ m)) := (e.symm.trans ψ).trans e
  have key : ∀ n : ℕ, ∀ d, (ψ' ^ n) d = e ((ψ ^ n) (e.symm d)) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply]
      simp [ψ']
  have h1 : ψ' = 1 := CFSG.ComponentClassification.HarrisLit.dihedral_mulAut_eq_one_of_odd hm ψ'
    (k := 3) (by decide) (by ext d; rw [key, hψ]; simp)
  ext d
  have h := key 1 (e d)
  rw [h1, pow_one, pow_one, MulEquiv.symm_apply_apply, MulAut.one_apply] at h
  rw [MulAut.one_apply]
  exact (e.injective h).symm

theorem conj_pow_eq_mul_pow189 {G : Type*} [Group G] {y t c : G} (hc : ∀ g : G, g * c = c * g)
    (h : y * t * y⁻¹ = t * c) (n : ℕ) : y ^ n * t * (y ^ n)⁻¹ = t * c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcn : y⁻¹ * c ^ n = c ^ n * y⁻¹ := Commute.pow_right (hc y⁻¹) n
    calc y ^ (n + 1) * t * (y ^ (n + 1))⁻¹ = y * (y ^ n * t * (y ^ n)⁻¹) * y⁻¹ := by
          rw [pow_succ', _root_.mul_inv_rev]; simp only [mul_assoc]
      _ = y * t * (y⁻¹ * c ^ n) := by rw [ih, hcn]; simp only [mul_assoc]
      _ = t * c ^ (n + 1) := by rw [← mul_assoc, h, pow_succ', mul_assoc]

theorem false_of_commute_sylow_gl2_189 [Finite F] (hF : Odd (Nat.card F))
    (T : Sylow 2 (GL (Fin 2) F))
    (hT : ∀ a ∈ (T : Subgroup (GL (Fin 2) F)), ∀ b ∈ (T : Subgroup (GL (Fin 2) F)),
      a * b = b * a) : False := by
  have hF' := isOddPrimePower189 hF
  let D : Sylow 2 (PGL(2, F)) := T.mapSurjective ProjGenLinGroup.mk_surjective
  obtain ⟨m, -, ⟨eD⟩⟩ := CFSG.GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hF' D
  have hm := CFSG.GorensteinWalter.pgl2_dihedral_sylow_parameter_ge_two F hF' D eD
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine DihedralGroup.not_commutative (n := 2 ^ m) (by omega) (by omega) ⟨⟨fun u v => ?_⟩⟩
  obtain ⟨a, ha, hau⟩ := Subgroup.mem_map.1 (eD.symm u).2
  obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.1 (eD.symm v).2
  have hcomm : eD.symm u * eD.symm v = eD.symm v * eD.symm u := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hau, ← hbv, ← map_mul, ← map_mul, hT a ha b hb]
  simpa using congrArg eD hcomm

theorem eq_one_of_mem_normalizer_gl2_189 [Finite F] (hF : Odd (Nat.card F))
    (h3 : ∀ a : Fˣ, a ^ 3 = 1 → a = 1) (T : Sylow 2 (GL (Fin 2) F)) {y : GL (Fin 2) F}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have hF' := isOddPrimePower189 hF
  let D : Sylow 2 (PGL(2, F)) := T.mapSurjective ProjGenLinGroup.mk_surjective
  obtain ⟨m, -, ⟨eD⟩⟩ := CFSG.GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hF' D
  have hm := CFSG.GorensteinWalter.pgl2_dihedral_sylow_parameter_ge_two F hF' D eD
  have hyD : ProjGenLinGroup.mk y ∈
      Subgroup.normalizer ((D : Subgroup (PGL(2, F))) : Set (PGL(2, F))) :=
    Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ hy)
  let ψ := (D : Subgroup (PGL(2, F))).normalizerMonoidHom ⟨_, hyD⟩
  have hψ3 : ψ ^ 3 = 1 := by
    have h : (⟨_, hyD⟩ : Subgroup.normalizer ((D : Subgroup (PGL(2, F))) : Set (PGL(2, F)))) ^ 3 =
        1 := Subtype.ext (by simp only [Subgroup.coe_pow, ← map_pow, hy3, map_one]; rfl)
    rw [← map_pow, h, map_one]
  have hψ : ψ = 1 := mulAut_eq_one_of_dihedral189 hm eD ψ hψ3
  have hcomm : ∀ t ∈ (T : Subgroup (GL (Fin 2) F)), t * y = y * t := by
    intro t ht
    have hd : ProjGenLinGroup.mk t ∈ (D : Subgroup (PGL(2, F))) := Subgroup.mem_map_of_mem _ ht
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hψ ⟨_, hd⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
    have h2 : ProjGenLinGroup.mk t = ProjGenLinGroup.mk (y * t * y⁻¹) := by
      simpa only [map_mul, map_inv] using h1.symm
    obtain ⟨c, hc, htc⟩ := ProjGenLinGroup.mk_eq_mk_iff'.1 h2
    have hc3 : c ^ 3 = 1 := by
      have h3' := conj_pow_eq_mul_pow189 (fun g => Subgroup.mem_center_iff.1 hc g) htc.symm 3
      rw [hy3, one_mul, inv_one, mul_one] at h3'
      exact mul_eq_left.1 h3'.symm
    rw [eq_one_of_mem_center_of_pow_three189 h3 hc hc3, mul_one] at htc
    conv_lhs => rw [htc]
    exact inv_mul_cancel_right (y * t) y
  by_contra hy1
  have hyc : y ∉ Subgroup.center (GL (Fin 2) F) := fun h =>
    hy1 (eq_one_of_mem_center_of_pow_three189 h3 h hy3)
  exact false_of_commute_sylow_gl2_189 hF T fun a ha b hb =>
    commute_of_not_mem_center189 hyc (hcomm a ha) (hcomm b hb)

end CFSG.RankThree.PartTwo.Sec18

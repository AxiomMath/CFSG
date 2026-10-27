module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.InvolGenAut
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix CFSG.QuasithinUnique.Setup.Family CFSG.LieType.SteinbergBR.AutGL32

local notation "M3" => Matrix (Fin 3) (Fin 3) (ZMod 2)

namespace InvolGenGL32

@[expose] def c6 : Fin 6 → M3 :=
  ![!![0, 1, 1; 0, 1, 0; 1, 1, 0], !![1, 0, 0; 1, 0, 1; 1, 1, 0], !![1, 0, 0; 1, 1, 0; 1, 0, 1],
    !![1, 1, 1; 0, 0, 1; 0, 1, 0], !![1, 0, 1; 0, 1, 1; 0, 0, 1], !![1, 0, 1; 0, 1, 0; 0, 0, 1]]

theorem c6_sq : ∀ i, c6 i * c6 i = 1 := by decide

@[expose] def u6 (i : Fin 6) : GL32 := ⟨c6 i, c6 i, c6_sq i, c6_sq i⟩

@[expose] def encM (S : M3) : ℕ :=
  (S 0 0).val + 2 * (S 0 1).val + 4 * (S 0 2).val + 8 * (S 1 0).val + 16 * (S 1 1).val +
    32 * (S 1 2).val + 64 * (S 2 0).val + 128 * (S 2 1).val + 256 * (S 2 2).val

@[expose] def tabIn : List (ℕ × Fin 6 × Fin 6 × Fin 6) :=
  [(84, 1, 2, 3), (124, 0, 1, 2), (266, 0, 2, 3), (458, 4, 0, 2), (214, 2, 3, 5), (302, 2, 3, 5),
    (161, 0, 4, 5), (401, 0, 1, 2), (337, 1, 0, 4), (465, 2, 0, 1), (305, 2, 0, 1), (233, 3, 4, 5),
    (281, 1, 0, 4), (345, 0, 4, 5), (313, 0, 1, 2), (277, 3, 0, 1), (309, 0, 2, 3), (275, 0, 1, 2),
    (403, 1, 2, 3), (167, 1, 0, 4), (279, 1, 0, 4)]

@[expose] def tabOut : List (ℕ × Fin 6 × Fin 6 × Fin 6) :=
  [(84, 0, 0, 1), (340, 0, 0, 2), (244, 2, 0, 0), (500, 1, 0, 2), (266, 2, 0, 0), (426, 0, 0, 1),
    (282, 1, 0, 2), (442, 0, 0, 2), (334, 1, 0, 1), (494, 0, 0, 1), (94, 1, 0, 1), (254, 0, 0, 1),
    (161, 1, 0, 1), (417, 0, 0, 2), (273, 0, 0, 1), (177, 1, 0, 2), (229, 5, 0, 0), (485, 0, 0, 3),
    (85, 0, 0, 3), (501, 3, 0, 0), (267, 0, 0, 3), (171, 0, 0, 1), (187, 0, 0, 3), (443, 0, 0, 1),
    (335, 0, 0, 2), (239, 0, 0, 1), (95, 1, 0, 2), (351, 1, 0, 1)]

@[expose] def lookIn (S : M3) : Fin 6 × Fin 6 × Fin 6 := (tabIn.lookup (encM S)).getD (0, 0, 0)

@[expose] def lookOut (S : M3) : Fin 6 × Fin 6 × Fin 6 := (tabOut.lookup (encM S)).getD (0, 0, 0)

@[expose] def kIn (S Z : M3) : M3 := Z * S * Z * S

@[expose] def kOut (S S' Z : M3) : M3 := Z * S * Zᵀ * S'

@[expose] def aIn (S : M3) : M3 := kIn S (c6 (lookIn S).1)

@[expose] def bIn (S : M3) : M3 :=
  kIn S (c6 (lookIn S).1) * kIn S (c6 (lookIn S).2.1) * kIn S (c6 (lookIn S).2.2)

@[expose] def aOut (S S' : M3) : M3 := kOut S S' (c6 (lookOut S).1)

@[expose] def bOut (S S' : M3) : M3 :=
  kOut S S' (c6 (lookOut S).1) * kOut S S' (c6 (lookOut S).2.1) * kOut S S' (c6 (lookOut S).2.2)

@[expose] def symM (a b c d e f : ZMod 2) : M3 := !![a, b, c; b, d, e; c, e, f]

theorem inner_check : ∀ S : M3, S * S = 1 → S ≠ 1 →
    aIn S ^ 4 = 1 ∧ aIn S ≠ 1 ∧ bIn S ^ 7 = 1 ∧ bIn S ≠ 1 := by
  decide +kernel

theorem outer_check : ∀ a b c d e f a' b' c' d' e' f' : ZMod 2,
    symM a b c d e f * symM a' b' c' d' e' f' = 1 →
      aOut (symM a b c d e f) (symM a' b' c' d' e' f') ^ 4 = 1 ∧
      aOut (symM a b c d e f) (symM a' b' c' d' e' f') ≠ 1 ∧
      bOut (symM a b c d e f) (symM a' b' c' d' e' f') ^ 7 = 1 ∧
      bOut (symM a b c d e f) (symM a' b' c' d' e' f') ≠ 1 := by
  decide +kernel

theorem eq_symM {S : M3} (h : Sᵀ = S) :
    S = symM (S 0 0) (S 0 1) (S 0 2) (S 1 1) (S 1 2) (S 2 2) := by
  have h' : ∀ i j, S j i = S i j := fun i j => congrFun (congrFun h i) j
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symM, h' 0 1, h' 0 2, h' 1 2]

theorem outer_ok {S S' : M3} (hS : Sᵀ = S) (hS' : S'ᵀ = S') (h : S * S' = 1) :
    aOut S S' ^ 4 = 1 ∧ aOut S S' ≠ 1 ∧ bOut S S' ^ 7 = 1 ∧ bOut S S' ≠ 1 := by
  rw [eq_symM hS, eq_symM hS'] at h ⊢
  exact outer_check _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem two_dvd_orderOf_of_pow_four {M : Type*} [Monoid M] {x : M} (h4 : x ^ 4 = 1)
    (h1 : x ≠ 1) : 2 ∣ orderOf x := by
  have hd : orderOf x ∣ 2 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one h4
  obtain ⟨m, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rcases m with _ | m
  · exact absurd (orderOf_eq_one_iff.1 (by rw [he, pow_zero])) h1
  · rw [he, pow_succ]
    exact dvd_mul_left 2 _

theorem eq_top_of_mat {H : Subgroup GL32} {a b : GL32} (ha : a ∈ H) (hb : b ∈ H)
    (ha4 : (a : M3) ^ 4 = 1) (ha1 : (a : M3) ≠ 1) (hb7 : (b : M3) ^ 7 = 1) (hb1 : (b : M3) ≠ 1) :
    H = ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have ha4' : a ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ha4, Units.val_one])
  have hb7' : b ^ 7 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hb7, Units.val_one])
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, Units.val_one])
  have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, Units.val_one])
  refine CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32
    ((two_dvd_orderOf_of_pow_four ha4' ha1').trans (Subgroup.orderOf_dvd_natCard H ha)) ?_
  have := Subgroup.orderOf_dvd_natCard H hb
  rwa [orderOf_eq_prime hb7' hb1'] at this

theorem coe_k_inner {s : GL32} (hs : s * s = 1) (i : Fin 6) :
    ((u6 i * (MulAut.conj s (u6 i))⁻¹ : GL32) : M3) = kIn s (c6 i) := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hui : (u6 i)⁻¹ = u6 i := inv_eq_of_mul_eq_one_right (Units.ext (c6_sq i))
  rw [MulAut.conj_apply,
    show u6 i * (s * u6 i * s⁻¹)⁻¹ = u6 i * s * (u6 i)⁻¹ * s⁻¹ by group, hsi, hui]
  rfl

theorem coe_k_outer (s y : GL32) :
    ((y * ((MulAut.conj s * tau) y)⁻¹ : GL32) : M3) = kOut s ↑s⁻¹ y := by
  have h1 : ((tau y)⁻¹ : GL32) = tau y⁻¹ := (map_inv tau y).symm
  have h2 : ((tau y⁻¹ : GL32) : M3) = (y : M3)ᵀ := by rw [tau_val, inv_inv]
  rw [MulAut.mul_apply, MulAut.conj_apply,
    show y * (s * tau y * s⁻¹)⁻¹ = y * s * (tau y)⁻¹ * s⁻¹ by group, h1]
  simp only [Units.val_mul, h2, kOut]

theorem conj_mul_tau_sq (s : GL32) :
    (MulAut.conj s * tau) * (MulAut.conj s * tau) = MulAut.conj (s * tau s) := by
  rw [mul_assoc, ← mul_assoc tau, tau_mul_conj, mul_assoc, tau_mul_tau, mul_one, map_mul]

theorem transpose_of_outer {s : GL32} (h : (MulAut.conj s * tau) * (MulAut.conj s * tau) = 1) :
    (s : M3)ᵀ = s ∧ ((s⁻¹ : GL32) : M3)ᵀ = ↑s⁻¹ := by
  have hst : s * tau s = 1 := conj_injective ((conj_mul_tau_sq s).symm.trans (h.trans (map_one _).symm))
  have hS' : ((s⁻¹ : GL32) : M3)ᵀ = ↑s⁻¹ := by rw [← tau_val, eq_inv_of_mul_eq_one_right hst]
  have h1 : (s : M3)ᵀ * ((s⁻¹ : GL32) : M3) = 1 := by
    rw [← hS', ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  refine ⟨?_, hS'⟩
  calc (s : M3)ᵀ = (s : M3)ᵀ * (((s⁻¹ : GL32) : M3) * (s : M3)) := by
        rw [Units.inv_mul, Matrix.mul_one]
    _ = s := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

end InvolGenGL32

open InvolGenGL32 in
theorem involGenAut_GL32 : InvolGenAut GL32 := by
  intro α hαα hα1
  rcases aut_GL32_cases α with ⟨s, rfl⟩ | ⟨s, hs⟩
  · have hss : s * s = 1 := conj_injective (by rw [map_mul, hαα, map_one])
    have hs1 : s ≠ 1 := fun h => hα1 (by rw [h, map_one])
    obtain ⟨h4, h4', h7, h7'⟩ := inner_check (s : M3) (by rw [← Units.val_mul, hss, Units.val_one])
      fun h => hs1 (Units.ext h)
    have e := coe_k_inner hss
    refine ⟨u6 (lookIn s).1, u6 (lookIn s).2.1, u6 (lookIn s).2.2, eq_top_of_mat
      (a := u6 (lookIn s).1 * (MulAut.conj s (u6 (lookIn s).1))⁻¹)
      (b := u6 (lookIn s).1 * (MulAut.conj s (u6 (lookIn s).1))⁻¹ *
        (u6 (lookIn s).2.1 * (MulAut.conj s (u6 (lookIn s).2.1))⁻¹) *
        (u6 (lookIn s).2.2 * (MulAut.conj s (u6 (lookIn s).2.2))⁻¹))
      (Subgroup.subset_closure (by simp)) (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))) ?_ ?_ ?_ ?_⟩
    · rw [e]; exact h4
    · rw [e]; exact h4'
    · rw [Units.val_mul, Units.val_mul, e, e, e]; exact h7
    · rw [Units.val_mul, Units.val_mul, e, e, e]; exact h7'
  · replace hs : α = MulAut.conj s * tau := hs
    subst hs
    obtain ⟨hS, hS'⟩ := transpose_of_outer hαα
    obtain ⟨h4, h4', h7, h7'⟩ := outer_ok hS hS' (Units.mul_inv s)
    have e := coe_k_outer s
    refine ⟨u6 (lookOut s).1, u6 (lookOut s).2.1, u6 (lookOut s).2.2, eq_top_of_mat
      (a := u6 (lookOut s).1 * ((MulAut.conj s * tau) (u6 (lookOut s).1))⁻¹)
      (b := u6 (lookOut s).1 * ((MulAut.conj s * tau) (u6 (lookOut s).1))⁻¹ *
        (u6 (lookOut s).2.1 * ((MulAut.conj s * tau) (u6 (lookOut s).2.1))⁻¹) *
        (u6 (lookOut s).2.2 * ((MulAut.conj s * tau) (u6 (lookOut s).2.2))⁻¹))
      (Subgroup.subset_closure (by simp)) (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))) ?_ ?_ ?_ ?_⟩
    · rw [e]; exact h4
    · rw [e]; exact h4'
    · rw [Units.val_mul, Units.val_mul, e, e, e]; exact h7
    · rw [Units.val_mul, Units.val_mul, e, e, e]; exact h7'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

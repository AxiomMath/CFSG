module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.ExactNormalFormE
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Fixed
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6Sound
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

theorem false_of_cube_of_fix_wRho_E6 {K : Type} [Field K] {z : Fin Tag.E6.rank → Kˣ}
    (hz : ∀ i, z i ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hθ : ∀ β, w • permLattice (exactPerm .E6 1) (w • permLattice (exactPerm .E6 1) β) = β)
    (hzθ : ∀ β, rootChar z (w • permLattice (exactPerm .E6 1) β) = rootChar z β)
    (hfix : ∀ β ∈ famKernel {z}, w • permLattice (exactPerm .E6 1) β = β) : False := by
  have hfive (v : Fin 5 → Fin Tag.E6.rank → ℤ) (hv : ∀ k, v k ∈ famKernel {z})
      (hli : LinearIndependent ℤ v) : False := by
    have h4 := fixed_span_finrank_le_four_E6 (ε := 1) rfl hθ (K := ℚ) (R := Set.range v)
      (by rintro _ ⟨k, rfl⟩; exact hfix _ (hv k))
    rw [← Set.range_comp] at h4
    have hliQ : LinearIndependent ℚ ((fun (r : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) =>
        ((r i : ℤ) : ℚ)) ∘ v) := by
      rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
      exact hli.map' ((Int.castAddHom ℚ).toIntLinearMap.compLeft _)
        (LinearMap.ker_eq_bot.2 fun x y h => funext fun i => Int.cast_injective (congrFun h i))
    have h5 := (finrank_span_eq_card hliQ).symm.trans_le h4
    simp at h5
  by_cases h1 : ∀ i, z i = 1
  · refine hfive (fun k => Pi.single (Fin.castSucc k) 1) (fun k => ?_)
      ((Pi.linearIndependent_single_one (Fin 6) ℤ).comp _ (Fin.castSucc_injective 5))
    simp only [famKernel, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
    exact ⟨.basis _, by simp [rootChar, h1]⟩
  obtain ⟨i₀, hi₀⟩ := not_forall.1 h1
  have hω3 := hz i₀
  have hord := orderOf_eq_prime hω3 hi₀
  generalize hω : z i₀ = ω at hω3 hord hi₀
  have hK3 (x : Kˣ) (hx : x ^ 3 = 1) : (x : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hsum : (1 : K) + ω + ω ^ 2 = 0 := by
    have h : ((ω : K) - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hK3 ω hω3
    exact (mul_eq_zero.1 h).resolve_left fun h' => hi₀ (Units.val_eq_one.1 (sub_eq_zero.1 h'))
  have hcases (j) : z j = 1 ∨ z j = ω ∨ z j = ω ^ 2 := by
    have h : ((z j : K) - 1) * ((z j : K) - ω) * ((z j : K) - ((ω ^ 2 : Kˣ) : K)) = 0 := by
      rw [Units.val_pow_eq_pow_val]
      linear_combination hK3 _ (hz j) - (z j : K) ^ 2 * hsum + (ω : K) * z j * hsum - hK3 ω hω3
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact .inl (Units.val_eq_one.1 (sub_eq_zero.1 h))
      · exact .inr (.inl (Units.ext (sub_eq_zero.1 h)))
    · exact .inr (.inr (Units.ext (sub_eq_zero.1 h)))
  have hω2 : ω ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have hω21 : ω ^ 2 ≠ ω := fun h => by
    rw [sq] at h
    exact hi₀ (mul_left_cancel (h.trans (mul_one ω).symm))
  classical
  obtain ⟨e, he, he₀⟩ : ∃ e : Fin Tag.E6.rank → ℤ, (∀ j, z j = ω ^ e j) ∧ e i₀ = 1 := by
    refine ⟨fun j => if z j = 1 then 0 else if z j = ω then 1 else 2, fun j => ?_, by
      simp [hω, hi₀]⟩
    rcases hcases j with h | h | h <;> simp [h, hi₀, hω2, hω21]
  have hchar (β : Fin Tag.E6.rank → ℤ) : rootChar z β = ω ^ ∑ i, β i * e i := by
    have he6 (j : Fin 6) : z j = ω ^ e j := he j
    change ∏ i : Fin 6, z i ^ β i = ω ^ ∑ i : Fin 6, β i * e i
    simp only [Fin.prod_univ_six, Fin.sum_univ_six, he6, ← zpow_mul', zpow_add]
  have hmem {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (h3 : (3 : ℤ) ∣ ∑ i, e i * β i) :
      β ∈ famKernel {z} := by
    simp only [famKernel, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
    refine ⟨hβ, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hord,
      Finset.sum_congr rfl fun i _ => mul_comm (β i) (e i)]
    exact_mod_cast h3
  rcases exists_roots_of_not_dvd_three_E6 e ⟨i₀, by rw [he₀]; decide⟩ with
    ⟨v, hv, hv3, hli⟩ | ⟨r, hr, hr3, horth⟩
  · exact hfive v (fun k => hmem (hv k) (hv3 k)) hli
  have hz3 (j : Fin 4) : ∑ i, ((r j i : ℤ) : ZMod 3) * ((e i : ℤ) : ZMod 3) = 0 := by
    rw [← (ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i, e i * r j i) 3).2 (by exact_mod_cast hr3 j)]
    push_cast
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.E6.rank → ℤ, s = Pi.single i₀ 1 := ⟨_, rfl⟩
  have hA : ∑ i, (((w • permLattice (exactPerm .E6 1) s) i : ℤ) : ZMod 3) * ((e i : ℤ) : ZMod 3) =
      -∑ i, ((s i : ℤ) : ZMod 3) * ((e i : ℤ) : ZMod 3) :=
    sum_theta_mul_eq_neg_E6 (ε := 1) rfl hθ hr horth (fun j => hfix _ (hmem (hr j) (hr3 j)))
      (fun i => ((e i : ℤ) : ZMod 3)) hz3 s
  have h := hzθ s
  rw [hchar, hchar, zpow_eq_zpow_iff_modEq, hord, ← ZMod.intCast_eq_intCast_iff] at h
  push_cast at h
  have hS : ∑ i, ((s i : ℤ) : ZMod 3) * ((e i : ℤ) : ZMod 3) = 1 := by
    simp [hs, Pi.single_apply, he₀]
  have hc := h.symm.trans hA
  rw [hS] at hc
  exact absurd hc (by decide)

end KGCentE6

end CFSG.StandardType

end

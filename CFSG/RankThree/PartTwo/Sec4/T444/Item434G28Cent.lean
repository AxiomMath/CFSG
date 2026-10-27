module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G28Sylow
public import Certificates.Certificate9548

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434G28

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten CFSG.Quasithin.B42G2Id
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Open CFSG.Quasithin.Explicit CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.Timmesfeld.RankTwo

@[expose] def sw6 (l : Fin 6) : Fin 6 := ⟨(l.val + 3) % 6, Nat.mod_lt _ (by norm_num)⟩

theorem ix6_sw6 : ∀ l : Fin 6, (ix6 l).swap = ix6 (sw6 l) := by decide

theorem decode_jCode_apply (l k : Fin 6) :
    decode jCode l k = if k = sw6 l then (1 : GF8) else 0 := by
  fin_cases l <;> fin_cases k <;> decide

section Cent


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem cmat_symp (τ : K ≃+* GF8) (h : ↥(cayleyGroup K)) :
    (cmat τ h).transpose * decode jCode * cmat τ h = decode jCode := by
  have hq : ∀ a b : Ix3, ∑ c : Ix3, repQ h c a * repQ h c.swap b = formQ K a b := by
    intro a b
    have := congrFun (congrFun (repQ_transpose_formQ h) a) b
    rw [Matrix.mul_assoc, formQ_mul, Matrix.mul_apply] at this
    simpa [Matrix.transpose_apply, Matrix.submatrix_apply] using this
  ext i j
  have key : ∑ l : Fin 6, cmat τ h l i * cmat τ h (sw6 l) j = decode jCode i j := by
    have h1 := congrArg τ (hq (ix6 i) (ix6 j))
    rw [map_sum] at h1
    simp only [map_mul] at h1
    rw [← ixEquiv.sum_comp] at h1
    simp only [ixEquiv_apply, ix6_sw6] at h1
    have h2 : τ (formQ K (ix6 i) (ix6 j)) = decode jCode i j := by
      rw [decode_jCode_apply, formQ_apply, ix6_sw6]
      by_cases hj : j = sw6 i
      · rw [ite_eq_left (by rw [hj]), ite_eq_left hj, map_one]
      · rw [ite_eq_right (fun h => hj (ix6_bijective.1 h)), ite_eq_right hj, map_zero]
    rw [h2] at h1
    simpa [cmat] using h1
  rw [← key]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, decode_jCode_apply]
  simp only [Finset.sum_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

namespace G28Model

theorem rho_symp (g : ↥(adjointGroup .G2 K)) :
    (M.rho g).transpose * decode jCode * M.rho g = decode jCode := by
  rw [rho_apply]
  exact cmat_symp M.τ (M.ψ g)

theorem pow_nine_of_centralizes_E0 (x : ↥(adjointGroup .G2 K)) (hx : ∀ e ∈ M.E0, x * e = e * x) :
    x ^ 9 = 1 := by
  have h : centOK e0L centV0 centB centBinv = true := Certificates.certificate9548
  have hP : ∀ k < 6, M.rho x * decode e0L[k]! = decode e0L[k]! * M.rho x := by
    intro k hk
    rw [← M.rho_e0Elt (by omega : k < 9), ← map_mul, ← map_mul, hx _ M.e0Elt_mem]
  apply M.rho_injective
  rw [map_pow, map_one]
  exact pow_nine_of_commutes h hP (M.rho_symp x)

include M in
theorem pow_nine_of_centralizes (hK : Nat.card K = 8) {E : Subgroup ↥(adjointGroup .G2 K)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (x : ↥(adjointGroup .G2 K)) (hx : ∀ e ∈ E, x * e = e * x) : x ^ 9 = 1 := by
  have : Finite ↥(adjointGroup .G2 K) := Subtype.finite
  obtain ⟨h, hh⟩ := M.exists_conj_E0 hK hE hE9
  have hinj : Function.Injective (fun e : E => (⟨h * e * h⁻¹, hh e e.2⟩ : M.E0)) := by
    intro a b hab
    have h1 : h * (a : ↥(adjointGroup .G2 K)) * h⁻¹ = h * (b : ↥(adjointGroup .G2 K)) * h⁻¹ :=
      congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hcard : Nat.card M.E0 = Nat.card E := by rw [(M.isElemAbelian_E0_card).2, hE9]
  have hbij := Function.Injective.bijective_of_nat_card_le hinj hcard.le
  have hs : ∀ e' ∈ M.E0, ∃ e ∈ E, h * e * h⁻¹ = e' := fun e' he' => by
    obtain ⟨⟨e, he⟩, hfe⟩ := hbij.2 ⟨e', he'⟩
    exact ⟨e, he, congrArg Subtype.val hfe⟩
  have hx' : ∀ e' ∈ M.E0, (h * x * h⁻¹) * e' = e' * (h * x * h⁻¹) := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := hs e' he'
    calc (h * x * h⁻¹) * (h * e * h⁻¹) = h * (x * e) * h⁻¹ := by group
      _ = h * (e * x) * h⁻¹ := by rw [hx e he]
      _ = (h * e * h⁻¹) * (h * x * h⁻¹) := by group
  have h9 := M.pow_nine_of_centralizes_E0 _ hx'
  rw [conj_pow] at h9
  simpa using h9

end G28Model

end Cent

end CFSG.RankThree.PartTwo.Sec4.Item434G28

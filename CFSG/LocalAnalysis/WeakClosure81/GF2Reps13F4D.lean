module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Hyperplanes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations (hyperplanes)
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem s134b_exists_seven_frame {K : Subgroup (MulAut W)} (hL3 : UC22.IsL3 ↥K 1) :
    ∃ x ∈ K, ∃ u ∈ K, orderOf x = 7 ∧ u * x * u⁻¹ = x ^ 2 := by
  obtain ⟨eSL⟩ := CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two hL3
  let eGL : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  let e : ↥K ≃* GL (Fin 3) (ZMod 2) := eSL.trans eGL
  let M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0,0,1; 1,0,1; 0,1,0]
  let Fm : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1,0,0; 0,0,1; 0,1,1]
  have hM7 : M ^ 7 = 1 := by decide +kernel
  have hM6 : M * M ^ 6 = 1 := by decide +kernel
  have hM6' : M ^ 6 * M = 1 := by decide +kernel
  have hMne : M ≠ 1 := by decide +kernel
  have hF2 : Fm * Fm ^ 2 = 1 := by decide +kernel
  have hF2' : Fm ^ 2 * Fm = 1 := by decide +kernel
  have hFM : Fm * M = M ^ 2 * Fm := by decide +kernel
  let x₀ : GL (Fin 3) (ZMod 2) := Units.mk M (M ^ 6) hM6 hM6'
  let u₀ : GL (Fin 3) (ZMod 2) := Units.mk Fm (Fm ^ 2) hF2 hF2'
  have hx₀pow : x₀ ^ 7 = 1 := by
    apply Units.ext
    simpa [x₀] using hM7
  have hx₀ne : x₀ ≠ 1 := by
    intro h1
    apply hMne
    have := congrArg (fun z : GL (Fin 3) (ZMod 2) =>
      (z : Matrix (Fin 3) (Fin 3) (ZMod 2))) h1
    simpa [x₀] using this
  have hx₀ord : orderOf x₀ = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx₀pow hx₀ne
  have hux₀ : u₀ * x₀ * u₀⁻¹ = x₀ ^ 2 := by
    apply Units.ext
    simp only [x₀, u₀, Units.val_mul, Units.val_pow_eq_pow_val, Units.inv_mk]
    rw [hFM, mul_assoc, hF2, mul_one]
  refine ⟨((e.symm x₀ : ↥K) : MulAut W), (e.symm x₀).2,
    ((e.symm u₀ : ↥K) : MulAut W), (e.symm u₀).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq e.symm x₀]
    exact hx₀ord
  · have hconj : (e.symm u₀ : ↥K) * (e.symm x₀ : ↥K) * (e.symm u₀ : ↥K)⁻¹ =
        (e.symm x₀ : ↥K) ^ 2 := by
      simpa using congrArg e.symm hux₀
    simpa using congrArg (fun z : ↥K => (z : MulAut W)) hconj

omit [Finite W] in
theorem s134b_map_conj_hyperplane {x x' u : MulAut W} (hux : u * x * u⁻¹ = x ^ 2)
    (hux' : u * x' * u⁻¹ = x') (i : ℕ) :
    (Subgroup.zpowers (x' * x ^ i)).map (MulAut.conj u).toMonoidHom =
      Subgroup.zpowers (x' * x ^ (2 * i)) := by
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers ((MulAut.conj u) (x' * x ^ i)) =
    Subgroup.zpowers (x' * x ^ (2 * i))
  rw [MulAut.conj_apply]
  congr 1
  have h1 : u * (x' * x ^ i) * u⁻¹ = (u * x' * u⁻¹) * (u * x * u⁻¹) ^ i := by
    rw [conj_pow]
    group
  rw [h1, hux', hux, ← pow_mul]

theorem s134b_mem_normalizer_sup {x x' u : MulAut W} (hux : u * x * u⁻¹ = x ^ 2)
    (hux' : u * x' * u⁻¹ = x') :
    u ∈ normalizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers x' : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (Subgroup.zpowers x ⊔ Subgroup.zpowers x').map (MulAut.conj u).toMonoidHom ≤
      Subgroup.zpowers x ⊔ Subgroup.zpowers x' := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change Subgroup.zpowers ((MulAut.conj u) x) ⊔ Subgroup.zpowers ((MulAut.conj u) x') ≤
      Subgroup.zpowers x ⊔ Subgroup.zpowers x'
    rw [MulAut.conj_apply, MulAut.conj_apply, hux, hux']
    exact sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨2, rfl⟩)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers x')))
  have hcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers x' : Subgroup (MulAut W)) ≤
      Nat.card (((Subgroup.zpowers x ⊔ Subgroup.zpowers x' : Subgroup (MulAut W))).map
        (MulAut.conj u).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

omit [Finite W] in
theorem s134b_zpowers_mul_inv {x x' : MulAut W} (hx : orderOf x = 7) (hcomm : x * x' = x' * x) :
    Subgroup.zpowers (x * x'⁻¹) = Subgroup.zpowers (x' * x ^ 6) := by
  have _hcomm : x * x' = x' * x := hcomm
  have h7 : x ^ 7 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hx6 : x ^ 6 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', show (6 : ℕ) + 1 = 7 by norm_num, h7]
  rw [← Subgroup.zpowers_inv (g := x * x'⁻¹), mul_inv_rev, inv_inv, hx6]

theorem s134b_rk_hypPart_double {x x' u : MulAut W} (hux : u * x * u⁻¹ = x ^ 2)
    (hux' : u * x' * u⁻¹ = x') (i : ℕ) :
    rk ↥(hypPart (Subgroup.zpowers x ⊔ Subgroup.zpowers x') (Subgroup.zpowers (x' * x ^ (2 * i)))) =
      rk ↥(hypPart (Subgroup.zpowers x ⊔ Subgroup.zpowers x')
        (Subgroup.zpowers (x' * x ^ i))) := by
  have hnorm := s134b_mem_normalizer_sup hux hux'
  have h := rk_hypPart_map_conj (E := Subgroup.zpowers x ⊔ Subgroup.zpowers x')
    (D := Subgroup.zpowers (x' * x ^ i)) (n := u) hnorm
  rw [s134b_map_conj_hyperplane hux hux' i] at h
  exact h

end CFSG.LocalAnalysis.WeakClosure81

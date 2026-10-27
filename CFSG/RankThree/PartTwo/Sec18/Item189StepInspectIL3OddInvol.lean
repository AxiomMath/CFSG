module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3OddGL2

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix
open scoped MatrixGroups

theorem exists_sylow_of_le189 {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] {C : Subgroup G} (Φ : H ≃* C) (S : Sylow p G) (hS : (S : Subgroup G) ≤ C) :
    ∃ T : Sylow p H, ∀ t : H, t ∈ (T : Subgroup H) ↔ ((Φ t : C) : G) ∈ (S : Subgroup G) := by
  refine ⟨(S.subtype hS).mapSurjective (f := Φ.symm.toMonoidHom) Φ.symm.surjective, fun t => ?_⟩
  change t ∈ ((S : Subgroup G).subgroupOf C).map Φ.symm.toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf]

variable {F : Type} [Field F] [Finite F]

theorem exists_central_involution_sl3_189 (hF : Odd (Nat.card F)) (S : Sylow 2 SL(3, F)) :
    ∃ z ∈ (S : Subgroup SL(3, F)), (∀ s ∈ (S : Subgroup SL(3, F)), s * z = z * s) ∧
      orderOf z = 2 := by
  have h2 : (2 : F) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero F hF
  let d : SL(3, F) := ⟨diagonal ![-1, -1, 1], by simp [det_diagonal, Fin.prod_univ_three]⟩
  have hd2 : d ^ 2 = 1 := by
    apply Subtype.ext
    show diagonal ![(-1 : F), -1, 1] ^ 2 = 1
    rw [sq, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  have hd1 : d ≠ 1 := by
    intro h
    have h00 : (-1 : F) = 1 := by
      simpa [d] using congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    exact h2 (by linear_combination -h00)
  have hcard : 2 ∣ Nat.card SL(3, F) := orderOf_eq_prime hd2 hd1 ▸ orderOf_dvd_natCard d
  have : Nontrivial (S : Subgroup SL(3, F)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (S.ne_bot_of_dvd_card hcard)
  have hZ := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcardZ⟩ := (S.isPGroup'.to_subgroup (Subgroup.center _)).nontrivial_iff_card.1 hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (S : Subgroup SL(3, F)))
    2 (by rw [hcardZ]; exact dvd_pow_self 2 hn.ne')
  refine ⟨((z : (S : Subgroup SL(3, F))) : SL(3, F)), (z : (S : Subgroup SL(3, F))).2,
    fun s hs => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨s, hs⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem nonempty_centralizer_equiv_gl2_189 (hF : Odd (Nat.card F)) (z : SL(3, F))
    (hz : orderOf z = 2) :
    Nonempty (GL (Fin 2) F ≃* Subgroup.centralizer ({z} : Set SL(3, F))) :=
  ⟨(CFSG.Wreathed.OddLinearTwoAutomorphisms.matrixEquiv F _ (Module.finBasisOfFinrankEq F _
    (CFSG.Wreathed.OddLinearThreeCentralizerCore.matrixAction_finrank F hF z hz).1)).trans
    (CFSG.Wreathed.OddLinearThreeCentralizerCore.matrixCentralizerEquiv F hF z hz)⟩

theorem eq_one_of_mem_normalizer_sl3_189 (hF : Odd (Nat.card F))
    (h3 : ∀ a : Fˣ, a ^ 3 = 1 → a = 1) (S : Sylow 2 SL(3, F)) {y : SL(3, F)}
    (hy : y ∈ Subgroup.normalizer ((S : Subgroup SL(3, F)) : Set SL(3, F))) (hy3 : y ^ 3 = 1) :
    y = 1 := by
  obtain ⟨z, hzS, hzc, hz⟩ := exists_central_involution_sl3_189 hF S
  obtain ⟨Φ⟩ := nonempty_centralizer_equiv_gl2_189 hF z hz
  set C := Subgroup.centralizer ({z} : Set SL(3, F)) with hCdef
  have hle : (S : Subgroup SL(3, F)) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hzc s hs)
  obtain ⟨T, hT⟩ := exists_sylow_of_le189 Φ S hle
  have hsq : ∀ (c : C) (g : GL (Fin 2) F), Φ g = c → (c : SL(3, F)) ^ 2 = 1 → g ^ 2 = 1 :=
    fun c g hg hc => Φ.injective (by
      rw [map_pow, hg, map_one]
      exact Subtype.ext (by simpa using hc))
  have hne : ∀ (c : C) (g : GL (Fin 2) F), Φ g = c → (c : SL(3, F)) ≠ 1 → g ≠ 1 :=
    fun c g hg hc h => hc (by rw [← hg, h, map_one]; rfl)
  have hcomm : ∀ (c : C) (g : GL (Fin 2) F), Φ g = c →
      (∀ s ∈ (S : Subgroup SL(3, F)), s * c = c * s) → ∀ t ∈ (T : Subgroup (GL (Fin 2) F)),
        t * g = g * t :=
    fun c g hg hc t ht => Φ.injective (by
      rw [map_mul, map_mul, hg]
      exact Subtype.ext (hc _ ((hT t).1 ht)))
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by decide)
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  obtain ⟨v, hv⟩ : ∃ v, Φ v = ⟨z, hzC⟩ := ⟨_, Φ.apply_symm_apply _⟩
  have hvc : v ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Φ.injective
    rw [map_mul, map_mul, hv]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Φ g).2)
  have hyz : y * z * y⁻¹ = z := by
    by_contra hne'
    have hz'S : y * z * y⁻¹ ∈ (S : Subgroup SL(3, F)) := (Subgroup.mem_normalizer_iff.1 hy z).1 hzS
    have hz'c : ∀ s ∈ (S : Subgroup SL(3, F)), s * (y * z * y⁻¹) = y * z * y⁻¹ * s := by
      intro s hs
      have hs' : y⁻¹ * s * y ∈ (S : Subgroup SL(3, F)) :=
        (Subgroup.mem_normalizer_iff.1 hy _).2 (by simpa [mul_assoc] using hs)
      have h := hzc _ hs'
      calc s * (y * z * y⁻¹) = y * (y⁻¹ * s * y * z) * y⁻¹ := by group
        _ = y * (z * (y⁻¹ * s * y)) * y⁻¹ := by rw [h]
        _ = y * z * y⁻¹ * s := by group
    have hz'C : y * z * y⁻¹ ∈ C :=
      Subgroup.mem_centralizer_singleton_iff.2 (hz'c z hzS).symm
    obtain ⟨w, hw⟩ : ∃ w, Φ w = ⟨y * z * y⁻¹, hz'C⟩ := ⟨_, Φ.apply_symm_apply _⟩
    by_cases hwc : w ∈ Subgroup.center (GL (Fin 2) F)
    · have hvw := eq_of_mem_center_of_sq189 hwc hvc
        (hsq _ w hw (by rw [conj_pow, hz2, mul_one, mul_inv_cancel]))
        (hsq _ v hv hz2) (hne _ w hw (fun h => hz1 (conj_eq_one_iff.1 h))) (hne _ v hv hz1)
      apply hne'
      have h := congrArg (fun g => (Φ g : SL(3, F))) hvw
      simpa only [hw, hv] using h
    · exact false_of_commute_sylow_gl2_189 hF T fun a ha b hb =>
        commute_of_not_mem_center189 hwc (hcomm _ w hw hz'c a ha) (hcomm _ w hw hz'c b hb)
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 (by
    calc y * z = y * z * y⁻¹ * y := by group
      _ = z * y := by rw [hyz])
  obtain ⟨u, hu⟩ : ∃ u, Φ u = ⟨y, hyC⟩ := ⟨_, Φ.apply_symm_apply _⟩
  have huN : u ∈ Subgroup.normalizer ((T : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hT, hT, map_mul, map_mul, map_inv, hu]
    exact Subgroup.mem_normalizer_iff.1 hy _
  have hu3 : u ^ 3 = 1 := Φ.injective (by
    rw [map_pow, hu, map_one]
    exact Subtype.ext hy3)
  have hu1 := eq_one_of_mem_normalizer_gl2_189 hF h3 T huN hu3
  have h := congrArg (fun g => (Φ g : SL(3, F))) hu1
  simpa only [hu, map_one, OneMemClass.coe_one] using h

end CFSG.RankThree.PartTwo.Sec18

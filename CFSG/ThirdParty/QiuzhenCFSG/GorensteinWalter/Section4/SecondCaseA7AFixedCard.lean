module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7IntersectionLeACentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ANormalH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Fixed points on the A7 order-nine subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A centralizing outside involution has exactly three fixed points on the
equation-(8) subgroup `A = K F`. -/
public theorem secondCase_a7_A_fixed_card_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M) (hyH : y ∈ c.H) :
    Nat.card (centralizerIn (od.K ⊔ od.F) y) = 3 := by
  classical
  let D : Subgroup G := w.M ⊓ conjugateSubgroup w.M y
  let A : Subgroup G := od.K ⊔ od.F
  let C : Subgroup G := centralizerIn A y
  let F' : Subgroup G := conjugateSubgroup od.F y
  have hAleD : A ≤ D := by
    exact le_sup_left.trans (by
      simpa [A, D] using
        secondCase_a7_A_sup_twoCore_le_inter_conjugate
          hmin c w d hA7 hmodel od hyH)
  have hDcentA : D ≤ Subgroup.centralizer (A : Set G) := by
    have h := secondCase_a7_inter_conjugate_le_A_centralizer
      hmin c w d hA7 hmodel od hy hyM hyH
    exact (by simpa [A, D] using h.trans inf_le_right)
  have hAcomm : ∀ {a b : G}, a ∈ A → b ∈ A → a * b = b * a := by
    intro a b haA hbA
    exact (Subgroup.mem_centralizer_iff.mp
      (hDcentA (hAleD haA)) b hbA).symm
  have hAcard : Nat.card A = 9 := by
    rw [show A = od.K ⊔ od.F by rfl, od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hAnormal : IsNormalIn A c.H := by
    simpa [A] using secondCase_a7_A_normal_H hmin c w d hA7 hmodel od
  have hF'card : Nat.card F' = 3 := by
    calc
      Nat.card F' = Nat.card od.F :=
        Subgroup.card_map_of_injective (MulAut.conj y).injective
      _ = 3 := od.F_card
  have hFne : od.F ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card od.F = 1 := by rw [hbot]; simp
    rw [od.F_card] at hcard
    omega
  obtain ⟨f, hfF, hfne⟩ := (Subgroup.nontrivial_iff_exists_ne_one od.F).mp
    ((Subgroup.nontrivial_iff_ne_bot od.F).mpr hFne)
  let fy : G := y * f * y⁻¹
  let z : G := f * fy
  have hfyF' : fy ∈ F' := by
    exact Subgroup.mem_map.mpr ⟨f, hfF, rfl⟩
  have hfA : f ∈ A := (le_sup_right : od.F ≤ A) hfF
  have hfyA : fy ∈ A := hAnormal.2 y hyH f hfA
  have hzA : z ∈ A := A.mul_mem hfA hfyA
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconjFy : y * fy * y⁻¹ = f := by
    dsimp [fy]
    rw [hyInv]
    calc
      y * (y * f * y) * y = (y * y) * f * (y * y) := by group
      _ = f := by rw [hy2]; simp
  have hzfix : y * z * y⁻¹ = z := by
    dsimp [z]
    calc
      y * (f * fy) * y⁻¹ =
          (y * f * y⁻¹) * (y * fy * y⁻¹) := by group
      _ = fy * f := by rw [hconjFy]
      _ = f * fy := hAcomm hfyA hfA
  have hzNe : z ≠ 1 := by
    intro hz1
    have hprod : f * fy = 1 := by simpa [z] using hz1
    have hfyEq : fy = f⁻¹ := by
      calc
        fy = 1 * fy := by simp
        _ = (f⁻¹ * f) * fy := by simp
        _ = f⁻¹ * (f * fy) := by group
        _ = f⁻¹ := by rw [hprod]; simp
    have hcommonF : f⁻¹ ∈ od.F := od.F.inv_mem hfF
    have hcommonF' : f⁻¹ ∈ F' := by rw [← hfyEq]; exact hfyF'
    have hFF' : od.F = F' :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        od.F F' od.F_card hF'card hcommonF hcommonF'
          (inv_ne_one.mpr hfne)
    have hyNF : y ∈ Subgroup.normalizer (od.F : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change F' = od.F
      exact hFF'.symm
    rw [od.F_normalizer] at hyNF
    exact hyM hyNF
  have hzC : z ∈ C := by
    refine ⟨hzA, ?_⟩
    have hmul := congrArg (fun q : G => q * y) hzfix
    have hcomm : y * z = z * y := by simpa [mul_assoc] using hmul
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hCleA : C ≤ A := inf_le_left
  have hCdiv : Nat.card C ∣ 9 := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hCleA
  have hCneOne : Nat.card C ≠ 1 := by
    intro hcard
    have hCbot : C = ⊥ := (Subgroup.eq_bot_iff_card (H := C)).mpr hcard
    have hzbot : z ∈ (⊥ : Subgroup G) := by rw [← hCbot]; exact hzC
    exact hzNe (Subgroup.mem_bot.mp hzbot)
  have hCneA : C ≠ A := by
    intro hCA
    have hyCentF : y ∈ Subgroup.centralizer (od.F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f' hf'
      have hf'C : f' ∈ C := by
        rw [hCA]
        exact (le_sup_right : od.F ≤ A) hf'
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp hf'C.2) y (by simp)
      exact hcomm.symm
    have hyNF : y ∈ Subgroup.normalizer (od.F : Set G) :=
      Subgroup.centralizer_le_normalizer (od.F : Set G) hyCentF
    rw [od.F_normalizer] at hyNF
    exact hyM hyNF
  have hCneNine : Nat.card C ≠ 9 := by
    intro hcard
    apply hCneA
    exact Subgroup.eq_of_le_of_card_ge hCleA (by rw [hcard, hAcard])
  obtain ⟨k, hk, hCcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card C ∣ 3 ^ 2 by
      norm_num
      exact hCdiv)
  interval_cases k
  · exact False.elim (hCneOne (by simpa only [pow_zero] using hCcard))
  · simpa only [pow_one] using hCcard
  · apply False.elim
    apply hCneNine
    norm_num only [pow_succ, pow_zero, mul_one] at hCcard ⊢
    exact hCcard

end CFSG.GorensteinWalter

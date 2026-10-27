module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7CosetEvenOrbit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AVFixedCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ACentralizerCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The sharp A7 even-coset involution bound -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A coset represented by a centralizing outside involution contains at
most eighteen involutions. -/
public theorem secondCase_a7_coset_involutions_card_le_18_of_mem_H
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
    Nat.card {x : G // IsInvolution x ∧
      x ∈ (w.M : Set G) * ({y} : Set G)} ≤ 18 := by
  classical
  let M : Subgroup G := w.M
  let D : Subgroup G := M ⊓ conjugateSubgroup M y
  let A : Subgroup G := od.K ⊔ od.F
  let V : Subgroup G := twoCoreOf c.Hhat
  let AV : Subgroup G := A ⊔ V
  let CM : Subgroup G := M ⊓ Subgroup.centralizer (A : Set G)
  let J := {x : G // IsInvolution x ∧
    x ∈ (M : Set G) * ({y} : Set G)}
  let rho : D →* MulAut G := MulAut.conj.comp D.subtype
  let : MulAction D G := MulAction.compHom G rho
  let O := MulAction.orbit D y
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D, M] using
      involution_mem_normalizer_inf_conjugateSubgroup w.M hy2
  have hyCoset : y ∈ (M : Set G) * ({y} : Set G) :=
    Set.mem_mul.mpr ⟨1, M.one_mem, y, by simp, by simp⟩
  have orbit_mem_J (x : O) : IsInvolution (x : G) ∧
      (x : G) ∈ (M : Set G) * ({y} : Set G) := by
    rcases MulAction.mem_orbit_iff.mp x.2 with ⟨g, hg⟩
    have hgEq : (g : G) * y * (g : G)⁻¹ = (x : G) := by
      change (g : G) * y * (g : G)⁻¹ = (x : G) at hg
      exact hg
    constructor
    · constructor
      · intro hx1
        apply hy.1
        calc
          y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [hgEq, hx1]; simp
      · calc
          (x : G) ^ 2 = ((g : G) * y * (g : G)⁻¹) ^ 2 := by rw [hgEq]
          _ = (g : G) * (y ^ 2) * (g : G)⁻¹ := by
            simp only [pow_two]
            group
          _ = 1 := by rw [hy.2]; simp
    · have hginvD : (g : G)⁻¹ ∈ D := D.inv_mem g.2
      have hyConjD : y * (g : G)⁻¹ * y⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp hyND (g : G)⁻¹).mp hginvD
      let m : G := (g : G) * (y * (g : G)⁻¹ * y⁻¹)
      have hmM : m ∈ M := M.mul_mem g.2.1 hyConjD.1
      refine Set.mem_mul.mpr ⟨m, hmM, y, by simp, ?_⟩
      rw [← hgEq]
      dsimp [m]
      group
  let eJO : J ≃ O :=
    { toFun := fun x =>
        ⟨x.1, by
          obtain ⟨g, hgD, hg⟩ :=
            secondCase_a7_involutions_in_coset_conjugate_by_intersection
              hmin c w d hA7 hmodel od hy hyM hyH hy x.2.1
                hyCoset x.2.2
          refine MulAction.mem_orbit_iff.mpr ⟨⟨g, hgD⟩, ?_⟩
          change g * y * g⁻¹ = x
          exact hg⟩
      invFun := fun x => ⟨x.1, orbit_mem_J x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  have hAVleD : AV ≤ D := by
    simpa [AV, A, V, D, M] using
      secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH
  let Fix : Subgroup G := centralizerIn AV y
  have hFixcard : Nat.card Fix = 6 := by
    simpa [Fix, AV, A, V] using
      secondCase_a7_A_sup_twoCore_fixed_card_eq_six
        hmin c w d hA7 hmodel od hy hyM hyH
  let stab := MulAction.stabilizer D y
  let f : Fix → stab := fun z =>
    ⟨⟨z.1, hAVleD z.2.1⟩, by
      change (z : G) * y * (z : G)⁻¹ = y
      have hcomm :=
        (Subgroup.mem_centralizer_iff.mp z.2.2) y (by simp)
      rw [← hcomm]
      group⟩
  have hf : Function.Injective f := by
    intro x z hxz
    apply Subtype.ext
    exact congrArg (fun q : stab => ((q.1 : D) : G)) hxz
  have hstabGe : 6 ≤ Nat.card stab := by
    rw [← hFixcard]
    exact Nat.card_le_card_of_injective f hf
  let : Fintype D := Fintype.ofFinite D
  let : Fintype O := Fintype.ofFinite O
  have horbitStab : Nat.card O * Nat.card stab = Nat.card D := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group D y
    simpa only [Nat.card_eq_fintype_card] using h
  have hDleCM : D ≤ CM := by
    simpa [D, CM, M, A] using
      secondCase_a7_inter_conjugate_le_A_centralizer
        hmin c w d hA7 hmodel od hy hyM hyH
  have hDcardLeCM : Nat.card D ≤ Nat.card CM :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hDleCM)
  have hCMcardLe : Nat.card CM ≤ 108 := by
    simpa [CM, M, A] using
      secondCase_a7_A_centralizer_card_le_108 hmin c w d hA7 hmodel od
  have hmulLe : Nat.card O * 6 ≤ Nat.card D := by
    calc
      Nat.card O * 6 ≤ Nat.card O * Nat.card stab :=
        Nat.mul_le_mul_left (Nat.card O) hstabGe
      _ = Nat.card D := horbitStab
  have hOcardLe : Nat.card O ≤ 18 := by omega
  calc
    Nat.card {x : G // IsInvolution x ∧
        x ∈ (w.M : Set G) * ({y} : Set G)} = Nat.card J := by rfl
    _ = Nat.card O := Nat.card_congr eJO
    _ ≤ 18 := hOcardLe

end CFSG.GorensteinWalter

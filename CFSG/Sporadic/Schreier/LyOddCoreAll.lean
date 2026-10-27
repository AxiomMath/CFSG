module

public import CFSG.Sporadic.Schreier.LyOddCoreOuter

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SymmetricLocal (oddCore_eq_pPrimeCore_two
  pPrimeCore_eq_bot_of_mulEquiv)

@[expose] def fixedConjEquiv {X : Type*} [Group X] (F : Subgroup X) [F.Normal] (t : X) :
    fixedSubgroup (MulAut.conjNormal t : MulAut F) ≃*
      ↥(F ⊓ Subgroup.centralizer ({t} : Set X)) where
  toFun x := ⟨((x : F) : X), (x : F).2, by
    have h := congrArg Subtype.val (x.2 : (MulAut.conjNormal t : MulAut F) (x : F) = (x : F))
    change t * ((x : F) : X) * t⁻¹ = ((x : F) : X) at h
    show ((x : F) : X) ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((x : F) : X) * t = t * ((x : F) : X) * t⁻¹ * t := by rw [h]
      _ = t * ((x : F) : X) := by group⟩
  invFun y := ⟨⟨y, y.2.1⟩, by
    show (MulAut.conjNormal t : MulAut F) ⟨y, y.2.1⟩ = ⟨y, y.2.1⟩
    apply Subtype.ext
    change t * (y : X) * t⁻¹ = y
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2.2
    rw [← h]
    group⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {X : Type*} [Group X] [Finite X]

theorem full_group_all_involution_odd_core (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Ly)) :
    (CFSG.generalizedFitting X).index ∣ 2 ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨hidx, hinner⟩ := full_group_inner_involution_odd_core hF hnab hJ
  refine ⟨hidx, fun t ht => ?_⟩
  by_cases htF : t ∈ CFSG.generalizedFitting X
  · exact hinner t htF ht
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
    CFSG.Sporadic.SmallOddCore.centralizer_generalizedFitting_eq_bot hF hnab
  set α : MulAut (CFSG.generalizedFitting X) := MulAut.conjNormal t with hαdef
  have hα : α ^ 2 = 1 := by
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [hαdef, ← map_pow, ht2, map_one]
  have hout : α ∉ (MulAut.conj : CFSG.generalizedFitting X →* MulAut _).range := by
    rintro ⟨s, hs⟩
    apply htF
    have hcen : (s : X)⁻¹ * t ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun β : MulAut (CFSG.generalizedFitting X) =>
        ((β ⟨y, hy⟩ : CFSG.generalizedFitting X) : X)) hs
      have h2 : (s : X) * y * (s : X)⁻¹ = t * y * t⁻¹ := h1
      calc y * ((s : X)⁻¹ * t) = (s : X)⁻¹ * ((s : X) * y * (s : X)⁻¹) * t := by group
        _ = (s : X)⁻¹ * (t * y * t⁻¹) * t := by rw [h2]
        _ = (s : X)⁻¹ * t * y := by group
    rw [hC, Subgroup.mem_bot] at hcen
    have hts : t = s := by
      calc t = (s : X) * ((s : X)⁻¹ * t) := by group
        _ = s := by rw [hcen, mul_one]
    rw [hts]
    exact s.2
  have hcore := outer_involution_fixed_odd_core hJ α hα hout
  rw [oddCore_eq_pPrimeCore_two] at hcore
  have hFC : CFSG.pPrimeCore 2
      ↥(CFSG.generalizedFitting X ⊓ Subgroup.centralizer ({t} : Set X)) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv 2 (fixedConjEquiv (CFSG.generalizedFitting X) t).symm hcore
  have key := (CFSG.LocalAnalysis.ComponentInitial.normal_prime_power_index_prime_complement_core
    2 (isPGroup_quotient_of_index_dvd_two hidx)).2 t
  rw [hFC, Subgroup.map_bot,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at key
  rw [oddCore_eq_pPrimeCore_two]
  exact key

end CFSG.Sporadic.LySchreier

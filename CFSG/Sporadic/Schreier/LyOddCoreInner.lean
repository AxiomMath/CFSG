module

public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.LocalAnalysis.ComponentInitial.OddCoreCorrespondence
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalOuterFixedOddCore
public import CFSG.Sporadic.SmallOddCore.Assembly

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SymmetricLocal (oddCore_eq_pPrimeCore_two
  pPrimeCore_eq_bot_of_mulEquiv)

theorem odd_card_oddCore_ly (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_eq_bot_of_quasisimple_center_two {H : Type*} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) (hZ : Nat.card (Subgroup.center H) = 2)
    (heven : 2 ∣ Nat.card H) : CFSG.oddCore H = ⊥ := by
  have hodd := odd_card_oddCore_ly H
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (inferInstance : (CFSG.oddCore H).Normal) with h | h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 heven)
  · have hdvd : Nat.card (CFSG.oddCore H) ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le h
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)

@[expose] def infCentralizerEquiv {X : Type*} [Group X] (F : Subgroup X) (s : F) :
    ↥(F ⊓ Subgroup.centralizer ({(s : X)} : Set X)) ≃* Subgroup.centralizer ({s} : Set F) where
  toFun x := ⟨⟨x, x.2.1⟩, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2.2)⟩
  invFun y := ⟨((y : F) : X), Subgroup.mem_inf.2 ⟨(y : F).2,
    Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem isPGroup_quotient_of_index_dvd_two {X : Type*} [Group X] {F : Subgroup X} [F.Normal]
    (h : F.index ∣ 2) :
    IsPGroup 2 (X ⧸ F) := by
  have hcard : Nat.card (X ⧸ F) = F.index := rfl
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [hcard, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [hcard, h2, pow_one])

variable {X : Type*} [Group X] [Finite X]

theorem index_generalizedFitting_dvd_two (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Ly)) :
    (CFSG.generalizedFitting X).index ∣ 2 := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hC : Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
    CFSG.Sporadic.SmallOddCore.centralizer_generalizedFitting_eq_bot hF hnab
  have hker : ((QuotientGroup.mk' (inner (CFSG.generalizedFitting X))).comp
      (MulAut.conjNormal : X →* MulAut (CFSG.generalizedFitting X))).ker =
      CFSG.generalizedFitting X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hin : MulAut.conjNormal x ∈ inner (CFSG.generalizedFitting X) :=
        (QuotientGroup.eq_one_iff _).1 hx
      obtain ⟨s, hs⟩ := hin
      have hcen : (s : X)⁻¹ * x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h1 := congrArg (fun α : MulAut (CFSG.generalizedFitting X) =>
          ((α ⟨y, hy⟩ : CFSG.generalizedFitting X) : X)) hs
        have h2 : (s : X) * y * (s : X)⁻¹ = x * y * x⁻¹ := h1
        calc y * ((s : X)⁻¹ * x) = (s : X)⁻¹ * ((s : X) * y * (s : X)⁻¹) * x := by group
          _ = (s : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
          _ = (s : X)⁻¹ * x * y := by group
      rw [hC, Subgroup.mem_bot] at hcen
      have hxs : x = s := by
        calc x = (s : X) * ((s : X)⁻¹ * x) := by group
          _ = s := by rw [hcen, mul_one]
      rw [hxs]
      exact s.2
    · intro hx
      show QuotientGroup.mk' (inner (CFSG.generalizedFitting X)) (MulAut.conjNormal x) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine ⟨⟨x, hx⟩, ?_⟩
      ext y
      rfl
  obtain ⟨θ⟩ := hJ
  rw [← hker, Subgroup.index_ker]
  exact (Subgroup.card_subgroup_dvd_card _).trans (outer_order_divides_two ⟨θ⟩).1

theorem full_group_inner_involution_odd_core (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.Ly)) :
    (CFSG.generalizedFitting X).index ∣ 2 ∧
      ∀ t ∈ CFSG.generalizedFitting X, orderOf t = 2 →
        CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have hidx := index_generalizedFitting_dvd_two hF hnab hJ
  refine ⟨hidx, fun t ht ht2 => ?_⟩
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := isPGroup_quotient_of_index_dvd_two hidx
  let s : CFSG.generalizedFitting X := ⟨t, ht⟩
  have hs2 : orderOf s = 2 := by rw [← Subgroup.orderOf_coe]; exact ht2
  obtain ⟨hq, hZ, -⟩ := involution_centralizers_quasisimple hJ s hs2
  have heven : 2 ∣ Nat.card (Subgroup.centralizer ({s} : Set (CFSG.generalizedFitting X))) := by
    have hmem : s ∈ Subgroup.centralizer ({s} : Set (CFSG.generalizedFitting X)) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    rw [← hs2, ← Subgroup.orderOf_mk s hmem]
    exact orderOf_dvd_natCard _
  have hcore := oddCore_eq_bot_of_quasisimple_center_two hq hZ heven
  rw [oddCore_eq_pPrimeCore_two] at hcore
  have hFC : CFSG.pPrimeCore 2
      ↥(CFSG.generalizedFitting X ⊓ Subgroup.centralizer ({t} : Set X)) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv 2 (infCentralizerEquiv (CFSG.generalizedFitting X) s) hcore
  have key := (CFSG.LocalAnalysis.ComponentInitial.normal_prime_power_index_prime_complement_core
    2 hp).2 t
  rw [hFC, Subgroup.map_bot,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at key
  rw [oddCore_eq_pPrimeCore_two]
  exact key

end CFSG.Sporadic.LySchreier

module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningComponent
public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalEndpointStatements
public import CFSG.RankThree.PartOne.KC.SymplecticFourInnerDefining
public import CFSG.RankThree.PartOne.KC.DefiningPrimeParameterRestriction
public import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.RankThreeEven (localRank)

namespace KCSymplecticDefining

theorem planeLocalCoreInner_statedProj_statedSp {p f : ℕ} {K : Type} [Field K] (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    PlaneLocalCoreInner p (StatedProj (StatedSp 2 K)) (fun _ => True) := by
  have : Fact p.Prime := ⟨hp⟩
  intro B hB A hAInn hA hAcard _ t htA ht1
  have := hA
  have hθ : ∀ a ∈ A, a ≠ 1 →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    intro a haA ha1
    have hap : orderOf a = p :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
    exact (KCSymplecticInner.symplectic_four_inner_defining_centralizer_local_cores_trivial hp
      hp3 hf hK B hB (hAInn haA) hap).2
  have h1 := hθ t htA ht1
  have h2 : autThetaT p B A = ⊥ := by
    apply le_bot_iff.mp
    calc autThetaT p B A ≤ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (StatedProj (StatedSp 2 K))))) :=
        (iInf_le _ t).trans ((iInf_le _ htA).trans (iInf_le _ ht1))
      _ = ⊥ := h1
  rw [autPlaneProduct, h1, h2, Subgroup.commutator_bot_left, bot_sup_eq]

theorem not_dvd_outer_statedProj_statedSp {p : ℕ} {K : Type} [Field K] (hp : p.Prime)
    (hp3 : 3 < p) (hK : Nat.card K = p ^ 1) :
    ¬ p ∣ Nat.card (Outer (StatedProj (StatedSp 2 K))) := by
  intro hd
  have h := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
    hp (by omega) le_rfl le_rfl hK).2
  rw [one_mul, pow_one] at h
  have h1 := Nat.le_of_dvd (by omega) (hd.trans h)
  omega

end KCSymplecticDefining

theorem symplectic_defining_prime_actual_component_local_core_product_centralizes :
    SymplecticDefiningPrimeActualComponentLocalCoreProductCentralizes := by
  intro X _ _ p hp hp3 N _ hN hX E hE hEcard t htE ht1 L hL n f hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hn2, hf1⟩ :=
    symplectic_defining_prime_actual_component_parameter_restriction hp hp3 N hN hX L hmod
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨φ⟩⟩ := hmod
  subst hn2 hf1
  have hplane := PlaneLocalCoreInner.of_mulEquiv hp φ
    (KCSymplecticDefining.planeLocalCoreInner_statedProj_statedSp hp hp3 hf hK)
  have hout := KCSymplecticDefining.not_dvd_outer_statedProj_statedSp hp hp3 hK
  have hinnAll : ∀ x : MulAut (L ⧸ center L), x ^ p = 1 →
      x ∈ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := by
    intro x hx
    have h1 := KCUnitaryDefining.mem_inner_of_pow_eq_one hp hout
      (x := MulAut.congr φ x) (by rw [← map_pow, hx, map_one])
    have h2 : MulAut.congr φ x ∈
        ((MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range).map
          (MulAut.congr φ).toMonoidHom := by
      rw [map_conj_range_mulAutCongr φ]
      exact h1
    have h3 := Subgroup.mem_map_equiv.mp h2
    rwa [MulEquiv.symm_apply_apply] at h3
  have hinner := KCUnitaryDefining.actualPlane_le_inner (L := L) hE hinnAll
  obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1
    hL hEL hSL hplane (Or.inr ⟨trivial, hinner⟩)
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

end CFSG.RankThree.PartOne

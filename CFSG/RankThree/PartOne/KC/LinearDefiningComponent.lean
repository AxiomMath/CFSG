module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningComponent
public import CFSG.RankThree.PartOne.KC.LinearThreeFourInnerDefining
public import CFSG.RankThree.PartOne.KC.DefiningPrimeParameterRestriction
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.Assembly.RankThreeEven (localRank)

namespace KCLinearDefining

theorem planeLocalCoreInner_projectiveSL {p f n : ℕ} {k : Type} [Field k] [Finite k] [CharP k p]
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hn : n = 3 ∨ n = 4) (hk : Nat.card k = p ^ f) :
    PlaneLocalCoreInner p (projectiveSL n k) (fun _ => True) := by
  have : Fact p.Prime := ⟨hp⟩
  intro B hB A hAInn hA hAcard _ t htA ht1
  have := hA
  have hθ : ∀ a ∈ A, a ≠ 1 →
      inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
    intro a haA ha1
    have hap : orderOf a = p :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
    exact (linear_three_four_inner_defining_centralizer_local_cores_trivial hp hp3 hf hn hk B hB
      (hAInn haA) hap).2
  have h1 := hθ t htA ht1
  have h2 : autThetaT p B A = ⊥ := by
    apply le_bot_iff.mp
    calc autThetaT p B A ≤ inSubgroup (aschbacherSolvableCore p)
          (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (projectiveSL n k)))) :=
        (iInf_le _ t).trans ((iInf_le _ htA).trans (iInf_le _ ht1))
      _ = ⊥ := h1
  rw [autPlaneProduct, h1, h2, Subgroup.commutator_bot_left, bot_sup_eq]

theorem not_dvd_outer_projectiveSL {p f n : ℕ} {k : Type} [Field k] (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) (hn : n = 3 ∨ n = 4) (hf3 : f ≤ 3) (hk : Nat.card k = p ^ f) :
    ¬ p ∣ Nat.card (Outer (projectiveSL n k)) := by
  intro hd
  have h0 := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
    (K := k) (n := n) hp hf (by omega) hk
  have h1 := hd.trans h0
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) h3
      omega
    · have := Nat.le_of_dvd (by omega : 0 < f) h3
      omega
  · have h4 : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)
    have h5 : p ∣ p ^ f - 1 + 1 := by rw [h4]; exact dvd_pow_self p (by omega)
    have : p ∣ 1 := (Nat.dvd_add_right h2).mp h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end KCLinearDefining

theorem linear_defining_prime_actual_component_local_core_product_centralizes_of
    (h3 : LinearTwoNormalizedComponentLocalCoreProductOddImage) :
    LinearDefiningPrimeActualComponentLocalCoreProductCentralizes := by
  intro X _ _ p hp hp3 N _ hN hX E hE hEcard t htE ht1 L hL n f hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  have hpar := linear_defining_prime_actual_component_parameter_restriction hp hp3 N hN hX L hmod
  obtain ⟨-, hf, -, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    exists_projectiveSL_of_statedClassicalModel_PSL hmod
  have hp5 : 5 ≤ p := by
    by_contra h
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hpf : 4 ≤ p ^ f := by
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  rcases hpar with rfl | h34
  ·
    obtain ⟨hres, hW, -⟩ := h3 (X ⧸ N) p hp hp3 E hE hEcard t htE ht1 L hL p f K hp hf hKcard hpf
      ⟨e⟩ hEL hSL
    have hWC := hW rfl
    refine ⟨hres.1.1, hres.1.2.1, ?_, ?_, hWC⟩
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_sup_left.trans hWC)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_sup_right.trans hWC)
  ·
    have hn : n = 3 ∨ n = 4 := by omega
    have hf3 : f ≤ 3 := by omega
    have : Fact p.Prime := ⟨hp⟩
    have := Fintype.ofFinite K
    have : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hKcard])
    have hplane := PlaneLocalCoreInner.of_mulEquiv hp e
      (KCLinearDefining.planeLocalCoreInner_projectiveSL hp hp3 hf hn hKcard)
    have hout := KCLinearDefining.not_dvd_outer_projectiveSL hp hp3 hf hn hf3 hKcard
    have hinnAll : ∀ x : MulAut (L ⧸ center L), x ^ p = 1 →
        x ∈ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range := by
      intro x hx
      have h1 := KCUnitaryDefining.mem_inner_of_pow_eq_one hp hout
        (x := MulAut.congr e x) (by rw [← map_pow, hx, map_one])
      have h2 : MulAut.congr e x ∈
          ((MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range).map
            (MulAut.congr e).toMonoidHom := by
        rw [map_conj_range_mulAutCongr e]
        exact h1
      have h3 := Subgroup.mem_map_equiv.mp h2
      rwa [MulEquiv.symm_apply_apply] at h3
    have hinner := KCUnitaryDefining.actualPlane_le_inner (L := L) hE hinnAll
    obtain ⟨h1, h2, h3⟩ := component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE
      ht1 hL hEL hSL hplane (Or.inr ⟨trivial, hinner⟩)
    have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
    exact ⟨hset, h3.trans (Subgroup.centralizer_le_normalizer _), h1, h2, h3⟩

end CFSG.RankThree.PartOne

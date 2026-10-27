module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LThree
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2G2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

section Tools

variable {X : Type} [Group X] [Finite X]

theorem inSubgroup_perfectResidual_le_commutator' (C : Subgroup X) :
    inSubgroup perfectResidual C ≤ ⁅C, C⁆ := by
  have h1 : perfectResidual C ≤ derivedSeries C 1 := iInf_le _ 1
  rw [derivedSeries_one] at h1
  calc inSubgroup perfectResidual C = (perfectResidual C).map C.subtype := rfl
    _ ≤ (commutator C).map C.subtype := Subgroup.map_mono h1
    _ = ⁅C, C⁆ := by
        rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]

theorem resCent_top_eq_centralizer_of_isPerfect {z : X}
    (h : Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set X))) :
    resCent (⊤ : Subgroup X) z = Subgroup.centralizer ({z} : Set X) := by
  refine le_antisymm ((resCent_le ⊤ z).trans inf_le_right) ?_
  exact le_inSubgroup_perfectResidual_of_isPerfect (X := (⊤ : Subgroup X) ⊓
    Subgroup.centralizer ({z} : Set X)) (le_inf le_top le_rfl) h

theorem isThreeA_of_perfect_centralizer {z : X} {m : ℕ} (h3 : orderOf z = 3)
    (hperf : Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set X)))
    (hSL : Sec4.IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set X)) m) : IsThreeA z m := by
  have hres := resCent_top_eq_centralizer_of_isPerfect hperf
  refine ⟨h3, ?_, isSLThreePiAt_congr (MulEquiv.subgroupCongr hres.symm) hSL⟩
  rw [hres]
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

end Tools

section G2


variable {K : Type} [Field K] [Finite K]

instance finite_adjointGroup_g2 : Finite (adjointGroup .G2 K) :=
  haveI : Finite (ModGL .G2 K) := CFSG.LieType.Chevalley.finite_modGL
  Subtype.finite

theorem g2_centralizer_threeA (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) ∧
      Sec4.IsSLThreePiAt ↥(Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))
        (Nat.card K) := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  rcases three_dvd_card_sub_one_or_add_one hK3 with h31 | h31
  · obtain ⟨e⟩ := Sec4.E27.nonempty_centralizer_mulEquiv_SL3 h31 hzS hz3 hz1
    have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)).1
    refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
    exact ⟨K, inferInstance, inferInstance, Or.inl ⟨rfl, by omega,
      ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)⟩⟩⟩
  · haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
    haveI : Fact (ringChar K).Prime := ⟨hp⟩
    have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
    obtain ⟨L, _, _, _, -, hdeg, -⟩ := exists_quadratic_ext' K
    haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
    obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU hK h31 hdeg hzS hz3 hz1
    refine ⟨(KS11Lie7Proof.isQuasisimple_centralizer_threeA h31 hK4 hzS hz3 hz1).1, ?_⟩
    refine ⟨L, inferInstance, inferInstance, Or.inr ⟨natCard_quadratic hdeg, by omega, ⟨?_⟩⟩⟩
    rw [hK]
    exact e

theorem g2_resCent_threeB (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {t : adjointGroup .G2 K} (htM : t ∈ g2LongSL2 K) (ht3 : orderOf t = 3) :
    resCent (⊤ : Subgroup (adjointGroup .G2 K)) t = g2ShortSL2 K := by
  have h3 : t ^ 3 = 1 := by rw [← ht3]; exact pow_orderOf_eq_one t
  have h1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht3
    omega
  have := Sec8.Item83Proof.inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2
    hK3 hK4 htM h3 h1
  show inSubgroup perfectResidual ((⊤ : Subgroup (adjointGroup .G2 K)) ⊓ _) = _
  rw [top_inf_eq]
  exact this

theorem g2_threeLocalModel (r : TauCeti.PrimePower) (hK : Nat.card K = r.card)
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) :
    ThreeLocalModel (adjointGroup .G2 K) r r.card (g2ShortSL2 K) (g2LongSL2 K) := by
  obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  obtain ⟨eM⟩ := nonempty_mulEquiv_g2LongSL2 (K := K)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, isPerfect_g2LongSL2 hK4, fun a ha b hb => g2Short_commute_g2Long ha hb, ?_, ?_,
    ?_, ?_, ?_⟩
  · haveI : Fintype K := Fintype.ofFinite K
    exact ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK], ⟨eS.symm⟩⟩
  ·
    intro x hxS hxM hx3
    have hB3 : eS.symm ⟨x, hxS⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxS⟩ : g2ShortSL2 K) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hB : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
        A * eS.symm ⟨x, hxS⟩ = eS.symm ⟨x, hxS⟩ * A := by
      intro A
      apply eS.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subtype.ext (g2Short_commute_g2Long (eS A).2 hxM)
    have h1 := eq_one_of_central_of_pow_three hB3 hB
    have h2 : (⟨x, hxS⟩ : g2ShortSL2 K) = 1 := by
      rw [← MulEquiv.apply_symm_apply eS ⟨x, hxS⟩, h1, map_one]
    exact congrArg Subtype.val h2
  ·
    obtain ⟨h3, h1⟩ := sl2Three_pow_three K
    refine ⟨((eM (sl2Three K) : g2LongSL2 K) : adjointGroup .G2 K), (eM _).2, ?_⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← Subgroup.coe_pow, ← map_pow, h3, map_one, Subgroup.coe_one]
    · intro h
      apply h1
      apply eM.injective
      rw [map_one]
      exact Subtype.ext h
  · intro g hg
    have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg
      omega
    exact KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 g hg3 hg1
  · intro z hzS hz
    have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hz
      omega
    obtain ⟨hperf, hSL⟩ := g2_centralizer_threeA hK3 hK4 hzS hz3 hz1
    rw [hK] at hSL
    exact isThreeA_of_perfect_centralizer hz hperf hSL
  · intro t htM ht
    exact g2_resCent_threeB hK3 hK4 htM ht

end G2

end Hering129L

end CFSG.RankThree.PartTwo.Sec12

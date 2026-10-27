module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2Aux
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Plain

variable {G : Type*} [Group G]

theorem map_centralizer_conj (m z : G) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.centralizer ({m * z * m⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc m * c * m⁻¹ * (m * z * m⁻¹) = m * (c * z) * m⁻¹ := by group
      _ = m * (z * c) * m⁻¹ := by rw [hc]
      _ = m * z * m⁻¹ * (m * c * m⁻¹) := by group
  · intro hy
    refine ⟨m⁻¹ * y * m, ?_, by group⟩
    calc m⁻¹ * y * m * z = m⁻¹ * (y * (m * z * m⁻¹)) * m := by group
      _ = m⁻¹ * ((m * z * m⁻¹) * y) * m := by rw [hy]
      _ = z * (m⁻¹ * y * m) := by group

noncomputable def centralizerConjEquiv (m z : G) :
    Subgroup.centralizer ({z} : Set G) ≃* Subgroup.centralizer ({m * z * m⁻¹} : Set G) :=
  ((Subgroup.centralizer ({z} : Set G)).equivMapOfInjective (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective).trans (MulEquiv.subgroupCongr (map_centralizer_conj m z))

end Plain

section G2


theorem conj_g2RootSL2_short_mem (K : Type) [Field K] (s : Matrix.SpecialLinearGroup (Fin 2) K) :
    g2WeylRep K * g2RootSL2 g2s K s * (g2WeylRep K)⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K := by
  have hh : ((g2RootSL2 g2s K s : adjointGroup Tag.G2 K) : ModGL Tag.G2 K) ∈
      Subgroup.closure (Set.range (xUnit Tag.G2 K g2s) ∪ Set.range (yUnit Tag.G2 K g2s)) := by
    rw [← range_simpleRootSL2]
    exact ⟨s, rfl⟩
  have key : ((g2WeylRep K * g2RootSL2 g2s K s * (g2WeylRep K)⁻¹ : adjointGroup Tag.G2 K) :
      ModGL Tag.G2 K) ∈ rootSubgroup Tag.G2 K g2δ ⊔ rootSubgroup Tag.G2 K (-g2δ) := by
    rw [← map_conj_canonicalRep_closure_xUnit_yUnit g2_w_smul]
    refine ⟨_, hh, ?_⟩
    simp [g2WeylRep, MulAut.conj_apply]
  exact key


section Split

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo

variable {K : Type} [Field K]

theorem nonempty_centralizer_mulEquiv_SL3 [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    Nonempty (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨A, hA⟩ := mem_g2ShortSL2_iff.mp hzS
  have hinj := rhoV_injective (K := K)
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hz3)
  obtain ⟨P, t, hPt⟩ := exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply HSLHom_injective (K := K)
      rw [map_pow, HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
    · rintro rfl
      apply hz1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (HSLHom K))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m : adjointGroup .G2 K := ⟨rhoV K P, by
    rw [rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ K _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ K _))⟩ with hm
  have hmz : ((m * z * m⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [coe_conj, ← hA, ← rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  have hKer := rootCharKernel_threeA (K := K) ht3
  have heq : Subgroup.centralizer ({m * z * m⁻¹} : Set (adjointGroup .G2 K)) = φ.range := by
    apply le_antisymm
    · intro x hx
      have hx' := (mem_centralizer_iff_toral hmz).mp hx
      obtain ⟨w, hw, hwx⟩ := Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2 φ hφ ht3 hx'
      have : w = x := Subtype.ext hwx
      rwa [← this]
    · refine range_le_of_a2y φ hφ _ fun γ hγ c => ?_
      rw [mem_centralizer_iff_toral hmz, mem_toralCentralizer]
      refine ⟨(a2y γ c).2, ?_⟩
      rw [coe_a2y hγ]
      have hmem : g2CommRoot (a2pos (γ 0, γ 1)) ∈ rootCharKernel (Pi.mulSingle g2ir t) := by
        rw [hKer]
        exact a2_long_roots hγ
      rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
  exact ⟨(centralizerConjEquiv m z).trans ((MulEquiv.subgroupCongr heq).trans
    (MonoidHom.ofInjective hφinj).symm)⟩

end Split


section Unitary

variable {K : Type} [Field K]

theorem card_centralizer_short_unitary [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨e⟩ := KS11Lie7Proof.nonempty_centralizer_mulEquiv_statedSU (p := 2) (f := n) hK h3 hdeg
    hzS hz3 hz1
  have hL : Nat.card L = (2 ^ n) ^ 2 := by rw [KS11Lie4Proof.natCard_quadratic hdeg, hK]
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hL

end Unitary

end G2

end CFSG.RankThree.PartTwo.Sec4.E27

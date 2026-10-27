module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusDefs
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5Lines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5Rank
import CFSG.GroupTheory.CardMapInfKer
import CFSG.GroupTheory.Frattini.PSubgroupLift
import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU
open CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.PartTwo.Sec21.U4Lines

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem card_torus6_su5 (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Nat.card (torus6 (unitaryInvolution K 2 2) 3) = 9 := by
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3 := by
    have hdvd' : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      norm_num
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd'
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  have hσ : ∀ u : rootsOfUnity 3 K,
      unitaryInvolution K 2 2 ((u : Kˣ) : K) = (u : Kˣ) := by
    intro u
    exact U4Lines.unitaryInvolution_rootsOfUnity even_two u
  have hT : ∀ v : D8Mod 3 K, (CFSG.RankThree.PartOne.KFU.diagU (d8Vec 5 v) :
      GL (Fin 5) K) ∈ SU (unitaryInvolution K 2 2) 5 := by
    intro v
    exact d8Vec_mem_SU (Or.inr rfl) d8Comb_five (unitaryInvolution K 2 2) hσ v
  have hP : ∀ τ : Equiv.Perm (Fin 5), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (CFSG.RankThree.PartOne.KFU.permGL τ : GL (Fin 5) K) ∈ SU (unitaryInvolution K 2 2) 5 := by
    intro τ hτ
    exact CFSG.RankThree.PartOne.KFU.permGL_mem_SU (unitaryInvolution K 2 2) τ hτ
  obtain ⟨SM⟩ := CFSG.RankThree.PartOne.KFU.exists_d8ctx d8Comb_five d8Comb2_five
    Nat.prime_three (by norm_num) hζ (SU (unitaryInvolution K 2 2) 5) hT hP
  have hcard := SM.card_F (by norm_num) hζ
  simpa [torus6, pow_two] using hcard

private theorem exists_cube_root_fixed (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ ζ : Kˣ, ζ ≠ 1 ∧ ζ ^ 3 = 1 ∧ unitaryInvolution K 2 2 (ζ : K) = ζ := by
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 :=
    U4Lines.card_rootsOfUnity_three even_two hK
  let : Fintype ↥(rootsOfUnity 3 K) := Fintype.ofFinite _
  have hlt : 1 < Fintype.card ↥(rootsOfUnity 3 K) := by
    rw [← Nat.card_eq_fintype_card, hμ]
    norm_num
  obtain ⟨ω, hω⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : rootsOfUnity 3 K)
  exact ⟨ω, fun h => hω (Subtype.ext (by simpa using congrArg (fun u : Kˣ => (u : K)) h)),
    (mem_rootsOfUnity 3 (ω : Kˣ)).mp ω.2, U4Lines.unitaryInvolution_rootsOfUnity even_two ω⟩

theorem u5_torusFacts (hK : Nat.card K = (2 ^ 2) ^ 2) :
    TorusFacts (StatedProj (StatedSU 5 (2 ^ 2) K)) ⊤
      ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2 := by
  obtain ⟨ζ, hζ_ne, hζ3, hζ_fix⟩ := exists_cube_root_fixed hK
  let x₃ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨diagU (dvec5 ζ ζ),
      CFSG.RankThree.PartOne.KFU.diagU_dvec5_mem_SU (unitaryInvolution K 2 2) hζ_fix hζ_fix⟩
  let x₄ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨diagU (dvec5 ζ ζ⁻¹),
      CFSG.RankThree.PartOne.KFU.diagU_dvec5_mem_SU (unitaryInvolution K 2 2)
        hζ_fix (by rw [Units.val_inv_eq_inv_val, map_inv₀, hζ_fix])⟩
  have hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ) := rfl
  have hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹) := rfl
  have hp5 : ∀ p : ℕ, p.Prime → p ∣ 2 ^ 2 + 1 → p = 5 := fun p hp hp_dvd =>
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (by simpa using hp_dvd)
  intro B₀ hB₀
  rcases (u5_notationB_torus_iff hK hζ_ne hζ3 hx₃ hx₄).mp hB₀ with hB₀_3 | hB₀_4
  · refine ⟨zpowers (suQ 5 hK x₄), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hB₀_3]
      exact (u5_line_le_kOf hK hζ_ne hζ3 hx₃ hx₄).1
    · exact (u5_notationB_torus_iff hK hζ_ne hζ3 hx₃ hx₄).mpr (Or.inr rfl)
    · rw [hB₀_3]
      exact u5_line_four_ne_three hK hζ_ne hζ3 hx₃ hx₄
    · intro Y hY
      rcases (u5_notationB_torus_iff hK hζ_ne hζ3 hx₃ hx₄).mp hY with hY3 | hY4
      · exact Or.inl (hY3.trans hB₀_3.symm)
      · exact Or.inr hY4
    · intro p hp hp_dvd
      obtain rfl := hp5 p hp hp_dvd
      refine ⟨u5_exists_centP hK hζ_ne hζ3 hx₃ hx₄ (Or.inl hB₀_3), ?_⟩
      rw [hB₀_3]
      exact u5_two_le_pRank hK hζ_ne hζ3 hx₃ hx₄
  · refine ⟨zpowers (suQ 5 hK x₃), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hB₀_4]
      exact (u5_line_le_kOf hK hζ_ne hζ3 hx₃ hx₄).2
    · exact (u5_notationB_torus_iff hK hζ_ne hζ3 hx₃ hx₄).mpr (Or.inl rfl)
    · rw [hB₀_4]
      exact (u5_line_four_ne_three hK hζ_ne hζ3 hx₃ hx₄).symm
    · intro Y hY
      rcases (u5_notationB_torus_iff hK hζ_ne hζ3 hx₃ hx₄).mp hY with hY3 | hY4
      · exact Or.inr hY3
      · exact Or.inl (hY4.trans hB₀_4.symm)
    · intro p hp hp_dvd
      obtain rfl := hp5 p hp hp_dvd
      refine ⟨u5_exists_centP hK hζ_ne hζ3 hx₃ hx₄ (Or.inr hB₀_4), ?_⟩
      rw [hB₀_4, sup_comm]
      exact u5_two_le_pRank hK hζ_ne hζ3 hx₃ hx₄

private theorem card_ker_suQ_five (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Nat.card (suQ 5 hK).ker = 5 := by
  have hker : (suQ 5 hK).ker =
      ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)).comap
        (CFSG.LieType.Universal.Unitary.equivStatedSU hK 5).toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  rw [hker, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective
      (CFSG.LieType.Universal.Unitary.equivStatedSU hK 5).symm.injective,
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num : 1 ≤ 5)).2.2]
  norm_num

private theorem exists_lift_card_nine (hK : Nat.card K = (2 ^ 2) ^ 2)
    {E : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))} (hE_card : Nat.card E = 9) :
    ∃ P : Subgroup ↥(SU (unitaryInvolution K 2 2) 5), Nat.card P = 9 ∧
      P ⊓ (suQ 5 hK).ker = ⊥ ∧ P.map (suQ 5 hK) = E := by
  have hq : IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  let E' : Subgroup ↥(SU (unitaryInvolution K 2 2) 5) := E.comap (suQ 5 hK)
  have hcard_E' : Nat.card E' = 45 := by
    change Nat.card (E.comap (suQ 5 hK)) = 45
    rw [CFSG.GroupTheory.card_comap_eq_card_ker_mul_card _ hq.surjective E, hE_card,
      card_ker_suQ_five hK]
  let P : Sylow 3 E' := default
  have hfac : (Nat.card E').factorization 3 = 2 := by
    rw [hcard_E', show (45 : ℕ) = 3 ^ 2 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    norm_num
  let P' : Subgroup ↥(SU (unitaryInvolution K 2 2) 5) := (P : Subgroup ↥E').map E'.subtype
  have hP'_card : Nat.card P' = 9 := by
    have h := Sylow.card_eq_multiplicity P
    rw [hfac] at h
    rw [Subgroup.card_map_of_injective E'.subtype_injective]
    simpa using h
  have hinf : P' ⊓ (suQ 5 hK).ker = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hP'_card, card_ker_suQ_five hK]
    decide
  refine ⟨P', hP'_card, hinf, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, -, rfl⟩ := hx
    exact Subgroup.mem_comap.mp y.2
  · rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot (suQ 5 hK) hinf, hP'_card, hE_card]

theorem u5_torusAt (hK : Nat.card K = (2 ^ 2) ^ 2) :
    TorusAt (StatedProj (StatedSU 5 (2 ^ 2) K)) ⊤ 2 := by
  intro E hE hE_ab hE_card
  obtain ⟨P', hP'_card, hP_inf_ker, hP'_map_eq⟩ := exists_lift_card_nine hK hE_card
  have hP_exp : ∀ x ∈ P', x ^ 3 = 1 := by
    intro x hxP
    have hxE : suQ 5 hK x ∈ E := by
      rw [← hP'_map_eq]
      exact Subgroup.mem_map_of_mem _ hxP
    have h3 : x ^ 3 ∈ P' ⊓ (suQ 5 hK).ker := by
      refine Subgroup.mem_inf.mpr ⟨P'.pow_mem hxP 3, MonoidHom.mem_ker.mpr ?_⟩
      rw [map_pow]
      exact hE_ab.2 _ hxE
    rw [hP_inf_ker] at h3
    exact Subgroup.mem_bot.mp h3
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KFU.exists_conj_into_d8Tor_su
    (n := 5) (Or.inr rfl) CFSG.RankThree.PartOne.KFU.d8Comb_five hK Nat.prime_three
    (by norm_num) (by norm_num) P' hP_exp
  have hP_conj_eq : P'.map (MulAut.conj g).toMonoidHom = torus6 (unitaryInvolution K 2 2) 3 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hg x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP'_card, card_torus6_su5 hK]
  have hfun : (MulAut.conj (suQ 5 hK g)).toMonoidHom.comp (suQ 5 hK) =
      (suQ 5 hK).comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  have hE_map : E.map (MulAut.conj (suQ 5 hK g)).toMonoidHom =
      (torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK) := by
    rw [← hP'_map_eq, ← hP_conj_eq, Subgroup.map_map, Subgroup.map_map, hfun]
  have hT : TorusFacts (StatedProj (StatedSU 5 (2 ^ 2) K)) ⊤
      (E.map (MulAut.conj (suQ 5 hK g)).toMonoidHom) 2 := by
    rw [hE_map]
    exact u5_torusFacts hK
  exact TorusFacts.of_conj (mem_top _) le_top hT

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

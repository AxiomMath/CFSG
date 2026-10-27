module

public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.GoldschmidtS146RPair
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SBd10

open CFSG.Goldschmidt CFSG.Goldschmidt.G3a CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank CFSG.Quasithin.A3Facts
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.OutStructure Matrix
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter sylowCenter_le)
open CFSG.Open (fusionIsBenderGroup)


open CFSG.Open CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank CFSG.Quasithin.A3Facts Matrix

theorem exists_two_five_u34 {X : Type} [Group X] (h : IsPSU 3 2 2 X) :
    ∃ x y : X, x ^ 5 = 1 ∧ y ^ 5 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ ∀ n : ℕ, x ^ n ≠ y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 5
    (by rw [Nat.card_units, hK]; norm_num)
  have hζ5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  set H : Subgroup (GL (Fin 3) K) := CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 2) K with hH
  have hdq (j k : Fin 3) : (torusVec ζ j k : Fin 3 → Kˣ) ^ (2 ^ 2 + 1) = 1 := by
    rw [show 2 ^ 2 + 1 = 5 by norm_num, torusVec_pow, hζ5, torusVec_one]
  have hxH : torusDiag (K := K) (torusVec ζ (0 : Fin 3) 2) ∈ H :=
    torusDiag_mem_SU (by norm_num) (prod_torusVec ζ _ _) (hdq _ _)
  have hyH : torusDiag (K := K) (torusVec ζ (1 : Fin 3) 2) ∈ H :=
    torusDiag_mem_SU (by norm_num) (prod_torusVec ζ _ _) (hdq _ _)
  let N := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf H
  let π : H →* CFSG.Assembly.LowTwoRank.StatedProj H := QuotientGroup.mk' N
  have hmem : ∀ u v : H, π u = π v → ((u : GL (Fin 3) K)⁻¹ * v) ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    fun u v h => by
      change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf] at h
      simpa using h
  have hone : ∀ u : H, π u = 1 ↔ (u : GL (Fin 3) K) ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := fun u => by
    change (u : H ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm (a b : Fin 3 → Kˣ) : Commute (torusDiag (K := K) a) (torusDiag b) :=
    (Commute.all a b).map torusDiag
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  set x₀ : H := ⟨_, hxH⟩ with hx₀
  set y₀ : H := ⟨_, hyH⟩ with hy₀
  have hx5 : x₀ ^ 5 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact torusVec_pow_order hζ _ _)
  have hy5 : y₀ ^ 5 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact torusVec_pow_order hζ _ _)
  have hxy : x₀ * y₀ = y₀ * x₀ := Subtype.ext (hcomm _ _).eq
  have hx1 : π x₀ ≠ 1 := by
    rw [Ne, hone]
    rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := torusDiag_hent hc 0
    have e1 := torusDiag_hent hc 1
    rw [torusVec_apply_left ζ h02] at e0
    rw [torusVec_apply_of_ne ζ h01.symm h12] at e1
    exact hζ1 (e0.symm.trans e1)
  have hy1 : ∀ n : ℕ, π x₀ ^ n ≠ π y₀ := by
    intro n hn
    rw [← map_pow] at hn
    have hm := hmem _ _ hn
    obtain ⟨c, hc⟩ := hm
    have hc' : ((x₀ ^ n : H) : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c =
        (y₀ : GL (Fin 3) K) := by
      rw [hc]
      exact mul_inv_cancel_left _ _
    rw [SubgroupClass.coe_pow] at hc'
    change torusDiag (K := K) (torusVec ζ (0 : Fin 3) 2) ^ n * GeneralLinearGroup.scalar (Fin 3) c =
      torusDiag (K := K) (torusVec ζ (1 : Fin 3) 2) at hc'
    rw [← map_pow, torusVec_pow, scalar_eq_torusDiag, ← map_mul] at hc'
    have e0 := torusDiag_hent hc' 0
    have e1 := torusDiag_hent hc' 1
    have e2 := torusDiag_hent hc' 2
    simp only [Pi.mul_apply, torusVec_apply_left _ h02, torusVec_apply_of_ne _ h01 h02,
      torusVec_apply_of_ne _ h01.symm h12, torusVec_apply_left _ h12,
      torusVec_apply_right _ h02, torusVec_apply_right _ h12, one_mul] at e0 e1 e2
    rw [e1] at e0 e2
    have hA : ζ ^ n = ζ⁻¹ := eq_inv_of_mul_eq_one_left e0
    rw [hA, inv_inv] at e2
    have h3 : ζ ^ 3 = 1 := by
      calc ζ ^ 3 = (ζ * ζ) * ζ := by rw [pow_succ, pow_two]
        _ = 1 := by rw [e2]; exact inv_mul_cancel ζ
    have := orderOf_dvd_of_pow_eq_one h3
    rw [hζ] at this
    omega
  refine ⟨e.symm (π x₀), e.symm (π y₀), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_pow, hx5, map_one, map_one]
  · rw [← map_pow, ← map_pow, hy5, map_one, map_one]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hxy]
  · intro h1
    exact hx1 (e.symm.injective (by rw [h1, map_one]))
  · intro n hn
    exact hy1 n (e.symm.injective (by rw [map_pow, hn]))



open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G3a CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter sylowCenter_le)
open CFSG.Open (fusionIsBenderGroup)

theorem borel_data_u34 {G : Type} [Group G] [Finite G]
    {L Q : Subgroup G} (hU : IsPSU 3 2 2 ↥L) (hQ : IsSylowTwoOf Q L) :
    (∃ z ∈ L, z ∈ Subgroup.normalizer (Q : Set G) ∧ orderOf z = 5) ∧
      Nat.card ↥(sylowCenter Q) = 4 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBender : fusionIsBenderGroup ↥L :=
    K1.fusionIsBenderGroup_of_stated_psu_three (by norm_num) hU
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hU
  have hcard : Nat.card K = 2 ^ (2 * 2) := by rw [hK, ← pow_mul]
  let e0' : ↥L ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ 2)) := e0
  let e : ↥L ≃* PSU3 2 2 :=
    e0'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative 2 (by norm_num) hcard)
  let T : Sylow 2 ↥L := GoldS146R.sylowOfIsSylowTwoOf hQ
  have hT : (T : Subgroup ↥L) = Q.subgroupOf L := GoldS146R.coe_sylowOfIsSylowTwoOf hQ
  obtain ⟨D, hD⟩ := exists_borelSetup hBender T
  obtain ⟨hZ, -, hDc⟩ := hD.orders_psu3 (by norm_num) e
  have hD15 : Nat.card ↥D = 15 := by rw [hDc]; norm_num
  have hQL : Q ≤ L := hQ.1
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 5 (by rw [hD15]; norm_num)
    refine ⟨((d : ↥L) : G), (d : ↥L).2, ?_, ?_⟩
    · have hdN : (d : ↥L) ∈ Subgroup.normalizer ((Q.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
        rw [← hT]
        exact hD.le d.2
      exact CFSG.ComponentClassification.AschbacherToolkit.BenderExt.Bridge.mem_normalizer_subgroupOf
        hQL _ hdN
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hd
  · have hmap : (sylowCenter (Q.subgroupOf L)).map L.subtype = sylowCenter Q := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (CFSG.ComponentClassification.AschbacherToolkit.BenderExt.Bridge.mem_sylowCenter_subgroupOf
          hQL x).mp hx
      · intro hg
        have hgL : g ∈ L := hQL (sylowCenter_le Q hg)
        refine ⟨⟨g, hgL⟩, ?_, rfl⟩
        exact (CFSG.ComponentClassification.AschbacherToolkit.BenderExt.Bridge.mem_sylowCenter_subgroupOf
          hQL ⟨g, hgL⟩).mpr hg
    rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective, ← hT, hZ]
    norm_num



open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.OutStructure CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem aut_pow_five_inner_u34 {X : Type} [Group X] (h : IsPSU 3 2 2 X)
    {α : MulAut X} (hα : α ^ 5 = 1) : α ∈ Inn X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 2 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 2 ^ 2 = 2) := by norm_num
  obtain ⟨⟨eT⟩, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU (isPrimeFormGram_one (n := 3)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  obtain ⟨-, -, -, -, -, hr⟩ := unitary_full_diagonal_outer_order hU hn3 hq
  have h5 : IsPGroup 5 (Subgroup.zpowers (MulAut.congr e' α)) := by
    have hord : (MulAut.congr e' α) ^ 5 = 1 := by rw [← map_pow, hα, map_one]
    have hdvd : orderOf (MulAut.congr e' α) ∣ 5 := orderOf_dvd_of_pow_eq_one hord
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
    · have : (MulAut.congr e' α) = 1 := orderOf_eq_one_iff.mp h1
      rw [this, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_card (n := 0) (by simp)
    · have hc : Nat.card (Subgroup.zpowers (MulAut.congr e' α)) = 5 ^ 1 := by
        rw [Nat.card_zpowers, h1, pow_one]
      exact IsPGroup.of_card hc
  have hmem := hr rfl 5 (by norm_num) (by norm_num) (by norm_num) _ h5 (Subgroup.mem_zpowers _)
  have hinner : (Inn X).map (MulAut.congr e').toMonoidHom =
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e'
  rw [← hinner] at hmem
  obtain ⟨β, hβ, hβα⟩ := hmem
  have : β = α := (MulAut.congr e').injective hβα
  exact this ▸ hβ

theorem normalizer_pow_five_u34 {G : Type} [Group G] (L : Subgroup G) [Group.IsPerfect ↥L]
    (hU : IsPSU 3 2 2 (↥L ⧸ Subgroup.center ↥L)) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hg5 : g ^ 5 = 1) :
    ∃ j ∈ L, ∃ z ∈ Subgroup.centralizer (L : Set G), g = j * z := by
  have hα : (actionOnQuot L ⟨g, hg⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 5 = 1 :=
      Subtype.ext (by simpa using hg5)
    rw [this, map_one]
  have h1 := aut_pow_five_inner_u34 hU hα
  have h2 := (actionOnQuot_mem_inner_iff L hg).mp h1
  exact (mem_sup_centralizer_iff L).mp h2

theorem card_u34 {X : Type} [Group X] (h : IsPSU 3 2 2 X) : Nat.card X = 62400 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four h

end CFSG.Quasithin.SBd10

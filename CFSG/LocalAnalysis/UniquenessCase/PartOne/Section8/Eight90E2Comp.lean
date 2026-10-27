module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime
import CFSG.GroupTheory.QuasisimpleCenterDivisibility
import CFSG.GroupTheory.PRankBound
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.ClassicalInvolution.GenericLocal.Twins
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (K_CatalogueThreePrimeSz)

variable {H : Type} [Group H] [Finite H]

theorem twentyseven_dvd_card_of_nine_dvd_card_quotient_center {Y C : Subgroup H}
    (hY3 : Nat.card Y = 3) (hYcent : Y ≤ Subgroup.centralizer (C : Set H))
    (hsplit : Y ≤ C ∨ Y ⊓ C = ⊥) (h9 : 9 ∣ Nat.card (↥C ⧸ center ↥C)) :
    27 ∣ Nat.card H := by
  rcases hsplit with hYC | hbot
  ·
    have hYZ : Y.subgroupOf C ≤ Subgroup.center ↥C := by
      intro y hy
      rw [Subgroup.mem_center_iff]
      intro c
      have hyY : (y : H) ∈ Y := Subgroup.mem_subgroupOf.mp hy
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hYcent hyY)) c.1 c.2)
    have hcardYc : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC).toEquiv
    have h3Z : 3 ∣ Nat.card ↥(Subgroup.center ↥C) := by
      have h := Subgroup.card_dvd_of_le hYZ
      rwa [hcardYc, hY3] at h
    obtain ⟨a, ha⟩ := h3Z
    obtain ⟨b, hb⟩ := h9
    have h27C : 27 ∣ Nat.card ↥C := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C)]
      refine ⟨b * a, ?_⟩
      rw [hb, ha]
      ring
    exact h27C.trans (Subgroup.card_subgroup_dvd_card C)
  ·
    have hsup : Nat.card ↥(Y ⊔ C) = 3 * Nat.card ↥C := by
      have hformula :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (H := Y) (K := C) (hYcent.trans (Subgroup.centralizer_le_normalizer (C : Set H)))
      rw [hbot, hY3] at hformula
      simpa using hformula
    have h9C : 9 ∣ Nat.card ↥C := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C)]
      exact dvd_mul_of_dvd_left h9 _
    have h27sup : 27 ∣ Nat.card ↥(Y ⊔ C) := by
      rw [hsup]
      obtain ⟨k, hk⟩ := h9C
      refine ⟨k, ?_⟩
      rw [hk]
      ring
    exact h27sup.trans (Subgroup.card_subgroup_dvd_card (Y ⊔ C))

theorem not_nine_dvd_card_quotient_center {Y C : Subgroup H} (hY : Y.Normal)
    (hY3 : Nat.card Y = 3) (h27 : ¬ 27 ∣ Nat.card H) (hC : CFSG.IsComponent C) :
    ¬ 9 ∣ Nat.card (↥C ⧸ center ↥C) := by
  intro h9
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYp : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by rw [hY3, pow_one])
  have hcomm : ⁅C, Y⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer
      (@IsNilpotent.to_isSolvable ↥Y _ hYp.isNilpotent) hY.isSubnormal).1 C hC
  have hYcent : Y ≤ Subgroup.centralizer (C : Set H) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hsplit : Y ≤ C ∨ Y ⊓ C = ⊥ := by
    by_cases hYC : Y ≤ C
    · exact Or.inl hYC
    · right
      have hdvd : Nat.card ↥(Y ⊓ C) ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le inf_le_left
      rw [hY3] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have htop : Y ⊓ C = Y := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
        exact hYC (le_of_eq htop.symm |>.trans inf_le_right)
  exact h27 (twentyseven_dvd_card_of_nine_dvd_card_quotient_center hY3 hYcent hsplit h9)

theorem encard_components_three_dvd_le_two (h27 : ¬ 27 ∣ Nat.card H) :
    {C : Subgroup H | CFSG.IsComponent C ∧ 3 ∣ Nat.card C}.encard ≤ 2 := by
  classical
  set S : Set (Subgroup H) := {C | CFSG.IsComponent C ∧ 3 ∣ Nat.card C} with hSdef
  have hSfin : S.Finite := Set.toFinite S
  have hcard : S.encard = (hSfin.toFinset.card : ℕ∞) := by
    rw [← hSfin.cast_ncard_eq, Set.ncard_eq_toFinset_card S hSfin]
  rw [hcard]
  have hle : hSfin.toFinset.card ≤ 2 := by
    have hcomp : ∀ J ∈ hSfin.toFinset, CFSG.Open.IsComponentOf J ⊤ := by
      intro J hJ
      exact (CFSG.isComponent_iff_open J).mp ((Set.Finite.mem_toFinset hSfin).mp hJ).1
    have hdvd : ∀ J ∈ hSfin.toFinset, 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
      intro J hJ
      have hJS := (Set.Finite.mem_toFinset hSfin).mp hJ
      exact CFSG.dvd_card_quotient_center_of_quasisimple hJS.1.1 (by norm_num) hJS.2
    have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.card_le_pRank_of_components_gen
      (Y := H) hSfin.toFinset hcomp ⊤ (fun J _ => le_top) (by norm_num) (by norm_num) hdvd
    have hp : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 2 :=
      CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (H := ⊤) (p := 3) (k := 2)
        (by norm_num) (by simpa using h27)
    exact hrank.trans hp
  exact_mod_cast hle

theorem exists_isSz_quotient_center (hK3 : K_CatalogueThreePrimeSz)
    (hH : CFSG.Open.IsKGroup H) {C : Subgroup H} (hC : CFSG.IsComponent C)
    (h3 : ¬ 3 ∣ Nat.card C) : ∃ m : ℕ, IsSz (↥C ⧸ center ↥C) m := by
  classical
  let J := ↥C ⧸ Subgroup.center ↥C
  let hJsimp : IsSimpleGroup J := hC.1.2.1
  have hJnonab : ∃ a b : J, a * b ≠ b * a := hC.1.2.2
  have hJcomm : ¬ IsMulCommutative J := by
    intro h
    let : IsMulCommutative J := h
    obtain ⟨a, b, hab⟩ := hJnonab
    exact hab (mul_comm a b)
  have hZbot : Subgroup.center J = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hJcomm
  let hJperf : Group.IsPerfect J :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hJcomm
  have hJquasi : CFSG.Open.IsQuasisimple J := by
    refine ⟨hJperf.commutator_eq_top, ?_⟩
    let e : J ⧸ Subgroup.center J ≃* J :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup_congr.mpr hJsimp
  have hKJ : CFSG.Open.IsKGroup J := (hH.subgroup C).quotient (Subgroup.center ↥C)
  have h3J : ¬ 3 ∣ Nat.card J := by
    intro hdvd
    apply h3
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C)]
    exact dvd_mul_of_dvd_left hdvd _
  have h3Jpi : 3 ∉ piSet (⊤ : Subgroup J) := by
    intro hmem
    exact h3J (by simpa using hmem.2)
  obtain ⟨m, hSz⟩ := hK3 J hKJ hJquasi h3Jpi
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : CFSG.pCore 2 J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 J) with h | h
    · exact h
    · exfalso
      have htop : IsPGroup 2 (⊤ : Subgroup J) := h ▸ CFSG.pCore_isPGroup
      have h2J : IsPGroup 2 J := htop.of_equiv Subgroup.topEquiv
      exact Group.IsPerfect.not_isNilpotent J (h2J.isNilpotent)
  refine ⟨m, ?_⟩
  let e : (J ⧸ CFSG.pCore 2 J) ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz

theorem exists_orderOf_eq_two_of_isSz_quotient_center {G : Type} [Group G] [Finite G]
    {C : Subgroup G} {m : ℕ} (hSz : IsSz (↥C ⧸ Subgroup.center ↥C) m) :
    ∃ s ∈ C, orderOf s = 2 := by
  have h2quot : 2 ∣ Nat.card (↥C ⧸ Subgroup.center ↥C) := by
    obtain ⟨E, hE⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_four_of_lieModel_twistedB2 hSz
    have h4 : 4 ∣ Nat.card (↥C ⧸ Subgroup.center ↥C) := by
      rw [← hE.2]
      exact Subgroup.card_subgroup_dvd_card E
    exact dvd_trans (by norm_num) h4
  have h2C : 2 ∣ Nat.card ↥C :=
    h2quot.trans (Subgroup.card_quotient_dvd_card (Subgroup.center ↥C))
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 h2C
  refine ⟨x, x.2, ?_⟩
  rw [Subgroup.orderOf_coe, hxord]

theorem false_of_four_components_not_three_dvd (hK3 : K_CatalogueThreePrimeSz)
    (hH : CFSG.Open.IsKGroup H)
    (h5 : ∀ s : H, orderOf s = 2 → CFSG.Open.pRank 5 (centralizer ({s} : Set H)) ≤ 3)
    {C1 : Subgroup H} (hC1 : CFSG.IsComponent C1) {s : H} (hsC1 : s ∈ C1)
    (hsord : orderOf s = 2) (T : Finset (Subgroup H)) (hTcard : T.card = 4)
    (hT : ∀ J ∈ T, CFSG.IsComponent J ∧ ¬ 3 ∣ Nat.card J) (hC1T : C1 ∉ T) : False := by
  have hcomp : ∀ J ∈ T, CFSG.Open.IsComponentOf J ⊤ := fun J hJ =>
    (CFSG.isComponent_iff_open J).mp (hT J hJ).1
  have hle : ∀ J ∈ T, J ≤ Subgroup.centralizer ({s} : Set H) := by
    intro J hJ
    have hJne : J ≠ C1 := by
      intro h
      exact hC1T (h ▸ hJ)
    have hcomm : ⁅J, C1⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute (hT J hJ).1 hC1 with h | h
      · exact absurd h hJne
      · exact h
    have hleC : J ≤ Subgroup.centralizer (C1 : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hys : y = s := by simpa using hy
    rw [hys]
    exact (Subgroup.mem_centralizer_iff.mp (hleC hj)) s hsC1
  have hdvd : ∀ J ∈ T, 5 ∣ Nat.card (↥J ⧸ center ↥J) := by
    intro J hJ
    obtain ⟨m, hSz⟩ := exists_isSz_quotient_center hK3 hH (hT J hJ).1 (hT J hJ).2
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz
      hSz
  have hrank := CFSG.LocalAnalysis.RankThreeUC.S15.card_le_pRank_of_components_gen
    (Y := H) T hcomp _ hle (by norm_num) (by norm_num) hdvd
  rw [hTcard] at hrank
  have := h5 s hsord
  omega

theorem encard_components_not_three_dvd_le_four (hK3 : K_CatalogueThreePrimeSz)
    (hH : CFSG.Open.IsKGroup H)
    (h5 : ∀ s : H, orderOf s = 2 → CFSG.Open.pRank 5 (centralizer ({s} : Set H)) ≤ 3) :
    {C : Subgroup H | CFSG.IsComponent C ∧ ¬ 3 ∣ Nat.card C}.encard ≤ 4 := by
  classical
  set S : Set (Subgroup H) := {C | CFSG.IsComponent C ∧ ¬ 3 ∣ Nat.card C} with hSdef
  have hSfin : S.Finite := Set.toFinite S
  rw [← hSfin.cast_ncard_eq]
  by_contra hle
  have h5n : 5 ≤ S.ncard := by
    have hlt : (4 : ℕ∞) < (S.ncard : ℕ∞) := lt_of_not_ge hle
    exact_mod_cast hlt
  have hcardT : 5 ≤ hSfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card S hSfin]
    exact h5n
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := hSfin.toFinset) hcardT
  have hmemS : ∀ J ∈ T, CFSG.IsComponent J ∧ ¬ 3 ∣ Nat.card J := fun J hJ =>
    (Set.Finite.mem_toFinset hSfin).mp (hTS hJ)
  obtain ⟨C1, hC1T⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hC1comp : CFSG.IsComponent C1 := (hmemS C1 hC1T).1
  obtain ⟨m, hSz⟩ := exists_isSz_quotient_center hK3 hH hC1comp (hmemS C1 hC1T).2
  obtain ⟨s, hsC1, hsord⟩ := exists_orderOf_eq_two_of_isSz_quotient_center hSz
  have hT'card : (T.erase C1).card = 4 := by
    rw [Finset.card_erase_of_mem hC1T, hTcard]
  have hT'mem : ∀ J ∈ T.erase C1, CFSG.IsComponent J ∧ ¬ 3 ∣ Nat.card J :=
    fun J hJ => hmemS J (Finset.mem_of_mem_erase hJ)
  exact false_of_four_components_not_three_dvd hK3 hH h5 hC1comp hsC1 hsord (T.erase C1)
    hT'card hT'mem (Finset.notMem_erase C1 T)

theorem le_normalizer_of_isComponent (hK3 : K_CatalogueThreePrimeSz)
    (hH : CFSG.Open.IsKGroup H) (h27 : ¬ 27 ∣ Nat.card H)
    (h5 : ∀ s : H, orderOf s = 2 → CFSG.Open.pRank 5 (centralizer ({s} : Set H)) ≤ 3)
    {K C : Subgroup H} (hK : ⁅K, K⁆ = K) (hC : CFSG.IsComponent C) :
    K ≤ normalizer (C : Set H) := by
  classical
  let : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  by_cases h3C : 3 ∣ Nat.card C
  · let S : Set (Subgroup H) := {D | CFSG.IsComponent D ∧ 3 ∣ Nat.card D}
    have hS : ∀ p ∈ K, ∀ M ∈ S, M.map (MulAut.conj p).toMonoidHom ∈ S := by
      intro p _ M hM
      refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj p) hM.1, ?_⟩
      rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]
      exact hM.2
    have hcard : S.encard ≤ 4 :=
      (encard_components_three_dvd_le_two h27).trans (by norm_num)
    exact CFSG.ClassicalInvolution.perfect_le_normalizer_of_invariant hS hcard ⟨hC, h3C⟩
  · let S : Set (Subgroup H) := {D | CFSG.IsComponent D ∧ ¬ 3 ∣ Nat.card D}
    have hS : ∀ p ∈ K, ∀ M ∈ S, M.map (MulAut.conj p).toMonoidHom ∈ S := by
      intro p _ M hM
      refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj p) hM.1, ?_⟩
      rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]
      exact hM.2
    exact CFSG.ClassicalInvolution.perfect_le_normalizer_of_invariant hS
      (encard_components_not_three_dvd_le_four hK3 hH h5) ⟨hC, h3C⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

module

public import CFSG.RankThree.PartTwo.Sec19.Step1915Proof
public import CFSG.RankThree.PartTwo.Sec19.Item19Res7ProofQuot
import CFSG.Quasithin.Vol2.F134LieD4
import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.RankThree.PartTwo.Sec19.Item19Res7ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Sec21 Sec21.Item211Proof Item19Res7Proof

@[expose] def Census1915Image : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L A : Subgroup G) (c : G),
    SectionFourHyp ↥(K ⊔ A) → CFSG.Open.pCoreOf 2 K ≠ ⊥ → Group.IsPerfect K →
    IsQuasisimple (K ⧸ CFSG.pCore 2 K) → A ≤ Subgroup.normalizer (K : Set G) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → c ∈ A → orderOf c = 3 →
    ¬ (∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) →
    L ≤ K → L ≤ Subgroup.centralizer ({c} : Set G) →
    (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal → Group.IsPerfect L →
    A ≤ Subgroup.normalizer (L : Set G) →
    (∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      a ∈ Subgroup.zpowers c) →
    (Sec13.IsLThreePi (L ⧸ CFSG.pCore 2 L) ∨
      Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    IsQuasisimple ↥((L.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)))

theorem census1915_of_item4_29
    (h429 : Sec4.Item4_29) (hI : Census1915Image) (h41 : Sec4.Item4_1LargePrime)
    (hExc : PartOne.ExceptionalCenterSmallPrimes) : Census1915 := by
  intro G _ _ K L A c hKA4 hO2 hKp hKq hAK hAe hA27 hcA hc3 hcK hLK hLc hLsn hLp hAL hsec htype
  have hImg := hI G K L A c hKA4 hO2 hKp hKq hAK hAe hA27 hcA hc3 hcK hLK hLc hLsn hLp hAL hsec
    htype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := ⟨hAe, hA27⟩
  have hAp : IsPGroup 3 A := hA.isPGroup
  have hθq : IsQuasisimple (lBar K) := isQuasisimple_theta_quot hKq
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAK
  have hX : SectionFourHyp (QuotX K A) := sectionFourHyp_quotX h41 hKA4 hAp hAK Φ₀ hθq
  have hθX : aschbacherSolvableCore 3 (QuotX K A) = ⊥ :=
    (theta_quotient_core_and_ranks (G := ↥(K ⊔ A))).1
  have hEF := partTwoE_eq_partTwoF_quotX hKA4 hO2 hAK
  have hL₁ : IsComponent (lOne K A) := isComponent_lOne hAK Φ₀ hθq
  have hA₁ : Late.IsE27 (aOne K A) := isE27_aOne hA
  have hc₁A : piX K A ⟨c, Subgroup.mem_sup_right hcA⟩ ∈ aOne K A := piX_mem_aOne hcA
  have hc₁3 : orderOf (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    rw [orderOf_piX hAp hcA, hc3]
  have hc₁1 : piX K A ⟨c, Subgroup.mem_sup_right hcA⟩ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc₁3
    norm_num at hc₁3
  set J := (L.subgroupOf (K ⊔ A)).map (piX K A) with hJdef
  set C₁ := lOne K A ⊓ Subgroup.centralizer
    ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set (QuotX K A)) with hC₁def
  have hJC : J ≤ C₁ := image_le_inf_centralizer (A := A) hLK hLc hcA
  set KK : Subgroup C₁ := J.subgroupOf C₁ with hKKdef
  have hKKJ : KK.map C₁.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJC
  obtain ⟨ψ, hψs, -, hψk⟩ := exists_psi hAp hAK hLK
  obtain ⟨eIJ⟩ := nonempty_imageTheta_equiv hAp hAK hLK
  have hJq := LocalCores.isQuasisimple_of_mulEquiv eIJ hImg
  have e₁ := Subgroup.subgroupOfEquivOfLe hJC
  have hKKq : IsQuasisimple KK := LocalCores.isQuasisimple_of_mulEquiv e₁.symm hJq
  have hKKsn : KK.IsSubnormal := isSubnormal_image hAp hAK hLK hLc hcA hLsn
  have hLOp : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := by
    have := hLp
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 L))
      (QuotientGroup.mk'_surjective _)
  have hLs : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := isSimpleGroup_of_type1915 hLOp htype
  have hcomap := comap_pCore_eq_of_surjective ψ hψs hJq hLs
  have hO : ∀ l ∈ L, l ∈ inSubgroup (aschbacherSolvableCore 3) K →
      l ∈ CFSG.Open.pCoreOf 2 L := by
    intro l hl hlθ
    have h1 : ψ ⟨l, hl⟩ = 1 := (hψk ⟨l, hl⟩).mpr hlθ
    have h2 : (⟨l, hl⟩ : L) ∈ (CFSG.pCore 2 _).comap ψ := by
      rw [Subgroup.mem_comap, h1]
      exact Subgroup.one_mem _
    rw [hcomap] at h2
    exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h2
  have hcent := zpowers_eq_aOne_inf_centralizer hAp hAK hLK hLc hcA hAL hO hsec
  have eL : L ⧸ CFSG.pCore 2 L ≃* KK ⧸ CFSG.pCore 2 KK := (quotientPCoreEquiv ψ hψs hJq hLs).trans
    (QuotientGroup.congr (CFSG.pCore 2 J) (CFSG.pCore 2 KK) e₁.symm
      (CFSG.pCore_map_iso 2 e₁.symm))
  rcases h429 (QuotX K A) hX hθX hEF (aOne K A) hA₁ _ hc₁A hc₁1 (lOne K A) hL₁ KK
      ⟨hKKq, hKKsn⟩ _ rfl (by
        rcases htype with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩
        · exact Or.inl ⟨p, e, hp, he, isoLThreePi_of_mulEquiv eL hiso⟩
        · exact Or.inr (Or.inr (Or.inl ⟨eL.symm.trans φ⟩)))
      (by rw [hKKJ]; exact hcent) with
    h1 | ⟨⟨eA7⟩, -⟩ | ⟨n, hn, hKKiso, hL₁iso, hind⟩ | ⟨n, hn, hKKiso, hM, hind⟩
  ·
    exfalso
    apply hcK
    refine mem_pCoreOf_of_mem_theta (hAK hcA) hKp hKq fun k hk => ?_
    have hkJ : piX K A ⟨k, Subgroup.mem_sup_left hk⟩ ∈ J := by
      rw [← hKKJ, h1]
      exact ⟨⟨k, Subgroup.mem_sup_left hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hJC hkJ).2
    have hone : piX K A ((⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(K ⊔ A)) *
        ⟨k, Subgroup.mem_sup_left hk⟩ * (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(K ⊔ A))⁻¹ *
        (⟨k, Subgroup.mem_sup_left hk⟩ : ↥(K ⊔ A))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact (piX_eq_one_iff hAp hAK _).mp hone
  ·
    exfalso
    have h20160 := le_card_of_type1915 hLOp htype
    have hcardL := Nat.card_congr eL.toEquiv
    have hle : Nat.card (KK ⧸ CFSG.pCore 2 KK) ≤ Nat.card KK :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 KK))
    have hF7 : Nat.card (Fin 7) = 7 := by simp
    have hA7 : Nat.card KK = 2520 := by
      rw [Nat.card_congr eA7.toEquiv, nat_card_alternatingGroup, hF7]
      decide
    have : Nat.card (L ⧸ CFSG.pCore 2 L) ≤ 2520 := hcardL ▸ hA7 ▸ hle
    omega
  ·
    have hKKs := isSimpleGroup_of_type1915 hKKq.1 (Or.inl ⟨2, n, inferInstance, hn, hKKiso⟩)
    have hbot := pCore_eq_bot_of_isSimpleGroup (exists_ne_comm_of_isQuasisimple hKKq)
    have eKK0 := (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    have hθeq := theta_eq_pCore_of_isLThreePi hKq
      ⟨2, 3 * n, inferInstance, by omega, isoLThreePi_of_mulEquiv Φ₀.symm hL₁iso⟩
    have eK := (QuotientGroup.quotientMulEquivOfEq hθeq.symm).trans Φ₀
    exact Or.inl ⟨2, n, inferInstance, hn, isoLThreePi_of_mulEquiv (eL.trans eKK0).symm hKKiso,
      isoLThreePi_of_mulEquiv eK.symm hL₁iso, inducesStdKind_of_lOne hAK hΦ₀ hcA hind⟩
  ·
    have hKKs := isSimpleGroup_of_type1915 hKKq.1 (Or.inl ⟨2, n, inferInstance, hn, hKKiso⟩)
    have hbot := pCore_eq_bot_of_isSimpleGroup (exists_ne_comm_of_isQuasisimple hKKq)
    have eKK0 := (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    obtain ⟨-, F, _, _, σ, hF, hσ, ⟨eF⟩⟩ :=
      CFSG.Quasithin.F134.LieD4.exists_mulEquiv_graphFixedRootGroup hM
    have hZ1 : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
      center_eq_bot_of_mulEquiv (Φ₀.trans eF)
        (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot (σ := σ.toRingHom)
          σ.surjective)
    have hMK := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv Φ₀ hM
    have hθeq := theta_eq_pCore_of_exceptional hExc hKq hZ1 (by decide) hMK
    have eK := (QuotientGroup.quotientMulEquivOfEq hθeq.symm).trans Φ₀
    exact Or.inr ⟨n, hn, F, inferInstance, inferInstance, hF, σ, hσ, ⟨Φ₀.trans eF⟩,
      isoLThreePi_of_mulEquiv (eL.trans eKK0).symm hKKiso,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eK hM,
      KFacts.InducesStdKind.inducesOuterTheta K (inducesStdKind_of_lOne hAK hΦ₀ hcA hind)
        (by decide)⟩

end CFSG.RankThree.PartTwo.Sec19

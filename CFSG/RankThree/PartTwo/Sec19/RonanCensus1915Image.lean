module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res7Proof1915
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
import CFSG.RankThree.PartTwo.Sec19.RonanCensus1915ImageCfg
import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Sec21 Sec21.Item211Proof Item19Res7Proof

section Census

theorem census1915Image_of_rowsS (R : Sec4.RonanK429.K429RowsS) (h41 : Sec4.Item4_1LargePrime) :
    Census1915Image := by
  intro G _ _ K L A c hKA4 _ hKp hKq hAK hAe hA27 hcA hc3 hcK hLK hLc hLsn hLp hAL hsec htype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := ⟨hAe, hA27⟩
  have hAp : IsPGroup 3 A := hA.isPGroup
  have hθq : IsQuasisimple (lBar K) := isQuasisimple_theta_quot hKq
  obtain ⟨Φ₀, -⟩ := exists_lEquiv hAK
  have hX : SectionFourHyp (QuotX K A) := sectionFourHyp_quotX h41 hKA4 hAp hAK Φ₀ hθq
  have hθX : aschbacherSolvableCore 3 (QuotX K A) = ⊥ :=
    (theta_quotient_core_and_ranks (G := ↥(K ⊔ A))).1
  have hL₁ : IsComponent (lOne K A) := isComponent_lOne hAK Φ₀ hθq
  have hA₁ : Late.IsE27 (aOne K A) := isE27_aOne hA
  have hc₁A : piX K A ⟨c, Subgroup.mem_sup_right hcA⟩ ∈ aOne K A := piX_mem_aOne hcA
  have hc₁3 : orderOf (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    rw [orderOf_piX hAp hcA, hc3]
  have hc₁1 : piX K A ⟨c, Subgroup.mem_sup_right hcA⟩ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc₁3
    norm_num at hc₁3
  have hAN : aOne K A ≤ Subgroup.normalizer (lOne K A : Set (QuotX K A)) :=
    fun x _ => mem_normalizer_lOne hAK x
  set J := (L.subgroupOf (K ⊔ A)).map (piX K A) with hJdef
  have hJC : J ≤ lOne K A ⊓ Subgroup.centralizer
      ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set (QuotX K A)) :=
    image_le_inf_centralizer (A := A) hLK hLc hcA
  have hJL₁ : J ≤ lOne K A := hJC.trans inf_le_left
  have hJsn := isSubnormal_image hAp hAK hLK hLc hcA hLsn
  obtain ⟨ψ, hψs, hψv, hψk⟩ := exists_psi hAp hAK hLK
  obtain ⟨eIJ⟩ := nonempty_imageTheta_equiv hAp hAK hLK
  have hLOp : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) := by
    have := hLp
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 L))
      (QuotientGroup.mk'_surjective _)
  have hLs : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := isSimpleGroup_of_type1915 hLOp htype
  have hJp : Group.IsPerfect J := by
    have := hLp
    exact Group.IsPerfect.ofSurjective (f := ψ) hψs
  have hJn : Nontrivial J := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    have hLθ : L ≤ (aschbacherSolvableCore 3 K).map K.subtype := fun l hl =>
      (hψk ⟨l, hl⟩).mp (Subsingleton.elim _ _)
    have hθs : Group.IsSolvable (aschbacherSolvableCore 3 K) :=
      (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).1
    have hMs : Group.IsSolvable ((aschbacherSolvableCore 3 K).map K.subtype) :=
      Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective _)
    have hLsol : Group.IsSolvable L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLθ)
    haveI : Nontrivial (L ⧸ CFSG.pCore 2 L) := hLs.toNontrivial
    haveI : Nontrivial L := (QuotientGroup.mk'_surjective (CFSG.pCore 2 L)).nontrivial
    haveI := hLp
    exact Group.IsPerfect.not_isSolvable L hLsol
  have hcomap := Census1915ImageProof.comap_pCore_eq_of_surjective_of_perfect ψ hψs hJp hLs
  have eL : L ⧸ CFSG.pCore 2 L ≃* J ⧸ CFSG.pCore 2 J :=
    Census1915ImageProof.quotientPCoreEquivOfPerfect ψ hψs hJp hLs
  have hmemO : ∀ (l : L), ψ l ∈ CFSG.pCore 2 J → (l : G) ∈ CFSG.Open.pCoreOf 2 L := by
    intro l hl
    have h1 : l ∈ (CFSG.pCore 2 J).comap ψ := hl
    rw [hcomap] at h1
    exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
  have hO : ∀ l ∈ L, l ∈ inSubgroup (aschbacherSolvableCore 3) K →
      l ∈ CFSG.Open.pCoreOf 2 L := by
    intro l hl hlθ
    refine hmemO ⟨l, hl⟩ ?_
    rw [(hψk ⟨l, hl⟩).mpr hlθ]
    exact Subgroup.one_mem _
  have hcent := zpowers_eq_aOne_inf_centralizer hAp hAK hLK hLc hcA hAL hO hsec
  have hL₁c : ¬ lOne K A ≤ Subgroup.centralizer
      ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set (QuotX K A)) := by
    intro hle
    apply hcK
    refine mem_pCoreOf_of_mem_theta (hAK hcA) hKp hKq fun k hk => ?_
    have hkL₁ : piX K A ⟨k, Subgroup.mem_sup_left hk⟩ ∈ lOne K A :=
      ⟨⟨k, Subgroup.mem_sup_left hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hle hkL₁)
    have hone : piX K A ((⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(K ⊔ A)) *
        ⟨k, Subgroup.mem_sup_left hk⟩ * (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(K ⊔ A))⁻¹ *
        (⟨k, Subgroup.mem_sup_left hk⟩ : ↥(K ⊔ A))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    exact (piX_eq_one_iff hAp hAK _).mp hone
  have hAC : aOne K A ⊓ Subgroup.centralizer (lOne K A : Set (QuotX K A)) = ⊥ :=
    Sec4.Res429.inf_centralizer_eq_bot hA₁ hc₁A hc₁1 hJL₁ hL₁c hcent
  have hAJ : aOne K A ≤ Subgroup.normalizer (J : Set (QuotX K A)) := by
    have h1 : A.subgroupOf (K ⊔ A) ≤
        Subgroup.normalizer ((L.subgroupOf (K ⊔ A) : Subgroup ↥(K ⊔ A)) : Set ↥(K ⊔ A)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq (hLK.trans le_sup_left)]
      exact Subgroup.subgroupOf_mono _ hAL
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  have hfaith : ∀ a₁ ∈ aOne K A, (∀ y ∈ J, a₁ * y * a₁⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 J) →
      a₁ ∈ Subgroup.zpowers (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) := by
    intro a₁ ha₁ h
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne ha₁
    have ha : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      intro l hl
      have hmem : a * l * a⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL haA) l).mp hl) (L.inv_mem hl)
      have hlJ : piX K A ⟨l, Subgroup.mem_sup_left (hLK hl)⟩ ∈ J :=
        ⟨⟨l, Subgroup.mem_sup_left (hLK hl)⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have hψeq : (ψ ⟨a * l * a⁻¹ * l⁻¹, hmem⟩ : QuotX K A) =
          piX K A ⟨a, Subgroup.mem_sup_right haA⟩ * piX K A ⟨l, Subgroup.mem_sup_left (hLK hl)⟩ *
            (piX K A ⟨a, Subgroup.mem_sup_right haA⟩)⁻¹ *
            (piX K A ⟨l, Subgroup.mem_sup_left (hLK hl)⟩)⁻¹ := by
        rw [hψv, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      refine hmemO ⟨_, hmem⟩ ?_
      rw [Sec18.mem_pCore_iff_mem_pCoreOf, hψeq]
      exact h _ hlJ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsec a haA ha)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simpa using hk
  have htypeJ : Sec4.RonanK429.IsType429 (J ⧸ CFSG.pCore 2 J) := by
    rcases htype with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl ⟨p, e, hp, he, Sec4.RonanK429.isoLThreePi_of_mulEquiv eL.symm hiso⟩
    · exact Or.inr (Or.inr (Or.inl ⟨eL.symm.trans φ⟩))
  have hZJ : Subgroup.center (J ⧸ CFSG.pCore 2 J) = ⊥ := by
    haveI := hLs
    haveI : IsSimpleGroup (J ⧸ CFSG.pCore 2 J) := MulEquiv.isSimpleGroup eL.symm
    haveI := hJp
    exact Sec4.RonanK429.center_eq_bot_of_isSimpleGroup_of_isPerfect
  have hZ3 : IsPGroup 3 (Subgroup.center (lOne K A)) :=
    Sec4.RonanK429.isPGroup_center_of_isComponent hθX hL₁
  have hJZ : J.subgroupOf (lOne K A) ⊓ Subgroup.center (lOne K A) = ⊥ :=
    Census1915ImageProof.inf_eq_bot_of_center_quot_eq_bot
      (Sec4.RonanK429.center_eq_bot_of_mulEquiv
        (Sec4.RonanK429.quotPCoreTwoCongr (Subgroup.subgroupOfEquivOfLe hJL₁)) hZJ)
      le_rfl hZ3
  have hcfg := Census1915ImageProof.cfgS429_of_perfect hA₁ hc₁A hL₁.1.1 hAN hAC hL₁c hJC hJp hJsn
    htypeJ hAJ hJZ hfaith
  have hlist := Sec4.RonanK432.list42_quotient_center hL₁.1
    (Sec4.sectionFourHyp_subgroup hX (lOne K A))
  have hO2S := (R.rowS_of_list42 hL₁.1.2.1 hL₁.1.2.2 hlist _ _ _ hcfg).1
  have h1 := Census1915ImageProof.pCore_eq_bot_of_isSubnormal hcfg.isSubnormal hO2S
  have h2 : CFSG.pCore 2 ((J.subgroupOf (lOne K A)).map
      (QuotientGroup.mk' (Subgroup.center (lOne K A)))) = ⊥ := by
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
      (Subgroup.subgroupOfEquivOfLe hcfg.le_autFix), h1, Subgroup.map_bot]
  have h3 : CFSG.pCore 2 J = ⊥ := by
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
      (Sec4.RonanK429.equivBar hJL₁ hJZ).symm, h2, Subgroup.map_bot]
  have eJ : J ≃* L ⧸ CFSG.pCore 2 L :=
    ((QuotientGroup.quotientMulEquivOfEq h3).trans QuotientGroup.quotientBot).symm.trans eL.symm
  haveI := hLs
  haveI : IsSimpleGroup J := MulEquiv.isSimpleGroup eJ
  have hna : ∃ a b : J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI := hJp
    exact Group.IsPerfect.not_isMulCommutative J ⟨⟨hcon⟩⟩
  exact LocalCores.isQuasisimple_of_mulEquiv eIJ.symm
    (LocalCores.isQuasisimple_of_isSimpleGroup hna).1

end Census

end CFSG.RankThree.PartTwo.Sec19

module

public import CFSG.RankThree.PartOne.S13K.KF133One
public import CFSG.RankThree.PartOne.S15K.KtData
public import CFSG.RankThree.PartOne.S11.Sec11One
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isKt_le_kZero {p : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (h : IsKt p E t K) : K ≤ kZero p E t := by
  by_cases hex : ∃ f, kExceptional p (kZero p E t) f
  · obtain ⟨f, hf⟩ := hex
    exact (h.1 f hf).1
  · exact (h.2 hex).le

omit [Finite G] in
theorem autFixedInG_le_centralizer_of_isKt {p : ℕ} {E : Subgroup G} {t : MulAut E}
    {K : Subgroup G} (h : IsKt p E t K) :
    autFixedInG E t ≤ Subgroup.centralizer (K : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' := S15K.kZero_le_centralizer p E t (isKt_le_kZero h hk)
  exact (Subgroup.mem_centralizer_iff.mp hk' y hy).symm

@[expose] def SplitType (p : ℕ) (K : Subgroup G) : Prop :=
  ∀ b : ↥K, b ≠ 1 → b ^ p = 1 →
    ∃ S₀ : Subgroup ↥K, S₀ ≠ ⊥ ∧ IsPGroup 2 S₀ ∧ b ∈ Subgroup.normalizer (S₀ : Set ↥K) ∧
      ⁅S₀, Subgroup.zpowers b⁆ = S₀

omit [Finite G] in
theorem splitType_of_psl_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {g : ℕ}
    (hmod : StatedClassicalModel ↥K .PSL 2 2 g) (hpg : p ∣ 2 ^ g - 1) : SplitType p K :=
  fun _ hb1 hbp => S15K.exists_two_subgroup_of_model hmod hp hp2 hpg hb1 hbp

theorem exists_two_subgroup_of_split {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {t : MulAut E} (ht : t ∈ reflectionSet p E) {K : Subgroup G}
    (hK : IsKt p E t K) (hsplit : SplitType p K) (hmov : autMovedInG E t ≤ K) :
    ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, E⁆ := by
  have hp := h.prime
  obtain ⟨hdec, -, -⟩ := node121a_of_hyp G p A c L E h t ht
  obtain ⟨a, haE, ha1, hap, hMz⟩ := S15K.exists_gen_autMovedInG hp h.E_elem ht.1
  have haK : a ∈ K := hmov (hMz ▸ Subgroup.mem_zpowers a)
  obtain ⟨S₀, hS1, hS2, hSn, hSc⟩ := hsplit (⟨a, haK⟩ : ↥K)
    (fun h1 => ha1 (congrArg Subtype.val h1)) (Subtype.ext hap)
  set S : Subgroup G := S₀.map K.subtype with hSdef
  have hSK : S ≤ K := Subgroup.map_subtype_le _
  have hCS : autFixedInG E t ≤ Subgroup.centralizer (S : Set G) := fun y hy =>
    Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hSK)
      (autFixedInG_le_centralizer_of_isKt hK hy)
  have haN : a ∈ Subgroup.normalizer (S : Set G) :=
    S15K.mem_normalizer_map_subtype (a := (⟨a, haK⟩ : ↥K)) hSn
  have hEN : E ≤ Subgroup.normalizer (S : Set G) := by
    rw [hdec]
    refine sup_le (hCS.trans (Subgroup.centralizer_le_normalizer _)) ?_
    rw [hMz, Subgroup.zpowers_le]
    exact haN
  refine ⟨S, hSK, ?_, hS2.map _, hEN, ?_⟩
  · intro hb
    apply hS1
    rw [hSdef, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hb
    exact hb
  · have hSc' : ⁅S, Subgroup.zpowers a⁆ = S := by
      have h1 := congrArg (Subgroup.map K.subtype) hSc
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h1
      exact h1
    apply le_antisymm
    · calc S = ⁅S, Subgroup.zpowers a⁆ := hSc'.symm
        _ ≤ ⁅S, E⁆ := Subgroup.commutator_mono_right (Subgroup.zpowers_le.2 haE)
    · exact Subgroup.le_normalizer_iff_commutator_le_left.1 hEN

theorem mem_sectionTenZero_of_split {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) {t : MulAut E} (ht : t ∈ reflectionSet p E) {K : Subgroup G}
    (hK : IsKt p E t K) (hsplit : SplitType p K) (hmov : autMovedInG E t ≤ K) {e : G}
    (he : e ∈ autFixedInG E t) (he1 : e ≠ 1) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKI : K ≤ I) : I ∈ sectionTenZero p E := by
  obtain ⟨S, hSK, hS1, hS2, hSN, hSE⟩ := exists_two_subgroup_of_split h ht hK hsplit hmov
  have heE : e ∈ E := (Subgroup.map_subtype_le _) he
  exact ⟨mem_thetaComponentFamily_iff.mpr ⟨e, heE, he1, hI⟩, S, hSK.trans hKI, hS1, hS2, hSN, hSE⟩

theorem mem_thetaCompZeroStarE_of_zeroStar {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) {M : Subgroup G}
    (hM : M ∈ sectionTenZeroStar p E) : M ∈ thetaCompZeroStarE p E := by
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hEadm : E ∈ admissibleTriples p E := by
    refine ⟨le_rfl, h.E_elem, hEcard, ?_⟩
    rw [hEA]
    exact h.setup.2.2.2.2.2.2.2.2.1
  have hBE : ∀ B ∈ admissibleTriples p E, B = E := fun B hB =>
    Subgroup.eq_of_le_of_card_ge hB.1 (by rw [hB.2.2.1, hEcard])
  refine ⟨⟨E, hEadm, hM.1⟩, ⟨E, hEadm, hM.2.1⟩, fun J hJ hMJ => ?_⟩
  obtain ⟨B, hB, hJB⟩ := hJ
  rw [hBE B hB] at hJB
  exact hM.2.2 J hJB hMJ

theorem exists_zeroStar_of_split {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (hS : SchreierFor InCatalog) (h : Sec12Hyp G p A c L E) (hEA : E = A) {t : MulAut E}
    (ht : t ∈ reflectionSet p E) {K : Subgroup G} (hK : IsKt p E t K) (hsplit : SplitType p K)
    (hmov : autMovedInG E t ≤ K) {e : G} (he : e ∈ autFixedInG E t) (he1 : e ≠ 1)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) :
    ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J := by
  have hZ := mem_sectionTenZero_of_split h ht hK hsplit hmov he he1 hI hKI
  have hsetup : SteinbergBM.SectionTenSetup G p E := by
    rw [hEA]
    exact h.setup
  obtain ⟨M, hM, hIM⟩ := exists_zeroStar_above_of_zero hS hsetup hZ
  exact ⟨M, mem_thetaCompZeroStarE_of_zeroStar h hEA hM, hIM⟩

end CFSG.RankThree.PartOne.K133

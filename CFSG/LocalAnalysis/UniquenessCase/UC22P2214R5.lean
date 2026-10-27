module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
import CFSG.LocalAnalysis.UniquenessCase.UC6Grp
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P2214R

theorem card_sq_dvd_card_bar2 {M V K : Subgroup G} (hVM : M ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 M ≤ centralizer (V : Set G)) (hK : K ∈ calC M)
    (hc2 : (conjSetOf M K).ncard = 2) (hZ : center ↥(mbarImage M V K) = ⊥) :
    Nat.card ↥(mbarImage M V K) ^ 2 ∣ Nat.card (Bar2 (conjClosure M K)) := by
  obtain ⟨K', hK', hne⟩ : ∃ K' ∈ conjSetOf M K, K' ≠ K := by
    by_contra hall
    have hsub : conjSetOf M K ⊆ {K} := fun A hA => by
      by_contra hA'
      exact hall ⟨A, hA, hA'⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton K)
    rw [hc2, Set.ncard_singleton] at this
    omega
  have hK'C := uc22p2214_calC_of_mem_conjSetOf hK hK'
  obtain ⟨hXM, hMX, -⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK
  have hle : ∀ A ∈ conjSetOf M K, A ≤ conjClosure M K := fun A hA =>
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) A hA le_rfl
  have hcomm : ∀ x ∈ mbarImage M V K, ∀ y ∈ mbarImage M V K', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := uc22p22l_barImage_commute hK hK'C hne.symm
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) a) ⟨a, ha, rfl⟩
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) b) ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, ← QuotientGroup.eq_one_iff, uc22br_gt_mk_eq_one_iff hVM]
    exact hO ⟨_, h1, rfl⟩
  have hinf : mbarImage M V K ⊓ mbarImage M V K' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    have hxZ : (⟨x, hx⟩ : ↥(mbarImage M V K)) ∈ center ↥(mbarImage M V K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcomm y.1 y.2 x hx')
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hxZ)
  have hcard' : Nat.card ↥(mbarImage M V K') = Nat.card ↥(mbarImage M V K) := by
    obtain ⟨g, hg, rfl⟩ := hK'
    have he : mbarImage M V (K.map (MulAut.conj g).toMonoidHom) =
        (mbarImage M V K).map
          (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : MBar M V)).toMonoidHom :=
      uc22br4_mbarImage_map_conj M V K ⟨g, hg⟩
    rw [he]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hXbar : Nat.card ↥(mbarImage M V (conjClosure M K)) ∣
      Nat.card (Bar2 (conjClosure M K)) := by
    rw [uc22br4_card_mbarImage M V _ hVM hXM]
    show _ ∣ (CFSG.pCore 2 ↥(conjClosure M K)).index
    apply Subgroup.index_dvd_of_le
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hO (uc22p21c_pCoreOf_le_of_subnormal (CFSG.Quasithin.A3.subnormal_of_normal hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)) ⟨x, hx, rfl⟩)
  have hsup : mbarImage M V K ⊔ mbarImage M V K' ≤ mbarImage M V (conjClosure M K) :=
    sup_le (uc22p2214_mbarImage_mono (hle K ⟨1, M.one_mem, by ext; simp⟩))
      (uc22p2214_mbarImage_mono (hle K' hK'))
  have h1 := CFSG.LocalAnalysis.UniquenessCase.UC6.card_sup_of_commute_of_disjoint hcomm hinf
  rw [hcard'] at h1
  calc Nat.card ↥(mbarImage M V K) ^ 2 = Nat.card ↥(mbarImage M V K ⊔ mbarImage M V K') := by
        rw [h1, sq]
    _ ∣ Nat.card ↥(mbarImage M V (conjClosure M K)) := Subgroup.card_dvd_of_le hsup
    _ ∣ Nat.card (Bar2 (conjClosure M K)) := hXbar

theorem two_pow_twelve_dvd_pair (D : Data G) {Ch : Choice2011 G}
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hKC : K ∈ calC D.M)
    (hq : CFSG.Open.IsQuasisimple ↥(mbarImage D.M c.V K)) {n : ℕ}
    (hK : (2 < n ∧ IsL2 ↥(mbarImage D.M c.V K) n ∧ 5 ∣ 2 ^ n + 1) ∨
      IsSz ↥(mbarImage D.M c.V K) n)
    (hc2 : (conjSetOf D.M K).ncard = 2) :
    2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M K)) := by
  have h6 : 2 ^ 6 ∣ Nat.card ↥(mbarImage D.M c.V K) := by
    rcases hK with ⟨hn2, hL, h5⟩ | hSz
    · have h4 := CFSG.RankThree.PartTwo.Census.mod_four_of_five_dvd_two_pow_add_one h5
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
        (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))]
      exact (Nat.pow_dvd_pow 2 (by omega)).mul_right _
    · obtain ⟨-, -, -, -, -, h3⟩ := CFSG.Blueprint.LieModel.admissible hSz
      rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hSz, ← pow_mul]
      exact ((Nat.pow_dvd_pow 2 (by omega)).mul_right _).mul_right _
  haveI : IsSimpleGroup ↥(mbarImage D.M c.V K) := by
    rcases hK with ⟨-, hL, -⟩ | hSz
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have hsq := card_sq_dvd_card_bar2 c.hVM (uc22p22f_pCoreOf_le_cent hV h1930 c) hKC hc2
    (uc22p21k_center_eq_bot hq)
  calc 2 ^ 12 = (2 ^ 6) ^ 2 := by norm_num
    _ ∣ Nat.card ↥(mbarImage D.M c.V K) ^ 2 := pow_dvd_pow_of_dvd h6 2
    _ ∣ Nat.card (Bar2 (conjClosure D.M K)) := hsq

end P2214R

end CFSG.LocalAnalysis.UniquenessCase.UC22

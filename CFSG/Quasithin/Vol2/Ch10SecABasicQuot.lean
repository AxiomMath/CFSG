module

public import CFSG.Quasithin.Vol2.Ch10SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem subgroupOf_pCoreOf (K : Subgroup G) : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

theorem mk_eq_one_iff {K : Subgroup G} (k : ↥K) :
    (k : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff, ← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf]

theorem le_pCoreOf_of_commutator_le {K X : Subgroup G}
    (hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hXK : X ≤ K)
    (h : ⁅X, K⁆ ≤ pCoreOf 2 K) : X ≤ pCoreOf 2 K := by
  intro x hx
  have hz : ((⟨x, hXK hx⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have hcomm : ((⁅(⟨x, hXK hx⟩ : ↥K), k⁆ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
      (mk_eq_one_iff _).mpr (h (Subgroup.commutator_mem_commutator hx k.2))
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      at hcomm
    exact hcomm.symm
  rw [hc, Subgroup.mem_bot] at hz
  exact (mk_eq_one_iff _).mp hz

theorem center_eq_bot_of_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    have hle : K ≤ pCoreOf 2 K := by
      conv_lhs => rw [← hK]
      rw [Subgroup.commutator_le]
      intro a ha b hb
      refine (mk_eq_one_iff (⁅(⟨a, ha⟩ : ↥K), ⟨b, hb⟩⁆ : ↥K)).mp ?_
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hz : (QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨a, ha⟩) ∈ Subgroup.center _ := by
        rw [h]
        exact Subgroup.mem_top _
      exact ((Subgroup.mem_center_iff.mp hz) _).symm
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K))
    apply hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [(mk_eq_one_iff a).mpr (hle a.2), (mk_eq_one_iff b).mpr (hle b.2)]

theorem inf_sup_pCoreOf_eq {K K' O X : Subgroup G}
    (hc : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hKX : K ≤ X) (hK'X : K' ≤ X)
    (hOX : O ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K)
    (hinf : K ⊓ O = pCoreOf 2 K) : K ⊓ (K' ⊔ O) = pCoreOf 2 K := by
  refine le_antisymm (le_pCoreOf_of_commutator_le hc inf_le_left ?_)
    (le_inf (Subgroup.map_subtype_le _) (hinf ▸ inf_le_right.trans le_sup_right))
  have hKO' : ⁅K, O⁆ ≤ pCoreOf 2 K := by
    rw [← hinf]
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hOX.trans hXK)) ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hKO
  calc ⁅K ⊓ (K' ⊔ O), K⁆ ≤ ⁅K' ⊔ O, K⁆ := Subgroup.commutator_mono inf_le_right le_rfl
    _ = ⁅K, K' ⊔ O⁆ := Subgroup.commutator_comm _ _
    _ = ⁅K, K'⁆ ⊔ ⁅K, O⁆ := commutator_sup_left_of_le hKX hK'X hOX hXK
    _ ≤ pCoreOf 2 K := sup_le hcomm hKO'

variable [Finite G] {T L I : Subgroup G}

theorem isSimpleGroup_conjugate (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    IsSimpleGroup (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) := by
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  rcases Vol2Native.lemma_1_2_1_three hK h37 h38 (pCoreOf_fsuM_ne_bot hyp.fsu.faithful)
      (conjugate_mem_cComp_fsuM hyp.fsu.maximal.1 (le_fsuM T L ht)) with hnorm | ⟨-, htypes⟩
  · exfalso
    have hN := (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((conjugate_le_fsuL0 ht).trans (fsuL0_le_fsuM T L))).mp hnorm
    have h1 : CFSG.conjugate (CFSG.conjugate L t) t = CFSG.conjugate L t :=
      conjugate_eq_self_iff.mpr (hN (le_fsuM T L ht))
    rw [conjugate_conjugate, conjugate_eq_self_iff.mpr (mul_self_mem_normalizer h37 h38 hyp ht htn)]
      at h1
    exact ne_conjugate htn h1
  · exact Vol2Native.L122A.isSimpleGroup_of_a38Types htypes

theorem center_quot_eq_bot
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
  center_eq_bot_of_perfect (perfect_L hyp.fsu.maximal.1)
    (isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.faithful hyp.not_normal)

theorem center_quot_conjugate_eq_bot (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    Subgroup.center (↥(CFSG.conjugate L t) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate L t)) = ⊥ :=
  center_eq_bot_of_perfect
    (perfect_of_mem_cComp (conjugate_mem_cComp_fsuM hyp.fsu.maximal.1 (le_fsuM T L ht)))
    (isSimpleGroup_conjugate h37 h38 hyp ht htn)

theorem inf_sup_pCoreOf_fsuL0 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    L ⊓ (CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L)) = pCoreOf 2 L :=
  inf_sup_pCoreOf_eq (center_quot_eq_bot h37 h38 hyp) (le_fsuL0 T L) (conjugate_le_fsuL0 ht)
    (Subgroup.map_subtype_le _) (fsuL0_le_normalizer hyp.fsu.maximal.1)
    (fun _ hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_fsuL0 T L hx))
    ((commutator_conjugate_le h37 hyp ht htn).trans inf_le_left)
    (inf_pCoreOf_fsuL0 hyp.fsu.maximal.1)

theorem conjugate_inf_sup_pCoreOf_fsuL0
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    CFSG.conjugate L t ⊓ (L ⊔ pCoreOf 2 (fsuL0 T L)) = pCoreOf 2 (CFSG.conjugate L t) :=
  inf_sup_pCoreOf_eq (center_quot_conjugate_eq_bot h37 h38 hyp ht htn) (conjugate_le_fsuL0 ht)
    (le_fsuL0 T L) (Subgroup.map_subtype_le _)
    (fsuL0_le_normalizer_conjugate hyp.fsu.maximal.1 (le_fsuM T L ht))
    (fun _ hx => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (conjugate_le_fsuL0 ht hx))
    ((Subgroup.commutator_comm _ _).le.trans ((commutator_conjugate_le h37 hyp ht htn).trans
      inf_le_right))
    (conjugate_inf_pCoreOf_fsuL0 hyp.fsu.maximal.1 ht)

end CFSG.Quasithin.Vol2.Ch10.SecA

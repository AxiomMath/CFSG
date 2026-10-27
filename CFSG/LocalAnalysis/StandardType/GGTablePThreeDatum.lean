module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDefs
import CFSG.LocalAnalysis.StandardType.GGD4OddCentLLocal
import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel
import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Datum

variable {G : Type} [Group G] [Finite G]

theorem exists_closure_pair_of_stdSub {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J) :
    ∃ y ∈ B, D = Subgroup.closure {x, y} := by
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hpre : LargeEvenStdSubPre 3 B x L D J := hDJ.1
  have hxB : x ∈ B := hS.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hzxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
  have hzxD : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
  have hne : Subgroup.zpowers x ≠ D := by
    intro h
    rw [h, hpre.2.2.1] at hzxcard
    norm_num at hzxcard
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra h
    simp only [not_exists, not_and] at h
    exact hne (le_antisymm hzxD fun z hz => Classical.not_not.mp (h z hz))
  refine ⟨y, hpre.1 hyD, ?_⟩
  have hclD : Subgroup.closure ({x, y} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxD
    · exact hyD
  have hzxcl : Subgroup.zpowers x ≤ Subgroup.closure ({x, y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hnecl : Subgroup.zpowers x ≠ Subgroup.closure ({x, y} : Set G) := by
    intro h
    exact hyz (h ▸ Subgroup.subset_closure (by simp))
  have hcardlt : Nat.card (Subgroup.zpowers x) <
      Nat.card (Subgroup.closure ({x, y} : Set G)) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hzxcl hnecl)
  have hdvd : Nat.card (Subgroup.closure ({x, y} : Set G)) ∣ 3 ^ 2 := by
    have h := Subgroup.card_dvd_of_le hclD
    rwa [hpre.2.2.1] at h
  have hcard9 : Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 hdvd
    have hk21 : k = 2 := by
      have hk012 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk012 with rfl | rfl | rfl
      · rw [pow_zero] at hk
        rw [hk, hzxcard] at hcardlt
        norm_num at hcardlt
      · rw [pow_one] at hk
        rw [hk, hzxcard] at hcardlt
        norm_num at hcardlt
      · rfl
    rw [hk21] at hk
    norm_num at hk
    exact hk
  exact (Subgroup.eq_of_le_of_card_ge hclD (by rw [hcard9, hpre.2.2.1]; norm_num)).symm

private theorem isComponentOf_map_subtype_of_subgroupOf {H : Subgroup G} {Y Q : Subgroup ↥H}
    (h : IsComponentOf Q Y) :
    IsComponentOf (Q.map H.subtype) (Y.map H.subtype) := by
  obtain ⟨hQY, hsn, hq⟩ := h
  exact ⟨Subgroup.map_mono hQY, CFSG.Assembly.IsSubnormal.map H.subtype hsn,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective Q H.subtype H.subtype_injective).symm hq⟩

theorem ggTablePThree_datum {B : Subgroup G} {x y : G} {L D J : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G)) :
    GGTablePThreeDatum (ggAutsOf L B hNL) (L.normalizerMonoidHom ⟨y, hNL hyB⟩)
      (J.subgroupOf L) := by
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre 3 B x L D J := hDJ.1
  have hJL : J ≤ L := hpre.2.2.2.2.2.1.1.trans inf_le_left
  have hxB : x ∈ B := hS.2.1
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hyB
  have hlocal : GGAutLocal (ggAutsOf L B hNL) (L.normalizerMonoidHom ⟨y, hyN⟩)
      (J.subgroupOf L) := ggD4OddCent_lLocal hI hDJ hD hyB hNL
  have hkernel : ∀ a ∈ ggAutsOf L B hNL,
      (∀ j ∈ J.subgroupOf L, a j = j) →
        a ∈ Subgroup.zpowers (L.normalizerMonoidHom ⟨y, hyN⟩) := by
    intro a ha hfix
    obtain ⟨b, hbB, hba⟩ := (mem_ggAutsOf hNL).1 ha
    have hbcent : b ∈ Subgroup.centralizer (J : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjm : (⟨j, hJL hj⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.mpr hj
      have h1 : L.normalizerMonoidHom ⟨b, hNL hbB⟩ ⟨j, hJL hj⟩ = ⟨j, hJL hj⟩ := by
        rw [hba, hfix ⟨j, hJL hj⟩ hjm]
      have h2 : b * j * b⁻¹ = j := by
        have h2' := congrArg (fun t : ↥L => (t : G)) h1
        rw [normalizerMonoidHom_apply_coe] at h2'
        simpa using h2'
      have h3 : b * j = j * b := by
        calc b * j = (b * j * b⁻¹) * b := by group
          _ = j * b := by rw [h2]
      exact h3.symm
    have hbD : b ∈ D := by
      rw [hpre.2.2.2.2.2.2]
      exact ⟨hbB, hbcent⟩
    have hb_cl : b ∈ Subgroup.closure ({x, y} : Set G) := hD ▸ hbD
    have hxy : Commute x y :=
      congrArg Subtype.val (hS.1.1.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)
    obtain ⟨m, n, hbxy⟩ := exists_zpow_mul_of_mem_closure_pair_of_commute hxy hb_cl
    have hb_sub : (⟨b, hNL hbB⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨x, hNL hxB⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ m *
          (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ n := by
      apply Subtype.ext
      change b = x ^ m * y ^ n
      exact hbxy
    have hmap : L.normalizerMonoidHom ⟨b, hNL hbB⟩ =
        (L.normalizerMonoidHom ⟨x, hNL hxB⟩) ^ m *
          (L.normalizerMonoidHom ⟨y, hyN⟩) ^ n := by
      rw [hb_sub, map_mul, map_zpow, map_zpow]
    have hxcent : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mp (hS.2.2.2.1.1 hl)
    have hxone : L.normalizerMonoidHom ⟨x, hNL hxB⟩ = 1 :=
      (normalizerMonoidHom_eq_one_iff (hNL hxB)).2 hxcent
    have ha_eq : a = (L.normalizerMonoidHom ⟨y, hyN⟩) ^ n := by
      rw [← hba, hmap, hxone]
      simp
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, ha_eq.symm⟩
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hS.2.2.2.1.1]
  have huniq : ∀ Q : Subgroup ↥L,
      IsComponentOf Q (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hyN⟩)) →
        Q = J.subgroupOf L := by
    intro Q hQ
    have hfixeq := ggAutFixedSubgroup_normalizerMonoidHom hyN
    have hQ' : IsComponentOf (Subgroup.map L.subtype Q)
        (Subgroup.map L.subtype (ggAutFixedSubgroup (L.normalizerMonoidHom ⟨y, hyN⟩))) :=
      isComponentOf_map_subtype_of_subgroupOf hQ
    rw [hfixeq, Subgroup.map_subgroupOf_eq_of_le
      (inf_le_left : L ⊓ Subgroup.centralizer ({y} : Set G) ≤ L), ← hLD] at hQ'
    have hle : Q.map L.subtype ≤ J := by
      rw [hpre.2.2.2.2.1]
      exact le_largeEvenLayer hQ'
    have hJeq : Q.map L.subtype = J :=
      (CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hQ'.2.2
        hpre.2.2.2.2.2.1 hQ' hle le_rfl).symm
    have hQcomap : Q = (Q.map L.subtype).comap L.subtype :=
      (Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q).symm
    rw [hQcomap, hJeq]
    exact Subgroup.comap_subtype J L
  have hcard : 3 ^ 3 ≤ Nat.card ↥(ggAutsOf L B hNL) := by
    rw [ggD4OddCent_card_lAuts hI hNL]
    have hm : 4 ≤ LargeEvenTwoLocalRank 3 G := hI.2.2.2.2.2.1.2.2.2
    exact Nat.pow_le_pow_of_le (by norm_num) (by omega)
  have hmark : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      True ∧ LargeEvenSplit 3 lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I :=
    ggD4OddCent_lMarking hst hNL (fun _ => True) (by
      intro P hP
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ => trivial⟩) hP)
  have hfinal : LargeEvenMarking ↥L fun lab _ _ I _ θ =>
      LargeEvenSplit 3 lab ∧ GGInducedInn (ggAutsOf L B hNL) θ I :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hmark
  exact ⟨⟨hlocal, hkernel⟩, huniq, hcard, hfinal⟩

theorem exists_ggTablePThree_datum {B : Subgroup G} {x : G} {L D J : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J) :
    ∃ (hNL : B ≤ Subgroup.normalizer (L : Set G)) (δ : MulAut ↥L),
      GGTablePThreeDatum (ggAutsOf L B hNL) δ (J.subgroupOf L) := by
  obtain ⟨y, hyB, hD⟩ := exists_closure_pair_of_stdSub hI hDJ
  have hNL : B ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_largeEvenStandardType hI.2.2.2.2.2.2.2
  exact ⟨hNL, L.normalizerMonoidHom ⟨y, hNL hyB⟩,
    ggTablePThree_datum hI hDJ hD hyB hNL⟩

end Datum

namespace GGTablePThree

variable {G : Type*} [Group G]

theorem largeEvenMarking_subgroupOf {L J : Subgroup G} (hJL : J ≤ L)
    {S : LargeEvenLabel → Prop} (h : LargeEvenMarking ↥J fun lab _ _ _ _ _ => S lab) :
    LargeEvenMarking ↥(J.subgroupOf L) fun lab _ _ _ _ _ => S lab := by
  exact largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) h

theorem center_subgroupOf_eq_bot_iff {L J : Subgroup G} (hJL : J ≤ L) :
    Subgroup.center ↥(J.subgroupOf L) = ⊥ ↔ Subgroup.center ↥J = ⊥ := by
  constructor
  · intro h
    exact center_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm h
  · intro h
    exact center_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) h

end GGTablePThree

end CFSG.StandardType

module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1Ord
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114NotF
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourA7
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L34Orders J1Orders
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Setup

variable {T L : Subgroup G}

omit [Finite G] in
theorem isSubnormal_sup_of_le_normalizer (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsSubnormal L (L ⊔ T) :=
  IsSubnormal.step le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTL))
    (IsSubnormal.refl _)

theorem noncentralTwoChiefFactorsInO2_of_simple (hL : ⁅L, L⁆ = L) (hs : IsSimpleGroup (O2Q L))
    (hLf : quasithinIsFaithfulLocal T L) : NoncentralTwoChiefFactorsInO2 L := by
  rintro A B ⟨hOB, hBA, hAL, hLA, hLB, -, h2⟩
  exfalso
  by_cases hAeq : A = L
  · have hBL : B ≤ L := hBA.le.trans hAL
    have hBn : (B.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBL).mpr hLB
    have h2' : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ B := fun x hx => h2 x (by rw [hAeq]; exact hx)
    exact hBA.ne ((hLf.2.1 B hBL hBn h2').trans hAeq.symm)
  · have hA := le_pCoreOf_of_normal_of_ne hL hs hAL hLA hAeq
    exact (not_le_of_gt hBA) (hA.trans hOB)

theorem commutator_reducedAggregate_ne_bot_of_simple (hL : ⁅L, L⁆ = L)
    (hs : IsSimpleGroup (O2Q L)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLf : quasithinIsFaithfulLocal T L) : ⁅reducedAggregate (L ⊔ T), L⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hXf⟩ := isFaithfulLocal_iff_isXf.mp hLf
  obtain ⟨W, hW, hWL⟩ := A4.exists_isTwoReducedIn_of_isXf hXf.1
    (isSubnormal_sup_of_le_normalizer hTL) (noncentralTwoChiefFactorsInO2_of_simple hL hs hLf)
    hXf.2
  intro hb
  apply hWL
  rw [eq_bot_iff, ← hb]
  exact Subgroup.commutator_mono (A7.le_reducedAggregate_of_isTwoReducedIn hW) le_rfl

theorem exists_fsu_of_faithful (h323 : Stmt3_2_3) (hsG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hq : QuasithinUnique.quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T L)
    (hLf : quasithinIsFaithfulLocal T L) (hL : ⁅L, L⁆ = L) (hs : IsSimpleGroup (O2Q L))
    (hqs : CFSG.IsQuasisimple (O2Q L)) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ V₀ : Subgroup G, IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V₀ ∧ FSU G T L V₀ := by
  obtain ⟨-, -, hI⟩ := h323 G T L hsG hnab hq hT hmax hLf hqs
  rw [Vol2.Ch11.SecA.conjClosure_eq_of_le_normalizer hTL] at hI
  obtain ⟨I, hIb⟩ : ∃ I : Subgroup G, IsIrrPlusBase L (reducedAggregate (L ⊔ T)) I :=
    exists_irrPlusBase hLf.2.1
      (fun x hx => by rw [← pow_two]; exact (reducedAggregate_props _).1 x hx)
      (le_sup_left.trans (Lem3228.le_normalizer_reducedAggregate' _))
      (commutator_reducedAggregate_ne_bot_of_simple hL hs hTL hLf)
  obtain ⟨V₀, hV₀, -, hfsu⟩ := hI I hIb
  exact ⟨V₀, hV₀, hfsu⟩

theorem pCoreOf_le_centralizer_of_le_reducedAggregate (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {W : Subgroup G} (hW : W ≤ reducedAggregate (L ⊔ T)) :
    pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (A4.pCoreOf_le_of_subnormal 2 (isSubnormal_sup_of_le_normalizer hTL)).trans
    ((reducedAggregate_props _).2.2.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW)))

end Setup

theorem card_autOn_j1 {T L W : Subgroup G}
    (hJ : IsSporadic .J1 (O2Q L)) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hW : W ≤ reducedAggregate (L ⊔ T))
    (hne : ¬ L ≤ Subgroup.centralizer (W : Set G)) : Nat.card ↥(autOn L W) = 175560 := by
  obtain ⟨f⟩ := hJ
  have hs : IsSimpleGroup (O2Q L) :=
    (MulEquiv.isSimpleGroup_congr f).mpr CFSG.Sporadic.J1.isSimpleGroup_J1
  obtain ⟨e⟩ := nonempty_autOn_equiv_O2Q hs hLW
    (pCoreOf_le_centralizer_of_le_reducedAggregate hTL hW) hne
  rw [Nat.card_congr (e.trans f).toEquiv]
  exact CFSG.Sporadic.J1.card_J1

theorem false_of_j1_of_faithful
    (h323 : Stmt3_2_3) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C)
    {T L : Subgroup G} (hsG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hq : QuasithinUnique.quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hmax : quasithinIsMaximalLocal T L) (hLf : quasithinIsFaithfulLocal T L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hJ : IsSporadic .J1 (O2Q L)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : ⁅L, L⁆ = L := hmax.1.2.1.2.1
  have hs : IsSimpleGroup (O2Q L) := by
    obtain ⟨f⟩ := hJ
    exact (MulEquiv.isSimpleGroup_congr f).mpr CFSG.Sporadic.J1.isSimpleGroup_J1
  have hqs : CFSG.IsQuasisimple (O2Q L) := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
    have : Group.IsPerfect (O2Q L) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact isQuasisimple_of_isSimpleGroup_of_isPerfect
  obtain ⟨V₀, hV₀, hfsu⟩ := exists_fsu_of_faithful h323 hsG hnab hq hT hmax hLf hL hs hqs hTL
  have hLL : L = conjClosure L T := (Vol2.Ch11.SecA.conjClosure_eq_of_le_normalizer hTL).symm
  have hR : V₀ ≤ reducedAggregate (L ⊔ T) := hV₀.1
  have hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hne₀ : ¬ L ≤ Subgroup.centralizer (V₀ : Set G) := not_le_centralizer_of_isIrrPlusIn hV₀
  have hLV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_of_le hTL hLV₀
  have hVR : conjClosure V₀ T ≤ reducedAggregate (L ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hR
  have hneV : ¬ L ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := card_autOn_j1 hJ hTL hLV hVR hneV
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hLL
  have hVeq : V₀ = conjClosure V₀ T := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlist, -⟩
    · exact h1
    · exact h1
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact card_SL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 6 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL4_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL5_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 7 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
  have hcard := card_autOn_j1 hJ hTL hLV₀ hR hne₀
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  obtain ⟨k, hk⟩ := exists_card_autOn_sup hLV₀ hTV₀ hTL hT.1
  rw [hcard] at hk
  have hc : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props _).2.1 _ (hR a.2) _ (hR b.2))⟩⟩
  obtain ⟨hk1, hk2, hk3, hk4⟩ := mul_two_pow_ne_j1 k
  by_cases hFF : IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn L V₀ : Set (MulAut ↥V₀))))
  ·
    obtain ⟨_, hcases⟩ := h328 G T L V₀ hfsu hLL hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, hl, -⟩ | ⟨⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨he, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_two_pow_ne_j1 _ h1.symm
    · exact card_SL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_SL3_ne_j1 (F := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)
        ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_statedSp_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_G2_derived_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 5 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_alt 7 (by norm_num), show Nat.factorial 7 / 2 = 2520 by decide] at h1
      exact hk1 h1
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(autOn L V₀))
      rw [hcard, hZ, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · rcases hm with rfl | rfl
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL4_two] at h1
        exact hk2 h1
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL5_two] at h1
        exact hk3 h1
    · obtain ⟨e⟩ := he
      have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_SL4_two] at h1
      norm_num at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_SL5_two] at h1
      exact hk3 h1
  ·
    obtain ⟨_, hcases⟩ := h329 G T L V₀ hfsu hLL hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, -, hl, -⟩ | ⟨m, hSU, -⟩ | ⟨f, hSz, -⟩ |
      ⟨m, F, _, _, _, hm, hF, hl, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, -, ⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_two_pow_ne_j1 _ h1.symm
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSU3.exists_equiv hSU
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hF] at this
        norm_num at this
      have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := m * 2) (by omega)
        (by rw [hF, pow_mul])
      exact card_statedSU_ne_j1 hF ((Nat.card_congr e.toEquiv).trans hcard)
    · obtain ⟨a, F, _, _, ha, hf, hF, ⟨e⟩⟩ := BinaryNaturalSz.exists_equiv hSz
      have hSzM : SuzukiModel ↥(autOn L V₀) 2 f := ⟨rfl, a, ha, F, inferInstance,
        inferInstance, hf, hF, ⟨e.symm⟩⟩
      obtain ⟨-, a', -, hf', hc'⟩ := CFSG.GH74.card_of_suzukiModel hSzM
      rw [hcard] at hc'
      apply not_three_dvd_ordSuzuki (f := f) ⟨a', hf'⟩
      rw [← hc']
      norm_num
    · rcases hl with hl | he
      · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
        rw [hcard] at h1
        exact ordA_two_two_pow_ne_j1 _ h1.symm
      · obtain ⟨e⟩ := he
        exact card_statedSL3_ne_j1 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, CFSG.ComponentClassification.M12Cover.card_mulAut] at h1
      exact hk4 h1
    · have h1 := Subgroup.card_quotient_dvd_card (Subgroup.center ↥(autOn L V₀))
      rw [Nat.card_congr e.toEquiv, hcard, CFSG.Sporadic.Mathieu.card_M22] at h1
      norm_num at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hcard, CFSG.Sporadic.Mathieu.card_M22] at h1
      norm_num at h1
    · have h23 := twentyThree_dvd_card_M23
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23
    · have h23 := twentyThree_dvd_card_M24
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23

end CFSG.Quasithin.H13

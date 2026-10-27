module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4O
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114NotF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L34Orders Sec1214Orders
open scoped IsMulCommutative

namespace Sec1214

variable {G : Type} [Group G] [Finite G] {T K : Subgroup G}

omit [Finite G] in
theorem le_pCoreOf_of_simple (hs : IsSimpleGroup (O2Q K))
    (hO2 : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal →
      (∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = K)
    {P : Subgroup G} (hPK : P ≤ K) (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hnot : ¬ K ≤ P) : P ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPn : (P.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
  rcases hs.eq_bot_or_eq_top_of_normal ((P.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    intro x hx
    have hxN : (⟨x, hPK hx⟩ : ↥K) ∈ P.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have hxP : (⟨x, hPK hx⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
      exact hb hxN
    exact ⟨_, hxP, rfl⟩
  · refine absurd (le_of_eq (hO2 P hPK hPn fun x hx => ?_).symm) hnot
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨x, hx⟩ ∈
        (P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
      rw [ht]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := hmem
    have ho : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K), MonoidHom.mem_ker, map_mul, map_inv, hcx,
        inv_mul_cancel]
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨_, ho⟩ : ↥(CFSG.pCore 2 ↥K))
    have hk' : (c⁻¹ * ⟨x, hx⟩) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hc1 : QuotientGroup.mk' (P.subgroupOf K) c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    have h1 : QuotientGroup.mk' (P.subgroupOf K) (⟨x, hx⟩ ^ 2 ^ k) = 1 := by
      rw [show (⟨x, hx⟩ : ↥K) = c * (c⁻¹ * ⟨x, hx⟩) by group, map_pow, map_mul, hc1, one_mul,
        ← map_pow, hk', map_one]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    simpa using h1

omit [Finite G] in
theorem noncentralTwoChiefFactorsInO2_of_simple (hs : IsSimpleGroup (O2Q K))
    (hKf : quasithinIsFaithfulLocal T K) : NoncentralTwoChiefFactorsInO2 K := by
  rintro A B ⟨hOB, hBA, hAK, hKA, hKB, -, h2⟩
  exfalso
  by_cases hAeq : A = K
  · have hBK : B ≤ K := hBA.le.trans hAK
    have hBn : (B.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBK).mpr hKB
    have h2' : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ B := fun x hx => h2 x (by rw [hAeq]; exact hx)
    exact hBA.ne ((hKf.2.1 B hBK hBn h2').trans hAeq.symm)
  · have hA := le_pCoreOf_of_simple hs hKf.2.1 hAK hKA fun hle => hAeq (le_antisymm hAK hle)
    exact (not_le_of_gt hBA) (hA.trans hOB)

omit [Finite G] in
theorem isSubnormal_sup_of_le_normalizer (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    IsSubnormal K (K ⊔ T) :=
  IsSubnormal.step le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTK))
    (IsSubnormal.refl _)

theorem commutator_reducedAggregate_ne_bot_of_simple (hs : IsSimpleGroup (O2Q K))
    (hKf : quasithinIsFaithfulLocal T K) (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ⁅reducedAggregate (K ⊔ T), K⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hXf⟩ := isFaithfulLocal_iff_isXf.mp hKf
  obtain ⟨W, hW, hWK⟩ := A4.exists_isTwoReducedIn_of_isXf hXf.1
    (isSubnormal_sup_of_le_normalizer hTK) (noncentralTwoChiefFactorsInO2_of_simple hs hKf) hXf.2
  intro hb
  apply hWK
  rw [eq_bot_iff, ← hb]
  exact Subgroup.commutator_mono (A7.le_reducedAggregate_of_isTwoReducedIn hW) le_rfl

omit [Finite G] in
theorem conjClosure_eq_of_le_normalizer' (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    conjClosure K T = K :=
  le_antisymm (conjClosure_le fun _t ht k hk =>
    (Subgroup.mem_normalizer_iff.mp (hTK ht) k).mp hk) (le_conjClosure K T)

theorem exists_fsu_of_simple (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    (hqtke : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hmax : quasithinIsMaximalLocal T K) (hKf : quasithinIsFaithfulLocal T K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hs : IsSimpleGroup (O2Q K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (h323 : Stmt3_2_3) :
    ∃ V₀ : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T V₀ ∧ FSU G T K V₀ := by
  obtain ⟨-, -, hI⟩ := h323 G T K hG hna hqtke hT hmax hKf hq
  rw [conjClosure_eq_of_le_normalizer' hTK] at hI
  obtain ⟨I, hIb⟩ := exists_irrPlusBase hKf.2.1
    (fun x hx => by rw [← pow_two]; exact (reducedAggregate_props _).1 x hx)
    (le_sup_left.trans (Lem3228.le_normalizer_reducedAggregate' _))
    (commutator_reducedAggregate_ne_bot_of_simple hs hKf hTK)
  obtain ⟨V₀, hV₀, -, hfsu⟩ := hI I hIb
  exact ⟨V₀, hV₀, hfsu⟩

theorem pCoreOf_le_centralizer_of_le (hTK : T ≤ Subgroup.normalizer (K : Set G)) {W : Subgroup G}
    (hW : W ≤ reducedAggregate (K ⊔ T)) : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (A4.pCoreOf_le_of_subnormal 2 (isSubnormal_sup_of_le_normalizer hTK)).trans
    ((reducedAggregate_props _).2.2.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hW)))

theorem card_autOn_eq_of_simple (hs : IsSimpleGroup (O2Q K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {W : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) (hW : W ≤ reducedAggregate (K ⊔ T))
    (hne : ¬ K ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn K W) = Nat.card (O2Q K) := by
  obtain ⟨e⟩ := nonempty_autOn_equiv_O2Q hs hKW (pCoreOf_le_centralizer_of_le hTK hW) hne
  exact Nat.card_congr e.toEquiv

theorem false_of_orderFacts
    (hG : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) (hqtke : quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hmax : quasithinIsMaximalLocal T K)
    (hKf : quasithinIsFaithfulLocal T K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hs : IsSimpleGroup (O2Q K)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (h323 : Stmt3_2_3) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C) {N : ℕ}
    (hcardQ : Nat.card (O2Q K) = N) (hN : OrderFacts N) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, hV₀, hfsu⟩ := exists_fsu_of_simple hG hna hqtke hT hmax hKf hq hs hTK h323
  have hKK : K = conjClosure K T := (conjClosure_eq_of_le_normalizer' hTK).symm
  have hR : V₀ ≤ reducedAggregate (K ⊔ T) := hV₀.1
  have hKV₀ : K ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hne₀ : ¬ K ≤ Subgroup.centralizer (V₀ : Set G) := not_le_centralizer_of_isIrrPlusIn hV₀
  have hKV : K ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    le_normalizer_conjClosure_of_le hTK hKV₀
  have hVR : conjClosure V₀ T ≤ reducedAggregate (K ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hR
  have hneV : ¬ K ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV : Nat.card ↥(autOn K (conjClosure V₀ T)) = N :=
    (card_autOn_eq_of_simple hs hTK hKV hVR hneV).trans hcardQ
  obtain ⟨-, -, hcases⟩ := h325 G T K V₀ hfsu hKK
  have hVeq : V₀ = conjClosure V₀ T := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlist, -⟩
    · exact h1
    · exact h1
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact hN.card_SL3_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact hN.card_statedSp_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 6 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
        exact hN.small.2.2.1 h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL4_two] at h1
        exact hN.small.2.2.2.2.2.1 h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL5_two] at h1
        exact hN.small.2.2.2.2.2.2 h1.symm
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 7 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
        exact hN.small.2.2.2.2.1 h1.symm
  have hcard : Nat.card ↥(autOn K V₀) = N :=
    (card_autOn_eq_of_simple hs hTK hKV₀ hR hne₀).trans hcardQ
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  obtain ⟨k, hk⟩ := exists_card_autOn_sup hKV₀ hTV₀ hTK hT.1
  rw [hcard] at hk
  have hc : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props _).2.1 _ (hR a.2) _ (hR b.2))⟩⟩
  by_cases hFF : IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn K V₀ : Set (MulAut ↥V₀))))
  ·
    obtain ⟨_, hcases⟩ := h328 G T K V₀ hfsu hKK hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, hl, -⟩ | ⟨⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · exact hN.card_PSL2_ne hl hcard
    · exact hN.card_SL3_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact hN.card_SL3_ne (F := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)
        ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact hN.card_statedSp_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact hN.card_G2_derived_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 5 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      exact hN.small.1 h1.symm
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      exact hN.small.2.2.2.2.1 h1.symm
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      exact hN.small.2.2.1 h1.symm
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_alt 7 (by norm_num), show Nat.factorial 7 / 2 = 2520 by decide] at h1
      exact (hN.pow k).1 h1
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(autOn K V₀))
      rw [hcard, hZ, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
      exact hN.small.2.2.2.1 h1
    · have h1 := Nat.card_congr e.toEquiv
      rcases hm with rfl | rfl
      · rw [hk, card_SL4_two] at h1
        exact (hN.pow k).2.1 h1
      · rw [hk, card_SL5_two] at h1
        exact (hN.pow k).2.2 h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_SL4_two] at h1
      exact hN.small.2.2.2.2.2.1 h1.symm
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_SL5_two] at h1
      exact (hN.pow k).2.2 h1
  ·
    obtain ⟨_, hcases⟩ := h329 G T K V₀ hfsu hKK hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, -, hl, -⟩ | ⟨m, hSU, -⟩ | ⟨f, hSz, -⟩ |
      ⟨m, F, _, _, _, -, hF, hl, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, -, ⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · exact hN.card_PSL2_ne hl hcard
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSU3.exists_equiv hSU
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hF] at this
        norm_num at this
      have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := m * 2) (by omega)
        (by rw [hF, pow_mul])
      exact hN.card_statedSU_ne hF ((Nat.card_congr e.toEquiv).trans hcard)
    · obtain ⟨a, F, _, _, ha, hf, hF, ⟨e⟩⟩ := BinaryNaturalSz.exists_equiv hSz
      have hSzM : SuzukiModel ↥(autOn K V₀) 2 f := ⟨rfl, a, ha, F, inferInstance,
        inferInstance, hf, hF, ⟨e.symm⟩⟩
      obtain ⟨-, a', -, hf', hc'⟩ := CFSG.GH74.card_of_suzukiModel hSzM
      rw [hcard] at hc'
      apply not_three_dvd_ordSuzuki (f := f) ⟨a', hf'⟩
      rw [← hc']
      exact hN.three
    · rcases hl with hl | he
      · exact hN.card_PSL3_ne hl hcard
      · obtain ⟨e⟩ := he
        exact hN.card_statedSL3_ne hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk] at h1
      exact hN.m12 k (h1 ▸ dvd_card_mulAut_M12)
    · have h1 := Subgroup.card_quotient_dvd_card (Subgroup.center ↥(autOn K V₀))
      rw [Nat.card_congr e.toEquiv, hcard, CFSG.Sporadic.Mathieu.card_M22] at h1
      exact hN.m22 h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [CFSG.Sporadic.Mathieu.card_M22] at h1
      exact hN.m22 (h1 ▸ dvd_refl _)
    · have h23 := twentyThree_dvd_card_M23
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      exact hN.m23 h23
    · have h23 := twentyThree_dvd_card_M24
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      exact hN.m23 h23

end Sec1214

end CFSG.Quasithin.H13

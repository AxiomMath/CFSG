module

public import CFSG.Quasithin.Vol2.Ch4Sec3InspC48
public import CFSG.Quasithin.Background.C48AsmLine
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4D

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.A4

namespace NoJ4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem c48Case6_of_cases {H R M L V K : Subgroup G}
    (hL : IsSporadic .M24 (ModO2 L) ∨ IsPSL 5 2 1 (ModO2 L))
    (hc : C48Case1 H R M L V K ∨ C48Case2 H R M L V K ∨ C48Case3 H R M L V K ∨
      C48Case4 H R M L V K ∨ C48Case5 H R M L V K ∨ C48Case6 H R M L V K ∨
      C48Case7 H R M L V K ∨ C48Case8 H R M L V K ∨ C48Case9 H R M L V K) :
    C48Case6 H R M L V K := by
  have hcard : Nat.card (ModO2 L) = 244823040 ∨ Nat.card (ModO2 L) = 9999360 := by
    rcases hL with h | h
    · left
      obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    · exact Or.inr (F420.card_of_l52 h)
  have key : ∀ N : ℕ, Nat.card (ModO2 L) = N → N ≠ 244823040 → N ≠ 9999360 → False := by
    intro N hN h1 h2
    rcases hcard with h | h <;> rw [hN] at h
    · exact h1 h
    · exact h2 h
  have halt6 : IsAltBlockType L 6 → False := by
    rintro ⟨-, α, hα, hker, -⟩
    refine key 360 ?_ (by norm_num) (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_of_alt' (by norm_num) (MulEquiv.refl _)]
    decide
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  ·
    exfalso
    obtain ⟨n, hPSL, -⟩ := h1
    have hc1 := C48.card_psl_two_two hPSL
    by_cases hn : 2 ≤ n
    · rcases hcard with h | h
      · exact card_psl_two_ne hn (by norm_num) (hc1.symm.trans h)
      · exact card_psl_two_ne hn (by norm_num) (hc1.symm.trans h)
    · interval_cases n <;> rcases hcard with h | h <;> rw [hc1] at h <;> norm_num at h
  ·
    exfalso
    obtain ⟨m, hm, hPSL, -⟩ := h2
    rcases hm with rfl | rfl
    · exact key 168 (card_of_l32 hPSL) (by norm_num) (by norm_num)
    · exact key 20160 (F420.card_of_l42 hPSL) (by norm_num) (by norm_num)
  · exact (halt6 h3.2).elim
  ·
    exfalso
    obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := h4.2
    refine key 2520 ?_ (by norm_num) (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_of_alt' (by norm_num) (MulEquiv.refl _)]
    decide
  ·
    exfalso
    obtain ⟨-, ⟨-, hc, ⟨e⟩⟩, -⟩ := h5.2
    refine key 1080 ?_ (by norm_num) (by norm_num)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (ModO2 L)), hc,
      Nat.card_congr e.toEquiv, card_of_alt' (by norm_num) (MulEquiv.refl _)]
    decide
  · exact h6
  ·
    exact (key 6048 (F420.card_of_u33 h7.2.2.1) (by norm_num) (by norm_num)).elim
  · exact (halt6 h8.2).elim
  ·
    exfalso
    obtain ⟨-, α, hα, hker, -⟩ := h9.2.1
    refine key 168 ?_ (by norm_num) (by norm_num)
    rw [card_modO2_of_surjective α hα hker, card_statedSL_three_two]

theorem pCoreOf_centralizer_ne_bot {r : G} (hr1 : r ≠ 1) (hr2 : r * r = 1) :
    pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hrH₀ : r ∈ Subgroup.centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZ : Subgroup.zpowers r ≤ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) := by
    refine le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr hrH₀) ?_ ?_
    · intro h hh
      refine Subgroup.mem_normalizer_fintype fun y hy' => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      have hhr : h * r * h⁻¹ = r := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
      rw [← conj_zpow, hhr]
      exact Subgroup.zpow_mem_zpowers r k
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  intro h
  apply hr1
  have := hZ (Subgroup.mem_zpowers r)
  rwa [h, Subgroup.mem_bot] at this

theorem centralizer_le_normalizer
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h425 : Thm4_2_5) {T M L Mm I H K : Subgroup G} (hy : Hyp4_2_3 G T M L Mm I)
    (hIH : InM I H) (c : Conf4212 G T M L I H K)
    (h6 : C48Case6 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) {r : G} (hrK : r ∈ Subgroup.centralizer (K : Set G)) (hr1 : r ≠ 1) (hr2 : r * r = 1)
    (hrI : I ≤ Subgroup.centralizer ({r} : Set G)) :
    Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  set LH := perfectCore (L ⊓ H) with hLH
  obtain ⟨H', hH'⟩ := exists_inM_of_pCoreOf_ne_bot (pCoreOf_centralizer_ne_bot hr1 hr2)
  have hIH' : InM I H' := ⟨hH'.1, hrI.trans hH'.2⟩
  have hKr : K ≤ Subgroup.centralizer ({r} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrK k hk)
  have hKH' : K ≤ H' := hKr.trans hH'.2
  have hH'M : ¬ H' ≤ M := fun h => c.K_not_le (hKH'.trans h)
  have hne : H' ≠ M := fun h => hH'M (h ▸ le_rfl)
  obtain ⟨K', c'⟩ := hy.lemma_4_2_12_two h36 h37 h38 h39 (h48 G) (inH_of_inM hIH') hH'M
    (h425 G T M L Mm I H' hy hIH' hne)
  have hLHI : LH ≤ I := LH_le hy hIH c
  have hLHI' : perfectCore (L ⊓ H') ≤ I := LH_le hy hIH' c'
  have hLHL : LH ≤ L := (perfectCore_le (L ⊓ H)).trans inf_le_left
  have hLHL' : perfectCore (L ⊓ H') ≤ L := (perfectCore_le (L ⊓ H')).trans inf_le_left
  have hLeq : perfectCore (L ⊓ H') = LH := le_antisymm
    (le_perfectCore_of_perfect (le_inf hLHL' (hLHI'.trans hIH.2)) (perfectCore_perfect _))
    (le_perfectCore_of_perfect (le_inf hLHL (hLHI.trans hIH'.2)) (perfectCore_perfect _))
  have hL : IsSporadic .M24 (ModO2 (perfectCore (L ⊓ H'))) ∨
      IsPSL 5 2 1 (ModO2 (perfectCore (L ⊓ H'))) := by
    rw [hLeq]
    rcases h6.2.2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have h6' := c48Case6_of_cases hL c'.cases
  have hK'N : H' ≤ Subgroup.normalizer (K' : Set G) := normal hy hIH' c' h6'.1
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_isSporadic h6.1
  have hn : (K'.subgroupOf K).Normal := by
    constructor
    intro n hn k
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hK'N (hKH' k.2)) _).mp hn
  have hKK' : K ≤ K' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.subgroupOf K) with h | h
    · exfalso
      apply ne_bot_of_mem_cComp c.LH_mem
      refine le_bot_iff.mp fun y hy => ?_
      have hyK : y ∈ K := c.LH_le hy
      have hyK' : y ∈ K' := c'.LH_le (hLeq ▸ hy)
      have : (⟨y, hyK⟩ : ↥K) ∈ K'.subgroupOf K := Subgroup.mem_subgroupOf.mpr hyK'
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ K'.subgroupOf K := h ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hcard : Nat.card ↥K' ≤ Nat.card ↥K := by
    obtain ⟨e⟩ := h6.1
    obtain ⟨e'⟩ := h6'.1
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv]
  have hKe : K = K' := Subgroup.eq_of_le_of_card_ge hKK' hcard
  rw [hKe]
  exact hH'.2.trans hK'N

omit [Finite G] in
theorem inf_centralizer_le_normalizer {K : Subgroup G} {r x : G}
    (hN : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({r} : Set G) ≤
      Subgroup.normalizer (perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) :=
  fun _ hg => normalizer_le_normalizer_perfectCore _
    (mem_normalizer_inf (hN hg.2) (Subgroup.le_normalizer hg.1))

end NoJ4

end CFSG.Quasithin.H13.Ch4

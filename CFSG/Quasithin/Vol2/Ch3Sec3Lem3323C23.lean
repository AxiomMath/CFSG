module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C45
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Sec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace C23

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem top (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α) :
    NCAtMost L (pCoreOf 2 L) L 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ncAtMost_zero_top (fun B hOB hBL hLB => ?_) fun h2 => ?_
  · rcases Mod3323.le_or_sup_eq hq hα hBL hLB with h | h
    · exact Or.inl (le_antisymm h hOB)
    · right
      rw [← h, sup_eq_left.mpr hOB]
  ·
    have hp : IsPGroup 2 (↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H l =>
        obtain ⟨k, hk⟩ := h2 l l.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Lem3328.mem_pCore_iff]
        simpa using hk
    have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
      rw [← hα.2, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα.1).toEquiv,
        ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3
          (ZMod 2)).toEquiv]
      exact card_L3Γ
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    rw [h168] at hm
    have h7 : 7 ∣ 2 ^ m := hm ▸ (by norm_num : 7 ∣ 168)
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7)
    omega

theorem qData (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    c134Q (L ⊔ T) L ≤ pCoreOf 2 L ∧ ⁅pCoreOf 2 L, L⁆ ≤ c134Q (L ⊔ T) L ∧
      L ≤ Subgroup.normalizer (c134Q (L ⊔ T) L : Set G) ∧
      T ≤ Subgroup.normalizer (c134Q (L ⊔ T) L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hON : ∀ x ∈ L ⊔ T, x ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) hx
  have hNQ : ∀ x ∈ L ⊔ T, x ∈ Subgroup.normalizer (c134Q (L ⊔ T) L : Set G) := fun x hx =>
    mem_normalizer_commutator (hON x hx) (hLTN hx)
  have hQO : c134Q (L ⊔ T) L ≤ pCoreOf 2 (L ⊔ T) :=
    commutator_le_left_of_le_normalizer fun x hx => hON x (Subgroup.mem_sup_left hx)
  have hQL : c134Q (L ⊔ T) L ≤ L :=
    commutator_le_right_of_le_normalizer ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hLTN)
  have hOLT : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLTN)
  refine ⟨CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQL
    (fun x hx => hNQ x (Subgroup.mem_sup_left hx))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hQO), Subgroup.commutator_mono hOLT le_rfl,
    fun x hx => hNQ x (Subgroup.mem_sup_left hx), fun x hx => hNQ x (Subgroup.mem_sup_right hx)⟩

omit [Finite G] in
theorem mem_normalizer_centerOf {Q : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) :
    x ∈ Subgroup.normalizer (centerOf Q : Set G) :=
  ChiefCount.mem_normalizer_inf hx (B2F.normalizer_le_normalizer_centralizer Q hx)

theorem case2 (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hi : IsC134Case2 (L ⊔ T) T L) :
    (∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c) ∧ HasNoncentralTwoChief L 2 ∧
      ¬ HasNoncentralTwoChief L 4 := by
  obtain ⟨hQO, hOQ, -, hTQ⟩ := qData hTL
  set Q := c134Q (L ⊔ T) L with hQ
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hLQ, -, β, hβs, hβk, hβe⟩, -⟩ := hi
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  have hQL : Q ≤ L := hQO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let act : ↥L → Matrix (Fin 3) (Fin 3) F := fun l => ((α l : GL (Fin 3) F) : Matrix _ _ F)
  have hβe' : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i) :=
    fun a u v huv i => by simpa [moduleAct, act] using hβe a u v huv i
  have hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      act x = (g : Matrix (Fin 3) (Fin 3) F) := fun g => by
    obtain ⟨x, hx⟩ := Chief3323.surj_moduleAct false hα.1 g
    exact ⟨x, by simpa [moduleAct] using hx⟩
  have hLbot : L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => by simp
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  refine ⟨fun t ht => Mod3323.exists_eq_mul_of_natural hTL hT2 hα₂ hF hα (by norm_num) hLQ β
    hβs hβi hβe ht (hTQ ht), ?_, ?_⟩
  · exact Chief3323.hasNoncentralTwoChief_two
      (Sec3323.isTwoChiefFactor_fst β hF bot_le hQL hLQ hLbot act hsurj hβs hβk hβe')
      (Sec3323.isTwoChiefFactor_snd β hF hQL hLQ act hsurj hβs hβe') le_rfl
  · rw [Chief3323.hasNoncentralTwoChief_iff]
    have hW₁N := Sec3323.le_normalizer_sumFst β act hLQ hβe'
    have h1 : NCAtMost L ⊥ (Sec3323.sumFst β) 1 :=
      ncAtMost_of_relIndex_lt (by rw [Sec3323.relIndex_fst β hF hβs hβk]; norm_num)
    have h2 : NCAtMost L (Sec3323.sumFst β) Q 1 :=
      ncAtMost_of_relIndex_lt (by rw [Sec3323.relIndex_snd β hF hβs]; norm_num)
    have h3 : NCAtMost L Q (pCoreOf 2 L) 0 := ncAtMost_zero_of_commutator_le hOQ
    have h4 := top h.Lq hα₂
    have hOL : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    have h12 := h1.add h2 bot_le (Sec3323.sumFst_le β) hQL hW₁N
    have h123 := h12.add h3 bot_le hQO (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hLQ
    have h1234 := h123.add h4 bot_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl hOL
    exact h1234.mono (by norm_num)

theorem case3 (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hi : IsC134Case3 (L ⊔ T) T L) :
    (∀ t ∈ T, ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c) ∧ HasNoncentralTwoChief L 2 ∧
      ¬ HasNoncentralTwoChief L 4 := by
  obtain ⟨hQO, hOQ, -, hTQ⟩ := qData hTL
  set Q := c134Q (L ⊔ T) L with hQ
  obtain ⟨⟨n, F, _, _, α, hFc, hα, ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩,
    ⟨hLQ, hZQ, β, hβs, hβk, hβe⟩⟩, -⟩ := hi
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ hα)
  have hQL : Q ≤ L := hQO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  let act : ↥L → Matrix (Fin 3) (Fin 3) F := fun l => ((α l : GL (Fin 3) F) : Matrix _ _ F)
  let actd : ↥L → Matrix (Fin 3) (Fin 3) F := fun l => moduleAct true (α l : GL (Fin 3) F)
  have hβ₁e' : ∀ (a : ↥L) (u v : ↥(centerOf Q)), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β₁ v) i = (act a).mulVec (Multiplicative.toAdd (β₁ u) i) :=
    fun a u v huv i => by simpa [moduleAct, act] using hβ₁e a u v huv i
  have hsurj : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      act x = (g : Matrix (Fin 3) (Fin 3) F) := fun g => by
    obtain ⟨x, hx⟩ := Chief3323.surj_moduleAct false hα.1 g
    exact ⟨x, by simpa [moduleAct] using hx⟩
  have hsurjd : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : ↥L,
      actd x = (g : Matrix (Fin 3) (Fin 3) F) := Chief3323.surj_moduleAct true hα.1
  have hLbot : L ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x _ =>
    Subgroup.mem_normalizer_iff.mpr fun y => by simp
  have hZL : centerOf Q ≤ L := inf_le_left.trans hQL
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  refine ⟨fun t ht => Mod3323.exists_eq_mul_of_natural hTL hT2 hα₂ hF hα (by norm_num) hLZ β₁
    hβ₁s hβ₁i hβ₁e ht (mem_normalizer_centerOf (hTQ ht)), ?_, ?_⟩
  · exact Chief3323.hasNoncentralTwoChief_two
      (Sec3323.isTwoChiefFactor_one hF bot_le hZL hLZ hLbot act hsurj β₁ hβ₁s hβ₁k hβ₁e')
      (Sec3323.isTwoChiefFactor_fst β hF hZQ hQL hLQ hLZ actd hsurjd hβs hβk hβe) le_rfl
  · rw [Chief3323.hasNoncentralTwoChief_iff]
    have hW₁N := Sec3323.le_normalizer_sumFst β actd hLQ hβe
    have h1 : NCAtMost L ⊥ (centerOf Q) 1 :=
      ncAtMost_of_relIndex_lt (by rw [Sec3323.relIndex_one hF β₁ hβ₁s hβ₁k]; norm_num)
    have h2 : NCAtMost L (centerOf Q) (Sec3323.sumFst β) 1 :=
      ncAtMost_of_relIndex_lt (by rw [Sec3323.relIndex_fst β hF hβs hβk]; norm_num)
    have h3 : NCAtMost L (Sec3323.sumFst β) Q 1 :=
      ncAtMost_of_relIndex_lt (by rw [Sec3323.relIndex_snd β hF hβs]; norm_num)
    have h4 : NCAtMost L Q (pCoreOf 2 L) 0 := ncAtMost_zero_of_commutator_le hOQ
    have h5 := top h.Lq hα₂
    have hOL : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    have h12 := h1.add h2 bot_le (Sec3323.le_sumFst β hZQ hβk)
      ((Sec3323.sumFst_le β).trans hQL) hLZ
    have h123 := h12.add h3 bot_le (Sec3323.sumFst_le β) hQL hW₁N
    have h1234 := h123.add h4 bot_le hQO (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hLQ
    exact h1234.add h5 bot_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L) le_rfl hOL

end C23

end CFSG.Quasithin.H13

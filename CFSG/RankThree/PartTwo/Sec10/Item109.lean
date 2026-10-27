module

public import CFSG.RankThree.PartTwo.Sec4.Item420
public import CFSG.RankThree.PartTwo.Sec10.Item10Std

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section General

variable {X : Type*} [Group X]

theorem le_of_isSimpleGroup_quotient [Finite X] {N K : Subgroup X} [N.Normal] (hK : K.Normal)
    [IsSimpleGroup (X ⧸ N)] {q : X ⧸ N} (hq : ¬ orderOf q ∣ Nat.card K) : K ≤ N := by
  have hKn : (K.map (QuotientGroup.mk' N)).Normal := hK.map _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' N)) with hbot | htop
  · intro k hk
    have h1 : QuotientGroup.mk' N k ∈ K.map (QuotientGroup.mk' N) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have h1 : q ∈ K.map (QuotientGroup.mk' N) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨k, hk, rfl⟩ := h1
    exact hq ((orderOf_map_dvd _ k).trans (Subgroup.orderOf_dvd_natCard K hk))

theorem oddCore_eq_pPrimeCore_two' (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem odd_card_oddCore [Finite X] : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two']
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

end General

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem Sec10Std.eq_bot_of_inf_le_normalizer (h : Sec10Std G A c L a R) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hU : R ⊓ L ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  by_contra hU1
  have hE : R ⊓ L ∈ partTwoE G := ⟨h.isElemAbelian_inf, h.card_inf, U, hU1, hU2, hU⟩
  rw [h.partTwoE_eq h.card_eq] at hE
  have h1 := h.card_D
  rw [hE.2.1 (sec10D c R L) h.isElemAbelian_D h.inf_le_D, h.card_inf] at h1
  norm_num at h1

theorem Sec10Std.odd_card_theta (h : Sec10Std G A c L a R) :
    Odd (Nat.card (aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hYcard : Nat.card (thetaPreimage L ⊥) = Nat.card (aschbacherSolvableCore 3 L) := by
    rw [card_thetaPreimage, Subgroup.card_bot, mul_one]
  have hEY : R ⊓ L ≤ Subgroup.normalizer ((thetaPreimage L ⊥ : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_thetaPreimage_of_mem hx.2 (by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      simp [Subgroup.mem_bot])
  obtain ⟨T, -, hT1, hT2, hET⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2)
    (h.isPGroup_R.to_le inf_le_left) (by rw [hYcard]; exact not_three_dvd_card_theta L)
    (by rw [hYcard]; exact h2) hEY
  exact hT1 (h.eq_bot_of_inf_le_normalizer hT2 hET)

theorem Sec10Std.isSimpleGroup_quot (h : Sec10Std G A c L a R) :
    IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  have : IsSimpleGroup (GorensteinWalter.PSL2 (GaloisField 3 3)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 3 3 (by norm_num)]
      norm_num)
  exact e.isSimpleGroup

theorem Sec10Std.exists_orderOf_quot (h : Sec10Std G A c L a R) :
    (∃ q : L ⧸ aschbacherSolvableCore 3 L, orderOf q = 3) ∧
      ∃ q : L ⧸ aschbacherSolvableCore 3 L, orderOf q = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.exists_mulEquiv_psl2
  refine ⟨?_, ⟨e.symm (KFacts.psl2QI _), ?_⟩⟩
  · obtain ⟨⟨x, hxRL⟩, hx1⟩ : ∃ x : (R ⊓ L : Subgroup G), x ≠ 1 := by
      by_contra hall
      push Not at hall
      have : Nat.card (R ⊓ L : Subgroup G) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun u v => (hall u).trans (hall v).symm⟩, ⟨1⟩⟩
      rw [h.card_inf] at this
      norm_num at this
    have hx1' : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hx3 : x ^ 3 = 1 := h.isElemAbelian_inf.2 x hxRL
    set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
    set xb : L ⧸ aschbacherSolvableCore 3 L := π ⟨x, hxRL.2⟩ with hxb
    have hxb3 : xb ^ 3 = 1 := by
      rw [hxb, ← map_pow]
      have : (⟨x, hxRL.2⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hxb1 : xb ≠ 1 := by
      intro h1
      exact hx1' (h.eq_one_of_mem_R_of_mem_theta hxRL.1 (mem_theta_of_mk_eq_one h1))
    exact ⟨xb, orderOf_eq_prime hxb3 hxb1⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime KFacts.psl2QI_sq KFacts.psl2QI_ne_one

theorem Sec10Std.pPrimeCore_eq (h : Sec10Std G A c L a R) :
    CFSG.pPrimeCore 3 L = aschbacherSolvableCore 3 L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.isSimpleGroup_quot
  have := Sec4.aschbacherSolvableCore_characteristic L
  obtain ⟨⟨q, hq⟩, -⟩ := h.exists_orderOf_quot
  apply le_antisymm
  · refine le_of_isSimpleGroup_quotient (CFSG.pPrimeCore_normal (p := 3) (G := L)) (q := q) ?_
    rw [hq]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  · exact le_sSup ⟨inferInstance,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_card_theta L)⟩

theorem Sec10Std.oddCore_eq (h : Sec10Std G A c L a R) :
    CFSG.oddCore L = aschbacherSolvableCore 3 L := by
  have := h.isSimpleGroup_quot
  have := Sec4.aschbacherSolvableCore_characteristic L
  obtain ⟨-, ⟨q, hq⟩⟩ := h.exists_orderOf_quot
  apply le_antisymm
  · refine le_of_isSimpleGroup_quotient (inferInstance : (CFSG.oddCore L).Normal) (q := q) ?_
    rw [hq]
    exact fun h2 => (Nat.not_even_iff_odd.mpr odd_card_oddCore) (even_iff_two_dvd.mpr h2)
  · exact le_sSup ⟨inferInstance, h.odd_card_theta⟩

theorem Sec10Std.isSimpleGroup_L (h : Sec10Std G A c L a R) : IsSimpleGroup L := by
  have hLtop : L ≠ ⊤ := fun hL => h.c_not_mem_L (hL ▸ Subgroup.mem_top c)
  obtain ⟨e⟩ := h.iso
  exact Sec4.rank3II_4_20 L (h.toTheoremFourHyp.sectionFourHyp hLtop)
    (Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
    (by rw [h.pPrimeCore_eq, h.oddCore_eq])
    ⟨(QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_eq).trans e⟩

theorem Sec10Std.theta_eq_bot (h : Sec10Std G A c L a R) : aschbacherSolvableCore 3 L = ⊥ := by
  have := h.isSimpleGroup_L
  have := Sec4.aschbacherSolvableCore_characteristic L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (aschbacherSolvableCore 3 L) with hb | ht
  · exact hb
  · exfalso
    apply not_three_dvd_card_theta L
    rw [ht, Subgroup.card_top]
    exact (by norm_num : (3 : ℕ) ∣ 27).trans h.twentyseven_dvd_card

theorem Sec10Std.nonempty_mulEquiv (h : Sec10Std G A c L a R) :
    Nonempty (L ≃* projSL 2 (GaloisField 3 3)) := by
  obtain ⟨e⟩ := h.iso
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq h.theta_eq_bot.symm)).trans e⟩

theorem Sec10Std.normalizer_le_normalizer_L (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Ln := L.map (MulAut.conj n).toMonoidHom with hLn
  have hcn : Subgroup.centralizer ({(MulAut.conj n) c} : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    have hz : Subgroup.zpowers ((MulAut.conj n) c) = Subgroup.zpowers c := by
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      rw [MonoidHom.map_zpowers] at h1
      exact h1
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
      GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hz]
  have hLnc : Ln ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt
    rw [thetaComponentsAt_eq_thetaComponentsIn, hcn] at h1
    exact h1
  have hZ : Subgroup.center (Ln ⧸ aschbacherSolvableCore 3 Ln) = ⊥ := by
    obtain ⟨e⟩ := h.exists_mulEquiv_psl2
    exact KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot
      ((Sec13.thetaQuotEquiv (MulAut.conj n) L).symm.trans e)
      (GorensteinWalter.psl2_center_eq_bot _)
  have h3 : 3 ∣ Nat.card Ln := by
    rw [hLn, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact (by norm_num : (3 : ℕ) ∣ 27).trans h.twentyseven_dvd_card
  exact Sec11.not_three_dvd_of_mem_thetaComponentsAt_ne h45 h.toHyp91 hLnc hne hZ h3

end Std

end CFSG.RankThree.PartTwo.Sec10

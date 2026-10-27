module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Three
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

namespace QA24

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ] {X : Subgroup Γ}

theorem no_normal_three_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ N : Subgroup A, N.Normal → IsPGroup 3 N → N = ⊥) :
    ∀ N : Subgroup B, N.Normal → IsPGroup 3 N → N = ⊥ := by
  intro N hN hN3
  have hc : (N.comap e.toMonoidHom).Normal := hN.comap _
  have hcp : IsPGroup 3 (N.comap e.toMonoidHom) := hN3.comap_of_injective _ e.injective
  have h1 := h _ hc hcp
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N, h1,
    Subgroup.map_bot]

omit [Finite Γ] in
theorem not_three_dvd_card_oddCore (h36 : A36Strong X) (hnq : ¬ CFSG.IsQuasisimple ↥X) :
    ¬ 3 ∣ Nat.card ↥(CFSG.oddCore ↥X) := by
  obtain ⟨hconc, hcommon, -⟩ := h36
  have hcase : A36Case3 ↥X ∨ A36Case4 ↥X := by
    rcases hconc with ⟨hc, -⟩ | ⟨hc, -⟩ | h3 | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · exact Or.inl h3
    · exact Or.inr h4
  obtain ⟨hFO, -, -, -, -⟩ := hcommon
  rw [← hFO]
  rcases hcase with ⟨p, hp, hp3, -, ⟨e⟩, -⟩ | ⟨-, -, -, hprime⟩
  · have hcard : Nat.card ↥(CFSG.fittingSubgroup ↥X) = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (Fin 2 → ZMod p) ≃ (Fin 2 → ZMod p)), Nat.card_pi]
      have : Fact p.Prime := ⟨hp⟩
      simp
    rw [hcard]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  · intro h3
    have := (hprime 3 Nat.prime_three h3).1
    omega

theorem no_normal_three (h36 : A36Strong X) (hnq : ¬ CFSG.IsQuasisimple ↥X) (N : Subgroup ↥X)
    [N.Normal] (hN : IsPGroup 3 N) : N = ⊥ := by
  have h3 := not_three_dvd_card_oddCore h36 hnq
  have hodd : Odd (Nat.card N) := by
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hle : N ≤ CFSG.oddCore ↥X := le_sSup ⟨inferInstance, hodd⟩
  have hdvd : Nat.card N ∣ Nat.card ↥(CFSG.oddCore ↥X) := Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  have hcop : Nat.Coprime (3 ^ k) (Nat.card ↥(CFSG.oddCore ↥X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have h1 : Nat.card N = 1 := by
    rw [hk] at hdvd ⊢
    exact Nat.Coprime.eq_one_of_dvd hcop hdvd
  exact (Subgroup.card_eq_one).mp h1

omit [Finite Γ] in
theorem exists_sl2_hom (h36 : A36Strong X) (hnq : ¬ CFSG.IsQuasisimple ↥X) :
    ∃ (p : ℕ) (_ : p.Prime) (_ : 3 < p) (Φ : ↥X →* SL(2, ZMod p)),
      ∀ x : ↥X, (∃ k : ℕ, x ^ 3 ^ k = 1) → Φ x = 1 → x = 1 := by
  obtain ⟨p, hp, hp3, ⟨e⟩⟩ := A312.exists_isSL2_oddCore h36 hnq
  have h3 := not_three_dvd_card_oddCore h36 hnq
  refine ⟨p, hp, hp3, e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore ↥X)), ?_⟩
  rintro x ⟨k, hk⟩ hx
  have hx1 : (QuotientGroup.mk x : ↥X ⧸ CFSG.oddCore ↥X) = 1 := by
    have : e (QuotientGroup.mk x) = 1 := hx
    exact e.injective (this.trans (map_one e).symm)
  have hxmem : x ∈ CFSG.oddCore ↥X := (QuotientGroup.eq_one_iff x).mp hx1
  have hdvd : orderOf x ∣ Nat.card ↥(CFSG.oddCore ↥X) := by
    have := Subgroup.orderOf_dvd_natCard (CFSG.oddCore ↥X) hxmem
    simpa using this
  have hk' : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (3 ^ k) (Nat.card ↥(CFSG.oddCore ↥X)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hk' hcop)
    hdvd)

end Abstract

section Context

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

omit [Finite G] in
theorem K1_le_g0 (T M H K1 : Subgroup G) : K1 ≤ S1421.g0Of T M H K1 :=
  (le_sup_left : K1 ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M)).trans le_sup_left

theorem embLoc (h37 : A37ForSQTK) (c : S1421.Core3Ctx T M H K1 L M₁) :
    H13.EmbLoc G (S1421.sOf T K1) (S1421.g0Of T M H K1) K1 L := by
  have hB : K1 ∈ lFamily (S1421.sOf T K1) := c.st.notation_.cComp_mem
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple
    c.st.hyp.nonabelian c.pCore_ne
  refine ⟨c.st.hyp.simple, c.st.hyp.nonabelian, c.st.hyp.qtke, c.pCore_ne,
    S1421.isSylowTwoOf_g0 c.inM c.sylow, K1_le_g0 T M H K1, hB, inf_le_right,
    ⟨c.mem, c.lt_L.le, fun Y hY hK1Y => ?_⟩, c.lt_L⟩
  exact lemma_1_2_4_unique (h37 _ hQ) hB hY c.mem hK1Y c.lt_L.le

theorem strong_data (h36 : A36ForSQTK) (h37 : A37ForSQTK) (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ CFSG.IsQuasisimple ↥(modO2Image (S1421.g0Of T M H K1) L) ∧
      A36Strong (modO2Image (S1421.g0Of T M H K1) L) := by
  have l := embLoc h37 c
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot c.st.hyp.qtke c.st.hyp.simple
    c.st.hyp.nonabelian c.pCore_ne
  obtain ⟨eH⟩ := l.hat_equiv
  exact ⟨fun hq => hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv eH.symm hq),
    h36 _ hQ _ l.hatBar_cComp⟩

theorem nonquasi_data (hSL2 : A312SL2Fact) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ CFSG.IsQuasisimple ↥(modO2Image (S1421.g0Of T M H K1) L) ∧
      A36Strong (modO2Image (S1421.g0Of T M H K1) L) ∧
      A312Nonquasi (modO2Image (S1421.g0Of T M H K1) K1)
        (modO2Image (S1421.g0Of T M H K1) L) := by
  have l := embLoc h37 c
  obtain ⟨hnq', h36'⟩ := strong_data h36 h37 c hnq
  exact ⟨hnq', h36', A312.nonquasi_of_lFamily hSL2 l.sylowBar l.hatBar_cComp l.bar_lt.le
    l.bar_lFamily h36' hnq'⟩

theorem no_normal_three_L (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (c : S1421.Core3Ctx T M H K1 L M₁) (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∀ N : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L), N.Normal → IsPGroup 3 N → N = ⊥ := by
  have l := embLoc h37 c
  obtain ⟨hnq', h36'⟩ := strong_data h36 h37 c hnq
  obtain ⟨eH⟩ := l.hat_equiv
  intro N hN hN3
  exact no_normal_three_of_mulEquiv eH.symm
    (fun N' hN' hN'3 => @no_normal_three _ _ _ (modO2Image (S1421.g0Of T M H K1) L) h36' hnq' N'
      hN' hN'3) N hN hN3

theorem exists_sl2_hom_L (hSL2 : A312SL2Fact) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ (p : ℕ) (_ : p.Prime) (_ : 3 < p) (Φ : ↥L →* SL(2, ZMod p)),
      ∀ x : ↥L, (∃ k : ℕ, x ^ 3 ^ k = 1) → Φ x = 1 → x = 1 := by
  obtain ⟨hnq', h36', -⟩ := nonquasi_data hSL2 h36 h37 c hnq
  obtain ⟨p, hp, hp3, Ψ, hΨ⟩ := exists_sl2_hom h36' hnq'
  have hLG : L ≤ S1421.g0Of T M H K1 := le_of_mem_cComp c.mem
  refine ⟨p, hp, hp3, Ψ.comp (H13.barMap hLG), ?_⟩
  rintro x ⟨k, hk⟩ hx
  have hbar : H13.barMap hLG x = 1 := by
    apply hΨ _ ⟨k, ?_⟩ hx
    rw [← map_pow, hk, map_one]
  have hker : x ∈ (H13.barMap hLG).ker := hbar
  obtain ⟨j, hj⟩ := H13.isPGroup_ker_barMap hLG ⟨x, hker⟩
  have hj' : x ^ 2 ^ j = 1 := congrArg (fun y : ↥(H13.barMap hLG).ker => ((y : ↥L))) hj
  have hd1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hd2 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) :=
    Nat.Coprime.pow j k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
    ((hcop.coprime_dvd_left hd1).coprime_dvd_right hd2) (dvd_refl _))

theorem pRank_three_le_one_L (hSL2 : A312SL2Fact) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : CFSG.pRank 3 ↥L ≤ 1 := by
  obtain ⟨p, hp, hp3, Φ, hΦ⟩ := exists_sl2_hom_L hSL2 h36 h37 c hnq
  exact pRank_three_le_one hp hp3 Φ hΦ

end Context

end QA24

end CFSG.Quasithin

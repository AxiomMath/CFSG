module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}


theorem exists_data83_of_g2_model (hKF : KF83GTwo) {A : Subgroup G} {c a : G}
    (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (3 * n)) (e : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    obtain ⟨p, hp, m, hpr, hm⟩ := FiniteField.card' K
    have h1 : p ∣ 2 ^ (3 * n) := by
      rw [← hK, Nat.card_eq_fintype_card, hm]
      exact dvd_pow_self p m.ne_zero
    have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h1)
    subst h2
    exact ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hout := h.inducesOuterTheta
  have hα3 : inducedAutHom L e ⟨a, ha⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e ha ha3
  have hnot : ¬ IsInnerAut (inducedAutHom L e ⟨a, ha⟩) :=
    (not_isInnerAut_inducedAutHom_iff L e ha).mpr hout
  obtain ⟨σ, hσ3, k, hαk⟩ := g2_order_three_field_descent hK3 hK4 hα3 hnot
  obtain ⟨e', he'⟩ : ∃ e' : L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 K,
      e' = e.trans (MulAut.conj k)⁻¹ := ⟨_, rfl⟩
  have hα' : inducedAutHom L e' ⟨a, ha⟩ = g2FieldHom K σ := by
    rw [he', inducedAutHom_trans, hαk]
    group
  obtain ⟨y₁, y₂, hy₁3, hy₂3, hy, hy₁1, hy₂₁, ⟨ι⟩⟩ := hKF K n hn hK σ hσ3
  have hfix : ∀ y, inducedAutHom L e' ⟨a, ha⟩ (g2Incl σ y) = g2Incl σ y := fun y => by
    rw [hα']
    exact (mem_range_g2Incl_iff hchar σ _).mp ⟨y, rfl⟩
  have hinj : Function.Injective (g2Incl σ) := g2Incl_injective σ
  have hz₁3 : g2Incl σ y₁ ^ 3 = 1 := by rw [← map_pow, hy₁3, map_one]
  have hz₂3 : g2Incl σ y₂ ^ 3 = 1 := by rw [← map_pow, hy₂3, map_one]
  have hz : g2Incl σ y₁ * g2Incl σ y₂ = g2Incl σ y₂ * g2Incl σ y₁ := by
    rw [← map_mul, ← map_mul, hy]
  have hz₁1 : g2Incl σ y₁ ≠ 1 := fun h1 => hy₁1 (hinj (by rw [h1, map_one]))
  have hz₂₁ : g2Incl σ y₂ ∉ Subgroup.zpowers (g2Incl σ y₁) := by
    rintro ⟨j, hj⟩
    exact hy₂₁ ⟨j, hinj (by rw [map_zpow]; exact hj)⟩
  have hne : inSubgroup perfectResidual (Subgroup.centralizer
      ({g2Incl σ y₁} : Set (adjointGroup Tag.G2 K))) ≠ ⊥ := by
    have := nontrivial_projSL_two (m := 3 * n) (by omega)
    exact ne_bot_of_mulEquiv ι
  have hinner : ∀ d : G, d ∈ L → InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal := by
    intro d hdL
    have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
    exact Or.inl (InducesStdKind.g2 K hK3 hK4 ⟨e', hdN, _,
      (inducedAutHom_eq_conj_of_mem e' hdL hdN).symm⟩)
  have hC : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n := by
    obtain ⟨-, k', hk', hk'', hC⟩ := barCentralizer_mulEquiv_g2 hn0 hK ha3 hout e'
    exact ⟨k', hk', hk'', hC⟩
  have hLbar : IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨e'⟩⟩
  refine exists_data83_of_model h e' hZ (hfix y₁) (hfix y₂) hz₁3 hz₂3 hz hz₁1 hz₂₁ hne hn
    hinner ?_
  rintro A₀ d - - - ⟨κ⟩
  exact Or.inl ⟨Or.inr hLbar, ⟨κ.trans ι⟩, Or.inl hC⟩

theorem exists_data83_of_g2 (hKF : KF83GTwo) {A : Subgroup G} {c a : G}
    (h : Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 * n ∧
      Sec4.IsoGTwo (L ⧸ aschbacherSolvableCore 3 L) q) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  obtain ⟨q, hq2, hqe, hv, ⟨e₁⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (3 * n)) = 2 ^ (3 * n) :=
    GaloisField.card 2 (3 * n) (by obtain ⟨k, rfl⟩ := hn; omega)
  have hKq : Nat.card (GaloisField 2 (3 * n)) = q.card := by
    rw [hK, TauCeti.PrimePower.card_def, hq2, hqe]
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 _ hKq
  have hZ : Subgroup.center (adjointGroup Tag.G2 (GaloisField 2 (3 * n))) = ⊥ :=
    center_adjointGroup_eq_bot
  exact exists_data83_of_g2_model hKF h hn hK
    (e₁.trans (e₂.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot)))

end CFSG.RankThree.PartTwo.Sec8.Item83Proof

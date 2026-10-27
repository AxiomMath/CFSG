module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Background.A3Structure313SL2
public import CFSG.Quasithin.Vol2.Ch11SecA11Concl
public import CFSG.Quasithin.Vol2.Ch11SecA12Setup
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecS

variable {G : Type} [Group G] [Finite G] {T L I V₂ K : Subgroup G} {n : ℕ}

namespace C11P9B

omit [Finite G] in
theorem conj_mem_preimage_xi {p : ℕ} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) {y : G}
    (hy : y ∈ preimageModTwoCore K (Subgroup.closure
      {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1})) :
    g * y * g⁻¹ ∈ preimageModTwoCore K (Subgroup.closure
      {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1}) := by
  obtain ⟨k, hk, rfl⟩ := hy
  set φ := conjV K g hg with hφ
  have hφ2 : (CFSG.pCore 2 ↥K).map φ.toMonoidHom = CFSG.pCore 2 ↥K := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 φ
    assumption
  set φb : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    QuotientGroup.congr _ _ φ hφ2 with hφb
  have hφp : (CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K)).map φb.toMonoidHom =
      CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv p φb
    assumption
  have hS : (Subgroup.closure {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1}).map
      φb.toMonoidHom ≤
      Subgroup.closure {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨hφp ▸ ⟨x, hx1, rfl⟩, ?_⟩
    rw [← map_pow, hx2, map_one]
  refine ⟨φ k, ?_, ?_⟩
  · have e : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (φ k) =
        φb.toMonoidHom (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) := rfl
    rw [SetLike.mem_coe, Subgroup.mem_comap, e]
    exact hS ⟨_, hk, rfl⟩
  · exact conjV_apply_coe K hg k

theorem normalizer_le_normalizer_xiP (p : ℕ) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (xiP K p : Set G) := by
  intro g hg
  refine normalizer_le_normalizer_oTwoUpper _ ?_
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact conj_mem_preimage_xi hg hy

omit [Finite G] in
theorem xiP_le (p : ℕ) : xiP K p ≤ K :=
  (oTwoUpper_le _).trans (Subgroup.map_subtype_le _)

theorem xiP_le_centralizer {p : ℕ} [Fact p.Prime] {W : Subgroup G}
    (hF : ∀ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) → Odd (orderOf y) →
      (y : G) ∈ Subgroup.centralizer (W : Set G)) :
    xiP K p ≤ Subgroup.centralizer (W : Set G) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨⟨k, hk, rfl⟩, hodd⟩
  have hS : Subgroup.closure {x | x ∈ CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ∧ x ^ p = 1} ≤
      CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1
  have ho : orderOf (K.subtype k) = orderOf k := Subgroup.orderOf_coe k
  exact hF k (CFSG.pCore_le_fitting _ p (hS hk)) (ho ▸ hodd)

omit [Finite G] in
theorem exists_odd_prime_dvd_fitting (hF : Facts12) (hFb : Facts12b) {Xq : Type} [Group Xq]
    [Finite Xq] (hn : 2 ≤ n) (hc : Concl1111 Xq n) (hnq : ¬ CFSG.IsQuasisimple Xq) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (CFSG.fittingSubgroup Xq) := by
  rcases hc with h2 | ⟨rfl, h3⟩
  · exact (hnq (hF.table Xq n hn h2).1).elim
  have q1 := fun hh => hnq (hFb.list3.1 Xq hh).1
  have q2 := fun hh => hnq (hFb.list3.2 Xq hh).1
  rcases h3 with h1 | h2 | ⟨p, hp, h5, h8, hP⟩ | h4 | ⟨s, h5 | h5⟩ | h6 | h7 | h8 | h9 | h10 |
    h11 | h12 | h13 | h14 | h15
  · exact (q1 (Or.inl h1)).elim
  · exact (q1 (Or.inr (Or.inl h2))).elim
  · exact (q2 (Or.inl ⟨p, hp, by omega, hP⟩)).elim
  · exact (q2 (Or.inr (Or.inl h4))).elim
  · cases s
    · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h5))))))))))).elim
    · exact (q2 (Or.inr (Or.inr (Or.inl h5)))).elim
  · cases s
    · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr h5))))))))))).elim
    · exact (q2 (Or.inr (Or.inr (Or.inr (Or.inl h5))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inl h6)))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inl h7))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8)))))).elim
  · exact (q2 (Or.inr (Or.inr (Or.inr (Or.inr h9))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))))))).elim
  · exact (q1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h13)))))))))).elim
  · obtain ⟨-, -, h5', hprimes⟩ := h14
    have hne : Nat.card (CFSG.fittingSubgroup Xq) ≠ 1 := by
      intro h1
      have hbot : CFSG.fittingSubgroup Xq = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      obtain ⟨e⟩ := h5'
      exact hnq (A313.IsSL2.isQuasisimple Nat.prime_five le_rfl
        ⟨(QuotientGroup.quotientBot.symm.trans
          (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e⟩)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    refine ⟨p, hp, fun h2 => ?_, hpd⟩
    have := (hprimes p hp hpd).1
    omega
  · obtain ⟨p, hp, -, h8', -, ⟨eF⟩, -⟩ := h15
    refine ⟨p, hp, by omega, ?_⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥(CFSG.fittingSubgroup Xq) = p ^ 2 := by
      rw [Nat.card_congr eF.toEquiv, Nat.card_eq_fintype_card]
      simp [Fintype.card_multiplicative, ZMod.card]
    rw [hcard]
    exact dvd_pow_self p two_ne_zero

theorem pCoreOf_ne_bot_of_isXi (hCT : QuasithinUnique.CharTwo K) {Y : Subgroup G}
    (hXi : IsXi T Y) (hYK : Y ≤ K) (hKY : K ≤ Subgroup.normalizer (Y : Set G)) :
    pCoreOf 2 Y ≠ ⊥ := by
  intro h0
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, p, hp, hp2, hpow, hidx, -⟩ := hXi
  have : Fact p.Prime := ⟨hp⟩
  have hYp : IsPGroup p Y := fun y => ⟨1, Subtype.ext (by
    have := hpow y y.2
    rw [h0, Subgroup.mem_bot] at this
    simpa using this)⟩
  have hdisj : Y ⊓ pCoreOf 2 K = ⊥ :=
    (IsPGroup.disjoint_of_ne p 2 hp2 Y (pCoreOf 2 K) hYp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)).eq_bot
  have hc : ⁅Y, pCoreOf 2 K⁆ ≤ Y ⊓ pCoreOf 2 K := by
    refine le_inf ?_ (commutator_le_of_le_normalizer
      (hYK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)))
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKY)
  rw [hdisj, le_bot_iff] at hc
  have hYC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hYO : Y ≤ pCoreOf 2 K := fun y hy => hCT ⟨hYK hy, hYC hy⟩
  have hY : Y = ⊥ := by rw [← inf_eq_left.mpr hYO, hdisj]
  have h1 : (pCoreOf 2 Y).relIndex Y = 1 := by
    rw [hY]
    exact Subgroup.relIndex_bot_right _
  rw [h1] at hidx
  rcases hidx with h | ⟨h, -⟩
  · have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
    omega
  · have := Nat.one_lt_pow (by norm_num : (3 : ℕ) ≠ 0) hp.one_lt
    omega

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA

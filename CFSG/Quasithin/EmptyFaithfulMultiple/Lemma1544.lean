module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Statements
import CFSG.Quasithin.Background.A1a
import CFSG.Quasithin.Background.OrderingMax
import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Construction

variable {G : Type*} [Group G]

private theorem mem_of_pow_mem_of_pow_mem_of_coprime {Q : Subgroup G} {x : G} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : x ^ m ∈ Q) (hn : x ^ n ∈ Q) : x ∈ Q := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  have h1 : x ^ ((m : ℤ) * a + (n : ℤ) * b) = (x ^ m) ^ a * (x ^ n) ^ b := by
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have h2 : (m : ℤ) * a + (n : ℤ) * b = 1 := by linarith
  rw [h2, zpow_one] at h1
  rw [h1]
  exact Q.mul_mem (Q.zpow_mem hm a) (Q.zpow_mem hn b)

variable [Finite G]

omit [Finite G] in
private theorem isSylowTwoOf_of_quasithinIsSylowTwo {T K : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTK : T ≤ K) : IsSylowTwoOf T K :=
  ⟨hTK, hT.1, fun h2 => hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩

omit [Finite G] in
private theorem exists_normal_elemAbelian_mod_pCore {H : Type*} [Group H] [Finite H]
    [Group.IsSolvable H] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) (hpH : p ∣ Nat.card H) :
    ∃ N : Subgroup H, N.Normal ∧ ¬ N ≤ CFSG.Open.pCore 2 H ∧
      (∀ n ∈ N, n ^ p ∈ CFSG.Open.pCore 2 H) ∧
      ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ CFSG.Open.pCore 2 H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hO2 : IsPGroup 2 (CFSG.Open.pCore 2 H) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p hpH
  have hhO : h ∉ CFSG.Open.pCore 2 H := by
    intro hmem
    obtain ⟨k, hk⟩ := hO2 ⟨h, hmem⟩
    have hk' : h ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : p ∣ 2 ^ k := hh ▸ orderOf_dvd_of_pow_eq_one hk'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have : Nontrivial (H ⧸ CFSG.Open.pCore 2 H) := by
    refine ⟨⟨(h : H ⧸ CFSG.Open.pCore 2 H), 1, ?_⟩⟩
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hhO
  obtain ⟨N', hN'⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_minimal_nontrivial_normal
      (G := H ⧸ CFSG.Open.pCore 2 H)
  obtain ⟨r, hr, hrab, d, hd, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary N' hN'
      inferInstance
  have hrp : r = p := by
    have hrH : r ∣ Nat.card H := by
      have h1 : r ∣ Nat.card N' := hcard ▸ dvd_pow_self r hd.ne'
      exact h1.trans ((Subgroup.card_subgroup_dvd_card N').trans
        (Subgroup.index_dvd_card (CFSG.Open.pCore 2 H)))
    rcases hprimes r hr hrH with h2 | h2
    · exfalso
      rw [h2] at hcard
      have hle := CFSG.LieType.BorelTits.le_pCore 2 hN'.1.1 (IsPGroup.of_card hcard)
      rw [B6.pCore_quotient_pCore] at hle
      exact hN'.1.2 (le_bot_iff.mp hle)
    · exact h2
  rw [hrp] at hrab
  refine ⟨N'.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 H)), hN'.1.1.comap _, ?_, ?_, ?_⟩
  · intro hle
    apply hN'.1.2
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hle hy
  · intro n hn
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hrab.2 _ hn
  · intro a ha b hb
    have hc := congrArg Subtype.val (hrab.1.is_comm.comm
      (⟨(a : H ⧸ CFSG.Open.pCore 2 H), ha⟩ : N') ⟨(b : H ⧸ CFSG.Open.pCore 2 H), hb⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc]
    group

private theorem exists_elemAbelian_section_of_solvable {H : Subgroup G} (hHs : Group.IsSolvable H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card H → q = 2 ∨ q = p) (hpH : p ∣ Nat.card H) :
    ∃ N : Subgroup G, N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set G) ∧ ¬ N ≤ pCoreOf 2 H ∧
      (∀ n ∈ N, n ^ p ∈ pCoreOf 2 H) ∧ ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H := by
  have := hHs
  obtain ⟨N, hNn, hNO, hpow, hcomm⟩ :=
    exists_normal_elemAbelian_mod_pCore (H := H) hp hp2 hprimes hpH
  refine ⟨N.map H.subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_, ?_⟩
  · have h1 := Subgroup.le_normalizer_map (H := N) H.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hNn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
  · intro hle
    exact hNO ((Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp hle)
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨n ^ p, hpow n hn, by simp⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b * a⁻¹ * b⁻¹, hcomm a ha b hb, by simp⟩

private theorem exists_irreducible_section {H N T : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hNH : N ≤ H) (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hNQ : ¬ N ≤ pCoreOf 2 H)
    (hpow : ∀ n ∈ N, n ^ p ∈ pCoreOf 2 H)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 H) :
    ∃ X : Subgroup G, X ≤ N ∧ X = oTwoUpper X ∧ T ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ x ∈ X, x ^ p ∈ pCoreOf 2 X) ∧
      (∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 X) ∧ ¬ X ≤ pCoreOf 2 X ∧
      ∀ Y : Subgroup G, pCoreOf 2 X ≤ Y → Y ≤ X → T ≤ Subgroup.normalizer (Y : Set G) →
        Y = pCoreOf 2 X ∨ Y = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H
  have hodd : ∀ x ∈ N, ∀ k : ℕ, x ^ 2 ^ k ∈ Q → x ∈ Q := fun x hx k hk =>
    mem_of_pow_mem_of_pow_mem_of_coprime
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))) hk
      (hpow x hx)
  obtain ⟨X, -, hXmin⟩ := Finite.exists_le_minimal
    (p := fun X : Subgroup G => X ≤ N ∧ T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ X ≤ Q)
    (a := N) ⟨le_rfl, hTN, hNQ⟩
  obtain ⟨hXN, hTX, hXQ⟩ := hXmin.1
  have hXH : X ≤ H := hXN.trans hNH
  have hQX : Q ⊓ X ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hx)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  have hOQ : pCoreOf 2 X ≤ Q := by
    intro x hx
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hodd x (hXN (CFSG.LieType.BorelTits.pCoreOf_le 2 X hx)) k (hk' ▸ Q.one_mem)
  have hpowX : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X := fun x hx =>
    hQX ⟨hpow x (hXN hx), X.pow_mem hx p⟩
  have hcommX : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 X := fun a ha b hb =>
    hQX ⟨hcomm a (hXN ha) b (hXN hb),
      X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)⟩
  refine ⟨X, hXN, ?_, hTX, hpowX, hcommX, fun h => hXQ (h.trans hOQ), ?_⟩
  ·
    symm
    refine hXmin.eq_of_le ⟨(oTwoUpper_le X).trans hXN,
      hTX.trans (normalizer_le_normalizer_oTwoUpper X), fun hle => hXQ fun x hx => ?_⟩
      (oTwoUpper_le X)
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X hx
    exact hodd x (hXN hx) k (hle hk)
  ·
    intro Y hOY hYX hTY
    by_cases hYQ : Y ≤ Q
    · exact Or.inl (le_antisymm (fun y hy => hQX ⟨hYQ hy, hYX hy⟩) hOY)
    · exact Or.inr (hXmin.eq_of_le ⟨hYX.trans hXN, hTY, hYQ⟩ hYX)

private theorem exists_elemAbelian_of_section {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X)
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 X) (hne : ¬ X ≤ pCoreOf 2 X) :
    ∃ d : ℕ, 1 ≤ d ∧ (pCoreOf 2 X).relIndex X = p ^ d ∧
      ∃ P : Subgroup G, P ≤ X ∧ IsElemAbelian p P ∧ p ^ d ≤ Nat.card P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hsub : (pCoreOf 2 X).subgroupOf X = CFSG.Open.pCore 2 X :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hpg : IsPGroup p (↥X ⧸ CFSG.Open.pCore 2 X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hpow x x.2
    rwa [show y = x ^ p from Subtype.ext (by simpa using hyx)] at hy
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hpg
  have hidx : (pCoreOf 2 X).relIndex X = p ^ d := by
    rw [Subgroup.relIndex, hsub]
    exact hd
  refine ⟨d, ?_, hidx, ?_⟩
  · rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0, pow_zero, Subgroup.relIndex_eq_one] at hidx
      exact hne hidx
    · exact h0
  · obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p X))
    have hPp : IsPGroup p ((S : Subgroup X).map X.subtype) := S.isPGroup'.map X.subtype
    have hPX : (S : Subgroup X).map X.subtype ≤ X := Subgroup.map_subtype_le _
    have hbot : ∀ y ∈ (S : Subgroup X).map X.subtype, y ∈ pCoreOf 2 X → y = 1 :=
      fun y hy1 hy2 => Subgroup.disjoint_def.mp
        (IsPGroup.disjoint_of_ne p 2 hp2 _ _ hPp
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)) hy1 hy2
    refine ⟨(S : Subgroup X).map X.subtype, hPX, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩,
      fun y hy => hbot _ (Subgroup.pow_mem _ hy p) (hpow y (hPX hy))⟩, ?_⟩
    · have h1 := hbot _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ a.2 b.2)
        (Subgroup.inv_mem _ a.2)) (Subgroup.inv_mem _ b.2)) (hcomm a (hPX a.2) b (hPX b.2))
      simp only [Subgroup.coe_mul]
      calc (a : G) * b = (a * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · have hdvd : p ^ d ∣ Nat.card X := hd ▸ Subgroup.index_dvd_card (CFSG.Open.pCore 2 X)
      rw [Subgroup.card_map_of_injective X.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (S.pow_dvd_card_of_pow_dvd_card hdvd)

theorem exists_xi_of_solvable {T K : Subgroup G} {p : ℕ} (hT : IsSylowTwoOf T K)
    (hK : pCoreOf 2 K ≠ ⊥) (hKs : Group.IsSolvable K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K)
    (hrank : ∀ E : Subgroup G, E ≤ K → IsElemAbelian p E → Nat.card E ≤ p ^ 2) :
    ∃ X : Subgroup G, X ≤ K ∧
      ((IsXi T X ∧ (pCoreOf 2 X).relIndex X = p ^ 2) ∨
        (IsSmallXi T X ∧ (pCoreOf 2 X).relIndex X = p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTK, hT2, hTodd⟩ := hT
  let π : Set Nat.Primes := {r | r.val = 2 ∨ r.val = p}
  have hTπ : CFSG.IsPiSubgroup π (T.subgroupOf K) := by
    intro r hr
    obtain ⟨n, hn⟩ :=
      IsPGroup.iff_card.mp (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm)
    rw [hn] at hr
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_two).mp (r.2.dvd_of_dvd_pow hr))
  obtain ⟨H', hH', hTH'⟩ := CFSG.SolvableHall.solvable_hall_containment hKs π _ hTπ
  have hHK : H'.map K.subtype ≤ K := Subgroup.map_subtype_le H'
  have hTH : T ≤ H'.map K.subtype := fun t ht => ⟨⟨t, hTK ht⟩, hTH' ht, rfl⟩
  have hcardH : Nat.card (H'.map K.subtype) = Nat.card H' :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card (H'.map K.subtype) → q = 2 ∨ q = p := by
    intro q hq hqH
    rw [hcardH] at hqH
    exact hH'.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqH
  have hpH : p ∣ Nat.card (H'.map K.subtype) := by
    rw [hcardH]
    have h1 : p ∣ Nat.card H' * H'.index := by rw [Subgroup.card_mul_index]; exact hpK
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact h
    · exact absurd (Or.inr rfl) (hH'.p_in_pi_of_p_dvd_index ⟨p, hp⟩ h)
  have hHs : Group.IsSolvable (H'.map K.subtype) := by
    have := hKs
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hHK)
  obtain ⟨N, hNH, hHN, hNQ, hpowN, hcommN⟩ :=
    exists_elemAbelian_section_of_solvable hHs hp hp2 hprimes hpH
  obtain ⟨X, hXN, hXo, hTX, hpowX, hcommX, hXO, hirr⟩ :=
    exists_irreducible_section hp hp2 hNH (hTH.trans hHN) hNQ hpowN hcommN
  obtain ⟨d, hd1, hidx, P, hPX, hPab, hPcard⟩ :=
    exists_elemAbelian_of_section hp hp2 hpowX hcommX hXO
  have hXK : X ≤ K := hXN.trans (hNH.trans hHK)
  have hd2 : d ≤ 2 :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mp (hPcard.trans (hrank P (hPX.trans hXK) hPab))
  have hXT : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    intro hbot
    apply hK
    have := pCoreOf_le_pCoreOf_of_sylow (sup_le hXK hTK) hT2 le_sup_right hTodd
    rw [hbot] at this
    exact le_bot_iff.mp this
  refine ⟨X, hXK, ?_⟩
  have hcommle : ⁅X, X⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hcommX a ha b hb
  interval_cases d
  · right
    rw [pow_one] at hidx
    exact ⟨⟨hXo, hTX, ⟨le_sup_right, hXT⟩, p, hp, hp2, hidx⟩, hidx⟩
  · left
    refine ⟨⟨hXo, hTX, hXT, p, hp, hp2, hpowX, Or.inl hidx, ?_⟩, hidx⟩
    rw [sup_eq_right.mpr hcommle]
    exact hirr

private theorem card_le_sq_of_le_isTwoLocal (hrk : evenRank G ≤ 2) {M : Subgroup G}
    (hM : IsTwoLocal M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hEM : E ≤ M)
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt hEM hE hk
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 M hM
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end Construction

section Hypothesis

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

private theorem exists_inM_of_inH {Y : Subgroup G} (hY : InH T Y) :
    ∃ M : Subgroup G, InM T M ∧ Y ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, hNM⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 Y, hY.2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩ :
      IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)))
  have hYM : Y ≤ M := (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y).trans hNM
  exact ⟨M, ⟨hM, hY.1.trans hYM⟩, hYM⟩

private theorem exists_inM_relIndex_dvd_of_isSmallXi {Y : Subgroup G} (hY : IsSmallXi T Y) :
    ∃ M : Subgroup G, InM T M ∧ ((pCoreOf 2 Y).relIndex Y).Prime ∧
      (pCoreOf 2 Y).relIndex Y ∣ Nat.card M := by
  obtain ⟨-, -, hYT, r, hr, -, hidx⟩ := hY
  obtain ⟨M, hM, hYTM⟩ := exists_inM_of_inH hYT
  exact ⟨M, hM, hidx ▸ hr, (Subgroup.index_dvd_card _).trans
    (Subgroup.card_dvd_of_le (le_sup_left.trans hYTM))⟩

theorem exists_xi_of_le_inM (hyp : MultipleCentralizerHypothesis G T) {K M : Subgroup G}
    (hM : InM T M) (hTK : T ≤ K) (hKM : K ≤ M) (hK : pCoreOf 2 K ≠ ⊥)
    (hKs : Group.IsSolvable K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K) :
    ∃ X : Subgroup G, X ≤ K ∧
      ((IsXi T X ∧ (pCoreOf 2 X).relIndex X = p ^ 2) ∨
        (IsSmallXi T X ∧ (pCoreOf 2 X).relIndex X = p)) :=
  exists_xi_of_solvable (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTK) hK hKs hp hp2 hpK
    fun _ hEK hE => card_le_sq_of_le_isTwoLocal hyp.qtke.2.2 hM.1.1 hp hp2 (hEK.trans hKM) hE

theorem stmt1544_of (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T)
    (h3 : Stmt1542Three G T) (h43 : Stmt1543 G T) : Stmt1544 G T := by
  intro M hM q hq hqM
  by_contra hne
  have hq7 : 7 ≤ q := by
    have h1 := hq.two_le
    have h2 := hq.eq_two_or_odd
    omega
  set S : Set ℕ := {r | r.Prime ∧ ∃ M' : Subgroup G, InM T M' ∧ r ∣ Nat.card M'}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro r ⟨-, M', -, hrM'⟩
    exact (Nat.le_of_dvd Nat.card_pos hrM').trans (Subgroup.card_le_card_group M')
  have hqS : q ∈ S := ⟨hq, M, hM, hqM⟩
  obtain ⟨hp, M₀, hM₀, hpM₀⟩ : sSup S ∈ S := Nat.sSup_mem ⟨q, hqS⟩ hSbdd
  have hmax : ∀ r ∈ S, r ≤ sSup S := fun r hr => le_csSup hSbdd hr
  have hqp : q ≤ sSup S := hmax q hqS
  obtain ⟨X, -, hX⟩ := exists_xi_of_le_inM hyp hM₀ hM₀.2 le_rfl
    (pCoreOf_ne_bot_of_isTwoLocal hM₀.1.1) (h2 M₀ hM₀) hp (by omega) hpM₀
  rcases hX with ⟨hXi, hidx⟩ | ⟨hXi, hidx⟩
  ·
    have h35 := (h3 X hXi).2.2.2
    rw [hidx] at h35
    rcases h35 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : sSup S = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (hp.dvd_of_dvd_pow (hk ▸ dvd_pow_self _ two_ne_zero))
      omega
    · have : sSup S = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp
        (hp.dvd_of_dvd_pow (hk ▸ dvd_pow_self _ two_ne_zero))
      omega
  ·
    have hξ : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ sSup S := by
      intro Y hY
      obtain ⟨M', hM', hprime, hdvd⟩ := exists_inM_relIndex_dvd_of_isSmallXi hY
      exact hmax _ ⟨hprime, M', hM', hdvd⟩
    have h5 := (h43 X _ hXi hidx hξ (by omega)).2.2.2.2
    omega

theorem stmt1545_of (hyp : MultipleCentralizerHypothesis G T) (h2 : Stmt1542Two G T)
    (h3 : Stmt1542Three G T) (h43 : Stmt1543 G T) (h44 : Stmt1544 G T) : Stmt1545 G T := by
  intro q hq hqC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := quasithinOmegaOneCenter T
  obtain ⟨M₁, -, -, hM₁, -, hCM₁, -⟩ := hyp.two_centralizer_maximal
  have hZT : Z ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun z hz => hz.1
  have hTC : T ≤ Subgroup.centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZT hz).2 x hx).symm
  have hM₁T : InM T M₁ := ⟨hM₁, hTC.trans hCM₁⟩
  rcases h44 M₁ hM₁T q hq (hqC.trans (Subgroup.card_dvd_of_le hCM₁)) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    subst h
    have := hyp.simple
    have hTne : T ≠ ⊥ := sylow_ne_bot hyp.nonabelian (hyp.sylow.1.toSylow hyp.sylow.2)
    have hZne : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot hyp.sylow.1 hTne
    have hZC : Z ≤ pCoreOf 2 (Subgroup.centralizer (Z : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((hZT.trans inf_le_left).trans hTC)
        (Subgroup.centralizer_le_normalizer _) (hyp.sylow.1.to_le (hZT.trans inf_le_left))
    have hCne : pCoreOf 2 (Subgroup.centralizer (Z : Set G)) ≠ ⊥ := fun h =>
      hZne (le_bot_iff.mp (h ▸ hZC))
    have hCs : Group.IsSolvable (Subgroup.centralizer (Z : Set G)) := by
      have := h2 M₁ hM₁T
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hCM₁)
    obtain ⟨X, hXC, hX⟩ :=
      exists_xi_of_le_inM hyp hM₁T hTC hCM₁ hCne hCs Nat.prime_five (by norm_num) hqC
    have hZX : ⁅Z, X⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hXC
    rcases hX with ⟨hXi, -⟩ | ⟨hXi, hidx⟩
    ·
      exact (h3 X hXi).1 hZX
    ·
      have hξ : ∀ Y : Subgroup G, IsSmallXi T Y → (pCoreOf 2 Y).relIndex Y ≤ 5 := by
        intro Y hY
        obtain ⟨M', hM', hprime, hdvd⟩ := exists_inM_relIndex_dvd_of_isSmallXi hY
        rcases h44 M' hM' _ hprime hdvd with h | h | h <;> omega
      exact (h43 X 5 hXi hidx hξ (by norm_num)).2.2.1 hZX

end Hypothesis

end CFSG.Quasithin.EmptyFaithfulMultiple

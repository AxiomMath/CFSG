module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E3
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6R77

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
  (P614I.relIndex_centralizer_le_card_commutator)

variable {G : Type} [Group G] [Finite G]

@[expose] def SixNineAt (M X : Subgroup G) (r : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ M → IsElemAbelian r E → Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ M →
    ∀ x ∈ X, (∃ y ∈ X, x * y ≠ y * x) → E ≤ normalizer (zpowers x : Set G) →
      normalizer (zpowers x : Set G) ≤ M

theorem rankThreeGamma_le_of_elemAbelian_cube {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hpr : p ≠ r) {M X : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (hXM : X ≤ M) (hX : IsElemAbelian r X)
    (hXcard : Nat.card X = r ^ 3) (h3 : 3 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) :
    rankThreeGamma 1 r X ≤ M := by
  obtain ⟨P, hPN, hPel, hPcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.out.one_lt (M ⊓ normalizer (X : Set G))
  set m := CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) with hm
  have hPM : P ≤ M := hPN.trans inf_le_left
  have hPE : P ≤ normalizer (X : Set G) := hPN.trans inf_le_right
  have hPc : ∀ a b : P, a * b = b * a := fun a b => Subtype.ext (hPel.comm a.2 b.2)
  have hPp : ∀ a : P, a ^ p = 1 := fun a => Subtype.ext (by simpa using hPel.2 a a.2)
  let φ : P →* MulAut X := X.normalizerMonoidHom.comp (inclusion hPE)
  have hφ : ∀ (a : P) (e : X), ((φ a e : X) : G) = a * e * (a : G)⁻¹ := fun _ _ => rfl
  have hker : ∀ a : P, φ a = 1 ↔ (a : G) ∈ centralizer (X : Set G) := by
    intro a
    rw [mem_centralizer_iff]
    constructor
    · intro h e he
      have h1 := congrArg (fun f : MulAut X => ((f ⟨e, he⟩ : X) : G)) h
      simp only [hφ, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    · intro h
      refine MulEquiv.ext fun e => Subtype.ext ?_
      rw [hφ, MulAut.one_apply, ← h e e.2, mul_inv_cancel_right]
  set K : Subgroup G := P ⊓ centralizer (X : Set G) with hK
  have hKel : IsElemAbelian p K := hPel.mono inf_le_left
  have hKM : K ≤ M ⊓ centralizer (X : Set G) := inf_le_inf_right _ hPM
  have hcardK : Nat.card φ.ker = Nat.card K := by
    have : φ.ker = K.subgroupOf P := by
      ext a
      rw [MonoidHom.mem_ker, hker, mem_subgroupOf, mem_inf]
      exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
    rw [this]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hPKA : Nat.card P = Nat.card K * Nat.card φ.range := by
    rw [← hcardK, ← index_ker, card_mul_index]
  have hAel : IsElemAbelian p φ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      rw [coe_mul, coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, hPc a b]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, hPp a, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1
    (show Nat.card φ.range ∣ p ^ m from ⟨Nat.card K, by rw [← hPcard, hPKA, mul_comm]⟩)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).1
    (show Nat.card K ∣ p ^ m from ⟨Nat.card φ.range, by rw [← hPcard, hPKA]⟩)
  have hij : i + j = m := Nat.pow_right_injective hp.out.two_le
    (show p ^ (i + j) = p ^ m by rw [pow_add, ← hi, ← hj, ← hPKA, hPcard])
  have hj3 : j ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1
    (hj ▸ card_le_pow_of_mulAut hp.out hpr hX hXcard hAel)
  have hi1 : 1 ≤ i := by omega
  have hK1 : K ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hi
    have := Nat.one_lt_pow (by omega : i ≠ 0) hp.out.one_lt
    omega
  obtain ⟨c, hcK, hc1⟩ := (bot_or_exists_ne_one K).resolve_left hK1
  have hcP : c ∈ P := (mem_inf.1 hcK).1
  have hcC : c ∈ centralizer (X : Set G) := (mem_inf.1 hcK).2
  have hcp : orderOf c = p := orderOf_eq_prime (hKel.2 c hcK) hc1
  have hline : ∀ L : Subgroup G, L ≤ X → 1 < CFSG.Open.pRank p (M ⊓ normalizer (L : Set G)) := by
    intro L hLX
    have hCN : M ⊓ centralizer (X : Set G) ≤ M ⊓ normalizer (L : Set G) :=
      inf_le_inf_left _ ((centralizer_le hLX).trans (centralizer_le_normalizer _))
    by_cases hi2 : 2 ≤ i
    · exact le_trans hi2 (CFSG.SectionRank.le_pRank hp.out.one_lt (hKM.trans hCN) hKel hi)
    have hi1' : i = 1 := by omega
    have hj3' : j = 3 := by omega
    have hpr1 : p ∣ r - 1 := by
      by_contra hpr1
      haveI := isCyclic_of_mulAut_three hpr hpr1 hX hXcard hAel.isPGroup
      have h := card_le_of_isCyclic hp.out.pos fun x : φ.range =>
        Subtype.ext (by simpa using hAel.2 x x.2)
      rw [hj, hj3'] at h
      have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (h.trans_eq (pow_one p).symm)
      omega
    obtain ⟨z, hz1, hzp, k, hzk⟩ := exists_powAut hpr1 hX hXcard (by norm_num)
    have hBel : IsElemAbelian p (φ.range ⊔ zpowers z) :=
      hAel.sup_of_commute (isElemAbelian_zpowers hzp) fun a _ b hb => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (mul_comm_of_pow hzk a) n).eq
    have hAB : φ.range = φ.range ⊔ zpowers z :=
      eq_of_le_of_card_ge le_sup_left (by
        rw [hj, hj3']
        exact card_le_pow_of_mulAut hp.out hpr hX hXcard hBel)
    have hzA : z ∈ φ.range := by
      rw [hAB]
      exact mem_sup_right (mem_zpowers z)
    obtain ⟨a, ha⟩ := hzA
    have haE : ∀ e : X, (a : G) * e * (a : G)⁻¹ = ((e ^ k : X) : G) := fun e => by
      rw [← hφ, ha, hzk]
    have haC : (a : G) ∉ centralizer (X : Set G) := fun h => hz1 (ha ▸ (hker a).2 h)
    have hap : orderOf (a : G) = p :=
      orderOf_eq_prime (hPel.2 a a.2) fun h => haC (h ▸ one_mem _)
    have haN : (a : G) ∈ M ⊓ normalizer (L : Set G) := by
      refine mem_inf.2 ⟨hPM a.2, mem_normalizer_of_conj_mem fun x hx => ?_⟩
      rw [haE ⟨x, hLX hx⟩, coe_pow]
      exact L.pow_mem hx k
    have hca : Commute c (a : G) := hPel.comm hcP a.2
    have hac : (a : G) ∉ zpowers c := fun h =>
      haC ((zpowers_le.2 hcC : zpowers c ≤ centralizer (X : Set G)) h)
    exact CFSG.GroupTheory.two_le_pRank_of_commute (hCN (hKM hcK)) haN hcp hap hca hac
  refine rankThreeGamma_le_of_forall_normalizer_zpowers_le hM hX.isPGroup hcC hcp
    fun y hyX hy1 => ?_
  have hyr : y ^ r = 1 := hX.2 y hyX
  have hyo : orderOf y = r := orderOf_eq_prime hyr hy1
  obtain ⟨w, hwX, hwy⟩ : ∃ w ∈ X, w ∉ zpowers y := by
    by_contra h
    push Not at h
    have h1 := card_le_of_le (show X ≤ zpowers y from h)
    rw [Nat.card_zpowers, hyo, hXcard] at h1
    have := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 (h1.trans_eq (pow_one r).symm)
    omega
  have hwo : orderOf w = r := orderOf_eq_prime (hX.2 w hwX) fun h => hwy (h ▸ one_mem _)
  obtain ⟨hEel, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian hX hyX hwX hyo hwo hwy
  have hEX : zpowers y ⊔ zpowers w ≤ X := sup_le (zpowers_le.mpr hyX) (zpowers_le.mpr hwX)
  have hcE : zpowers c ≤ M ⊓ centralizer ((zpowers y ⊔ zpowers w : Subgroup G) : Set G) :=
    zpowers_le.mpr (mem_inf.2 ⟨hPM hcP, centralizer_le hEX hcC⟩)
  have hΓ := h76 r hr.out _ (hEX.trans hXM) hEel hEcard
    (lt_of_lt_of_le zero_lt_one (CFSG.SectionRank.le_pRank hp.out.one_lt hcE
      (isElemAbelian_zpowers (hKel.2 c hcK)) (by rw [Nat.card_zpowers, hcp, pow_one])))
    fun L hLE _ => hline L (hLE.trans hEX)
  exact (normalizer_zpowers_le_rankThreeGamma (mem_sup_left (mem_zpowers y)) hyr hy1).trans hΓ

theorem rankThreeGamma_le_of_not_isCyclic_center {p r : ℕ} [hp : Fact p.Prime]
    [hr : Fact r.Prime] (hpr : p ≠ r) {M X : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (h69 : SixNineAt M X r)
    (hrank : CFSG.Open.pRank r X ≤ 3) (hXM : X ≤ M) (hX : IsPGroup r X)
    (hexp : ∀ x ∈ X, x ^ r = 1) {a b : G} (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a)
    (hZ : ¬ IsCyclic (X ⊓ centralizer (X : Set G) : Subgroup G))
    (h3 : 3 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) {c : G}
    (hcX : c ∈ centralizer (X : Set G)) (hc : orderOf c = p) : rankThreeGamma 1 r X ≤ M := by
  set Z : Subgroup G := X ⊓ centralizer (X : Set G) with hZdef
  have hZX : Z ≤ X := inf_le_left
  have hZel : IsElemAbelian r Z := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => hexp x (hZX hx)⟩
    exact (mem_centralizer_iff.1 (mem_inf.1 y.2).2) x (mem_inf.1 x.2).1
  have haZ : a ∉ Z := fun h => hab ((mem_centralizer_iff.1 (mem_inf.1 h).2) b hb).symm
  obtain ⟨k, hk⟩ := (hX.to_le hZX).exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    apply hZ
    have hk2' : k < 2 := by omega
    interval_cases k
    · rw [pow_zero] at hk
      exact isCyclic_of_orderOf_eq_card (1 : Z) (by rw [orderOf_one, hk])
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  have hZa : Z ⊔ zpowers a ≤ X := sup_le hZX (zpowers_le.mpr ha)
  have hZael : IsElemAbelian r (Z ⊔ zpowers a) :=
    hZel.sup_of_commute (isElemAbelian_zpowers (hexp a ha)) fun z hz w hw => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_right
        (show Commute z a from ((mem_centralizer_iff.1 (mem_inf.1 hz).2) a ha).symm) n).eq
  obtain ⟨l, hl⟩ := (hX.to_le hZa).exists_card_eq
  have hl3 : l ≤ 3 := (CFSG.SectionRank.le_pRank hr.out.one_lt hZa hZael hl).trans hrank
  have hkl : k < l := by
    have hdvd : r ^ k ∣ r ^ l := by
      rw [← hk, ← hl]
      exact card_dvd_of_le le_sup_left
    refine lt_of_le_of_ne ((Nat.pow_dvd_pow_iff_le_right hr.out.one_lt).1 hdvd) fun hkl => haZ ?_
    have : Z = Z ⊔ zpowers a := eq_of_le_of_card_ge le_sup_left (by rw [hk, hl, hkl])
    rw [this]
    exact mem_sup_right (mem_zpowers a)
  have hZcard : Nat.card Z = r ^ 2 := by rw [hk, show k = 2 by omega]
  have hNZ : M ⊓ normalizer (X : Set G) ≤ M ⊓ normalizer (Z : Set G) :=
    inf_le_inf_left _ (normalizer_le_normalizer_inf_centralizer X)
  have hΓZ : rankThreeGamma 1 r Z ≤ M :=
    rankThreeGamma_le_of_two_lt_pRank hpr h76 (hZX.trans hXM) hZel hZcard
      (lt_of_lt_of_le (by omega) (CFSG.SectionRank.pRank_mono hp.out.one_lt hNZ))
  refine rankThreeGamma_le_of_forall_normalizer_zpowers_le hM hX hcX hc fun y hyX hy1 => ?_
  by_cases hyZ : y ∈ Z
  · exact (normalizer_zpowers_le_rankThreeGamma hyZ (hexp y hyX) hy1).trans hΓZ
  refine h69 Z (hZX.trans hXM) hZel hZcard hΓZ y hyX ?_ ?_
  · by_contra h
    push Not at h
    exact hyZ (mem_inf.2 ⟨hyX, mem_centralizer_iff.2 fun w hw => (h w hw).symm⟩)
  · exact fun z hz => centralizer_le_normalizer_zpowers y
      (mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (mem_inf.1 hz).2) y hyX).symm)

theorem rankThreeGamma_le_of_isCyclic_center {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hpr : p ≠ r) {M X P : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (h69 : SixNineAt M X r) (hXM : X ≤ M)
    (hX : IsPGroup r X) (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥) {a b : G}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a * b ≠ b * a)
    (hZ : IsCyclic (X ⊓ centralizer (X : Set G) : Subgroup G)) (hPM : P ≤ M)
    (hPX : P ≤ normalizer (X : Set G)) (hPel : IsElemAbelian p P) (hPcard : Nat.card P = p ^ 4)
    (hKcard : Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) = p) :
    rankThreeGamma 1 r X ≤ M := by
  set Z : Subgroup G := X ⊓ centralizer (X : Set G) with hZdef
  have hZX : Z ≤ X := inf_le_left
  obtain ⟨c, hcK, hc1⟩ := (bot_or_exists_ne_one (P ⊓ centralizer (X : Set G))).resolve_left
    fun h => by
      rw [h, card_bot] at hKcard
      exact hp.out.one_lt.ne hKcard
  have hcX : c ∈ centralizer (X : Set G) := (mem_inf.1 hcK).2
  have hc : orderOf c = p := orderOf_eq_prime ((hPel.mono inf_le_left).2 c hcK) hc1
  have hX'Z : (⁅X, X⁆ : Subgroup G) ≤ Z :=
    le_inf (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2.commutator_le_self X)
      (commutator_eq_bot_iff_le_centralizer.mp hcl)
  have habX' : ⁅a, b⁆ ∈ (⁅X, X⁆ : Subgroup G) := commutator_mem_commutator ha hb
  have habne : ⁅a, b⁆ ≠ 1 := fun h => hab (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hZcard : Nat.card Z = r := by
    haveI := hZ
    have hle : Nat.card Z ≤ r := card_le_of_isCyclic hr.out.pos fun x =>
      Subtype.ext (by simpa using hexp x (hZX x.2))
    obtain ⟨k, hk⟩ := (hX.to_le hZX).exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have h1 := hX'Z habX'
      rw [eq_bot_of_card_eq Z hk, mem_bot] at h1
      exact habne h1
    rw [hk] at hle ⊢
    have := (Nat.pow_le_pow_iff_right hr.out.one_lt).1 (hle.trans_eq (pow_one r).symm)
    rw [show k = 1 by omega, pow_one]
  have hX'card : Nat.card (⁅X, X⁆ : Subgroup G) = r := by
    have hdvd : Nat.card (⁅X, X⁆ : Subgroup G) ∣ r := by
      rw [← hZcard]
      exact card_dvd_of_le hX'Z
    rcases (Nat.dvd_prime hr.out).1 hdvd with h | h
    · exfalso
      have h1 := habX'
      rw [eq_bot_of_card_eq _ h, mem_bot] at h1
      exact habne h1
    · exact h
  obtain ⟨d, hXd, hPd⟩ := exists_card_le_pow_mul_card_inf_centralizer hp.out hpr hX hexp hPX hPel
  have hd3 : 3 ≤ d := by
    rw [hPcard, hKcard, ← pow_succ] at hPd
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hPd
    omega
  have hXcard : Nat.card X = r ^ (d + 1) := by rw [hXd, hX'card, pow_succ, mul_comm]
  have hpX : ¬ p ∣ Nat.card X := by
    rw [hXcard]
    exact fun h => hpr ((Nat.prime_dvd_prime_iff_eq hp.out hr.out).1 (hp.out.dvd_of_dvd_pow h))
  have hP1 : P ≠ ⊥ := fun h => by
    rw [h, card_bot] at hPcard
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hp.out.one_lt
    omega
  obtain ⟨H, hHP, hHcard, u, huX, huH, y₀, hy₀X, huy₀⟩ :=
    exists_hyperplane_centralizes_noncentral hPel hP1 hPX hpX ha hb hab
  have huZ : u ∉ Z := fun h => huy₀ ((mem_centralizer_iff.1 (mem_inf.1 h).2) y₀ hy₀X).symm
  have huo : orderOf u = r := orderOf_eq_prime (hexp u huX) fun h => huZ (h ▸ one_mem _)
  have hZC : ∀ w ∈ X, Z ≤ centralizer ({w} : Set G) := fun w hw z hz =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (mem_inf.1 hz).2) w hw).symm
  have hZcomm : ∀ x ∈ X, ∀ w ∈ Z, w * x = x * w := fun x hx w hw =>
    ((mem_centralizer_iff.1 (mem_inf.1 hw).2) x hx).symm
  obtain ⟨hE₀el, hE₀card⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZcard huo huZ (hZcomm u huX)
  have hE₀X : Z ⊔ zpowers u ≤ X := sup_le hZX (zpowers_le.mpr huX)
  have hHN : H ≤ M ⊓ normalizer ((Z ⊔ zpowers u : Subgroup G) : Set G) := fun h hh =>
    mem_inf.2 ⟨hPM (hHP hh), mem_normalizer_sup
      (normalizer_le_normalizer_inf_centralizer X (hPX (hHP hh)))
      (centralizer_le_normalizer_zpowers u (mem_centralizer_singleton_iff.2 (huH h hh)))⟩
  have hHcard' : Nat.card H = p ^ 3 :=
    Nat.eq_of_mul_eq_mul_right hp.out.pos (hHcard.trans (hPcard.trans (pow_succ p 3)))
  have hΓ₀ : rankThreeGamma 1 r (Z ⊔ zpowers u) ≤ M :=
    rankThreeGamma_le_of_two_lt_pRank hpr h76 (hE₀X.trans hXM) hE₀el hE₀card
      (lt_of_lt_of_le (by norm_num)
        (CFSG.SectionRank.le_pRank hp.out.one_lt hHN (hPel.mono hHP) hHcard'))
  have hcent : ∀ w ∈ Z, w ≠ 1 → normalizer (zpowers w : Set G) ≤ M := fun w hw hw1 =>
    (normalizer_zpowers_le_rankThreeGamma (mem_sup_left hw) (hexp w (hZX hw)) hw1).trans hΓ₀
  have hnc : ∀ w ∈ X, w ∉ Z → ∃ y ∈ X, w * y ≠ y * w := by
    intro w hwX hwZ
    by_contra h
    push Not at h
    exact hwZ (mem_inf.2 ⟨hwX, mem_centralizer_iff.2 fun y hy => (h y hy).symm⟩)
  have hCu : ∀ w ∈ X, w * u = u * w → w ∉ Z → normalizer (zpowers w : Set G) ≤ M := by
    intro w hwX hwu hwZ
    refine h69 _ (hE₀X.trans hXM) hE₀el hE₀card hΓ₀ w hwX (hnc w hwX hwZ) ?_
    exact le_trans (sup_le (hZC w hwX) (zpowers_le.mpr (mem_centralizer_singleton_iff.2 hwu.symm)))
      (centralizer_le_normalizer_zpowers w)
  have hgen : ∀ y ∈ X, y ∉ Z → normalizer (zpowers y : Set G) ≤ M := by
    intro y hyX hyZ
    have hidx : ∀ w ∈ X, (centralizer ({w} : Set G)).relIndex X ≤ r := fun w hw =>
      (P614I.relIndex_centralizer_le_card_commutator X w).trans
        ((card_le_of_le (commutator_mono le_rfl (zpowers_le.mpr hw))).trans hX'card.le)
    have hCidx : (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G)).relIndex X ≤ r * r :=
      relIndex_inf_le.trans (Nat.mul_le_mul (hidx u huX) (hidx y hyX))
    obtain ⟨x, hxC, hxZ⟩ : ∃ x ∈ (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G)) ⊓ X,
        x ∉ Z := by
      by_contra h
      push Not at h
      have h1 := card_le_of_le
        (show (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G)) ⊓ X ≤ Z from h)
      rw [hZcard] at h1
      have h2 : Nat.card X ≤ r * r * r := by
        rw [← relIndex_mul_card (centralizer ({u} : Set G) ⊓ centralizer ({y} : Set G)) X]
        exact Nat.mul_le_mul hCidx h1
      rw [hXcard] at h2
      have := (Nat.pow_le_pow_iff_right hr.out.one_lt).1
        (h2.trans_eq (show r * r * r = r ^ 3 by ring))
      omega
    have hxX : x ∈ X := (mem_inf.1 hxC).2
    have hxu : x ∈ centralizer ({u} : Set G) := (mem_inf.1 (mem_inf.1 hxC).1).1
    have hxy : x ∈ centralizer ({y} : Set G) := (mem_inf.1 (mem_inf.1 hxC).1).2
    have hxo : orderOf x = r := orderOf_eq_prime (hexp x hxX) fun h => hxZ (h ▸ one_mem _)
    obtain ⟨hBel, hBcard⟩ :=
      CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hZcard hxo hxZ (hZcomm x hxX)
    have hBX : Z ⊔ zpowers x ≤ X := sup_le hZX (zpowers_le.mpr hxX)
    have hBu : Z ⊔ zpowers x ≤ centralizer ({u} : Set G) :=
      sup_le (hZC u huX) (zpowers_le.mpr hxu)
    have hΓB : rankThreeGamma 1 r (Z ⊔ zpowers x) ≤ M := by
      refine rankThreeGamma_le_of_forall_normalizer_zpowers_le hM (hX.to_le hBX)
        (centralizer_le hBX hcX) hc fun w hwB hw1 => ?_
      by_cases hwZ : w ∈ Z
      · exact hcent w hwZ hw1
      · exact hCu w (hBX hwB) (mem_centralizer_singleton_iff.1 (hBu hwB)) hwZ
    refine h69 _ (hBX.trans hXM) hBel hBcard hΓB y hyX (hnc y hyX hyZ) ?_
    exact le_trans (sup_le (hZC y hyX) (zpowers_le.mpr hxy)) (centralizer_le_normalizer_zpowers y)
  refine rankThreeGamma_le_of_forall_normalizer_zpowers_le hM hX hcX hc fun y hyX hy1 => ?_
  by_cases hyZ : y ∈ Z
  · exact hcent y hyZ hy1
  · exact hgen y hyX hyZ

theorem rankThreeGamma_le_of_three_lt_pRank {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hr2 : r ≠ 2) (hpr : p ≠ r) {M X : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : PartOne.Section7.Conclusion76 M p) (h69 : SixNineAt M X r)
    (hrank : CFSG.Open.pRank r X ≤ 3) (hXM : X ≤ M) (hX : IsPGroup r X) (hnc : ¬ IsCyclic X)
    (hexp : ∀ x ∈ X, x ^ r = 1) (hcl : ⁅⁅X, X⁆, X⁆ = ⊥)
    (h3 : 3 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G))) : rankThreeGamma 1 r X ≤ M := by
  obtain ⟨P, hPN, hPel, hPcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.out.one_lt (M ⊓ normalizer (X : Set G))
  set m := CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) with hm
  have hPM : P ≤ M := hPN.trans inf_le_left
  have hPX : P ≤ normalizer (X : Set G) := hPN.trans inf_le_right
  have hKel : IsElemAbelian p (P ⊓ centralizer (X : Set G)) := hPel.mono inf_le_left
  obtain ⟨i, hi⟩ := hKel.isPGroup.exists_card_eq
  have hT1 := card_le_pow_three_mul_card_inf_centralizer hr2 hp.out hpr hX hPX hPel hrank
  rw [hPcard, hi, ← pow_add] at hT1
  have hmi : m ≤ 3 + i := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hT1
  by_cases hi2 : 2 ≤ i
  · exact PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hM h76 hXM hX
      (CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hr.out hr2 hX hnc)
      (hi2.trans (CFSG.SectionRank.le_pRank hp.out.one_lt (inf_le_inf_right _ hPM) hKel hi))
  have hi1 : i = 1 := by omega
  have hm4 : m = 4 := by omega
  have hKcard : Nat.card (P ⊓ centralizer (X : Set G) : Subgroup G) = p := by
    rw [hi, hi1, pow_one]
  obtain ⟨c, hcK, hc1⟩ := (bot_or_exists_ne_one (P ⊓ centralizer (X : Set G))).resolve_left
    fun h => by
      rw [h, card_bot] at hKcard
      exact hp.out.one_lt.ne hKcard
  have hcX : c ∈ centralizer (X : Set G) := (mem_inf.1 hcK).2
  have hc : orderOf c = p := orderOf_eq_prime (hKel.2 c hcK) hc1
  by_cases hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a
  ·
    have hXel : IsElemAbelian r X := ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hexp⟩
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hn3 : n ≤ 3 := (CFSG.SectionRank.le_pRank hr.out.one_lt le_rfl hXel hn).trans hrank
    have hn2 : 2 ≤ n :=
      (CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic hr.out hr2 hX hnc).trans
        (CFSG.SectionRank.pRank_le hr.out.one_lt fun E hEX _ => (card_le_of_le hEX).trans hn.le)
    interval_cases n
    · exact rankThreeGamma_le_of_two_lt_pRank hpr h76 hXM hXel hn (lt_trans (by norm_num) h3)
    · exact rankThreeGamma_le_of_elemAbelian_cube hpr hM h76 hXM hXel hn h3
  push Not at hab
  obtain ⟨a, ha, b, hb, hab⟩ := hab
  by_cases hZ : IsCyclic (X ⊓ centralizer (X : Set G) : Subgroup G)
  · exact rankThreeGamma_le_of_isCyclic_center hpr hM h76 h69 hXM hX hexp hcl ha hb hab hZ hPM
      hPX hPel (by rw [hPcard, hm4]) hKcard
  · exact rankThreeGamma_le_of_not_isCyclic_center hpr hM h76 h69 hrank hXM hX hexp ha hb hab hZ
      h3 hcX hc

end CFSG.LocalAnalysis.UniquenessCase.UC6R77

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOneInput
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBU3
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.OrderPrimeConj
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_two_le_of_isSU3 {X : Type} [Group X] {n : ℕ} (hX : IsSU3 X n) : 2 ≤ n := by
  rcases hX.2 with ⟨-, ⟨-, h1, -, h2⟩, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · by_contra h
    obtain rfl : n = 1 := by omega
    exact h2 rfl
  all_goals exact absurd h (by norm_num)

theorem uc22ine229_pRank_le_one_of_isSU3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : IsSU3 X n) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : ¬ q ∣ 2 ^ n + 1)
    (hZ : ¬ q ∣ Nat.card (center X)) : CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 := by
  apply CFSG.SectionRank.pRank_le hq.one_lt
  intro E _ hE
  have hdisj : Disjoint E (MulAut.conj : X →* MulAut X).ker := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxk
    have hxZ : x ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut X => f g) (MonoidHom.mem_ker.1 hxk)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    rcases (Nat.dvd_prime hq).1 (orderOf_dvd_of_pow_eq_one (hE.2 x hxE)) with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (by rw [← h]; exact Subgroup.orderOf_dvd_natCard _ hxZ) hZ
  rw [pow_one, ← UC6S846.card_map_of_disjoint_ker _ _ hdisj]
  exact UCK.u3RankOne X n hX q hq hq2 hqn _ (Subgroup.map_le_range _ _)
    (CFSG.SectionRank.isElemAbelian_map hE _)

theorem uc22ine229_exists_involution_of_cartan (hC : uc22pwCartanSU3) {M Y : Subgroup G}
    (hY : Y ∈ calC M) {n : ℕ} (hn : 2 < n) (hX : IsSU3 (Bar2 Y) n) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 Y)) ≤ 1) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) : ∃ t ∈ Y ⊓ normalizer (X : Set G), orderOf t = 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨U⟩ : Nonempty (Sylow 2 (Bar2 Y)) := inferInstance
  obtain ⟨e, m', hm', hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  obtain ⟨E, -, -, -, -, hπ, -, -, w, hw2, hwE, -⟩ := hC (Bar2 Y) hX.1 n hn hX U Unit
    (IsPGroup.of_card (n := 0) (by simp)) 1 (fun _ _ => Iff.rfl) e m' hm' hnm
  have hqE : q ∣ Nat.card E := by
    have h : q ∈ piSet E := hπ ▸ (⟨hq, hqn⟩ : q ∈ etaSet n)
    exact h.2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqE
  have hZc : Nat.card (zpowers (x : Bar2 Y)) = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isConj_of_natCard_eq_prime_of_sylow_cyclic
      (fun Q => RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hq2 hrank Q) hZc
      (uc22ine229_card_map hXY hq hq2 hXc)
  have hwZ : w ∈ normalizer ((zpowers (x : Bar2 Y)) : Set (Bar2 Y)) := by
    rw [UC6S846.mem_normalizer_iff_map_conj, MonoidHom.map_zpowers]
    show zpowers (w * (x : Bar2 Y) * w⁻¹) = _
    rw [hwE x x.2, Subgroup.zpowers_inv]
  have hw' : MulAut.conj g w ∈ normalizer
      (((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) : Set (Bar2 Y)) := by
    rw [← hg, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hwZ
  have hw1 : MulAut.conj g w ≠ 1 := by
    intro h
    have hw : w = 1 := (MulAut.conj g).injective (h.trans (map_one _).symm)
    have h1 := hwE x x.2
    rw [hw, one_mul, inv_one, mul_one] at h1
    have h2 : (x : Bar2 Y) ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [Subgroup.orderOf_coe, hx] at h3
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h3)
  obtain ⟨y, hyN, hy⟩ := uc22ine229_exists_lift hXY hq hq2
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])) hw'
  have h2 : y ^ 2 ∈ CFSG.pCore 2 ↥Y := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥Y), MonoidHom.mem_ker, map_pow, hy,
      MulAut.conj_apply, conj_pow, hw2, mul_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y) ⟨y ^ 2, h2⟩
  have hyk : (y : G) ^ 2 ^ (k + 1) = 1 := by
    have h : (y ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h' : y ^ 2 ^ (k + 1) = 1 := by
      rw [pow_succ', pow_mul]
      exact h
    simpa using congrArg Subtype.val h'
  have hy1 : (y : G) ≠ 1 := by
    intro h
    apply hw1
    rw [← hy, show y = 1 from Subtype.ext h, map_one]
  exact ⟨_, pow_mem (show (y : G) ∈ Y ⊓ normalizer (X : Set G) from ⟨y.2, hyN⟩) _,
    uc22ine229_orderOf_pow_eq_prime Nat.prime_two hy1 hyk⟩

theorem uc22ine229_exists_involution_of_isSU3 (hG : GriessAllModelsStatement)
    (hC : uc22pwCartanSU3) {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ} (hX : IsSU3 (Bar2 Y) n)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) : ∃ t ∈ Y ⊓ normalizer (X : Set G), orderOf t = 2 := by
  have hrank := uc22ine229_pRank_le_one_of_isSU3 hX hq hq2
    (uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn)
    (uc22ine229_not_dvd_card_center hG hX hq hq2 hqn)
  by_cases h3 : q = 3
  · subst h3
    exact uc22ine229_exists_involution_of_three hY hrank hXY hXc
  have hn : 2 < n := by
    have h2n := uc22ine229_two_le_of_isSU3 hX
    by_contra h
    obtain rfl : n = 2 := by omega
    have h3' : q ∣ 3 := hqn
    exact h3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3')
  exact uc22ine229_exists_involution_of_cartan hC hY hn hX hq hq2 hqn hrank hXY hXc

end CFSG.LocalAnalysis.UniquenessCase.UC22

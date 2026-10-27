module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212Center
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint.Multiplier (genericOrders)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_exists_prime_seven_le {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≠ 4) :
    ∃ r : ℕ, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ n - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
    · have hdvd : 2 ^ m - 1 ∣ 2 ^ (m + m) - 1 := by
        have h := Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 2
        rwa [one_pow, ← pow_mul, mul_two] at h
      by_cases hm4 : m = 4
      · subst hm4
        exact ⟨17, by norm_num, by norm_num, by norm_num⟩
      · obtain ⟨r, hr, hr7, hrd⟩ := ih m (by omega) (by omega) hm4
        exact ⟨r, hr, hr7, hrd.trans hdvd⟩
    · obtain ⟨r, hr, hr5, hrd⟩ := CFSG.exists_prime_five_le_dvd_two_pow_sub_one hn3
      refine ⟨r, hr, ?_, hrd⟩
      rcases (by omega : r = 5 ∨ r = 6 ∨ 7 ≤ r) with rfl | rfl | h
      · exact absurd hrd (uc22p20v_not_five_dvd_sub_one hodd)
      · exact absurd hr (by norm_num)
      · exact h

theorem uc22s2112r34_not_dvd_genericOrders {t : StatedLieTag} {n p f s : ℕ}
    (htn : FunTwoType t n ∨ ((t = .PSL ∨ t = .PSU) ∧ n = 3)) (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ (genericOrders t n p f).1 := by
  intro h
  have hn : ∀ t' : StatedLieTag, t' = .PSL ∨ t' = .PSU → t = t' → 0 < n ∧ n ≤ 5 := by
    rintro t' ht' rfl
    rcases htn with h2 | ⟨-, h3⟩
    · rcases ht' with rfl | rfl <;> simp only [FunTwoType] at h2 <;> omega
    · omega
  rcases CFSG.LocalAnalysis.RankFourTheoremC.eq_psl_or_psu_of_dvd_genericOrders hs (by omega)
    t n p f h with ⟨rfl, hsn, -⟩ | ⟨rfl, hsn, -⟩
  · obtain ⟨h0, h5⟩ := hn .PSL (Or.inl rfl) rfl
    exact absurd (Nat.le_of_dvd h0 hsn) (by omega)
  · obtain ⟨h0, h5⟩ := hn .PSU (Or.inr rfl) rfl
    exact absurd (Nat.le_of_dvd h0 hsn) (by omega)

theorem uc22s2112r34_not_mem_sig {D : Data G} {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {s : ℕ}
    (hs : s ∈ piSet c.B0) : s ∉ D.sig := fun hsσ => by
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hs
  exact uc22s217v_not_sp D Ch hH c hb hs.1 hbo
    (UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hsσ)

theorem uc22s2112r34_pRank_le_three {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {s : ℕ} (hs : s ∈ piSet c.B0) (hs2 : s ≠ 2) :
    CFSG.Open.pRank s D.M ≤ 3 :=
  Nat.le_of_not_lt fun h4 =>
    uc22s2112r34_not_mem_sig hσ hH c hL hs (hσ.four_mem s hs.1 hs2 h4)

theorem uc22s2112r34_exists_prime_mem_piSet {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hpσ : p ∈ D.sig) :
    ∃ r : ℕ, r ∈ piSet c.B0 ∧ r ≠ p ∧ 5 ≤ r ∧ (c.n ≠ 4 → 7 ≤ r) := by
  have hmem : ∀ {r : ℕ}, r.Prime → r ∣ 2 ^ c.n - 1 → r ∈ piSet c.B0 := fun hr hrd => by
    rw [c.hpi]
    exact ⟨hr, hrd⟩
  have hne : ∀ {r : ℕ}, r ∈ piSet c.B0 → r ≠ p := fun hr hrp =>
    uc22s2112r34_not_mem_sig hσ hH c hL hr (hrp ▸ hpσ)
  by_cases hn4 : c.n = 4
  · have h5 : (5 : ℕ) ∈ piSet c.B0 := hmem (by norm_num) (by rw [hn4]; norm_num)
    exact ⟨5, h5, hne h5, le_rfl, fun h => absurd hn4 h⟩
  · obtain ⟨r, hr, hr7, hrd⟩ := uc22s2112r34_exists_prime_seven_le hn3 hn4
    exact ⟨r, hmem hr hrd, hne (hmem hr hrd), by omega, fun _ => hr7⟩

theorem uc22s2112r34_exists_mem_orderOf {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) (hn4 : c.n ≠ 4)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hpσ : p ∈ D.sig) :
    ∃ b ∈ c.B0, ∃ s : ℕ, s.Prime ∧ 7 ≤ s ∧ s ≠ p ∧ orderOf b = s := by
  obtain ⟨s, hs, hsp, -, hs7⟩ := uc22s2112r34_exists_prime_mem_piSet hσ hH c hn3 hL hpσ
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hs
  exact ⟨b, hb, s, hs.1, hs7 hn4, hsp, hbo⟩

omit [Finite G] in
theorem uc22s2112r34_mem_normalizer_map {L T : Subgroup G} {b : G}
    (hbL : b ∈ normalizer (L : Set G)) (hbT : b ∈ normalizer (T : Set G)) {x : BarInf L}
    (hx : inducedBarInfAutHom L ⟨b, hbL⟩ = MulAut.conj x) :
    x ∈ normalizer ((((T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) : Subgroup (BarInf L)) : Set (BarInf L)) := by
  set P : Subgroup (BarInf L) :=
    ((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) with hP
  have key : ∀ (g : G) (hgL : g ∈ normalizer (L : Set G)), g ∈ normalizer (T : Set G) →
      ∀ y ∈ P, inducedBarInfAutHom L ⟨g, hgL⟩ y ∈ P := by
    intro g hgL hgT y hy
    obtain ⟨l, hl, rfl⟩ := mem_map.1 hy
    refine mem_map.2 ⟨L.normalizerMonoidHom ⟨g, hgL⟩ l, ?_, rfl⟩
    rw [mem_subgroupOf] at hl ⊢
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 hgT _).1 (mem_inf.1 hl).1,
      (L.normalizerMonoidHom ⟨g, hgL⟩ l).2⟩
  have hbL' : b⁻¹ ∈ normalizer (L : Set G) := inv_mem hbL
  have hinv : inducedBarInfAutHom L ⟨b⁻¹, hbL'⟩ = MulAut.conj x⁻¹ := by
    rw [map_inv MulAut.conj, ← hx, ← map_inv]
    rfl
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h := key b hbL hbT y hy
    rwa [hx, MulAut.conj_apply] at h
  · intro hy
    have h := key b⁻¹ hbL' (inv_mem hbT) _ hy
    rw [hinv, MulAut.conj_apply] at h
    have he : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
    rwa [he] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22

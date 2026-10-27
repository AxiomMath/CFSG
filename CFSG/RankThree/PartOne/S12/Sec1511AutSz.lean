module

public import CFSG.RankThree.PartOne.K159.AutSzIso
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.K159.SzAbs CFSG.RankThree.PartOne.StrongP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace Sec1511

theorem orderModC_of_prime {H : Type*} [Group H] (B : Subgroup H) {n : H} {r : ℕ} (hr : r.Prime)
    (h1 : n ^ r ∈ Subgroup.centralizer (B : Set H)) (h2 : n ∉ Subgroup.centralizer (B : Set H)) :
    OrderModC B n r := by
  refine ⟨hr.pos, h1, fun k hk0 hkr hck => h2 ?_⟩
  have hcop : Nat.Coprime k r := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 fun hd => ?_)
    have := Nat.le_of_dvd hk0 hd
    omega
  have hbez := Nat.gcd_eq_gcd_ab k r
  rw [hcop.gcd_eq_one] at hbez
  have hn : n = (n ^ k) ^ (Nat.gcdA k r) * (n ^ r) ^ (Nat.gcdB k r) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (k : ℤ) * Nat.gcdA k r + (r : ℤ) * Nat.gcdB k r = 1 := by simpa using hbez.symm
    rw [this, zpow_one]
  rw [hn]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hck _) (Subgroup.zpow_mem _ h1 _)

theorem sz_row_exact {H : Type} [Group H]
    [Finite H] {S : Subgroup H} [hSn : S.Normal] (hsimple : IsSimpleGroup ↥S)
    (hiso : Census3.IsoLie ↥S (.suzuki 2)) (hC : Subgroup.centralizer (S : Set H) = ⊥)
    {P : Subgroup H} (hP : IsSylowOf 5 P ⊤) (hΩel : IsElementaryAbelian 5 (omegaOne 5 P))
    (hΩ : Nat.card (omegaOne 5 P) = 25 ∨ Nat.card (omegaOne 5 P) = 125) :
    Nat.card (omegaOne 5 P) = 25 ∧
      ∃ g ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H),
        OrderModC (omegaOne 5 P) g 5 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSz := szSylow_of_isoLie hiso
  have hP' : CFSG.ABGLocalTools.IsSylowOf 5 P ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.2 hP
  set E : Subgroup H := omegaOne 5 P with hE
  have hEP : E ≤ P := (Subgroup.closure_le _).2 fun _ hx => hx.1
  have hPp : IsPGroup 5 P := hP.2.1
  set T : Subgroup H := P ⊓ S with hT
  have hTS : T ≤ S := inf_le_right
  have hTP : T ≤ P := inf_le_left
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 5 T S :=
    hP'.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.2 hSn])
  have hTcard : Nat.card T = 25 := by
    rw [hTsyl.card_eq, hSz.card, factorization_five]
    norm_num
  obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hcycQ : IsCyclic ↥(T.subgroupOf S) := by
    have h1 : IsCyclic ↥(Q : Subgroup ↥S) := hSz.cyclic Q
    rwa [hQ] at h1
  have hcycT : IsCyclic ↥T := (Subgroup.subgroupOfEquivOfLe hTS).isCyclic.1 hcycQ
  have hTnE : ¬ T ≤ E := by
    intro hTE
    obtain ⟨g, hg⟩ := hcycT.exists_generator
    have hord25 : orderOf g = 25 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg]
      exact hTcard
    have hg5 : (g : H) ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) (g : H) (hTE g.2)
    have hg5' : g ^ 5 = 1 := Subtype.ext (by simpa using hg5)
    have := orderOf_dvd_of_pow_eq_one hg5'
    rw [hord25] at this
    omega
  have hout : Nat.card (Outer ↥S) ∣ 5 := by
    have h := CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥S 2 5
      (CTP.suzukiModel_of_isoLie 2 hiso)
    exact h.1.2.1
  have hHS : Nat.card (H ⧸ S) ≤ 5 :=
    (CTP.card_quotient_le_outer S hC).trans (Nat.le_of_dvd (by norm_num) hout)
  have hPcard : Nat.card P ≤ 125 := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_subgroup_dvd_card P
    have h2 : Nat.card H = 32537600 * Nat.card (H ⧸ S) := by
      rw [← hSz.card]
      exact (Subgroup.card_mul_index S).symm
    have hm0 : 0 < Nat.card (H ⧸ S) := Nat.card_pos
    rw [ha, h2] at h1
    have ha3 : a ≤ 3 := by
      by_contra hcon
      have h625 : 5 ^ 4 ∣ 5 ^ a := pow_dvd_pow 5 (by omega)
      have h3 := h625.trans h1
      generalize Nat.card (H ⧸ S) = m at hHS hm0 h3
      interval_cases m <;> omega
    rw [ha]
    calc 5 ^ a ≤ 5 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
      _ = 125 := by norm_num
  have hE25 : Nat.card E = 25 := by
    rcases hΩ with h | h
    · exact h
    · exfalso
      have hEP' : E = P := Subgroup.eq_of_le_of_card_ge hEP (by rw [h]; exact hPcard)
      exact hTnE (hEP' ▸ hTP)
  refine ⟨hE25, ?_⟩
  have hEnT : ¬ E ≤ T := by
    intro hET
    have hEqT : E = T := Subgroup.eq_of_le_of_card_ge hET (by rw [hTcard, hE25])
    exact hTnE hEqT.symm.le
  have hnc : ∃ t ∈ T, t ∉ Subgroup.centralizer (E : Set H) := by
    by_contra hcon
    push Not at hcon
    have hTcomm : ∀ t ∈ T, ∀ e ∈ E, t * e = e * t := fun t ht e he =>
      (Subgroup.mem_centralizer_iff.1 (hcon t ht) e he).symm
    set P' : Subgroup H := T ⊔ E with hP'
    have hP'P : P' ≤ P := sup_le hTP hEP
    have hP'p : IsPGroup 5 P' := hPp.to_le hP'P
    have hTP' : T ≤ P' := le_sup_left
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP'p
    have hgt : 25 < Nat.card P' := by
      by_contra hle
      push Not at hle
      have : T = P' := Subgroup.eq_of_le_of_card_ge hTP' (by rw [hTcard]; exact hle)
      exact hEnT (this ▸ (le_sup_right : E ≤ T ⊔ E))
    have h125 : 125 ∣ Nat.card P' := by
      rw [hn] at hgt ⊢
      have h3 : 3 ≤ n := by
        by_contra h
        push Not at h
        interval_cases n <;> omega
      have := pow_dvd_pow 5 h3
      simpa using this
    have hcomm : ∀ x ∈ P', ∀ t ∈ T, x * t = t * x := by
      have hle : P' ≤ Subgroup.centralizer (T : Set H) := by
        refine sup_le ?_ ?_
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          have : (⟨t, ht⟩ : ↥T) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨t, ht⟩ := by
            let _ := hcycT.commGroup
            exact mul_comm _ _
          exact congrArg Subtype.val this
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          exact hTcomm t ht x hx
      intro x hx t ht
      exact (Subgroup.mem_centralizer_iff.1 (hle hx) t ht).symm
    exact sz_core hSz hsimple hC hTS hTcard hP'p hTP' h125 hcomm
  obtain ⟨t, htT, htC⟩ := hnc
  have htP : t ∈ P := hTP htT
  obtain ⟨k, hk⟩ := hPp ⟨t, htP⟩
  have htk : t ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ j : ℕ, t ^ (5 ^ j) ∈ Subgroup.centralizer (E : Set H) :=
    ⟨k, by rw [htk]; exact Subgroup.one_mem _⟩
  set j := Nat.find hex with hj
  have hjmem : t ^ (5 ^ j) ∈ Subgroup.centralizer (E : Set H) := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hjmem
    exact htC hjmem
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have himin : t ^ (5 ^ i) ∉ Subgroup.centralizer (E : Set H) :=
    Nat.find_min hex (by omega)
  refine ⟨t ^ (5 ^ i), ?_, orderModC_of_prime E (by norm_num) ?_ himin⟩
  · exact Subgroup.pow_mem _ (mem_normalizer_omegaOne_of_mem htP) _
  · rw [← pow_mul, ← pow_succ]
    rw [hi] at hjmem
    exact hjmem

end Sec1511

end CFSG.RankThree.PartOne

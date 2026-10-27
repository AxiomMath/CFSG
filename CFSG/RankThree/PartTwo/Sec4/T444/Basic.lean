module

import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section General

variable {G : Type*} [Group G] [Finite G]

theorem not_three_dvd_card_of_isPGroup_two {X : Subgroup G} (hX : IsPGroup 2 X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  intro h
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)

theorem not_three_dvd_card_inSubgroup_pPrimeCore (H : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (CFSG.pPrimeCore 3) H) := by
  rw [inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

omit [Finite G] in
theorem le_normalizer_inSubgroup_pPrimeCore (H : Subgroup G) :
    H ≤ Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore 3) H : Set G) := by
  have h := Subgroup.le_normalizer_map (H := CFSG.pPrimeCore 3 H) H.subtype
  rwa [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h

omit [Finite G] in
theorem le_inSubgroup_pPrimeCore {X H : Subgroup G} (hXH : X ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ 3 ∣ Nat.card X) :
    X ≤ inSubgroup (CFSG.pPrimeCore 3) H := by
  have hn : (X.subgroupOf H).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hnorm h.2) x).mp hx
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card (X.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX
  have hle : X.subgroupOf H ≤ CFSG.pPrimeCore 3 H := le_sSup ⟨hn, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hXH]
  exact Subgroup.map_mono hle

omit [Finite G] in
theorem le_pPrimeCore_of_normal {X : Subgroup G} (hX : X.Normal) (h3 : ¬ 3 ∣ Nat.card X) :
    X ≤ CFSG.pPrimeCore 3 G :=
  le_sSup ⟨hX, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩

theorem not_three_dvd_card_pPrimeCore : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 G) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card

theorem two_le_pRank_of_le {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hBA : B ≤ A) (hB : Nat.card B = 3 ^ 2) : 2 ≤ CFSG.Open.pRank 3 B :=
  Sec5.le_pRank_of_elemAbelian Nat.prime_three le_rfl (Sec5.isElemAbelian_of_le hA hBA) hB

theorem le_of_le_normalizer_of_gamma_le {A M : Subgroup G} (hA : Late.IsE27 A)
    (hM : gamma 2 A ≤ M) {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX : ¬ 3 ∣ Nat.card X) : X ≤ M :=
  Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
    (by rw [hA.2]; norm_num) hAX ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hX)
    fun B hBA hB => inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      ((normalizer_le_gamma hBA (two_le_pRank_of_le hA.1 hBA hB)).trans hM))

theorem map_starQuot_ne_bot_iff {G : Type} [Group G] [Finite G] {Q : Subgroup G} :
    Q.map (starQuot G) ≠ ⊥ ↔ ¬ Q ≤ CFSG.pPrimeCore 3 G := by
  rw [Ne, Subgroup.map_eq_bot_iff, starQuot, QuotientGroup.ker_mk']

theorem exists_sylow_le_normalizer {A Q : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) (r : ℕ) [Fact r.Prime] :
    ∃ S : Sylow r Q,
      A ≤ Subgroup.normalizer (((S : Subgroup Q).map Q.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 r
    hA hQ (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  refine ⟨S, fun a ha => ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  conv_rhs => rw [← hS ⟨a, ha⟩]
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem Ctx444.le (h : Ctx444 G A M) : A ≤ M :=
  h.isE27.le_gamma.trans h.gamma_le

theorem Ctx444.le_of_le_normalizer (h : Ctx444 G A M) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ 3 ∣ Nat.card X) : X ≤ M :=
  le_of_le_normalizer_of_gamma_le h.isE27 h.gamma_le hAX hX

theorem Ctx444.pPrimeCore_le (h : Ctx444 G A M) : CFSG.pPrimeCore 3 G ≤ M :=
  h.le_of_le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    not_three_dvd_card_pPrimeCore

theorem Ctx444.pPrimeCore_le_inSubgroup (h : Ctx444 G A M) :
    CFSG.pPrimeCore 3 G ≤ inSubgroup (CFSG.pPrimeCore 3) M :=
  le_inSubgroup_pPrimeCore h.pPrimeCore_le
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; trivial) not_three_dvd_card_pPrimeCore

theorem Ctx444.le_normalizer_inSubgroup (h : Ctx444 G A M) :
    A ≤ Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore 3) M : Set G) :=
  h.le.trans (le_normalizer_inSubgroup_pPrimeCore M)

theorem Ctx444.pCoreOf_eq_of_pPrimeCore_eq (h : Ctx444 G A M)
    (hPQ : CFSG.pPrimeCore 3 G = inSubgroup (CFSG.pPrimeCore 3) M) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) = CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pPrimeCore 3 G with hP
  apply le_antisymm
  ·
    have hn : (⊤ : Subgroup G) ≤ Subgroup.normalizer
        (CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
    have h2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup G)
    have hnormal : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup G)).Normal :=
      ⟨fun x hx g => by
        have := (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_top g)) x).mp hx
        simpa using this⟩
    have hleP : CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) ≤ P :=
      le_pPrimeCore_of_normal hnormal (not_three_dvd_card_of_isPGroup_two h2)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hleP.trans h.pPrimeCore_le)
      (le_top.trans hn) h2
  ·
    have h2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
    have hnM : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    have hleQ : CFSG.Open.pCoreOf 2 M ≤ inSubgroup (CFSG.pPrimeCore 3) M :=
      le_inSubgroup_pPrimeCore (CFSG.LieType.BorelTits.pCoreOf_le 2 M) hnM
        (not_three_dvd_card_of_isPGroup_two h2)
    rw [← hPQ] at hleQ
    have hleOP : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hleQ
        (h.pPrimeCore_le.trans hnM) h2
    have hnP : (⊤ : Subgroup G) ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 P : Set G) := by
      refine le_top.trans ?_
      rw [← Subgroup.normalizer_eq_top (H := P)]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P
    exact hleOP.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hnP
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P))

theorem Ctx444.pPrimeCore_ne_of_top_mem (h : Ctx444 G A M) (hG : ⊤ ∈ Late.scriptH₀ A M) :
    CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M := by
  intro hPQ
  apply hG.2.2
  rw [top_inf_eq]
  exact h.pCoreOf_eq_of_pPrimeCore_eq hPQ

theorem Ctx444.not_le_pPrimeCore (h : Ctx444 G A M)
    (hor : CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M ∨ ⊤ ∈ Late.scriptH₀ A M) :
    ¬ inSubgroup (CFSG.pPrimeCore 3) M ≤ CFSG.pPrimeCore 3 G := by
  have hne : CFSG.pPrimeCore 3 G ≠ inSubgroup (CFSG.pPrimeCore 3) M :=
    hor.elim id h.pPrimeCore_ne_of_top_mem
  exact fun hle => hne (le_antisymm h.pPrimeCore_le_inSubgroup hle)

end Ctx

end CFSG.RankThree.PartTwo.Sec4

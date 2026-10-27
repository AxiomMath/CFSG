module

public import CFSG.RankThree.PartTwo.KFacts.KS116
public import CFSG.RankThree.PartTwo.Sec11.SimsR1BlackburnSmall
public import CFSG.RankThree.PartTwo.Sec11.SimsR1BlackburnOmega
public import CFSG.RankThree.PartTwo.Sec11.SimsR1BlackburnOut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

private theorem frattini_le_of_comm_pow {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (N : Subgroup P) (hc : ∀ x y : P, ⁅x, y⁆ ∈ N)
    (hpow : ∀ x : P, x ^ p ∈ N) : frattini P ≤ N := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := p)]
  refine (closure_le _).2 ?_
  rintro x (hx | ⟨y, rfl⟩)
  · exact (commutator_le.2 fun a _ b _ => hc a b : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ N) hx
  · exact hpow y

private theorem eq_of_lt_of_card_mul {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {A B K : Subgroup G} (hAB : A < B) (hBK : B ≤ K) (hA : Nat.card A * p = Nat.card K) :
    B = K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAB.le
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hBdvd : Nat.card B ∣ Nat.card K := Subgroup.card_dvd_of_le hBK
  rw [hm, ← hA] at hBdvd
  rcases (Nat.dvd_prime hp).1 ((Nat.mul_dvd_mul_iff_left hApos).1 hBdvd) with h | h
  · exact absurd (Subgroup.eq_of_le_of_card_ge hAB.le (le_of_eq (by rw [hm, h, mul_one]))) hAB.ne
  · exact Subgroup.eq_of_le_of_card_ge hBK (le_of_eq (by rw [hm, h, hA]))

private theorem exists_zpowers_eq {P : Type*} [Group P] {C : Subgroup P} (hC : IsCyclic C) :
    ∃ c : P, C = zpowers c := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  refine ⟨g, le_antisymm (fun y hy => ?_) (zpowers_le.2 g.2)⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨y, hy⟩)
  exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem relIndex_zpowers_dvd {p : ℕ} {P : Type*} [Group P] (F : Subgroup P) [F.Normal]
    (c : P) (hc : c ^ p ∈ F) : F.relIndex (zpowers c) ∣ p := by
  let N : Subgroup (zpowers c) := F.subgroupOf (zpowers c)
  let g : zpowers c := ⟨c, mem_zpowers c⟩
  have hgen : ∀ y : zpowers c ⧸ N, y ∈ zpowers (QuotientGroup.mk g : zpowers c ⧸ N) := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simpa [g] using hk))
  have h1 : Nat.card (zpowers c ⧸ N) = orderOf (QuotientGroup.mk g : zpowers c ⧸ N) :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).symm
  have h2 : (QuotientGroup.mk g : zpowers c ⧸ N) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hc
  change Nat.card (zpowers c ⧸ N) ∣ p
  rw [h1]
  exact orderOf_dvd_of_pow_eq_one h2

private theorem card_zpowers_sup_center {p : ℕ} (hp : p.Prime) {D : Type*} [Group D] [Finite D]
    (hexp : ∀ x : D, x ^ p = 1) (hcZ : Nat.card (center D) = p) {w : D} (hw : w ∉ center D) :
    Nat.card ↥(zpowers w ⊔ center D) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hw1 : w ≠ 1 := fun h => hw (h ▸ one_mem _)
  have hord : orderOf w = p := orderOf_eq_prime (hexp w) hw1
  have hzp : Nat.card (zpowers w) = p := by rw [Nat.card_zpowers, hord]
  have hrel : (center D).relIndex (zpowers w) = p := by
    have hdvd : (center D).relIndex (zpowers w) ∣ p := by
      rw [← hzp]
      exact Subgroup.index_dvd_card _
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd ((Subgroup.relIndex_eq_one.1 h) (mem_zpowers w)) hw
    · exact h
  have h2 : (center D).relIndex (zpowers w ⊔ center D) = p := by
    rw [Subgroup.relIndex_sup_right, hrel]
  have h3 : ((center D).subgroupOf (zpowers w ⊔ center D)).index *
      Nat.card ((center D).subgroupOf (zpowers w ⊔ center D)) =
        Nat.card ↥(zpowers w ⊔ center D) := Subgroup.index_mul_card _
  have h4 : Nat.card ((center D).subgroupOf (zpowers w ⊔ center D)) = Nat.card (center D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [← h3, h4, hcZ]
  change (center D).relIndex (zpowers w ⊔ center D) * p = p ^ 2
  rw [h2]
  ring

private theorem exists_two_gen {p : ℕ} (hp : p.Prime) {D : Type*} [Group D] [Finite D]
    (hcard : Nat.card D = p ^ 3) (hexp : ∀ x : D, x ^ p = 1) (hcZ : Nat.card (center D) = p) :
    ∃ u₁ u₂ : D, zpowers u₁ ⊔ center D ⊔ zpowers u₂ = ⊤ := by
  have hp1 := hp.one_lt
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : D, u₁ ∉ center D := by
    by_contra h
    push Not at h
    have htop : center D = ⊤ := top_unique fun x _ => h x
    rw [htop, Subgroup.card_top, hcard] at hcZ
    have : p < p ^ 3 := by simpa using Nat.pow_lt_pow_right hp1 (show 1 < 3 by norm_num)
    omega
  have hA : Nat.card ↥(zpowers u₁ ⊔ center D) = p ^ 2 :=
    card_zpowers_sup_center hp hexp hcZ hu₁
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : D, u₂ ∉ zpowers u₁ ⊔ center D := by
    by_contra h
    push Not at h
    have htop : zpowers u₁ ⊔ center D = ⊤ := top_unique fun x _ => h x
    rw [htop, Subgroup.card_top, hcard] at hA
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  refine ⟨u₁, u₂, eq_of_lt_of_card_mul hp (A := zpowers u₁ ⊔ center D) (K := ⊤) ?_ le_top ?_⟩
  · exact lt_of_le_of_ne le_sup_left fun h => hu₂ (h ▸ mem_sup_right (mem_zpowers u₂))
  · rw [hA, Subgroup.card_top, hcard]
    ring

private theorem exists_two_gen_le {p : ℕ} (hp : p.Prime) {P : Type} [Group P] [Finite P]
    (E : Subgroup P) (hEcard : Nat.card E = p ^ 3) (hEexp : Monoid.exponent E = p)
    (hcZ : Nat.card (center E) = p) :
    ∃ u₁ ∈ E, ∃ u₂ ∈ E, E ≤ zpowers u₁ ⊔ zpowers u₂ ⊔ (center E).map E.subtype := by
  have hexp : ∀ x : E, x ^ p = 1 := fun x => by
    rw [← hEexp]
    exact Monoid.pow_exponent_eq_one x
  obtain ⟨u₁, u₂, hu⟩ := exists_two_gen hp hEcard hexp hcZ
  refine ⟨u₁, u₁.2, u₂, u₂.2, ?_⟩
  have hE : (⊤ : Subgroup E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := congrArg (Subgroup.map E.subtype) hu
  rw [hE, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h
  exact h.ge.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    (le_sup_right.trans le_sup_left))

private theorem commutator_le_center_of_isExtraspecial {p : ℕ} (E : Type*) [Group E]
    [IsExtraspecial p E] : _root_.commutator E ≤ center E := by
  haveI : IsElementaryAbelian p (E ⧸ center E) := IsExtraspecial.quotient_elementary_abelian p E
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance

theorem blackburn_of_extraspecial {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {P : Type} [Group P]
    [Finite P] (hP : IsPGroup p P) (E : Subgroup P) [E.Characteristic] [IsExtraspecial p E]
    (hEcard : Nat.card E = p ^ 3) (hEexp : Monoid.exponent E = p)
    (hC : IsCyclic (centralizer (E : Set P))) :
    (∃ s : Finset P, s.card ≤ 3 ∧ Subgroup.closure (s : Set P) = ⊤) ∧
      ((∀ s : Finset P, s.card ≤ 2 → Subgroup.closure (s : Set P) ≠ ⊤) →
        ∃ Z₀ : Subgroup P, Z₀.Characteristic ∧ frattini P ≤ Z₀ ∧
          (frattini P).relIndex Z₀ = p) := by
  classical
  have hpp : p.Prime := Fact.out
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  have hcZ : Nat.card (center E) = p := IsExtraspecial.center_order_p p E
  have hEpow : ∀ e ∈ E, e ^ p = 1 := by
    intro e he
    have h := Monoid.pow_exponent_eq_one (⟨e, he⟩ : E)
    rw [hEexp] at h
    simpa using congrArg Subtype.val h
  set C : Subgroup P := centralizer (E : Set P)
  haveI hCchar : C.Characteristic := inferInstance
  obtain ⟨c, hcC⟩ := exists_zpowers_eq hC
  have hEC : ∀ e ∈ E, ∀ y ∈ C, e * y = y * e := fun e he y hy => mem_centralizer_iff.1 hy e he
  have hZC : (center E).map E.subtype ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_centralizer_iff.2 fun h hh => congrArg Subtype.val ((mem_center_iff.1 hz) ⟨h, hh⟩)
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, ⁅a, b⁆ ∈ C := by
    intro a ha b hb
    have hce : ⁅(⟨a, ha⟩ : E), (⟨b, hb⟩ : E)⁆ ∈ center E :=
      commutator_le_center_of_isExtraspecial (p := p) E
        (commutator_mem_commutator (mem_top _) (mem_top _))
    exact hZC ⟨_, hce, map_commutatorElement E.subtype ⟨a, ha⟩ ⟨b, hb⟩⟩
  by_cases hH : E ⊔ C = ⊤
  ·
    obtain ⟨u₁, -, u₂, -, hgen⟩ := exists_two_gen_le hpp E hEcard hEexp hcZ
    have htop : zpowers u₁ ⊔ zpowers u₂ ⊔ C = ⊤ := by
      have h : E ⊔ C ≤ zpowers u₁ ⊔ zpowers u₂ ⊔ C :=
        sup_le (hgen.trans (sup_le_sup_left hZC _)) le_sup_right
      rw [hH] at h
      exact top_unique h
    have hdec : ∀ x : P, ∃ e ∈ E, ∃ y ∈ C, e * y = x := fun x =>
      mem_sup_of_normal_right.1 (by rw [hH]; exact mem_top x)
    refine ⟨⟨{u₁, u₂, c}, Finset.card_le_three, ?_⟩, fun hno => ?_⟩
    · refine top_unique ?_
      rw [← htop]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact zpowers_le.2 (subset_closure (by simp))
      · exact zpowers_le.2 (subset_closure (by simp))
      · rw [hcC]
        exact zpowers_le.2 (subset_closure (by simp))
    · have hΦC : frattini P ≤ C := by
        refine frattini_le_of_comm_pow hP C ?_ ?_
        · intro x y
          obtain ⟨e₁, he₁, y₁, hy₁, rfl⟩ := hdec x
          obtain ⟨e₂, he₂, y₂, hy₂, rfl⟩ := hdec y
          have hk : ∀ g : P, QuotientGroup.mk' C g = 1 ↔ g ∈ C := fun g =>
            QuotientGroup.eq_one_iff g
          refine (hk _).1 ?_
          rw [map_commutatorElement, map_mul, map_mul, (hk y₁).2 hy₁, (hk y₂).2 hy₂, mul_one,
            mul_one, ← map_commutatorElement]
          exact (hk _).2 (hcomm e₁ he₁ e₂ he₂)
        · intro x
          obtain ⟨e, he, y, hy, rfl⟩ := hdec x
          rw [(show Commute e y from hEC e he y hy).mul_pow, hEpow e he, one_mul]
          exact C.pow_mem hy p
      refine ⟨C, hCchar, hΦC, ?_⟩
      have hcp : c ^ p ∈ frattini P := CFSG.pth_power_mem_frattini_of_isPGroup c
      have hdvd : (frattini P).relIndex C ∣ p := by
        rw [hcC]
        exact relIndex_zpowers_dvd (frattini P) c hcp
      rcases (Nat.dvd_prime hpp).1 hdvd with h1 | h1
      · exfalso
        have hCΦ : C ≤ frattini P := relIndex_eq_one.1 h1
        have h2 : zpowers u₁ ⊔ zpowers u₂ ⊔ frattini P = ⊤ := by
          have h : zpowers u₁ ⊔ zpowers u₂ ⊔ C ≤ zpowers u₁ ⊔ zpowers u₂ ⊔ frattini P :=
            sup_le_sup_left hCΦ _
          rw [htop] at h
          exact top_unique h
        have h3 := frattini_nongenerating h2
        refine hno {u₁, u₂} Finset.card_le_two (top_unique ?_)
        rw [← h3]
        exact sup_le (zpowers_le.2 (subset_closure (by simp)))
          (zpowers_le.2 (subset_closure (by simp)))
      · exact h1
  ·
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ E ⊔ C := by
      by_contra h
      push Not at h
      exact hH (top_unique fun y _ => h y)
    obtain ⟨A₁, hA₁E, hA₁card, hA₁Φ⟩ :=
      exists_le_frattini_of_not_mem_sup_centralizer hp hP E hEcard hEexp hx
    have hidx : (E ⊔ C).index ≤ p :=
      index_sup_centralizer_le_of_extraspecial hp hP E hEcard hEexp
    have hindex : (E ⊔ C).index = p := by
      obtain ⟨n, hn⟩ := hP.index (E ⊔ C)
      have hne : (E ⊔ C).index ≠ 1 := fun h => hH (index_eq_one.1 h)
      rw [hn] at hidx hne ⊢
      have hn1 : n ≤ 1 := (Nat.pow_le_pow_iff_right hpp.one_lt).1 (by simpa using hidx)
      have hn0 : n ≠ 0 := fun h => hne (by simp [h])
      have : n = 1 := by omega
      rw [this, pow_one]
    have hHx : E ⊔ C ⊔ zpowers x = ⊤ := by
      refine eq_of_lt_of_card_mul hpp (A := E ⊔ C) (K := ⊤) ?_ le_top ?_
      · exact lt_of_le_of_ne le_sup_left fun h =>
          hx (by rw [h]; exact mem_sup_right (mem_zpowers x))
      · have h := index_mul_card (E ⊔ C)
        rw [hindex] at h
        rw [Subgroup.card_top, mul_comm]
        exact h
    obtain ⟨u, huE, huA⟩ : ∃ u ∈ E, u ∉ A₁ := by
      by_contra h
      push Not at h
      have h1 := Subgroup.card_le_of_le (show E ≤ A₁ from h)
      rw [hEcard, hA₁card] at h1
      have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
      omega
    have hEu : zpowers u ⊔ A₁ = E := by
      refine eq_of_lt_of_card_mul hpp (A := A₁) (K := E) ?_ ?_ ?_
      · exact lt_of_le_of_ne le_sup_right fun h =>
          huA (by rw [h]; exact mem_sup_left (mem_zpowers u))
      · exact sup_le (zpowers_le.2 huE) hA₁E
      · rw [hA₁card, hEcard]
        ring
    refine ⟨⟨{u, c, x}, Finset.card_le_three, ?_⟩, fun hno => ?_⟩
    · apply frattini_nongenerating
      refine top_unique ?_
      rw [← hHx]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hEu.ge.trans (sup_le (zpowers_le.2 (mem_sup_left (subset_closure (by simp))))
          (hA₁Φ.trans le_sup_right))
      · rw [hcC]
        exact zpowers_le.2 (mem_sup_left (subset_closure (by simp)))
      · exact zpowers_le.2 (mem_sup_left (subset_closure (by simp)))
    · refine ⟨E ⊔ frattini P, inferInstance, le_sup_right, ?_⟩
      rw [relIndex_sup_right]
      have hrel : A₁.relIndex E = p := by
        have h := relIndex_mul_card (H := A₁) (K := E)
        rw [inf_of_le_left hA₁E, hA₁card, hEcard] at h
        have hp2 : 0 < p ^ 2 := pow_pos hpp.pos 2
        exact Nat.eq_of_mul_eq_mul_right hp2 (h.trans (by ring))
      have hdvd : (frattini P).relIndex E ∣ p := hrel ▸ relIndex_dvd_of_le_left E hA₁Φ
      rcases (Nat.dvd_prime hpp).1 hdvd with h1 | h1
      · exfalso
        have hEΦ : E ≤ frattini P := relIndex_eq_one.1 h1
        have hT : Subgroup.closure (({c, x} : Finset P) : Set P) ⊔ frattini P = ⊤ := by
          refine top_unique ?_
          rw [← hHx]
          refine sup_le (sup_le ?_ ?_) ?_
          · exact hEΦ.trans le_sup_right
          · rw [hcC]
            exact zpowers_le.2 (mem_sup_left (subset_closure (by simp)))
          · exact zpowers_le.2 (mem_sup_left (subset_closure (by simp)))
        exact hno {c, x} Finset.card_le_two (frattini_nongenerating hT)
      · exact h1

theorem blackburnRankTwo_holds : KFacts.BlackburnRankTwo := by
  intro p _ hp P _ _ hP hE
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  by_cases hΩ : Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2
  · obtain ⟨s, hs, hcl⟩ := blackburn_small hp hP hΩ
    exact ⟨⟨s, hs.trans (by norm_num), hcl⟩, fun h => absurd hcl (h s hs)⟩
  · have hp3 : 3 < p := by omega
    have hrank := groupRank_le_two hP hE
    haveI : IsExtraspecial p (CFSG.omega₁ (G := P) (p := p)) :=
      isExtraspecial_omega hp3 hrank hΩ
    haveI : (CFSG.omega₁ (G := P) (p := p)).Characteristic :=
      CFSG.omega₁_characteristic P (p := p)
    obtain ⟨hexp, hcard⟩ := omega_large hp3 hrank hΩ
    exact blackburn_of_extraspecial (by omega) hP (CFSG.omega₁ (G := P) (p := p)) hcard hexp
      (isCyclic_centralizer_omega hp3 hrank hΩ)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

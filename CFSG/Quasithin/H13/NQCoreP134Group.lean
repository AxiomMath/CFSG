module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Group
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3

variable {G : Type*} [Group G]

theorem mem_zpowers_pow_of_coprime {g : G} {n : ℕ} (h : Nat.Coprime n (orderOf g)) :
    g ∈ Subgroup.zpowers (g ^ n) :=
  mem_zpowers_pow_iff.mpr h

section Finite

variable [Finite G]

theorem exists_elemAbelian_sq {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc : p ^ 2 ≤ Nat.card P) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have hP : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hk ▸ hc)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) p (n := 2)
    (hk ▸ pow_dvd_pow p hk2)
  have hEc : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq hE
  have hEel : IsElemAbelian p E :=
    ⟨hEc, fun x _ => Subtype.ext (by simpa using hexp (x : G) x.2)⟩
  refine ⟨E.map P.subtype, Subgroup.map_subtype_le E,
    CFSG.SectionRank.isElemAbelian_map hEel P.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective P.subtype_injective, hE]

theorem false_of_commute' {p : ℕ} [hp : Fact p.Prime] (hrank : Open.pRank p (⊤ : Subgroup G) ≤ 2)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) {z : G} (hz : z ∉ E)
    (hzp : z ^ p = 1) (hzE : ∀ a ∈ E, a * z = z * a) : False := by
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set k : Set G := (E : Set G) ∪ {z} with hk
  have hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact hEcomm x hx y hy
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzE x hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact (hzE y hy).symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  set C := Subgroup.closure k with hC
  have hCcomm : IsMulCommutative C :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  have hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hCcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCp : ∀ x ∈ C, x ^ p = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hE.2 x hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact hzp
    | one => exact one_pow p
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hCc x hx y hy) p), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hCpg : IsPGroup p C := fun g => ⟨1, Subtype.ext (by simpa using hCp g g.2)⟩
  have hEC : E ≤ C := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hzC : z ∈ C := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hCpg
  have hlt : p ^ 2 < p ^ n := by
    rcases Nat.lt_or_ge (p ^ 2) (p ^ n) with h | h
    · exact h
    · exfalso
      have hle : Nat.card C ≤ Nat.card E := by rw [hn, hEc]; exact h
      exact hz ((Subgroup.eq_of_le_of_card_ge hEC hle) ▸ hzC)
  have hn3 : 2 < n := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hlt
  have hCel : IsElemAbelian p C := ⟨hCcomm, hCp⟩
  have := CFSG.SectionRank.le_pRank hp.out.one_lt (le_top : C ≤ ⊤) hCel hn
  omega

theorem false_of_normalizes' {p : ℕ} [hp : Fact p.Prime]
    (hrank : Open.pRank p (⊤ : Subgroup G) ≤ 2) {P M : Subgroup G}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc : p ^ 2 ≤ Nat.card P)
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hinf : P ⊓ M = ⊥) (hpM : p ∣ Nat.card M) :
    False := by
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer P M hPM
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hmod := hPp.card_modEq_card_fixedPoints M
  have hF : p ∣ Nat.card (FixedPoints.subgroup P M) :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 hpM))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hF
  have hwp : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw
    exact hp.out.one_lt.ne hw
  set z : G := ((w : M) : G) with hz
  have hzp : z ^ p = 1 := by
    have := congrArg (fun u : FixedPoints.subgroup P M => ((u : M) : G)) hwp
    simpa [hz] using this
  have hz1 : z ≠ 1 := by
    intro h
    apply hw1
    exact Subtype.ext (Subtype.ext h)
  have hcomm : ∀ a ∈ P, a * z = z * a := by
    intro a ha
    have hfix : (⟨a, ha⟩ : P) • (w : M) = (w : M) := w.2 ⟨a, ha⟩
    have h1 : a * z * a⁻¹ = z := congrArg Subtype.val hfix
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h1]
  obtain ⟨E, hEP, hE, hEc⟩ := exists_elemAbelian_sq hexp hc
  have hzE : z ∉ E := by
    intro h
    have hzM : z ∈ P ⊓ M := ⟨hEP h, (w : M).2⟩
    rw [hinf, Subgroup.mem_bot] at hzM
    exact hz1 hzM
  exact false_of_commute' hrank hE hEc hzE hzp fun a ha => hcomm a (hEP ha)

omit [Finite G] in
theorem mem_of_mem_sup_of_coprime {p : ℕ} [hp : Fact p.Prime] {M M' : Subgroup G}
    (hMM' : M' ≤ Subgroup.centralizer (M : Set G)) (hpM : ¬ p ∣ Nat.card M) {x : G}
    (hx : x ∈ M ⊔ M') (hxp : x ^ p = 1) : x ∈ M' := by
  have hCN : M' ≤ Subgroup.normalizer (M : Set G) :=
    hMM'.trans (P134.centralizer_le_normalizer_self M)
  obtain ⟨m, hm, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hCN).1 hx
  have hmc : m * c = c * m := (Subgroup.mem_centralizer_iff.mp (hMM' hc)) m hm
  have h1 : m ^ p * c ^ p = 1 := by rw [← Commute.mul_pow hmc, hxp]
  have h2 : m ^ p ∈ M' := by
    have e : m ^ p = (c ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [e]
    exact M'.inv_mem (M'.pow_mem hc p)
  have hdvd : orderOf m ∣ Nat.card M := by
    have h := orderOf_dvd_natCard (⟨m, hm⟩ : M)
    rwa [← Subgroup.orderOf_coe] at h
  have hcop : Nat.Coprime p (orderOf m) :=
    Nat.Coprime.coprime_dvd_right hdvd ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpM)
  have hm' : m ∈ M' := (Subgroup.zpowers_le.mpr h2) (mem_zpowers_pow_of_coprime hcop)
  exact M'.mul_mem hm' hc

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {L O : Subgroup G} (hO : IsPGroup 2 O) (hOL : O ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ O) (hxp : x ^ p = 1) : x ∈ L := by
  obtain ⟨l, hl, o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hOL).1 hx
  have hpow : ∀ n : ℕ, ∃ l' ∈ L, (l * o) ^ n = l' * o ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hon : o ^ n ∈ Subgroup.normalizer (L : Set G) := hOL (O.pow_mem ho n)
      have h1 : o ^ n * l * (o ^ n)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hon l).mp hl
      refine ⟨l' * (o ^ n * l * (o ^ n)⁻¹), L.mul_mem hl' h1, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨k, hk⟩ := hO ⟨o, ho⟩
  have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨l', hl', he⟩ := hpow (2 ^ k)
  rw [hok, mul_one] at he
  have hcop : Nat.Coprime (2 ^ k) (orderOf (l * o)) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxp) ?_
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2))
  have h := mem_zpowers_pow_of_coprime hcop
  rw [he] at h
  exact (Subgroup.zpowers_le.mpr hl') h

theorem card_commutator_le {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}
    (hexp : ∀ x ∈ P, x ^ p = 1) (hc2 : p ^ 2 ≤ Nat.card P) (hc3 : Nat.card P ≤ p ^ 3) :
    Nat.card (⁅P, P⁆ : Subgroup G) ≤ p := by
  have hPp : IsPGroup p P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hΦ : frattiniIn P = ⁅P, P⁆ := frattiniIn_eq_commutator hPp hexp
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hΦP : frattiniIn P ≤ P := Subgroup.map_subtype_le _
  have hΦne : frattiniIn P ≠ P := frattiniIn_ne_of_ne_bot hP1
  rw [← hΦ]
  by_contra hlt
  push Not at hlt
  have hpk := hp.out.one_lt
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (hPp.to_le hΦP)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
  have hj2 : 2 ≤ j := by
    rw [hj] at hlt
    by_contra h
    push Not at h
    have h1 : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos (by omega)
    rw [pow_one] at h1
    omega
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hpk).1 (hk ▸ hc3)
  have hjk : j < k := by
    have hle : Nat.card (frattiniIn P) ≤ Nat.card P := Subgroup.card_le_of_le hΦP
    have hne : Nat.card (frattiniIn P) ≠ Nat.card P := fun h =>
      hΦne (Subgroup.eq_of_le_of_card_ge hΦP h.ge)
    rw [hj, hk] at hle hne
    have := (Nat.pow_le_pow_iff_right hpk).1 hle
    have hne' : j ≠ k := fun h => hne (by rw [h])
    omega
  obtain ⟨u, huP, huΦ⟩ : ∃ u ∈ P, u ∉ frattiniIn P := by
    by_contra hall
    push Not at hall
    exact hΦne (le_antisymm hΦP hall)
  set W := Subgroup.zpowers u ⊔ frattiniIn P with hW
  have hWP : W ≤ P := sup_le (Subgroup.zpowers_le.mpr huP) hΦP
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 (hPp.to_le hWP)
  have hji : j < i := by
    have hle : Nat.card (frattiniIn P) ≤ Nat.card W := Subgroup.card_le_of_le le_sup_right
    have hne : Nat.card (frattiniIn P) ≠ Nat.card W := fun h =>
      huΦ ((Subgroup.eq_of_le_of_card_ge (le_sup_right : frattiniIn P ≤ W) h.ge) ▸
        Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
    rw [hj, hi] at hle hne
    have := (Nat.pow_le_pow_iff_right hpk).1 hle
    have hne' : j ≠ i := fun h => hne (by rw [h])
    omega
  have hik : i ≤ k := by
    have hle : Nat.card W ≤ Nat.card P := Subgroup.card_le_of_le hWP
    rw [hi, hk] at hle
    exact (Nat.pow_le_pow_iff_right hpk).1 hle
  have hWeq : W = P := Subgroup.eq_of_le_of_card_ge hWP (by
    rw [hi, hk]
    exact Nat.pow_le_pow_right hp.out.pos (by omega))
  have hzP : Subgroup.zpowers u = P :=
    eq_of_sup_frattiniIn_eq (Subgroup.zpowers_le.mpr huP) hWeq
  have hcard : Nat.card P ≤ p := by
    rw [← hzP, Nat.card_zpowers]
    exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one (hexp u huP))
  have : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hpk (by norm_num)
  omega

theorem commute_of_normal_of_card_eq_prime {p : ℕ} [hp : Fact p.Prime] {P A : Subgroup G}
    (hP : IsPGroup p P) (hAP : A ≤ P) (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hA : Nat.card A = p) : ∀ a ∈ A, ∀ x ∈ P, a * x = x * a := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hAn : (A.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hPA
  have hcardA : Nat.card (A.subgroupOf P) = p := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
  have hne : A.subgroupOf P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardA
    exact hp.out.one_lt.ne hcardA
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hle : A.subgroupOf P ≤ Subgroup.center ↥P := by
    have hdvd : Nat.card (A.subgroupOf P ⊓ Subgroup.center ↥P : Subgroup ↥P) ∣ p :=
      hcardA ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hinf
    · have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        A.subgroupOf P ⊓ Subgroup.center ↥P ≤ A.subgroupOf P) (by rw [h1, hcardA])
      exact heq ▸ inf_le_right
  intro a ha x hx
  have hmem : (⟨a, hAP ha⟩ : P) ∈ Subgroup.center ↥P := hle (Subgroup.mem_subgroupOf.mpr ha)
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩).symm)

theorem card_sup_eq_of_mul' {P T : Subgroup G} (hcop : Nat.Coprime (Nat.card P) (Nat.card T))
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s) :
    Nat.card (P ⊔ T : Subgroup G) = Nat.card P * Nat.card T := by
  apply le_antisymm
  · let f : P × T → (P ⊔ T : Subgroup G) := fun ys =>
      ⟨(ys.1 : G) * ys.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left ys.1.2)
        (Subgroup.mem_sup_right ys.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨y, hy, s, hs, rfl⟩ := P134.exists_mul_of_mem_sup hmul hg
      exact ⟨(⟨y, hy⟩, ⟨s, hs⟩), rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at this
  · have h1 : Nat.card P ∣ Nat.card (P ⊔ T : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card T ∣ Nat.card (P ⊔ T : Subgroup G) := Subgroup.card_dvd_of_le le_sup_right
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2)

theorem prime_dvd_of_le_sup' {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P T B : Subgroup G}
    (hP : IsPGroup p P) (hT : IsPGroup 2 T)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s) (hB : B ≤ P ⊔ T) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p := by
  intro q hq hqB
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card).1 hT
  have hcop : Nat.Coprime (Nat.card P) (Nat.card T) := by
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp.out Nat.prime_two).mpr hp2)
  have h1 : q ∣ Nat.card P * Nat.card T :=
    (card_sup_eq_of_mul' hcop hmul) ▸ hqB.trans (Subgroup.card_dvd_of_le hB)
  rw [ha, hb] at h1
  rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 (hq.dvd_of_dvd_pow h))
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

end Finite

end CFSG.Quasithin.H13.NQCore

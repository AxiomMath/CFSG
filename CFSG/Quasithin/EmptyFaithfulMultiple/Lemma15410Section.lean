module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Aut
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15410Module
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Background.A1cA133
public import CFSG.Quasithin.Background.E2Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.SectionRank.Ccomm
open scoped commutatorElement

section Prelim

variable {H : Type*} [Group H]

theorem rho_eq_one_of_commute {K : Type*} [Group K] (ρ : H →* K) {Q X : Subgroup H}
    (hQ : IsPGroup 2 Q) (hQX : Q ≤ X) (hXo : X = oTwoUpper X) {x : H} (hx3 : x ^ 3 = 1)
    (hgen : ∀ y ∈ X, ∃ k : ℕ, ∃ q ∈ Q, y = x ^ k * q)
    (hcomm : ∀ q ∈ Q, ρ x * ρ q = ρ q * ρ x) : ∀ q ∈ Q, ρ q = 1 := by
  have hρx3 : (ρ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have htriv : ∀ q ∈ Q, ∀ n : ℕ, Odd n → (ρ q) ^ n ∈ Subgroup.zpowers (ρ x) → ρ q = 1 := by
    intro q hq n hn hmem
    obtain ⟨j, hj⟩ := hQ ⟨q, hq⟩
    have hj' : (ρ q) ^ 2 ^ j = 1 := by
      have := congrArg (fun z : Q => ρ z) hj
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h3 : ((ρ q) ^ n) ^ 3 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρx3, one_zpow]
    have hd1 : orderOf (ρ q) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hd2 : orderOf (ρ q) ∣ n * 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_mul, h3])
    have hcop : Nat.Coprime (2 ^ j) (n * 3) :=
      Nat.Coprime.pow_left j (Nat.Coprime.mul_right (Nat.coprime_two_left.mpr hn)
        (by norm_num))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hX : ∀ y ∈ X, ρ y ∈ Subgroup.zpowers (ρ x) := by
    have hle : X ≤ (Subgroup.zpowers (ρ x)).comap ρ := by
      rw [hXo, oTwoUpper]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyX, hyo⟩
      obtain ⟨k, q, hq, rfl⟩ := hgen y (hXo ▸ hyX)
      show ρ (x ^ k * q) ∈ Subgroup.zpowers (ρ x)
      have hcq : Commute (ρ x ^ k) (ρ q) := (Commute.pow_left (hcomm q hq) k)
      have hpow : (ρ (x ^ k * q)) ^ orderOf (x ^ k * q) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [map_mul, map_pow, hcq.mul_pow, ← pow_mul] at hpow
      have hmem : (ρ q) ^ orderOf (x ^ k * q) ∈ Subgroup.zpowers (ρ x) := by
        have : (ρ q) ^ orderOf (x ^ k * q) = ((ρ x) ^ (k * orderOf (x ^ k * q)))⁻¹ :=
          eq_inv_of_mul_eq_one_right hpow
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
      rw [map_mul, map_pow, htriv q hq _ hyo hmem, mul_one]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    exact fun y hy => hle hy
  intro q hq
  have h1 := hX q (hQX hq)
  exact htriv q hq 1 odd_one (by rw [pow_one]; exact h1)

theorem eq_bot_of_le_fitting_inf_centralizer [Finite H] (h2 : CFSG.Open.pCore 2 H = ⊥)
    {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    (hQF : Q ≤ CFSG.fittingSubgroup H ⊓ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H)) :
    Q = ⊥ := by
  set F := CFSG.fittingSubgroup H with hF
  set Z := F ⊓ Subgroup.centralizer (F : Set H) with hZ
  have hZn : Z.Normal := by
    have : F.Normal := inferInstance
    exact Subgroup.normal_inf_normal _ _
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha.1
  let D : Subgroup H :=
    { carrier := {z | z ∈ Z ∧ ∃ k : ℕ, z ^ 2 ^ k = 1}
      one_mem' := ⟨Z.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨Z.mul_mem ha hb, k + l, ?_⟩
        rw [(Commute.mul_pow (hZc a ha b hb) _), pow_add, pow_mul, hk, one_pow, mul_comm,
          pow_mul, hl, one_pow, one_mul]
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨Z.inv_mem ha, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hDn : D.Normal := ⟨fun n ⟨hn, k, hk⟩ g =>
    ⟨hZn.conj_mem n hn g, k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩⟩
  have hD2 : IsPGroup 2 D := fun d => by
    obtain ⟨k, hk⟩ := d.2.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hDle : D ≤ CFSG.Open.pCore 2 H := CFSG.LieType.BorelTits.le_pCore 2 hDn hD2
  rw [h2] at hDle
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
  exact hDle ⟨hQF hq, k, by simpa using congrArg Subtype.val hk⟩

theorem exists_odd_pCore_not_centralized [Finite H] (hsolv : Group.IsSolvable H)
    (h2 : CFSG.Open.pCore 2 H = ⊥) {Q : Subgroup H} (hQ : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ¬ Q ≤ Subgroup.centralizer (CFSG.Open.pCore p H : Set H) := by
  by_contra hcon
  push Not at hcon
  apply hQ1
  have hF : Q ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases hq2 : q.1.1 = 2
    · rw [hq2, h2]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
    · exact hcon _ hq hq2
  have hQF : Q ≤ CFSG.fittingSubgroup H :=
    hF.trans (CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv)
  exact eq_bot_of_le_fitting_inf_centralizer h2 hQ (le_inf hQF hF)

end Prelim


section Frattini

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]

noncomputable abbrev fratAct (R : Subgroup H) [R.Normal] (D : Subgroup R) [D.Characteristic] :
    H →* MulAut (D ⧸ frattini D) :=
  (frattiniAction D).comp MulAut.conjNormal

omit [Finite H] in
theorem fratAct_mk (R : Subgroup H) [R.Normal] (D : Subgroup R) [D.Characteristic] (g : H)
    (d : D) : fratAct R D g (d : D ⧸ frattini D) =
      ((⟨⟨g * ((d : R) : H) * g⁻¹, by
          have := (MulAut.conjNormal g (d : R)).2
          rwa [MulAut.conjNormal_apply] at this⟩,
        by
          have := (MulAut.characteristic D (MulAut.conjNormal g) d).2
          exact this⟩ : D) : D ⧸ frattini D) := by
  rw [fratAct, MonoidHom.comp_apply, frattiniAction_mk]
  congr 2

omit [Finite H] in
theorem fratAct_eq_one_iff (R : Subgroup H) [R.Normal] (D : Subgroup R) [D.Characteristic]
    (g : H) : fratAct R D g = 1 ↔ ∀ x ∈ D, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn D := by
  rw [← mem_ker_frattiniAction_iff, MonoidHom.mem_ker]
  rfl


omit [Finite H] in
theorem conjNormal_mem_of_char (R : Subgroup H) [R.Normal] (D : Subgroup R)
    [hc : D.Characteristic] (g : H) {r : R} (hr : r ∈ D) : MulAut.conjNormal g r ∈ D := by
  rw [← hc.fixed (MulAut.conjNormal g)] at hr
  exact hr

theorem exists_section_of_not_centralizes (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ 2) {Q X : Subgroup H} (hQ : IsPGroup 2 Q)
    (hQX : Q ≤ X) (hXo : X = oTwoUpper X) {x : H} (hx3 : x ^ 3 = 1)
    (hgen : ∀ y ∈ X, ∃ k : ℕ, ∃ q ∈ Q, y = x ^ k * q) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (hnc : ¬ Q ≤ Subgroup.centralizer (CFSG.Open.pCore p H : Set H)) :
    ∃ D : Subgroup H, D.Normal ∧ D ≤ CFSG.Open.pCore p H ∧ (∀ d ∈ D, d ^ p = 1) ∧
      ((Nat.card D = p ^ 2 ∧ ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∨
        (Nat.card D = p ^ 3 ∧ ¬ ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)) ∧
      (∀ D' : Subgroup H, ⁅D, D⁆ ≤ D' → D' ≤ D → Q ≤ Subgroup.normalizer (D' : Set H) →
        D' = ⁅D, D⁆ ∨ D' = D) ∧
      (∃ d ∈ D, x * d * x⁻¹ * d⁻¹ ∉ ⁅D, D⁆) ∧ (p = 3 → Nat.card D = 9) := by
  classical
  set R := CFSG.Open.pCore p H with hRdef
  have hRn : R.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hRp : IsPGroup p R := CFSG.LieType.BorelTits.pCore_isPGroup p
  obtain ⟨D₀, hD₀, hfaith⟩ := exists_isSupercritical_faithful hp2 hRp
  have hD₀c : D₀.Characteristic := hD₀.characteristic
  set E := D₀ ⧸ frattini D₀ with hEdef
  set ρ : H →* MulAut E := fratAct R D₀ with hρ
  set ι : D₀ →* H := R.subtype.comp D₀.subtype with hι
  have hιinj : Function.Injective ι := R.subtype_injective.comp D₀.subtype_injective
  have hιapp : ∀ d : D₀, ι d = ((d : R) : H) := fun _ => rfl
  obtain ⟨q₀, hq₀, hρq₀⟩ : ∃ q₀ ∈ Q, ρ q₀ ≠ 1 := by
    by_contra h
    push Not at h
    apply hnc
    intro q hq
    have hcop : (orderOf (MulAut.conjNormal (H := R) q)).Coprime p := by
      obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
      have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : (MulAut.conjNormal (H := R) q) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
      exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h1)
        (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)))
    have hα := hfaith _ hcop ((fratAct_eq_one_iff R D₀ q).mp (h q hq))
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := congrArg (fun α : MulAut R => ((α ⟨r, hr⟩ : R) : H)) hα
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc r * q = (q * r * q⁻¹) * q := by rw [h1]
      _ = q * r := by group
  have hD₀p : IsPGroup p D₀ := hRp.to_subgroup D₀
  obtain ⟨-, hEcomm, hEpow⟩ := frattini_quotient_elementary hD₀p
  have hD₀exp : ∀ y : D₀, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using hD₀.pow_eq_one (y : R) y.2)
  have hrankR : CFSG.Open.pRank p (⊤ : Subgroup R) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt R.subtype
      R.subtype_injective).trans hrank
  have hrankD : CFSG.Open.pRank p (⊤ : Subgroup D₀) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.out.one_lt D₀.subtype
      D₀.subtype_injective).trans hrankR
  obtain ⟨hD3, hE2⟩ := rank_two_exponent_prime_order_bound hD₀p hD₀exp hrankD
  obtain ⟨k, hk⟩ := (hD₀p.to_quotient (frattini D₀)).exists_card_eq
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp (hk ▸ hE2)
  have hk2' : k = 2 := by
    by_contra hne
    have hcyc : IsCyclic E := by
      interval_cases k
      · rw [pow_zero] at hk
        have : Subsingleton E := (Nat.card_eq_one_iff_unique.mp hk).1
        infer_instance
      · exact isCyclic_of_prime_card (by rw [hk, pow_one])
      · exact absurd rfl hne
    exact hρq₀ (rho_eq_one_of_commute ρ hQ hQX hXo hx3 hgen
      (fun q _ => mulAut_comm_of_isCyclic _ _) q₀ hq₀)
  have hE : IsElemSq p E := ⟨hEcomm, hEpow, by rw [hk, hk2']⟩
  set A : Subgroup (MulAut E) := Q.map ρ with hA
  have hA2 : IsPGroup 2 A := hQ.map ρ
  have hxA : ∀ a ∈ A, ρ x * a * (ρ x)⁻¹ ∈ A := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, hxQ q hq, by simp only [map_mul, map_inv]⟩
  have hxnc : ∃ a ∈ A, ρ x * a ≠ a * ρ x := by
    by_contra h
    push Not at h
    exact hρq₀ (rho_eq_one_of_commute ρ hQ hQX hXo hx3 hgen
      (fun q hq => h _ ⟨q, hq, rfl⟩) q₀ hq₀)
  have hρx3 : (ρ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hirrE : ∀ L : Subgroup E, Nat.card L = p → ∃ a ∈ A, ∃ l ∈ L, a l ∉ L :=
    fun L hL => hE.exists_not_mapsTo hp2 hA2 hρx3 hxA hxnc hL
  have hρx1 : ρ x ≠ 1 := by
    intro h1
    obtain ⟨a, -, ha⟩ := hxnc
    exact ha (by rw [h1, one_mul, mul_one])
  set D : Subgroup H := D₀.map R.subtype with hD
  have hDι : D = (⊤ : Subgroup D₀).map ι := by
    rw [hD, hι, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmemD : ∀ y : H, y ∈ D ↔ ∃ d : D₀, ι d = y := by
    intro y
    rw [hDι]
    simp
  have hconjι : ∀ (g : H) (d : D₀), ι ⟨MulAut.conjNormal g (d : R),
      conjNormal_mem_of_char R D₀ g d.2⟩ = g * ι d * g⁻¹ := by
    intro g d
    simp [hιapp, MulAut.conjNormal_apply]
  have hDn : D.Normal := ⟨fun n hn g => by
    obtain ⟨d, rfl⟩ := (hmemD n).mp hn
    exact (hmemD _).mpr ⟨_, hconjι g d⟩⟩
  have hDR : D ≤ R := Subgroup.map_subtype_le D₀
  have hDexp : ∀ d ∈ D, d ^ p = 1 := by
    intro y hy
    obtain ⟨d, rfl⟩ := (hmemD y).mp hy
    rw [← map_pow, hD₀exp d, map_one]
  have hcomm : ⁅D, D⁆ = (commutator D₀).map ι := by
    rw [hDι, ← Subgroup.map_commutator, commutator_def]
  have hcardD : Nat.card D = Nat.card D₀ := by
    rw [hD, Subgroup.card_map_of_injective R.subtype_injective]
  have hcommD : (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ↔ ∀ a b : D₀, a * b = b * a := by
    constructor
    · intro h a b
      apply hιinj
      rw [map_mul, map_mul]
      exact h _ ((hmemD _).mpr ⟨a, rfl⟩) _ ((hmemD _).mpr ⟨b, rfl⟩)
    · intro h a ha b hb
      obtain ⟨a', rfl⟩ := (hmemD a).mp ha
      obtain ⟨b', rfl⟩ := (hmemD b).mp hb
      rw [← map_mul, ← map_mul, h]
  have hcard_E : Nat.card D₀ = p ^ 2 * Nat.card (frattini D₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini D₀), hk, hk2']
  have hΦc : frattini D₀ ≤ commutator D₀ := by
    refine frattini_le_of_commutator_pow_mem (p := p) _ (fun a b => ?_) (fun a => ?_)
    · rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    · rw [hD₀exp a]
      exact Subgroup.one_mem _
  have hstruct : (Nat.card D = p ^ 2 ∧ ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∨
      (Nat.card D = p ^ 3 ∧ ¬ ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) := by
    by_cases hab : ∀ a b : D₀, a * b = b * a
    · left
      have hΦ : frattini D₀ = ⊥ := (frattini_eq_bot_iff hD₀p).mpr ⟨hab, hD₀exp⟩
      refine ⟨?_, hcommD.mpr hab⟩
      rw [hcardD, hcard_E, hΦ, Subgroup.card_bot, mul_one]
    · right
      refine ⟨?_, fun h => hab (hcommD.mp h)⟩
      have hΦne : frattini D₀ ≠ ⊥ := fun h => hab ((frattini_eq_bot_iff hD₀p).mp h).1
      obtain ⟨j, hj⟩ := (hD₀p.to_subgroup (frattini D₀)).exists_card_eq
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hj
        exact hΦne (Subgroup.card_eq_one.mp hj)
      have hle : p ^ (2 + j) ≤ p ^ 3 := by rw [pow_add, ← hj, ← hcard_E]; exact hD3
      have hj1 : j = 1 := by
        have := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle
        omega
      rw [hcardD, hcard_E, hj, hj1]
      ring
  have hirrD : ∀ D' : Subgroup H, ⁅D, D⁆ ≤ D' → D' ≤ D →
      Q ≤ Subgroup.normalizer (D' : Set H) → D' = ⁅D, D⁆ ∨ D' = D := by
    intro D' hcD hD'D hQD'
    set D₀' : Subgroup D₀ := D'.comap ι with hD₀'
    set U : Subgroup E := D₀'.map (QuotientGroup.mk' (frattini D₀)) with hU
    have hUinv : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
      rintro _ ⟨q, hq, rfl⟩ _ ⟨d, hd, rfl⟩
      refine ⟨⟨MulAut.conjNormal q (d : R), conjNormal_mem_of_char R D₀ q d.2⟩, ?_, ?_⟩
      · show ι _ ∈ D'
        rw [hconjι]
        exact (Subgroup.mem_normalizer_iff.mp (hQD' hq) (ι d)).mp hd
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hρ, fratAct_mk]
        congr 1
    have hUdvd : Nat.card U ∣ p ^ 2 := hE.card ▸ Subgroup.card_subgroup_dvd_card U
    obtain ⟨m, hm, hUm⟩ := (Nat.dvd_prime_pow hp.out).mp hUdvd
    interval_cases m
    · left
      refine le_antisymm (fun y hy => ?_) hcD
      obtain ⟨d, rfl⟩ := (hmemD y).mp (hD'D hy)
      have hdU : ((d : D₀) : E) ∈ U := ⟨d, hy, rfl⟩
      rw [pow_zero] at hUm
      rw [Subgroup.card_eq_one.mp hUm, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hdU
      rw [hcomm]
      exact ⟨d, hΦc hdU, rfl⟩
    · exfalso
      obtain ⟨a, ha, u, hu, hau⟩ := hirrE U (by rw [hUm, pow_one])
      exact hau (hUinv a ha u hu)
    · right
      refine le_antisymm hD'D (fun y hy => ?_)
      obtain ⟨d, rfl⟩ := (hmemD y).mp hy
      have hUtop : U = ⊤ := Subgroup.eq_top_of_card_eq U (hUm.trans hE.card.symm)
      have hsup : D₀' ⊔ frattini D₀ = ⊤ := by
        rw [eq_top_iff]
        intro d' _
        have hd'U : ((d' : D₀) : E) ∈ U := by rw [hUtop]; exact Subgroup.mem_top _
        obtain ⟨d'', hd'', he⟩ := hd'U
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
        have hd'eq : d' = d'' * (d''⁻¹ * d') := by group
        rw [hd'eq]
        exact Subgroup.mul_mem_sup hd'' he
      have hD₀'top : D₀' = ⊤ := frattini_nongenerating hsup
      have hdmem : d ∈ D₀' := by rw [hD₀'top]; exact Subgroup.mem_top d
      exact hdmem
  have hcommN : ⁅D, D⁆.Normal := Subgroup.commutator_normal D D
  have hnontriv : ∃ d ∈ D, x * d * x⁻¹ * d⁻¹ ∉ ⁅D, D⁆ := by
    by_contra h
    push Not at h
    apply hρx1
    rw [hρ, fratAct_eq_one_iff]
    intro r hr
    have hy := h (ι ⟨r, hr⟩) ((hmemD _).mpr ⟨_, rfl⟩)
    set c : D₀ := ⟨r, hr⟩⁻¹ * ⟨MulAut.conjNormal x r, conjNormal_mem_of_char R D₀ x hr⟩ with hc
    have hcι : ι c = (ι ⟨r, hr⟩)⁻¹ * (x * ι ⟨r, hr⟩ * x⁻¹ * (ι ⟨r, hr⟩)⁻¹) * ι ⟨r, hr⟩ := by
      have h1 : ι ⟨MulAut.conjNormal x r, conjNormal_mem_of_char R D₀ x hr⟩ =
          x * ι ⟨r, hr⟩ * x⁻¹ := hconjι x ⟨r, hr⟩
      rw [hc, map_mul, map_inv, h1]
      group
    have hcmem : ι c ∈ ⁅D, D⁆ := by
      rw [hcι]
      have := hcommN.conj_mem _ hy (ι ⟨r, hr⟩)⁻¹
      rwa [inv_inv] at this
    rw [hcomm] at hcmem
    obtain ⟨c', hc', hcc'⟩ := hcmem
    rw [hιinj hcc'] at hc'
    have : Fact (IsPGroup p D₀) := ⟨hD₀p⟩
    have hcΦ : c ∈ frattini D₀ := CFSG.commutator_le_frattini_of_isPGroup (R := D₀) (p := p) hc'
    exact ⟨c, hcΦ, rfl⟩
  have hcZ : commutator D₀ ≤ Subgroup.center D₀ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : ⁅(a : R), (b : R)⁆ ∈ centerOf D₀ :=
      hD₀.commutator_le (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _))
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (g : R) g.2
    have e : ((⁅a, b⁆ : D₀) : R) = ⁅(a : R), (b : R)⁆ := rfl
    simp only [Subgroup.coe_mul, e]
    exact h2
  have hcenter : ∀ z : D₀, z ∈ Subgroup.center D₀ → ι z ∈ centerOf D := by
    intro z hz
    refine ⟨(hmemD _).mpr ⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨d, rfl⟩ := (hmemD y).mp hy
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz d]
  have h9 : p = 3 → Nat.card D = 9 := by
    intro hp3
    rcases hstruct with ⟨h, -⟩ | ⟨-, hnab⟩
    · rw [h, hp3]
      norm_num
    exfalso
    have hnabD₀ : ¬ ∀ a b : D₀, a * b = b * a := fun h => hnab (hcommD.mpr h)
    have hRnt : Nontrivial R := by
      by_contra hR
      rw [not_nontrivial_iff_subsingleton] at hR
      exact hnabD₀ fun a b => Subtype.ext (Subsingleton.elim _ _)
    have hiso : IsPOnePlusTwo p D₀ := by
      rcases hD₀.iso_cases hp2 hRp hrankR with he | he | h
      · obtain ⟨e⟩ := he
        exact absurd (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])) hnabD₀
      · obtain ⟨e⟩ := he
        exact absurd (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])) hnabD₀
      · exact h
    have hisoD : IsPOnePlusTwo p D :=
      isPOnePlusTwo_of_mulEquiv (D₀.equivMapOfInjective R.subtype R.subtype_injective) hiso
    obtain ⟨t, htA, htinv⟩ := hE.exists_inv_mem hA2 hirrE
    obtain ⟨q₁, hq₁, rfl⟩ := htA
    have hinvc : ∀ α : MulAut E, α * ρ q₁ * α⁻¹ = ρ q₁ := by
      intro α
      ext y
      rw [MulAut.mul_apply, MulAut.mul_apply, htinv, map_inv, MulAut.apply_inv_self, htinv]
    let S := {q : H // q ∈ Q ∧ ρ q = ρ q₁}
    have hfS : ∀ q : S, x * q.1 * x⁻¹ ∈ Q ∧ ρ (x * q.1 * x⁻¹) = ρ q₁ := fun q =>
      ⟨hxQ _ q.2.1, by rw [map_mul, map_mul, map_inv, q.2.2, hinvc]⟩
    let f : S → S := fun q => ⟨x * q.1 * x⁻¹, hfS q⟩
    have hf3 : ∀ q, f (f (f q)) = q := by
      intro q
      apply Subtype.ext
      show x * (x * (x * q.1 * x⁻¹) * x⁻¹) * x⁻¹ = q.1
      calc x * (x * (x * q.1 * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * q.1 * (x ^ 3)⁻¹ := by
            rw [pow_three']; group
        _ = q.1 := by rw [hx3]; group
    let σ : Equiv.Perm S := ⟨f, fun q => f (f q), hf3, hf3⟩
    have hσ3 : σ ^ 3 ^ 1 = 1 := by
      ext q
      show (f (f (f q))).1 = q.1
      rw [hf3]
    have : Fintype S := Fintype.ofFinite S
    have hS : ¬ 3 ∣ Fintype.card S := by
      let e : S ≃ ↥(Q ⊓ ρ.ker) :=
        { toFun := fun q => ⟨q₁⁻¹ * q.1, Subgroup.mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem hq₁) q.2.1,
            MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, q.2.2, inv_mul_cancel])⟩⟩
          invFun := fun k => ⟨q₁ * k.1, Q.mul_mem hq₁ (Subgroup.mem_inf.mp k.2).1, by
            rw [map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp k.2).2, mul_one]⟩
          left_inv := fun q => Subtype.ext (by simp)
          right_inv := fun k => Subtype.ext (by simp) }
      rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
      obtain ⟨a, ha⟩ := (hQ.to_le (inf_le_left : Q ⊓ ρ.ker ≤ Q)).exists_card_eq
      rw [ha]
      intro h3
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨t₀, ht₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hS hσ3
    have hxt : x * t₀.1 * x⁻¹ = t₀.1 := congrArg Subtype.val ht₀
    have htinv0 : ∀ y, ρ t₀.1 y = y⁻¹ := by rw [t₀.2.2]; exact htinv
    have hΦZ : frattini D₀ ≤ Subgroup.center D₀ := hΦc.trans hcZ
    have ht : ∀ y ∈ D, t₀.1 * y * t₀.1⁻¹ * y ∈ centerOf D := by
      intro y hy
      obtain ⟨d, rfl⟩ := (hmemD y).mp hy
      set c : D₀ := ⟨MulAut.conjNormal t₀.1 (d : R), conjNormal_mem_of_char R D₀ t₀.1 d.2⟩
        with hc
      have h1 : ((c : D₀) : E) = ((d⁻¹ : D₀) : E) := by
        have e1 : ρ t₀.1 (d : E) = ((c : D₀) : E) := fratAct_mk R D₀ t₀.1 d
        rw [← e1, htinv0, QuotientGroup.mk_inv]
      rw [QuotientGroup.eq] at h1
      have h2 : c * d ∈ Subgroup.center D₀ := by
        have h3 := (Subgroup.center D₀).inv_mem (hΦZ h1)
        rw [mul_inv_rev, inv_inv, inv_inv] at h3
        have h4 := (Subgroup.normal_of_characteristic _ : (Subgroup.center D₀).Normal).conj_mem
          _ h3 d⁻¹
        rwa [inv_inv, show d⁻¹ * (d * c) * d = c * d by group] at h4
      have h5 := hcenter _ h2
      rwa [map_mul, hconjι] at h5
    have hcD : ⁅D, D⁆ ≤ centerOf D := by
      rw [hcomm]
      rintro _ ⟨z, hz, rfl⟩
      exact hcenter z (hcZ hz)
    have hcDne : ⁅D, D⁆ ≠ ⊥ := by
      intro hbot
      apply hnab
      intro a ha b hb
      have h1 : ⁅a, b⁆ ∈ ⁅D, D⁆ := Subgroup.commutator_mem_commutator ha hb
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hZcard : Nat.card (centerOf D) = p := A1c.card_centerOf hisoD.1
    have hZD : centerOf D ≤ ⁅D, D⁆ := by
      refine (Subgroup.eq_of_le_of_card_ge hcD ?_).ge
      have hdvd : Nat.card (⁅D, D⁆ : Subgroup H) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le hcD
      rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hcDne
      · rw [h, hZcard]
    obtain ⟨d, hdD, hdx⟩ := hnontriv
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hρx1 (map_one ρ)
    have hxo : orderOf x = p := by rw [hp3]; exact orderOf_eq_prime hx3 hx1
    have hxc : x ∈ Subgroup.centralizer ({t₀.1} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * t₀.1 = (x * t₀.1 * x⁻¹) * x := by group
        _ = t₀.1 * x := by rw [hxt]
    have := hDn
    have h3 := A1c.two_lt_pRank_of_inverting_element hp2 hisoD ht hxc hxo
      ⟨d, hdD, fun h => hdx (hZD h)⟩
    omega
  exact ⟨D, hDn, hDR, hDexp, hstruct, hirrD, hnontriv, h9⟩

end Frattini


section Lift

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hy, ho⟩
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hy ho) ho

theorem oTwoUpper_eq_self_of_isPGroup {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {D : Subgroup H} (hD : IsPGroup p D) : oTwoUpper D = D := by
  refine le_antisymm (oTwoUpper_le D) fun d hd => mem_oTwoUpper_of_odd hd ?_
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hD) ⟨d, hd⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow

omit [Finite G] in
theorem commutator_le_self (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun _ ha _ hb =>
    H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem exists_pow_mul_of_relIndex_three {X : Subgroup G} (hX3 : (pCoreOf 2 X).relIndex X = 3)
    {x : G} (hxX : x ∈ X) (hx3 : orderOf x = 3) :
    ∀ y ∈ X, ∃ k : ℕ, ∃ q ∈ pCoreOf 2 X, y = x ^ k * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X with hQdef
  have hxQ : x ∉ Q := by
    intro h
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨x, h⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have := orderOf_dvd_of_pow_eq_one hk'
    rw [hx3] at this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX)
  set W := Subgroup.zpowers x ⊔ Q with hW
  have hWX : W ≤ X := sup_le (Subgroup.zpowers_le.mpr hxX) (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
  have hQW : Q ≤ W := le_sup_right
  have h1 := Subgroup.relIndex_mul_relIndex Q W X hQW hWX
  rw [hX3] at h1
  have hQW1 : Q.relIndex W ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact fun h => hxQ (h (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  have hWX1 : W.relIndex X = 1 := by
    have hdvd : Q.relIndex W ∣ 3 := ⟨_, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hQW1
    · rw [h] at h1
      omega
  have hXW : X ≤ W := Subgroup.relIndex_eq_one.mp hWX1
  intro y hy
  have hyW : y ∈ (W : Set G) := hXW hy
  rw [hW, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxN] at hyW
  obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.mp hyW
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨n, -, hn⟩ := exists_pow_eq_zpow (by rw [← hx3]; exact pow_orderOf_eq_one x) m
  exact ⟨n, q, hq, by rw [hn]⟩


theorem exists_xi_of_not_le_pCoreOf {M T X : Subgroup G} (hTM : T ≤ M) (hRT : pCoreOf 2 M ≤ T)
    (hR : pCoreOf 2 M ≠ ⊥) (hMs : Group.IsSolvable M)
    (hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p M ≤ 2)
    (hXM : X ≤ M) (hXo : X = oTwoUpper X) (hX3 : (pCoreOf 2 X).relIndex X = 3)
    (hQT : pCoreOf 2 X ≤ T) (hQ : ¬ pCoreOf 2 X ≤ pCoreOf 2 M) :
    ∃ (p : ℕ) (Y : Subgroup G) (x : G), p.Prime ∧ p ≠ 2 ∧ Y ≤ M ∧
      M ≤ Subgroup.normalizer (Y : Set G) ∧ IsXi T Y ∧ (∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y) ∧
      (((pCoreOf 2 Y).relIndex Y = p ^ 2 ∧ ⁅Y, Y⁆ ≤ pCoreOf 2 Y) ∨
        (pCoreOf 2 Y).relIndex Y = p ^ 3) ∧
      (p = 3 → (pCoreOf 2 Y).relIndex Y = 9) ∧
      x ∈ X ∧ orderOf x = 3 ∧ (∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∉ ⁅Y, Y⁆ ⊔ pCoreOf 2 Y) ∧
      (∀ Y' : Subgroup G, ⁅Y, Y⁆ ⊔ pCoreOf 2 Y ≤ Y' → Y' ≤ Y →
        pCoreOf 2 X ≤ Subgroup.normalizer (Y' : Set G) →
          Y' = ⁅Y, Y⁆ ⊔ pCoreOf 2 Y ∨ Y' = Y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.Open.pCore 2 ↥M with hN
  set π : ↥M →* (↥M ⧸ N) := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set R := pCoreOf 2 M with hRdef
  have hπ1 : ∀ m : M, π m = 1 ↔ (m : G) ∈ R := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨m, h, rfl⟩
    · rintro ⟨m', hm', he⟩
      rwa [show m = m' from Subtype.ext he.symm]
  set Q := pCoreOf 2 X with hQdef
  have hQX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hQM : Q ≤ M := hQX.trans hXM
  have h3X : 3 ∣ Nat.card X := hX3 ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨⟨x, hxX⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  rw [Subgroup.orderOf_mk] at hxo
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxM : x ∈ M := hXM hxX
  set Qb := (Q.subgroupOf M).map π with hQb
  set Xb := (X.subgroupOf M).map π with hXb
  set xb := π ⟨x, hxM⟩ with hxb
  have hQb2 : IsPGroup 2 Qb :=
    (hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).map π
  have hQb1 : Qb ≠ ⊥ := by
    intro hbot
    apply hQ
    intro q hq
    have : π ⟨q, hQM hq⟩ ∈ Qb := ⟨⟨q, hQM hq⟩, hq, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ1] at this
    exact this
  have hQbXb : Qb ≤ Xb := Subgroup.map_mono (Subgroup.subgroupOf_mono _ hQX)
  have hXo' : X.subgroupOf M = oTwoUpper (X.subgroupOf M) := by
    have h1 := oTwoUpper_map M.subtype (X.subgroupOf M)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM, ← hXo] at h1
    apply Subgroup.map_injective M.subtype_injective
    rw [← h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM]
  have hXbo : Xb = oTwoUpper Xb := by
    rw [hXb, oTwoUpper_map, ← hXo']
  have hxb3 : xb ^ 3 = 1 := by rw [hxb, ← map_pow, ← map_one π]; congr 1; exact Subtype.ext hx3
  have hgen := exists_pow_mul_of_relIndex_three hX3 hxX hxo
  have hgenb : ∀ y ∈ Xb, ∃ k : ℕ, ∃ q ∈ Qb, y = xb ^ k * q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, q, hq, hyq⟩ := hgen y hy
    refine ⟨k, π ⟨q, hQM hq⟩, ⟨⟨q, hQM hq⟩, hq, rfl⟩, ?_⟩
    rw [hxb, ← map_pow, ← map_mul]
    congr 1
    exact Subtype.ext hyq
  have hxQb : ∀ q ∈ Qb, xb * q * xb⁻¹ ∈ Qb := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨x, hxM⟩ * q * ⟨x, hxM⟩⁻¹, ?_, by rw [hxb, map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX)
      q).mp hq
  have hMbs : Group.IsSolvable (↥M ⧸ N) := by
    have := hMs
    exact Group.isSolvable_of_surjective hπs
  have hMb2 : CFSG.Open.pCore 2 (↥M ⧸ N) = ⊥ := B6.pCore_quotient_pCore
  obtain ⟨p, hp, hp2, hnc⟩ := exists_odd_pCore_not_centralized hMbs hMb2 hQb2 hQb1
  have : Fact p.Prime := ⟨hp⟩
  have hrankb : CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ N)) ≤ 2 := by
    have hN2 : ¬ p ∣ Nat.card N := by
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
      rw [hn]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    rw [CFSG.SectionRank.pRank_quotient_eq N hN2, pRank_top_subtype]
    exact hrank p hp hp2
  obtain ⟨D, hDn, -, hDexp, hstruct, hirrD, ⟨db, hdbD, hdbx⟩, h9⟩ :=
    exists_section_of_not_centralizes hp2 hrankb hQb2 hQbXb hXbo hxb3 hgenb hxQb hnc
  have hDp : IsPGroup p D := by
    rcases hstruct with ⟨h, -⟩ | ⟨h, -⟩ <;> exact IsPGroup.of_card h
  set Y' : Subgroup M := oTwoUpper (D.comap π) with hY'
  set Y : Subgroup G := Y'.map M.subtype with hY
  have hY'map : Y'.map π = D := by
    rw [hY', ← oTwoUpper_map, Subgroup.map_comap_eq_self_of_surjective hπs,
      oTwoUpper_eq_self_of_isPGroup hp2 hDp]
  have hYo : Y = oTwoUpper ((D.comap π).map M.subtype) := by rw [hY, hY', oTwoUpper_map]
  have hYM : Y ≤ M := Subgroup.map_subtype_le Y'
  have hmemY : ∀ y : G, y ∈ Y ↔ ∃ hy : y ∈ M, (⟨y, hy⟩ : M) ∈ Y' := by
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y'.2, hy'⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨_, hy', rfl⟩
  have hY'D : ∀ y' : M, y' ∈ Y' → π y' ∈ D := fun y' hy' => hY'map ▸ ⟨y', hy', rfl⟩
  have hlift : ∀ d ∈ D, ∃ y' ∈ Y', π y' = d := fun d hd => by
    rw [← hY'map] at hd
    exact hd
  have hMY : M ≤ Subgroup.normalizer (Y : Set G) := by
    have h1 : M ≤ Subgroup.normalizer (((D.comap π).map M.subtype : Subgroup G) : Set G) := by
      intro m hm
      refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
      obtain ⟨y', hy', rfl⟩ := hy
      refine ⟨⟨m, hm⟩ * y' * ⟨m, hm⟩⁻¹, ?_, by simp⟩
      show π _ ∈ D
      rw [map_mul, map_mul, map_inv]
      exact hDn.conj_mem _ hy' _
    rw [hYo]
    exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
  have hO2 : pCoreOf 2 Y = Y ⊓ R := by
    apply le_antisymm
    · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 Y) ?_
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYM)
        (hMY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)
      intro y hy
      refine A4.mem_normalizer_of_conj_mem fun z hz => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hMY (hYM hy)) z).mp hz.1
      · exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hYM hy)) z).mp hz.2
  have hmemO2 : ∀ y : G, y ∈ pCoreOf 2 Y ↔ ∃ hy : y ∈ M, (⟨y, hy⟩ : M) ∈ Y' ∧
      π ⟨y, hy⟩ = 1 := by
    intro y
    rw [hO2, Subgroup.mem_inf, hmemY]
    constructor
    · rintro ⟨⟨hy, hy'⟩, hyR⟩
      exact ⟨hy, hy', (hπ1 _).mpr hyR⟩
    · rintro ⟨hy, hy', h1⟩
      exact ⟨⟨hy, hy'⟩, (hπ1 ⟨y, hy⟩).mp h1⟩
  have hYcomm : ⁅Y, Y⁆ = (⁅Y', Y'⁆).map M.subtype := by rw [hY, Subgroup.map_commutator]
  have hDcomm : ⁅D, D⁆ = (⁅Y', Y'⁆).map π := by rw [Subgroup.map_commutator, hY'map]
  set K₀ := ⁅Y, Y⁆ ⊔ pCoreOf 2 Y with hK₀
  have hK₀Y : K₀ ≤ Y := sup_le (commutator_le_self Y) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hmemK₀ : ∀ y' : M, y' ∈ Y' → ((y' : G) ∈ K₀ ↔ π y' ∈ ⁅D, D⁆) := by
    intro y' hy'
    constructor
    · intro hy
      have hle : K₀ ≤ ((⁅D, D⁆.comap π).map M.subtype) := by
        refine sup_le ?_ ?_
        · rw [hYcomm]
          rintro _ ⟨c, hc, rfl⟩
          exact ⟨c, by rw [hDcomm]; exact ⟨c, hc, rfl⟩, rfl⟩
        · intro z hz
          obtain ⟨hzM, -, h1⟩ := (hmemO2 z).mp hz
          exact ⟨⟨z, hzM⟩, Subgroup.mem_comap.mpr (by rw [h1]; exact Subgroup.one_mem _), rfl⟩
      obtain ⟨y'', hy'', he⟩ := hle hy
      rw [show y' = y'' from Subtype.ext he.symm]
      exact hy''
    · intro hd
      rw [hDcomm] at hd
      obtain ⟨c, hc, hce⟩ := hd
      have hcY' : c ∈ Y' := commutator_le_self Y' hc
      have h1 : (y' : G) = (c : G) * ((c⁻¹ * y' : M) : G) := by simp
      rw [h1]
      refine Subgroup.mul_mem_sup (by rw [hYcomm]; exact ⟨c, hc, rfl⟩) ?_
      refine (hmemO2 _).mpr ⟨(c⁻¹ * y').2, Y'.mul_mem (Y'.inv_mem hcY') hy', ?_⟩
      rw [show (⟨((c⁻¹ * y' : M) : G), (c⁻¹ * y').2⟩ : M) = c⁻¹ * y' from rfl, map_mul,
        map_inv, hce, inv_mul_cancel]
  have hidx : (pCoreOf 2 Y).relIndex Y = Nat.card D := by
    let ψ : ↥Y →* (↥M ⧸ N) := π.comp (Subgroup.inclusion hYM)
    have hker : ψ.ker = (pCoreOf 2 Y).subgroupOf Y := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hmemO2]
      constructor
      · intro h
        obtain ⟨hy, hy'⟩ := (hmemY y).mp y.2
        exact ⟨hy, hy', h⟩
      · rintro ⟨hy, -, h⟩
        exact h
    have hrange : ψ.range = D := by
      rw [← hY'map]
      ext d
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨hy, hy'⟩ := (hmemY y).mp y.2
        exact ⟨⟨y, hy⟩, hy', rfl⟩
      · rintro ⟨y', hy', rfl⟩
        exact ⟨⟨y', (hmemY _).mpr ⟨y'.2, hy'⟩⟩, rfl⟩
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange]
  have hpow : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y := by
    intro y hy
    obtain ⟨hyM, hy'⟩ := (hmemY y).mp hy
    refine (hmemO2 _).mpr ⟨M.pow_mem hyM p, Y'.pow_mem hy' p, ?_⟩
    rw [show (⟨y ^ p, M.pow_mem hyM p⟩ : M) = ⟨y, hyM⟩ ^ p from rfl, map_pow]
    exact hDexp _ (hY'D _ hy')
  have hirr : ∀ Y₁ : Subgroup G, K₀ ≤ Y₁ → Y₁ ≤ Y → Q ≤ Subgroup.normalizer (Y₁ : Set G) →
      Y₁ = K₀ ∨ Y₁ = Y := by
    intro Y₁ hK₁ hY₁ hQY₁
    set D₁ := (Y₁.subgroupOf M).map π with hD₁
    have hD₁D : D₁ ≤ D := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyM, hy'⟩ := (hmemY y).mp (hY₁ hy)
      exact hY'D _ hy'
    have hcD₁ : ⁅D, D⁆ ≤ D₁ := by
      intro d hd
      rw [hDcomm] at hd
      obtain ⟨c, hc, rfl⟩ := hd
      refine ⟨c, ?_, rfl⟩
      exact hK₁ (Subgroup.mem_sup_left (by rw [hYcomm]; exact ⟨c, hc, rfl⟩))
    have hQD₁ : Qb ≤ Subgroup.normalizer (D₁ : Set (↥M ⧸ N)) := by
      rintro _ ⟨q, hq, rfl⟩
      refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨q * y * q⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hQY₁ hq) y).mp hy
    rcases hirrD D₁ hcD₁ hD₁D hQD₁ with h | h
    · left
      refine le_antisymm (fun y hy => ?_) hK₁
      obtain ⟨hyM, hy'⟩ := (hmemY y).mp (hY₁ hy)
      rw [show y = ((⟨y, hyM⟩ : M) : G) from rfl, hmemK₀ _ hy', ← h]
      exact ⟨⟨y, hyM⟩, hy, rfl⟩
    · right
      refine le_antisymm hY₁ (fun y hy => ?_)
      obtain ⟨hyM, hy'⟩ := (hmemY y).mp hy
      have hd : π ⟨y, hyM⟩ ∈ D₁ := h ▸ hY'D _ hy'
      obtain ⟨y₁, hy₁, he⟩ := hd
      have hy₁Y : (y₁ : G) ∈ Y := hY₁ hy₁
      obtain ⟨hy₁M, hy₁'⟩ := (hmemY _).mp hy₁Y
      have hdiff : ((y₁⁻¹ * ⟨y, hyM⟩ : M) : G) ∈ pCoreOf 2 Y := by
        refine (hmemO2 _).mpr ⟨(y₁⁻¹ * ⟨y, hyM⟩).2, Y'.mul_mem (Y'.inv_mem hy₁') hy', ?_⟩
        rw [show (⟨((y₁⁻¹ * ⟨y, hyM⟩ : M) : G), (y₁⁻¹ * ⟨y, hyM⟩).2⟩ : M) =
          y₁⁻¹ * ⟨y, hyM⟩ from rfl, map_mul, map_inv, he, inv_mul_cancel]
      have h1 : y = (y₁ : G) * ((y₁⁻¹ * ⟨y, hyM⟩ : M) : G) := by simp
      rw [h1]
      exact Y₁.mul_mem hy₁ (hK₁ (Subgroup.mem_sup_right hdiff))
  have hxnt : ∃ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∉ K₀ := by
    obtain ⟨y', hy', rfl⟩ := hlift db hdbD
    refine ⟨y', (hmemY _).mpr ⟨y'.2, hy'⟩, fun hK => hdbx ?_⟩
    have hz : (⟨x, hxM⟩ * y' * ⟨x, hxM⟩⁻¹ * y'⁻¹ : M) ∈ Y' := by
      have h1 : x * (y' : G) * x⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hMY hxM) _).mp ((hmemY _).mpr ⟨y'.2, hy'⟩)
      obtain ⟨h2M, h2⟩ := (hmemY _).mp h1
      exact Y'.mul_mem h2 (Y'.inv_mem hy')
    have := (hmemK₀ _ hz).mp hK
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at this
  have hYo' : Y = oTwoUpper Y := by rw [hYo, oTwoUpper_oTwoUpper]
  have hRYT : R ≤ pCoreOf 2 (Y ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRT.trans le_sup_right)
      ((sup_le hYM hTM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hcard : ((pCoreOf 2 Y).relIndex Y = p ^ 2 ∧ ⁅Y, Y⁆ ≤ pCoreOf 2 Y) ∨
      ((pCoreOf 2 Y).relIndex Y = p ^ 3 ∧ ¬ ⁅Y, Y⁆ ≤ pCoreOf 2 Y) := by
    rcases hstruct with ⟨h, hab⟩ | ⟨h, hab⟩
    · left
      refine ⟨hidx.trans h, ?_⟩
      rw [hYcomm, Subgroup.map_le_iff_le_comap]
      intro c hc
      have hcY' : c ∈ Y' := commutator_le_self Y' hc
      refine (hmemO2 _).mpr ⟨c.2, hcY', ?_⟩
      have h1 : π c ∈ ⁅D, D⁆ := by rw [hDcomm]; exact ⟨c, hc, rfl⟩
      have h2 : ⁅D, D⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro a ha b hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hab a ha b hb
      rw [h2, Subgroup.mem_bot] at h1
      exact h1
    · right
      refine ⟨hidx.trans h, fun hle => hab ?_⟩
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := hlift a ha
      obtain ⟨b', hb', rfl⟩ := hlift b hb
      have hc : ((⁅a', b'⁆ : M) : G) ∈ pCoreOf 2 Y :=
        hle (by rw [hYcomm]; exact ⟨_, Subgroup.commutator_mem_commutator ha' hb', rfl⟩)
      obtain ⟨h1M, h1Y, h1⟩ := (hmemO2 _).mp hc
      rw [show (⟨((⁅a', b'⁆ : M) : G), _⟩ : M) = ⁅a', b'⁆ from rfl, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
  have hXi : IsXi T Y := by
    refine ⟨hYo', hTM.trans hMY, fun h => hR (le_bot_iff.mp (h ▸ hRYT)), p, hp, hp2, hpow, ?_,
      fun Y₁ hK₁ hY₁ hTY₁ => hirr Y₁ hK₁ hY₁ (hQT.trans hTY₁)⟩
    rcases hcard with ⟨h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨p, Y, x, hp, hp2, hYM, hMY, hXi, hpow, ?_, fun hp3 => hidx.trans (h9 hp3), hxX, hxo,
    hxnt, hirr⟩
  rcases hcard with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end Lift

end CFSG.Quasithin.EmptyFaithfulMultiple

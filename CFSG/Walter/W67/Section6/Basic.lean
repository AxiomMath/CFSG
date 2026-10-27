module

public import CFSG.Walter.W67.Transport
public import CFSG.Walter.W67.Lemma26i
public import CFSG.Walter.W67.Section5.Prop52

public section

namespace CFSG.Walter.W67

namespace Sec6

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] (s : Std G)

theorem eX_eq (Y : Subgroup G) : s.eX Y = Nat.card Y := by
  rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]

theorem exists_generator :
    ∃ g ∈ s.fr.E, Subgroup.zpowers g = s.fr.E := by
  obtain ⟨g, hg, hgen⟩ := s.fr.exists_generator_E
  rw [s.F_eq_bot, sup_bot_eq] at hgen
  exact ⟨g, hg, hgen⟩

theorem E_comm :
    ∀ x ∈ s.fr.E, ∀ y ∈ s.fr.E, x * y = y * x := by
  obtain ⟨g, -, hgen⟩ := exists_generator s
  intro x hx y hy
  rw [← hgen] at hx hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (Commute.zpow_zpow_self g i j).eq

theorem isCyclic_E : IsCyclic s.fr.E := by
  obtain ⟨g, hg, hgen⟩ := exists_generator s
  refine ⟨⟨⟨g, hg⟩, fun x => ?_⟩⟩
  have hx : (x : G) ∈ Subgroup.zpowers g := by rw [hgen]; exact x.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem E_le_centralizer
    {X : Subgroup G} (hXE : X ≤ s.fr.E) :
    s.fr.E ≤ Subgroup.centralizer (X : Set G) := fun e he =>
  Subgroup.mem_centralizer_iff.mpr fun x hx => E_comm s x (hXE hx) e he

theorem E_le_normalizer
    {X : Subgroup G} (hXE : X ≤ s.fr.E) :
    s.fr.E ≤ Subgroup.normalizer (X : Set G) :=
  (E_le_centralizer s hXE).trans (Subgroup.centralizer_le_normalizer _)

theorem F_le {X : Subgroup G} : s.F ≤ X := by rw [s.F_eq_bot]; exact bot_le

theorem normalizer_eq {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) = s.L X ⊔ s.fr.E :=
  (s.L_spec X hXE hX).normalizer_eq (F_le s)

theorem L_le_normalizer {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    s.L X ≤ Subgroup.normalizer (X : Set G) :=
  (s.L_spec X hXE hX).normal.1

theorem L_le_centralizer {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    s.L X ≤ Subgroup.centralizer (X : Set G) :=
  (s.L_spec X hXE hX).le_centralizer

theorem normalizer_le_normalizer_L {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer ((s.L X : Subgroup G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (L_le_normalizer s hXE hX)).mp
    (s.L_spec X hXE hX).normal.2

theorem E_le_normalizer_L
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    s.fr.E ≤ Subgroup.normalizer ((s.L X : Subgroup G) : Set G) :=
  (E_le_normalizer s hXE).trans (normalizer_le_normalizer_L s hXE hX)

theorem jr {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    ∃ K' : Subgroup G, IsJRSubgroup (s.L X) s.J K' s.p (s.f / Nat.card X) ∧
      (3 < s.p ^ (s.f / Nat.card X) → K' = s.KX X) := by
  obtain ⟨K', hK', h3⟩ := (s.L_spec X hXE hX).jr
  rw [eX_eq] at hK' h3
  exact ⟨K', hK', h3⟩

theorem card_dvd_f
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) : Nat.card X ∣ s.f := by
  have := (lemma_2_6_i G s.toHyp s.fr hXE hX).1
  rwa [eX_eq] at this

theorem f_div_pos
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) : 0 < s.f / Nat.card X :=
  Nat.div_pos (Nat.le_of_dvd s.f_pos (card_dvd_f s hXE hX)) Nat.card_pos

theorem mem_of_odd_of_mem_zpowers_sup {K' : Subgroup G} (hK' : K' ≤ Subgroup.centralizer
    ({s.J} : Set G)) (hJK' : s.J ∉ K') {x : G} (hx : x ∈ Subgroup.zpowers s.J ⊔ K')
    (hodd : Odd (orderOf x)) : x ∈ K' := by
  have hC : K' ≤ Subgroup.centralizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hkJ : Commute k s.J := Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)
    exact (hkJ.zpow_right n).symm.eq
  have hN : K' ≤ Subgroup.normalizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) :=
    hC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨j, hj, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx
  rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
  · rwa [one_mul]
  exfalso
  obtain ⟨n, hn⟩ := hodd
  have hc : Commute s.J k := (Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)).symm
  have h1 : (s.J * k) ^ orderOf (s.J * k) = 1 := pow_orderOf_eq_one _
  rw [hc.mul_pow, hn, pow_succ, pow_mul, pow_two, s.J_mul_J, one_pow, one_mul] at h1
  have hJ : s.J = (k ^ (2 * n + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact hJK' (hJ ▸ K'.inv_mem (K'.pow_mem hk _))

theorem L_inf_E_le {X : Subgroup G} {K' : Subgroup G} {g : ℕ}
    (hK' : IsJRSubgroup (s.L X) s.J K' s.p g) : s.L X ⊓ s.fr.E ≤ K' := by
  intro e he
  obtain ⟨heL, heE⟩ := Subgroup.mem_inf.mp he
  have heH : e ∈ s.H := s.fr.E_le_H heE
  have he' : e ∈ s.L X ⊓ Subgroup.centralizer ({s.J} : Set G) := Subgroup.mem_inf.mpr ⟨heL, heH⟩
  rw [hK'.centralizer_eq] at he'
  exact mem_of_odd_of_mem_zpowers_sup s (hK'.K_le.trans inf_le_right) hK'.J_not_mem he'
    (odd_orderOf_of_mem_oddPart heE)

theorem L_inf_E_of_three_lt
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (h3 : 3 < s.p ^ (s.f / Nat.card X)) : s.L X ⊓ s.fr.E = ⊥ := by
  obtain ⟨K', hK', hK'X⟩ := jr s hXE hX
  rw [eq_bot_iff]
  intro e he
  have heK' := L_inf_E_le s hK' he
  rw [hK'X h3] at heK'
  have : e ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨heK'.1, (Subgroup.mem_inf.mp he).2⟩
  rwa [s.fr.K_inf_E] at this

theorem L_inf_E_of_not_three_dvd
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (h3 : ¬ 3 ∣ Nat.card s.fr.E) : s.L X ⊓ s.fr.E = ⊥ := by
  by_cases hq : 3 < s.p ^ (s.f / Nat.card X)
  · exact L_inf_E_of_three_lt s hXE hX hq
  obtain ⟨K', hK', -⟩ := jr s hXE hX
  obtain ⟨eK'⟩ := hK'.iso
  have hpos := f_div_pos s hXE hX
  have hFcard : Nat.card (GaloisField s.p (s.f / Nat.card X)) = s.p ^ (s.f / Nat.card X) :=
    GaloisField.card _ _ hpos.ne'
  have hq3 : s.p ^ (s.f / Nat.card X) = 3 := by
    have hp3 : 3 ≤ s.p := by
      have := (Fact.out : s.p.Prime).two_le
      have := s.p_ne_two
      omega
    have : s.p ≤ s.p ^ (s.f / Nat.card X) := Nat.le_self_pow hpos.ne' _
    omega
  have hK'card : Nat.card K' = 12 := by
    rw [Nat.card_congr eK'.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
      ⟨s.p, s.f / Nat.card X, Fact.out, s.odd_p, hpos, hFcard⟩, hFcard, hq3]
    norm_num
  rw [eq_bot_iff]
  intro e he
  have heK' := L_inf_E_le s hK' he
  have heE := (Subgroup.mem_inf.mp he).2
  have hodd : Odd (orderOf e) := odd_orderOf_of_mem_oddPart heE
  have hdvd12 : orderOf e ∣ 12 := hK'card ▸ Subgroup.orderOf_dvd_natCard K' heK'
  have hdvdE : orderOf e ∣ Nat.card s.fr.E := Subgroup.orderOf_dvd_natCard _ heE
  have h13 : orderOf e ∣ 3 := by
    have h4 : Nat.Coprime (orderOf e) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_left.mpr hodd).symm
    have : orderOf e ∣ 2 ^ 2 * 3 := by simpa using hdvd12
    exact h4.dvd_of_dvd_mul_left this
  rw [Subgroup.mem_bot]
  rcases (Nat.dvd_prime Nat.prime_three).mp h13 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ hdvdE) h3

theorem exists_jrGroup
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    ∃ K' : Subgroup G, IsJRSubgroup (s.L X) s.J K' s.p (s.f / Nat.card X) ∧
      (3 < s.p ^ (s.f / Nat.card X) → K' = s.KX X) ∧
      ∃ hL : JRGroup (s.L X), hL.p = s.p ∧ hL.f = s.f / Nat.card X ∧ (hL.J : G) = s.J ∧
        hL.K.map (s.L X).subtype = K' := by
  obtain ⟨K', hK', h3⟩ := jr s hXE hX
  obtain ⟨hL, hLp, hLf, hLJ, hLK⟩ :=
    IsJRSubgroup.nonempty_jrGroup G s.p_ne_two (f_div_pos s hXE hX) hK'
  exact ⟨K', hK', h3, hL, hLp, hLf, hLJ, hLK⟩

theorem jrGroup_q {X : Subgroup G} (hL : JRGroup (s.L X)) (hLp : hL.p = s.p)
    (hLf : hL.f = s.f / Nat.card X) : hL.q = s.p ^ (s.f / Nat.card X) := by
  rw [JRGroup.q, hLp, hLf]

theorem p_eq_three_or_five
    (hR : RFacts) : s.p = 3 ∨ s.p = 5 := by
  obtain ⟨K', -, -, hL, hLp, hLf, -, -⟩ := exists_jrGroup s le_rfl s.E_ne_bot
  have hq := jrGroup_q s hL hLp hLf
  have hpos := f_div_pos s le_rfl s.E_ne_bot
  by_cases h5 : hL.q = 5
  · right
    rw [hq] at h5
    have hdvd : s.p ∣ 5 := h5 ▸ dvd_pow_self s.p hpos.ne'
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd h (Fact.out : s.p.Prime).one_lt.ne'
    · exact h
  · left
    obtain ⟨n, -, hn⟩ := (hR _ hL h5).1.1
    rw [hq] at hn
    have hdvd : s.p ∣ 3 ^ n := hn ▸ dvd_pow_self s.p hpos.ne'
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
      ((Fact.out : s.p.Prime).dvd_of_dvd_pow hdvd)

theorem p5_card_X
    (hR : RFacts) (hp : s.p = 5) {X : Subgroup G} (hXE : X ≤ s.fr.E)
    (hX : X ≠ ⊥) : Nat.card X = s.f := by
  obtain ⟨K', -, -, hL, hLp, hLf, -, -⟩ := exists_jrGroup s hXE hX
  have hq := jrGroup_q s hL hLp hLf
  have hpos := f_div_pos s hXE hX
  have hq5 : hL.q = 5 := by
    by_contra h5
    obtain ⟨n, -, hn⟩ := (hR _ hL h5).1.1
    rw [hq, hp] at hn
    have : 5 ∣ 3 ^ n := hn ▸ dvd_pow_self 5 hpos.ne'
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) this
    norm_num at this
  rw [hq, hp] at hq5
  have hf1 : s.f / Nat.card X = 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 5)
      (show 5 ^ (s.f / Nat.card X) = 5 ^ 1 by rw [hq5, pow_one])
  obtain ⟨c, hc⟩ := card_dvd_f s hXE hX
  have hcpos : 0 < Nat.card X := Nat.card_pos
  rw [hc, Nat.mul_div_cancel_left _ hcpos] at hf1
  rw [hc, hf1, mul_one]

theorem p5_eq_E
    (hR : RFacts) (hp : s.p = 5) {X : Subgroup G} (hXE : X ≤ s.fr.E)
    (hX : X ≠ ⊥) : X = s.fr.E := by
  refine Subgroup.eq_of_le_of_card_ge hXE ?_
  rw [p5_card_X s hR hp hXE hX]
  exact Nat.le_of_dvd s.f_pos (card_dvd_f s le_rfl s.E_ne_bot)

theorem p5_card_E
    (hR : RFacts) (hp : s.p = 5) :
    Nat.card s.fr.E = s.f ∧ (Nat.card s.fr.E).Prime := by
  have hEf := p5_card_X s hR hp le_rfl s.E_ne_bot
  refine ⟨hEf, ?_⟩
  have h1 : 1 < Nat.card s.fr.E := (Subgroup.one_lt_card_iff_ne_bot _).mpr s.E_ne_bot
  set r := (Nat.card s.fr.E).minFac with hr
  have hrp : r.Prime := Nat.minFac_prime h1.ne'
  have : Fact r.Prime := ⟨hrp⟩
  obtain ⟨⟨x, hx⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.E) r
    (Nat.minFac_dvd _)
  rw [Subgroup.orderOf_mk] at hox
  have hX : Subgroup.zpowers x ≤ s.fr.E := Subgroup.zpowers_le.mpr hx
  have hX1 : Subgroup.zpowers x ≠ ⊥ := by
    intro h
    have := Nat.card_zpowers x
    rw [h, Subgroup.card_bot, hox] at this
    exact hrp.one_lt.ne this
  have hXc := p5_card_X s hR hp hX hX1
  rw [Nat.card_zpowers, hox, ← hEf] at hXc
  rw [← hXc]
  exact hrp

theorem mem_sigma_iff {r : ℕ} : r ∈ s.fr.σ ↔ r.Prime ∧ r ∣ Nat.card s.fr.E := by
  rw [Frame.σ, Nat.mem_primeFactors]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, Nat.card_pos.ne'⟩⟩

theorem prop_5_2'
    (hJ : JFacts) (hR : RFacts) (hp : s.p = 5) : ¬ 5 ∣ Nat.card s.fr.E :=
  prop_5_2_of lemma_2_6_i IsJRSubgroup.nonempty_jrGroup G s hp hJ hR

theorem p5_card_E_mem
    (h41 : S_prop_4_1) (hJ : JFacts) (hR : RFacts) (hp : s.p = 5) :
    Nat.card s.fr.E = 7 ∨ Nat.card s.fr.E = 11 ∨ Nat.card s.fr.E = 19 := by
  obtain ⟨-, hprime⟩ := p5_card_E s hR hp
  have hr : Nat.card s.fr.E ∈ s.fr.σ := (mem_sigma_iff s).mpr ⟨hprime, dvd_rfl⟩
  rcases (h41 G s hJ hR hr).2 hp with h | h | h | h
  · exact absurd (h ▸ dvd_rfl) (prop_5_2' s hJ hR hp)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem p3_mem_sigma (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    (hp : s.p = 3) {r : ℕ} (hr : r ∈ s.fr.σ) : r ≠ 3 ∧ r ∣ s.q ^ 2 - s.q + 1 := by
  have h3 : r ≠ 3 := by
    rintro rfl
    exact h56 G s hp hR ((mem_sigma_iff s).mp hr).2
  rcases (h41 G s hJ hR hr).1 hp with h | h
  · exact absurd h h3
  · exact ⟨h3, h⟩

theorem card_K : Nat.card s.K = s.q * (s.q ^ 2 - 1) / 2 := by
  have hFcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f := GaloisField.card _ _ s.f_pos.ne'
  rw [Nat.card_congr s.iso.toEquiv, CFSG.GorensteinWalter.psl2_card_formula _
    ⟨s.p, s.f, Fact.out, s.odd_p, s.f_pos, hFcard⟩, hFcard]
  rfl

theorem card_K_dvd : Nat.card s.K ∣ s.q * (s.q ^ 2 - 1) := by
  rw [card_K]
  exact Nat.div_dvd_of_dvd (by
    have hq : Odd s.q := (s.odd_p).pow
    have : Even (s.q ^ 2 - 1) := by
      have h1 : Odd (s.q ^ 2) := hq.pow
      exact Nat.Odd.sub_odd h1 odd_one
    exact (this.mul_left _).two_dvd)

theorem not_dvd_of_dvd_cyclotomic_six {r q : ℕ} (hr : r.Prime) (hr3 : r ≠ 3)
    (hdvd : r ∣ q ^ 2 - q + 1) : ¬ r ∣ q * (q ^ 2 - 1) := by
  have : Fact r.Prime := ⟨hr⟩
  intro hK
  have hq1 : q ≤ q ^ 2 := by nlinarith [Nat.zero_le q]
  have h1 : ((q : ZMod r)) ^ 2 - q + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast [Nat.cast_sub hq1] at this
    exact this
  by_cases hq0 : q = 0
  · subst hq0
    simp at h1
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)
  have h2 : ((q : ZMod r)) * ((q : ZMod r) ^ 2 - 1) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hK
    push_cast [Nat.cast_sub hq2] at this
    exact this
  rcases mul_eq_zero.mp h2 with h | h
  · rw [h] at h1
    simp at h1
  · have hx : (q : ZMod r) = 2 := by linear_combination h - h1
    rw [hx] at h
    have h3 : ((3 : ℕ) : ZMod r) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)

theorem not_dvd_q_mul
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {r : ℕ} (hr : r ∈ s.fr.σ) : ¬ r ∣ s.q * (s.q ^ 2 - 1) := by
  have hrp : r.Prime := ((mem_sigma_iff s).mp hr).1
  intro hK'
  rcases p_eq_three_or_five s hR with hp | hp
  · obtain ⟨hr3, hdvd⟩ := p3_mem_sigma s h41 h56 hJ hR hp hr
    exact not_dvd_of_dvd_cyclotomic_six hrp hr3 hdvd hK'
  · obtain ⟨hEf, hEp⟩ := p5_card_E s hR hp
    have hrE : r = Nat.card s.fr.E := by
      have := ((mem_sigma_iff s).mp hr).2
      exact (Nat.prime_dvd_prime_iff_eq hrp hEp).mp this
    have hq : s.q = 5 ^ r := by rw [Hyp.q, hp, hrE, hEf]
    have : Fact r.Prime := ⟨hrp⟩
    have h120 : ((s.q * (s.q ^ 2 - 1) : ℕ) : ZMod r) = ((120 : ℕ) : ZMod r) := by
      have hq1 : 1 ≤ s.q ^ 2 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
      push_cast [Nat.cast_sub hq1]
      rw [hq]
      push_cast
      rw [ZMod.pow_card]
      norm_num
    have h0 := (ZMod.natCast_eq_zero_iff _ _).mpr hK'
    rw [h120, ZMod.natCast_eq_zero_iff] at h0
    rcases p5_card_E_mem s h41 hJ hR hp with h | h | h <;> rw [← hrE] at h <;> subst h <;>
      norm_num at h0

theorem not_dvd_card_K
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {r : ℕ} (hr : r ∈ s.fr.σ) : ¬ r ∣ Nat.card s.K := fun hK =>
  not_dvd_q_mul s h41 h56 hJ hR hr (hK.trans (card_K_dvd s))

theorem coprime_q_mul_E
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts) :
    Nat.Coprime (s.q * (s.q ^ 2 - 1)) (Nat.card s.fr.E) := by
  refine Nat.coprime_of_dvd fun k hk hkq hkE => ?_
  exact not_dvd_q_mul s h41 h56 hJ hR ((mem_sigma_iff s).mpr ⟨hk, hkE⟩) hkq

theorem q_mul_dvd
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    s.p ^ (s.f / Nat.card X) * ((s.p ^ (s.f / Nat.card X)) ^ 2 - 1) ∣ s.q * (s.q ^ 2 - 1) := by
  obtain ⟨c, hc⟩ := card_dvd_f s hXE hX
  have hcpos : 0 < Nat.card X := Nat.card_pos
  have hfc : s.f / Nat.card X = c := by rw [hc, Nat.mul_div_cancel_left _ hcpos]
  rw [hfc]
  have hq : s.q = (s.p ^ c) ^ Nat.card X := by rw [Hyp.q, ← pow_mul, hc, mul_comm]
  rw [hq]
  apply mul_dvd_mul
  · exact dvd_pow_self _ hcpos.ne'
  · have e : ((s.p ^ c) ^ Nat.card X) ^ 2 - 1 = ((s.p ^ c) ^ 2) ^ Nat.card X - 1 ^ Nat.card X := by
      rw [one_pow]
      congr 1
      ring
    rw [e]
    exact Nat.sub_dvd_pow_sub_pow _ _ _

theorem coprime_card_K_E
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts) :
    Nat.Coprime (Nat.card s.K) (Nat.card s.fr.E) := by
  refine Nat.coprime_of_dvd fun k hk hkK hkE => ?_
  exact not_dvd_card_K s h41 h56 hJ hR ((mem_sigma_iff s).mpr ⟨hk, hkE⟩) hkK

theorem not_three_dvd_card_E
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts)
    (hR : RFacts) : ¬ 3 ∣ Nat.card s.fr.E := by
  rcases p_eq_three_or_five s hR with hp | hp
  · exact h56 G s hp hR
  · rcases p5_card_E_mem s h41 hJ hR hp with h | h | h <;> rw [h] <;> decide

theorem L_inf_E
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) : s.L X ⊓ s.fr.E = ⊥ :=
  L_inf_E_of_not_three_dvd s hXE hX (not_three_dvd_card_E s h41 h56 hJ hR)

theorem card_normalizer
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    Nat.card (Subgroup.normalizer (X : Set G)) = Nat.card (s.L X) * Nat.card s.fr.E := by
  rw [normalizer_eq s hXE hX, sup_comm]
  have h := Sec52.card_sup_mul_card_inf (E_le_normalizer_L s hXE hX)
  rw [L_inf_E s h41 h56 hJ hR hXE hX, Subgroup.card_bot, mul_one] at h
  exact h

end Sec6

end CFSG.Walter.W67

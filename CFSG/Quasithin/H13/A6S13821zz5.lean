module

public import CFSG.Quasithin.H13.U3X10
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Ord
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem le_center_of_normal_ne_top {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) {N : Subgroup Q} [hN : N.Normal]
    (hNt : N ≠ ⊤) : N ≤ Subgroup.center Q := by
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hmn : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases hmn.eq_bot_or_eq_top with hbot | htop
  · intro x hx
    have h1 : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    apply hNt
    have hdec : ∀ a : Q, ∃ n ∈ N, n⁻¹ * a ∈ Subgroup.center Q := by
      intro a
      have h1 : π a ∈ N.map π := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := h1
      refine ⟨n, hn, ?_⟩
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hna
      exact hna
    rw [eq_top_iff, ← hperf]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    obtain ⟨n, hn, hz⟩ := hdec a
    obtain ⟨n', hn', hz'⟩ := hdec b
    set z := n⁻¹ * a with hzdef
    set z' := n'⁻¹ * b with hz'def
    have ha : a = n * z := by rw [hzdef]; group
    have hb : b = n' * z' := by rw [hz'def]; group
    have hzc : ∀ g : Q, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
    have hzc' : ∀ g : Q, z' * g = g * z' := fun g => (Subgroup.mem_center_iff.mp hz' g).symm
    have e : ⁅a, b⁆ = ⁅n, n'⁆ := by
      rw [commutatorElement_def, commutatorElement_def, ha, hb]
      calc n * z * (n' * z') * (n * z)⁻¹ * (n' * z')⁻¹
          = n * (z * n') * z' * z⁻¹ * n⁻¹ * z'⁻¹ * n'⁻¹ := by group
        _ = n * (n' * z) * z' * z⁻¹ * n⁻¹ * z'⁻¹ * n'⁻¹ := by rw [hzc n']
        _ = n * n' * (z * z' * z⁻¹) * n⁻¹ * z'⁻¹ * n'⁻¹ := by group
        _ = n * n' * z' * n⁻¹ * z'⁻¹ * n'⁻¹ := by
          rw [show z * z' * z⁻¹ = z' by rw [hzc z']; group]
        _ = n * n' * (z' * n⁻¹) * z'⁻¹ * n'⁻¹ := by group
        _ = n * n' * (n⁻¹ * z') * z'⁻¹ * n'⁻¹ := by rw [hzc' n⁻¹]
        _ = n * n' * n⁻¹ * n'⁻¹ := by group
    rw [e, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn hn') (N.inv_mem hn)) (N.inv_mem hn')

theorem card_quot_center_of_surjective {Q R : Type*} [Group Q] [Group R] [Finite Q]
    (hperf : commutator Q = ⊤) (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) {φ : Q →* R}
    (hφ : Function.Surjective φ) [Nontrivial R] :
    Nat.card (R ⧸ Subgroup.center R) = Nat.card (Q ⧸ Subgroup.center Q) ∧
      Nat.card (Subgroup.center R) ∣ Nat.card (Subgroup.center Q) := by
  classical
  have hperfR : commutator R = ⊤ := by
    rw [commutator, ← Subgroup.map_top_of_surjective φ hφ, ← Subgroup.map_commutator, ← commutator,
      hperf, Subgroup.map_top_of_surjective φ hφ]
  have hZR : Subgroup.center R ≠ ⊤ := by
    intro h
    obtain ⟨r, hr⟩ := exists_ne (1 : R)
    apply hr
    have h1 : r ∈ commutator R := by rw [hperfR]; exact Subgroup.mem_top r
    have h2 : commutator R = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y
      exact this
    rw [h2] at h1
    exact h1
  set P := (Subgroup.center R).comap φ with hP
  have hPn : P.Normal := Subgroup.Normal.comap inferInstance φ
  have hPt : P ≠ ⊤ := by
    intro h
    apply hZR
    rw [eq_top_iff]
    intro r _
    obtain ⟨a, rfl⟩ := hφ r
    have : a ∈ P := by rw [h]; exact Subgroup.mem_top a
    exact this
  have hPZ : P ≤ Subgroup.center Q := le_center_of_normal_ne_top hperf hs hPt
  have hZP : Subgroup.center Q ≤ P := by
    intro z hz
    rw [hP, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro r
    obtain ⟨a, rfl⟩ := hφ r
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz a)]
  have hPeq : P = Subgroup.center Q := le_antisymm hPZ hZP
  set f := QuotientGroup.map (Subgroup.center Q) (Subgroup.center R) φ hZP with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hφ r
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hfi : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker] at hx
    have h1 : φ a ∈ Subgroup.center R := by
      have := hx
      rw [hf, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at this
      exact this
    have h2 : a ∈ Subgroup.center Q := hPZ h1
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact h2
  refine ⟨(Nat.card_congr (MulEquiv.ofBijective f ⟨hfi, hfs⟩).toEquiv).symm, ?_⟩
  have hZmap : Subgroup.center R = (Subgroup.center Q).map φ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨a, rfl⟩ := hφ r
      exact ⟨a, hPZ hr, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hZP ha
  rw [hZmap]
  exact Subgroup.card_map_dvd _ _

theorem two_pow_mul_odd_inj {a b O O' : ℕ} (hO : Odd O) (hO' : Odd O')
    (h : 2 ^ a * O = 2 ^ b * O') : a = b ∧ O = O' := by
  have hc₁ : Nat.Coprime (2 ^ a) O' := (Nat.coprime_two_left.2 hO').pow_left _
  have hc₂ : Nat.Coprime (2 ^ b) O := (Nat.coprime_two_left.2 hO).pow_left _
  have h1 : a ≤ b := by
    have hdvd : 2 ^ a ∣ 2 ^ b * O' := ⟨O, h.symm⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc₁.dvd_of_dvd_mul_right hdvd)
  have h2 : b ≤ a := by
    have hdvd : 2 ^ b ∣ 2 ^ a * O := ⟨O', h⟩
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc₂.dvd_of_dvd_mul_right hdvd)
  have hab : a = b := le_antisymm h1 h2
  subst hab
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

theorem false_of_sl2_eq {q g z : ℕ} (hq : 4 ≤ q) (hg : g ∣ 3)
    (h : (q ^ 6 - 1) * g = (q ^ 2 - 1) * (q ^ 3 + 1) * z) : False := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hZ : ((q : ℤ) ^ 6 - 1) * g = ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 3 + 1) * z := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hq6] at this
    linear_combination this
  have hne : ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) ≠ 0 := by
    have h1 : (16 : ℤ) ≤ (q : ℤ) ^ 2 := by
      have : (4 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    have h2 : (0 : ℤ) < (q : ℤ) ^ 2 - q + 1 := by
      have : (4 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    exact mul_ne_zero (by linarith) h2.ne'
  have h1 : ((q : ℤ) ^ 2 + q + 1) * g = ((q : ℤ) + 1) * z := by
    have h2 : ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 - q + 1) *
        (((q : ℤ) ^ 2 + q + 1) * g - ((q : ℤ) + 1) * z) = 0 := by
      linear_combination hZ
    have h3 := (mul_eq_zero.mp h2).resolve_left hne
    linear_combination h3
  have h2 : (q ^ 2 + q + 1) * g = (q + 1) * z := by exact_mod_cast h1
  have h3 : q + 1 ∣ g := by
    have h4 : q + 1 ∣ (q + 1) * (q * g) + g := by
      rw [show (q + 1) * (q * g) + g = (q ^ 2 + q + 1) * g by ring, h2]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h4
  have h4 := Nat.le_of_dvd (by norm_num) (h3.trans hg)
  omega

theorem false_of_sl3_eq {q g z : ℕ} (hq : 4 ≤ q) (hg : g ∣ 3) (hz : Odd z)
    (h : (q ^ 3 - 1) * (q ^ 2 - 1) * g = (q ^ 2 - 1) * (q ^ 3 + 1) * z) : False := by
  have hq2 : 0 < q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  have h1 : (q ^ 3 - 1) * g = (q ^ 3 + 1) * z := by
    apply Nat.eq_of_mul_eq_mul_left hq2
    calc (q ^ 2 - 1) * ((q ^ 3 - 1) * g) = (q ^ 3 - 1) * (q ^ 2 - 1) * g := by ring
      _ = (q ^ 2 - 1) * (q ^ 3 + 1) * z := h
      _ = (q ^ 2 - 1) * ((q ^ 3 + 1) * z) := by ring
  have hq3 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hg3 : g = 1 ∨ g = 3 := by
    have := (Nat.dvd_prime Nat.prime_three).mp hg
    tauto
  obtain ⟨k, rfl⟩ := hz
  generalize q ^ 3 = Q at h1 hq3
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rcases hg3 with rfl | rfl <;> omega
  · have hX : (Q + 1) * 3 ≤ (Q + 1) * (2 * k + 1) := Nat.mul_le_mul_left _ (by omega)
    rcases hg3 with rfl | rfl <;> omega

theorem le_three_of_dvd {a b g : ℕ} (hcb : Nat.Coprime (a + 2) b) (hg : g ∣ 3)
    (h : a + 2 ∣ b * g) : a + 2 ≤ 3 :=
  Nat.le_of_dvd (by norm_num) ((hcb.dvd_of_dvd_mul_left h).trans hg)

theorem coprime_add_two {a b : ℕ} (ha : Odd a) (hba : b ∣ a) : Nat.Coprime (a + 2) b := by
  have hc : Nat.Coprime (a + 2) a := by
    rw [add_comm, Nat.coprime_add_self_left]
    exact Nat.coprime_two_left.mpr ha
  exact Nat.Coprime.coprime_dvd_right hba hc

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (k - 1) - 1, by omega⟩

theorem sq_sub_one_dvd {x : ℕ} : x ^ 2 - 1 ∣ x ^ 4 - 1 ∧ x ^ 2 - 1 ∣ x ^ 6 - 1 :=
  ⟨Nat.pow_sub_one_dvd_pow_sub_one x (by norm_num), Nat.pow_sub_one_dvd_pow_sub_one x (by norm_num)⟩

theorem false_of_b42Types_psu3 {X : Type} [Group X] [Finite X] (hX : Bridge.B42Types X)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n))
    (hodd : Odd (Nat.card (Subgroup.center X))) : False := by
  classical
  obtain ⟨r, hr, hUr⟩ := L1295B.two_part_ordTwistedA_two (n := n) (by omega)
  set q := 2 ^ n with hqdef
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set z := Nat.card (Subgroup.center X) with hz
  set U := ordTwistedA 2 q with hU
  set g := Nat.gcd 3 (q + 1) with hg
  have hg3 : g ∣ 3 := Nat.gcd_dvd_left _ _
  have hq21 : q + 1 ∣ q ^ 2 - 1 := ⟨q - 1, by simpa using Nat.sq_sub_sq q 1⟩
  have hUg : U * g = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [hU, GoldS146R.ordTwistedA_two_eq' q (by omega)]
    apply Nat.div_mul_cancel
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right ((Nat.gcd_dvd_right _ _).trans hq21) _) _
  have hq3 : q ^ 3 = 2 ^ (n * 3) := by rw [hqdef, ← pow_mul]
  have hrg : r * g = (q ^ 2 - 1) * (q ^ 3 + 1) := by
    have h1 : 2 ^ (n * 3) * (r * g) = 2 ^ (n * 3) * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      rw [← mul_assoc, ← hUr, hUg, hq3]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hXc : Nat.card X = U * z := by
    rw [← hcard, hz]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hX2 : Nat.card X = 2 ^ (n * 3) * (r * z) := by rw [hXc, hUr, mul_assoc]
  have hrz : Odd (r * z) := hr.mul hodd
  have hUlow : 20800 ≤ U := by
    have h1 : 62400 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
      have h2 : 64 ≤ q ^ 3 := by
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
      have h3 : 15 ≤ q ^ 2 - 1 := by
        have : 16 ≤ q ^ 2 := by nlinarith
        omega
      have h4 : 65 ≤ q ^ 3 + 1 := by omega
      calc 62400 = 64 * (15 * 65) := by norm_num
        _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4)
    have h2 : U * g ≤ U * 3 := Nat.mul_le_mul_left _ (Nat.le_of_dvd (by norm_num) hg3)
    omega
  have hz1 : 1 ≤ z := hodd.pos
  have hXlow : 20800 ≤ Nat.card X := by
    rw [hXc]
    calc 20800 ≤ U := hUlow
      _ ≤ U * z := Nat.le_mul_of_pos_right _ hz1
  have key : ∀ {a b : ℕ}, 1 ≤ a → 1 ≤ b → 2 ^ (2 * a) * (2 ^ b - 1) = 0 → False := by
    intro a b _ hb h
    have := Nat.one_le_two_pow (n := b)
    have : 2 ^ b - 1 ≠ 0 := by
      have : 2 ≤ 2 ^ b := Nat.le_self_pow (by omega) 2
      omega
    simp_all
  clear key
  rcases hX with ⟨K, _, _, m, hm, hK, ⟨e⟩⟩ | ⟨m, hm, K, _, _, hK, ⟨e⟩⟩ |
      ⟨K, _, _, m, hm, hK, ⟨e⟩⟩ | ⟨K, _, _, m, hm, hK, ⟨e⟩⟩ | ⟨K, _, _, hK, N, -, ⟨e⟩⟩ |
      ⟨m, hm, ⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | ⟨K, _, _, m, hK, hm, ⟨e⟩⟩
  ·
    have h1 : Nat.card X = 2 ^ m * (4 ^ m - 1) := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
        Vol2.Ch10.SecA.card_SL_two_pow hK]
    have hodd' : Odd (4 ^ m - 1) := by
      rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hX2)
    have h4 : q ^ 6 = 4 ^ m := by
      rw [hm3, hqdef, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    refine false_of_sl2_eq hq4 hg3 (z := z) ?_
    rw [h4, hodd2]
    calc r * z * g = (r * g) * z := by ring
      _ = (q ^ 2 - 1) * (q ^ 3 + 1) * z := by rw [hrg]
  ·
    have h1 : Nat.card X = 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
        Vol2.Ch10.SecA.card_SL_three_pow hK]
    have hodd' : Odd ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
      (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hX2)
    have hmn : m = n := by omega
    subst hmn
    refine false_of_sl3_eq hq4 hg3 hodd (z := z) ?_
    have e1 : (2 : ℕ) ^ (3 * m) = q ^ 3 := by rw [hqdef, ← pow_mul, mul_comm]
    have e2 : (2 : ℕ) ^ (2 * m) = q ^ 2 := by rw [hqdef, ← pow_mul, mul_comm]
    rw [e1, e2] at hodd2
    rw [hodd2]
    calc r * z * g = (r * g) * z := by ring
      _ = (q ^ 2 - 1) * (q ^ 3 + 1) * z := by rw [hrg]
  ·
    have h1 : Nat.card X = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) := by
      rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hK]
    have hodd' : Odd ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
      (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hX2)
    set s := 2 ^ m with hs
    have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
    have e4 : (2 : ℕ) ^ (4 * m) = s ^ 4 := by rw [hs, ← pow_mul, mul_comm]
    have hqs : q ^ 3 = s ^ 4 := by rw [hq3, ← e4, hm3]
    rw [e2, e4] at hodd2
    have hs4 : 16 ≤ s ^ 4 := by
      have : 4 ≤ s := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      calc 16 ≤ 4 ^ 4 := by norm_num
        _ ≤ s ^ 4 := Nat.pow_le_pow_left this 4
    have hdvd : s ^ 4 - 1 + 2 ∣ ((s ^ 2 - 1) * (s ^ 4 - 1)) * g := by
      have h2 : ((s ^ 2 - 1) * (s ^ 4 - 1)) * g = (q ^ 2 - 1) * (s ^ 4 + 1) * z := by
        rw [hodd2, ← hqs]
        calc r * z * g = (r * g) * z := by ring
          _ = (q ^ 2 - 1) * (q ^ 3 + 1) * z := by rw [hrg]
      rw [h2, show s ^ 4 - 1 + 2 = s ^ 4 + 1 by omega]
      exact ⟨(q ^ 2 - 1) * z, by ring⟩
    have hodd4 : Odd (s ^ 4 - 1) := by rw [← e4]; exact odd_two_pow_sub_one (by omega)
    have hc : Nat.Coprime (s ^ 4 - 1 + 2) ((s ^ 2 - 1) * (s ^ 4 - 1)) :=
      Nat.Coprime.mul_right (coprime_add_two hodd4 sq_sub_one_dvd.1)
        (coprime_add_two hodd4 dvd_rfl)
    have := le_three_of_dvd hc hg3 hdvd
    omega
  ·
    set s := 2 ^ m with hs
    have h1 : Nat.card X = 2 ^ (6 * m) * ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK, hs, ← pow_mul, mul_comm m 6]
    have e6 : (2 : ℕ) ^ (6 * m) = s ^ 6 := by rw [hs, ← pow_mul, mul_comm]
    have e2 : (2 : ℕ) ^ (2 * m) = s ^ 2 := by rw [hs, ← pow_mul, mul_comm]
    have hodd' : Odd ((s ^ 6 - 1) * (s ^ 2 - 1)) := by
      rw [← e6, ← e2]
      exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
    obtain ⟨hm3, hodd2⟩ := two_pow_mul_odd_inj hodd' hrz (h1.symm.trans hX2)
    have hqs : q ^ 3 = s ^ 6 := by rw [hq3, ← e6, hm3]
    have hs6 : 64 ≤ s ^ 6 := by
      have : 2 ≤ s := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ s ^ 6 := Nat.pow_le_pow_left this 6
    have hdvd : s ^ 6 - 1 + 2 ∣ ((s ^ 6 - 1) * (s ^ 2 - 1)) * g := by
      have h2 : ((s ^ 6 - 1) * (s ^ 2 - 1)) * g = (q ^ 2 - 1) * (s ^ 6 + 1) * z := by
        rw [hodd2, ← hqs]
        calc r * z * g = (r * g) * z := by ring
          _ = (q ^ 2 - 1) * (q ^ 3 + 1) * z := by rw [hrg]
      rw [h2, show s ^ 6 - 1 + 2 = s ^ 6 + 1 by omega]
      exact ⟨(q ^ 2 - 1) * z, by ring⟩
    have hodd6 : Odd (s ^ 6 - 1) := by rw [← e6]; exact odd_two_pow_sub_one (by omega)
    have hc : Nat.Coprime (s ^ 6 - 1 + 2) ((s ^ 6 - 1) * (s ^ 2 - 1)) :=
      Nat.Coprime.mul_right (coprime_add_two hodd6 dvd_rfl)
        (coprime_add_two hodd6 sq_sub_one_dvd.2)
    have := le_three_of_dvd hc hg3 hdvd
    omega
  ·
    have h1 : Nat.card X ≤ 12096 := by
      rw [Nat.card_congr e.toEquiv, ← U3.card_quasithinG2_two hK]
      exact Subgroup.card_le_card_group N
    omega
  ·
    have h1 : Nat.card X ≤ 2520 := by
      rw [Nat.card_congr e.toEquiv]
      rcases hm with rfl | rfl | rfl <;>
        rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide
    omega
  ·
    have h1 : Nat.card (X ⧸ Subgroup.center X) = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hcard] at h1
    omega
  ·
    have hK2 : Nat.card K = 2 := hK
    rcases hm with rfl | rfl
    · have h1 : Nat.card X = 20160 := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv,
          Vol2.Ch10.SecA.card_SL_four_of_two hK2]
      omega
    · have h1 : Nat.card X = 2 ^ 10 * 9765 := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 5 K).toEquiv,
          Vol2.Ch10.SecA.card_SL_five_of_two hK2]
        norm_num
      have := (two_pow_mul_odd_inj (by decide) hrz (h1.symm.trans hX2)).1
      omega

end CFSG.Quasithin.H13.A6.A6S20

module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3

variable {G : Type*} [Group G]

theorem isMulCommutative_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) :
    IsMulCommutative P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP]; norm_num)

theorem mul_comm_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) : a * b = b * a := by
  exact congrArg Subtype.val
    ((isMulCommutative_of_card_nine hP).is_comm.comm (⟨a, ha⟩ : P) ⟨b, hb⟩)

theorem commutator_eq_bot_of_card_nine {P : Subgroup G} (hP : Nat.card P = 9) : ⁅P, P⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact mul_comm_of_card_nine hP hb ha

theorem card_eq_three_of_lt {P U : Subgroup G} (hP : Nat.card P = 9) (hUP : U ≤ P)
    (hU1 : U ≠ ⊥) (hUP' : U ≠ P) : Nat.card U = 3 := by
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hdvd : Nat.card U ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hP]
    exact Subgroup.card_dvd_of_le hUP
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk')) hU1
  · simpa using hk'
  · exact absurd (Subgroup.eq_of_le_of_card_ge hUP (by rw [hP, hk']; norm_num)) hUP'

section Rank

variable [Finite G]

theorem false_of_commute (hrank : Open.pRank 3 (⊤ : Subgroup G) ≤ 2) {P : Subgroup G}
    (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1) {z : G} (hz : z ∉ P) (hz3 : z ^ 3 = 1)
    (hzP : ∀ a ∈ P, a * z = z * a) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k : Set G := (P : Set G) ∪ {z} with hk
  have hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x := by
    rintro x (hx | hx) y (hy | hy)
    · exact mul_comm_of_card_nine hP hx hy
    · rw [Set.mem_singleton_iff.mp hy]
      exact hzP x hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact (hzP y hy).symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  set E := Subgroup.closure k with hE
  have hEcomm : IsMulCommutative E :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm x hx y hy
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hexp x hx
      · rw [Set.mem_singleton_iff.mp hx]
        exact hz3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      rw [(Commute.mul_pow (hEc x hx y hy) 3), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE3 g g.2)⟩
  have hPE : P ≤ E := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hzE : z ∈ E := Subgroup.subset_closure (Or.inr rfl)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hEp
  have h9 : 9 ∣ 3 ^ n := by
    rw [← hP, ← hn]
    exact Subgroup.card_dvd_of_le hPE
  have hlt : 9 < 3 ^ n := by
    rcases Nat.lt_or_ge 9 (3 ^ n) with h | h
    · exact h
    · exfalso
      have hle : Nat.card E ≤ Nat.card P := by rw [hn, hP]; exact h
      exact hz ((Subgroup.eq_of_le_of_card_ge hPE hle) ▸ hzE)
  have hn3 : 3 ≤ n := by
    by_contra hlt3
    push Not at hlt3
    interval_cases n <;> norm_num at hlt
  have hEel : IsElemAbelian 3 E := ⟨hEcomm, hE3⟩
  have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : E ≤ ⊤) hEel hn
  omega

theorem false_of_normalizes (hrank : Open.pRank 3 (⊤ : Subgroup G) ≤ 2) {P M : Subgroup G}
    (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hinf : P ⊓ M = ⊥) (h3 : 3 ∣ Nat.card M) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer P M hPM
  have hP3 : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hmod := hP3.card_modEq_card_fixedPoints M
  have hF : 3 ∣ Nat.card (FixedPoints.subgroup P M) :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 h3))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 hF
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw
    omega
  set z : G := ((w : M) : G) with hz
  have hz3 : z ^ 3 = 1 := by
    have := congrArg (fun u : FixedPoints.subgroup P M => ((u : M) : G)) hw3
    simpa [hz] using this
  have hz1 : z ≠ 1 := by
    intro h
    apply hw1
    exact Subtype.ext (Subtype.ext h)
  have hzP : z ∉ P := by
    intro h
    have hzM : z ∈ P ⊓ M := ⟨h, (w : M).2⟩
    rw [hinf, Subgroup.mem_bot] at hzM
    exact hz1 hzM
  have hcomm : ∀ a ∈ P, a * z = z * a := by
    intro a ha
    have hfix : (⟨a, ha⟩ : P) • (w : M) = (w : M) := w.2 ⟨a, ha⟩
    have h1 : a * z * a⁻¹ = z := congrArg Subtype.val hfix
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h1]
  exact false_of_commute hrank hP hexp hzP hz3 hcomm

end Rank

theorem exists_invariant_of_index_two {P N N₀ : Subgroup G} (hP : Nat.card P = 9)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hNP : N ≤ Subgroup.normalizer (P : Set G))
    (hN₀ : ∀ n ∈ N, n ∈ N₀ → ∀ a ∈ P, n * a * n⁻¹ = a)
    (hidx : ∀ x ∈ N, ∀ y ∈ N, x ∉ N₀ → y ∉ N₀ → x⁻¹ * y ∈ N₀) :
    ∃ U : Subgroup G, U ≤ P ∧ U ≠ ⊥ ∧ U ≠ P ∧ N ≤ Subgroup.normalizer (U : Set G) := by
  have hconj : ∀ n ∈ N, ∀ a ∈ P, n * a * n⁻¹ ∈ P := fun n hn a ha =>
    (Subgroup.mem_normalizer_iff.mp (hNP hn) a).mp ha
  have hkey : ∃ c ∈ P, c ≠ 1 ∧ ∀ n ∈ N, n * c * n⁻¹ ∈ Subgroup.zpowers c := by
    have hP1 : (⊥ : Subgroup G) ≠ P := by
      intro h
      rw [← h, Subgroup.card_bot] at hP
      omega
    obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
      by_contra hne
      push Not at hne
      exact hP1 (le_antisymm bot_le fun x hx => Subgroup.mem_bot.mpr (hne x hx))
    by_cases hall : ∀ n ∈ N, n ∈ N₀
    · refine ⟨a, haP, ha1, fun n hn => ?_⟩
      rw [hN₀ n hn (hall n hn) a haP]
      exact Subgroup.mem_zpowers a
    push Not at hall
    obtain ⟨x, hxN, hxN₀⟩ := hall
    have hact : ∀ n ∈ N, ∀ b ∈ P, n * b * n⁻¹ = b ∨ n * b * n⁻¹ = x * b * x⁻¹ := by
      intro n hn b hb
      by_cases hn₀ : n ∈ N₀
      · exact Or.inl (hN₀ n hn hn₀ b hb)
      · right
        have hm := hidx x hxN n hn hxN₀ hn₀
        have hmN : x⁻¹ * n ∈ N := N.mul_mem (N.inv_mem hxN) hn
        have h1 := hN₀ _ hmN hm b hb
        calc n * b * n⁻¹ = x * ((x⁻¹ * n) * b * (x⁻¹ * n)⁻¹) * x⁻¹ := by group
          _ = x * b * x⁻¹ := by rw [h1]
    have hx2 : ∀ b ∈ P, x * (x * b * x⁻¹) * x⁻¹ = b := by
      intro b hb
      have hxi : x⁻¹ ∉ N₀ := fun h => hxN₀ (by simpa using N₀.inv_mem h)
      have hm := hidx x hxN x⁻¹ (N.inv_mem hxN) hxN₀ hxi
      have hmN : x⁻¹ * x⁻¹ ∈ N := N.mul_mem (N.inv_mem hxN) (N.inv_mem hxN)
      have h1 := hN₀ _ hmN hm b hb
      calc x * (x * b * x⁻¹) * x⁻¹ =
          x * (x * ((x⁻¹ * x⁻¹) * b * (x⁻¹ * x⁻¹)⁻¹) * x⁻¹) * x⁻¹ := by rw [h1]
        _ = b := by group
    set σa := x * a * x⁻¹ with hσa
    have hσaP : σa ∈ P := hconj x hxN a haP
    by_cases hin : σa ∈ Subgroup.zpowers a
    · refine ⟨a, haP, ha1, fun n hn => ?_⟩
      rcases hact n hn a haP with h | h
      · rw [h]
        exact Subgroup.mem_zpowers a
      · rw [h]
        exact hin
    · set c := a * σa with hc
      have hcP : c ∈ P := P.mul_mem haP hσaP
      have hc1 : c ≠ 1 := by
        intro h
        apply hin
        have : σa = a⁻¹ := by
          calc σa = a⁻¹ * (a * σa) := by group
            _ = a⁻¹ := by rw [← hc, h, mul_one]
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
      refine ⟨c, hcP, hc1, fun n hn => ?_⟩
      rcases hact n hn c hcP with h | h
      · rw [h]
        exact Subgroup.mem_zpowers c
      · rw [h]
        have h2 : x * c * x⁻¹ = c := by
          have e : x * c * x⁻¹ = (x * a * x⁻¹) * (x * σa * x⁻¹) := by rw [hc]; group
          rw [e, hσa, hx2 a haP]
          exact mul_comm_of_card_nine hP hσaP haP
        rw [h2]
        exact Subgroup.mem_zpowers c
  obtain ⟨c, hcP, hc1, hcN⟩ := hkey
  have hc3 : c ^ 3 = 1 := hexp c hcP
  have hcard : Nat.card (Subgroup.zpowers c) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hc3
  refine ⟨Subgroup.zpowers c, Subgroup.zpowers_le.mpr hcP, ?_, ?_, ?_⟩
  · intro h
    apply hc1
    have : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at this
    exact this
  · intro h
    rw [h, hP] at hcard
    omega
  · have hmap : ∀ n ∈ N, (Subgroup.zpowers c).map (MulAut.conj n).toMonoidHom ≤
        Subgroup.zpowers c := by
      intro n hn
      rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le]
      exact hcN n hn
    intro n hn
    exact mem_normalizer_of_map_conj_le (hmap n hn) (hmap n⁻¹ (N.inv_mem hn))

theorem centralizer_le_normalizer_self (L : Subgroup G) :
    Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff] at hc
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    have e : c * l * c⁻¹ = l := by rw [← hc l hl, mul_inv_cancel_right]
    rw [e]
    exact hl
  · intro hl
    have h1 := hc _ hl
    have h2 : c * l = c * (c * l * c⁻¹) := by
      calc c * l = c * l * c⁻¹ * c := by group
        _ = c * (c * l * c⁻¹) := h1
    have e : l = c * l * c⁻¹ := mul_left_cancel h2
    rw [e]
    exact hl

theorem mem_centralizer_of_pow_three_eq_one [Finite G] {L : Subgroup G}
    (hZ : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) (h3 : ¬ 3 ∣ Nat.card L) {x : G}
    (hx : x ∈ L ⊔ Subgroup.centralizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.centralizer (L : Set G) := by
  have hCN : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_self L
  obtain ⟨l, hl, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hCN).1 hx
  have hlc : l * c = c * l := (Subgroup.mem_centralizer_iff.mp hc) l hl
  have hl3 : l ^ 3 = 1 := by
    have h1 : l ^ 3 * c ^ 3 = 1 := by rw [← Commute.mul_pow hlc, hx3]
    have h2 : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmem : l ^ 3 ∈ L ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨L.pow_mem hl 3, h2 ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hc 3)⟩
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hl1 : l = 1 := by
    have hord : orderOf (⟨l, hl⟩ : L) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hl3))
    have hord2 : orderOf (⟨l, hl⟩ : L) ∣ Nat.card L := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
    · have := orderOf_eq_one_iff.mp h
      exact congrArg Subtype.val this
    · exact absurd (h ▸ hord2) h3
  rw [hl1, one_mul]
  exact hc

theorem mem_of_mem_sup_of_pow_three_eq_one [Finite G] {L O : Subgroup G} (hO : IsPGroup 2 O)
    (hOL : O ≤ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L ⊔ O) (hx3 : x ^ 3 = 1) :
    x ∈ L := by
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
  have hmod : ∀ n : ℕ, (l * o) ^ n = (l * o) ^ (n % 3) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx3, one_pow, mul_one]
  have h2 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have : 2 ^ k % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    omega
  rcases h2 with h | h
  · rw [hmod, h, pow_one] at he
    rw [he]
    exact hl'
  · rw [hmod, h] at he
    have e : l * o = ((l * o) ^ 2)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ', hx3]
    rw [e, he]
    exact L.inv_mem hl'

theorem exists_mul_of_mem_sup {P T : Subgroup G}
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s) {g : G} (hg : g ∈ P ⊔ T) :
    ∃ y ∈ P, ∃ s ∈ T, g = y * s := by
  let M : Subgroup G :=
    { carrier := {g | ∃ y ∈ P, ∃ s ∈ T, g = y * s}
      one_mem' := ⟨1, P.one_mem, 1, T.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, s₁, hs₁, rfl⟩ ⟨y₂, hy₂, s₂, hs₂, rfl⟩
        obtain ⟨y₃, hy₃, s₃, hs₃, he⟩ := hmul s₁ hs₁ y₂ hy₂
        refine ⟨y₁ * y₃, P.mul_mem hy₁ hy₃, s₃ * s₂, T.mul_mem hs₃ hs₂, ?_⟩
        calc y₁ * s₁ * (y₂ * s₂) = y₁ * (s₁ * y₂) * s₂ := by group
          _ = y₁ * y₃ * (s₃ * s₂) := by rw [he]; group
      inv_mem' := by
        rintro _ ⟨y, hy, s, hs, rfl⟩
        obtain ⟨y', hy', s', hs', he⟩ := hmul s⁻¹ (T.inv_mem hs) y⁻¹ (P.inv_mem hy)
        exact ⟨y', hy', s', hs', by rw [mul_inv_rev, he]⟩ }
  have hle : P ⊔ T ≤ M := sup_le (fun y hy => ⟨y, hy, 1, T.one_mem, by simp⟩)
    (fun s hs => ⟨1, P.one_mem, s, hs, by simp⟩)
  exact hle hg

theorem card_sup_eq_of_mul [Finite G] {P T : Subgroup G} (hP : Nat.card P = 9)
    (hT : IsPGroup 2 T) (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s) :
    Nat.card (P ⊔ T : Subgroup G) = 9 * Nat.card T := by
  apply le_antisymm
  ·
    let f : P × T → (P ⊔ T : Subgroup G) := fun ys =>
      ⟨(ys.1 : G) * ys.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left ys.1.2)
        (Subgroup.mem_sup_right ys.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨y, hy, s, hs, rfl⟩ := exists_mul_of_mem_sup hmul hg
      exact ⟨(⟨y, hy⟩, ⟨s, hs⟩), rfl⟩
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod, hP] at this
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
    have h1 : 9 ∣ Nat.card (P ⊔ T : Subgroup G) := hP ▸ Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card T ∣ Nat.card (P ⊔ T : Subgroup G) := Subgroup.card_dvd_of_le le_sup_right
    have hcop : Nat.Coprime 9 (Nat.card T) := by
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd h1 h2)

theorem prime_dvd_of_le_sup [Finite G] {P T B : Subgroup G} (hP : Nat.card P = 9)
    (hT : IsPGroup 2 T) (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hB : B ≤ P ⊔ T) : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3 := by
  intro q hq hqB
  have h1 : q ∣ 9 * Nat.card T :=
    (card_sup_eq_of_mul hP hT hmul) ▸ hqB.trans (Subgroup.card_dvd_of_le hB)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
  rw [hk] at h1
  rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
  · right
    have : q ∣ 3 ^ 2 := by norm_num; exact h
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow this)
  · left
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)

end CFSG.Quasithin.P134

module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

namespace Lem22

variable {G : Type} [Group G]

theorem eq_one_of_conj_eq_inv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y f : G} {k j : ℕ}
    (hy : y ^ p ^ k = 1) (hf : f ^ p ^ j = 1) (hyf : y * f * y⁻¹ = f⁻¹) : f = 1 := by
  have h2 : y ^ 2 * f * (y ^ 2)⁻¹ = f := by
    calc y ^ 2 * f * (y ^ 2)⁻¹ = y * (y * f * y⁻¹) * y⁻¹ := by rw [pow_two]; group
      _ = y * f⁻¹ * y⁻¹ := by rw [hyf]
      _ = (y * f * y⁻¹)⁻¹ := by group
      _ = f := by rw [hyf, inv_inv]
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have hy' : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc y = y ^ (p ^ k + 1) := by rw [pow_succ, hy, one_mul]
      _ = y ^ (2 * (m + 1)) := by rw [hm]; ring_nf
  have hcomm : ∀ r : ℕ, (y ^ 2) ^ r * f * ((y ^ 2) ^ r)⁻¹ = f := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      calc (y ^ 2) ^ (r + 1) * f * ((y ^ 2) ^ (r + 1))⁻¹
          = (y ^ 2) ^ r * (y ^ 2 * f * (y ^ 2)⁻¹) * ((y ^ 2) ^ r)⁻¹ := by group
        _ = f := by rw [h2, ih]
  have h3 : y * f * y⁻¹ = f := by
    rw [hy']
    exact hcomm (m + 1)
  have h4 : f ^ 2 = 1 := by
    rw [pow_two]
    calc f * f = f * (y * f * y⁻¹)⁻¹ := by rw [hyf, inv_inv]
      _ = f * f⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel f
  have hodd' : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m', hm'⟩ := hodd'
  calc f = f ^ (p ^ j + 1) := by rw [pow_succ, hf, one_mul]
    _ = (f ^ 2) ^ (m' + 1) := by rw [← pow_mul, hm']; ring_nf
    _ = 1 := by rw [h4, one_pow]

theorem pow_mul_eq_of_comm {x y d : G} (hd : y * x = x * y * d) (hdy : Commute d y) (k : ℕ) :
    y ^ k * x = x * y ^ k * d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : Commute d (y ^ k) := hdy.pow_right k
    calc y ^ (k + 1) * x = y * (y ^ k * x) := by rw [pow_succ', mul_assoc]
      _ = y * (x * y ^ k * d ^ k) := by rw [ih]
      _ = y * x * y ^ k * d ^ k := by simp only [mul_assoc]
      _ = x * y * d * y ^ k * d ^ k := by rw [hd]
      _ = x * y * (d * y ^ k) * d ^ k := by simp only [mul_assoc]
      _ = x * y * (y ^ k * d) * d ^ k := by rw [h1.eq]
      _ = x * (y * y ^ k) * (d * d ^ k) := by simp only [mul_assoc]
      _ = x * y ^ (k + 1) * d ^ (k + 1) := by rw [← pow_succ', ← pow_succ']

theorem mul_pow_eq_of_comm {x y d : G} (hd : y * x = x * y * d) (hdx : Commute d x)
    (hdy : Commute d y) (k : ℕ) : (x * y) ^ k = x ^ k * y ^ k * d ^ (k.choose 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : (k + 1).choose 2 = k + k.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]
    have h1 : Commute (d ^ k.choose 2) x := hdx.pow_left _
    have h2 : Commute (d ^ k * d ^ k.choose 2) y := (hdy.pow_left _).mul_left (hdy.pow_left _)
    have h3 := pow_mul_eq_of_comm hd hdy k
    calc (x * y) ^ (k + 1) = x ^ k * y ^ k * d ^ k.choose 2 * (x * y) := by rw [pow_succ, ih]
      _ = x ^ k * y ^ k * (d ^ k.choose 2 * x) * y := by simp only [mul_assoc]
      _ = x ^ k * y ^ k * (x * d ^ k.choose 2) * y := by rw [h1.eq]
      _ = x ^ k * (y ^ k * x) * d ^ k.choose 2 * y := by simp only [mul_assoc]
      _ = x ^ k * (x * y ^ k * d ^ k) * d ^ k.choose 2 * y := by rw [h3]
      _ = x ^ k * x * y ^ k * ((d ^ k * d ^ k.choose 2) * y) := by simp only [mul_assoc]
      _ = x ^ k * x * y ^ k * (y * (d ^ k * d ^ k.choose 2)) := by rw [h2.eq]
      _ = x ^ k * x * (y ^ k * y) * (d ^ k * d ^ k.choose 2) := by simp only [mul_assoc]
      _ = x ^ (k + 1) * y ^ (k + 1) * d ^ ((k + 1).choose 2) := by
        rw [← pow_succ, ← pow_succ, ← pow_add, hc]

variable {P : Subgroup G} {n : G} {p : ℕ}

theorem conj_eq_inv_of_mem (hn2 : ∀ x ∈ P, (n * n) * x * (n * n)⁻¹ = x) {y : G} (hy : y ∈ P) :
    n * (y * (n * y * n⁻¹)⁻¹) * n⁻¹ = (y * (n * y * n⁻¹)⁻¹)⁻¹ := by
  have h1 := hn2 y hy
  calc n * (y * (n * y * n⁻¹)⁻¹) * n⁻¹ = (n * y * n⁻¹) * ((n * n) * y * (n * n)⁻¹)⁻¹ := by group
    _ = (n * y * n⁻¹) * y⁻¹ := by rw [h1]
    _ = (y * (n * y * n⁻¹)⁻¹)⁻¹ := by group

theorem eq_of_inv_of_mem (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ f ∈ (frattini ↥P).map P.subtype, n * f = f * n) {y y' : G} (hy : y ∈ P)
    (hyinv : n * y * n⁻¹ = y⁻¹) (hy'inv : n * y' * n⁻¹ = y'⁻¹)
    (hyy' : y⁻¹ * y' ∈ (frattini ↥P).map P.subtype) : y = y' := by
  set f := y⁻¹ * y' with hfdef
  have hy'e : y' = y * f := by rw [hfdef]; group
  have hfP : f ∈ P := frattini_map_le P hyy'
  have hnf : n * f * n⁻¹ = f := by
    rw [hcomm f hyy', mul_inv_cancel_right]
  have hyf : y * f * y⁻¹ = f⁻¹ := by
    have h1 : n * y' * n⁻¹ = (n * y * n⁻¹) * (n * f * n⁻¹) := by rw [hy'e]; group
    rw [hy'inv, hyinv, hnf, hy'e] at h1
    calc y * f * y⁻¹ = (f⁻¹ * y⁻¹)⁻¹ * y⁻¹ := by group
      _ = (y⁻¹ * f)⁻¹ * y⁻¹ := by rw [show f⁻¹ * y⁻¹ = y⁻¹ * f from by rw [← h1]; group]
      _ = f⁻¹ := by group
  obtain ⟨k, hk⟩ := hPp ⟨y, hy⟩
  obtain ⟨j, hj⟩ := hPp ⟨f, hfP⟩
  have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hj' : f ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hf1 := eq_one_of_conj_eq_inv hp hp2 hk' hj' hyf
  rw [hy'e, hf1, mul_one]

variable [Finite G]

theorem pow_mem_frattini_map (hp : p.Prime) (hPp : IsPGroup p ↥P) {x : G} (hx : x ∈ P) :
    x ^ p ∈ (frattini ↥P).map P.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨⟨x, hx⟩ ^ p, CFSG.SectionRank.Ccomm.pow_mem_frattini hPp ⟨x, hx⟩, by simp⟩

theorem commutator_mem_frattini_map (hp : p.Prime) (hPp : IsPGroup p ↥P) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) : x * y * x⁻¹ * y⁻¹ ∈ (frattini ↥P).map P.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆,
    CFSG.SectionRank.Ccomm.commutator_mem_frattini hPp _ _, rfl⟩

theorem mem_closure_inv (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hninv : ∀ x ∈ P, n * x * n⁻¹ * x ∈ (frattini ↥P).map P.subtype) :
    ∀ x ∈ P, x ∈ Subgroup.closure {u | ∃ y ∈ P, u = y * (n * y * n⁻¹)⁻¹} := by
  have hnP' : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hnP x).mp hx
  have huP : ∀ x ∈ P, x * (n * x * n⁻¹)⁻¹ ∈ P := fun x hx =>
    P.mul_mem hx (P.inv_mem (hnP' x hx))
  set R := Subgroup.closure {u | ∃ y ∈ P, u = y * (n * y * n⁻¹)⁻¹} with hR
  have hRP : R ≤ P := (Subgroup.closure_le _).mpr fun u ⟨x, hx, hu'⟩ => hu' ▸ huP x hx
  have hRtop : R.subgroupOf P ⊔ frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨k, hk⟩ := hPp ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨m, hm⟩ := hodd
    set y := x ^ (m + 1) with hy
    have hyP : y ∈ P := P.pow_mem hx _
    have hy2 : y * y = x := by
      rw [hy, ← pow_add]
      calc x ^ (m + 1 + (m + 1)) = x ^ (p ^ k + 1) := by rw [hm]; ring_nf
        _ = x := by rw [pow_succ, hk', one_mul]
    have huR : y * (n * y * n⁻¹)⁻¹ ∈ R := Subgroup.subset_closure ⟨y, hyP, rfl⟩
    have hf : (n * y * n⁻¹) * y ∈ (frattini ↥P).map P.subtype := hninv y hyP
    have e : x = (y * (n * y * n⁻¹)⁻¹) * ((n * y * n⁻¹) * y) := by
      rw [← hy2]
      group
    have hfP : (n * y * n⁻¹) * y ∈ P := frattini_map_le P hf
    have h1 : (⟨x, hx⟩ : ↥P) = ⟨y * (n * y * n⁻¹)⁻¹, hRP huR⟩ * ⟨(n * y * n⁻¹) * y, hfP⟩ :=
      Subtype.ext e
    rw [h1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr huR))
      (Subgroup.mem_sup_right ?_)
    obtain ⟨f₀, hf₀, hf₀e⟩ := hf
    have : f₀ = ⟨(n * y * n⁻¹) * y, hfP⟩ := Subtype.ext hf₀e
    rw [← this]
    exact hf₀
  have hReq : R.subgroupOf P = ⊤ := frattini_nongenerating hRtop
  intro x hx
  have : (⟨x, hx⟩ : ↥P) ∈ R.subgroupOf P := by rw [hReq]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem comm_of_mem_frattini (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hcomm : ∀ f ∈ (frattini ↥P).map P.subtype, n * f = f * n)
    (hninv : ∀ x ∈ P, n * x * n⁻¹ * x ∈ (frattini ↥P).map P.subtype)
    (hn2 : ∀ x ∈ P, (n * n) * x * (n * n)⁻¹ = x) :
    ∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f := by
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hΦP : Φ ≤ P := frattini_map_le P
  have hnP' : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hnP x).mp hx
  have huP : ∀ x ∈ P, x * (n * x * n⁻¹)⁻¹ ∈ P := fun x hx =>
    P.mul_mem hx (P.inv_mem (hnP' x hx))
  have hcomm_inv : ∀ f ∈ Φ, ∀ y ∈ P, n * y * n⁻¹ = y⁻¹ → f * y = y * f := by
    intro f hf y hy hyinv
    have hinv' : n * (f * y * f⁻¹) * n⁻¹ = (f * y * f⁻¹)⁻¹ := by
      have hnf : n * f * n⁻¹ = f := by rw [hcomm f hf, mul_inv_cancel_right]
      have hnf' : n * f⁻¹ * n⁻¹ = f⁻¹ := by
        have := congrArg (·⁻¹) hnf
        simpa [mul_assoc] using this
      calc n * (f * y * f⁻¹) * n⁻¹ = (n * f * n⁻¹) * (n * y * n⁻¹) * (n * f⁻¹ * n⁻¹) := by
            group
        _ = f * y⁻¹ * f⁻¹ := by rw [hnf, hyinv, hnf']
        _ = (f * y * f⁻¹)⁻¹ := by group
    have hmem : y⁻¹ * (f * y * f⁻¹) ∈ Φ := by
      have h1 : y⁻¹ * f * y ∈ Φ := by
        have := conj_mem_frattini (Subgroup.le_normalizer (P.inv_mem hy)) hf
        rwa [inv_inv] at this
      have e : y⁻¹ * (f * y * f⁻¹) = (y⁻¹ * f * y) * f⁻¹ := by group
      rw [e]
      exact Φ.mul_mem h1 (Φ.inv_mem hf)
    have heq := eq_of_inv_of_mem hp hp2 hPp hcomm hy hyinv hinv' hmem
    calc f * y = (f * y * f⁻¹) * f := by group
      _ = y * f := by rw [← heq]
  intro f hf x hx
  have hxR := mem_closure_inv hp hp2 hPp hnP hninv x hx
  clear hx
  induction hxR using Subgroup.closure_induction with
  | mem u hu' =>
    obtain ⟨y, hy, rfl⟩ := hu'
    exact hcomm_inv f hf _ (huP y hy) (conj_eq_inv_of_mem hn2 hy)
  | one => simp
  | mul a b _ _ iha ihb =>
    calc f * (a * b) = (f * a) * b := by group
      _ = (a * f) * b := by rw [iha]
      _ = a * (f * b) := by group
      _ = a * (b * f) := by rw [ihb]
      _ = a * b * f := by group
  | inv a _ iha =>
    calc f * a⁻¹ = a⁻¹ * (a * f) * a⁻¹ := by group
      _ = a⁻¹ * (f * a) * a⁻¹ := by rw [iha]
      _ = a⁻¹ * f := by group

theorem pow_eq_one_of_inv (hp : p.Prime) (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P)
    (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hcomm : ∀ f ∈ (frattini ↥P).map P.subtype, n * f = f * n)
    (hninv : ∀ x ∈ P, n * x * n⁻¹ * x ∈ (frattini ↥P).map P.subtype)
    (hn2 : ∀ x ∈ P, (n * n) * x * (n * n)⁻¹ = x) : ∀ x ∈ P, x ^ p = 1 := by
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hZ := comm_of_mem_frattini hp hp2 hPp hnP hcomm hninv hn2
  have hnP' : ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun x hx => (Subgroup.mem_normalizer_iff.mp hnP x).mp hx
  have hmul : ∀ x ∈ P, ∀ y ∈ P, x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1 := by
    intro x hx y hy hxp hyp
    set d := y⁻¹ * x⁻¹ * y * x with hd
    have hdΦ : d ∈ Φ := by
      have := commutator_mem_frattini_map hp hPp (P.inv_mem hy) (P.inv_mem hx)
      simpa only [inv_inv] using this
    have hdx : Commute d x := hZ d hdΦ x hx
    have hdy : Commute d y := hZ d hdΦ y hy
    have hyx : y * x = x * y * d := by rw [hd]; group
    have hdp : d ^ p = 1 := by
      have h1 := pow_mul_eq_of_comm hyx hdy p
      have h2 : y ^ p * x = x * y ^ p := hZ _ (pow_mem_frattini_map hp hPp hy) x hx
      rw [h2] at h1
      have h3 : x * y ^ p * 1 = x * y ^ p * d ^ p := by rw [mul_one]; exact h1
      exact (mul_left_cancel h3).symm
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) hp3
    rw [mul_pow_eq_of_comm hyx hdx hdy p, hxp, hyp, one_mul, one_mul, hc, pow_mul, hdp, one_pow]
  have hinv : ∀ u ∈ P, n * u * n⁻¹ = u⁻¹ → u ^ p = 1 := by
    intro u hu hun
    have hup : u ^ p ∈ Φ := pow_mem_frattini_map hp hPp hu
    have h1 : n * u ^ p * n⁻¹ = (u ^ p)⁻¹ := by
      rw [← conj_pow, hun, inv_pow]
    have h2 : n * u ^ p * n⁻¹ = u ^ p := by rw [hcomm _ hup, mul_inv_cancel_right]
    have h3 : (u ^ p) ^ 2 = 1 := by
      rw [pow_two]
      calc u ^ p * u ^ p = (n * u ^ p * n⁻¹)⁻¹ * u ^ p := by rw [h1, inv_inv]
        _ = (u ^ p)⁻¹ * u ^ p := by rw [h2]
        _ = 1 := inv_mul_cancel _
    exact eq_one_of_sq_eq_one hp hp2 hPp (P.pow_mem hu p) h3
  have key : ∀ z ∈ Subgroup.closure {u | ∃ y ∈ P, u = y * (n * y * n⁻¹)⁻¹},
      z ∈ P ∧ z ^ p = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem u hu' =>
      obtain ⟨y, hy, rfl⟩ := hu'
      have huP : y * (n * y * n⁻¹)⁻¹ ∈ P := P.mul_mem hy (P.inv_mem (hnP' y hy))
      exact ⟨huP, hinv _ huP (conj_eq_inv_of_mem hn2 hy)⟩
    | one => exact ⟨P.one_mem, one_pow _⟩
    | mul a b _ _ iha ihb => exact ⟨P.mul_mem iha.1 ihb.1, hmul a iha.1 b ihb.1 iha.2 ihb.2⟩
    | inv a _ iha => exact ⟨P.inv_mem iha.1, by rw [inv_pow, iha.2, inv_one]⟩
  intro x hx
  exact (key x (mem_closure_inv hp hp2 hPp hnP hninv x hx)).2

theorem card_eq_of_rank (hp : p.Prime) (hPp : IsPGroup p ↥P) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hZ : ∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f) (hΦ1 : frattini ↥P ≠ ⊥)
    (hrank : ∀ E : Subgroup G, E ≤ P → IsMulCommutative ↥E → Nat.card E ≤ p ^ 2) :
    Nat.card P = p ^ 3 ∧ Nat.card ((frattini ↥P).map P.subtype) = p := by
  have : Fact p.Prime := ⟨hp⟩
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  have hΦP : Φ ≤ P := frattini_map_le P
  have hΦb : Φ ≠ ⊥ := fun h0 =>
    hΦ1 ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).mp h0)
  set Z := P ⊓ Subgroup.centralizer (P : Set G) with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp ha.2) b hb).symm
  have hΦZ : Φ ≤ Z := fun f hf =>
    ⟨hΦP hf, Subgroup.mem_centralizer_iff.mpr fun x hx => (hZ f hf x hx).symm⟩
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
    by_contra hno
    push Not at hno
    apply hΦ1
    exact (CFSG.SectionRank.Ccomm.frattini_eq_bot_iff hPp).mpr
      ⟨fun a b => Subtype.ext (hno a a.2 b b.2), fun a => Subtype.ext (by simpa using hexp a a.2)⟩
  have hxZ : x ∉ Z := fun h => hxy ((Subgroup.mem_centralizer_iff.mp h.2) y hy).symm
  have hab : ∀ S : Set G, S ⊆ P → S.Pairwise Commute → Nat.card (Subgroup.closure S) ≤ p ^ 2 :=
    fun S hS hc => hrank _ ((Subgroup.closure_le _).mpr hS) (Subgroup.isMulCommutative_closure hc)
  set E := Subgroup.closure (insert x (Z : Set G)) with hEdef
  have hsubE : insert x (Z : Set G) ⊆ P := Set.insert_subset hx fun a ha => hZP ha
  have hEP : E ≤ P := (Subgroup.closure_le _).mpr hsubE
  have hEc : (insert x (Z : Set G)).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Commute.refl _
    · exact (hZcomm b hb a hx).symm
    · exact hZcomm a ha b hx
    · exact hZcomm a ha b (hZP hb)
  have hEcard : Nat.card E ≤ p ^ 2 := hab _ hsubE hEc
  have hZE : Z ≤ E := fun z hz => Subgroup.subset_closure (Set.mem_insert_of_mem _ hz)
  have hxE : x ∈ E := Subgroup.subset_closure (Set.mem_insert _ _)
  have hZlt : Z < E := lt_of_le_of_ne hZE fun h => hxZ (h ▸ hxE)
  obtain ⟨a, ha⟩ := (hPp.to_le hZP).exists_card_eq
  obtain ⟨b, hb⟩ := (hPp.to_le hEP).exists_card_eq
  have hZ1 : 1 < Nat.card Z :=
    (Subgroup.one_lt_card_iff_ne_bot Z).mpr fun h => hΦb (le_bot_iff.mp (h ▸ hΦZ))
  have hab' : a < b := by
    have := Subgroup.card_lt_of_lt hZlt
    rw [ha, hb] at this
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp this
  have hb2 : b ≤ 2 := by
    rw [hb] at hEcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hEcard
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [ha, h, pow_zero] at hZ1
      exact absurd hZ1 (lt_irrefl 1)
    · exact h
  have hZp : Nat.card Z = p := by rw [ha, show a = 1 by omega, pow_one]
  have hEp : Nat.card E = p ^ 2 := by rw [hb, show b = 2 by omega]
  have hΦp : Nat.card Φ = p := by
    have h1 : Nat.card Φ ∣ Nat.card Z := Subgroup.card_dvd_of_le hΦZ
    rw [hZp] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hΦb
    · exact h
  have hCE : ∀ w ∈ P, x * w = w * x → w ∈ E := by
    intro w hw hxw
    have hE'c : (insert w (insert x (Z : Set G))).Pairwise Commute := by
      refine hEc.insert fun c hc _ => ?_
      rcases hc with rfl | hc
      · exact ⟨hxw.symm, hxw⟩
      · exact ⟨(hZcomm c hc w hw).symm, hZcomm c hc w hw⟩
    have hE'card := hab _ (Set.insert_subset hw hsubE) hE'c
    have hEE' : E ≤ Subgroup.closure (insert w (insert x (Z : Set G))) :=
      Subgroup.closure_mono (Set.subset_insert _ _)
    have heq := Subgroup.eq_of_le_of_card_ge hEE' (by rw [hEp]; exact hE'card)
    rw [heq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hcΦ : ∀ w ∈ P, x * w * x⁻¹ * w⁻¹ ∈ Φ := fun w hw =>
    commutator_mem_frattini_map hp hPp hx hw
  let φ : ↥P →* G :=
    { toFun := fun w => x * w * x⁻¹ * (w : G)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hcom : (x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
            (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) :=
          hZ _ (hcΦ b b.2) _ (P.inv_mem a.2)
        simp only [Subgroup.coe_mul]
        calc x * (a * b) * x⁻¹ * ((a : G) * b)⁻¹
            = x * a * x⁻¹ * ((x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = x * a * x⁻¹ * ((a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹)) := by rw [hcom]
          _ = x * a * x⁻¹ * (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) := by group }
  have hrange : φ.range ≤ Φ := by
    rintro _ ⟨w, rfl⟩
    exact hcΦ w w.2
  have hker : φ.ker.map P.subtype ≤ E := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 : x * w * x⁻¹ * (w : G)⁻¹ = 1 := hw
    refine hCE w w.2 ?_
    calc x * (w : G) = x * w * x⁻¹ * (w : G)⁻¹ * (w * x) := by group
      _ = w * x := by rw [h1, one_mul]
  have hcardP : Nat.card P = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hk : Nat.card φ.ker ≤ p ^ 2 := by
    have := Subgroup.card_le_of_le hker
    rwa [Subgroup.card_map_of_injective P.subtype_injective, hEp] at this
  have hr : Nat.card φ.range ≤ p := by
    have := Subgroup.card_le_of_le hrange
    rwa [hΦp] at this
  have hle : Nat.card P ≤ p ^ 3 := by
    rw [hcardP, pow_succ]
    exact Nat.mul_le_mul hk hr
  have hyE : y ∉ E := by
    intro hyE
    have hEcomm : IsMulCommutative ↥E := Subgroup.isMulCommutative_closure hEc
    apply hxy
    have := hEcomm.is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩
    exact congrArg Subtype.val this
  have hEltP : Nat.card E < Nat.card P :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hEP fun h => hyE (h ▸ hy))
  obtain ⟨c, hc⟩ := hPp.exists_card_eq
  rw [hEp, hc] at hEltP
  rw [hc] at hle
  have hc3 : 2 < c := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hEltP
  have hc3' : c ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  exact ⟨by rw [hc, show c = 3 by omega], hΦp⟩

end Lem22

end CFSG.Quasithin.H13

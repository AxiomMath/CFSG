module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.C48Cover

variable {X : Type*} [Group X]

theorem conj_eq_of_pow {y t : X} (hy : y ^ 7 = 1) {d : ℕ} (hd0 : 0 < d) (hd7 : d < 7)
    (h : y ^ d * t * (y ^ d)⁻¹ = t) : y * t * y⁻¹ = t := by
  have hfix : ∀ m : ℕ, (y ^ d) ^ m * t * ((y ^ d) ^ m)⁻¹ = t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc (y ^ d) ^ (m + 1) * t * ((y ^ d) ^ (m + 1))⁻¹
          = (y ^ d) ^ m * (y ^ d * t * (y ^ d)⁻¹) * ((y ^ d) ^ m)⁻¹ := by group
        _ = t := by rw [h, ih]
  have key : ∀ m q : ℕ, d * m = 7 * q + 1 → y * t * y⁻¹ = t := by
    intro m q hm
    have : y = (y ^ d) ^ m := by
      rw [← pow_mul, hm, pow_succ, pow_mul, hy, one_pow, one_mul]
    rw [this]
    exact hfix m
  interval_cases d
  · simpa using h
  · exact key 4 1 rfl
  · exact key 5 2 rfl
  · exact key 2 1 rfl
  · exact key 3 2 rfl
  · exact key 6 5 rfl

theorem conj_pow_injective {y t : X} (hy : y ^ 7 = 1) (hyt : y * t * y⁻¹ ≠ t) {i j : ℕ}
    (hi : i < 7) (hj : j < 7) (hij : y ^ i * t * (y ^ i)⁻¹ = y ^ j * t * (y ^ j)⁻¹) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · apply hyt
    refine conj_eq_of_pow hy (d := j - i) (by omega) (by omega) ?_
    have hj' : y ^ j = y ^ i * y ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    calc y ^ (j - i) * t * (y ^ (j - i))⁻¹
        = (y ^ i)⁻¹ * ((y ^ i * y ^ (j - i)) * t * (y ^ i * y ^ (j - i))⁻¹) * y ^ i := by group
      _ = t := by rw [← hj', ← hij]; group
  · apply hyt
    refine conj_eq_of_pow hy (d := i - j) (by omega) (by omega) ?_
    have hi' : y ^ i = y ^ j * y ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    calc y ^ (i - j) * t * (y ^ (i - j))⁻¹
        = (y ^ j)⁻¹ * ((y ^ j * y ^ (i - j)) * t * (y ^ j * y ^ (i - j))⁻¹) * y ^ j := by group
      _ = t := by rw [← hi', hij]; group

theorem conj_pow_mem {N : Subgroup X} {y t : X} (hyN : y ∈ Subgroup.normalizer (N : Set X))
    (htN : t ∈ N) (j : ℕ) : y ^ j * t * (y ^ j)⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyN j) t).mp htN

theorem exists_conj_pow_eq {N : Subgroup X} (hN8 : Nat.card N = 8) {y t : X} (hy : y ^ 7 = 1)
    (hyN : y ∈ Subgroup.normalizer (N : Set X)) (htN : t ∈ N) (hyt : y * t * y⁻¹ ≠ t) {n : X}
    (hn : n ∈ N) (hn1 : n ≠ 1) : ∃ j : ℕ, j < 7 ∧ y ^ j * t * (y ^ j)⁻¹ = n := by
  by_contra hcon
  push Not at hcon
  have : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hN8]; norm_num)
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hyt
    group
  let f : Option (Option (Fin 7)) → ↥N := fun o =>
    o.elim 1 fun o' => o'.elim ⟨n, hn⟩ fun j => ⟨_, conj_pow_mem hyN htN j⟩
  have hf : Function.Injective f := by
    have hne1 : ∀ j : ℕ, y ^ j * t * (y ^ j)⁻¹ ≠ 1 := fun j h => ht1 (by
      have := congrArg (fun z => (y ^ j)⁻¹ * z * y ^ j) h
      simpa [mul_assoc] using this)
    rintro (_ | _ | i) (_ | _ | j) h <;>
      simp only [f, Option.elim, Subtype.ext_iff, Subgroup.coe_one] at h
    · rfl
    · exact (hn1 h.symm).elim
    · exact (hne1 j h.symm).elim
    · exact (hn1 h).elim
    · rfl
    · exact (hcon j j.2 h.symm).elim
    · exact (hne1 i h).elim
    · exact (hcon i i.2 h).elim
    · exact congrArg some (congrArg some (Fin.ext (conj_pow_injective hy hyt i.2 j.2 h)))
  have := Nat.card_le_card_of_injective f hf
  rw [hN8, Nat.card_eq_fintype_card] at this
  simp at this

theorem eq_one_of_conj_eq {N : Subgroup X} (hN8 : Nat.card N = 8) {y t : X} (hy : y ^ 7 = 1)
    (hyN : y ∈ Subgroup.normalizer (N : Set X)) (htN : t ∈ N) (hyt : y * t * y⁻¹ ≠ t) {n : X}
    (hn : n ∈ N) (hny : y * n * y⁻¹ = n) : n = 1 := by
  by_contra hn1
  obtain ⟨j, -, rfl⟩ := exists_conj_pow_eq hN8 hy hyN htN hyt hn hn1
  apply hyt
  have h1 : y ^ j * (y * t * y⁻¹) * (y ^ j)⁻¹ = y ^ j * t * (y ^ j)⁻¹ := by
    calc y ^ j * (y * t * y⁻¹) * (y ^ j)⁻¹ = y * (y ^ j * t * (y ^ j)⁻¹) * y⁻¹ := by group
      _ = y ^ j * t * (y ^ j)⁻¹ := hny
  exact mul_left_cancel (mul_right_cancel h1)

theorem mem_of_commute_of_simple {B : Type*} [Group B] {N : Subgroup B} [N.Normal]
    (hs : IsSimpleGroup (B ⧸ N)) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {y t : B}
    (htN : t ∈ N) (hyt : y * t * y⁻¹ ≠ t) {c : B} (hc : ∀ n ∈ N, c * n = n * c) : c ∈ N := by
  set C := Subgroup.centralizer (N : Set B) with hC
  have hcC : c ∈ C := Subgroup.mem_centralizer_iff.mpr fun n hn => (hc n hn).symm
  have : (C.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' N)) with hb | ht
  · have h1 : QuotientGroup.mk' N c = 1 := by
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hcC
      rwa [hb, Subgroup.mem_bot] at this
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  · exfalso
    obtain ⟨d, hd, hdy⟩ : QuotientGroup.mk' N y ∈ C.map (QuotientGroup.mk' N) := by
      rw [ht]
      trivial
    have hk : d⁻¹ * y ∈ N := QuotientGroup.eq.mp hdy
    apply hyt
    set n' := d⁻¹ * y with hn'
    have hy : y = d * n' := by rw [hn']; group
    have h1 : n' * t = t * n' := hNc _ hk t htN
    have h2 : t * d = d * t := Subgroup.mem_centralizer_iff.mp hd t htN
    calc y * t * y⁻¹ = d * (n' * t) * n'⁻¹ * d⁻¹ := by rw [hy]; group
      _ = d * t * d⁻¹ := by rw [h1]; group
      _ = t := by rw [← h2]; group

theorem mem_of_central_of_simple {B : Type*} [Group B] {N : Subgroup B} [N.Normal]
    (hZ : Subgroup.center (B ⧸ N) = ⊥) {u : B} (hu : ∀ b : B, (u * b)⁻¹ * (b * u) ∈ N) :
    u ∈ N := by
  have h1 : (u : B ⧸ N) ∈ Subgroup.center (B ⧸ N) := Subgroup.mem_center_iff.mpr fun q => by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq]
    exact hu b
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem center_eq_bot_of_not_prime {Q : Type*} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    (h : ¬ (Nat.card Q).Prime) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a
    let _ : CommGroup Q := { ‹Group Q› with mul_comm := hcomm }
    exact h (IsSimpleGroup.prime_card (α := Q))

theorem sq_eq_of_section {B N : Subgroup X} (hBN : B ≤ Subgroup.normalizer (N : Set X))
    (hNB : N ≤ B) (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1)
    (hN8 : Nat.card N = 8) (hCN : ∀ c ∈ B, (∀ n ∈ N, c * n = n * c) → c ∈ N)
    (hZN : ∀ u ∈ B, (∀ b ∈ B, (u * b)⁻¹ * (b * u) ∈ N) → u ∈ N) {y t : X} (hyB : y ∈ B)
    (hy : y ^ 7 = 1) (htN : t ∈ N) (hyt : y * t * y⁻¹ ≠ t) (σ : X ≃* X)
    (hσ : ∀ b ∈ B, σ b * b⁻¹ ∈ N) : ∀ b ∈ B, σ (σ b) = b := by
  have hyN : y ∈ Subgroup.normalizer (N : Set X) := hBN hyB
  have hσN : ∀ n ∈ N, σ n ∈ N := fun n hn => by
    have := N.mul_mem (hσ n (hNB hn)) hn
    rwa [inv_mul_cancel_right] at this
  have hσconj : ∀ b ∈ B, ∀ n ∈ N, σ (b * n * b⁻¹) = b * σ n * b⁻¹ := by
    intro b hb n hn
    have hd := hσ b hb
    have hbn : b * σ n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hBN hb) _).mp (hσN n hn)
    have hσb : σ b = (σ b * b⁻¹) * b := by group
    rw [map_mul, map_mul, map_inv, hσb]
    calc σ b * b⁻¹ * b * σ n * (σ b * b⁻¹ * b)⁻¹
        = (σ b * b⁻¹) * (b * σ n * b⁻¹) * (σ b * b⁻¹)⁻¹ := by group
      _ = b * σ n * b⁻¹ := by rw [hNc _ hd _ hbn, mul_inv_cancel_right]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hyt
    group
  obtain ⟨k, -, hk⟩ := exists_conj_pow_eq hN8 hy hyN htN hyt (hσN t htN)
    (fun h => ht1 (σ.injective (h.trans (map_one σ).symm)))
  have hσk : ∀ n ∈ N, σ n = y ^ k * n * (y ^ k)⁻¹ := by
    intro n hn
    by_cases hn1 : n = 1
    · rw [hn1, map_one]
      group
    obtain ⟨j, -, rfl⟩ := exists_conj_pow_eq hN8 hy hyN htN hyt hn hn1
    rw [hσconj _ (Subgroup.pow_mem _ hyB j) t htN, ← hk]
    group
  have hykB : y ^ k ∈ B := Subgroup.pow_mem _ hyB k
  have hykN : y ^ k ∈ N := by
    refine hZN _ hykB fun b hb => ?_
    set c := (b * y ^ k)⁻¹ * (y ^ k * b) with hc
    have hcB : c ∈ B := B.mul_mem (B.inv_mem (B.mul_mem hb hykB)) (B.mul_mem hykB hb)
    have hcN : c ∈ N := by
      refine hCN c hcB fun n hn => ?_
      have hbn : b * n * b⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hBN hb) n).mp hn
      have h1 : y ^ k * (b * n * b⁻¹) * (y ^ k)⁻¹ = b * (y ^ k * n * (y ^ k)⁻¹) * b⁻¹ := by
        rw [← hσk _ hbn, ← hσk n hn, hσconj b hb n hn]
      calc c * n = (b * y ^ k)⁻¹ * (y ^ k * (b * n * b⁻¹) * (y ^ k)⁻¹) * (y ^ k * b) := by
            rw [hc]; group
        _ = (b * y ^ k)⁻¹ * (b * (y ^ k * n * (y ^ k)⁻¹) * b⁻¹) * (y ^ k * b) := by rw [h1]
        _ = n * c := by rw [hc]; group
    have : (y ^ k * b)⁻¹ * (b * y ^ k) = c⁻¹ := by rw [hc]; group
    rw [this]
    exact N.inv_mem hcN
  have hyk1 : y ^ k = 1 := by
    have h2 := hN2 _ hykN
    have h7 : (y ^ k) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
    calc y ^ k = ((y ^ k) * (y ^ k)) ^ 3 * y ^ k := by rw [h2, one_pow, one_mul]
      _ = (y ^ k) ^ 7 := by group
      _ = 1 := h7
  have hσN1 : ∀ n ∈ N, σ n = n := fun n hn => by rw [hσk n hn, hyk1]; group
  intro b hb
  have hd := hσ b hb
  set d := σ b * b⁻¹ with hd'
  have hσb : σ b = d * b := by rw [hd']; group
  rw [hσb, map_mul, hσN1 _ hd, hσb, ← mul_assoc, hN2 _ hd, one_mul]

theorem exists_conj_eq_mul_self {Y : Type*} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    (hA : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (σ : MulAut Y) :
    ∃ c : Y, σ * σ = MulAut.conj c := by
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcZ : c ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun φ : MulAut Y => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * c = c * g * c⁻¹ * c := by rw [h1]
        _ = c * g := by group
    rwa [hZ] at hcZ
  set I := (MulAut.conj : Y →* MulAut Y).range with hI
  have hIc : Nat.card I = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : I.index ≤ 2 := by
    have h := I.card_mul_index
    have hpos : 0 < Nat.card Y := Nat.card_pos
    rw [hIc] at h
    nlinarith
  have hidx0 : I.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem : σ * σ ∈ I := by
    rcases (by omega : I.index = 1 ∨ I.index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      trivial
    · exact Subgroup.mul_self_mem_of_index_two h2 σ
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

variable {G : Type*} [Group G] {K : Subgroup G}

@[expose] def kConj (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) : ↥K ≃* ↥K where
  toFun k := ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp k.2⟩
  invFun k := ⟨x⁻¹ * k * x, (Subgroup.mem_normalizer_iff''.mp hx k).mp k.2⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem coe_kConj (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((kConj x hx k : ↥K) : G) = x * k * x⁻¹ := rfl

@[expose] noncomputable def barConj (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    MulAut (↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (kConj x hx)
    (Subgroup.characteristic_iff_map_eq.mp inferInstance (kConj x hx))

theorem barConj_mk (x : G) (hx : x ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    barConj x hx (k : ↥K ⧸ Subgroup.center ↥K) = ((kConj x hx k : ↥K) : ↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.congr_mk _ _ _ _ k

theorem mul_self_mem_centralizer (hK : commutator ↥K = ⊤) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (h : barConj x hx * barConj x hx = 1) :
    x * x ∈ Subgroup.centralizer (K : Set G) := by
  have hxx : x * x ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hx hx
  set α := kConj (x * x) hxx with hα
  have hz : ∀ k : ↥K, α k * k⁻¹ ∈ Subgroup.center ↥K := by
    intro k
    have h1 := congrArg (fun φ : MulAut (↥K ⧸ Subgroup.center ↥K) =>
      φ (k : ↥K ⧸ Subgroup.center ↥K)) h
    simp only [MulAut.mul_apply, barConj_mk, MulAut.one_apply] at h1
    have h2 : kConj x hx (kConj x hx k) = α k := Subtype.ext (by
      simp only [coe_kConj, hα]
      group)
    rw [h2, QuotientGroup.eq] at h1
    have h5 : α k * k⁻¹ = k * ((α k)⁻¹ * k)⁻¹ * k⁻¹ := by group
    rw [h5]
    exact (Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ h1) k)
  let f : ↥K →* ↥(Subgroup.center ↥K) :=
    { toFun := fun k => ⟨α k * k⁻¹, hz k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb := Subgroup.mem_center_iff.mp (hz b) a⁻¹
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc α a * α b * (b⁻¹ * a⁻¹) = α a * ((α b * b⁻¹) * a⁻¹) := by group
          _ = α a * (a⁻¹ * (α b * b⁻¹)) := by rw [hb]
          _ = α a * a⁻¹ * (α b * b⁻¹) := by group) }
  have hker : f.ker = ⊤ := top_le_iff.mp (hK ▸ Abelianization.commutator_subset_ker f)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : f ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    trivial
  have h2 : α ⟨k, hk⟩ = ⟨k, hk⟩ := by
    have := congrArg Subtype.val h1
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
    exact mul_inv_eq_one.mp this
  have h3 := congrArg Subtype.val h2
  rw [hα, coe_kConj] at h3
  calc k * (x * x) = (x * x) * k * (x * x)⁻¹ * (x * x) := by rw [h3]
    _ = x * x * k := by group

end CFSG.Quasithin.C48Cover

module

public import CFSG.Quasithin.Background.Harris.R1.D4VertWords
public import CFSG.Quasithin.Recognition.CertF8

public section

namespace CFSG.Quasithin.Background.Harris.R1.L28Q4

open CFSG.Quasithin

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Q4 where
  a : GF8
  b : GF8
  c : GF8
  d : GF8
  deriving DecidableEq

namespace Q4

@[expose] def mul (x y : Q4) : Q4 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

@[expose] def adj (x : Q4) : Q4 := ⟨x.d, x.b, x.c, x.a⟩

@[expose] def one : Q4 := ⟨1, 0, 0, 1⟩

end Q4

@[expose] def wordQ (g : Fin 2 → Q4) (w : List (Fin 2 × Bool)) : Q4 :=
  w.foldl (fun acc p => acc.mul (if p.2 then g p.1 else (g p.1).adj)) Q4.one

@[expose] def gAq : Q4 := ⟨GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0⟩

@[expose] def gBq : Q4 := ⟨GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 1⟩

@[expose] def uQ : Q4 := wordQ ![gAq, gBq] D4Vert.l28U

@[expose] def cQ : Q4 := wordQ ![gAq, gBq] D4Vert.l28C

@[expose] def allG : List GF8 := (List.range 8).map GF8.ofNat'

theorem allG_mem : ∀ a : GF8, a ∈ allG := by decide +kernel

@[expose] def bTabQ : List (Q4 × List (Fin 2 × Bool)) := [
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1⟩,
      []),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1⟩,
      [(0, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 5⟩,
      [(1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5⟩,
      [(0, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 5⟩,
      [(1, true), (0, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 7⟩,
      [(1, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 5⟩,
      [(0, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 7⟩,
      [(0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 7⟩,
      [(1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 7⟩,
      [(1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 6⟩,
      [(1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 7⟩,
      [(0, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 7⟩,
      [(0, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 6⟩,
      [(0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 7⟩,
      [(1, true), (0, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 6⟩,
      [(1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 6⟩,
      [(1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 6⟩,
      [(1, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 3⟩,
      [(1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 4, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7⟩,
      [(0, true), (1, true), (0, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 6⟩,
      [(0, true), (1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 3⟩,
      [(0, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 6⟩,
      [(1, true), (0, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 3, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 6⟩,
      [(1, true), (0, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 3⟩,
      [(1, true), (0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 3⟩,
      [(1, true), (1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 3⟩,
      [(1, true), (1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 3⟩,
      [(1, true), (1, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 4⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 3⟩,
      [(0, true), (1, true), (0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 6, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 3⟩,
      [(0, true), (1, true), (1, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 4⟩,
      [(0, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 4⟩,
      [(1, true), (0, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 4⟩,
      [(1, true), (1, true), (0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 4⟩,
      [(1, true), (1, true), (1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 4⟩,
      [(1, true), (1, true), (1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 4⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 4⟩,
      [(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 2⟩,
      [(0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 2⟩,
      [(1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 5, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 2⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1⟩,
      [(1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1⟩,
      [(1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1⟩,
      [(1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1⟩,
      [(1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 5⟩,
      [(1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 5⟩,
      [(1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 5⟩,
      [(1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (1, true)]),
    (⟨GF8.ofNat' 2, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 5⟩,
      [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true)])
  ]

@[expose] def eQ : List Q4 := [
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 5, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 6, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 7, GF8.ofNat' 1⟩]


@[expose] def hQ : List Q4 := [
    ⟨GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 0, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0⟩,
    ⟨GF8.ofNat' 0, GF8.ofNat' 2, GF8.ofNat' 5, GF8.ofNat' 1⟩,
    ⟨GF8.ofNat' 5, GF8.ofNat' 1, GF8.ofNat' 0, GF8.ofNat' 2⟩,
    ⟨GF8.ofNat' 0, GF8.ofNat' 4, GF8.ofNat' 7, GF8.ofNat' 7⟩,
    ⟨GF8.ofNat' 5, GF8.ofNat' 5, GF8.ofNat' 7, GF8.ofNat' 5⟩,
    ⟨GF8.ofNat' 7, GF8.ofNat' 7, GF8.ofNat' 0, GF8.ofNat' 4⟩,
    ⟨GF8.ofNat' 0, GF8.ofNat' 3, GF8.ofNat' 6, GF8.ofNat' 2⟩,
    ⟨GF8.ofNat' 7, GF8.ofNat' 4, GF8.ofNat' 6, GF8.ofNat' 6⟩]


@[expose] def bQ : List Q4 := bTabQ.map Prod.fst

theorem bTabQ_words : ∀ p ∈ bTabQ, wordQ ![uQ, cQ] p.2 = p.1 := by decide +kernel
theorem bQ_mul : ∀ x ∈ bQ, ∀ y ∈ bQ, x.mul y ∈ bQ := by decide +kernel
theorem bQ_adj : ∀ x ∈ bQ, x.adj ∈ bQ := by decide +kernel
theorem bQ_one : Q4.one ∈ bQ := by decide +kernel
theorem bQ_u : uQ ∈ bQ := by decide +kernel
theorem bQ_c : cQ ∈ bQ := by decide +kernel
theorem bQ_nodup : bQ.Nodup := by decide +kernel
theorem bQ_length : bQ.length = 56 := by decide +kernel
theorem eQ_length : eQ.length = 8 := by decide +kernel
theorem eQ_sub : ∀ e ∈ eQ, e ∈ bQ := by decide +kernel
theorem eQ_mul : ∀ x ∈ eQ, ∀ y ∈ eQ, x.mul y ∈ eQ := by decide +kernel
theorem eQ_normal : ∀ x ∈ bQ, ∀ e ∈ eQ, (x.mul e).mul x.adj ∈ eQ := by decide +kernel
theorem normaliser_eQ : ∀ a ∈ allG, ∀ b ∈ allG, ∀ c ∈ allG, ∀ d ∈ allG,
    a * d + b * c = 1 → (∀ e ∈ eQ, ((⟨a, b, c, d⟩ : Q4).mul e).mul (⟨a, b, c, d⟩ : Q4).adj ∈ eQ) →
    (⟨a, b, c, d⟩ : Q4) ∈ bQ := by decide +kernel
theorem gAq_not_mem : gAq ∉ bQ := by decide +kernel
theorem hQ_words : D4Vert.l28H.map (fun w => wordQ ![gAq, gBq] w) = hQ := by decide +kernel
theorem hQ_nodup : hQ.Nodup := by decide +kernel
theorem hQ_coset : ∀ x ∈ hQ, ∀ y ∈ hQ, x ≠ y → x.adj.mul y ∉ bQ := by decide +kernel

theorem eQ_adj : ∀ e ∈ eQ, e.adj ∈ eQ := by decide +kernel
theorem one_mem_eQ : Q4.one ∈ eQ := by decide +kernel
theorem eQ_nodup : eQ.Nodup := by decide +kernel
theorem commute_central : ∀ a ∈ allG, ∀ b ∈ allG, ∀ c ∈ allG, ∀ d ∈ allG,
    a * d + b * c = 1 → ((⟨a, b, c, d⟩ : Q4).mul gAq = gAq.mul ⟨a, b, c, d⟩) →
    ((⟨a, b, c, d⟩ : Q4).mul gBq = gBq.mul ⟨a, b, c, d⟩) → (⟨a, b, c, d⟩ : Q4) = Q4.one := by
  decide +kernel
theorem hQ_coset_idx : ∀ i j : Fin 9, i ≠ j →
    (wordQ ![gAq, gBq] (D4Vert.l28H.getD i.val [])).adj.mul
      (wordQ ![gAq, gBq] (D4Vert.l28H.getD j.val [])) ∉ bQ := by
  decide +kernel

end CFSG.Quasithin.Background.Harris.R1.L28Q4

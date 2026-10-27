module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Quasithin.Vol2.KGFactC31OrbSound

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier

@[expose] def g6A : Array (Array ℕ) := #[ruA0A, ruA1A, ruC0A, ruC1A, ruNs0A, ruNs1A]

@[expose] def g6IA : Array (Array ℕ) := g6A.map ruInv

@[expose] def wA (w : List ℤ) : Array ℕ := wordA 4060 g6A g6IA w

@[expose] def maskA : List (Array ℕ) → ℕ → Array ℕ
  | [], _ => idA 4060
  | b :: bs, m => compA 4060 (if m % 2 = 1 then b else idA 4060) (maskA bs (m / 2))

@[expose] def spanA (bs : List (Array ℕ)) : List (Array ℕ) :=
  (List.range (2 ^ bs.length)).map (maskA bs)

@[expose] def inA (sp : List (Array ℕ)) (t : Array ℕ) : Bool := sp.any fun u => eqA 4060 u t

@[expose] def commA (a b : Array ℕ) : Bool :=
  (List.range 8).all (fun i => a[b[i]!]! == b[a[i]!]!) &&
    eqA 4060 (compA 4060 a b) (compA 4060 b a)

@[expose] def sqIterA : ℕ → Array ℕ → Array ℕ
  | 0, t => t
  | k + 1, t => sqIterA k (compA 4060 t t)

@[expose] def cjA (h hi t : Array ℕ) : Array ℕ := compA 4060 (compA 4060 h t) hi

variable {n : ℕ}

theorem rep_maskA :
    ∀ {k : ℕ} (v : Fin k → Equiv.Perm (Fin 4060)) (bs : List (Array ℕ)),
      List.Forall₂ (Rep 4060) bs (List.ofFn v) → ∀ m,
        Rep 4060 (maskA bs m) (eElt v (maskVec k m))
  | 0, v, bs, h, m => by
    rw [List.ofFn_zero, List.forall₂_nil_right_iff] at h
    subst h
    rw [show eElt v (maskVec 0 m) = 1 by simp [eElt]]
    exact rep_idA
  | k + 1, v, bs, h, m => by
    rw [List.ofFn_succ] at h
    cases h with
    | cons hb hbs =>
      rw [maskA, eElt_succ, maskVec_succ, maskVec_zero]
      refine rep_compA ?_ (rep_maskA (fun i => v i.succ) _ hbs (m / 2))
      have hval : ((m % 2 : ℕ) : ZMod 2).val = m % 2 :=
        ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))
      rw [hval]
      split_ifs with h1
      · rw [h1, pow_one]; exact hb
      · have h0 : m % 2 = 0 := by omega
        rw [h0, pow_zero]; exact rep_idA

theorem inA_spanA_iff {k : ℕ} {v : Fin k → Equiv.Perm (Fin 4060)} {bs : List (Array ℕ)}
    (hbs : List.Forall₂ (Rep 4060) bs (List.ofFn v)) {t : Array ℕ} {g : Equiv.Perm (Fin 4060)}
    (ht : Rep 4060 t g) : inA (spanA bs) t = true ↔ ∃ c, eElt v c = g := by
  have hlen : bs.length = k := by rw [hbs.length_eq, List.length_ofFn]
  rw [inA, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hu
    exact ⟨_, eq_of_eqA (rep_maskA v bs hbs m) ht he⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨m, hm, rfl⟩ := exists_maskVec c
    refine ⟨maskA bs m, List.mem_map.mpr ⟨m, ?_, rfl⟩,
      (eqA_iff (rep_maskA v bs hbs m) ht).2 rfl⟩
    rw [List.mem_range, hlen]
    exact hm

theorem commA_iff {a b : Array ℕ} {g h : Equiv.Perm (Fin 4060)} (ha : Rep 4060 a g)
    (hb : Rep 4060 b h) : commA a b = true ↔ g * h = h * g := by
  rw [commA, Bool.and_eq_true]
  constructor
  · rintro ⟨-, he⟩
    exact eq_of_eqA (rep_compA ha hb) (rep_compA hb ha) he
  · intro he
    refine ⟨?_, (eqA_iff (rep_compA ha hb) (rep_compA hb ha)).2 he⟩
    rw [List.all_eq_true]
    intro i hi
    have hi' : i < 4060 := by have := List.mem_range.1 hi; omega
    have h1 := (rep_compA ha hb).apply hi'
    have h2 := (rep_compA hb ha).apply hi'
    rw [compA_get hi'] at h1 h2
    rw [beq_iff_eq, h1, h2, he]

theorem rep_sqIterA {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g) :
    ∀ k, Rep 4060 (sqIterA k t) (g ^ 2 ^ k)
  | 0 => by simpa [sqIterA] using ht
  | k + 1 => by
    rw [sqIterA, pow_succ, mul_comm, pow_mul]
    have := rep_sqIterA (rep_compA ht ht) k
    rwa [← sq] at this

theorem rep_cjA {h hi t : Array ℕ} {hg tg : Equiv.Perm (Fin 4060)} (hh : Rep 4060 h hg)
    (hhi : Rep 4060 hi hg⁻¹) (ht : Rep 4060 t tg) : Rep 4060 (cjA h hi t) (hg * tg * hg⁻¹) :=
  rep_compA (rep_compA hh ht) hhi

end CFSG.Quasithin.KGC31.Ru

end

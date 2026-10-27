module

public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.RankThree.Native.PrimeLines

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def linesOKG (p N r n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert)
    (xs : Array (Array ℕ)) : Bool :=
  enumOK n gs ps c && c.pts.size == N &&
    allLt N (fun k => eqA n (powArr n c.pts[k]! p) (idA n)) &&
    allLt N (fun k => eqA n c.pts[k]! (idA n) ||
      (List.range r).any fun j => (List.range p).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) &&
    allLt r (fun j => allLt r fun j' => j == j' ||
      allLt p fun e => !(eqA n xs[j]! (powArr n xs[j']! e))) &&
    allLt r (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! p) (idA n) &&
      !(eqA n xs[j]! (idA n)) && c.pts.toList.any (eqA n xs[j]!))

section Lines

variable {p N r n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {xs : Array (Array ℕ)}

theorem linesOKG_parts (h : linesOKG p N r n gs ps c xs = true) :
    enumOK n gs ps c = true ∧ c.pts.size = N ∧
    allLt N (fun k => eqA n (powArr n c.pts[k]! p) (idA n)) = true ∧
    allLt N (fun k => eqA n c.pts[k]! (idA n) ||
      (List.range r).any fun j => (List.range p).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) = true ∧
    allLt r (fun j => allLt r fun j' => j == j' ||
      allLt p fun e => !(eqA n xs[j]! (powArr n xs[j']! e))) = true ∧
    allLt r (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! p) (idA n) &&
      !(eqA n xs[j]! (idA n)) && c.pts.toList.any (eqA n xs[j]!)) = true := by
  simp only [linesOKG, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem linesOKG_line (h : linesOKG p N r n gs ps c xs = true) (j : Fin r) :
    validA n xs[(j : ℕ)]! = true ∧ eqA n (powArr n xs[(j : ℕ)]! p) (idA n) = true ∧
      eqA n xs[(j : ℕ)]! (idA n) = false ∧ c.pts.toList.any (eqA n xs[(j : ℕ)]!) = true := by
  have hl := allLt_spec (linesOKG_parts h).2.2.2.2.2 j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hl
  exact ⟨hl.1.1.1, hl.1.1.2, hl.1.2, hl.2⟩

theorem linesOKG_valid (h : linesOKG p N r n gs ps c xs = true) :
    ∀ i < r, validA n xs[i]! = true := fun i hi => (linesOKG_line h ⟨i, hi⟩).1

theorem linesOKG_rep (h : linesOKG p N r n gs ps c xs = true) (j : Fin r) :
    Rep n xs[(j : ℕ)]! (permOfArr n xs[(j : ℕ)]!) :=
  rep_of_validA (linesOKG_line h j).1

theorem linesOKG_ne_one (h : linesOKG p N r n gs ps c xs = true) (j : Fin r) :
    permOfArr n xs[(j : ℕ)]! ≠ 1 := fun e => by
  have := (eqA_iff (linesOKG_rep h j) rep_idA).2 e
  rw [(linesOKG_line h j).2.2.1] at this
  exact Bool.false_ne_true this

theorem linesOKG_pow_line (h : linesOKG p N r n gs ps c xs = true) (j : Fin r) :
    permOfArr n xs[(j : ℕ)]! ^ p = 1 :=
  (eqA_iff (rep_powArr (linesOKG_rep h j) p) rep_idA).1 (linesOKG_line h j).2.1

theorem linesOKG_orderOf (hp : p.Prime) (h : linesOKG p N r n gs ps c xs = true) (j : Fin r) :
    orderOf (permOfArr n xs[(j : ℕ)]!) = p := by
  have : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (linesOKG_pow_line h j) (linesOKG_ne_one h j)

theorem linesOKG_card (hps : ∀ q ∈ ps, q < n) (h : linesOKG p N r n gs ps c xs = true) :
    Nat.card (Subgroup.closure (permsA n gs)) = N :=
  (enumOK_spec hps (linesOKG_parts h).1).2.1.trans (linesOKG_parts h).2.1

theorem linesOKG_pow (hps : ∀ q ∈ ps, q < n) (h : linesOKG p N r n gs ps c xs = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.closure (permsA n gs)) : g ^ p = 1 := by
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps (linesOKG_parts h).1 hg
  rw [(linesOKG_parts h).2.1] at hk
  exact (eqA_iff (rep_powArr hkg p) rep_idA).1 (allLt_spec (linesOKG_parts h).2.2.1 hk)

theorem linesOKG_mem (hps : ∀ q ∈ ps, q < n) (h : linesOKG p N r n gs ps c xs = true)
    (j : Fin r) : permOfArr n xs[(j : ℕ)]! ∈ Subgroup.closure (permsA n gs) :=
  enumOK_mem_of_any hps (linesOKG_parts h).1 (linesOKG_rep h j) (linesOKG_line h j).2.2.2

theorem linesOKG_exponent (hp : p.Prime) (hr : 0 < r) (hps : ∀ q ∈ ps, q < n)
    (h : linesOKG p N r n gs ps c xs = true) :
    Monoid.exponent (Subgroup.closure (permsA n gs)) = p := by
  have hdvd : Monoid.exponent (Subgroup.closure (permsA n gs)) ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (linesOKG_pow hps h g.2)
  rcases (Nat.dvd_prime hp).1 hdvd with he | he
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 he
    have := congrArg Subtype.val
      (hs.elim (⟨_, linesOKG_mem hps h ⟨0, hr⟩⟩ : Subgroup.closure (permsA n gs)) 1)
    exact linesOKG_ne_one h ⟨0, hr⟩ this
  · exact he

theorem linesOKG_lines (hp : p.Prime) (hps : ∀ q ∈ ps, q < n)
    (h : linesOKG p N r n gs ps c xs = true) :
    {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Subgroup.closure (permsA n gs) ∧ Nat.card H = p} =
        Set.range (fun j : Fin r => Subgroup.zpowers (permOfArr n xs[(j : ℕ)]!)) ∧
      Function.Injective (fun j : Fin r => Subgroup.zpowers (permOfArr n xs[(j : ℕ)]!)) := by
  have hP := linesOKG_parts h
  have : Fact p.Prime := ⟨hp⟩
  apply prime_subgroups_eq_range (fun j : Fin r => permOfArr n xs[(j : ℕ)]!)
    (linesOKG_mem hps h) (linesOKG_ne_one h) (linesOKG_pow_line h)
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hP.1 hg
    rw [hP.2.1] at hk
    have hc := allLt_spec hP.2.2.2.1 hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at hc
    rcases hc with hc | ⟨j, hj, e, -, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 hc) hg1
    · exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (linesOKG_rep h ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj
    by_contra hne
    have hd := allLt_spec (allLt_spec hP.2.2.2.2.1 j.2) j'.2
    have hne' : ((j : ℕ) == (j' : ℕ)) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => hne (Fin.ext e)
    rw [hne', Bool.false_or] at hd
    have := allLt_spec hd hk
    rw [Bool.not_eq_true', ← Bool.not_eq_true] at this
    exact this ((eqA_iff (linesOKG_rep h j) (rep_powArr (linesOKG_rep h j') k)).2 hjj)

theorem factorization_pow_mulG {k m : ℕ} (hp : p.Prime) (hm : ¬p ∣ m) :
    (p ^ k * m).factorization p = k := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, Nat.add_zero]

theorem linesOKG_sylow {k : ℕ} (hp : p.Prime) {P : Subgroup (Equiv.Perm (Fin n))}
    (hps : ∀ q ∈ ps, q < n) (h : linesOKG p N r n gs ps c xs = true)
    (hQP : Subgroup.closure (permsA n gs) ≤ P) (hk : (Nat.card P).factorization p = k)
    (hN : N = p ^ k) :
    ∃ S : Sylow p P, (S : Subgroup P) = (Subgroup.closure (permsA n gs)).subgroupOf P := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ((Subgroup.closure (permsA n gs)).subgroupOf P) =
      p ^ (Nat.card P).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, linesOKG_card hps h, hk, hN]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem linesOKG_sylow_of_card {k m : ℕ} (hp : p.Prime) {P : Subgroup (Equiv.Perm (Fin n))}
    (hps : ∀ q ∈ ps, q < n) (h : linesOKG p N r n gs ps c xs = true)
    (hQP : Subgroup.closure (permsA n gs) ≤ P) (hP : Nat.card P = p ^ k * m) (hm : ¬p ∣ m)
    (hN : N = p ^ k) :
    ∃ S : Sylow p P, (S : Subgroup P) = (Subgroup.closure (permsA n gs)).subgroupOf P :=
  linesOKG_sylow hp hps h hQP (by rw [hP]; exact factorization_pow_mulG hp hm) hN

end Lines

end CFSG.RankThree.PartOne

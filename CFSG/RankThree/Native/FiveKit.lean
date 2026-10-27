module

public import CFSG.RankThree.Native.ChainCentralizer
public import CFSG.RankThree.Native.PrimeLines
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Monster.B.Mathieu.SylowSound
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.Bool

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open scoped commutatorElement

variable {n : ℕ}

@[expose] def pow5A (n : ℕ) (x : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 5) fun e => powArr n x e

theorem rep_pow5A {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X) :
    ∀ e < (pow5A n x).size, Rep n (pow5A n x)[e]! (X ^ e) := by
  intro e he
  rw [getElem!_pos _ e he]
  simp only [pow5A, Array.getElem_ofFn]
  exact rep_powArr hx e

@[expose] def linesOK (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert)
    (xs : Array (Array ℕ)) : Bool :=
  enumOK n gs ps c && c.pts.size == 125 &&
    allLt 125 (fun k => eqA n (powArr n c.pts[k]! 5) (idA n)) &&
    allLt 125 (fun k => eqA n c.pts[k]! (idA n) ||
      (List.range 31).any fun j => (List.range 5).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) &&
    allLt 31 (fun j => allLt 31 fun j' => j == j' ||
      allLt 5 fun e => !(eqA n xs[j]! (powArr n xs[j']! e))) &&
    allLt 31 (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! 5) (idA n) &&
      !(eqA n xs[j]! (idA n)) && c.pts.toList.any (eqA n xs[j]!))

section Lines

variable {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {xs : Array (Array ℕ)}

theorem linesOK_parts (h : linesOK n gs ps c xs = true) :
    enumOK n gs ps c = true ∧ c.pts.size = 125 ∧
    allLt 125 (fun k => eqA n (powArr n c.pts[k]! 5) (idA n)) = true ∧
    allLt 125 (fun k => eqA n c.pts[k]! (idA n) ||
      (List.range 31).any fun j => (List.range 5).any fun e =>
        eqA n c.pts[k]! (powArr n xs[j]! e)) = true ∧
    allLt 31 (fun j => allLt 31 fun j' => j == j' ||
      allLt 5 fun e => !(eqA n xs[j]! (powArr n xs[j']! e))) = true ∧
    allLt 31 (fun j => validA n xs[j]! && eqA n (powArr n xs[j]! 5) (idA n) &&
      !(eqA n xs[j]! (idA n)) && c.pts.toList.any (eqA n xs[j]!)) = true := by
  simp only [linesOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem linesOK_line (h : linesOK n gs ps c xs = true) (j : Fin 31) :
    validA n xs[(j : ℕ)]! = true ∧ eqA n (powArr n xs[(j : ℕ)]! 5) (idA n) = true ∧
      eqA n xs[(j : ℕ)]! (idA n) = false ∧ c.pts.toList.any (eqA n xs[(j : ℕ)]!) = true := by
  have hl := allLt_spec (linesOK_parts h).2.2.2.2.2 j.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hl
  exact ⟨hl.1.1.1, hl.1.1.2, hl.1.2, hl.2⟩

theorem linesOK_rep (h : linesOK n gs ps c xs = true) (j : Fin 31) :
    Rep n xs[(j : ℕ)]! (permOfArr n xs[(j : ℕ)]!) :=
  rep_of_validA (linesOK_line h j).1

theorem linesOK_ne_one (h : linesOK n gs ps c xs = true) (j : Fin 31) :
    permOfArr n xs[(j : ℕ)]! ≠ 1 := fun e => by
  have := (eqA_iff (linesOK_rep h j) rep_idA).2 e
  rw [(linesOK_line h j).2.2.1] at this
  exact Bool.false_ne_true this

theorem linesOK_pow_line (h : linesOK n gs ps c xs = true) (j : Fin 31) :
    permOfArr n xs[(j : ℕ)]! ^ 5 = 1 :=
  (eqA_iff (rep_powArr (linesOK_rep h j) 5) rep_idA).1 (linesOK_line h j).2.1

theorem linesOK_orderOf (h : linesOK n gs ps c xs = true) (j : Fin 31) :
    orderOf (permOfArr n xs[(j : ℕ)]!) = 5 :=
  orderOf_eq_prime (linesOK_pow_line h j) (linesOK_ne_one h j)

variable (hps : ∀ p ∈ ps, p < n) (h : linesOK n gs ps c xs = true)
include hps h

theorem linesOK_card : Nat.card (Subgroup.closure (permsA n gs)) = 125 :=
  (enumOK_spec hps (linesOK_parts h).1).2.1.trans (linesOK_parts h).2.1

theorem linesOK_pow {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.closure (permsA n gs)) :
    g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps (linesOK_parts h).1 hg
  rw [(linesOK_parts h).2.1] at hk
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec (linesOK_parts h).2.2.1 hk)

theorem linesOK_mem (j : Fin 31) :
    permOfArr n xs[(j : ℕ)]! ∈ Subgroup.closure (permsA n gs) :=
  enumOK_mem_of_any hps (linesOK_parts h).1 (linesOK_rep h j) (linesOK_line h j).2.2.2

theorem linesOK_exponent : Monoid.exponent (Subgroup.closure (permsA n gs)) = 5 := by
  have hdvd : Monoid.exponent (Subgroup.closure (permsA n gs)) ∣ 5 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (linesOK_pow hps h g.2)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with he | he
  · exfalso
    have hs := Monoid.exp_eq_one_iff.1 he
    have := congrArg Subtype.val
      (hs.elim (⟨_, linesOK_mem hps h 0⟩ : Subgroup.closure (permsA n gs)) 1)
    exact linesOK_ne_one h 0 this
  · exact he

theorem linesOK_lines :
    {H : Subgroup (Equiv.Perm (Fin n)) | H ≤ Subgroup.closure (permsA n gs) ∧ Nat.card H = 5} =
        Set.range (fun j : Fin 31 => Subgroup.zpowers (permOfArr n xs[(j : ℕ)]!)) ∧
      Function.Injective (fun j : Fin 31 => Subgroup.zpowers (permOfArr n xs[(j : ℕ)]!)) := by
  have hP := linesOK_parts h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply prime_subgroups_eq_range (fun j : Fin 31 => permOfArr n xs[(j : ℕ)]!)
    (linesOK_mem hps h) (linesOK_ne_one h) (linesOK_pow_line h)
  · intro g hg hg1
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hP.1 hg
    rw [hP.2.1] at hk
    have hc := allLt_spec hP.2.2.2.1 hk
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range] at hc
    rcases hc with hc | ⟨j, hj, e, -, hje⟩
    · exact absurd ((eqA_iff hkg rep_idA).1 hc) hg1
    · exact ⟨⟨j, hj⟩, e, (eqA_iff hkg (rep_powArr (linesOK_rep h ⟨j, hj⟩) e)).1 hje⟩
  · intro j j' k hk hjj
    by_contra hne
    have hd := allLt_spec (allLt_spec hP.2.2.2.2.1 j.2) j'.2
    have hne' : ((j : ℕ) == (j' : ℕ)) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => hne (Fin.ext e)
    rw [hne', Bool.false_or] at hd
    have := allLt_spec hd hk
    rw [Bool.not_eq_true', ← Bool.not_eq_true] at this
    exact this ((eqA_iff (linesOK_rep h j) (rep_powArr (linesOK_rep h j') k)).2 hjj)

end Lines

section Chain

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}

theorem mem_of_siftA (hA : ChainArrays Q O S base W) (hc : rawChainOK n O S base W 1 = true)
    {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hG : Rep n g G)
    (hs : siftA n (rawLevels n S base) base 0 g = true) : G ∈ Q.originalSubgroup :=
  (siftA_iff_mem_originalSubgroup hA (by norm_num) hc hG).1 hs

@[expose] def relsOK (n : ℕ) (base x : Array ℕ) (rels : List (ℕ × ℕ × ℕ)) : Bool :=
  rels.all fun r => decide (r.2.2 < 5) && decide (r.1 < base.size) &&
    decide (r.2.1 < base.size) && (powArr n x r.2.2)[base[r.1]!]! == base[r.2.1]!

theorem relsOK_spec {x : Array ℕ} {rels : List (ℕ × ℕ × ℕ)} (h : relsOK n base x rels = true) :
    ∀ r ∈ rels, r.2.2 < (pow5A n x).size ∧ r.1 < base.size ∧ r.2.1 < base.size ∧
      ((pow5A n x)[r.2.2]!)[base[r.1]!]! = base[r.2.1]! := by
  intro r hr
  have h' := List.all_eq_true.1 h r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  refine ⟨by simpa [pow5A] using h1, h2, h3, ?_⟩
  rw [getElem!_pos (pow5A n x) r.2.2 (by simpa [pow5A] using h1)]
  simpa [pow5A] using h4

theorem centralizer_eq_of_ptailOK (hA : ChainArrays Q O S base W)
    (hc : rawChainOK n O S base W 1 = true) {x : Array ℕ} {X : Equiv.Perm (Fin n)}
    (hx : Rep n x X) {rels : List (ℕ × ℕ × ℕ)} (hrels : relsOK n base x rels = true)
    {gs : Array (Array ℕ)} {ps : List ℕ} {cC : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hC : enumOK n gs ps cC = true) (hcomm : allLt gs.size (fun k => commA n gs[k]! x) = true)
    (hsift : allLt gs.size (fun k => siftA n (rawLevels n S base) base 0 gs[k]!) = true)
    (htail : ptailOK n (rawLevels n S base) base x (pow5A n x) rels cC.pts.toList base.size 0
      (idA n) = true) :
    Subgroup.closure (permsA n gs) = Subgroup.centralizer {X} ⊓ Q.originalSubgroup := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hrep := rep_of_validA (enumOK_gens_valid hC hk)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · exact (commA_iff hrep hx).1 (allLt_spec hcomm hk)
    · exact mem_of_siftA hA hc hrep (allLt_spec hsift hk)
  · intro g hg
    have htail' : ptailOK n (rawLevels n S base) base x (pow5A n x) rels cC.pts.toList
        Q.baseCount 0 (idA n) = true := by
      rw [← hA.base_size]
      exact htail
    obtain ⟨e, he, hre⟩ := centralizer_subset_of_ptailOK hA (chainCheckFacts hc)
      (validSchreier_of_chainOK hA (by norm_num) hc).1 hx (rep_pow5A hx) (relsOK_spec hrels)
      htail' hg
    exact enumOK_mem_of_mem hps hC hre he

theorem originalSubgroup_ofArrays_three {S : Array (Array ℕ)} {hn : 1 ≤ n} {hk : 3 ≤ S.size}
    {bs : List (Fin n)} {hb : bs.Nodup} {W' : Array (List ℤ)}
    (hc : rawChainOK n (S.extract 0 3) S (bs.map Fin.val).toArray W' 1 = true)
    {a b u : Array ℕ} {A B U : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (hu : Rep n u U) (e0 : eqA n S[0]! a = true) (e1 : eqA n S[1]! b = true)
    (e2 : eqA n S[2]! u = true) :
    (RawSchreierDatum.ofArrays n hn S 3 hk bs hb W').originalSubgroup =
      Subgroup.closure {A, B, U} := by
  have hinv := (chainCheckFacts hc).strong_inv
  have hrep : ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) := fun j hj =>
    (rep_permOfArr (hinv j hj)).1
  have g0 : permOfArr n S[0]! = A := eq_of_eqA (hrep 0 (by omega)) ha e0
  have g1 : permOfArr n S[1]! = B := eq_of_eqA (hrep 1 (by omega)) hb' e1
  have g2 : permOfArr n S[2]! = U := eq_of_eqA (hrep 2 (by omega)) hu e2
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl g0
    · exact Or.inr (Or.inl g1)
    · exact Or.inr (Or.inr g2)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, g0⟩
    · exact ⟨1, by norm_num, g1⟩
    · exact ⟨2, by norm_num, g2⟩

end Chain

section Normal

variable {gC gA : Array (Array ℕ)} {ps : List ℕ} {cC cA : ArrCert}

theorem le_of_gens_mem (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (hAe : enumOK n gA ps cA = true)
    (hmem : allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true) :
    Subgroup.closure (permsA n gA) ≤ Subgroup.closure (permsA n gC) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact enumOK_mem_of_any hps hC (rep_of_validA (enumOK_gens_valid hAe hl)) (allLt_spec hmem hl)

theorem normal_kit (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (hAe : enumOK n gA ps cA = true)
    (hmem : allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true)
    (hnorm : allLt gC.size (fun k => allLt gA.size fun l =>
      cA.pts.toList.any (eqA n (conjA n gC[k]! gA[l]!))) = true) :
    ((Subgroup.closure (permsA n gA)).subgroupOf (Subgroup.closure (permsA n gC))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_gens_mem hps hC hAe hmem)]
  apply closure_le_normalizer_closure
  rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
  exact enumOK_mem_of_any hps hAe (rep_conjA (enumOK_gens_valid hC hk)
    (rep_of_validA (enumOK_gens_valid hAe hl))) (allLt_spec (allLt_spec hnorm hk) hl)

theorem pow_five_of_enum (hps : ∀ p ∈ ps, p < n) (hAe : enumOK n gA ps cA = true)
    (hpow : allLt cA.pts.size (fun k => eqA n (powArr n cA.pts[k]! 5) (idA n)) = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Subgroup.closure (permsA n gA)) : g ^ 5 = 1 := by
  obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hAe hg
  exact (eqA_iff (rep_powArr hkg 5) rep_idA).1 (allLt_spec hpow hk)

theorem mem_centralizer_closure_iff {g : Equiv.Perm (Fin n)} :
    g ∈ Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ↔
      ∀ l < gA.size, permOfArr n gA[l]! * g = g * permOfArr n gA[l]! := by
  constructor
  · intro hg l hl
    exact Subgroup.mem_centralizer_iff.1 hg _ (Subgroup.subset_closure (mem_permsA hl))
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      exact h l hl
    | one => simp
    | mul y z _ _ hy hz => exact Commute.mul_left hy hz
    | inv y _ hy => exact Commute.inv_left hy

theorem centralizer_eq_zpowers_kit (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (hAe : enumOK n gA ps cA = true) {x : Array ℕ} {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    (hXC : X ∈ Subgroup.closure (permsA n gC))
    (hXA : X ∈ Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))))
    (hcent : allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      (List.range 5).any fun e => eqA n cC.pts[k]! (powArr n x e)) = true) :
    Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓
      Subgroup.closure (permsA n gC) = Subgroup.zpowers X := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hC hgC
    have hc : (allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) = true := by
      refine allLt_iff.2 fun l hl => ?_
      exact (commA_iff hkg (rep_of_validA (enumOK_gens_valid hAe hl))).2
        ((mem_centralizer_closure_iff.1 hgA l hl).symm)
    have h := allLt_spec hcent hk
    rw [hc] at h
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range] at h
    obtain ⟨e, -, he⟩ := h
    rw [(eqA_iff hkg (rep_powArr hx e)).1 he]
    exact Subgroup.npow_mem_zpowers _ e
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨hXA, hXC⟩

theorem centralizer_eq_self_kit (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (hAe : enumOK n gA ps cA = true)
    (hmem : allLt gA.size (fun l => cC.pts.toList.any (eqA n gA[l]!)) = true)
    (hab : allLt gA.size (fun l => allLt gA.size fun l' => commA n gA[l]! gA[l']!) = true)
    (hcent : allLt cC.pts.size (fun k => !(allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) ||
      cA.pts.toList.any (eqA n cC.pts[k]!)) = true) :
    Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) ⊓
      Subgroup.closure (permsA n gC) = Subgroup.closure (permsA n gA) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k, hk, hkg⟩ := enumOK_exists_rep hps hC hgC
    have hc : (allLt gA.size fun l => commA n cC.pts[k]! gA[l]!) = true := by
      refine allLt_iff.2 fun l hl => ?_
      exact (commA_iff hkg (rep_of_validA (enumOK_gens_valid hAe hl))).2
        ((mem_centralizer_closure_iff.1 hgA l hl).symm)
    have h := allLt_spec hcent hk
    rw [hc, Bool.not_true, Bool.false_or] at h
    exact enumOK_mem_of_any hps hAe hkg h
  · intro g hg
    refine Subgroup.mem_inf.2 ⟨?_, le_of_gens_mem hps hC hAe hmem hg⟩
    have hgen : ∀ l < gA.size, permOfArr n gA[l]! ∈
        Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) := by
      intro l hl
      rw [mem_centralizer_closure_iff]
      intro l' hl'
      exact ((commA_iff (rep_of_validA (enumOK_gens_valid hAe hl))
        (rep_of_validA (enumOK_gens_valid hAe hl'))).1 (allLt_spec (allLt_spec hab hl) hl')).symm
    have hle : Subgroup.closure (permsA n gA) ≤
        Subgroup.centralizer (Subgroup.closure (permsA n gA) : Set (Equiv.Perm (Fin n))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨l, hl, rfl⟩
      exact hgen l hl
    exact hle hg

end Normal

section Derived

variable {gC gD : Array (Array ℕ)} {ps : List ℕ} {cC cD : ArrCert}

theorem derived_kit (hps : ∀ p ∈ ps, p < n) (hC : enumOK n gC ps cC = true)
    (hDe : enumOK n gD ps cD = true) (h3 : 3 ≤ gC.size)
    (hgD : gD = #[commutatorA n gC[1]! gC[2]!, gC[2]!]) {c d : Array ℕ}
    (hcv : validA n c = true) (hdv : validA n d = true)
    (hcm : cC.pts.toList.any (eqA n c) = true) (hdm : cC.pts.toList.any (eqA n d) = true)
    (hb : eqA n gC[2]! (commutatorA n c d) = true)
    (hnorm : allLt gC.size (fun k => allLt gD.size fun l =>
      cD.pts.toList.any (eqA n (conjA n gC[k]! gD[l]!))) = true)
    (hcomm : allLt gC.size (fun k => allLt gC.size fun l =>
      cD.pts.toList.any (eqA n (commutatorA n gC[k]! gC[l]!))) = true) :
    ⁅Subgroup.closure (permsA n gC), Subgroup.closure (permsA n gC)⁆ =
      Subgroup.closure (permsA n gD) := by
  have hval : ∀ k < gC.size, validA n gC[k]! = true := fun k hk => enumOK_gens_valid hC hk
  have hmemC : ∀ k < gC.size, permOfArr n gC[k]! ∈ Subgroup.closure (permsA n gC) :=
    fun k hk => Subgroup.subset_closure (mem_permsA hk)
  have hcC : permOfArr n c ∈ Subgroup.closure (permsA n gC) :=
    enumOK_mem_of_any hps hC (rep_of_validA hcv) hcm
  have hdC : permOfArr n d ∈ Subgroup.closure (permsA n gC) :=
    enumOK_mem_of_any hps hC (rep_of_validA hdv) hdm
  have hg2 : permOfArr n gC[2]! = ⁅permOfArr n c, permOfArr n d⁆ :=
    (eqA_iff (rep_of_validA (hval 2 (by omega))) (rep_commutatorA hcv hdv)).1 hb
  have hD0 : permOfArr n gD[0]! = ⁅permOfArr n gC[1]!, permOfArr n gC[2]!⁆ := by
    have e : gD[0]! = commutatorA n gC[1]! gC[2]! := by simp [hgD]
    rw [e]
    exact permOfArr_eq_of_rep (rep_commutatorA (hval 1 (by omega)) (hval 2 (by omega)))
  have hD1 : permOfArr n gD[1]! = permOfArr n gC[2]! := by
    have e : gD[1]! = gC[2]! := by simp [hgD]
    rw [e]
  have hDsize : gD.size = 2 := by simp [hgD]
  apply commutator_closure_eq_closure
  · rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := hDsize ▸ hl
    obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
    · dsimp only
      rw [hD0]
      exact Subgroup.commutator_mem_commutator (hmemC 1 (by omega)) (hmemC 2 (by omega))
    · dsimp only
      rw [hD1, hg2]
      exact Subgroup.commutator_mem_commutator hcC hdC
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any hps hDe (rep_conjA (hval k hk) (rep_of_validA
      (enumOK_gens_valid hDe hl))) (allLt_spec (allLt_spec hnorm hk) hl)
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any hps hDe (rep_commutatorA (hval k hk) (hval l hl))
      (allLt_spec (allLt_spec hcomm hk) hl)

end Derived

end CFSG.RankThree.Native

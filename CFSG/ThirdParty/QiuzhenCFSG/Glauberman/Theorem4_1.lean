module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_1
public import Mathlib.GroupTheory.Nilpotent

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — §4, Theorem 4.1 and Corollary 4.1

Statements and proofs of Lemma 4.1, Theorem 4.1 (the replacement theorem for odd primes) and
Corollary 4.1 of George Glauberman, *A Characteristic Subgroup of a p-Stable Group*, Canadian
Journal of Mathematics 20 (1968), 1101–1135 — reference [6] of the dihedral-Sylow project —
following the validated transcription in `refs/glauberman-p-stable.tex` (Lemma 4.1 at L752–L779,
Theorem 4.1 at L781–L917, Corollary 4.1 at L919–L925).

The statement uses Gorenstein's `A(S)` (`thompsonAbelianSubgroups S`) and `Z(J(S))`
(`thompsonCenter S`, equal to the wrapper's `ZJ S`) from
`FeitThompson/Gorenstein/Chapter8_2.lean`.  The paper's `[B,A;n]` iterated commutator
(`replacementCommChain` in that module) and the lower-central-series facts
(`lowerCentralSeries_commutator_le`, `eq_one_of_mem_pGroup_sq_eq_one`) plus the conjugation
helpers of `FeitThompson/Commutator/Core.lean` (`conj_mem_commutator_of_mem_left`) are private
in the currently-cached build artifacts of those modules, so this file carries verbatim public
local copies (same convention as `Theorem3_1.lean`'s local copies of the Thompson replacement
machinery).

The paper's commutator convention is `[x,y] = x⁻¹y⁻¹xy`; Mathlib's `⁅x,y⁆` is
`x·y·x⁻¹·y⁻¹`.  The two conventions generate the same commutator *subgroups*, so all
subgroup-level statements are convention-independent; the element-level identities of
Lemma 4.1(b),(c) and the Case-2 computation are re-derived in Mathlib's right convention.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local copies of declarations that are private in the cached build -/

/-- An element of the finite `p`-group `H` of order dividing 2 is trivial, for `p` odd.
Verbatim local copy of the (private) `eq_one_of_mem_pGroup_sq_eq_one` of
`FeitThompson/Gorenstein/Chapter8_2.lean`. -/
public theorem eq_one_of_mem_pGroup_sq_eq_one
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (H : Subgroup G) (hHp : IsPGroup p ↥H) {d : G} (hd : d ∈ H) (hdsq : d ^ 2 = 1) :
    d = 1 := by
  have hpow : orderOf (⟨d, hd⟩ : H) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hdsq)
  rcases (IsPGroup.iff_orderOf (p := p) (G := H)).1 hHp (⟨d, hd⟩ : H) with ⟨k, hk⟩
  have hk_dvd : p ^ k ∣ 2 := by simpa [hk] using hpow
  have hk_zero : k = 0 := by
    cases k with
    | zero =>
        rfl
    | succ k =>
        exfalso
        have hpdvd : p ∣ 2 := by
          exact dvd_trans (dvd_pow_self p (Nat.succ_ne_zero _)) hk_dvd
        have hp_eq_two : p = 2 := by
          exact (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hpdvd
        exact hpodd hp_eq_two
  have hord : orderOf (⟨d, hd⟩ : H) = 1 := by
    simpa [hk_zero] using hk
  have htriv : (⟨d, hd⟩ : H) = 1 := orderOf_eq_one_iff.mp hord
  exact congrArg Subtype.val htriv

/-- `x·⁅a,b⁆·x⁻¹ = ⁅x·a,b⁆·⁅b,x⁆`.  Local copy of the (private) `conj_commutator_left`
of `FeitThompson/Commutator/Core.lean`. -/
public lemma conj_commutator_left (x a b : G) :
    x * ⁅a, b⁆ * x⁻¹ = ⁅x * a, b⁆ * ⁅b, x⁆ := by
  simp [commutatorElement_def, mul_assoc]

/-- Once conjugation on a generating set is controlled, it is controlled on the closure.
Local copy of the (private) `conj_mem_closure` of `FeitThompson/Commutator/Core.lean`. -/
public lemma conj_mem_closure {S : Set G} (x y : G) (hy : y ∈ Subgroup.closure S)
    (hS : ∀ z, z ∈ S → x * z * x⁻¹ ∈ Subgroup.closure S) :
    x * y * x⁻¹ ∈ Subgroup.closure S := by
  refine
    Subgroup.closure_induction (k := S)
      (p := fun z _hz => x * z * x⁻¹ ∈ Subgroup.closure S)
      (mem := fun z hz => hS z hz) (one := by simp)
      (mul := ?_) (inv := ?_) hy
  · intro a b _ha _hb ha hb
    simpa [mul_assoc] using (Subgroup.closure S).mul_mem ha hb
  · intro a _ha ha
    simpa [mul_assoc] using (Subgroup.closure S).inv_mem ha

/-- Conjugation by elements of the left subgroup preserves the commutator subgroup.
Local copy of the (private) `conj_mem_commutator_of_mem_left` of
`FeitThompson/Commutator/Core.lean`. -/
public lemma conj_mem_commutator_of_mem_left {H' K' : Subgroup G} {x y : G} (hx : x ∈ H')
    (hy : y ∈ ⁅H', K'⁆) : x * y * x⁻¹ ∈ ⁅H', K'⁆ := by
  let S : Set G := {g : G | ∃ a ∈ H', ∃ b ∈ K', ⁅a, b⁆ = g}
  have hy' : y ∈ Subgroup.closure S := by
    simpa [Subgroup.commutator_def, S] using hy
  have hS : ∀ z, z ∈ S → x * z * x⁻¹ ∈ Subgroup.closure S := by
    intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    have h₁ : ⁅x * a, b⁆ ∈ Subgroup.closure S := by
      refine Subgroup.subset_closure ?_
      exact ⟨x * a, H'.mul_mem hx ha, b, hb, rfl⟩
    have hxb : ⁅x, b⁆ ∈ Subgroup.closure S := by
      refine Subgroup.subset_closure ?_
      exact ⟨x, hx, b, hb, rfl⟩
    have h₂ : ⁅b, x⁆ ∈ Subgroup.closure S := by
      have : (⁅x, b⁆)⁻¹ ∈ Subgroup.closure S := (Subgroup.closure S).inv_mem hxb
      simpa [commutatorElement_inv] using this
    have : ⁅x * a, b⁆ * ⁅b, x⁆ ∈ Subgroup.closure S := (Subgroup.closure S).mul_mem h₁ h₂
    rewrite [conj_commutator_left]
    exact this
  have : x * y * x⁻¹ ∈ Subgroup.closure S := conj_mem_closure (S := S) x y hy' hS
  simpa [Subgroup.commutator_def, S] using this

/-- `⁅S_m, S_m⁆ ⊆ S_{m+m+1}` for the lower central series.  Verbatim local copy of the
(private) `lowerCentralSeries_commutator_le` of `FeitThompson/Gorenstein/Chapter8_2.lean`
(proved there from the Three Subgroups Lemma). -/
public theorem lowerCentralSeries_commutator_le
    (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  induction j generalizing i with
  | zero =>
      simp [Subgroup.lowerCentralSeries]
  | succ j ih =>
      let N : Subgroup G := (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
      let q : G →* G ⧸ N := QuotientGroup.mk' N
      have h1le :
          ⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
            (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤ N := by
        dsimp [N]
        rw [Subgroup.commutator_comm (⊤ : Subgroup G)]
        change
          ⁅(⊤ : Subgroup G).lowerCentralSeries (i + 1),
            (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
              (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (ih (i + 1))
      have h2le :
          ⁅⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆,
            (⊤ : Subgroup G)⁆ ≤ N := by
        dsimp [N]
        exact Subgroup.commutator_mono (ih i) le_rfl
      have h1bot :
          ⁅⁅(⊤ : Subgroup G).map q, ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆,
            ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅⁅(⊤ : Subgroup G).map q, ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆,
              ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆ =
              (⁅⁅(⊤ : Subgroup G), (⊤ : Subgroup G).lowerCentralSeries i⁆,
                (⊤ : Subgroup G).lowerCentralSeries j⁆).map q := by
                rw [Subgroup.map_commutator, Subgroup.map_commutator]
          _ ≤ N.map q := Subgroup.map_mono h1le
          _ = ⊥ := QuotientGroup.map_mk'_self (N := N)
      have h2bot :
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries i).map q,
            ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆,
            (⊤ : Subgroup G).map q⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries i).map q,
              ((⊤ : Subgroup G).lowerCentralSeries j).map q⁆,
              (⊤ : Subgroup G).map q⁆ =
              (⁅⁅(⊤ : Subgroup G).lowerCentralSeries i,
                (⊤ : Subgroup G).lowerCentralSeries j⁆, (⊤ : Subgroup G)⁆).map q := by
                rw [Subgroup.map_commutator, Subgroup.map_commutator]
          _ ≤ N.map q := Subgroup.map_mono h2le
          _ = ⊥ := QuotientGroup.map_mk'_self (N := N)
      have hbotq :
          ⁅⁅((⊤ : Subgroup G).lowerCentralSeries j).map q, (⊤ : Subgroup G).map q⁆,
            ((⊤ : Subgroup G).lowerCentralSeries i).map q⁆ = ⊥ := by
        exact Subgroup.commutator_commutator_eq_bot_of_rotate h1bot h2bot
      have hleq :
          (⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
            (⊤ : Subgroup G).lowerCentralSeries i⁆).map q = ⊥ := by
        simpa [Subgroup.map_commutator] using hbotq
      have hle :
          ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
            (⊤ : Subgroup G).lowerCentralSeries i⁆ ≤ N := by
        have hker :=
          (Subgroup.map_eq_bot_iff
            (f := q)
            (H := ⁅⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆,
              (⊤ : Subgroup G).lowerCentralSeries i⁆)).1 hleq
        simpa [q, QuotientGroup.ker_mk'] using hker
      dsimp [N] at hle
      change ⁅(⊤ : Subgroup G).lowerCentralSeries i,
        ⁅(⊤ : Subgroup G).lowerCentralSeries j, (⊤ : Subgroup G)⁆⁆ ≤
          (⊤ : Subgroup G).lowerCentralSeries (i + j + 2)
      rw [Subgroup.commutator_comm]
      exact hle

/-- The paper's iterated commutator `[B,A;n]`: `[B,A;0] = B`, `[B,A;n+1] = [ [B,A;n], A ]`
(left-normed).  Local re-derivation of the (private) `replacementCommChain` of
`FeitThompson/Gorenstein/Chapter8_2.lean`. -/
@[expose]
public def commChain (B A : Subgroup G) : ℕ → Subgroup G
  | 0 => B
  | n + 1 => ⁅commChain B A n, A⁆

@[simp] public theorem commChain_zero (B A : Subgroup G) :
    commChain B A 0 = B := rfl

@[simp] public theorem commChain_succ (B A : Subgroup G) (n : ℕ) :
    commChain B A (n + 1) = ⁅commChain B A n, A⁆ := rfl

/-- `A` normalises every term of `[B,A;·]` (given `A ≤ N_G(B)`).  Local copy of
`replacementCommChain_le_normalizer`. -/
public theorem commChain_le_normalizer
    (B A : Subgroup G) (hB_norm : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ n, A ≤ Subgroup.normalizer (commChain B A n : Set G)
  | 0 => by
      rw [commChain_zero]
      exact hB_norm
  | n + 1 => by
      let D : Subgroup G := commChain B A n
      let : ((⁅D, A⁆).subgroupOf (D ⊔ A)).Normal := commutator_normal_in_sup D A
      have hsup_norm : D ⊔ A ≤ Subgroup.normalizer (((⁅D, A⁆ : Subgroup G) : Set G)) := by
        exact
          Subgroup.le_normalizer_of_normal_subgroupOf
            (H := ⁅D, A⁆) (K := D ⊔ A) (commutator_le_sup D A)
      rw [commChain_succ]
      exact le_sup_right.trans hsup_norm

/-- The chain descends: `[B,A;n+1] ≤ [B,A;n]`. -/
public theorem commChain_descends
    (B A : Subgroup G) (hB_norm : A ≤ Subgroup.normalizer (B : Set G)) (n : ℕ) :
    commChain B A (n + 1) ≤ commChain B A n := by
  rw [commChain_succ]
  refine (Subgroup.commutator_le).2 ?_
  intro x hx a ha
  have ha_norm : a ∈ Subgroup.normalizer (commChain B A n : Set G) :=
    commChain_le_normalizer B A hB_norm n ha
  have hconj : a * x⁻¹ * a⁻¹ ∈ commChain B A n :=
    (Subgroup.mem_normalizer_iff.mp ha_norm x⁻¹).1
      ((commChain B A n).inv_mem hx)
  rw [commutatorElement_def]
  simpa [mul_assoc] using (commChain B A n).mul_mem hx hconj

/-- Every term lies in `B`. -/
public theorem commChain_le_left
    (B A : Subgroup G) (hB_norm : A ≤ Subgroup.normalizer (B : Set G)) :
    ∀ n, commChain B A n ≤ B
  | 0 => le_rfl
  | n + 1 =>
      (commChain_descends B A hB_norm n).trans (commChain_le_left B A hB_norm n)

/-- The chain is antitone. -/
public theorem commChain_antitone
    (B A : Subgroup G) (hB_norm : A ≤ Subgroup.normalizer (B : Set G)) {i j : ℕ}
    (hij : i ≤ j) :
    commChain B A j ≤ commChain B A i := by
  induction hij with
  | refl =>
      exact le_rfl
  | @step j hij ih =>
      exact (commChain_descends B A hB_norm j).trans ih

/-- The chain terms lie in `B ⊔ A`. -/
public theorem commChain_le_sup
    (B A : Subgroup G) :
    ∀ n, commChain B A n ≤ B ⊔ A
  | 0 => le_sup_left
  | n + 1 =>
      calc
        commChain B A (n + 1) = ⁅commChain B A n, A⁆ := by
          rw [commChain_succ]
        _ ≤ commChain B A n ⊔ A := Subgroup.commutator_le_sup _ _
        _ ≤ B ⊔ A := sup_le (commChain_le_sup B A n) le_sup_right

/-- The lower central series of `S = B ⊔ A` (as subgroups of `G`). -/
public def lcs (S : Subgroup G) : ℕ → Subgroup G :=
  fun n => ((⊤ : Subgroup ↥S).lowerCentralSeries n).map S.subtype

/-- The top subgroup of `S`, mapped into `G`, is `S` itself. -/
public lemma map_top_subtype (S : Subgroup G) : (⊤ : Subgroup ↥S).map S.subtype = S := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hx_eq⟩
    exact hx_eq ▸ y.2
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩

@[simp] public theorem lcs_zero (S : Subgroup G) : lcs S 0 = S := by
  simp [lcs, map_top_subtype]

@[simp] public theorem lcs_succ (S : Subgroup G) (n : ℕ) : lcs S (n + 1) = ⁅lcs S n, S⁆ := by
  rw [lcs, lcs, Subgroup.lowerCentralSeries_succ, Subgroup.map_commutator, map_top_subtype]

/-- `lcs` is antitone. -/
public theorem lcs_antitone (S : Subgroup G) : Antitone (lcs S) := by
  intro i j hij
  unfold lcs
  exact Subgroup.map_mono (Subgroup.lowerCentralSeries_antitone _ hij)

/-- `[B,A;n] ⊆ S_{n+1}` for `S = B ⊔ A` (the lower central series term of index `n`). -/
public theorem commChain_le_lcs (B A : Subgroup G) :
    ∀ n, commChain B A n ≤ lcs (B ⊔ A) n
  | 0 => by
      simp [lcs, map_top_subtype]
  | n + 1 => by
      rw [commChain_succ, lcs_succ]
      exact
        (Subgroup.commutator_mono (commChain_le_lcs B A n) (le_sup_right : A ≤ B ⊔ A))

/-- `[B,A;n] = ⊥` for some `n`, provided `S = B ⊔ A` is nilpotent. -/
public theorem commChain_eventually_bot_of_isNilpotent
    (B A : Subgroup G)
    (hnil : Group.IsNilpotent ↥(B ⊔ A)) :
    ∃ n, commChain B A n = ⊥ := by
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := ↥(B ⊔ A))).1 hnil
  refine ⟨n, ?_⟩
  apply le_antisymm
  · calc
      commChain B A n ≤ lcs (B ⊔ A) n := commChain_le_lcs B A n
      _ = ⊥ := by
        simp [lcs, hn]
  · exact bot_le

/-- `[B,A;n] = ⊥` for some `n`, provided `S = B ⊔ A` is a finite `p`-group. -/
public theorem commChain_eventually_bot
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, commChain B A n = ⊥ := by
  exact
    commChain_eventually_bot_of_isNilpotent B A
      (IsPGroup.isNilpotent (p := p) hBAp)

/-- `[B,A;n]` is Abelian for some positive `n`. -/
public theorem commChain_exists_positive_abelian
    {p : ℕ} [Fact (Nat.Prime p)] [Finite G]
    (B A : Subgroup G)
    (hBAp : IsPGroup p ↥(B ⊔ A)) :
    ∃ n, 0 < n ∧ IsMulCommutative (commChain B A n) := by
  obtain ⟨n, hn⟩ := commChain_eventually_bot (p := p) B A hBAp
  by_cases hnpos : 0 < n
  · exact ⟨n, hnpos, by
      rw [hn]
      exact (Subgroup.le_centralizer_iff_isMulCommutative (K := ⊥)).1 bot_le⟩
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    have hBbot : B = ⊥ := by
      rw [hnzero] at hn
      simpa [commChain_zero] using hn
    rw [commChain_succ, commChain_zero, hBbot, Subgroup.commutator_bot_left]
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := ⊥)).1 bot_le

/-! ## Lemma 4.1 (paper L752–L779) — commutator identities

The paper states these in the *left* convention `[x,y] = x⁻¹y⁻¹xy`; Mathlib's `⁅x,y⁆ =
x·y·x⁻¹·y⁻¹` is the *right* convention.  Subgroup-level statements (d), (e) are
convention-independent; the element-level identities (a)–(c) are re-derived here in
Mathlib's right convention (with `(a)` and `(b)` being exactly the paper's words under
the correspondence `[x,y] ↦ ⁅x⁻¹,y⁻¹⁆`). -/

/-- Lemma 4.1(a): `[x,y] = [y,x]⁻¹`, i.e. `⁅x,y⁆ = ⁅y,x⁆⁻¹`. -/
public lemma lemma4_1a (x y : G) : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := by
  simp [commutatorElement_inv]

/-- Lemma 4.1(b): the P. Hall identity, in the paper's form
`[x,y⁻¹,z]^y · [y,z⁻¹,x]^z · [z,x⁻¹,y]^x = 1` with the substitution `y = b⁻¹`,
`z = [x,c]` used in the proof of Theorem 4.1 (paper L849–L852).  Re-derived in the right
convention: term 1 is `b·⁅⁅b⁻¹,x⁻¹⁆,[x,c]⁻¹⁆·b⁻¹`, term 2 is
`[x,c]⁻¹·⁅⁅b,[x,c]⁆⁻¹,x⁻¹⁆·[x,c]`, term 3 is `x⁻¹·⁅⁅x,[x,c]⁻¹⁆,b⁆·x`, where
`[x,c] = ⁅x⁻¹,c⁻¹⁆`. -/
public lemma lemma4_1b (x b c : G) :
    b * ⁅⁅b⁻¹, x⁻¹⁆, ⁅x⁻¹, c⁻¹⁆⁻¹⁆ * b⁻¹ *
      ((⁅x⁻¹, c⁻¹⁆)⁻¹ * ⁅⁅b, ⁅x⁻¹, c⁻¹⁆⁆⁻¹, x⁻¹⁆ * ⁅x⁻¹, c⁻¹⁆) *
      (x⁻¹ * ⁅⁅x, ⁅x⁻¹, c⁻¹⁆⁻¹⁆, b⁆ * x) = 1 := by
  simp [commutatorElement_def, mul_assoc]

/-- Lemma 4.1(c): if `[H,H] ⊆ Z(H)` then `[x,yz] = [x,y][x,z]` and `[yz,x] = [y,x][z,x]`.
The paper takes `H = ⟨x,y,z⟩`; the statement below is the general form with `x,y,z ∈ H`. -/
public lemma lemma4_1c {H : Subgroup G} (x y z : G) (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H)
    (hH : ⁅H, H⁆ ≤ centerIn H) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ ∧ ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
  have hxz_cent : ⁅x, z⁆ ∈ Subgroup.centralizer (H : Set G) := by
    have hmem : ⁅x, z⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mem_commutator hx hz
    exact (inf_le_right : centerIn H ≤ Subgroup.centralizer (H : Set G)) (hH hmem)
  have hyx_cent : ⁅y, x⁆ ∈ Subgroup.centralizer (H : Set G) := by
    have hmem : ⁅y, x⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mem_commutator hy hx
    exact (inf_le_right : centerIn H ≤ Subgroup.centralizer (H : Set G)) (hH hmem)
  have hzx_cent : ⁅z, x⁆ ∈ Subgroup.centralizer (H : Set G) := by
    have hmem : ⁅z, x⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mem_commutator hz hx
    exact (inf_le_right : centerIn H ≤ Subgroup.centralizer (H : Set G)) (hH hmem)
  have hcomm_yz : y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ := by
    have hz_y : y * ⁅x, z⁆ = ⁅x, z⁆ * y := (Subgroup.mem_centralizer_iff.mp hxz_cent) y hy
    calc
      y * ⁅x, z⁆ * y⁻¹ = (⁅x, z⁆ * y) * y⁻¹ := by rw [hz_y]
      _ = ⁅x, z⁆ := by simp [mul_assoc]
  have hcomm_yzx : y * ⁅z, x⁆ * y⁻¹ = ⁅z, x⁆ := by
    have hz_y : y * ⁅z, x⁆ = ⁅z, x⁆ * y := (Subgroup.mem_centralizer_iff.mp hzx_cent) y hy
    calc
      y * ⁅z, x⁆ * y⁻¹ = (⁅z, x⁆ * y) * y⁻¹ := by rw [hz_y]
      _ = ⁅z, x⁆ := by simp [mul_assoc]
  have hzx_comm_yx : ⁅z, x⁆ * ⁅y, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    -- both lie in the centre of H, hence commute
    have h1 : ⁅z, x⁆ ∈ centerIn H := by
      exact (hH (Subgroup.commutator_mem_commutator hz hx))
    have h2 : ⁅y, x⁆ ∈ centerIn H := by
      exact (hH (Subgroup.commutator_mem_commutator hy hx))
    -- centre of H is Abelian: both elements centralise H, so each commutes with the other
    have hyxS : ⁅y, x⁆ ∈ H := (inf_le_left : centerIn H ≤ H) h2
    have hyxC : ⁅y, x⁆ ∈ Subgroup.centralizer (H : Set G) :=
      (inf_le_right : centerIn H ≤ Subgroup.centralizer (H : Set G)) h2
    have hzxS : ⁅z, x⁆ ∈ H := (inf_le_left : centerIn H ≤ H) h1
    exact (Subgroup.mem_centralizer_iff.mp hyxC) ⁅z, x⁆ hzxS
  constructor
  · rw [commutatorElement_mul_right_eq_mul_conj]
    calc
      ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by simp [mul_assoc]
      _ = ⁅x, y⁆ * ⁅x, z⁆ := by rw [hcomm_yz]
  · rw [commutatorElement_mul_left_eq_conj_mul]
    rw [hcomm_yzx]
    rw [hzx_comm_yx]

/-- Lemma 4.1(d): `[X,Y] = [Y,X]` for subgroups. -/
public lemma lemma4_1d (X Y : Subgroup G) : ⁅X, Y⁆ = ⁅Y, X⁆ :=
  Subgroup.commutator_comm X Y

/-- Lemma 4.1(e): the Three Subgroups Lemma: `[X,Y,Z] = [Y,Z,X] = 1` implies
`[Z,X,Y] = 1`. -/
public lemma lemma4_1e (X Y Z : Subgroup G)
    (h1 : ⁅⁅X, Y⁆, Z⁆ = ⊥) (h2 : ⁅⁅Y, Z⁆, X⁆ = ⊥) :
    ⁅⁅Z, X⁆, Y⁆ = ⊥ := by
  exact Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Z) (H₂ := X) (H₃ := Y)
    (by simpa [Subgroup.commutator_comm] using h1)
    (by simpa [Subgroup.commutator_comm] using h2)

/-! ## Element-level helpers for the Case-2 computation (paper L849–L899) -/

/-- `[u⁻¹,x] = [u,x]⁻¹` when `[u,x]` is central in `S`. -/
public lemma commutatorElement_inv_left_of_central {S : Subgroup G} (u x : G)
    (hu : u ∈ S) (_hx : x ∈ S) (h : ⁅u, x⁆ ∈ centerIn S) :
    ⁅u⁻¹, x⁆ = ⁅u, x⁆⁻¹ := by
  calc
    ⁅u⁻¹, x⁆ = u⁻¹ * ⁅x, u⁆ * u := by rw [commutatorElement_inv_left]
    _ = ⁅x, u⁆ := by
      have hz : ⁅x, u⁆ ∈ centerIn S := by
        simpa [commutatorElement_inv] using (centerIn S).inv_mem h
      have hzC : ⁅x, u⁆ ∈ Subgroup.centralizer (S : Set G) :=
        (inf_le_right : centerIn S ≤ Subgroup.centralizer (S : Set G)) hz
      have hcomm : ⁅x, u⁆ * u = u * ⁅x, u⁆ :=
        ((Subgroup.mem_centralizer_iff.mp hzC) u hu).symm
      calc
        u⁻¹ * ⁅x, u⁆ * u = u⁻¹ * (⁅x, u⁆ * u) := by simp [mul_assoc]
        _ = u⁻¹ * (u * ⁅x, u⁆) := by rw [hcomm]
        _ = ⁅x, u⁆ := by simp
    _ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_inv]

/-- `[u,x⁻¹] = [u⁻¹,x⁻¹]⁻¹` when `[u,x]` is central in `S` (the form used at (4.9)). -/
public lemma commutatorElement_inv_right_of_central {S : Subgroup G} (u x : G)
    (hu : u ∈ S) (hx : x ∈ S) (h : ⁅u, x⁆ ∈ centerIn S) :
    ⁅u, x⁻¹⁆ = ⁅u⁻¹, x⁻¹⁆⁻¹ := by
  calc
    ⁅u, x⁻¹⁆ = x⁻¹ * ⁅x, u⁆ * x := by rw [commutatorElement_inv_right]
    _ = x⁻¹ * ⁅u⁻¹, x⁆ * x := by
      have h' : ⁅x, u⁆ = ⁅u⁻¹, x⁆ := by
        calc
          ⁅x, u⁆ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_inv]
          _ = ⁅u⁻¹, x⁆ := (commutatorElement_inv_left_of_central (S := S) u x hu hx h).symm
      rw [h']
    _ = ⁅x⁻¹, u⁻¹⁆ := by
      conv_rhs => rw [commutatorElement_inv_left]
    _ = ⁅u⁻¹, x⁻¹⁆⁻¹ := by rw [commutatorElement_inv]

/-- `[u·v,w] = [u,w]` when `v` is central in `S` (used to drop the `B'`-remainder
inside a commutator). -/
public lemma commutatorElement_mul_left_of_central {S : Subgroup G} (u v w : G)
    (_hu : u ∈ S) (hv : v ∈ centerIn S) (hw : w ∈ S) :
    ⁅u * v, w⁆ = ⁅u, w⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hv' : ⁅v, w⁆ = 1 := by
    have hvc : v ∈ Subgroup.centralizer (S : Set G) :=
      (inf_le_right : centerIn S ≤ Subgroup.centralizer (S : Set G)) hv
    exact
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hvc) w hw).symm
  have hconj : u * ⁅v, w⁆ * u⁻¹ = 1 := by rw [hv']; simp
  rw [hconj]
  simp

/-- Lemma 3.2(b) of the paper, in the right convention: for `A` Abelian with
`[x,A]` Abelian (here the generators `⁅x⁻¹,a⁻¹⁆` commute pairwise), one has
`[x,a,b] = [x,b,a]`, i.e. `⁅⁅a⁻¹,x⁻¹⁆,b⁻¹⁆ = ⁅⁅b⁻¹,x⁻¹⁆,a⁻¹⁆`. -/
public lemma lemma3_2b_right (x a b : G) (hab : Commute a b)
    (hx : Commute ⁅x⁻¹, a⁻¹⁆ ⁅x⁻¹, b⁻¹⁆) :
    ⁅⁅a⁻¹, x⁻¹⁆, b⁻¹⁆ = ⁅⁅b⁻¹, x⁻¹⁆, a⁻¹⁆ := by
  have h1 : ⁅⁅a⁻¹, x⁻¹⁆, b⁻¹⁆ = ⁅a⁻¹, x⁻¹⁆ * ⁅b⁻¹, x⁻¹⁆ * ⁅x⁻¹, b⁻¹ * a⁻¹⁆ := by
    simp [commutatorElement_def, mul_assoc]
  have h2 : ⁅⁅b⁻¹, x⁻¹⁆, a⁻¹⁆ = ⁅b⁻¹, x⁻¹⁆ * ⁅a⁻¹, x⁻¹⁆ * ⁅x⁻¹, a⁻¹ * b⁻¹⁆ := by
    simp [commutatorElement_def, mul_assoc]
  have hba : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
    simpa [mul_assoc] using congrArg (fun t : G => t⁻¹) hab
  rw [h1, h2, hba]
  have hx' : Commute ⁅a⁻¹, x⁻¹⁆ ⁅b⁻¹, x⁻¹⁆ := by
    have h1' : ⁅a⁻¹, x⁻¹⁆ = ⁅x⁻¹, a⁻¹⁆⁻¹ := by simp [commutatorElement_inv]
    have h2' : ⁅b⁻¹, x⁻¹⁆ = ⁅x⁻¹, b⁻¹⁆⁻¹ := by simp [commutatorElement_inv]
    change ⁅a⁻¹, x⁻¹⁆ * ⁅b⁻¹, x⁻¹⁆ = ⁅b⁻¹, x⁻¹⁆ * ⁅a⁻¹, x⁻¹⁆
    rw [h1', h2']
    calc
      ⁅x⁻¹, a⁻¹⁆⁻¹ * ⁅x⁻¹, b⁻¹⁆⁻¹ = (⁅x⁻¹, b⁻¹⁆ * ⁅x⁻¹, a⁻¹⁆)⁻¹ := by rw [mul_inv_rev]
      _ = (⁅x⁻¹, a⁻¹⁆ * ⁅x⁻¹, b⁻¹⁆)⁻¹ := by rw [hx]
      _ = ⁅x⁻¹, b⁻¹⁆⁻¹ * ⁅x⁻¹, a⁻¹⁆⁻¹ := by rw [mul_inv_rev]
  rw [hx'.eq]

/-- From the Hall-Witt identity plus `A₁ = ⁅⁅b⁻¹,x⁻¹⁆,w⁻¹⁆` central in `S` and
`A₃ = ⁅⁅x,w⁻¹⁆,b⁆ = 1`, one gets `A₂ = ⁅⁅b,w⁆⁻¹,x⁻¹⁆ = A₁⁻¹` (paper (4.9), L852–L861). -/
public lemma hallWitt_A2_eq_A1_inv {S : Subgroup G} (x b w : G)
    (hbS : b ∈ S) (hwS : w ∈ S) (_hxS : x ∈ S)
    (hA1 : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ ∈ centerIn S)
    (hA3 : ⁅⁅x, w⁻¹⁆, b⁆ = 1) :
    ⁅⁅b, w⁆⁻¹, x⁻¹⁆ = ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ := by
  have hA1c : ∀ g : G, g ∈ S → g * ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ = ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * g := by
    intro g hg
    have hA1C : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ ∈ Subgroup.centralizer (S : Set G) :=
      (inf_le_right : centerIn S ≤ Subgroup.centralizer (S : Set G)) hA1
    exact (Subgroup.mem_centralizer_iff.mp hA1C) g hg
  have hHW :
      b * ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * b⁻¹ *
        (w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w) * (x⁻¹ * ⁅⁅x, w⁻¹⁆, b⁆ * x) = 1 := by
    simp [commutatorElement_def, mul_assoc]
  have hT1 : b * ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * b⁻¹ = ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ := by
    rw [hA1c b hbS]
    simp [mul_assoc]
  have hT3 : x⁻¹ * ⁅⁅x, w⁻¹⁆, b⁆ * x = 1 := by
    rw [hA3]
    simp
  have h : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * (w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w) * 1 = 1 := by
    simpa [hT1, hT3, mul_assoc] using hHW
  have h' : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * (w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w) = 1 := by simpa using h
  have hA1X : w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w = (⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆)⁻¹ := by
    -- A₁ * X = 1, so X = A₁⁻¹
    calc
      w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w =
          (⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆)⁻¹ * (⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆ * (w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w)) := by
            group
      _ = (⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆)⁻¹ * 1 := by rw [h']
      _ = (⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆)⁻¹ := by simp
  have hA1ic : ∀ g : G, g ∈ S → g * ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ = ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ * g := by
    intro g hg
    have hA1i : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ ∈ centerIn S := (centerIn S).inv_mem hA1
    have hA1iC : ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ ∈ Subgroup.centralizer (S : Set G) :=
      (inf_le_right : centerIn S ≤ Subgroup.centralizer (S : Set G)) hA1i
    exact (Subgroup.mem_centralizer_iff.mp hA1iC) g hg
  calc
    ⁅⁅b, w⁆⁻¹, x⁻¹⁆ = w * (w⁻¹ * ⁅⁅b, w⁆⁻¹, x⁻¹⁆ * w) * w⁻¹ := by
      simp [mul_assoc]
    _ = w * ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ * w⁻¹ := by rw [hA1X]
    _ = ⁅⁅b⁻¹, x⁻¹⁆, w⁻¹⁆⁻¹ := by
      rw [hA1ic w hwS]
      simp [mul_assoc]

/-- The commutator `⁅X, Y ⊔ Z⁆` lies in `K` if `[X,Y]`, `[X,Z]` do and `K` is
invariant under conjugation by `Y` and `Z`.  Mirror of `comm_join_left_le`. -/
public lemma comm_join_right_le {X Y Z K : Subgroup G}
    (hXY : ⁅X, Y⁆ ≤ K) (hXZ : ⁅X, Z⁆ ≤ K)
    (hconjY : ∀ y ∈ Y, ∀ w ∈ K, y * w * y⁻¹ ∈ K)
    (hconjZ : ∀ z ∈ Z, ∀ w ∈ K, z * w * z⁻¹ ∈ K) :
    ⁅X, Y ⊔ Z⁆ ≤ K := by
  apply Subgroup.commutator_le.mpr
  intro x hx g hg
  -- g ∈ Y ⊔ Z = closure (Y ∪ Z)
  have hg' : g ∈ Subgroup.closure ((Y : Set G) ∪ (Z : Set G)) := by
    simpa [Subgroup.sup_eq_closure] using hg
  have hmain : ⁅x, g⁆ ∈ K ∧ (∀ w ∈ K, g * w * g⁻¹ ∈ K) ∧ (∀ w ∈ K, g⁻¹ * w * g ∈ K) := by
    exact Subgroup.closure_induction (k := (Y : Set G) ∪ (Z : Set G))
      (p := fun t _ht => ⁅x, t⁆ ∈ K ∧ (∀ w ∈ K, t * w * t⁻¹ ∈ K) ∧ (∀ w ∈ K, t⁻¹ * w * t ∈ K))
      (by
        intro t ht
        rcases ht with htY | htZ
        · constructor
          · exact hXY (Subgroup.commutator_mem_commutator hx htY)
          · constructor
            · intro w hw
              exact hconjY t htY w hw
            · intro w hw
              have htY' : t⁻¹ ∈ Y := Y.inv_mem htY
              simpa [inv_inv] using hconjY t⁻¹ htY' w hw
        · constructor
          · exact hXZ (Subgroup.commutator_mem_commutator hx htZ)
          · constructor
            · intro w hw
              exact hconjZ t htZ w hw
            · intro w hw
              have htZ' : t⁻¹ ∈ Z := Z.inv_mem htZ
              simpa [inv_inv] using hconjZ t⁻¹ htZ' w hw)
      (by
        constructor
        · simp
        · constructor <;> intro w hw <;> simp [hw])
      (by
        intro a b _ha _hb ha hb
        constructor
        · have hb1 : ⁅x, b⁆ ∈ K := hb.1
          have ha_conj : a * ⁅x, b⁆ * a⁻¹ ∈ K := ha.2.1 ⁅x, b⁆ hb1
          have hcomm : ⁅a, ⁅x, b⁆⁆ ∈ K := by
            have : ⁅a, ⁅x, b⁆⁆ = a * ⁅x, b⁆ * a⁻¹ * (⁅x, b⁆)⁻¹ := by
              simp [commutatorElement_def, mul_assoc]
            rw [this]
            exact K.mul_mem ha_conj (K.inv_mem hb1)
          have heq : ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅a, ⁅x, b⁆⁆ * ⁅x, b⁆ := by
            simp [commutatorElement_def, mul_assoc]
          rw [heq]
          exact K.mul_mem (K.mul_mem ha.1 hcomm) hb1
        · constructor
          · intro w hw
            have heq : (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by
              simp [mul_assoc]
            rw [heq]
            exact ha.2.1 (b * w * b⁻¹) (hb.2.1 w hw)
          · intro w hw
            have heq : (a * b)⁻¹ * w * (a * b) = b⁻¹ * (a⁻¹ * w * a) * b := by
              simp [mul_assoc]
            rw [heq]
            exact hb.2.2 (a⁻¹ * w * a) (ha.2.2 w hw))
      (by
        intro a _ha ha
        constructor
        · have ha1 : ⁅x, a⁆ ∈ K := ha.1
          have hax : ⁅a, x⁆ ∈ K := by
            have : ⁅a, x⁆ = (⁅x, a⁆)⁻¹ := by rw [commutatorElement_inv]
            rw [this]
            exact K.inv_mem ha1
          have hconj : a⁻¹ * ⁅a, x⁆ * a ∈ K := ha.2.2 ⁅a, x⁆ hax
          rw [commutatorElement_inv_right]
          exact hconj
        · constructor
          · intro w hw
            simpa [inv_inv] using ha.2.2 w hw
          · intro w hw
            simpa [inv_inv] using ha.2.1 w hw)
      hg'
  exact hmain.1

/-- The commutator `⁅X ⊔ Y, Z⁆` lies in `K` if `[X,Z]`, `[Y,Z]` do and `K` is
invariant under conjugation by `X` and `Y`.  Proved by induction over the join with
a strengthened predicate (each generator's commutator is in `K` and conjugation by the
generator preserves `K`). -/
public lemma comm_join_left_le {X Y Z K : Subgroup G}
    (hXZ : ⁅X, Z⁆ ≤ K) (hYZ : ⁅Y, Z⁆ ≤ K)
    (hconjX : ∀ x ∈ X, ∀ w ∈ K, x * w * x⁻¹ ∈ K)
    (hconjY : ∀ y ∈ Y, ∀ w ∈ K, y * w * y⁻¹ ∈ K) :
    ⁅X ⊔ Y, Z⁆ ≤ K := by
  apply Subgroup.commutator_le.mpr
  intro g hg z hz
  -- g ∈ X ⊔ Y = closure (X ∪ Y)
  have hg' : g ∈ Subgroup.closure ((X : Set G) ∪ (Y : Set G)) := by
    simpa [Subgroup.sup_eq_closure] using hg
  have hmain : ⁅g, z⁆ ∈ K ∧ (∀ w ∈ K, g * w * g⁻¹ ∈ K) ∧ (∀ w ∈ K, g⁻¹ * w * g ∈ K) := by
    exact Subgroup.closure_induction (k := (X : Set G) ∪ (Y : Set G))
      (p := fun t _ht => ⁅t, z⁆ ∈ K ∧ (∀ w ∈ K, t * w * t⁻¹ ∈ K) ∧ (∀ w ∈ K, t⁻¹ * w * t ∈ K))
      (by
        intro t ht
        rcases ht with htX | htY
        · constructor
          · exact hXZ (Subgroup.commutator_mem_commutator htX hz)
          · constructor
            · intro w hw
              exact hconjX t htX w hw
            · intro w hw
              have htX' : t⁻¹ ∈ X := X.inv_mem htX
              simpa [inv_inv] using hconjX t⁻¹ htX' w hw
        · constructor
          · exact hYZ (Subgroup.commutator_mem_commutator htY hz)
          · constructor
            · intro w hw
              exact hconjY t htY w hw
            · intro w hw
              have htY' : t⁻¹ ∈ Y := Y.inv_mem htY
              simpa [inv_inv] using hconjY t⁻¹ htY' w hw)
      (by
        constructor
        · simp
        · constructor <;> intro w hw <;> simp [hw])
      (by
        intro a b _ha _hb ha hb
        constructor
        · -- ⁅a·b, z⁆ = ⁅a,⁅b,z⁆⁆ · ⁅b,z⁆ · ⁅a,z⁆ ∈ K
          have hb1 : ⁅b, z⁆ ∈ K := hb.1
          have ha_conj : a * ⁅b, z⁆ * a⁻¹ ∈ K := ha.2.1 ⁅b, z⁆ hb1
          have hcomm : ⁅a, ⁅b, z⁆⁆ ∈ K := by
            have : ⁅a, ⁅b, z⁆⁆ = a * ⁅b, z⁆ * a⁻¹ * (⁅b, z⁆)⁻¹ := by
              simp [commutatorElement_def, mul_assoc]
            rw [this]
            exact K.mul_mem ha_conj (K.inv_mem hb1)
          have heq : ⁅a * b, z⁆ = ⁅a, ⁅b, z⁆⁆ * ⁅b, z⁆ * ⁅a, z⁆ := by
            simp [commutatorElement_def, mul_assoc]
          rw [heq]
          exact K.mul_mem (K.mul_mem hcomm hb1) ha.1
        · constructor
          · intro w hw
            have heq : (a * b) * w * (a * b)⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by
              simp [mul_assoc]
            rw [heq]
            exact ha.2.1 (b * w * b⁻¹) (hb.2.1 w hw)
          · intro w hw
            have heq : (a * b)⁻¹ * w * (a * b) = b⁻¹ * (a⁻¹ * w * a) * b := by
              simp [mul_assoc]
            rw [heq]
            exact hb.2.2 (a⁻¹ * w * a) (ha.2.2 w hw))
      (by
        intro a _ha ha
        constructor
        · -- ⁅a⁻¹,z⁆ = a⁻¹·⁅z,a⁆·a ∈ K
          have ha1 : ⁅a, z⁆ ∈ K := ha.1
          have hza : ⁅z, a⁆ ∈ K := by
            have : ⁅z, a⁆ = (⁅a, z⁆)⁻¹ := by rw [commutatorElement_inv]
            rw [this]
            exact K.inv_mem ha1
          have hconj : a⁻¹ * ⁅z, a⁆ * a ∈ K := ha.2.2 ⁅z, a⁆ hza
          rw [commutatorElement_inv_left]
          exact hconj
        · constructor
          · intro w hw
            simpa [inv_inv] using ha.2.2 w hw
          · intro w hw
            simpa [inv_inv] using ha.2.1 w hw)
      hg'
  exact hmain.1

/-- `[S_i, S_j] ⊆ S_{i+j+1}` for the mapped lower central series (Hall, Cor. 10.3.5). -/
public lemma lcs_commutator_le (S : Subgroup G) (i j : ℕ) :
    ⁅lcs S i, lcs S j⁆ ≤ lcs S (i + j + 1) := by
  unfold lcs
  rw [← Subgroup.map_commutator]
  apply Subgroup.map_mono
  exact lowerCentralSeries_commutator_le (G := ↥S) i j

/-- The paper's `[x,A]`: the subgroup generated by `⁅x,a⁆` for `a ∈ A`. -/
public def commSub (x : G) (A : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | ∃ a ∈ A, ⁅x, a⁆ = g}

/-- A subgroup of an Abelian subgroup is Abelian. -/
public lemma isMulCommutative_of_le {H K : Subgroup G} (h : H ≤ K)
    (hK : IsMulCommutative K) : IsMulCommutative H := by
  refine IsMulCommutative.of_setLike_mul_comm ?_
  intro y hy z hz
  exact setLike_mul_comm (s := K) (h hy) (h hz)

/-- `[H,K] ≤ H` whenever `K` normalises `H`. -/
public lemma commutator_le_left_of_normalizer {H K : Subgroup G}
    (hK_norm_H : K ≤ Subgroup.normalizer (H : Set G)) : ⁅H, K⁆ ≤ H :=
  (Subgroup.le_normalizer_iff_commutator_le_left (H := K) (K := H)).1 hK_norm_H

/-- `[B,A] ⊆ B` (from `B ⊴ P` and `A ≤ P`). -/
public lemma commutator_B_A_le_B {P A B : Subgroup G} (hA : A ≤ P) (hB_le_P : B ≤ P)
    (hB_normal : (B.subgroupOf P).Normal) : ⁅B, A⁆ ≤ B := by
  have hP_norm_B : P ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_P).1 hB_normal
  exact commutator_le_left_of_normalizer (H := B) (K := A) (hA.trans hP_norm_B)

/-- `⁅x,a⁆ ∈ [x,A]` for `a ∈ A`. -/
public lemma commSub_mem (x : G) (A : Subgroup G) {a : G} (ha : a ∈ A) :
    ⁅x, a⁆ ∈ commSub x A := by
  exact Subgroup.subset_closure ⟨a, ha, rfl⟩

/-- `[x,A] ⊆ [B,A]` when `x ∈ B`. -/
public lemma commSub_le_commutator (x : G) (B A : Subgroup G) (hxB : x ∈ B) :
    commSub x A ≤ ⁅B, A⁆ := by
  rw [commSub]
  exact (Subgroup.closure_le (⁅B, A⁆)).2 (by
    intro g hg
    rcases hg with ⟨a, ha, rfl⟩
    exact Subgroup.commutator_mem_commutator hxB ha)

/-- Conjugation invariance of `commChain B A j ⊔ ⁅B,B⁆` under elements of `A ∪ B`,
given `[B,B] ⊆ Z(S₀)`, `A ≤ N(B)`, and `A` normalises each chain term. -/
public lemma conj_inv_chainB' {S₀ A B : Subgroup G} (j : ℕ)
    (hB'Z : ⁅B, B⁆ ≤ centerIn S₀) (_hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hA_chain : ∀ j, ⁅A, commChain B A j⁆ ≤ commChain B A j)
    (hchain_le_B : ∀ j, commChain B A j ≤ B)
    (hA_le_S0 : A ≤ S₀) (hB_le_S0 : B ≤ S₀)
    {t : G} (ht : t ∈ (A : Set G) ∪ (B : Set G)) :
    ∀ w ∈ commChain B A j ⊔ ⁅B, B⁆, t * w * t⁻¹ ∈ commChain B A j ⊔ ⁅B, B⁆ := by
  rcases ht with htA | htB
  · -- t ∈ A
    have hcentral : ∀ β ∈ ⁅B, B⁆, β * t = t * β := by
      intro β hβ
      have hβC : β ∈ Subgroup.centralizer (S₀ : Set G) :=
        (inf_le_right : centerIn S₀ ≤ Subgroup.centralizer (S₀ : Set G)) (hB'Z hβ)
      exact ((Subgroup.mem_centralizer_iff.mp hβC) t (hA_le_S0 htA)).symm
    have hmemA : ∀ w ∈ commChain B A j, t * w * t⁻¹ ∈ commChain B A j := by
      intro w hw
      have h : ⁅t, w⁆ ∈ commChain B A j := hA_chain j (Subgroup.commutator_mem_commutator htA hw)
      have heq : t * w * t⁻¹ = ⁅t, w⁆ * w := by simp [commutatorElement_def, mul_assoc]
      rw [heq]
      exact (commChain B A j).mul_mem h hw
    intro w hw
    have hw' : w ∈ Subgroup.closure (((commChain B A j : Set G) ∪ ((⁅B, B⁆ : Subgroup G) : Set G))) := by
      simpa [Subgroup.sup_eq_closure] using hw
    refine Subgroup.closure_induction (k := (commChain B A j : Set G) ∪ ((⁅B, B⁆ : Subgroup G) : Set G))
      (p := fun z _hz => t * z * t⁻¹ ∈ commChain B A j ⊔ ⁅B, B⁆) ?_ ?_ ?_ ?_ hw'
    · intro z hz
      rcases hz with hzCh | hzB'
      · exact Subgroup.mem_sup_left (hmemA z hzCh)
      · have heq : t * z * t⁻¹ = z := by
          calc
            t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [hcentral z hzB']
            _ = z := by simp [mul_assoc]
        rw [heq]
        exact Subgroup.mem_sup_right hzB'
    · simp
    · intro a b _ha _hb ha hb
      have heq : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by simp [mul_assoc]
      rw [heq]
      exact (commChain B A j ⊔ ⁅B, B⁆).mul_mem ha hb
    · intro a _ha ha
      have heq : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact (commChain B A j ⊔ ⁅B, B⁆).inv_mem ha
  · -- t ∈ B
    have hcentral : ∀ β ∈ ⁅B, B⁆, β * t = t * β := by
      intro β hβ
      have hβC : β ∈ Subgroup.centralizer (S₀ : Set G) :=
        (inf_le_right : centerIn S₀ ≤ Subgroup.centralizer (S₀ : Set G)) (hB'Z hβ)
      exact ((Subgroup.mem_centralizer_iff.mp hβC) t (hB_le_S0 htB)).symm
    have hmemB : ∀ w ∈ commChain B A j, t * w * t⁻¹ ∈ commChain B A j ⊔ ⁅B, B⁆ := by
      intro w hw
      have h : ⁅t, w⁆ ∈ ⁅B, B⁆ := Subgroup.commutator_mem_commutator htB (hchain_le_B j hw)
      have heq : t * w * t⁻¹ = ⁅t, w⁆ * w := by simp [commutatorElement_def, mul_assoc]
      rw [heq]
      exact (commChain B A j ⊔ ⁅B, B⁆).mul_mem (Subgroup.mem_sup_right h) (Subgroup.mem_sup_left hw)
    intro w hw
    have hw' : w ∈ Subgroup.closure (((commChain B A j : Set G) ∪ ((⁅B, B⁆ : Subgroup G) : Set G))) := by
      simpa [Subgroup.sup_eq_closure] using hw
    refine Subgroup.closure_induction (k := (commChain B A j : Set G) ∪ ((⁅B, B⁆ : Subgroup G) : Set G))
      (p := fun z _hz => t * z * t⁻¹ ∈ commChain B A j ⊔ ⁅B, B⁆) ?_ ?_ ?_ ?_ hw'
    · intro z hz
      rcases hz with hzCh | hzB'
      · exact hmemB z hzCh
      · have heq : t * z * t⁻¹ = z := by
          calc
            t * z * t⁻¹ = (z * t) * t⁻¹ := by rw [hcentral z hzB']
            _ = z := by simp [mul_assoc]
        rw [heq]
        exact Subgroup.mem_sup_right hzB'
    · simp
    · intro a b _ha _hb ha hb
      have heq : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by simp [mul_assoc]
      rw [heq]
      exact (commChain B A j ⊔ ⁅B, B⁆).mul_mem ha hb
    · intro a _ha ha
      have heq : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by simp [mul_assoc]
      rw [heq]
      exact (commChain B A j ⊔ ⁅B, B⁆).inv_mem ha

/-! ## Theorem 4.1 (paper L781–L917) and Corollary 4.1 (L919–L925)

The proof follows the paper: (4.1) `A ∩ B` centralises `[B,A]` by the Three
Subgroups Lemma; the chain `[B,A;n]` is eventually trivial and eventually
Abelian; Case 1 (`[B,A;n+1] ≠ 1`) constructs `A* = [x,A]·C_A([x,A])` via the
Replacement Theorem `theorem3_1a`; Case 2 (`[B,A;n+1] = 1`) works in
`S₀ = A ⊔ B` with `B′ = ⁅B,B⁆ ⊆ Z(S₀)` (from `[B,B] ⊆ Z(B) ∩ Z(J(S))`),
proves (4.5)–(4.8) (the congruence of the lower central series of `S₀` with
the chain modulo `B′`, `S_{n+3} = 1`, `[B,A;3] = 1`), and in the odd-prime
subcase (`p ≠ 2` and `[B,A;2] ≠ 1`) uses the P. Hall identity to show
`[x,A]` Abelian (`hallWitt_commute` below, with its element-level congruence
helper `hallWitt_congruence_mod_B'`) — and then repeats the Case-1
construction.

The paper's commutator convention is left-normed `[x,y] = x⁻¹y⁻¹xy`; Mathlib's
`⁅x,y⁆ = x·y·x⁻¹·y⁻¹` is the right convention, and the paper's `[x,y]`
corresponds to `⁅x⁻¹,y⁻¹⁆` (subgroup-level statements are convention-independent).
-/

/-- The paper's congruence `[x,c,b] ≡ [x,b,c] (mod B′)`, L889–L891, at the element
level: for `u ∈ B` and `p, q ∈ A`, the commutators `⁅⁅q,u⁆,p⁆` and `⁅⁅p,u⁆,q⁆`
differ by an element of `B′ = ⁅B,B⁆`.  This is Lemma 3.2(b) of the paper carried
out modulo `B′` (its hypothesis that `[x,A]` is Abelian holds modulo `B′` since
`[B,A] ⊆ B` and `B/B′` is Abelian). -/
private lemma hallWitt_congruence_mod_B' {S0 A B : Subgroup G} (u p q : G)
    (huB : u ∈ B) (hpA : p ∈ A) (hqA : q ∈ A)
    (hA_comm : IsMulCommutative A)
    (hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hB'Z : ⁅B, B⁆ ≤ centerIn S0)
    (_hA_le_S0 : A ≤ S0) (hB_le_S0 : B ≤ S0) :
    ⁅⁅q, u⁆, p⁆ * (⁅⁅p, u⁆, q⁆)⁻¹ ∈ ⁅B, B⁆ := by
  classical
  let z : G := ⁅u, q⁆
  let z' : G := ⁅u, p⁆
  have hBA_le_B : ⁅B, A⁆ ≤ B :=
    commutator_le_left_of_normalizer (H := B) (K := A) hB_norm
  have hzB : z ∈ B := by
    dsimp [z]
    exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hqA))
  have hz'B : z' ∈ B := by
    dsimp [z']
    exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hpA))
  have hzS0 : z ∈ S0 := hB_le_S0 hzB
  have hz'S0 : z' ∈ S0 := hB_le_S0 hz'B
  have hzz'S0 : z * z' ∈ S0 := S0.mul_mem hzS0 hz'S0
  -- A is Abelian, so p and q commute
  have hpq : p * q = q * p := by
    have hcentA : A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA_comm
    have hpC : p ∈ Subgroup.centralizer (A : Set G) := hcentA hpA
    exact ((Subgroup.mem_centralizer_iff.mp hpC) q hqA).symm
  have hEq : ⁅u, p * q⁆ = ⁅u, q * p⁆ := by
    simp [hpq]
  have hExp1 : ⁅u, p * q⁆ = z' * p * z * p⁻¹ := by
    dsimp [z, z']
    rw [commutatorElement_mul_right_eq_mul_conj]
  have hExp2 : ⁅u, q * p⁆ = z * q * z' * q⁻¹ := by
    dsimp [z, z']
    rw [commutatorElement_mul_right_eq_mul_conj]
  have hI3a : p * z * p⁻¹ = z * ⁅z⁻¹, p⁆ := by
    simp [commutatorElement_def, mul_assoc]
  have hI3b : q * z' * q⁻¹ = z' * ⁅z'⁻¹, q⁆ := by
    simp [commutatorElement_def, mul_assoc]
  have hMain : z' * z * ⁅z⁻¹, p⁆ = z * z' * ⁅z'⁻¹, q⁆ := by
    calc
      z' * z * ⁅z⁻¹, p⁆ = z' * (z * ⁅z⁻¹, p⁆) := by simp [mul_assoc]
      _ = z' * (p * z * p⁻¹) := by rw [← hI3a]
      _ = z' * p * z * p⁻¹ := by simp [mul_assoc]
      _ = ⁅u, p * q⁆ := hExp1.symm
      _ = ⁅u, q * p⁆ := hEq
      _ = z * q * z' * q⁻¹ := hExp2
      _ = z * (q * z' * q⁻¹) := by simp [mul_assoc]
      _ = z * (z' * ⁅z'⁻¹, q⁆) := by rw [hI3b]
      _ = z * z' * ⁅z'⁻¹, q⁆ := by simp [mul_assoc]
  have hI4 : ⁅z', z⁆ * z * z' = z' * z := by
    simp [commutatorElement_def, mul_assoc]
  have hγB' : ⁅z', z⁆ ∈ ⁅B, B⁆ :=
    Subgroup.commutator_mem_commutator (h₁ := hz'B) (h₂ := hzB)
  have hγ_cent : ⁅z', z⁆ ∈ centerIn S0 := hB'Z hγB'
  have hγC : ⁅z', z⁆ ∈ Subgroup.centralizer (S0 : Set G) :=
    (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hγ_cent
  have hγ_comm : (z * z') * ⁅z', z⁆ = ⁅z', z⁆ * (z * z') :=
    (Subgroup.mem_centralizer_iff.mp hγC) (z * z') hzz'S0
  have hMain2 : ⁅z', z⁆ * (z * z') * ⁅z⁻¹, p⁆ = (z * z') * ⁅z'⁻¹, q⁆ := by
    calc
      ⁅z', z⁆ * (z * z') * ⁅z⁻¹, p⁆ = (⁅z', z⁆ * z * z') * ⁅z⁻¹, p⁆ := by
        simp [mul_assoc]
      _ = z' * z * ⁅z⁻¹, p⁆ := by rw [hI4]
      _ = z * z' * ⁅z'⁻¹, q⁆ := hMain
      _ = (z * z') * ⁅z'⁻¹, q⁆ := by simp [mul_assoc]
  have hγT3 : ⁅z', z⁆ * ⁅z⁻¹, p⁆ = ⁅z'⁻¹, q⁆ := by
    calc
      ⁅z', z⁆ * ⁅z⁻¹, p⁆ = (z * z')⁻¹ * (⁅z', z⁆ * (z * z') * ⁅z⁻¹, p⁆) := by
        rw [hγ_comm.symm]
        group
      _ = (z * z')⁻¹ * ((z * z') * ⁅z'⁻¹, q⁆) := by rw [hMain2]
      _ = ⁅z'⁻¹, q⁆ := by simp [mul_assoc]
  have hT3 : ⁅z⁻¹, p⁆ = (⁅z', z⁆)⁻¹ * ⁅z'⁻¹, q⁆ := by
    calc
      ⁅z⁻¹, p⁆ = (⁅z', z⁆)⁻¹ * (⁅z', z⁆ * ⁅z⁻¹, p⁆) := by group
      _ = (⁅z', z⁆)⁻¹ * ⁅z'⁻¹, q⁆ := by rw [hγT3]
  have hT3T4 : ⁅z⁻¹, p⁆ * (⁅z'⁻¹, q⁆)⁻¹ = (⁅z', z⁆)⁻¹ := by
    calc
      ⁅z⁻¹, p⁆ * (⁅z'⁻¹, q⁆)⁻¹ =
          ((⁅z', z⁆)⁻¹ * ⁅z'⁻¹, q⁆) * (⁅z'⁻¹, q⁆)⁻¹ := by rw [hT3]
      _ = (⁅z', z⁆)⁻¹ := by group
  have hT3T4' : ⁅⁅q, u⁆, p⁆ * (⁅⁅p, u⁆, q⁆)⁻¹ = (⁅z', z⁆)⁻¹ := by
    calc
      ⁅⁅q, u⁆, p⁆ * (⁅⁅p, u⁆, q⁆)⁻¹ = ⁅z⁻¹, p⁆ * (⁅z'⁻¹, q⁆)⁻¹ := by
        congr 1
        · rw [show ⁅q, u⁆ = z⁻¹ from by
            dsimp [z]
            rw [commutatorElement_inv]]
        · rw [show ⁅p, u⁆ = z'⁻¹ from by
            dsimp [z']
            rw [commutatorElement_inv]]
      _ = (⁅z', z⁆)⁻¹ := hT3T4
  exact hT3T4' ▸ (⁅B, B⁆).inv_mem hγB'

/-- The P. Hall (Hall–Witt) computation of Case 2, paper L849–L899.

**Statement.**  Let `S₀ ⊇ A ∪ B` with `A` Abelian and `A ≤ N_G(B)`, let
`B′ = ⁅B,B⁆ ⊆ Z(S₀)`, and assume `[B,A;3] = 1` (i.e. `commChain B A 3 = ⊥`).
For `x0 ∈ B` and `b, c ∈ A`, the paper's commutators `[x0,b]` and `[x0,c]`
commute; in Mathlib's right convention (where the paper's `[u,v] = ⁅u⁻¹,v⁻¹⁆`):

    ⁅⁅b⁻¹,x0⁻¹⁆, ⁅x0⁻¹,c⁻¹⁆⁻¹⁆ = 1.

**Proof (paper L849–L899).**  The P. Hall identity (Lemma 4.1(b) here,
`lemma4_1b`) with `y = b⁻¹`, `z = [x0,c]` gives, after dropping the
conjugations (the three displayed commutators lie in `B′ ⊆ Z(S₀)`) and using
`[z,x0⁻¹,b⁻¹] = 1` (its inner commutator lies in `[B,B] = B′`), the identity
(4.9) `[[x0,b],[x0,c]] = [b⁻¹,[x0,c]⁻¹,x0]⁻¹` — this is the landed
`hallWitt_A2_eq_A1_inv`.  The congruence chain of the paper

    [w⁻¹,b⁻¹] ≡ [w,b⁻¹]⁻¹ ≡ [w,b] ≡ [x0,c,b] ≡ [x0,b,c]   (mod B′),

for `w = [x0,c]`, is proved here directly at the element level: the first
congruence is the identity `⁅z,b⁆·(⁅b,z⁻¹⁆)⁻¹ = ⁅⁅z,b⁆,z⁻¹⁆` with the right
hand side in `B′` (both arguments lie in `B`); the middle step is an exact
equality because `⁅b,z⁻¹⁆ ∈ [B,A;2]` and `[B,A;3] = 1`; the last step is
Lemma 3.2(b) carried out modulo `B′` (the lemma `hallWitt_congruence_mod_B'`
above), whose hypothesis that `[x,A]` is Abelian holds modulo `B′` since
`[B,A] ⊆ B` and `B/B′` is Abelian.  Since `B′ ⊆ Z(S₀)` the remainders drop
inside commutators with `u = x0⁻¹`, promoting the congruence to the exact
identity `⁅⁅z,b⁆,u⁆ = ⁅⁅⁅p,u⁆,q⁆,u⁆` (with `p = b⁻¹`, `q = c⁻¹`,
`z = ⁅x0⁻¹,c⁻¹⁆`); by symmetry `⁅⁅z′,c⁆,u⁆ = ⁅⁅⁅q,u⁆,p⁆,u⁆`, and the two
right-hand sides coincide modulo `B′`, hence `G = G⁻¹` for
`G = ⁅⁅p,u⁆,⁅q,u⁆⁆`.  Thus `G² = 1`; as `p` is odd and `S₀` is a `p`-group,
`G = 1` (the landed `eq_one_of_mem_pGroup_sq_eq_one`).

This is used exactly at the point where the paper concludes "[x,A] is Abelian"
in the odd-prime subcase of Case 2; the construction of
`A* = [x,A]·C_A([x,A]) ∈ A(S)` then goes through `theorem3_1a` exactly as in
Case 1. -/
public theorem hallWitt_commute {S0 A B : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hS0p : IsPGroup p S0) (hpodd : p ≠ 2)
    (hA_le_S0 : A ≤ S0) (hB_le_S0 : B ≤ S0)
    (hA_comm : IsMulCommutative A)
    (hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hB'Z : ⁅B, B⁆ ≤ centerIn S0)
    (hchain3 : commChain B A 3 = ⊥)
    (x0 b c : G) (hx0B : x0 ∈ B) (hbA : b ∈ A) (hcA : c ∈ A) :
    ⁅⁅b⁻¹, x0⁻¹⁆, ⁅x0⁻¹, c⁻¹⁆⁻¹⁆ = 1 := by
  classical
  let u : G := x0⁻¹
  let p : G := b⁻¹
  let q : G := c⁻¹
  let z : G := ⁅u, q⁆
  let z' : G := ⁅u, p⁆
  let G0 : G := ⁅⁅p, u⁆, ⁅q, u⁆⁆
  have huB : u ∈ B := by
    dsimp [u]
    exact B.inv_mem hx0B
  have hpA : p ∈ A := by
    dsimp [p]
    exact A.inv_mem hbA
  have hqA : q ∈ A := by
    dsimp [q]
    exact A.inv_mem hcA
  have hbS0 : b ∈ S0 := hA_le_S0 hbA
  have hcS0 : c ∈ S0 := hA_le_S0 hcA
  have huS0 : u ∈ S0 := hB_le_S0 huB
  have hx0S0 : x0 ∈ S0 := hB_le_S0 hx0B
  -- [B,A] ⊆ B
  have hBA_le_B : ⁅B, A⁆ ≤ B :=
    commutator_le_left_of_normalizer (H := B) (K := A) hB_norm
  have hzB : z ∈ B := by
    dsimp [z]
    exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hqA))
  have hz'B : z' ∈ B := by
    dsimp [z']
    exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hpA))
  have hzS0 : z ∈ S0 := hB_le_S0 hzB
  have hz'S0 : z' ∈ S0 := hB_le_S0 hz'B
  have hzinvB : z⁻¹ ∈ B := B.inv_mem hzB
  have hz'invB : z'⁻¹ ∈ B := B.inv_mem hz'B
  have hpuB : ⁅p, u⁆ ∈ B := by
    have hmem : ⁅p, u⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator (h₁ := hpA) (h₂ := huB)
    have hmem' : ⁅p, u⁆ ∈ ⁅B, A⁆ := by simpa [Subgroup.commutator_comm] using hmem
    exact hBA_le_B hmem'
  have hquB : ⁅q, u⁆ ∈ B := by
    have hmem : ⁅q, u⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator (h₁ := hqA) (h₂ := huB)
    have hmem' : ⁅q, u⁆ ∈ ⁅B, A⁆ := by simpa [Subgroup.commutator_comm] using hmem
    exact hBA_le_B hmem'
  have hG0B' : G0 ∈ ⁅B, B⁆ := by
    dsimp [G0]
    exact Subgroup.commutator_mem_commutator (h₁ := hpuB) (h₂ := hquB)
  have hG0_cent : G0 ∈ centerIn S0 := hB'Z hG0B'
  have hG0S0 : G0 ∈ S0 := by
    dsimp [G0]
    exact S0.mul_mem (S0.mul_mem (S0.mul_mem (hB_le_S0 hpuB) (hB_le_S0 hquB))
      (S0.inv_mem (hB_le_S0 hpuB))) (S0.inv_mem (hB_le_S0 hquB))
  -- HW1: ⁅⁅z,b⁆,u⁆ = G0⁻¹
  have hA3 : ⁅⁅x0, z⁻¹⁆, b⁆ = 1 := by
    have hx0z : ⁅x0, z⁻¹⁆ ∈ ⁅B, B⁆ :=
      Subgroup.commutator_mem_commutator (h₁ := hx0B) (h₂ := hzinvB)
    have hx0zC : ⁅x0, z⁻¹⁆ ∈ centerIn S0 := hB'Z hx0z
    have hx0zC' : ⁅x0, z⁻¹⁆ ∈ Subgroup.centralizer (S0 : Set G) :=
      (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hx0zC
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (((Subgroup.mem_centralizer_iff.mp hx0zC') b hbS0).symm)
  have hA1 : ⁅⁅b⁻¹, x0⁻¹⁆, z⁻¹⁆ ∈ centerIn S0 := by
    have h1 : ⁅b⁻¹, x0⁻¹⁆ ∈ B := by simpa [p, u] using hpuB
    exact hB'Z (Subgroup.commutator_mem_commutator (h₁ := h1) (h₂ := hzinvB))
  have hw1' := hallWitt_A2_eq_A1_inv (S := S0) (x := x0) (b := b) (w := z)
    hbS0 hzS0 hx0S0 hA1 hA3
  have hw1 : ⁅⁅z, b⁆, u⁆ = G0⁻¹ := by
    simpa [u, z, G0, p, q, commutatorElement_inv] using hw1'
  -- HW2: ⁅⁅z',c⁆,u⁆ = G0
  have hA3' : ⁅⁅x0, z'⁻¹⁆, c⁆ = 1 := by
    have hx0z : ⁅x0, z'⁻¹⁆ ∈ ⁅B, B⁆ :=
      Subgroup.commutator_mem_commutator (h₁ := hx0B) (h₂ := hz'invB)
    have hx0zC : ⁅x0, z'⁻¹⁆ ∈ centerIn S0 := hB'Z hx0z
    have hx0zC' : ⁅x0, z'⁻¹⁆ ∈ Subgroup.centralizer (S0 : Set G) :=
      (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hx0zC
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (((Subgroup.mem_centralizer_iff.mp hx0zC') c hcS0).symm)
  have hA1' : ⁅⁅c⁻¹, x0⁻¹⁆, z'⁻¹⁆ ∈ centerIn S0 := by
    have h1 : ⁅c⁻¹, x0⁻¹⁆ ∈ B := by simpa [q, u] using hquB
    exact hB'Z (Subgroup.commutator_mem_commutator (h₁ := h1) (h₂ := hz'invB))
  have hw2' := hallWitt_A2_eq_A1_inv (S := S0) (x := x0) (b := c) (w := z')
    hcS0 hz'S0 hx0S0 hA1' hA3'
  have hw2 : ⁅⁅z', c⁆, u⁆ = G0 := by
    simpa [u, z', G0, p, q, commutatorElement_inv] using hw2'
  -- chain 1: ⁅⁅z,b⁆,u⁆ = ⁅⁅⁅p,u⁆,q⁆,u⁆
  have ha : ⁅z, b⁆ * (⁅b, z⁻¹⁆)⁻¹ ∈ ⁅B, B⁆ := by
    have hzbB : ⁅z, b⁆ ∈ B := by
      exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := hzB) (h₂ := hbA))
    have hI1 : ⁅z, b⁆ * (⁅b, z⁻¹⁆)⁻¹ = ⁅⁅z, b⁆, z⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hI1]
    exact Subgroup.commutator_mem_commutator (h₁ := hzbB) (h₂ := hzinvB)
  have hb : ⁅b, z⁻¹⁆ = ⁅z⁻¹, b⁻¹⁆ := by
    have hbz2 : ⁅b, z⁻¹⁆ ∈ commChain B A 2 := by
      have hzBA : z⁻¹ ∈ ⁅B, A⁆ := by
        exact (⁅B, A⁆).inv_mem (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hqA))
      have hmem : ⁅b, z⁻¹⁆ ∈ ⁅A, ⁅B, A⁆⁆ :=
        Subgroup.commutator_mem_commutator (h₁ := hbA) (h₂ := hzBA)
      simpa [commChain_succ, commChain_zero, Subgroup.commutator_comm] using hmem
    have hdiff : ⁅⁅b, z⁻¹⁆, b⁻¹⁆ ∈ commChain B A 3 :=
      Subgroup.commutator_mem_commutator (H₁ := commChain B A 2) (H₂ := A)
        (h₁ := hbz2) (h₂ := A.inv_mem hbA)
    have hdiff1 : ⁅⁅b, z⁻¹⁆, b⁻¹⁆ = 1 := by
      have : ⁅⁅b, z⁻¹⁆, b⁻¹⁆ ∈ (⊥ : Subgroup G) := by
        rw [hchain3] at hdiff
        exact hdiff
      simpa using (Subgroup.mem_bot.mp this)
    have hI2 : ⁅b, z⁻¹⁆ * (⁅z⁻¹, b⁻¹⁆)⁻¹ = ⁅⁅b, z⁻¹⁆, b⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    have hX : ⁅b, z⁻¹⁆ * (⁅z⁻¹, b⁻¹⁆)⁻¹ = 1 := by
      rw [hI2, hdiff1]
    calc
      ⁅b, z⁻¹⁆ = (⁅b, z⁻¹⁆ * (⁅z⁻¹, b⁻¹⁆)⁻¹) * ⁅z⁻¹, b⁻¹⁆ := by group
      _ = ⁅z⁻¹, b⁻¹⁆ := by rw [hX]; simp
  have hc : ⁅z⁻¹, b⁻¹⁆ * (⁅⁅p, u⁆, q⁆)⁻¹ ∈ ⁅B, B⁆ := by
    have hcong := hallWitt_congruence_mod_B' (S0 := S0) u p q huB hpA hqA
      hA_comm hB_norm hB'Z hA_le_S0 hB_le_S0
    -- hcong : ⁅⁅q,u⁆,p⁆ * (⁅⁅p,u⁆,q⁆)⁻¹ ∈ ⁅B,B⁆
    -- ⁅⁅q,u⁆,p⁆ = ⁅z⁻¹,p⁆ = ⁅z⁻¹,b⁻¹⁆
    simpa [p, q, z, commutatorElement_inv] using hcong
  let β₁ : G := ⁅z, b⁆ * (⁅b, z⁻¹⁆)⁻¹
  let β₃ : G := ⁅z⁻¹, b⁻¹⁆ * (⁅⁅p, u⁆, q⁆)⁻¹
  have hβ₁B' : β₁ ∈ ⁅B, B⁆ := ha
  have hβ₃B' : β₃ ∈ ⁅B, B⁆ := hc
  have hδB' : β₁ * β₃ ∈ ⁅B, B⁆ := (⁅B, B⁆).mul_mem hβ₁B' hβ₃B'
  have hδ_cent : β₁ * β₃ ∈ centerIn S0 := hB'Z hδB'
  have hδC : β₁ * β₃ ∈ Subgroup.centralizer (S0 : Set G) :=
    (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hδ_cent
  have hW_S0 : ⁅⁅p, u⁆, q⁆ ∈ S0 := by
    have hpu_S0 : ⁅p, u⁆ ∈ S0 := hB_le_S0 hpuB
    exact S0.mul_mem (S0.mul_mem (S0.mul_mem hpu_S0 (hA_le_S0 hqA)) (S0.inv_mem hpu_S0)) (S0.inv_mem (hA_le_S0 hqA))
  have hδW : (β₁ * β₃) * ⁅⁅p, u⁆, q⁆ = ⁅⁅p, u⁆, q⁆ * (β₁ * β₃) :=
    ((Subgroup.mem_centralizer_iff.mp hδC) (⁅⁅p, u⁆, q⁆) hW_S0).symm
  have hzb : ⁅z, b⁆ = β₁ * β₃ * ⁅⁅p, u⁆, q⁆ := by
    calc
      ⁅z, b⁆ = β₁ * ⁅b, z⁻¹⁆ := by
        dsimp [β₁]
        group
      _ = β₁ * ⁅z⁻¹, b⁻¹⁆ := by rw [hb]
      _ = β₁ * (β₃ * ⁅⁅p, u⁆, q⁆) := by
        congr 1
        dsimp [β₃]
        group
      _ = β₁ * β₃ * ⁅⁅p, u⁆, q⁆ := by simp [mul_assoc]
  have hchain1 : ⁅⁅z, b⁆, u⁆ = ⁅⁅⁅p, u⁆, q⁆, u⁆ := by
    calc
      ⁅⁅z, b⁆, u⁆ = ⁅β₁ * β₃ * ⁅⁅p, u⁆, q⁆, u⁆ := by rw [hzb]
      _ = ⁅⁅⁅p, u⁆, q⁆, u⁆ := by
        rw [show (β₁ * β₃) * ⁅⁅p, u⁆, q⁆ = ⁅⁅p, u⁆, q⁆ * (β₁ * β₃) from hδW]
        exact commutatorElement_mul_left_of_central (S := S0)
          (u := ⁅⁅p, u⁆, q⁆) (v := β₁ * β₃) (w := u) hW_S0 hδ_cent huS0
  -- chain 2 (symmetric): ⁅⁅z',c⁆,u⁆ = ⁅⁅⁅q,u⁆,p⁆,u⁆
  have ha' : ⁅z', c⁆ * (⁅c, z'⁻¹⁆)⁻¹ ∈ ⁅B, B⁆ := by
    have hz'cB : ⁅z', c⁆ ∈ B := by
      exact hBA_le_B (Subgroup.commutator_mem_commutator (h₁ := hz'B) (h₂ := hcA))
    have hI1' : ⁅z', c⁆ * (⁅c, z'⁻¹⁆)⁻¹ = ⁅⁅z', c⁆, z'⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hI1']
    exact Subgroup.commutator_mem_commutator (h₁ := hz'cB) (h₂ := hz'invB)
  have hb' : ⁅c, z'⁻¹⁆ = ⁅z'⁻¹, c⁻¹⁆ := by
    have hcz'2 : ⁅c, z'⁻¹⁆ ∈ commChain B A 2 := by
      have hz'BA : z'⁻¹ ∈ ⁅B, A⁆ := by
        exact (⁅B, A⁆).inv_mem (Subgroup.commutator_mem_commutator (h₁ := huB) (h₂ := hpA))
      have hmem : ⁅c, z'⁻¹⁆ ∈ ⁅A, ⁅B, A⁆⁆ :=
        Subgroup.commutator_mem_commutator (h₁ := hcA) (h₂ := hz'BA)
      simpa [commChain_succ, commChain_zero, Subgroup.commutator_comm] using hmem
    have hdiff : ⁅⁅c, z'⁻¹⁆, c⁻¹⁆ ∈ commChain B A 3 :=
      Subgroup.commutator_mem_commutator (H₁ := commChain B A 2) (H₂ := A)
        (h₁ := hcz'2) (h₂ := A.inv_mem hcA)
    have hdiff1 : ⁅⁅c, z'⁻¹⁆, c⁻¹⁆ = 1 := by
      have : ⁅⁅c, z'⁻¹⁆, c⁻¹⁆ ∈ (⊥ : Subgroup G) := by
        rw [hchain3] at hdiff
        exact hdiff
      simpa using (Subgroup.mem_bot.mp this)
    have hI2' : ⁅c, z'⁻¹⁆ * (⁅z'⁻¹, c⁻¹⁆)⁻¹ = ⁅⁅c, z'⁻¹⁆, c⁻¹⁆ := by
      simp [commutatorElement_def, mul_assoc]
    have hX : ⁅c, z'⁻¹⁆ * (⁅z'⁻¹, c⁻¹⁆)⁻¹ = 1 := by
      rw [hI2', hdiff1]
    calc
      ⁅c, z'⁻¹⁆ = (⁅c, z'⁻¹⁆ * (⁅z'⁻¹, c⁻¹⁆)⁻¹) * ⁅z'⁻¹, c⁻¹⁆ := by group
      _ = ⁅z'⁻¹, c⁻¹⁆ := by rw [hX]; simp
  have hc' : ⁅z'⁻¹, c⁻¹⁆ * (⁅⁅q, u⁆, p⁆)⁻¹ ∈ ⁅B, B⁆ := by
    have hcong := hallWitt_congruence_mod_B' (S0 := S0) u q p huB hqA hpA
      hA_comm hB_norm hB'Z hA_le_S0 hB_le_S0
    -- hcong : ⁅⁅p,u⁆,q⁆ * (⁅⁅q,u⁆,p⁆)⁻¹ ∈ ⁅B,B⁆ — hmm — need the swapped version
    simpa [p, q, z', commutatorElement_inv] using hcong
  let β₁' : G := ⁅z', c⁆ * (⁅c, z'⁻¹⁆)⁻¹
  let β₃' : G := ⁅z'⁻¹, c⁻¹⁆ * (⁅⁅q, u⁆, p⁆)⁻¹
  have hβ₁'B' : β₁' ∈ ⁅B, B⁆ := ha'
  have hβ₃'B' : β₃' ∈ ⁅B, B⁆ := hc'
  have hδ'B' : β₁' * β₃' ∈ ⁅B, B⁆ := (⁅B, B⁆).mul_mem hβ₁'B' hβ₃'B'
  have hδ'_cent : β₁' * β₃' ∈ centerIn S0 := hB'Z hδ'B'
  have hδ'C : β₁' * β₃' ∈ Subgroup.centralizer (S0 : Set G) :=
    (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hδ'_cent
  have hW'_S0 : ⁅⁅q, u⁆, p⁆ ∈ S0 := by
    have hqu_S0 : ⁅q, u⁆ ∈ S0 := hB_le_S0 hquB
    exact S0.mul_mem (S0.mul_mem (S0.mul_mem hqu_S0 (hA_le_S0 hpA)) (S0.inv_mem hqu_S0)) (S0.inv_mem (hA_le_S0 hpA))
  have hδ'W : (β₁' * β₃') * ⁅⁅q, u⁆, p⁆ = ⁅⁅q, u⁆, p⁆ * (β₁' * β₃') :=
    ((Subgroup.mem_centralizer_iff.mp hδ'C) (⁅⁅q, u⁆, p⁆) hW'_S0).symm
  have hz'c : ⁅z', c⁆ = β₁' * β₃' * ⁅⁅q, u⁆, p⁆ := by
    calc
      ⁅z', c⁆ = β₁' * ⁅c, z'⁻¹⁆ := by
        dsimp [β₁']
        group
      _ = β₁' * ⁅z'⁻¹, c⁻¹⁆ := by rw [hb']
      _ = β₁' * (β₃' * ⁅⁅q, u⁆, p⁆) := by
        congr 1
        dsimp [β₃']
        group
      _ = β₁' * β₃' * ⁅⁅q, u⁆, p⁆ := by simp [mul_assoc]
  have hchain2 : ⁅⁅z', c⁆, u⁆ = ⁅⁅⁅q, u⁆, p⁆, u⁆ := by
    calc
      ⁅⁅z', c⁆, u⁆ = ⁅β₁' * β₃' * ⁅⁅q, u⁆, p⁆, u⁆ := by rw [hz'c]
      _ = ⁅⁅⁅q, u⁆, p⁆, u⁆ := by
        rw [show (β₁' * β₃') * ⁅⁅q, u⁆, p⁆ = ⁅⁅q, u⁆, p⁆ * (β₁' * β₃') from hδ'W]
        exact commutatorElement_mul_left_of_central (S := S0)
          (u := ⁅⁅q, u⁆, p⁆) (v := β₁' * β₃') (w := u) hW'_S0 hδ'_cent huS0
  -- connect: ⁅⁅⁅q,u⁆,p⁆,u⁆ = ⁅⁅⁅p,u⁆,q⁆,u⁆ via the congruence
  have hcon : ⁅⁅⁅q, u⁆, p⁆, u⁆ = ⁅⁅⁅p, u⁆, q⁆, u⁆ := by
    have hcong := hallWitt_congruence_mod_B' (S0 := S0) u p q huB hpA hqA
      hA_comm hB_norm hB'Z hA_le_S0 hB_le_S0
    -- hcong : ⁅⁅q,u⁆,p⁆ * (⁅⁅p,u⁆,q⁆)⁻¹ ∈ ⁅B,B⁆ — write ⁅⁅q,u⁆,p⁆ = δ·⁅⁅p,u⁆,q⁆
    let γ : G := ⁅⁅q, u⁆, p⁆ * (⁅⁅p, u⁆, q⁆)⁻¹
    have hγB' : γ ∈ ⁅B, B⁆ := by simpa [γ] using hcong
    have hγ_cent : γ ∈ centerIn S0 := hB'Z hγB'
    have hγC : γ ∈ Subgroup.centralizer (S0 : Set G) :=
      (inf_le_right : centerIn S0 ≤ Subgroup.centralizer (S0 : Set G)) hγ_cent
    have hγW : γ * ⁅⁅p, u⁆, q⁆ = ⁅⁅p, u⁆, q⁆ * γ :=
      ((Subgroup.mem_centralizer_iff.mp hγC) (⁅⁅p, u⁆, q⁆) hW_S0).symm
    have hqpeq : ⁅⁅q, u⁆, p⁆ = γ * ⁅⁅p, u⁆, q⁆ := by
      dsimp [γ]
      group
    calc
      ⁅⁅⁅q, u⁆, p⁆, u⁆ = ⁅γ * ⁅⁅p, u⁆, q⁆, u⁆ := by rw [hqpeq]
      _ = ⁅⁅⁅p, u⁆, q⁆, u⁆ := by
        rw [show γ * ⁅⁅p, u⁆, q⁆ = ⁅⁅p, u⁆, q⁆ * γ from hγW]
        exact commutatorElement_mul_left_of_central (S := S0)
          (u := ⁅⁅p, u⁆, q⁆) (v := γ) (w := u) hW_S0 hγ_cent huS0
  -- G0⁻¹ = G0
  have hGinv : G0⁻¹ = G0 := by
    calc
      G0⁻¹ = ⁅⁅z, b⁆, u⁆ := hw1.symm
      _ = ⁅⁅⁅p, u⁆, q⁆, u⁆ := hchain1
      _ = ⁅⁅⁅q, u⁆, p⁆, u⁆ := hcon.symm
      _ = ⁅⁅z', c⁆, u⁆ := hchain2.symm
      _ = G0 := hw2
  have hsq : G0 ^ 2 = 1 := by
    have h1 : G0 * G0 = G0 * G0⁻¹ := by rw [hGinv]
    have hsq' : G0 * G0 = 1 := by
      calc
        G0 * G0 = G0 * G0⁻¹ := h1
        _ = 1 := by simp
    simpa [pow_two] using hsq'
  -- goal: ⁅⁅p,u⁆,⁅q,u⁆⁆ = 1
  have hG0eq : ⁅⁅b⁻¹, x0⁻¹⁆, ⁅x0⁻¹, c⁻¹⁆⁻¹⁆ = G0 := by
    dsimp [u, p, q, G0]
    rw [commutatorElement_inv]
  exact hG0eq.trans (eq_one_of_mem_pGroup_sq_eq_one hpodd S0 hS0p hG0S0 hsq)

/-- From the Hall–Witt bridge, `[x,A]` is Abelian for every `x ∈ B`
(instantiating `hallWitt_commute` at `x⁻¹`; the generators `⁅x,a⁆` of
`commSub x A` then commute pairwise). -/
public lemma commSub_abelian_of_hallWitt {S0 A B : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hS0p : IsPGroup p S0) (hpodd : p ≠ 2)
    (hA_le_S0 : A ≤ S0) (hB_le_S0 : B ≤ S0)
    (hA_comm : IsMulCommutative A)
    (hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hB'Z : ⁅B, B⁆ ≤ centerIn S0)
    (hchain3 : commChain B A 3 = ⊥)
    (x0 : G) (hx0B : x0 ∈ B) :
    IsMulCommutative (commSub x0 A) := by
  -- the generators `⁅x0,a⁆` commute pairwise: instantiate the bridge at `x0⁻¹`
  -- (the paper's `[x0⁻¹,a⁻¹] = ⁅x0,a⁆`).
  have hgen : ∀ a b : G, a ∈ A → b ∈ A → Commute ⁅x0, a⁆ ⁅x0, b⁆ := by
    intro a b ha hb
    have hw := hallWitt_commute (S0 := S0) (p := p) hS0p hpodd hA_le_S0 hB_le_S0
      hA_comm hB_norm hB'Z hchain3 x0⁻¹ a⁻¹ b⁻¹ (B.inv_mem hx0B) (A.inv_mem ha) (A.inv_mem hb)
    -- hw : ⁅⁅a⁻¹⁻¹, x0⁻¹⁻¹⁆, ⁅x0⁻¹⁻¹, b⁻¹⁻¹⁆⁻¹⁆ = 1, i.e. ⁅⁅a, x0⁆, ⁅b, x0⁆⁆ = 1
    have hw' : Commute ⁅a, x0⁆ ⁅b, x0⁆ := by
      exact commutatorElement_eq_one_iff_commute.mp (by simpa using hw)
    -- ⁅a,x0⁆ = (⁅x0,a⁆)⁻¹ and ⁅b,x0⁆ = (⁅x0,b⁆)⁻¹, so ⁅x0,a⁆ commutes with ⁅x0,b⁆
    simpa [commutatorElement_inv] using hw'.inv_left.inv_right
  rw [commSub]
  refine Subgroup.isMulCommutative_closure (k := {g : G | ∃ a ∈ A, ⁅x0, a⁆ = g}) (Set.Pairwise.of_forall₂ ?_)
  intro y hy z hz
  show y * z = z * y
  rcases hy with ⟨a, ha, rfl⟩
  rcases hz with ⟨b, hb, rfl⟩
  exact hgen a b ha hb

/-- (4.1): `A ∩ B` centralises `[B,A]`.  From the Three Subgroups Lemma applied
to `[B,A∩B,A] ⊆ [B,B,J(S)] = 1` (by `[B,B] ⊆ Z(J(S))`, `A ⊆ J(S)`) and
`[A∩B,A,B] ⊆ [A,A,B] = 1` (`A` Abelian). -/
public lemma A_inf_B_centralizes_commutator {P A B : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    (hBB_le_ZJ : ⁅B, B⁆ ≤ thompsonCenter (G := G) P) :
    A ⊓ B ≤ Subgroup.centralizer ((⁅B, A⁆ : Subgroup G) : Set G) := by
  let J : Subgroup G := thompsonSubgroup (G := G) P
  have hA_le_J : A ≤ J := le_sSup hA
  have hAA_bot : ⁅A, A⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2
      ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA.2.1)
  have h1 : ⁅⁅B, A ⊓ B⁆, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅⁅B, A ⊓ B⁆, A⁆ ≤ ⁅⁅B, B⁆, A⁆ := by
        exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl inf_le_right) le_rfl
      _ ≤ ⁅⁅B, B⁆, J⁆ := Subgroup.commutator_mono le_rfl hA_le_J
      _ = ⊥ := by
        have hBB_le_centJ : ⁅B, B⁆ ≤ Subgroup.centralizer (J : Set G) := by
          have hBJ : ⁅B, B⁆ ≤ centerIn J := hBB_le_ZJ
          exact hBJ.trans (by
            change J ⊓ Subgroup.centralizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)
            exact inf_le_right)
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hBB_le_centJ
  have h2 : ⁅⁅A ⊓ B, A⁆, B⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅⁅A ⊓ B, A⁆, B⁆ ≤ ⁅⁅A, A⁆, B⁆ := by
        exact Subgroup.commutator_mono (Subgroup.commutator_mono inf_le_left le_rfl) le_rfl
      _ = ⊥ := by
        simp [hAA_bot]
  have h3 : ⁅⁅A, B⁆, A ⊓ B⁆ = ⊥ := lemma4_1e B (A ⊓ B) A h1 h2
  have h3' : ⁅A ⊓ B, ⁅B, A⁆⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using h3
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A ⊓ B) (H₂ := ⁅B, A⁆)).1 h3'

/-- `subgroupCentralizerIn' U H = centralizer H ⊓ U` is a `public def` of
`Theorem3_1.lean` whose definitional unfolding through the `Subgroup.Inf`/`copy`
structure is not transparent to the elaborator in this module (unlike in
`Theorem3_1.lean` itself), so membership constructions `⟨h₁,h₂⟩` and
`Subgroup.mem_inf.mpr` fail to elaborate against it.  This lemma makes the two
membership forms interconvertible; it carries no mathematical content and is
used exactly to translate `x ∈ subgroupCentralizerIn' U H` into
`x ∈ centralizer H ∧ x ∈ U` (and conversely). -/
public lemma mem_subgroupCentralizerIn' {U H : Subgroup G} {x : G} :
    x ∈ subgroupCentralizerIn' U H ↔ x ∈ Subgroup.centralizer (H : Set G) ∧ x ∈ U := by
  rw [subgroupCentralizerIn']
  exact Subgroup.mem_inf

/-- `C_U(H) ≤ U`.  With `subgroupCentralizerIn'` exposed this is the second
component of the inf; stated standalone so that Theorem 4.1 can lift
`c ∈ C_U(H)` to `c ∈ U` by a plain ≤-application without re-elaborating a
membership conversion inside tactic bullets (which makes the elaborator loop). -/
public lemma subgroupCentralizerIn'_le_right (U H : Subgroup G) : subgroupCentralizerIn' U H ≤ U := by
  intro x hx
  exact (Subgroup.mem_inf.mp hx).2

/-- `[M ⊔ C_A(M), A] ⊆ [M, A]` when `A` is Abelian: `C_A(M) ≤ A`, so
`[C_A(M), A] ≤ [A, A] = 1`, and `[M, A]` is invariant under conjugation by `M`
and by `C_A(M)` (the `comm_join_left_le` decomposition).  Used exactly for the
paper's `[A*,A,A] ⊆ [M,A,A]` step in Theorem 4.1, Case 1 and Case 2. -/
public lemma comm_sup_centralizer_le_comm {A M : Subgroup G}
    (hA_comm : IsMulCommutative A) :
    ⁅M ⊔ subgroupCentralizerIn' A M, A⁆ ≤ ⁅M, A⁆ := by
  refine comm_join_left_le (X := M) (Y := subgroupCentralizerIn' A M) (Z := A)
    (K := ⁅M, A⁆) ?_ ?_ ?_ ?_
  · exact le_rfl
  · have hCA_bot : ⁅subgroupCentralizerIn' A M, A⁆ = ⊥ := by
      apply le_bot_iff.mp
      calc
        ⁅subgroupCentralizerIn' A M, A⁆ ≤ ⁅A, A⁆ :=
          Subgroup.commutator_mono (subgroupCentralizerIn'_le_right A M) le_rfl
        _ = ⊥ := by
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2
            ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA_comm)
    exact hCA_bot.le.trans bot_le
  · intro x hx w hw
    exact conj_mem_commutator_of_mem_left (H' := M) (K' := A) hx hw
  · intro c hc w hw
    have hcA : c ∈ A := subgroupCentralizerIn'_le_right A M hc
    have hw' : w ∈ ⁅A, M⁆ := by simpa [Subgroup.commutator_comm] using hw
    have hconj : c * w * c⁻¹ ∈ ⁅A, M⁆ :=
      conj_mem_commutator_of_mem_left (H' := A) (K' := M) hcA hw'
    simpa [Subgroup.commutator_comm] using hconj

/-- (4.1), membership form: `A ∩ B ⊆ C_A(M)` for every `M ⊆ [B,A]` (`A ∈ A(S)`,
`[B,B] ⊆ Z(J(S))`).  Used in Theorem 4.1 to show `A ∩ B ⊆ C_A([x,A])`. -/
public lemma A_inf_B_le_centralizer_in {P A B M : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    (hBB_le_ZJ : ⁅B, B⁆ ≤ thompsonCenter (G := G) P)
    (hM_le_BA : M ≤ ⁅B, A⁆) :
    A ⊓ B ≤ subgroupCentralizerIn' A M := by
  intro y hy
  rw [mem_subgroupCentralizerIn']
  refine ⟨?_, (Subgroup.mem_inf.mp hy).1⟩
  have hcent_BA : A ⊓ B ≤ Subgroup.centralizer ((⁅B, A⁆ : Subgroup G) : Set G) :=
    A_inf_B_centralizes_commutator (G := G) hA hBB_le_ZJ
  have hcent_M : Subgroup.centralizer ((⁅B, A⁆ : Subgroup G) : Set G) ≤
      Subgroup.centralizer (M : Set G) :=
    Subgroup.centralizer_le (show (M : Set G) ⊆ (⁅B, A⁆ : Subgroup G) from hM_le_BA)
  exact hcent_M (hcent_BA hy)

/-- If `A` does not centralise `[C,A]`, then some `x ∈ C` has `A` not
centralising `[x,A]`. -/
public lemma exists_mem_of_commutator_chain_ne_bot (_B A C : Subgroup G)
    (_hA_comm : IsMulCommutative A) (h : ⁅⁅C, A⁆, A⁆ ≠ ⊥) :
    ∃ x : G, x ∈ C ∧ ⁅commSub x A, A⁆ ≠ ⊥ := by
  by_contra hnone
  have hcent : ∀ x ∈ C, ⁅commSub x A, A⁆ = ⊥ := by
    intro x hx
    by_contra hne
    exact hnone ⟨x, hx, hne⟩
  have hbot : ⁅⁅C, A⁆, A⁆ = ⊥ := by
    apply le_bot_iff.mp
    have hCA_le_cent : ⁅C, A⁆ ≤ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.commutator_le]
      intro x hx a ha
      have hxa : ⁅x, a⁆ ∈ commSub x A := commSub_mem x A ha
      have hx_cent : commSub x A ≤ Subgroup.centralizer (A : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (hcent x hx)
      exact hx_cent hxa
    exact ((Subgroup.commutator_eq_bot_iff_le_centralizer).2 hCA_le_cent).le
  exact h hbot

/-- Conjugation invariance of the join `K₁ ⊔ K₂` under `X`: it suffices that `X`
conjugates `K₁` into `K₁ ⊔ K₂` and fixes the elements of `K₂`. -/
private lemma conj_mem_sup_of_conj_mem_of_fixed (X K1 K2 : Subgroup G)
    (hfix2 : ∀ x : G, x ∈ X → ∀ w : G, w ∈ K2 → x * w * x⁻¹ = w)
    (hconj1 : ∀ x : G, x ∈ X → ∀ w : G, w ∈ K1 → x * w * x⁻¹ ∈ K1 ⊔ K2) :
    ∀ x : G, x ∈ X → ∀ w : G, w ∈ K1 ⊔ K2 → x * w * x⁻¹ ∈ K1 ⊔ K2 := by
  intro x hx w hw
  refine Subgroup.closure_induction (k := (K1 : Set G) ∪ (K2 : Set G))
    (p := fun t _ht => x * t * x⁻¹ ∈ K1 ⊔ K2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rcases ht with ht1 | ht2
    · exact hconj1 x hx t ht1
    · rw [hfix2 x hx t ht2]
      exact Subgroup.mem_sup_right ht2
  · simp
  · intro a b _ha _hb ha hb
    have heq : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by
      simp [mul_assoc]
    rw [heq]
    exact (K1 ⊔ K2).mul_mem ha hb
  · intro a _ha ha
    have hinv : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by
      simp [mul_assoc]
    rw [hinv]
    exact (K1 ⊔ K2).inv_mem ha
  · simpa [Subgroup.sup_eq_closure] using hw

/-- The induction step of (4.5): `⁅commChain B A j ⊔ B′, S₀⁆ ≤ [B,A;j+1]·B′`
for `S₀ = A ⊔ B`, `B′ = ⁅B,B⁆` (`A` Abelian, `A ≤ N_G(B)`, `B′ ⊆ Z(S₀)`). -/
private lemma commChain_sup_B'_commutator_le (A B : Subgroup G) (j : ℕ)
    (_hA_comm : IsMulCommutative A)
    (hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hB'Z : ⁅B, B⁆ ≤ centerIn (A ⊔ B)) :
    ⁅commChain B A j ⊔ ⁅B, B⁆, A ⊔ B⁆ ≤ commChain B A (j + 1) ⊔ ⁅B, B⁆ := by
  classical
  let B' : Subgroup G := ⁅B, B⁆
  let C : Subgroup G := commChain B A j
  have hC_le_B : C ≤ B := commChain_le_left B A hB_norm j
  have hBA_le_B : ⁅B, A⁆ ≤ B :=
    commutator_le_left_of_normalizer (H := B) (K := A) hB_norm
  have hCA_le_B : ⁅C, A⁆ ≤ B := (Subgroup.commutator_mono hC_le_B le_rfl).trans hBA_le_B
  have hCB_le_B' : ⁅C, B⁆ ≤ B' := Subgroup.commutator_mono hC_le_B le_rfl
  have hB'_central : ∀ g : G, g ∈ A ⊔ B → ∀ b' : G, b' ∈ B' → b' * g * b'⁻¹ = g := by
    intro g hg b' hb'
    have hb'C : b' ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
      (inf_le_right : centerIn (A ⊔ B) ≤
        Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hB'Z hb')
    have hcomm : b' * g = g * b' :=
      ((Subgroup.mem_centralizer_iff.mp hb'C) g hg).symm
    calc
      b' * g * b'⁻¹ = (g * b') * b'⁻¹ := by rw [hcomm]
      _ = g := by simp [mul_assoc]
  have hfix2_A : ∀ a : G, a ∈ A → ∀ w : G, w ∈ B' → a * w * a⁻¹ = w := by
    intro a ha w hw
    have hwC : w ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
      (inf_le_right : centerIn (A ⊔ B) ≤
        Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hB'Z hw)
    have hcomm : w * a = a * w :=
      ((Subgroup.mem_centralizer_iff.mp hwC) a (Subgroup.mem_sup_left ha)).symm
    calc
      a * w * a⁻¹ = (w * a) * a⁻¹ := by rw [hcomm]
      _ = w := by simp [mul_assoc]
  have hfix2_B : ∀ b : G, b ∈ B → ∀ w : G, w ∈ B' → b * w * b⁻¹ = w := by
    intro b hb w hw
    have hwC : w ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
      (inf_le_right : centerIn (A ⊔ B) ≤
        Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hB'Z hw)
    have hcomm : w * b = b * w :=
      ((Subgroup.mem_centralizer_iff.mp hwC) b (Subgroup.mem_sup_right hb)).symm
    calc
      b * w * b⁻¹ = (w * b) * b⁻¹ := by rw [hcomm]
      _ = w := by simp [mul_assoc]
  have hconj1_A : ∀ a : G, a ∈ A → ∀ w : G, w ∈ ⁅C, A⁆ → a * w * a⁻¹ ∈ ⁅C, A⁆ ⊔ B' := by
    intro a ha w hw
    exact Subgroup.mem_sup_left (by
      simpa [Subgroup.commutator_comm] using
        conj_mem_commutator_of_mem_left (H' := A) (K' := C) ha
          (by simpa [Subgroup.commutator_comm] using hw))
  have hconj1_B : ∀ b : G, b ∈ B → ∀ w : G, w ∈ ⁅C, A⁆ → b * w * b⁻¹ ∈ ⁅C, A⁆ ⊔ B' := by
    intro b hb w hw
    have hbwB' : ⁅b, w⁆ ∈ B' := by
      exact Subgroup.commutator_mono le_rfl hCA_le_B (Subgroup.commutator_mem_commutator hb hw)
    have hbw : b * w * b⁻¹ = ⁅b, w⁆ * w := by
      simp [commutatorElement_def, mul_assoc]
    rw [hbw]
    exact (⁅C, A⁆ ⊔ B').mul_mem (Subgroup.mem_sup_right hbwB') (Subgroup.mem_sup_left hw)
  -- first: drop the `B′` factor from the left argument
  have h1 : ⁅C ⊔ B', A ⊔ B⁆ ≤ ⁅C, A ⊔ B⁆ := by
    refine comm_join_left_le (X := C) (Y := B') (Z := A ⊔ B)
      (K := ⁅C, A ⊔ B⁆) ?_ ?_ ?_ ?_
    · exact le_rfl
    · have hB'bot : ⁅B', A ⊔ B⁆ = ⊥ := by
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := B') (H₂ := A ⊔ B)).2
          (hB'Z.trans (inf_le_right : centerIn (A ⊔ B) ≤
            Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)))
      exact hB'bot.le.trans bot_le
    · intro c hc w hw
      exact conj_mem_commutator_of_mem_left (H' := C) (K' := A ⊔ B) hc hw
    · intro b' hb' w hw
      have hwS0 : w ∈ A ⊔ B := by
        have hle : C ⊔ (A ⊔ B) ≤ A ⊔ B :=
          sup_le (hC_le_B.trans (le_sup_right : B ≤ A ⊔ B)) le_rfl
        exact hle (Subgroup.commutator_le_sup C (A ⊔ B) hw)
      have hb'eq : b' * w * b'⁻¹ = w := hB'_central w hwS0 b' hb'
      rw [hb'eq]
      exact hw
  -- then: split the right argument `A ⊔ B` into `A` and `B`
  have h2 : ⁅C, A ⊔ B⁆ ≤ ⁅C, A⁆ ⊔ B' := by
    refine comm_join_right_le (X := C) (Y := A) (Z := B)
      (K := ⁅C, A⁆ ⊔ B') ?_ ?_ ?_ ?_
    · exact le_sup_left
    · exact hCB_le_B'.trans le_sup_right
    · exact conj_mem_sup_of_conj_mem_of_fixed A ⁅C, A⁆ B' hfix2_A hconj1_A
    · exact conj_mem_sup_of_conj_mem_of_fixed B ⁅C, A⁆ B' hfix2_B hconj1_B
  calc
    ⁅C ⊔ B', A ⊔ B⁆ ≤ ⁅C, A ⊔ B⁆ := h1
    _ ≤ ⁅C, A⁆ ⊔ B' := h2
    _ = commChain B A (j + 1) ⊔ B' := by
      rw [commChain_succ]

set_option maxHeartbeats 1600000 in
/-- (4.5), first direction: for `S₀ = A ⊔ B` and `B′ = ⁅B,B⁆`, the lower
central series satisfies `S_j ≤ [B,A;j]·B′` for all `j ≥ 1` (`A` Abelian,
`A ≤ N_G(B)`, `B′ ⊆ Z(S₀)`). -/
public lemma lcs_le_commChain_sup_B' (A B : Subgroup G)
    (hA_comm : IsMulCommutative A)
    (hB_norm : A ≤ Subgroup.normalizer (B : Set G))
    (hB'Z : ⁅B, B⁆ ≤ centerIn (A ⊔ B)) :
    ∀ j : ℕ, 1 ≤ j → lcs (A ⊔ B) j ≤ commChain B A j ⊔ ⁅B, B⁆ := by
  classical
  let B' : Subgroup G := ⁅B, B⁆
  have hBA_le_B : ⁅B, A⁆ ≤ B :=
    commutator_le_left_of_normalizer (H := B) (K := A) hB_norm
  have hfix2_A : ∀ a : G, a ∈ A → ∀ w : G, w ∈ B' → a * w * a⁻¹ = w := by
    intro a ha w hw
    have hwC : w ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
      (inf_le_right : centerIn (A ⊔ B) ≤
        Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hB'Z hw)
    have hcomm : w * a = a * w :=
      ((Subgroup.mem_centralizer_iff.mp hwC) a (Subgroup.mem_sup_left ha)).symm
    calc
      a * w * a⁻¹ = (w * a) * a⁻¹ := by rw [hcomm]
      _ = w := by simp [mul_assoc]
  have hfix2_B : ∀ b : G, b ∈ B → ∀ w : G, w ∈ B' → b * w * b⁻¹ = w := by
    intro b hb w hw
    have hwC : w ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
      (inf_le_right : centerIn (A ⊔ B) ≤
        Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hB'Z hw)
    have hcomm : w * b = b * w :=
      ((Subgroup.mem_centralizer_iff.mp hwC) b (Subgroup.mem_sup_right hb)).symm
    calc
      b * w * b⁻¹ = (w * b) * b⁻¹ := by rw [hcomm]
      _ = w := by simp [mul_assoc]
  have hconj1_A : ∀ a : G, a ∈ A → ∀ w : G, w ∈ ⁅B, A⁆ → a * w * a⁻¹ ∈ ⁅B, A⁆ ⊔ B' := by
    intro a ha w hw
    exact Subgroup.mem_sup_left (by
      simpa [Subgroup.commutator_comm] using
        conj_mem_commutator_of_mem_left (H' := A) (K' := B) ha
          (by simpa [Subgroup.commutator_comm] using hw))
  have hconj1_B : ∀ b : G, b ∈ B → ∀ w : G, w ∈ ⁅B, A⁆ → b * w * b⁻¹ ∈ ⁅B, A⁆ ⊔ B' := by
    intro b hb w hw
    have hbwB' : ⁅b, w⁆ ∈ B' := by
      exact Subgroup.commutator_mono le_rfl hBA_le_B (Subgroup.commutator_mem_commutator hb hw)
    have hbw : b * w * b⁻¹ = ⁅b, w⁆ * w := by
      simp [commutatorElement_def, mul_assoc]
    rw [hbw]
    exact (⁅B, A⁆ ⊔ B').mul_mem (Subgroup.mem_sup_right hbwB') (Subgroup.mem_sup_left hw)
  have hconjK_A : ∀ a : G, a ∈ A → ∀ w : G, w ∈ ⁅B, A⁆ ⊔ B' → a * w * a⁻¹ ∈ ⁅B, A⁆ ⊔ B' :=
    conj_mem_sup_of_conj_mem_of_fixed A ⁅B, A⁆ B' hfix2_A hconj1_A
  have hconjK_B : ∀ b : G, b ∈ B → ∀ w : G, w ∈ ⁅B, A⁆ ⊔ B' → b * w * b⁻¹ ∈ ⁅B, A⁆ ⊔ B' :=
    conj_mem_sup_of_conj_mem_of_fixed B ⁅B, A⁆ B' hfix2_B hconj1_B
  have hbase : ⁅A ⊔ B, A ⊔ B⁆ ≤ commChain B A 1 ⊔ B' := by
    refine comm_join_left_le (X := A) (Y := B) (Z := A ⊔ B)
      (K := commChain B A 1 ⊔ B') ?_ ?_ ?_ ?_
    · -- ⁅A, A ⊔ B⁆ ≤ K
      refine comm_join_right_le (X := A) (Y := A) (Z := B)
        (K := commChain B A 1 ⊔ B') ?_ ?_ ?_ ?_
      · have hAA : ⁅A, A⁆ = ⊥ :=
          (Subgroup.commutator_eq_bot_iff_le_centralizer).2
            ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA_comm)
        exact hAA.le.trans bot_le
      · have hAB : ⁅A, B⁆ ≤ commChain B A 1 ⊔ B' := by
          rw [commChain_succ, commChain_zero]
          exact (le_of_eq (Subgroup.commutator_comm A B)).trans le_sup_left
        exact hAB
      · exact hconjK_A
      · exact hconjK_B
    · -- ⁅B, A ⊔ B⁆ ≤ K
      refine comm_join_right_le (X := B) (Y := A) (Z := B)
        (K := commChain B A 1 ⊔ B') ?_ ?_ ?_ ?_
      · have hBA : ⁅B, A⁆ ≤ commChain B A 1 ⊔ B' := by
          rw [commChain_succ, commChain_zero]
          exact le_sup_left
        exact hBA
      · exact le_sup_right
      · exact hconjK_A
      · exact hconjK_B
    · exact hconjK_A
    · exact hconjK_B
  have hmain : ∀ j : ℕ, 1 ≤ j → lcs (A ⊔ B) j ≤ commChain B A j ⊔ B' := by
    intro j
    induction j with
    | zero =>
        intro hj
        omega
    | succ j ih =>
        intro hj
        by_cases hj0 : j = 0
        · subst j
          simpa [lcs_succ, lcs_zero, B', commChain_succ, commChain_zero] using hbase
        · have hjj : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
          calc
            lcs (A ⊔ B) (j + 1) = ⁅lcs (A ⊔ B) j, A ⊔ B⁆ := by rw [lcs_succ]
            _ ≤ ⁅commChain B A j ⊔ B', A ⊔ B⁆ :=
              Subgroup.commutator_mono (ih hjj) le_rfl
            _ ≤ commChain B A (j + 1) ⊔ B' :=
              commChain_sup_B'_commutator_le A B j hA_comm hB_norm hB'Z
  intro j hj
  exact hmain j hj

set_option maxHeartbeats 4000000 in
/-- Theorem 4.1 (paper L781–L917): let `S` be a finite `p`-group, `A ∈ A(S)`,
`B ⊴ S` of nilpotence class at most two with `[B,B] ⊆ Z(J(S))`.  If
`[B,A;3] ≠ 1`, or if `p` is odd and `[B,A;2] ≠ 1`, then there exists
`A* ∈ A(S)` with `A ∩ B < A* ∩ B` and `[A*,A,A] = 1`.

Route (paper L790–L917): (4.1) `A∩B` centralises `[B,A]`; `[B,A;r] = 1` for
some least positive `r`, and `[B,A;n]` is Abelian for some least positive `n`.
Case 1 (`[B,A;n+1] ≠ 1`): `r ≥ n+2 ≥ 3`, `x ∈ [B,A;r-3]` with `A` not
centralising `[x,A]`, `M = [x,A] ⊆ [B,A;n]` Abelian, so
`A* = M·C_A(M) ∈ A(S)` by `theorem3_1a`; `A∩B ⊆ C_A(M)` by (4.1), `M ⊄ A`,
and `[A*,A,A] ⊆ [B,A;r] = 1`.  Case 2 (`[B,A;n+1] = 1`): in `S₀ = A·B` with
`B′ = [B,B] ⊆ Z(S₀)`, (4.5) gives `S_{n+2} ⊆ B′` (so `S_{n+3} = 1`), the
argument with `m = ⌊(n+4)/2⌋` forces `n ≤ 2` and hence `[B,A;3] = 1`; the
hypothesis then forces `p` odd and `[B,A;2] ≠ 1`; choose `x ∈ B` with `A` not
centralising `[x,A]`; by the Hall–Witt computation (`hallWitt_commute`) `[x,A]`
is Abelian; `A* = [x,A]·C_A([x,A]) ∈ A(S)` works as in Case 1. -/
public theorem theorem4_1 {P : Subgroup G} [Finite G] {p : ℕ} [Fact p.Prime]
    (hSp : IsPGroup p P) {A B : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P)
    (hB_le_P : B ≤ P) (hB_normal : (B.subgroupOf P).Normal)
    (hB_class2 : ⁅⁅B, B⁆, B⁆ = ⊥)
    (hBB_le_ZJ : ⁅B, B⁆ ≤ thompsonCenter (G := G) P)
    (h : commChain B A 3 ≠ ⊥ ∨ (p ≠ 2 ∧ commChain B A 2 ≠ ⊥)) :
    ∃ Astar : Subgroup G,
      Astar ∈ thompsonAbelianSubgroups (G := G) P ∧
        A ⊓ B < Astar ⊓ B ∧ ⁅⁅Astar, A⁆, A⁆ = ⊥ := by
  classical
  let S0 : Subgroup G := A ⊔ B
  have hS0_le_P : S0 ≤ P := sup_le hA.1 hB_le_P
  have hS0p : IsPGroup p S0 := hSp.to_le (H := S0) hS0_le_P
  have hP_le_normB : P ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_P).1 hB_normal
  have hA_norm_B : A ≤ Subgroup.normalizer (B : Set G) := hA.1.trans hP_le_normB
  have hA_comm : IsMulCommutative A := hA.2.1
  have hBAp : IsPGroup p ↥(B ⊔ A) := hSp.to_le (H := B ⊔ A) (sup_le hB_le_P hA.1)
  have hBA_le_B : ⁅B, A⁆ ≤ B :=
    commutator_B_A_le_B (P := P) hA.1 hB_le_P hB_normal
  have hB'_central_BA : ⁅B, B⁆ ≤ centerIn S0 := by
    -- [B,B] ⊆ Z(B) (class ≤ 2) and [B,B] ⊆ Z(J(S)) ⊇ C(A); both B, A ⊆ S0
    intro z hz
    have hzB : z ∈ B := by
      exact (sup_le le_rfl le_rfl : B ⊔ B ≤ B) (Subgroup.commutator_le_sup B B hz)
    refine ⟨Subgroup.mem_sup_right hzB, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    -- z commutes with every element of S0 = closure (A ∪ B)
    have hz_centB : z ∈ Subgroup.centralizer (B : Set G) := by
      -- [B,B] ≤ centralizer B from class ≤ 2
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅B, B⁆) (H₂ := B)).1 hB_class2 hz
    have hz_centA : z ∈ Subgroup.centralizer (A : Set G) := by
      have hzJ : z ∈ thompsonCenter (G := G) P := hBB_le_ZJ hz
      have hzCJ : z ∈ Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) :=
        (inf_le_right : centerIn (thompsonSubgroup (G := G) P) ≤
          Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)) hzJ
      have hA_le_J : A ≤ thompsonSubgroup (G := G) P := le_sSup hA
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hzCJ) a (hA_le_J ha)
    have hcommB : ∀ b : G, b ∈ B → z * b = b * z := fun b hb =>
      ((Subgroup.mem_centralizer_iff.mp hz_centB) b hb).symm
    have hcommA : ∀ a : G, a ∈ A → z * a = a * z := fun a ha =>
      ((Subgroup.mem_centralizer_iff.mp hz_centA) a ha).symm
    -- z commutes with every element of closure (A ∪ B) = S0
    have hmain : z * g = g * z := by
      refine Subgroup.closure_induction (k := (A : Set G) ∪ (B : Set G))
        (p := fun t _ => z * t = t * z) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        rcases ht with htA | htB
        · exact hcommA t htA
        · exact hcommB t htB
      · simp
      · intro a b _ _ ha hb
        calc
          z * (a * b) = (z * a) * b := by simp [mul_assoc]
          _ = (a * z) * b := by rw [ha]
          _ = a * (z * b) := by simp [mul_assoc]
          _ = a * (b * z) := by rw [hb]
          _ = (a * b) * z := by simp [mul_assoc]
      · intro a _ ha
        -- ha : z * a = a * z, hence z * a⁻¹ = a⁻¹ * z
        have hz_inv : z * a⁻¹ = a⁻¹ * z := by
          calc
            z * a⁻¹ = (a * z⁻¹)⁻¹ := by simp
            _ = (z⁻¹ * a)⁻¹ := by
              congr 1
              -- a * z⁻¹ = z⁻¹ * a
              have hza : z * a = a * z := ha
              have hcomm : Commute z a := hza
              exact hcomm.inv_left.symm
            _ = a⁻¹ * z := by simp
        exact hz_inv
      · -- g ∈ S0 = closure (A ∪ B)
        have hg' : g ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
          simpa [S0, Subgroup.sup_eq_closure] using hg
        exact hg'
    exact hmain.symm
  -- (4.1): A ∩ B centralises [B,A]
  have h41 : A ⊓ B ≤ Subgroup.centralizer ((⁅B, A⁆ : Subgroup G) : Set G) :=
    A_inf_B_centralizes_commutator (G := G) hA hBB_le_ZJ
  -- [B,A;r] = 1 for some least positive r
  have h_exists_r : ∃ r : ℕ, 0 < r ∧ commChain B A r = ⊥ := by
    obtain ⟨n, hn⟩ := commChain_eventually_bot (p := p) B A hBAp
    by_cases hnpos : 0 < n
    · exact ⟨n, hnpos, hn⟩
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnpos
      refine ⟨1, Nat.zero_lt_one, ?_⟩
      have hBbot : B = ⊥ := by
        simpa [commChain_zero, hn0] using hn
      rw [commChain_succ, commChain_zero, hBbot, Subgroup.commutator_bot_left]
  have h_exists_n : ∃ n : ℕ, 0 < n ∧ IsMulCommutative (commChain B A n) :=
    commChain_exists_positive_abelian (p := p) B A hBAp
  let n : ℕ := Nat.find h_exists_n
  have hn_pos : 0 < n := (Nat.find_spec h_exists_n).1
  have hn_comm : IsMulCommutative (commChain B A n) := (Nat.find_spec h_exists_n).2
  have hn_min : ∀ k : ℕ, 0 < k → IsMulCommutative (commChain B A k) → n ≤ k :=
    fun k hk hkc => Nat.find_min' h_exists_n ⟨hk, hkc⟩
  let r : ℕ := Nat.find h_exists_r
  have hr_pos : 0 < r := (Nat.find_spec h_exists_r).1
  have hr_bot : commChain B A r = ⊥ := (Nat.find_spec h_exists_r).2
  have hr_min : ∀ k : ℕ, 0 < k → commChain B A k = ⊥ → r ≤ k :=
    fun k hk hkb => Nat.find_min' h_exists_r ⟨hk, hkb⟩
  -- the construction of A* = M ⊔ C_A(M) given x ∈ B with M = [x,A] Abelian,
  -- A not centralising M, and [M,A,A] = 1:
  have hconstruct :
      ∀ x : G, x ∈ B → ⁅commSub x A, A⁆ ≠ ⊥ → IsMulCommutative (commSub x A) →
        ⁅⁅commSub x A, A⁆, A⁆ = ⊥ →
        ∃ Astar : Subgroup G,
          Astar ∈ thompsonAbelianSubgroups (G := G) P ∧
            A ⊓ B < Astar ⊓ B ∧ ⁅⁅Astar, A⁆, A⁆ = ⊥ := by
    intro x hxB hx_not_cent hM_comm hMAA_bot
    let M : Subgroup G := commSub x A
    let C : Subgroup G := subgroupCentralizerIn' A M
    have hxP : x ∈ P := hB_le_P hxB
    have hAstar_AS : M ⊔ C ∈ thompsonAbelianSubgroups (G := G) P :=
      theorem3_1a hA hxP hM_comm
    have hM_le_BA : M ≤ ⁅B, A⁆ := commSub_le_commutator x B A hxB
    have hM_le_B : M ≤ B := hM_le_BA.trans hBA_le_B
    have hM_le_P : M ≤ P := hM_le_B.trans hB_le_P
    have hAB_le_C : A ⊓ B ≤ C := A_inf_B_le_centralizer_in (G := G) hA hBB_le_ZJ hM_le_BA
    have hM_not_le_A : ¬ M ≤ A := by
      intro hM_le_A
      have hMA_bot : ⁅M, A⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅M, A⁆ ≤ ⁅A, A⁆ := Subgroup.commutator_mono hM_le_A le_rfl
          _ = ⊥ := by
            exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2
              ((Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hA_comm)
      exact hx_not_cent hMA_bot
    have hAB_le_Astar : A ⊓ B ≤ M ⊔ C := hAB_le_C.trans le_sup_right
    have hAB_le_inter : A ⊓ B ≤ (M ⊔ C) ⊓ B := le_inf hAB_le_Astar inf_le_right
    have hM_le_inter : M ≤ (M ⊔ C) ⊓ B := le_inf le_sup_left hM_le_B
    have hlt : A ⊓ B < (M ⊔ C) ⊓ B := by
      refine lt_of_le_of_ne hAB_le_inter ?_
      intro hEq
      have hM_le_A : M ≤ A := (hM_le_inter.trans (le_of_eq hEq.symm)).trans inf_le_left
      exact hM_not_le_A hM_le_A
    -- [A*,A,A] = 1
    have hAstarAA : ⁅⁅M ⊔ C, A⁆, A⁆ = ⊥ := by
      have hMC_le_M : ⁅M ⊔ C, A⁆ ≤ ⁅M, A⁆ := comm_sup_centralizer_le_comm (A := A) (M := M) hA_comm
      apply le_bot_iff.mp
      exact (Subgroup.commutator_mono hMC_le_M le_rfl).trans (le_of_eq hMAA_bot)
    exact ⟨M ⊔ C, hAstar_AS, hlt, hAstarAA⟩
  -- now split into the two cases
  by_cases h44 : commChain B A (n + 1) = ⊥
  · -- Case 2: [B,A;n+1] = 1
    have hB'Z0 : ⁅B, B⁆ ≤ centerIn S0 := hB'_central_BA
    -- (4.5): lcs S0 j ≤ [B,A;j]·B' for j ≥ 1
    have h45 : ∀ j : ℕ, 1 ≤ j → lcs S0 j ≤ commChain B A j ⊔ ⁅B, B⁆ :=
      lcs_le_commChain_sup_B' A B hA_comm hA_norm_B hB'Z0
    -- (4.6): S_{n+3} = 1, i.e. lcs S0 (n+2) = ⊥
    have h46 : lcs S0 (n + 2) = ⊥ := by
      have hS_n1 : lcs S0 (n + 1) ≤ ⁅B, B⁆ := by
        have hle := h45 (n + 1) (by omega)
        calc
          lcs S0 (n + 1) ≤ commChain B A (n + 1) ⊔ ⁅B, B⁆ := hle
          _ = ⁅B, B⁆ := by rw [h44, bot_sup_eq]
      have hle : lcs S0 (n + 2) ≤ ⁅⁅B, B⁆, S0⁆ := by
        calc
          lcs S0 (n + 2) = ⁅lcs S0 (n + 1), S0⁆ := by rw [lcs_succ]
          _ ≤ ⁅⁅B, B⁆, S0⁆ := Subgroup.commutator_mono hS_n1 le_rfl
      have hbot : ⁅⁅B, B⁆, S0⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅B, B⁆) (H₂ := S0)).2
          (hB'Z0.trans inf_le_right)
      exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
    -- m = ⌊(n+4)/2⌋ ; [B,A;m-1] Abelian ; n ≤ 2
    let m : ℕ := (n + 4) / 2
    have hm_le : 2 * m ≤ n + 4 := by
      dsimp [m]
      exact Nat.mul_div_le (n + 4) 2
    have hm_ge : n + 3 ≤ 2 * m := by
      have hdiv : n + 4 = 2 * ((n + 4) / 2) + (n + 4) % 2 := (Nat.div_add_mod (n + 4) 2).symm
      have hmod : (n + 4) % 2 ≤ 1 := by
        exact Nat.le_of_lt_succ (Nat.mod_lt (n + 4) (by norm_num))
      have hle' : n + 4 ≤ 2 * ((n + 4) / 2) + 1 := by
        calc
          n + 4 = 2 * ((n + 4) / 2) + (n + 4) % 2 := hdiv
          _ ≤ 2 * ((n + 4) / 2) + 1 := by omega
      omega
    have hm_ge2 : 2 ≤ m := by
      dsimp [m]
      omega
    have hchain_m_abelian : IsMulCommutative (commChain B A (m - 1)) := by
      have hlcs_comm : ⁅lcs S0 (m - 1), lcs S0 (m - 1)⁆ = ⊥ := by
        apply le_bot_iff.mp
        calc
          ⁅lcs S0 (m - 1), lcs S0 (m - 1)⁆ ≤ lcs S0 (m - 1 + (m - 1) + 1) :=
            lcs_commutator_le S0 (m - 1) (m - 1)
          _ = lcs S0 (2 * m - 1) := by
            congr 1
            omega
          _ ≤ lcs S0 (n + 2) := lcs_antitone S0 (by omega)
          _ = ⊥ := h46
      have hlcs_abelian : IsMulCommutative (lcs S0 (m - 1)) :=
        (Subgroup.commutator_self_eq_bot_iff).1 hlcs_comm
      have hchain_le : commChain B A (m - 1) ≤ lcs S0 (m - 1) := by
        simpa [S0, sup_comm] using commChain_le_lcs B A (m - 1)
      exact isMulCommutative_of_le hchain_le hlcs_abelian
    have hn_le_m : n ≤ m - 1 := hn_min (m - 1) (by omega) hchain_m_abelian
    have hn_le_two : n ≤ 2 := by
      dsimp [m] at hn_le_m
      omega
    -- (4.7): [B,A;3] = 1
    have h47 : commChain B A 3 = ⊥ := by
      apply le_bot_iff.mp
      calc
        commChain B A 3 ≤ commChain B A (n + 1) := commChain_antitone B A hA_norm_B (by omega)
        _ = ⊥ := h44
    -- the hypothesis forces p odd and [B,A;2] ≠ 1
    rcases h with hBA3 | hOdd
    · exact False.elim (hBA3 h47)
    · rcases hOdd with ⟨hpodd, hBA2⟩
      -- find x ∈ B with A not centralising [x,A]
      have hx_not_cent_exists : ∃ x : G, x ∈ B ∧ ⁅commSub x A, A⁆ ≠ ⊥ := by
        exact exists_mem_of_commutator_chain_ne_bot B A B hA_comm (by
          simpa [commChain_succ, commChain_zero] using hBA2)
      rcases hx_not_cent_exists with ⟨x, hxB, hx_not_cent⟩
      -- by the Hall–Witt bridge, [x,A] is Abelian
      have hM_comm : IsMulCommutative (commSub x A) := by
        exact commSub_abelian_of_hallWitt (S0 := S0) (p := p) hS0p hpodd
          (le_sup_left : A ≤ A ⊔ B) (le_sup_right : B ≤ A ⊔ B)
          hA_comm hA_norm_B hB'Z0 h47 x hxB
      -- [M,A,A] ≤ [B,A;3] = 1
      have hMAA_bot : ⁅⁅commSub x A, A⁆, A⁆ = ⊥ := by
        have hM_le_1 : commSub x A ≤ commChain B A 1 := commSub_le_commutator x B A hxB
        apply le_bot_iff.mp
        calc
          ⁅⁅commSub x A, A⁆, A⁆ ≤ ⁅⁅commChain B A 1, A⁆, A⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_mono hM_le_1 le_rfl) le_rfl
          _ = commChain B A 3 := by simp [commChain_succ]
          _ = ⊥ := h47
      exact hconstruct x hxB hx_not_cent hM_comm hMAA_bot
  · -- Case 1: [B,A;n+1] ≠ 1
    have hBA1 : commChain B A (n + 1) ≠ ⊥ := h44
    have hr_ge : r ≥ n + 2 := by
      by_contra hnot
      have hle : r ≤ n + 1 := by omega
      have hant : commChain B A (n + 1) ≤ commChain B A r :=
        commChain_antitone B A hA_norm_B hle
      have hbot : commChain B A (n + 1) = ⊥ := by
        apply le_bot_iff.mp
        exact hant.trans (le_of_eq hr_bot)
      exact hBA1 hbot
    have hr_ge3 : r ≥ 3 := by omega
    have hrn1 : commChain B A (r - 1) ≠ ⊥ := by
      intro hbot
      have hrle : r ≤ r - 1 := hr_min (r - 1) (by omega) hbot
      omega
    have hsucc : ⁅commChain B A (r - 3), A⁆ = commChain B A (r - 2) := by
      have harg : r - 2 = (r - 3) + 1 := by omega
      rw [harg, commChain_succ]
    have hx_exists : ∃ x : G, x ∈ commChain B A (r - 3) ∧ ⁅commSub x A, A⁆ ≠ ⊥ := by
      exact exists_mem_of_commutator_chain_ne_bot B A (commChain B A (r - 3)) hA_comm (by
        -- ⁅⁅commChain (r-3), A⁆, A⁆ = ⁅commChain (r-2), A⁆ = commChain (r-1) ≠ ⊥
        have h2 : ⁅commChain B A (r - 2), A⁆ = commChain B A (r - 1) := by
          have harg : r - 1 = (r - 2) + 1 := by omega
          rw [harg, commChain_succ]
        rw [hsucc, h2]
        exact hrn1)
    rcases hx_exists with ⟨x, hxC, hx_not_cent⟩
    have hxB : x ∈ B := (commChain_le_left B A hA_norm_B (r - 3)) hxC
    -- M ⊆ [B,A;r-2] ⊆ [B,A;n], hence M Abelian
    have hM_le_r2 : commSub x A ≤ commChain B A (r - 2) := by
      exact (commSub_le_commutator x (commChain B A (r - 3)) A hxC).trans (le_of_eq hsucc)
    have hM_comm : IsMulCommutative (commSub x A) := by
      have hle : commChain B A (r - 2) ≤ commChain B A n :=
        commChain_antitone B A hA_norm_B (by omega)
      exact isMulCommutative_of_le (hM_le_r2.trans hle) hn_comm
    -- [M,A,A] ≤ [B,A;r] = 1
    have hMAA_bot : ⁅⁅commSub x A, A⁆, A⁆ = ⊥ := by
      apply le_bot_iff.mp
      calc
        ⁅⁅commSub x A, A⁆, A⁆ ≤ ⁅⁅commChain B A (r - 2), A⁆, A⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hM_le_r2 le_rfl) le_rfl
        _ = commChain B A r := by
          calc
            ⁅⁅commChain B A (r - 2), A⁆, A⁆ = ⁅commChain B A (r - 1), A⁆ := by
              congr 1
              have harg : r - 1 = (r - 2) + 1 := by omega
              rw [harg, commChain_succ]
            _ = commChain B A ((r - 1) + 1) := by
              rw [commChain_succ]
            _ = commChain B A r := by
              congr 1
              omega
        _ = ⊥ := hr_bot
    exact hconstruct x hxB hx_not_cent hM_comm hMAA_bot

/-- Corollary 4.1 (paper L919–L925): let `S` be a finite `p`-group and `B ⊴ S`
with `[B,B] ⊆ Z(B) ∩ Z(J(S))`.  Then there exists `A ∈ A(S)` with
`[B,A;3] = 1`, and if `p` is odd, `[B,A;2] = 1`.  (Choose `A ∈ A(S)`
maximising `|A ∩ B|`; Theorem 4.1 would then produce `A*` with a strictly
larger intersection.) -/
public theorem corollary4_1 {P : Subgroup G} [Finite G] {p : ℕ} [Fact p.Prime]
    (hSp : IsPGroup p P) {B : Subgroup G}
    (hB_le_P : B ≤ P) (hB_normal : (B.subgroupOf P).Normal)
    (hBB_le_ZB : ⁅B, B⁆ ≤ centerIn B) (hBB_le_ZJ : ⁅B, B⁆ ≤ thompsonCenter (G := G) P) :
    ∃ A : Subgroup G,
      A ∈ thompsonAbelianSubgroups (G := G) P ∧
        commChain B A 3 = ⊥ ∧ (p ≠ 2 → commChain B A 2 = ⊥) := by
  classical
  have hB_class2 : ⁅⁅B, B⁆, B⁆ = ⊥ := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2
      (hBB_le_ZB.trans (inf_le_right : centerIn B ≤ Subgroup.centralizer (B : Set G)))
  -- an element of A(S) exists
  let s : Set (Subgroup G) := {C : Subgroup G | C ≤ P ∧ IsMulCommutative C}
  have hs_fin : s.Finite := Set.toFinite s
  have hs_ne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    refine ⟨bot_le, ?_⟩
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := ⊥)).1 bot_le
  obtain ⟨A0, hA0_s, hA0_max⟩ :=
    Set.exists_max_image s (fun C : Subgroup G => Nat.card C) hs_fin hs_ne
  have hA0_AS : A0 ∈ thompsonAbelianSubgroups (G := G) P :=
    ⟨hA0_s.1, hA0_s.2, fun B hB_le_P hB_comm => hA0_max B ⟨hB_le_P, hB_comm⟩⟩
  -- choose A ∈ A(S) maximising |A ∩ B|
  let t : Set (Subgroup G) := thompsonAbelianSubgroups (G := G) P
  have ht_fin : t.Finite := Set.toFinite t
  have ht_ne : t.Nonempty := ⟨A0, hA0_AS⟩
  obtain ⟨A, hA_t, hA_max⟩ :=
    Set.exists_max_image t (fun C : Subgroup G => Nat.card ↥(C ⊓ B)) ht_fin ht_ne
  have hA : A ∈ thompsonAbelianSubgroups (G := G) P := hA_t
  have hchain3 : commChain B A 3 = ⊥ := by
    by_contra hne
    obtain ⟨Astar, hAstar_AS, hlt, _⟩ :=
      theorem4_1 (G := G) hSp hA hB_le_P hB_normal hB_class2 hBB_le_ZJ (Or.inl hne)
    have hle_card : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(Astar ⊓ B) := Subgroup.card_le_of_le hlt.le
    have hlt_card : Nat.card ↥(A ⊓ B) < Nat.card ↥(Astar ⊓ B) := by
      refine lt_of_le_of_ne hle_card ?_
      intro hEq
      have hEq' : A ⊓ B = Astar ⊓ B := Subgroup.eq_of_le_of_card_ge hlt.le (Nat.le_of_eq hEq.symm)
      exact hlt.ne hEq'
    exact (not_lt_of_ge (hA_max Astar hAstar_AS)) hlt_card
  have hchain2 : p ≠ 2 → commChain B A 2 = ⊥ := by
    intro hpodd
    by_contra hne
    obtain ⟨Astar, hAstar_AS, hlt, _⟩ :=
      theorem4_1 (G := G) hSp hA hB_le_P hB_normal hB_class2 hBB_le_ZJ (Or.inr ⟨hpodd, hne⟩)
    have hle_card : Nat.card ↥(A ⊓ B) ≤ Nat.card ↥(Astar ⊓ B) := Subgroup.card_le_of_le hlt.le
    have hlt_card : Nat.card ↥(A ⊓ B) < Nat.card ↥(Astar ⊓ B) := by
      refine lt_of_le_of_ne hle_card ?_
      intro hEq
      have hEq' : A ⊓ B = Astar ⊓ B := Subgroup.eq_of_le_of_card_ge hlt.le (Nat.le_of_eq hEq.symm)
      exact hlt.ne hEq'
    exact (not_lt_of_ge (hA_max Astar hAstar_AS)) hlt_card
  exact ⟨A, hA, hchain3, hchain2⟩

end CFSG.Glauberman

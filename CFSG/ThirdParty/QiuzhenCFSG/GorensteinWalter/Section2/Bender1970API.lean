module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Coset.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Section 1 — the `O_q` / `O_π` / `O^p` / `π`-notation API

This lower layer holds the API of `refs/bender-abelian-sylow2.tex` Section 1
(the `O_q`/`O_π`/`O^p`/`π`-notation of [1], plus the Thompson lemma 1.1 and
its `O^p`-residual machinery).  The per-statement modules
(`Bender1970_16`, `Bender1970_17i/17ii/17iii`, `Bender1970_18`,
`Bender1970_19`) import THIS module instead of the wrapper
`GorensteinWalter.Section2.Bender1970`, so that the wrapper can import them
at landing without an import cycle.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u v
/-! ## The `O_q` / `O_π` / `O^p` / `π`-notation API ([1], Section 1) -/

/-- `π(X)`: the set of prime divisors of the order of `X`. -/
@[expose]
public def primesOfOrder {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Set ℕ :=
  {q : ℕ | q ∈ (Nat.card (↥H)).primeFactors}

/-- `O_q(H)`: the largest normal `q`-subgroup of `H`, regarded as an ambient
subgroup.  This reuses `pCore` from `FeitThompson.PCore.Defs`. -/
@[expose]
public def qCoreOf {G : Type u} [Group G] [Finite G] (H : Subgroup G) (q : ℕ) : Subgroup G :=
  (pCore q (↥H)).map H.subtype

/-- The set of normal subgroups of `G` whose order is a `π`-number, i.e. all
prime divisors of the order lie in `π`. -/
@[expose]
public def normalPiSubgroups {G : Type u} [Group G] [Finite G] (π : Set ℕ) : Set (Subgroup G) :=
  {K : Subgroup G | K.Normal ∧ ∀ q : ℕ, q ∈ (Nat.card (↥K)).primeFactors → q ∈ π}

/-- `O_π(G)`: the largest normal `π`-subgroup of `G` ([1], Section 1). -/
@[expose]
public def piCore (π : Set ℕ) (G : Type u) [Group G] [Finite G] : Subgroup G :=
  sSup (normalPiSubgroups (G := G) π)

/-- `O_π(H)`, regarded as an ambient subgroup of `G`. -/
@[expose]
public def piCoreOf {G : Type u} [Group G] [Finite G] (H : Subgroup G) (π : Set ℕ) : Subgroup G :=
  (piCore π (↥H)).map H.subtype

/-- `O^p(H)`: the `p`-residual of `H`, the intersection of the normal
subgroups of `H` of `p`-power index, regarded as an ambient subgroup.  This
mirrors `twoResidualOf` (= `O^2`). -/
@[expose]
public def pResidualOf {G : Type u} [Group G] [Finite G] (H : Subgroup G) (p : ℕ) : Subgroup G :=
  (sInf {N : Subgroup (↥H) | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}).map H.subtype


/-! ## Private machinery for the `O_q`/`O_π` API proofs -/

/-- If all prime divisors of `n` equal `p`, then `n` is a power of `p`. -/
private lemma exists_pow_of_primeFactors_subset_singleton {n : ℕ} (hn : n ≠ 0) {p : ℕ}
    (hp : ∀ r : ℕ, r ∈ n.primeFactors → r = p) : ∃ k : ℕ, n = p ^ k := by
  let S : Finset ℕ := n.primeFactors
  have hmain : n = (p ^ n.factorization p) ^ S.card := by
    calc
      n = ∏ r ∈ S, r ^ n.factorization r := by
        simpa [S] using (Nat.prod_primeFactors_pow_factorization hn)
      _ = ∏ r ∈ S, p ^ n.factorization p := by
        apply Finset.prod_congr rfl
        intro r hr
        have hrp : r = p := hp r hr
        simp [hrp]
      _ = (p ^ n.factorization p) ^ S.card := by
        simp
  exact ⟨n.factorization p * S.card, by
    rw [pow_mul]
    exact hmain⟩

/-- The pointwise product of a normal subgroup with any subgroup is their join. -/
private lemma mul_eq_sup_of_normal {G : Type u} [Group G] (A B : Subgroup G)
    (hA : A.Normal) : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  apply le_antisymm
  · intro x hx
    change x ∈ A ⊔ B at hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyA | hyB
      · exact Set.mem_mul.mpr ⟨y, hyA, 1, B.one_mem, mul_one y⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, y, hyB, one_mul y⟩
    · intro x hx
      rcases hx with hxA | hxB
      · exact Set.mem_mul.mpr ⟨x⁻¹, A.inv_mem hxA, 1, B.one_mem, mul_one x⁻¹⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, x⁻¹, B.inv_mem hxB, one_mul x⁻¹⟩
    · exact Set.mem_mul.mpr ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
    · intro a b hx hy ha hb
      rcases (Set.mem_mul).1 ha with ⟨a₁, ha₁, b₁, hb₁, rfl⟩
      rcases (Set.mem_mul).1 hb with ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine Set.mem_mul.mpr ⟨a₁ * (b₁ * a₂ * b₁⁻¹), ?_, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      · exact A.mul_mem ha₁ (hA.conj_mem a₂ ha₂ b₁)
      · group
  · intro x hx
    rcases (Set.mem_mul).1 hx with ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

/-- The join of a normal subgroup with a subgroup has cardinality dividing the
product of the cardinalities. -/
private lemma card_sup_dvd_card_mul {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hA : A.Normal) :
    Nat.card (↥(A ⊔ B)) ∣ Nat.card (↥A) * Nat.card (↥B) := by
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (B : Set G) * (A : Set G) := by
    have h1 : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
      mul_eq_sup_of_normal A B hA
    have h2 : (A : Set G) * (B : Set G) = (B : Set G) * (A : Set G) := by
      apply le_antisymm
      · intro x hx
        rcases (Set.mem_mul).1 hx with ⟨a, ha, b, hb, rfl⟩
        refine Set.mem_mul.mpr ⟨b, hb, b⁻¹ * a * b, by simpa using hA.conj_mem a ha b⁻¹, ?_⟩
        group
      · intro x hx
        rcases (Set.mem_mul).1 hx with ⟨b, hb, a, ha, rfl⟩
        refine Set.mem_mul.mpr ⟨b * a * b⁻¹, hA.conj_mem a ha b, b, hb, ?_⟩
        group
    exact h1.trans h2
  have h1 : Nat.card ((B : Set G) * (A : Set G)) =
      Nat.card ↥A * Nat.card ((B : Set G).image (QuotientGroup.mk' A)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := A) (t := (B : Set G))
  have h2 : Nat.card ((B : Set G).image (QuotientGroup.mk' A)) =
      Nat.card (B.map (QuotientGroup.mk' A)) := by
    rfl
  have h3 : Nat.card (B.map (QuotientGroup.mk' A)) ∣ Nat.card ↥B :=
    Subgroup.card_map_dvd (f := QuotientGroup.mk' A) (H := B)
  calc
    Nat.card (↥(A ⊔ B)) = Nat.card (((A ⊔ B : Subgroup G) : Set G)) := rfl
    _ = Nat.card ((B : Set G) * (A : Set G)) := by rw [hset]
    _ = Nat.card ↥A * Nat.card ((B : Set G).image (QuotientGroup.mk' A)) := h1
    _ = Nat.card ↥A * Nat.card (B.map (QuotientGroup.mk' A)) := by rw [h2]
    _ ∣ Nat.card ↥A * Nat.card ↥B := Nat.mul_dvd_mul_left (Nat.card ↥A) h3

/-- The set of normal π-subgroups is nonempty. -/
private lemma normalPiSubgroups_nonempty {G : Type u} [Group G] [Finite G]
    (π : Set ℕ) : (normalPiSubgroups (G := G) π).Nonempty := by
  refine ⟨⊥, ?_⟩
  constructor
  · infer_instance
  · intro q hq
    simp at hq

/-- The set of normal π-subgroups is directed: the join of two members is a
member (normal, and every prime divisor of its order lies in `π`). -/
private lemma directedOn_normalPiSubgroups {G : Type u} [Group G] [Finite G]
    (π : Set ℕ) : DirectedOn (· ≤ ·) (normalPiSubgroups (G := G) π) := by
  intro A hA B hB
  have hA_normal : A.Normal := hA.1
  have hB_normal : B.Normal := hB.1
  refine ⟨A ⊔ B, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · exact Subgroup.sup_normal A B
  · intro q hq
    have hqpf : q ∈ (Nat.card (↥(A ⊔ B))).primeFactors := hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqpf
    have hdvd : q ∣ Nat.card (↥A) * Nat.card (↥B) :=
      (Nat.dvd_of_mem_primeFactors hqpf).trans (card_sup_dvd_card_mul A B hA.1)
    rcases (Nat.Prime.dvd_mul hqprime).mp hdvd with hqA | hqB
    · exact hA.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hqA, Nat.card_pos.ne'⟩)
    · exact hB.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hqB, Nat.card_pos.ne'⟩)

/-- A finite subgroup is a `p`-group iff all prime divisors of its order equal
`p`. -/
private lemma isPGroup_iff_primeFactors_subset_singleton {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) {p : ℕ} (hp : p.Prime) :
    IsPGroup p K ↔ ∀ r : ℕ, r ∈ (Nat.card (↥K)).primeFactors → r = p := by
  constructor
  · intro hK r hr
    have hqprime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ Nat.card (↥K) := Nat.dvd_of_mem_primeFactors hr
    have : Fact p.Prime := ⟨hp⟩
    rcases (IsPGroup.iff_card (p := p) (G := ↥K)).mp hK with ⟨n, hcard⟩
    have hrdvd' : r ∣ p ^ n := hcard ▸ hrdvd
    have hrp : r ∣ p := hqprime.dvd_of_dvd_pow hrdvd'
    exact (Nat.prime_dvd_prime_iff_eq (p := r) (q := p) hqprime hp).mp hrp
  · intro hπ
    have hneq : Nat.card (↥K) ≠ 0 := Nat.card_pos.ne'
    rcases exists_pow_of_primeFactors_subset_singleton hneq (p := p) hπ with ⟨k, hk⟩
    exact IsPGroup.of_card hk

/-- `O_p(G) = O_π(G)` for `π = {p}`, `p` prime. -/
private lemma pCore_eq_piCore_of_prime {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) : pCore p G = piCore ({p} : Set ℕ) G := by
  have hset : normalPSubgroups (G := G) p = normalPiSubgroups (G := G) ({p} : Set ℕ) := by
    ext K
    simp [normalPSubgroups, normalPiSubgroups]
    intro hKnorm
    simpa [Nat.mem_primeFactors] using isPGroup_iff_primeFactors_subset_singleton K hp
  change sSup (normalPSubgroups (G := G) p) = sSup (normalPiSubgroups (G := G) ({p} : Set ℕ))
  rw [hset]

/-- `O_q(H)` is a `q`-group. -/
public theorem qCoreOf_isPGroup {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (q : ℕ) : IsPGroup q (qCoreOf H q) := by
  exact IsPGroup.map (pCore_isPGroup (p := q) (G := ↥H)) H.subtype

/-- `O_q(H)` is normal in `H`. -/
public theorem qCoreOf_normal_in {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (q : ℕ) : IsNormalIn (qCoreOf H q) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ H
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥H) * f * (⟨h, hh⟩ : ↥H)⁻¹ ∈ pCore q (↥H) := by
      exact (pCore_normal (p := q) (G := ↥H)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥H) * f * (⟨h, hh⟩ : ↥H)⁻¹, hconj, ?_⟩
    rw [hfk]
    simpa using hfk

/-- `O_q(H) ≤ H`. -/
public theorem qCoreOf_le {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (q : ℕ) : qCoreOf H q ≤ H := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
  rw [← hfx]
  change (f : G) ∈ H
  simp

/-- `O_π(H) ≤ H`. -/
public theorem piCoreOf_le {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) : piCoreOf H π ≤ H := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
  rw [← hfx]
  change (f : G) ∈ H
  simp

/-- The order of `O_π(H)` is a `π`-number: every prime divisor of
`|O_π(H)|` lies in `π`. -/
public theorem piCoreOf_primeDivisors {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) :
    ∀ q : ℕ, q ∈ (Nat.card ↥(piCoreOf H π)).primeFactors → q ∈ π := by
  intro q hq
  have hqpf : q ∈ (Nat.card (↥(piCoreOf H π))).primeFactors := hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqpf
  have hqdvd : q ∣ Nat.card (↥(piCoreOf H π)) := Nat.dvd_of_mem_primeFactors hqpf
  let : Fintype (↥(piCoreOf H π)) := Fintype.ofFinite _
  have : Fact q.Prime := ⟨hqprime⟩
  have hqcard : q ∣ Fintype.card (↥(piCoreOf H π)) := by
    simpa [Nat.card_eq_fintype_card] using hqdvd
  rcases exists_prime_orderOf_dvd_card (G := ↥(piCoreOf H π)) q hqcard with ⟨g, hg⟩
  have hgmem : (g : G) ∈ piCoreOf H π := g.2
  have hgpi : (g : G) ∈ (piCore π (↥H)).map H.subtype := by
    exact hgmem
  rcases (Subgroup.mem_map).1 hgpi with ⟨x, hxpi, hgx⟩
  have hxorder : orderOf (x : ↥H) = q := by
    calc
      orderOf (x : ↥H) = orderOf (H.subtype x) :=
        (orderOf_injective H.subtype H.subtype_injective x).symm
      _ = orderOf (g : G) := congrArg orderOf hgx
      _ = orderOf g :=
        orderOf_injective (piCoreOf H π).subtype (piCoreOf H π).subtype_injective g
      _ = q := hg
  have hdir := directedOn_normalPiSubgroups (G := ↥H) π
  have hne := normalPiSubgroups_nonempty (G := ↥H) π
  rcases ((Subgroup.mem_sSup_of_directedOn hne hdir).mp hxpi) with ⟨K, hK, hxK⟩
  have hqdvdk : q ∣ Nat.card (↥K) := by
    let : Fintype (↥K) := Fintype.ofFinite _
    let xK : ↥K := ⟨x, hxK⟩
    have horder : orderOf xK = q := by
      calc
        orderOf xK = orderOf (K.subtype xK) :=
          (orderOf_injective K.subtype K.subtype_injective xK).symm
        _ = orderOf (x : ↥H) := by simp [xK]
        _ = q := hxorder
    simpa [horder] using orderOf_dvd_card (x := xK)
  have hqpfK : q ∈ (Nat.card (↥K)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqprime, hqdvdk, Nat.card_pos.ne'⟩
  exact hK.2 q hqpfK

/-- `O_q(H) ⊆ O_π(H)` whenever `q ∈ π` (q a prime). -/
public theorem qCoreOf_le_piCoreOf {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) (q : ℕ) (hq : q ∈ π) (hp : q.Prime) :
    qCoreOf H q ≤ piCoreOf H π := by
  -- pCore q (↥H) is a normal π-subgroup, hence ≤ O_π
  have hpc : pCore q (↥H) ≤ piCore π (↥H) := by
    refine le_sSup ?_
    refine ⟨pCore_normal (p := q) (G := ↥H), ?_⟩
    intro r hr
    have hqprime : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrdvd : r ∣ Nat.card (↥(pCore q (↥H))) := Nat.dvd_of_mem_primeFactors hr
    have : Fact q.Prime := ⟨hp⟩
    rcases (IsPGroup.iff_card (p := q) (G := ↥(pCore q (↥H)))).mp
      (pCore_isPGroup (p := q) (G := ↥H)) with ⟨n, hcard⟩
    have hrdvd' : r ∣ q ^ n := hcard ▸ hrdvd
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq (p := r) (q := q) hqprime hp).mp
      (hqprime.dvd_of_dvd_pow hrdvd')
    simpa [hrq] using hq
  -- map both sides through H.subtype
  exact Subgroup.map_mono (f := H.subtype) hpc

/-- `O^p(H) ≤ H`. -/
public theorem pResidualOf_le {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) : pResidualOf H p ≤ H := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
  rw [← hfx]
  change (f : G) ∈ H
  simp

/-- The `p`-residual is contained in every normal subgroup whose index is a
`p`-power.  This is the basic elimination rule for the `sInf` definition of
`pResidualOf`; it is used when reducing a Thompson-lemma action to the
quotient by a normal `p`-power-index subgroup. -/
public theorem pResidualOf_le_of_normal_index
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (N : Subgroup (↥H))
    (hN : N.Normal) (hidx : ∃ n : ℕ, N.index = p ^ n) :
    pResidualOf H p ≤ N.map H.subtype := by
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
  have hNmem : N ∈ {M : Subgroup (↥H) |
      M.Normal ∧ ∃ n : ℕ, M.index = p ^ n} := ⟨hN, hidx⟩
  have hle : sInf {M : Subgroup (↥H) |
      M.Normal ∧ ∃ n : ℕ, M.index = p ^ n} ≤ N := sInf_le hNmem
  have hyN : y ∈ N := hle hy
  exact Subgroup.mem_map.mpr ⟨y, hyN, hxy⟩

/-! The following transport lemma is the quotient-compatibility part of the
`O^p` reduction used in Thompson's lemma.  It is stated for the intrinsic
`sInf` definition (before the ambient `pResidualOf` map) so that it can be
applied directly to an isomorphic copy of the acting group. -/

/-- The intrinsic `p`-residual is preserved by group isomorphisms. -/
public theorem pResidual_map_iso
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]
    (p : ℕ) (e : G ≃* H) :
    (sInf {N : Subgroup G | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}).map
        e.toMonoidHom =
      sInf {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n} := by
  let FG : Set (Subgroup G) :=
    {N | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  let FH : Set (Subgroup H) :=
    {N | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  apply le_antisymm
  · apply le_sInf
    intro M hM
    have hcomap : M.comap e.toMonoidHom ∈ FG := by
      refine ⟨hM.1.comap e.toMonoidHom, ?_⟩
      rcases hM.2 with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [M.index_comap_of_surjective e.surjective, hn]
    have hle : sInf FG ≤ M.comap e.toMonoidHom := sInf_le hcomap
    exact (Subgroup.map_le_iff_le_comap).2 hle
  · have hback : (sInf FH).map e.symm.toMonoidHom ≤ sInf FG := by
      apply le_sInf
      intro N hN
      have hmap : N.map e.toMonoidHom ∈ FH := by
        refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
        rcases hN.2 with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        exact (N.index_map_of_bijective e.bijective).trans hn
      have hle : sInf FH ≤ N.map e.toMonoidHom := sInf_le hmap
      apply (Subgroup.map_le_iff_le_comap).2
      refine hle.trans ?_
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
      simpa using hx
    have hback' := Subgroup.map_mono (f := e.toMonoidHom) hback
    simpa [Subgroup.map_map] using hback'

/-- If `O^p(K) = K`, then `K` is generated by the normal closures of its
`p'`-subgroups.  This is the generation step in the reduction from Bender's
Thompson lemma to the `P × Q` lemma: the join below is normal, and its index
has no prime divisor other than `p`, because it contains every Sylow
`q`-subgroup for `q ≠ p`. -/
public theorem pResidualOf_eq_self_implies_coprimeGenerated_eq_top
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hK : pResidualOf K p = K) :
    sSup {N : Subgroup (↥K) | ∃ Q : Subgroup (↥K),
      Nat.Coprime p (Nat.card (↥Q)) ∧
        N = Subgroup.normalClosure (Q : Set (↥K))} = ⊤ := by
  have hres :
      sInf {N : Subgroup (↥K) | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n} = ⊤ := by
    apply (Subgroup.map_subtype_inj (H := K)).mp
    have hmapTop : (⊤ : Subgroup (↥K)).map K.subtype = K := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
    exact (show
      (sInf {N : Subgroup (↥K) | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}).map
          K.subtype = K from hK).trans hmapTop.symm
  let family : Set (Subgroup (↥K)) :=
    {N : Subgroup (↥K) | ∃ Q : Subgroup (↥K),
      Nat.Coprime p (Nat.card (↥Q)) ∧
        N = Subgroup.normalClosure (Q : Set (↥K))}
  let L : Subgroup (↥K) := sSup family
  have hLnormal : L.Normal := by
    apply Subgroup.sSup_normal
    intro N hN
    rcases hN with ⟨Q, _hQ, rfl⟩
    exact Subgroup.normalClosure_normal
  have hQle : ∀ Q : Subgroup (↥K), Nat.Coprime p (Nat.card (↥Q)) → Q ≤ L := by
    intro Q hQ
    exact (Subgroup.le_normalClosure :
      Q ≤ Subgroup.normalClosure (Q : Set (↥K))).trans
        (le_sSup (show Subgroup.normalClosure (Q : Set (↥K)) ∈ family from
          ⟨Q, hQ, rfl⟩))
  have hidxne : L.index ≠ 0 := by
    intro hzero
    have hcard0 : Nat.card (↥L) * L.index = 0 := by simp [hzero]
    have hcardK0 : Nat.card (↥K) = 0 := by
      simpa [L.card_mul_index] using hcard0
    exact Nat.card_pos.ne' hcardK0
  have hprime : ∀ q : ℕ, q ∈ L.index.primeFactors → q = p := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqindex : q ∣ L.index := Nat.dvd_of_mem_primeFactors hq
    by_contra hqp
    let : Fact q.Prime := ⟨hqprime⟩
    let Q : Sylow q (↥K) := Classical.choice Sylow.nonempty
    have hQcard : Nat.Coprime p (Nat.card (↥(Q : Subgroup (↥K)))) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q) (G := Q)).mp Q.2
      rw [hn]
      exact hqprime.coprime_pow_of_not_dvd (by
        intro hdiv
        apply hqp
        exact (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hdiv)
    have hQL : (Q : Subgroup (↥K)) ≤ L := hQle (Q : Subgroup (↥K)) hQcard
    have hqQindex : q ∣ (Q : Subgroup (↥K)).index :=
      dvd_trans hqindex (Subgroup.index_dvd_of_le hQL)
    exact Q.not_dvd_index hqQindex
  have hpower : ∃ n : ℕ, L.index = p ^ n :=
    exists_pow_of_primeFactors_subset_singleton hidxne hprime
  have hresL :
      sInf {N : Subgroup (↥K) | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n} ≤ L := by
    apply sInf_le
    exact ⟨hLnormal, hpower⟩
  have htopL : (⊤ : Subgroup (↥K)) ≤ L := by
    simpa [hres] using hresL
  apply top_unique
  exact htopL

/-- A subgroup equal to its `p`-residual centralizes `B` once all of its
`p'`-subgroups centralize `B`.  The normalization hypothesis makes the
centralizer of `B` normal inside `K`, so it contains the normal closures in
`pResidualOf_eq_self_implies_coprimeGenerated_eq_top`. -/
public theorem centralizes_of_pResidualOf_eq_self_of_coprime_subgroups
    {G : Type u} [Group G] [Finite G]
    (K B : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hK : pResidualOf K p = K)
    (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hcop : ∀ Q : Subgroup (↥K), Nat.Coprime p (Nat.card (↥Q)) →
      Centralizes (Q.map K.subtype) B) :
    Centralizes K B := by
  let N : Subgroup (Subgroup.normalizer (B : Set G)) :=
    (Subgroup.centralizer (B : Set G)).subgroupOf
      (Subgroup.normalizer (B : Set G))
  let f : (↥K) →* Subgroup.normalizer (B : Set G) := Subgroup.inclusion hKB
  let C : Subgroup (↥K) := N.comap f
  have hNnormal : N.Normal := by
    exact Subgroup.normal_subgroupOf_centralizer_normalizer (B : Set G)
  have hCnormal : C.Normal := hNnormal.comap f
  let family : Set (Subgroup (↥K)) :=
    {M : Subgroup (↥K) | ∃ Q : Subgroup (↥K),
      Nat.Coprime p (Nat.card (↥Q)) ∧
        M = Subgroup.normalClosure (Q : Set (↥K))}
  have hfamilyTop : sSup family = ⊤ :=
    pResidualOf_eq_self_implies_coprimeGenerated_eq_top K p hp hK
  have hfamilyC : sSup family ≤ C := by
    apply sSup_le
    intro M hM
    rcases hM with ⟨Q, hQ, rfl⟩
    let : C.Normal := hCnormal
    apply Subgroup.normalClosure_le_normal
    intro q hq
    change (Subgroup.inclusion hKB q : Subgroup.normalizer (B : Set G)) ∈ N
    change (q : G) ∈ Subgroup.centralizer (B : Set G)
    apply hcop Q hQ
    exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
  have htopC : (⊤ : Subgroup (↥K)) ≤ C := by
    simpa [hfamilyTop] using hfamilyC
  intro k hk
  have hkC : (⟨k, hk⟩ : ↥K) ∈ C := htopC trivial
  exact hkC

/-- `O_{2'}(G) = O_π(G)` for `π` the set of odd primes: a finite normal
subgroup has odd order iff all prime divisors of its order are odd. -/
public theorem pPrimeCore_eq_piCore_odd {G : Type u} [Group G] [Finite G] :
    pPrimeCore 2 G = piCore {q : ℕ | Odd q} G := by
  have hset : normalPPrimeSubgroups (G := G) 2 = normalPiSubgroups (G := G) {q : ℕ | Odd q} := by
    ext K
    simp [normalPPrimeSubgroups, normalPiSubgroups]
    intro hKnorm
    constructor
    · intro hodd q hqprime hqdvd _hne
      have hqne2 : q ≠ 2 := by
        intro hq2
        have h2dvd : 2 ∣ Nat.card (↥K) := hq2 ▸ hqdvd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
      exact (hqprime.eq_two_or_odd').elim (fun h2 => False.elim (hqne2 h2)) id
    · intro hπ
      rw [← Nat.not_even_iff_odd]
      intro hEven
      have h2dvd : 2 ∣ Nat.card (↥K) := even_iff_two_dvd.mp hEven
      have hodd2 : Odd 2 := hπ 2 Nat.prime_two h2dvd Nat.card_pos.ne'
      have hodd2' : ¬ Odd 2 := by norm_num
      exact hodd2' hodd2
  change sSup (normalPPrimeSubgroups (G := G) 2) = sSup (normalPiSubgroups (G := G) {q : ℕ | Odd q})
  rw [hset]

/-- `O_{2'}(H) = O_π(H)` for `π` the set of odd primes, as ambient
subgroups. -/
public theorem oddCoreOf_eq_piCoreOf_odd {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : oddCoreOf H = piCoreOf H {q : ℕ | Odd q} := by
  unfold oddCoreOf piCoreOf
  congr 1
  exact pPrimeCore_eq_piCore_odd (G := ↥H)

/-- `O_2(H) = O_π(H)` for `π = {2}`, as ambient subgroups. -/
public theorem twoCoreOf_eq_piCoreOf_2 {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : twoCoreOf H = piCoreOf H {2} := by
  unfold twoCoreOf piCoreOf
  congr 1
  exact pCore_eq_piCore_of_prime (G := ↥H) 2 Nat.prime_two

/-- `O_q(H) = O_π(H)` for `π = {q}` (q a prime): the `π`-core with singleton
`π` is the `q`-core. -/
public theorem qCoreOf_eq_piCoreOf_singleton {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (q : ℕ) (hp : q.Prime) : qCoreOf H q = piCoreOf H {q} := by
  unfold qCoreOf piCoreOf
  congr 1
  exact pCore_eq_piCore_of_prime (G := ↥H) q hp

/-! ## Statement 1.1: the Thompson lemma -/

/-- Bender [1], Statement 1.1 (Thompson lemma, p. 164): a product of a
`p`-group `P` and a group `K` acts on a `p`-group `B`; if `K = O^p(K)`,
`[P, K] = 1` and `[C_B(P), K] = 1`, then `K` centralizes `B`.  The paper's
"product `PK` acts on `B`" is expressed here by the two normalization
hypotheses `P ≤ N_G(B)` and `K ≤ N_G(B)` (conjugation action).  This is the
"Thompson lemma 1.1" required by the [1]-Section-1 theory of Statements 1.6
and 1.7 in the blockers ledger. -/
public theorem bender1970_1_1_thompson
    {G : Type u} [Group G] [Finite G] (p : ℕ) (hp : p.Prime)
    (P K B : Subgroup G)
    (hPp : IsPGroup p P) (hBp : IsPGroup p B)
    (hK : pResidualOf K p = K)
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (hPK : ⁅P, K⁆ = ⊥)
    (hCBK : ⁅B ⊓ Subgroup.centralizer (P : Set G), K⁆ = ⊥) :
    Centralizes K B := by
  let : Fact p.Prime := ⟨hp⟩
  have hcop : ∀ Q : Subgroup (↥K), Nat.Coprime p (Nat.card (↥Q)) →
      Centralizes (Q.map K.subtype) B := by
    intro Q hQ
    have hQleK : Q.map K.subtype ≤ K := Subgroup.map_subtype_le (H := K) Q
    have hQB : Q.map K.subtype ≤ Subgroup.normalizer (B : Set G) :=
      hQleK.trans hKB
    have hPQ : ⁅P, Q.map K.subtype⁆ = ⊥ := by
      apply bot_unique
      rw [← hPK]
      exact Subgroup.commutator_mono le_rfl hQleK
    have hcardQ : Nat.card (↥(Q.map K.subtype)) = Nat.card (↥Q) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have hQcop : Nat.Coprime p (Nat.card (↥(Q.map K.subtype))) := by
      rw [hcardQ]
      exact hQ
    have hfixed : B ⊓ Subgroup.centralizer (P : Set G) ≤
        Subgroup.centralizer ((Q.map K.subtype : Subgroup G) : Set G) := by
      have hcentK : B ⊓ Subgroup.centralizer (P : Set G) ≤
          Subgroup.centralizer (K : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hCBK
      exact hcentK.trans (Subgroup.centralizer_le (by
        intro x hx
        exact hQleK hx))
    have hBQ : ⁅B, Q.map K.subtype⁆ = ⊥ :=
      ThompsonPQ.thompson_p_times_q P (Q.map K.subtype) B hPp hBp hQcop
        hPB hQB hPQ hfixed
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
    simpa [Subgroup.commutator_comm] using hBQ
  exact centralizes_of_pResidualOf_eq_self_of_coprime_subgroups
    K B p hp hK hKB hcop


end CFSG.GorensteinWalter

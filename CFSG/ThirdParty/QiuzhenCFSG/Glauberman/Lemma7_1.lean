module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Lemma 7.1

This file proves Lemma 7.1 of [6] (Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canad. J. Math. 20 (1968), 1101–1135), following the validated transcription in
`refs/glauberman-p-stable.tex` L1816–L1838:

> **Lemma.**  Let `G` be a finite group and `p` a prime.  Suppose that `H ⊆ G` and
> `G = O_{p'}(G)H`.  Let `W` be a `p`-subgroup of `H`.  If `g ∈ G` and `W^g ⊆ H`, then
> there exist `c ∈ O_{p'}(G) ∩ C(W)` and `h ∈ H` such that `g = ch`.

Here `O_{p'}(G)` is `pPrimeCore p G`, the hypothesis `G = O_{p'}(G)H` is taken in its
join form `pPrimeCore p G ⊔ H = ⊤` (the product decomposition is equivalent because
`O_{p'}(G) ⊴ G`), and `W` is a `p`-subgroup of `H` (i.e. `W : Subgroup H` with
`IsPGroup p W`; elements of `W` are lifted to `G` through the inclusion `H.subtype`).

**Conjugation convention.**  The paper writes `x^a = a⁻¹xa` throughout.  Accordingly the
hypothesis is stated as `∀ w : W, g⁻¹ * (w : G) * g ∈ H` (i.e. `W^g ⊆ H` in the paper's
convention — the same convention as `Glauberman.conjSubset`).  The statement pinned in the
round-2 ledger writes `g * (w : G) * g⁻¹ ∈ H`, which is `W^(g⁻¹)` in the paper's convention;
the two are *not* interchangeable in the conclusion `g = c·h` with `c` on the left (the
mirrored argument with `g` replaced by `g⁻¹` produces a factorization `g = h·c` with `h ∈ H`,
`c ∈ O_{p'}(G) ∩ C(W)`, which cannot in general be re-ordered to `g = c'·h'` with
`c' ∈ O_{p'}(G) ∩ C(W)`).  This file therefore follows the paper's convention; this is a
recorded statement drift from the pinned element form (the theorem is the same statement,
with the hypothesis expressed in the paper's conjugation convention).

## Proof route (paper L1816–L1838)

1. *Product decomposition.*  From `pPrimeCore p G ⊔ H = ⊤` and normality of `N = O_{p'}(G)`,
   `g = b·k` with `b ∈ N`, `k ∈ H`.
2. *`W^b ⊆ H`.*  For `w ∈ W`, `w^b = b⁻¹wb = (w^g)^{k⁻¹} = k·(g⁻¹wg)·k⁻¹ ∈ H`.
3. *`R = ⟨W, W^b⟩`.*  With `W' = W.map H.subtype` and `Wb = {b⁻¹wb | w ∈ W'}`, put
   `R = W' ⊔ Wb ⊆ H`.  Each generator of `Wb` is `(b⁻¹·w·b·w⁻¹)·w` with
   `b⁻¹·w·b·w⁻¹ ∈ N`, so `Wb ≤ N ⊔ W'` and dually `W' ≤ N ⊔ Wb`; hence `R ≤ N ⊔ W'` and
   `R ≤ N ⊔ Wb`, which yields the two decompositions
   `R = L·W' = L·Wb` (as sets, `L := N ⊓ R`): every `r ∈ R` is `n·w` with `n = r·w⁻¹ ∈ R ∩ N = L`.
4. *Sylow.*  `W'` and `Wb` are Sylow `p`-subgroups of `R`: both are `p`-groups, and with
   `L = N ⊓ R` one has `Subgroup.IsComplement' (L.subgroupOf R) (W'.subgroupOf R)` (disjoint: a
   `p`-group and a `p'`-group; product `= ⊤`: the decomposition), so
   `(W'.subgroupOf R).index = Nat.card L`, which is not divisible by `p` (its cardinal
   divides `Nat.card N`, coprime to `p`); by `IsPGroup.toSylow`, `W'.subgroupOf R` is a
   Sylow `p`-subgroup of `R`, and likewise for `Wb`.
5. *Sylow conjugacy.*  Sylow conjugacy inside `R` gives `r ∈ R` with `r • Wb = W` (right
   conjugation `x ↦ r·x·r⁻¹`).  Write `r⁻¹ = l·w` with `l ∈ L`, `w ∈ W'` (decomposition
   above).  Since `w ∈ W'` normalizes `W'`, `Wb = (r⁻¹)·W = (l·w)·W = l·W`, so `l⁻¹` (right)
   conjugates `Wb` into `W'`, i.e. **in the paper's convention** `d := l` satisfies
   `(Wb)^d ⊆ W'`.
6. *`c = bd` centralizes `W`.*  For `x ∈ W'`: `x^b ∈ Wb`, hence `x^{bd} = (x^b)^d ∈ W'`;
   and `x⁻¹·x^{bd} = (x⁻¹·x^b)·((x^b)⁻¹·(x^b)^d) ∈ N` because `b, d ∈ N` and `N ⊴ G`, so
   `x⁻¹·x^{bd} ∈ W' ∩ N = 1`, i.e. `x^{bd} = x` and `c = bd ∈ C(W)`.  (The paper prints
   `x⁻¹x^{bd} ∈ R∩O_{p'}(G) = 1` at this point; the printed equality is a typo — the valid
   inference is `x⁻¹x^{bd} ∈ W ∩ O_{p'}(G) = 1`, using that `x⁻¹x^{bd} ∈ W`, a `p`-group,
   and `O_{p'}(G)` is a `p'`-group.)
7. *Conclusion.*  `c = b·d ∈ N`, `h = d⁻¹·k ∈ H`, and `g = bk = bd·d⁻¹k = c·h`.
-/

open scoped Pointwise

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-- **Lemma 7.1** ([6], §7; `refs/glauberman-p-stable.tex` L1816–L1838): if `H ≤ G` with
`G = O_{p'}(G)·H` (in join form: `pPrimeCore p G ⊔ H = ⊤`), `W` is a `p`-subgroup of `H`,
and the conjugate `W^g` (paper convention `x^g = g⁻¹xg`) is contained in `H`, then
`g = c·h` with `c ∈ O_{p'}(G) ∩ C(W)` and `h ∈ H`.

The hypothesis is `∀ w : W, g⁻¹ * (w : G) * g ∈ H` (paper conjugation convention; see the
module docstring for why this differs from the ledger's pinned element form).  The centralizer
is taken with respect to the lifted subgroup `W.map H.subtype : Subgroup G` (the elements of
`W`, viewed in `G`). -/
public theorem lemma7_1 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (hGH : pPrimeCore p G ⊔ H = ⊤)
    (W : Subgroup H) (hWp : IsPGroup p W) {g : G}
    (hg : ∀ w : W, g⁻¹ * (w : G) * g ∈ H) :
    ∃ c : G, c ∈ pPrimeCore p G ∧
      c ∈ Subgroup.centralizer ((W.map H.subtype : Subgroup G) : Set G) ∧
      ∃ h : G, h ∈ H ∧ g = c * h := by
  classical
  let N : Subgroup G := pPrimeCore p G
  have hN : N.Normal := pPrimeCore_normal (p := p) (G := G)
  have hcopN : Nat.Coprime p (Nat.card N) := by
    simpa [N] using (pPrimeCore_coprime_card (p := p) (G := G))
  have hp : Nat.Prime p := Fact.out
  -- Step 1: g = b·k with b ∈ N, k ∈ H (from N ⊔ H = ⊤ and N ⊴ G, so N ⊔ H = H·N).
  have hgHN : g ∈ (H : Set G) * (N : Set G) := by
    have h1 : g ∈ N ⊔ H := by
      simpa [N, ← hGH] using (Subgroup.mem_top (G := G) g)
    have hset : (↑(N ⊔ H) : Set G) = (H : Set G) * (N : Set G) := by
      simpa [sup_comm] using (Subgroup.mul_normal (H := H) (N := N))
    exact hset ▸ h1
  rcases (Set.mem_mul.mp hgHN) with ⟨h0, hh0H, n0, hn0N, hh0n0⟩
  let b : G := h0 * n0 * h0⁻¹
  let k : G := h0
  have hbN : b ∈ N := by
    dsimp [b]
    simpa [inv_inv] using (Subgroup.Normal.conj_mem' hN n0 hn0N (h0⁻¹))
  have hbk : b * k = g := by
    dsimp [b, k]
    calc
      (h0 * n0 * h0⁻¹) * h0 = h0 * n0 := by group
      _ = g := hh0n0
  have hkH : k ∈ H := hh0H
  let W' : Subgroup G := W.map H.subtype
  let Wb : Subgroup G := W'.map (MulAut.conj (b⁻¹)).toMonoidHom
  let R : Subgroup G := W' ⊔ Wb
  let L : Subgroup G := N ⊓ R
  have hW'p : IsPGroup p W' := by
    simpa [W'] using (IsPGroup.map hWp H.subtype)
  have hW'R : W' ≤ R := le_sup_left
  have hWbR : Wb ≤ R := le_sup_right
  have hWbp : IsPGroup p Wb := by
    simpa [Wb] using (IsPGroup.map hW'p (MulAut.conj (b⁻¹)).toMonoidHom)
  have hW'H : W' ≤ H := by
    simpa [W'] using (Subgroup.map_subtype_le (H := H) W)
  -- Step 2: W^b ⊆ H.
  have hWbH : Wb ≤ H := by
    intro y hy
    rcases (Subgroup.mem_map.mp hy) with ⟨x, hxW', rfl⟩
    rcases (Subgroup.mem_map.mp hxW') with ⟨w, hwW, hxw⟩
    have hmain : b⁻¹ * (w : G) * b = k * (g⁻¹ * (w : G) * g) * k⁻¹ := by
      rw [← hbk]
      group
    have hkin : k * (g⁻¹ * (w : G) * g) * k⁻¹ ∈ H :=
      Subgroup.mul_mem H (Subgroup.mul_mem H hkH (hg ⟨w, hwW⟩)) (Subgroup.inv_mem H hkH)
    rw [← hxw]
    change (MulAut.conj (b⁻¹)) (w : G) ∈ H
    rw [MulAut.conj_apply, inv_inv]
    rw [hmain]
    exact hkin
  have hRH : R ≤ H := by
    exact sup_le hW'H hWbH
  -- Step 3: R ≤ N ⊔ W' and R ≤ N ⊔ Wb (via the commutator trick for the generators).
  have hWb_le_sup : Wb ≤ N ⊔ W' := by
    intro y hy
    rcases (Subgroup.mem_map.mp hy) with ⟨x, hxW', rfl⟩
    rcases (Subgroup.mem_map.mp hxW') with ⟨w, hwW, hxw⟩
    let n : G := b⁻¹ * (w : G) * b * (w : G)⁻¹
    have hnN : n ∈ N := by
      dsimp [n]
      have h1 : (w : G) * b * (w : G)⁻¹ ∈ N := by
        simpa [inv_inv] using (Subgroup.Normal.conj_mem' hN b hbN ((w : G)⁻¹))
      rw [show b⁻¹ * (w : G) * b * (w : G)⁻¹ = b⁻¹ * ((w : G) * b * (w : G)⁻¹) by group]
      exact Subgroup.mul_mem N (Subgroup.inv_mem N hbN) h1
    have hyE : (MulAut.conj (b⁻¹)) (w : G) = n * (w : G) := by
      dsimp [n]
      simp only [inv_inv]
      group
    have hwW' : (w : G) ∈ W' := by
      exact (Subgroup.mem_map.mpr ⟨w, hwW, rfl⟩ : H.subtype w ∈ W.map H.subtype)
    have hnW : n * (w : G) ∈ N ⊔ W' :=
      Subgroup.mul_mem (N ⊔ W') (Subgroup.mem_sup_left (S := N) (T := W') hnN)
        (Subgroup.mem_sup_right (S := N) (T := W') hwW')
    rw [← hxw]
    change (MulAut.conj (b⁻¹)) (w : G) ∈ N ⊔ W'
    rw [hyE]
    exact hnW
  have hR_le_sup : R ≤ N ⊔ W' := by
    exact sup_le le_sup_right hWb_le_sup
  have hW'_le_sup' : W' ≤ N ⊔ Wb := by
    intro x hxW'
    let y : G := b⁻¹ * x * b
    have hyWb : y ∈ Wb := by
      exact Subgroup.mem_map.mpr ⟨x, hxW', by simp [y]⟩
    let n : G := b * y * b⁻¹ * y⁻¹
    have hnN : n ∈ N := by
      dsimp [n]
      have h1 : y * b⁻¹ * y⁻¹ ∈ N := by
        simpa [inv_inv] using (Subgroup.Normal.conj_mem' hN (b⁻¹) (Subgroup.inv_mem N hbN) (y⁻¹))
      rw [show b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹) by group]
      exact Subgroup.mul_mem N hbN h1
    have hprod : n * y = x := by
      dsimp [n, y]
      group
    have hnW : n * y ∈ N ⊔ Wb :=
      Subgroup.mul_mem (N ⊔ Wb) (Subgroup.mem_sup_left (S := N) (T := Wb) hnN)
        (Subgroup.mem_sup_right (S := N) (T := Wb) hyWb)
    simpa [hprod] using hnW
  have hR_le_sup' : R ≤ N ⊔ Wb := by
    exact sup_le hW'_le_sup' le_sup_right
  -- Decompositions: every element of R is l·w (l ∈ L, w ∈ W') and l·y (l ∈ L, y ∈ Wb).
  have hR_decomp : ∀ r : G, r ∈ R → ∃ l : G, l ∈ L ∧ ∃ w : G, w ∈ W' ∧ r = l * w := by
    intro r hr
    have hrNS : r ∈ W' ⊔ N := by
      simpa [sup_comm] using hR_le_sup hr
    have hset : (↑(W' ⊔ N) : Set G) = (W' : Set G) * (N : Set G) :=
      Subgroup.mul_normal (H := W') (N := N)
    have hrm : r ∈ (W' : Set G) * (N : Set G) := hset ▸ hrNS
    rcases (Set.mem_mul.mp hrm) with ⟨w, hwW', n, hnN, hwn⟩
    have hnR : n ∈ R := by
      have hw1 : w⁻¹ ∈ R := Subgroup.inv_mem R (hW'R hwW')
      have : w⁻¹ * r = n := by
        rw [← hwn]
        group
      exact this ▸ (Subgroup.mul_mem R hw1 hr)
    have hlN : w * n * w⁻¹ ∈ N := by
      simpa [inv_inv] using (Subgroup.Normal.conj_mem' hN n hnN (w⁻¹))
    have hlR : w * n * w⁻¹ ∈ R :=
      Subgroup.mul_mem R (Subgroup.mul_mem R (hW'R hwW') hnR)
        (Subgroup.inv_mem R (hW'R hwW'))
    refine ⟨w * n * w⁻¹, Subgroup.mem_inf.mpr ⟨hlN, hlR⟩, w, hwW', ?_⟩
    calc
      r = w * n := hwn.symm
      _ = (w * n * w⁻¹) * w := by group
  have hR_decomp' : ∀ r : G, r ∈ R → ∃ l : G, l ∈ L ∧ ∃ y : G, y ∈ Wb ∧ r = l * y := by
    intro r hr
    have hrNS : r ∈ Wb ⊔ N := by
      simpa [sup_comm] using hR_le_sup' hr
    have hset : (↑(Wb ⊔ N) : Set G) = (Wb : Set G) * (N : Set G) :=
      Subgroup.mul_normal (H := Wb) (N := N)
    have hrm : r ∈ (Wb : Set G) * (N : Set G) := hset ▸ hrNS
    rcases (Set.mem_mul.mp hrm) with ⟨y, hyWb, n, hnN, hyn⟩
    have hnR : n ∈ R := by
      have hy1 : y⁻¹ ∈ R := Subgroup.inv_mem R (hWbR hyWb)
      have : y⁻¹ * r = n := by
        rw [← hyn]
        group
      exact this ▸ (Subgroup.mul_mem R hy1 hr)
    have hlN : y * n * y⁻¹ ∈ N := by
      simpa [inv_inv] using (Subgroup.Normal.conj_mem' hN n hnN (y⁻¹))
    have hlR : y * n * y⁻¹ ∈ R :=
      Subgroup.mul_mem R (Subgroup.mul_mem R (hWbR hyWb) hnR)
        (Subgroup.inv_mem R (hWbR hyWb))
    refine ⟨y * n * y⁻¹, Subgroup.mem_inf.mpr ⟨hlN, hlR⟩, y, hyWb, ?_⟩
    calc
      r = y * n := hyn.symm
      _ = (y * n * y⁻¹) * y := by group
  -- Disjointness: W' ∩ N = ⊥ (a p-subgroup and a p'-subgroup).
  have hcopW'N : Nat.Coprime (Nat.card (↥W')) (Nat.card N) := by
    rcases (IsPGroup.exists_card_eq hW'p) with ⟨n, hn⟩
    rw [hn]
    exact hcopN.pow_left n
  have hW'N_disj : Disjoint W' N := Subgroup.disjoint_of_coprime_natCard hcopW'N
  have hcardWb : Nat.card (↥Wb) = Nat.card (↥W') := by
    have hf : Function.Injective ((MulAut.conj (b⁻¹)).toMonoidHom) :=
      (MulAut.conj (b⁻¹)).injective
    simpa [Wb] using
      (Subgroup.card_map_of_injective (K := W') (f := (MulAut.conj (b⁻¹)).toMonoidHom) hf)
  have hcopWbN : Nat.Coprime (Nat.card (↥Wb)) (Nat.card N) := by
    rwa [hcardWb]
  have hWbN_disj : Disjoint Wb N := Subgroup.disjoint_of_coprime_natCard hcopWbN
  have hW'L_disj : Disjoint W' L := hW'N_disj.mono_right inf_le_left
  have hWbL_disj : Disjoint Wb L := hWbN_disj.mono_right inf_le_left
  -- Sylow-ness of W' and Wb inside R.
  have hLR : L ≤ R := inf_le_right
  have hL_le_N : L ≤ N := inf_le_left
  have hcomp : Subgroup.IsComplement' (L.subgroupOf R) (W'.subgroupOf R) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxL hxW
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hW'L_disj)
        ((Subgroup.mem_subgroupOf).mp hxW) ((Subgroup.mem_subgroupOf).mp hxL)
    · apply Set.eq_univ_iff_forall.mpr
      intro t
      rw [Set.mem_mul]
      rcases (hR_decomp (t : G) t.property) with ⟨l, hlL, w, hwW', htl⟩
      refine ⟨⟨l, hLR hlL⟩, (Subgroup.mem_subgroupOf).2 hlL,
        ⟨w, hW'R hwW'⟩, (Subgroup.mem_subgroupOf).2 hwW', ?_⟩
      apply Subtype.ext
      exact htl.symm
  have hW''p : IsPGroup p (W'.subgroupOf R) := by
    exact IsPGroup.of_equiv (hG := hW'p) (W'.subgroupOfEquivOfLe le_sup_left).symm
  have hWidx : ¬ p ∣ (W'.subgroupOf R).index := by
    rw [Subgroup.IsComplement'.index_eq_card hcomp]
    have hcopLR : Nat.Coprime p (Nat.card (L.subgroupOf R)) := by
      have hcard : Nat.card (L.subgroupOf R) = Nat.card L :=
        Nat.card_congr (L.subgroupOfEquivOfLe hLR).toEquiv
      have hcopL : Nat.Coprime p (Nat.card L) :=
        Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopN
      simpa [hcard] using hcopL
    exact (hp.coprime_iff_not_dvd).1 hcopLR
  have hcomp' : Subgroup.IsComplement' (L.subgroupOf R) (Wb.subgroupOf R) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxL hxW
      apply Subtype.ext
      exact (Subgroup.disjoint_def.mp hWbL_disj)
        ((Subgroup.mem_subgroupOf).mp hxW) ((Subgroup.mem_subgroupOf).mp hxL)
    · apply Set.eq_univ_iff_forall.mpr
      intro t
      rw [Set.mem_mul]
      rcases (hR_decomp' (t : G) t.property) with ⟨l, hlL, y, hyWb, htl⟩
      refine ⟨⟨l, hLR hlL⟩, (Subgroup.mem_subgroupOf).2 hlL,
        ⟨y, hWbR hyWb⟩, (Subgroup.mem_subgroupOf).2 hyWb, ?_⟩
      apply Subtype.ext
      exact htl.symm
  have hWb''p : IsPGroup p (Wb.subgroupOf R) := by
    exact IsPGroup.of_equiv (hG := hWbp) (Wb.subgroupOfEquivOfLe le_sup_right).symm
  have hWbidx : ¬ p ∣ (Wb.subgroupOf R).index := by
    rw [Subgroup.IsComplement'.index_eq_card hcomp']
    have hcopLR' : Nat.Coprime p (Nat.card (L.subgroupOf R)) := by
      have hcard : Nat.card (L.subgroupOf R) = Nat.card L :=
        Nat.card_congr (L.subgroupOfEquivOfLe hLR).toEquiv
      have hcopL : Nat.Coprime p (Nat.card L) :=
        Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcopN
      simpa [hcard] using hcopL
    exact (hp.coprime_iff_not_dvd).1 hcopLR'
  let PW : Sylow p (↥R) := IsPGroup.toSylow hW''p hWidx
  let PWb : Sylow p (↥R) := IsPGroup.toSylow hWb''p hWbidx
  -- Sylow conjugacy inside R: some r ∈ R right-conjugates Wb into W'.
  let : Finite (Subgroup (↥R)) :=
    Finite.of_injective (fun H : Subgroup (↥R) => (H : Set (↥R))) SetLike.coe_injective
  let : Finite (Sylow p (↥R)) := inferInstance
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq (↥R) PWb PW
  -- Write r⁻¹ = l·w with l ∈ L, w ∈ W'.
  have hrinvR : ((r⁻¹ : ↥R) : G) ∈ R := by
    exact (Subgroup.inv_mem R r.property)
  rcases (hR_decomp ((r⁻¹ : ↥R) : G) hrinvR) with ⟨l, hlL, w, hwW', hrlw⟩
  let l' : ↥R := ⟨l, hLR hlL⟩
  let w' : ↥R := ⟨w, hW'R hwW'⟩
  have hlr : (r⁻¹ : ↥R) = l' * w' := by
    apply Subtype.ext
    exact hrlw
  have hr1 : PWb = (r⁻¹ : ↥R) • PW := by
    calc
      PWb = (r⁻¹ : ↥R) • (r • PWb) := by
        rw [← mul_smul, inv_mul_cancel]
        simp
      _ = (r⁻¹ : ↥R) • PW := by rw [hr]
  have hwPW : w' ∈ (PW : Subgroup (↥R)) := by
    simpa [PW] using (Subgroup.mem_subgroupOf).2 hwW'
  have hwsmul : w' • PW = PW := by
    apply (Sylow.smul_eq_iff_mem_normalizer).2
    exact (Subgroup.le_normalizer (H := (PW : Subgroup (↥R)))) hwPW
  have hr2 : PWb = l' • PW := by
    calc
      PWb = (r⁻¹ : ↥R) • PW := hr1
      _ = (l' * w') • PW := by rw [hlr]
      _ = l' • (w' • PW) := by rw [mul_smul]
      _ = l' • PW := by rw [hwsmul]
  have hl1 : (l'⁻¹ : ↥R) • PWb = PW := by
    calc
      (l'⁻¹ : ↥R) • PWb = (l'⁻¹ : ↥R) • (l' • PW) := by rw [hr2]
      _ = ((l'⁻¹ : ↥R) * l') • PW := by rw [← mul_smul]
      _ = PW := by
        rw [inv_mul_cancel]
        simp
  -- In the paper's convention, d := l conjugates Wb into W'.
  have hMain : ∀ z : G, z ∈ Wb → l⁻¹ * z * l ∈ W' := by
    intro z hz
    let z' : ↥R := ⟨z, hWbR hz⟩
    have hzPWb : z' ∈ (PWb : Subgroup (↥R)) := by
      simpa [PWb] using (Subgroup.mem_subgroupOf).2 hz
    have hzsmul : (MulAut.conj (l'⁻¹)) z' ∈
        (MulAut.conj (l'⁻¹) • (PWb : Subgroup (↥R))) :=
      Subgroup.smul_mem_pointwise_smul z' (MulAut.conj (l'⁻¹)) (PWb : Subgroup (↥R)) hzPWb
    have hzPW : (MulAut.conj (l'⁻¹)) z' ∈ (PW : Subgroup (↥R)) := by
      have hsmul : (↑(l'⁻¹ • PWb : Sylow p (↥R)) : Subgroup (↥R)) = (PW : Subgroup (↥R)) := by
        simpa using (congrArg (fun X : Sylow p (↥R) => (X : Subgroup (↥R))) hl1)
      have hsmul' : (MulAut.conj (l'⁻¹) • (PWb : Subgroup (↥R)) : Subgroup (↥R)) =
          (PW : Subgroup (↥R)) := by
        simpa [Sylow.coe_subgroup_smul] using hsmul
      exact hsmul' ▸ hzsmul
    have hmem : ((MulAut.conj (l'⁻¹)) z' : G) ∈ W' := (Subgroup.mem_subgroupOf).mp hzPW
    have hzG : ((MulAut.conj (l'⁻¹)) z' : G) = l⁻¹ * z * l := by
      rw [MulAut.conj_apply]
      simp only [inv_inv]
      rfl
    rw [← hzG]
    exact hmem
  -- For x ∈ W': x^{b·l} ∈ W' and x⁻¹·x^{b·l} ∈ N, hence x^{b·l} = x.
  have hxbd : ∀ x : G, x ∈ W' → (b * l)⁻¹ * x * (b * l) ∈ W' := by
    intro x hx
    have hz : b⁻¹ * x * b ∈ Wb := by
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
    have hm := hMain (b⁻¹ * x * b) hz
    simpa [mul_assoc, mul_inv_rev] using hm
  have hcong : ∀ x : G, x ∈ W' → x⁻¹ * ((b * l)⁻¹ * x * (b * l)) ∈ N := by
    intro x hx
    have h1 : x⁻¹ * (b⁻¹ * x * b) ∈ N := by
      have h1a : x⁻¹ * b⁻¹ * x ∈ N :=
        Subgroup.Normal.conj_mem' hN (b⁻¹) (Subgroup.inv_mem N hbN) x
      simpa [mul_assoc] using (Subgroup.mul_mem N h1a hbN)
    have h2 : (b⁻¹ * x * b)⁻¹ * (l⁻¹ * (b⁻¹ * x * b) * l) ∈ N := by
      have h2a : (b⁻¹ * x * b)⁻¹ * l⁻¹ * (b⁻¹ * x * b) ∈ N :=
        Subgroup.Normal.conj_mem' hN (l⁻¹) (Subgroup.inv_mem N (hL_le_N hlL)) (b⁻¹ * x * b)
      simpa [mul_assoc] using (Subgroup.mul_mem N h2a (hL_le_N hlL))
    have hcomb : x⁻¹ * ((b * l)⁻¹ * x * (b * l)) =
        (x⁻¹ * (b⁻¹ * x * b)) * ((b⁻¹ * x * b)⁻¹ * (l⁻¹ * (b⁻¹ * x * b) * l)) := by
      rw [mul_inv_rev]
      group
    rw [hcomb]
    exact Subgroup.mul_mem N h1 h2
  have hx1 : ∀ x : G, x ∈ W' → x⁻¹ * ((b * l)⁻¹ * x * (b * l)) = 1 := by
    intro x hx
    exact (Subgroup.disjoint_def.mp hW'N_disj)
      (Subgroup.mul_mem W' (Subgroup.inv_mem W' hx) (hxbd x hx)) (hcong x hx)
  have hxeq : ∀ x : G, x ∈ W' → (b * l)⁻¹ * x * (b * l) = x := by
    intro x hx
    exact (inv_mul_eq_one.mp (hx1 x hx)).symm
  have hc : ∀ x : G, x ∈ W' → x * (b * l) = (b * l) * x := by
    intro x hx
    calc
      x * (b * l) = (b * l) * ((b * l)⁻¹ * x * (b * l)) := by group
      _ = (b * l) * x := by rw [hxeq x hx]
  -- Conclusion: c = b·l, h = l⁻¹·k.
  refine ⟨b * l, Subgroup.mul_mem N hbN (hL_le_N hlL), ?_, l⁻¹ * k, ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff).2 (fun x hx => hc x hx)
  · exact Subgroup.mul_mem H (Subgroup.inv_mem H (hRH (hLR hlL))) hkH
  · calc
      g = b * k := hbk.symm
      _ = (b * l) * (l⁻¹ * k) := by group

end CFSG.Glauberman

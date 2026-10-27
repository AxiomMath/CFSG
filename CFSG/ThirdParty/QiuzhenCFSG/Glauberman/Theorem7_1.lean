module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma7_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Theorem 7.1

This file proves Theorem 7.1 of [6] (Glauberman, *A Characteristic Subgroup of a p-Stable
Group*, Canad. J. Math. 20 (1968), 1101–1135), following the validated transcription in
`refs/glauberman-p-stable.tex` L1874–L1970:

> **Theorem 7.1.**  Let `G` be a finite group, `p` a prime, and `K` a characteristic functor.
> Suppose that `S` is a Sylow `p`-subgroup of `G`.  Assume that `G` satisfies `(C_p)` and
> that every element of `M_p(G)` satisfies `(F_p)`.  Then, for every non-identity subgroup
> `W` of `S`,
> \[
>   N(W)=O_{p'}(N(W))\bigl(N(W)\cap N(K(S))\bigr).
> \]

Here `(F_p)` is the condition of the paper (L1865–L1872): `G = O_{p'}(G)N_G(K(S))` for
every Sylow `p`-subgroup `S` of `G`, formalized in its join form (equivalent because
`O_{p'}(G) ⊴ G`):

* `SatisfiesFp p K G := ∀ S : Sylow p G, pPrimeCore p G ⊔ N_G(K(S)) = ⊤`.

The conclusion `N(W) = O_{p'}(N(W))·(N(W) ∩ N(K(S)))` is formalized as an equality of
subgroups of `G`: with `N = N_G(W)`, the right-hand side is `O_{p'}(N)` mapped into `G`
through `N.subtype`, joined with `N ∩ N_G(K(S))`:

* `Subgroup.normalizer (W : Set G) =
   (pPrimeCore p ↥N).map N.subtype ⊔ (N ⊓ Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G))`.

## Proof route (paper L1874–L1970)

1. `W ≤ N = N_G(W)` and `W ⊴ N`; as `W` is a non-trivial `p`-subgroup of `N`, `O_p(N) ≠ 1`.
2. Extend `N` to an element `M₀ ∈ M_p(G)` with `N ≤ M₀` (finite maximality), so the set
   `𝒮` of `M ∈ M_p(G)` satisfying `(7.1)` (`W ≤ M` and `N = L·(N∩M)`, `L = O_{p'}(N)`) is
   non-empty; choose `M ∈ 𝒮` with `|M|_p` maximal.
3. Let `T ∈ Syl_p M` with `W ≤ T`.  By `(F_p)` for `M` and Lemma 7.1 (applied inside `M`),
   `N ∩ M = (O_{p'}(M) ∩ C(W))·N_{N∩M}(K(T))` — (7.2).
4. `O_{p'}(M) ∩ C(W) ≤ L`: it is normal in `N ∩ M`; hence `L·(O_{p'}(M) ∩ C(W))` is a
   normal `p'`-subgroup of `N` containing `L`, so it equals `L` (the `p'`-core is the
   largest normal `p'`-subgroup).  Consequently `N = L·N_{N∩M}(K(T))` — (7.3).
5. Choose `M₁ ∈ M_p(G)` containing `N_G(K(T))` (possible since `K(T) ≠ 1` is a normal
   `p`-subgroup of its own normalizer); `M₁` satisfies (7.1), so by maximality of `M`
   and the Sylow-counting chain
   `|T| = |M|_p ≥ |M₁|_p ≥ |N_G(K(T))|_p ≥ |N_G(T)|_p ≥ |T|`
   one gets `T ∈ Syl_p(N_G(T))`; by Sylow's theorem `T ∈ Syl_p G`.
6. Take `g ∈ G` with `T^g = S`; then `W^g ⊆ S`; by `(C_p)`, `g = cn` with `c ∈ C(W)`,
   `n ∈ N_G(K(S))`.  The conjugation chain `K(T)^c = K(S)` and `N^c = N` give
   `N = L·N(K(S)) = O_{p'}(N)·(N ∩ N(K(S)))`, the desired equality.

**Registered bridges.**  The paper's characteristic functor satisfies property (c) of
L1139–L1145: *if `φ` is an isomorphism of `P` onto `Q`, then `φ(K(P)) = K(Q)`*.  The
landed structure `CharacteristicFunctor` records only the conjugation-invariance axiom
`K_conj`; the full isomorphism-invariance is needed exactly once in the proof: to
identify `K(T)` computed inside the ambient group `M` with `K(T)` computed in `G` (via
the canonical isomorphism `T ≃ T.map M.subtype`) — this is what makes `N_G(T) ≤
N_G(K(T))` (used in the Sylow-counting chain) and the final conjugation step
`K(T)^c = K(S)` valid.  This is registered as the bridge
`characteristicFunctor_map_subtype`.

All other steps are proved in full (the `M_p`-maximality choice and the Sylow counting are
carried out using the `p`-part `pPart p n = p ^ padicValNat p n` of the orders).
-/

open scoped Pointwise

namespace CFSG.Glauberman

universe u

set_option maxHeartbeats 800000

/-! ## Local infrastructure: the `p`-part of a natural number -/

/-- The `p`-part `p ^ padicValNat p n` of a natural number `n`. -/
private def pPart (p n : ℕ) : ℕ := p ^ padicValNat p n

/-- The `p`-part is monotone under divisibility (for non-zero `b`). -/
private lemma pPart_mono {p : ℕ} [Fact p.Prime] {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    pPart p a ≤ pPart p b := by
  have ha : a ≠ 0 := by
    intro ha
    exact hb (by simpa [ha] using hab)
  unfold pPart
  have hv : padicValNat p a ≤ padicValNat p b := by
    rw [← padicValNat_dvd_iff_le (a := b) hb]
    exact dvd_trans (pow_padicValNat_dvd (p := p) (n := a)) hab
  exact pow_le_pow_right₀ (by exact (Nat.Prime.one_le (Fact.out : Nat.Prime p))) hv

/-- The `p`-part of the order of a finite group equals the order of any Sylow `p`-subgroup. -/
private lemma pPart_card_eq_card_of_sylow {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (T : Sylow p G) : pPart p (Nat.card G) = Nat.card T := by
  classical
  have hTp : IsPGroup p (T : Subgroup G) := T.isPGroup'
  obtain ⟨n, hn⟩ := hTp.exists_card_eq
  have hnot : ¬ p ∣ (T : Subgroup G).index := Sylow.not_dvd_index (P := T)
  have hTcard_ne : Nat.card (↥(T : Subgroup G)) ≠ 0 :=
    ne_of_gt (Nat.card_pos (α := ↥(T : Subgroup G)))
  have hTindex_ne : (T : Subgroup G).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite (H := (T : Subgroup G))
  have hcard : Nat.card (↥(T : Subgroup G)) * (T : Subgroup G).index = Nat.card G := by
    simp
  have hv : padicValNat p (Nat.card G) = n := by
    rw [← hcard]
    rw [padicValNat.mul hTcard_ne hTindex_ne]
    rw [hn]
    rw [padicValNat.prime_pow]
    rw [padicValNat.eq_zero_of_not_dvd hnot]
    rw [add_zero]
  unfold pPart
  rw [hv]
  exact hn.symm

/-! ## Local infrastructure: the normalizer grows in a finite `p`-group -/

/-- A proper subgroup of a finite `p`-group is properly contained in its normalizer
(Gorenstein, *Finite Groups*, Theorem 2.7). -/
private lemma normalizer_lt_of_lt_of_isPGroup {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {H : Subgroup P} (hH : H < ⊤) :
    H < Subgroup.normalizer (H : Set P) := by
  classical
  have htop : IsPGroup p (⊤ : Subgroup P) :=
    IsPGroup.of_equiv (hG := hP) (Subgroup.topEquiv (G := P)).symm
  have hHp : IsPGroup p H := htop.to_le hH.le
  -- H acts on the left cosets P ⧸ H; the fixed points are the cosets of N_G(H).
  have hmod : Nat.card (P ⧸ H) ≡ Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) [MOD p] :=
    hHp.card_modEq_card_fixedPoints (α := P ⧸ H)
  have htotal : p ∣ Nat.card (P ⧸ H) := by
    rw [← Subgroup.index_eq_card]
    have hindex_ne_one : H.index ≠ 1 := by
      intro h1
      exact hH.ne' (Subgroup.index_eq_one.mp h1).symm
    rcases (hP.index H) with ⟨k, hk⟩
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hindex_ne_one
      simp [hk, hk0]
    rw [hk]
    exact dvd_pow_self p hk0
  have hfixed : p ∣ Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) :=
    Nat.modEq_zero_iff_dvd.mp ((hmod.symm).trans htotal.modEq_zero_nat)
  have hfixed_card : Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) =
      (H.comap (Subgroup.normalizer (H : Set P)).subtype).index := by
    calc
      Nat.card (MulAction.fixedPoints (↥H) (P ⧸ H)) =
          Nat.card (Subgroup.normalizer (H : Set P) ⧸
            H.comap (Subgroup.normalizer (H : Set P)).subtype) := by
            exact Nat.card_congr
              (Sylow.fixedPointsMulLeftCosetsEquivQuotient (H := H))
      _ = (H.comap (Subgroup.normalizer (H : Set P)).subtype).index := by
            rw [Subgroup.index_eq_card]
  have hfixed' : p ∣ (H.subgroupOf (Subgroup.normalizer (H : Set P))).index := by
    simpa [hfixed_card, Subgroup.comap_subtype] using hfixed
  have hindex_ne_one : (H.subgroupOf (Subgroup.normalizer (H : Set P))).index ≠ 1 := by
    intro h1
    have : p ∣ (1 : ℕ) := by
      simpa [h1] using hfixed'
    exact (Nat.Prime.not_dvd_one (Fact.out : Nat.Prime p)) this
  refine lt_of_le_of_ne H.le_normalizer ?_
  intro heq
  apply hindex_ne_one
  rw [← heq]
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.index_top

/-- A Sylow `p`-subgroup of its own normalizer is a Sylow `p`-subgroup of `G`
(Sylow's theorem; cf. [6, §7, proof of Theorem 7.1]). -/
private lemma isSylow_of_sylow_normalizer {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] {T : Subgroup G} (hTp : IsPGroup p T)
    (TN : Sylow p ↥(Subgroup.normalizer (T : Set G)))
    (hTN_eq : (TN : Subgroup ↥(Subgroup.normalizer (T : Set G))) =
      T.subgroupOf (Subgroup.normalizer (T : Set G))) :
    ∃ S : Sylow p G, (S : Subgroup G) = T := by
  classical
  obtain ⟨S, hTS⟩ := hTp.exists_le_sylow
  refine ⟨S, ?_⟩
  apply le_antisymm
  · by_contra hnot
    -- hnot : ¬ (S : Subgroup G) ≤ T; with T ≤ S this is a strict inclusion.
    have hlt : T < (S : Subgroup G) := lt_of_le_of_ne hTS (by
      intro heq
      apply hnot
      rw [heq])
    let H : Subgroup ↥(S : Subgroup G) := T.subgroupOf (S : Subgroup G)
    have hHlt : H < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      exact hlt.ne' (by
        calc
          (S : Subgroup G) = (⊤ : Subgroup ↥(S : Subgroup G)).map (S : Subgroup G).subtype := by
            simpa using (Subgroup.subgroupOf_map_subtype (H := (S : Subgroup G)) (K := (S : Subgroup G))).symm
          _ = (T.subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype := by
            simpa [H] using congrArg
              (fun X : Subgroup ↥(S : Subgroup G) => X.map (S : Subgroup G).subtype) htop.symm
          _ = T := by
            exact (Subgroup.map_subgroupOf_eq_of_le hTS))
    have hHp : IsPGroup p (↥(S : Subgroup G)) := S.isPGroup'
    have hgrowth := normalizer_lt_of_lt_of_isPGroup (P := ↥(S : Subgroup G)) (p := p) hHp hHlt
    -- N_{S}(H) = (N_G(T) ∩ S).subgroupOf S
    have hnorm : Subgroup.normalizer (H : Set ↥(S : Subgroup G)) =
        ((Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G)).subgroupOf (S : Subgroup G) := by
      have h : (Subgroup.normalizer (T : Set G)).subgroupOf (S : Subgroup G) =
          Subgroup.normalizer (T.subgroupOf (S : Subgroup G)) :=
        Subgroup.subgroupOf_normalizer_eq (H := T) (N := (S : Subgroup G)) hTS
      simpa [H, Subgroup.inf_subgroupOf_right] using h.symm
    -- Q is the p-subgroup of N_G(T) corresponding to N_G(T) ∩ S
    let Q : Subgroup ↥(Subgroup.normalizer (T : Set G)) :=
      ((Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G)).subgroupOf (Subgroup.normalizer (T : Set G))
    have hQp : IsPGroup p Q := by
      have hXp : IsPGroup p (((Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G)) : Subgroup G) := by
        apply IsPGroup.to_le (hK := S.isPGroup')
        exact inf_le_right
      exact IsPGroup.of_equiv (hG := hXp)
        (Subgroup.subgroupOfEquivOfLe (show (Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G) ≤
          Subgroup.normalizer (T : Set G) from inf_le_left)).symm
    have hQleT : (T.subgroupOf (Subgroup.normalizer (T : Set G)) : Subgroup ↥(Subgroup.normalizer (T : Set G))) ≤ Q := by
      intro x hx
      dsimp [Q]
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨Subgroup.le_normalizer hx, hTS hx⟩
    have hQeq := (TN.is_maximal' hQp (by simpa [hTN_eq] using hQleT))
    -- N_G(T) ∩ S = T
    have hXeq : (Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G) = T := by
      calc
        (Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G) =
            (((Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G)).subgroupOf
              (Subgroup.normalizer (T : Set G))).map (Subgroup.normalizer (T : Set G)).subtype := by
          rw [Subgroup.subgroupOf_map_subtype]
          exact (inf_eq_left.mpr (show (Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G) ≤
            Subgroup.normalizer (T : Set G) from inf_le_left)).symm
        _ = Q.map (Subgroup.normalizer (T : Set G)).subtype := by
          rfl
        _ = (T.subgroupOf (Subgroup.normalizer (T : Set G))).map
            (Subgroup.normalizer (T : Set G)).subtype := by
              rw [hQeq, hTN_eq]
        _ = T := by
              exact (Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer)
    -- contradiction with the growth of H
    have hne : H ≠ Subgroup.normalizer (H : Set ↥(S : Subgroup G)) := ne_of_lt hgrowth
    apply hne
    rw [hnorm]
    change (T.subgroupOf (S : Subgroup G)) =
      ((Subgroup.normalizer (T : Set G)) ⊓ (S : Subgroup G)).subgroupOf (S : Subgroup G)
    rw [hXeq]
  · exact hTS

/-! ## Condition `(F_p)` -/

variable {G : Type u} [Group G]

/-- Condition `(F_p)` of [6, §7, L1865–L1872] for a finite group `G`, a characteristic
functor `K` and a prime `p`: `G = O_{p'}(G)·N_G(K(S))` for every Sylow `p`-subgroup `S`
of `G`, in join form (equivalent to the product form since `O_{p'}(G) ⊴ G`). -/
@[expose]
public def SatisfiesFp (p : ℕ) [Fact p.Prime] (K : CharacteristicFunctor p)
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ S : Sylow p G,
    pPrimeCore p G ⊔ Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G) = ⊤

/-! ## The characteristic functor commutes with subgroup embeddings -/

/-- Paper property (c) of the characteristic functor
(`refs/glauberman-p-stable.tex` L1139–L1145): *if `φ` is an isomorphism of `P` onto `Q`,
then `φ(K(P)) = K(Q)`*.  The landed structure `CharacteristicFunctor` (`Theorem5_1.lean`)
records this as `K_map`; it is needed once in the proof of Theorem 7.1: for a subgroup
`H ≤ G` and a subgroup `U` of `H`, the
canonical isomorphism `↥U ≃* ↥(U.map H.subtype)` identifies `K(U)` computed in the
ambient group `H` with `K(U.map H.subtype)` computed in `G`:

`(K.K (G := ↥H) U).map H.subtype = K.K (G := G) (U.map H.subtype)`.

This is what licenses `N_G(T) ≤ N_G(K(T))` (Sylow-counting chain in the proof of Theorem
7.1) and the final conjugation step `K(T)^c = K(S)` for `c ∉ M`. -/
public theorem characteristicFunctor_map_subtype {p : ℕ} (K : CharacteristicFunctor p)
    (H0 : Subgroup G) (U : Subgroup H0) :
    (K.K (H := ↥H0) (U : Subgroup H0) : Subgroup ↥H0).map H0.subtype =
      K.K (H := G) (U.map H0.subtype) := by
  exact (K.K_map H0.subtype U
    (H0.subtype_injective.comp U.subtype_injective)).symm

/-! ## Theorem 7.1 -/

/-- **Theorem 7.1** ([6], §7; `refs/glauberman-p-stable.tex` L1874–L1970): if the finite
group `G` satisfies `(C_p)` and every element of `M_p(G)` satisfies `(F_p)`, then for
every non-identity subgroup `W` of the Sylow `p`-subgroup `S`,

`N_G(W) = O_{p'}(N_G(W))·(N_G(W) ∩ N_G(K(S)))`,

formalized as an equality of subgroups of `G` (the `p'`-core of `N_G(W)` is mapped into
`G` through `N_G(W).subtype`). -/
public theorem theorem7_1 [Finite G] (p : ℕ) [Fact p.Prime]
    (K : CharacteristicFunctor p) (S : Sylow p G)
    (hCp : SatisfiesCp K G) (hFp : ∀ M : Subgroup G, M ∈ MpSet p G → SatisfiesFp p K (↥M)) :
    ∀ W : Subgroup G, W ≤ (S : Subgroup G) → W ≠ ⊥ →
      Subgroup.normalizer (W : Set G) =
        (pPrimeCore p (↥(Subgroup.normalizer (W : Set G)))).map
            (Subgroup.normalizer (W : Set G)).subtype ⊔
          (Subgroup.normalizer (W : Set G) ⊓
            Subgroup.normalizer ((K.K (S : Subgroup G) : Subgroup G) : Set G)) := by
  classical
  intro W hWleS hWne
  let N : Subgroup G := Subgroup.normalizer (W : Set G)
  let L : Subgroup G := (pPrimeCore p ↥N).map N.subtype
  -- basic facts
  have hWp : IsPGroup p W := IsPGroup.to_le S.isPGroup' hWleS
  have hWN : W ≤ N := Subgroup.le_normalizer (H := W)
  have hL_le_N : L ≤ N := by
    intro x hx
    rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, rfl⟩
    exact y.property
  -- Step 1: W ≤ O_p(N), hence O_p(N) ≠ 1
  let WN : Subgroup ↥N := W.subgroupOf N
  have hWNp : IsPGroup p WN :=
    IsPGroup.of_equiv (hG := hWp) (Subgroup.subgroupOfEquivOfLe hWN).symm
  have hWNne : WN ≠ ⊥ := by
    intro hbot
    apply hWne
    calc
      W = WN.map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hWN).symm
      _ = (⊥ : Subgroup ↥N).map N.subtype := by rw [hbot]
      _ = ⊥ := by simp
  have hOpN : pCore p ↥N ≠ ⊥ := by
    intro hbot
    apply hWNne
    have hle : WN ≤ pCore p ↥N := le_sSup ⟨(inferInstance : WN.Normal), hWNp⟩
    exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
  -- Step 2: some M₀ ∈ M_p(G) with N ≤ M₀
  let 𝒯 : Set (Subgroup G) := {K : Subgroup G | N ≤ K ∧ pCore p (↥K) ≠ ⊥}
  have h𝒯ne : 𝒯.Nonempty := ⟨N, ⟨le_rfl, hOpN⟩⟩
  have h𝒯fin : 𝒯.Finite := Set.toFinite 𝒯
  obtain ⟨M₀, hM₀max⟩ := h𝒯fin.exists_maximalFor (fun K : Subgroup G => Nat.card (↥K)) 𝒯 h𝒯ne
  have hM₀𝒯 : M₀ ∈ 𝒯 := hM₀max.1
  have hM₀Mp : M₀ ∈ MpSet p G := by
    refine ⟨hM₀𝒯.2, ?_⟩
    intro K hKp hM₀K
    have hK𝒯 : K ∈ 𝒯 := ⟨le_trans hM₀𝒯.1 hM₀K, hKp⟩
    exact (Subgroup.eq_of_le_of_card_ge hM₀K (hM₀max.2 hK𝒯 (Subgroup.card_le_of_le hM₀K))).symm
  -- Step 3: the set 𝒮 of (7.1)-satisfiers and the maximal M
  let 𝒮 : Set (Subgroup G) := {K : Subgroup G | K ∈ MpSet p G ∧ W ≤ K ∧ L ⊔ (N ⊓ K) = N}
  have h𝒮ne : 𝒮.Nonempty := ⟨M₀, hM₀Mp, hWN.trans hM₀𝒯.1, by
    calc
      L ⊔ (N ⊓ M₀) = L ⊔ N := by rw [inf_eq_left.2 hM₀𝒯.1]
      _ = N := sup_eq_right.2 hL_le_N⟩
  have h𝒮fin : 𝒮.Finite := Set.toFinite 𝒮
  obtain ⟨M, hMmax⟩ := h𝒮fin.exists_maximalFor (fun K : Subgroup G => pPart p (Nat.card (↥K))) 𝒮 h𝒮ne
  have hM𝒮 : M ∈ 𝒮 := hMmax.1
  have hMMp : M ∈ MpSet p G := hM𝒮.1
  have hWM : W ≤ M := hM𝒮.2.1
  have h71M : L ⊔ (N ⊓ M) = N := hM𝒮.2.2
  have hMmax' : ∀ K : Subgroup G, K ∈ MpSet p G → W ≤ K → L ⊔ (N ⊓ K) = N →
      pPart p (Nat.card (↥K)) ≤ pPart p (Nat.card (↥M)) := by
    intro K hK1 hK2 hK3
    exact hMmax.le ⟨hK1, hK2, hK3⟩
  -- Step 4: T ∈ Syl_p M with W ≤ T
  let WM : Subgroup ↥M := W.subgroupOf M
  have hWMp : IsPGroup p WM :=
    IsPGroup.of_equiv (hG := hWp) (Subgroup.subgroupOfEquivOfLe hWM).symm
  obtain ⟨T, hWT⟩ := hWMp.exists_le_sylow
  let T' : Subgroup G := (T : Subgroup ↥M).map M.subtype
  have hWleT' : W ≤ T' := by
    calc
      W = WM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hWM).symm
      _ ≤ T' := Subgroup.map_mono (f := M.subtype) hWT
  let KM : Subgroup ↥M := K.K (H := ↥M) (T : Subgroup ↥M)
  let K' : Subgroup G := KM.map M.subtype
  have hK' : K' = K.K (H := G) T' := by
    exact characteristicFunctor_map_subtype K M (T : Subgroup ↥M)
  -- (F_p) for M applied to T
  have hFpT : pPrimeCore p ↥M ⊔
      Subgroup.normalizer ((K.K (H := ↥M) (T : Subgroup ↥M) : Subgroup ↥M) : Set ↥M) = ⊤ := by
    exact hFp M hMMp T
  -- Step 5: Lemma 7.1 inside M
  let Hm : Subgroup ↥M :=
    Subgroup.normalizer ((K.K (H := ↥M) (T : Subgroup ↥M) : Subgroup ↥M) : Set ↥M)
  have hWmH : WM ≤ Hm := hWT.trans (sylow_le_normalizer_K (G := ↥M) K T)
  let WH : Subgroup Hm := WM.subgroupOf Hm
  have hWHp : IsPGroup p WH :=
    IsPGroup.of_equiv (hG := hWMp) (Subgroup.subgroupOfEquivOfLe hWmH).symm
  -- (7.2) decomposition: every g ∈ N ∩ M is c·h with c ∈ O_{p'}(M) ∩ C(W), h ∈ N_{N∩M}(K(T))
  have h72 : ∀ g : G, g ∈ (N ⊓ M : Subgroup G) →
      ∃ c h : G,
        c ∈ (pPrimeCore p ↥M).map M.subtype ∧ c ∈ Subgroup.centralizer (W : Set G) ∧
        h ∈ (N ⊓ M) ⊓ Subgroup.normalizer (K' : Set G) ∧ g = c * h := by
    intro g hgNM
    have hgN : g ∈ N := (Subgroup.mem_inf.mp hgNM).1
    have hgM : g ∈ M := (Subgroup.mem_inf.mp hgNM).2
    let gm : ↥M := ⟨g, hgM⟩
    have hghyp : ∀ w : WH, (gm : ↥M)⁻¹ * (w : ↥M) * (gm : ↥M) ∈ Hm := by
      intro w
      have hwWM : ((w : ↥Hm) : ↥M) ∈ WM := (Subgroup.mem_subgroupOf).1 w.2
      have hwWG : (w : G) ∈ W := by
        exact (Subgroup.mem_subgroupOf).1 (by simpa using hwWM)
      refine hWmH ?_
      dsimp [WM]
      rw [Subgroup.mem_subgroupOf]
      exact ((Subgroup.mem_normalizer_iff'').mp hgN (w : G)).mp hwWG
    rcases (lemma7_1 (G := ↥M) (H := Hm) (hGH := hFpT) (W := WH) (hWp := hWHp) (g := gm)
      hghyp) with ⟨c, hcCore, hcCent, h, hhH, hgh⟩
    refine ⟨(c : G), (h : G), ?_, ?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨c, hcCore, rfl⟩
    · -- c ∈ C_G(W)
      rw [Subgroup.mem_centralizer_iff]
      intro x hxW
      have hxWM : (⟨x, hWM hxW⟩ : ↥M) ∈ WM := (Subgroup.mem_subgroupOf).2 hxW
      have hmap : (WH.map Hm.subtype : Subgroup ↥M) = WM :=
        Subgroup.map_subgroupOf_eq_of_le hWmH
      have hc' := (Subgroup.mem_centralizer_iff.mp hcCent) (⟨x, hWM hxW⟩ : ↥M) (by simpa [hmap] using hxWM)
      simpa [hmap] using congrArg (fun y : ↥M => (y : G)) hc'
    · -- h ∈ (N ⊓ M) ⊓ normalizer (K' : Set G)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- h ∈ N: h = c⁻¹·g
        have hcN : (c : G) ∈ N :=
          (Subgroup.centralizer_le_normalizer (W : Set G)) (by
            rw [Subgroup.mem_centralizer_iff]
            intro x hxW
            have hxWM : (⟨x, hWM hxW⟩ : ↥M) ∈ WM := (Subgroup.mem_subgroupOf).2 hxW
            have hmap : (WH.map Hm.subtype : Subgroup ↥M) = WM :=
              Subgroup.map_subgroupOf_eq_of_le hWmH
            have hc' := (Subgroup.mem_centralizer_iff.mp hcCent) (⟨x, hWM hxW⟩ : ↥M) (by simpa [hmap] using hxWM)
            simpa [hmap] using congrArg (fun y : ↥M => (y : G)) hc')
        have hh_eq : (h : G) = (c : G)⁻¹ * g := by
          have h' := congrArg (fun y : ↥M => (y : G)) hgh
          have hh : (c : G) * (h : G) = g := h'.symm
          calc
            (h : G) = (c : G)⁻¹ * ((c : G) * (h : G)) := by group
            _ = (c : G)⁻¹ * g := by rw [hh]
        rw [hh_eq]
        exact Subgroup.mul_mem N (Subgroup.inv_mem N hcN) hgN
      · -- h ∈ M
        exact (h : ↥M).property
      · -- h normalizes K' in G
        change (h : G) ∈ Subgroup.normalizer (K' : Set G)
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          rcases (Subgroup.mem_map.mp hx) with ⟨y, hyKM, rfl⟩
          refine Subgroup.mem_map.mpr ⟨(h : ↥M) * y * (h : ↥M)⁻¹, ?_, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp hhH y).1 hyKM
          · simp [mul_assoc]
        · intro hx
          rcases (Subgroup.mem_map.mp hx) with ⟨y, hyKM, hyx⟩
          have hyh : (h : ↥M)⁻¹ * y * (h : ↥M) ∈ KM := by
            simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem Hm hhH) y).1 hyKM
          have hxeq : x = (h : G)⁻¹ * (y : G) * (h : G) := by
            calc
              x = (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * (h : G) := by group
              _ = (h : G)⁻¹ * (y : G) * (h : G) := by
                have hyx' : (y : G) = (h : G) * x * (h : G)⁻¹ := by
                  simpa [Subgroup.coe_subtype] using hyx
                rw [hyx']
          rw [hxeq]
          refine Subgroup.mem_map.mpr ⟨(h : ↥M)⁻¹ * y * (h : ↥M), hyh, ?_⟩
          · simp [Subgroup.coe_subtype, mul_assoc]
    · -- g = c·h in G
      exact congrArg (fun y : ↥M => (y : G)) hgh
  -- (7.2): N ⊓ M = A ⊔ B
  let A0 : Subgroup G := (pPrimeCore p ↥M).map M.subtype
  let CW : Subgroup G := Subgroup.centralizer (W : Set G)
  let A : Subgroup G := A0 ⊓ CW
  let B : Subgroup G := (N ⊓ M) ⊓ Subgroup.normalizer (K' : Set G)
  have hA_le_NM : A ≤ N ⊓ M := by
    refine le_inf ?_ ?_
    · exact (inf_le_right.trans (Subgroup.centralizer_le_normalizer (W : Set G)))
    · exact (inf_le_left.trans (Subgroup.map_subtype_le (H := M) (K := pPrimeCore p ↥M)))
  have hB_le_NM : B ≤ N ⊓ M := inf_le_left
  have h72' : N ⊓ M = A ⊔ B := by
    apply le_antisymm
    · intro g hgNM
      rcases h72 g hgNM with ⟨c, h, hcA0, hcCW, hhB, hgh⟩
      refine (hgh ▸ ?_)
      exact Subgroup.mul_mem (A ⊔ B) (Subgroup.mem_sup_left ⟨hcA0, hcCW⟩)
        (Subgroup.mem_sup_right hhB)
    · exact sup_le hA_le_NM hB_le_NM
  -- A ≤ L (the p'-group argument)
  have hL_normal : (L.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hL_le_N]
    intro a x haL hxN
    rcases (Subgroup.mem_map.mp haL) with ⟨p0, hp0, rfl⟩
    have hxp : x * (p0 : G) * x⁻¹ ∈ (pPrimeCore p ↥N).map N.subtype := by
      refine Subgroup.mem_map.mpr ⟨(⟨x, hxN⟩ : ↥N) * p0 * (⟨x, hxN⟩ : ↥N)⁻¹, ?_, ?_⟩
      · exact (pPrimeCore_normal (p := p) (G := ↥N)).conj_mem p0 hp0 (⟨x, hxN⟩ : ↥N)
      · simp [mul_assoc]
    exact hxp
  have hA_normal : (A.subgroupOf (N ⊓ M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA_le_NM]
    intro x k hxA hkNM
    rcases (Subgroup.mem_inf.mp hxA) with ⟨hxA0, hxCW⟩
    refine ⟨?_, ?_⟩
    · -- k·x·k⁻¹ ∈ A0 = (pPrimeCore p ↥M).map M.subtype
      rcases (Subgroup.mem_map.mp hxA0) with ⟨y, hyCore, rfl⟩
      refine Subgroup.mem_map.mpr ⟨(⟨k, (Subgroup.mem_inf.mp hkNM).2⟩ : ↥M) * y * (⟨k, (Subgroup.mem_inf.mp hkNM).2⟩ : ↥M)⁻¹, ?_, ?_⟩
      · exact (pPrimeCore_normal (p := p) (G := ↥M)).conj_mem y hyCore (⟨k, (Subgroup.mem_inf.mp hkNM).2⟩ : ↥M)
      · simp [mul_assoc]
    · -- k·x·k⁻¹ ∈ CW
      have hk_normalizes : k ∈ Subgroup.normalizer (W : Set G) :=
        (Subgroup.mem_inf.mp hkNM).1
      rw [Subgroup.mem_centralizer_iff] at hxCW
      change k * x * k⁻¹ ∈ CW
      dsimp [CW]
      rw [Subgroup.mem_centralizer_iff]
      intro w hwW
      have hkwk : (k * x * k⁻¹) * w = k * (x * (k⁻¹ * w * k)) * k⁻¹ := by group
      have hcomm : x * (k⁻¹ * w * k) = (k⁻¹ * w * k) * x :=
        (hxCW (k⁻¹ * w * k) (by
          exact ((Subgroup.mem_normalizer_iff'').mp hk_normalizes (w : G)).1 hwW)).symm
      rw [hkwk, hcomm]
      group
  -- A ≤ L: the p'-core maximality argument, carried out inside N
  let L' : Subgroup ↥N := pPrimeCore p ↥N
  let NM' : Subgroup ↥N := (N ⊓ M).subgroupOf N
  let A' : Subgroup ↥N := A.subgroupOf N
  have hL'normal : L'.Normal := pPrimeCore_normal (p := p) (G := ↥N)
  have hA'_le_NM' : A' ≤ NM' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hA_le_NM hx
  have hA'_normal : (A'.subgroupOf NM').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA'_le_NM']
    intro a x haA' hxNM'
    rw [Subgroup.mem_subgroupOf] at haA' hxNM'
    change (x : G) * (a : G) * (x : G)⁻¹ ∈ A
    exact (Subgroup.normal_subgroupOf_iff hA_le_NM).1 hA_normal (a : G) (x : G) haA' hxNM'
  -- (7.1) inside N: L' ⊔ NM' = ⊤
  have htop' : L' ⊔ NM' = ⊤ := by
    apply Subgroup.map_injective (f := N.subtype) N.subtype_injective
    calc
      (L' ⊔ NM').map N.subtype = L'.map N.subtype ⊔ NM'.map N.subtype :=
        Subgroup.map_sup L' NM' N.subtype
      _ = L ⊔ (N ⊓ M) := by
        dsimp [NM']
        rw [Subgroup.subgroupOf_map_subtype]
        simp [L, L']
      _ = N := h71M
      _ = (⊤ : Subgroup ↥N).map N.subtype := by
        ext x
        constructor
        · intro hx
          exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          exact y.property
  -- decomposition of elements of ↥N: every x is l·m with m ∈ NM'
  have hdecomp : ∀ x : ↥N, ∃ l : ↥N, l ∈ L' ∧ ∃ m : ↥N, m ∈ NM' ∧ x = l * m := by
    intro x
    have hx : x ∈ (↑(L' ⊔ NM') : Set ↥N) := by
      rw [htop']
      trivial
    have hprod : (↑(L' ⊔ NM') : Set ↥N) = (NM' : Set ↥N) * (L' : Set ↥N) := by
      rw [sup_comm]
      exact Subgroup.mul_normal (H := NM') (N := L')
    rcases (Set.mem_mul.mp (hprod ▸ hx)) with ⟨m, hmNM', l, hlL', hml⟩
    refine ⟨m * l * m⁻¹, hL'normal.conj_mem l hlL' m, m, hmNM', ?_⟩
    calc
      x = m * l := hml.symm
      _ = (m * l * m⁻¹) * m := by group
  -- decomposition of elements of L' ⊔ A': every a is l·a₂ with a₂ ∈ A'
  have hdecompA : ∀ a : ↥N, a ∈ L' ⊔ A' → ∃ l : ↥N, l ∈ L' ∧ ∃ a₂ : ↥N, a₂ ∈ A' ∧ a = l * a₂ := by
    intro a ha
    have hprodA : (↑(A' ⊔ L') : Set ↥N) = (A' : Set ↥N) * (L' : Set ↥N) :=
      Subgroup.mul_normal (H := A') (N := L')
    have ha' : a ∈ (↑(A' ⊔ L') : Set ↥N) := by
      simpa [sup_comm] using ha
    rcases (Set.mem_mul.mp (hprodA ▸ ha')) with ⟨a₂, ha₂A', l, hlL', ha₂l⟩
    refine ⟨a₂ * l * a₂⁻¹, hL'normal.conj_mem l hlL' a₂, a₂, ha₂A', ?_⟩
    calc
      a = a₂ * l := ha₂l.symm
      _ = (a₂ * l * a₂⁻¹) * a₂ := by group
  -- L' ⊔ A' ⊴ ↥N
  have hLA'_normal : (L' ⊔ A').Normal := by
    refine ⟨?_⟩
    intro a ha y
    rcases hdecompA a ha with ⟨l₃, hl₃L', a₂, ha₂A', hla⟩
    rcases hdecomp y with ⟨l₂, hl₂L', m₁, hm₁NM', hylm⟩
    let l₄ : ↥N := m₁ * l₃ * m₁⁻¹
    let a₃ : ↥N := m₁ * a₂ * m₁⁻¹
    have hl₄ : l₄ ∈ L' := hL'normal.conj_mem l₃ hl₃L' m₁
    have ha₃ : a₃ ∈ A' := (Subgroup.normal_subgroupOf_iff hA'_le_NM').1 hA'_normal a₂ m₁ ha₂A' hm₁NM'
    have hX : y * a * y⁻¹ = l₂ * (l₄ * a₃) * l₂⁻¹ := by
      dsimp [l₄, a₃]
      rw [hylm, hla]
      group
    rw [hX]
    have hl₂l₄ : l₂ * l₄ * l₂⁻¹ ∈ L' := hL'normal.conj_mem l₄ hl₄ l₂
    have hl₂a₃ : l₂ * a₃ * l₂⁻¹ ∈ L' ⊔ A' := by
      have hc : (l₂ * a₃ * l₂⁻¹) * a₃⁻¹ ∈ L' := by
        have h1 : a₃ * l₂ * a₃⁻¹ ∈ L' := hL'normal.conj_mem l₂ hl₂L' a₃
        have h2 : (a₃ * l₂ * a₃⁻¹) * l₂⁻¹ ∈ L' :=
          Subgroup.mul_mem L' h1 (Subgroup.inv_mem L' hl₂L')
        have heq' : (l₂ * a₃ * l₂⁻¹) * a₃⁻¹ = ((a₃ * l₂ * a₃⁻¹) * l₂⁻¹)⁻¹ := by group
        rw [heq']
        exact Subgroup.inv_mem L' h2
      have hprod : l₂ * a₃ * l₂⁻¹ = ((l₂ * a₃ * l₂⁻¹) * a₃⁻¹) * a₃ := by group
      rw [hprod]
      exact Subgroup.mul_mem (L' ⊔ A') (Subgroup.mem_sup_left (S := L') (T := A') hc)
        (Subgroup.mem_sup_right (S := L') (T := A') ha₃)
    have heq' : l₂ * (l₄ * a₃) * l₂⁻¹ = (l₂ * l₄ * l₂⁻¹) * (l₂ * a₃ * l₂⁻¹) := by group
    rw [heq']
    exact Subgroup.mul_mem (L' ⊔ A') (Subgroup.mem_sup_left (S := L') (T := A') hl₂l₄) hl₂a₃
  -- L' ⊔ A' is a p'-subgroup of ↥N
  have hLA'_p' : Nat.Coprime p (Nat.card (↥(L' ⊔ A'))) := by
    have hprodA : (↑(A' ⊔ L') : Set ↥N) = (A' : Set ↥N) * (L' : Set ↥N) :=
      Subgroup.mul_normal (H := A') (N := L')
    have hcard : Nat.card (↥(L' ⊔ A')) =
        Nat.card (↥L') * Nat.card ((A' : Set ↥N).image (↑) : Set (↥N ⧸ L')) := by
      have hcardset : Nat.card ((L' ⊔ A' : Subgroup ↥N) : Set ↥N) =
          Nat.card (↥L') * Nat.card ((A' : Set ↥N).image (↑) : Set (↥N ⧸ L')) := by
        rw [sup_comm]
        rw [hprodA]
        exact Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := L') (t := (A' : Set ↥N))
      simpa using hcardset
    have hcopL' : Nat.Coprime p (Nat.card (↥L')) :=
      pPrimeCore_coprime_card (p := p) (G := ↥N)
    have hcop_img : Nat.Coprime p (Nat.card ((A' : Set ↥N).image (↑) : Set (↥N ⧸ L'))) := by
      have himg : Nat.card ((A' : Set ↥N).image (↑) : Set (↥N ⧸ L')) =
          Nat.card (A'.map (QuotientGroup.mk' L')) := by
        have hset : ((A' : Set ↥N).image (↑) : Set (↥N ⧸ L')) =
            (A'.map (QuotientGroup.mk' L') : Set (↥N ⧸ L')) := by
          ext x
          constructor
          · rintro ⟨y, hy, hyx⟩
            refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
            exact (by rfl : QuotientGroup.mk' L' y = (y : ↥N ⧸ L')).trans hyx
          · intro hx
            rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, hyx⟩
            exact ⟨y, hy, (by rfl : (y : ↥N ⧸ L') = QuotientGroup.mk' L' y).trans hyx⟩
        rw [hset]
        rfl
      have hdvd : Nat.card (A'.map (QuotientGroup.mk' L')) ∣ Nat.card (↥A') :=
        Subgroup.card_map_dvd (H := A') (QuotientGroup.mk' L')
      have hcopA' : Nat.Coprime p (Nat.card (↥A')) := by
        have hA'card : Nat.card (↥A') = Nat.card (↥A) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans hA_le_NM inf_le_left)).toEquiv
        have hcopA : Nat.Coprime p (Nat.card (↥A)) := by
          have hAdvd : Nat.card (↥A) ∣ Nat.card (↥A0) :=
            Subgroup.card_dvd_of_le (H := A) (K := A0) (show A ≤ A0 from inf_le_left)
          have hcopA0 : Nat.Coprime p (Nat.card (↥A0)) := by
            have hA0card : Nat.card (↥A0) = Nat.card (pPrimeCore p ↥M) := by
              exact Subgroup.card_map_of_injective (K := pPrimeCore p ↥M) (f := M.subtype) M.subtype_injective
            simpa [hA0card] using (pPrimeCore_coprime_card (p := p) (G := ↥M))
          exact Nat.Coprime.of_dvd_right hAdvd hcopA0
        simpa [hA'card] using hcopA
      exact Nat.Coprime.of_dvd_right hdvd hcopA'
    rw [hcard]
    exact Nat.Coprime.mul_right hcopL' hcop_img
  -- L' ⊔ A' ≤ L' = pPrimeCore p ↥N
  have hLA'_le_L' : L' ⊔ A' ≤ L' := by
    have hle : L' ⊔ A' ≤ pPrimeCore p ↥N := le_sSup ⟨hLA'_normal, hLA'_p'⟩
    simpa [L'] using hle
  -- A ≤ L
  have hA_le_L : A ≤ L := by
    intro x hxA
    have hxN : x ∈ N := (hA_le_NM (by exact hxA)).1
    have hxA' : (⟨x, hxN⟩ : ↥N) ∈ A' := by
      rw [Subgroup.mem_subgroupOf]
      exact hxA
    have hxL' : (⟨x, hxN⟩ : ↥N) ∈ L' := hLA'_le_L' (le_sup_right (a := L') (b := A') hxA')
    exact Subgroup.mem_map.mpr ⟨⟨x, hxN⟩, hxL', rfl⟩
  -- (7.3): N = L ⊔ B
  have h73 : N = L ⊔ B := by
    calc
      N = L ⊔ (N ⊓ M) := h71M.symm
      _ = L ⊔ (A ⊔ B) := by rw [h72']
      _ = (L ⊔ A) ⊔ B := by rw [sup_assoc]
      _ = L ⊔ B := by rw [sup_eq_left.2 hA_le_L]
  -- Step 6: M₁ ∈ M_p(G) containing N_G(K')
  have hK'_ne : K' ≠ ⊥ := by
    have hTne : (T : Subgroup ↥M) ≠ ⊥ := by
      intro hbot
      apply hWne
      calc
        W = WM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hWM).symm
        _ = (⊥ : Subgroup ↥M).map M.subtype := by
          exact congrArg (fun X : Subgroup ↥M => X.map M.subtype)
            (le_bot_iff.mp (hWT.trans (le_of_eq hbot)))
        _ = ⊥ := by simp
    have hKne : KM ≠ ⊥ := by
      have hTp' : IsPGroup p (T : Subgroup ↥M) := T.isPGroup'
      have hKn := K.K_nontrivial (P := (T : Subgroup ↥M)) hTp' hTne
      exact hKn
    intro hbot
    apply hKne
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    simpa [K'] using hbot
  have hK'_p : IsPGroup p K' := by
    have hKp : IsPGroup p KM := (T.isPGroup').to_le (K.K_le (T : Subgroup ↥M))
    exact IsPGroup.map hKp M.subtype
  let NK' : Subgroup G := Subgroup.normalizer (K' : Set G)
  have hOpNK' : pCore p (↥NK') ≠ ⊥ := by
    intro hbot
    apply hK'_ne
    have hle : K'.subgroupOf NK' ≤ pCore p (↥NK') := le_sSup ⟨(inferInstance : (K'.subgroupOf NK').Normal), by
      exact IsPGroup.of_equiv (hG := hK'_p) (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm⟩
    -- K' ≠ ⊥
    have hK'ne' : K'.subgroupOf NK' ≠ ⊥ := by
      intro hb
      apply hK'_ne
      calc
        K' = (K'.subgroupOf NK').map NK'.subtype := (Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer).symm
        _ = (⊥ : Subgroup ↥NK').map NK'.subtype := by rw [hb]
        _ = ⊥ := by simp
    exact False.elim (hK'ne' (le_bot_iff.mp (hle.trans (le_of_eq hbot))))
  let 𝒯₁ : Set (Subgroup G) := {K : Subgroup G | NK' ≤ K ∧ pCore p (↥K) ≠ ⊥}
  have h𝒯₁ne : 𝒯₁.Nonempty := ⟨NK', ⟨le_rfl, hOpNK'⟩⟩
  have h𝒯₁fin : 𝒯₁.Finite := Set.toFinite 𝒯₁
  obtain ⟨M₁, hM₁max⟩ := h𝒯₁fin.exists_maximalFor (fun K : Subgroup G => Nat.card (↥K)) 𝒯₁ h𝒯₁ne
  have hM₁𝒯 : M₁ ∈ 𝒯₁ := hM₁max.1
  have hM₁Mp : M₁ ∈ MpSet p G := by
    refine ⟨hM₁𝒯.2, ?_⟩
    intro K hKp hM₁K
    have hK𝒯 : K ∈ 𝒯₁ := ⟨le_trans hM₁𝒯.1 hM₁K, hKp⟩
    exact (Subgroup.eq_of_le_of_card_ge hM₁K (hM₁max.2 hK𝒯 (Subgroup.card_le_of_le hM₁K))).symm
  -- B ≤ M₁
  have hB_le_M₁ : B ≤ M₁ := by
    intro x hxB
    exact hM₁𝒯.1 ((Subgroup.mem_inf.mp hxB).2)
  -- W ≤ M₁
  have hWT'_le_NK' : T' ≤ NK' := by
    -- T' ≤ N_G(T') and N_G(T') ≤ N_G(K(T')) = N_G(K') via K_conj
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxNT' : x ∈ Subgroup.normalizer (T' : Set G) :=
      Subgroup.le_normalizer (H := T') hx
    have hmapT' : T'.map (MulAut.conj x).toMonoidHom = T' :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxNT')
    calc
      K'.map (MulAut.conj x).toMonoidHom
          = (K.K (H := G) T').map (MulAut.conj x).toMonoidHom := by rw [hK']
      _ = K.K (H := G) (T'.map (MulAut.conj x).toMonoidHom) :=
          (K.K_conj (P := T') (g := x)).symm
      _ = K.K (H := G) T' := by rw [hmapT']
      _ = K' := hK'.symm
  have hNGT'_le_NK' : Subgroup.normalizer (T' : Set G) ≤ NK' := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmapT' : T'.map (MulAut.conj x).toMonoidHom = T' :=
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hx)
    calc
      K'.map (MulAut.conj x).toMonoidHom
          = (K.K (H := G) T').map (MulAut.conj x).toMonoidHom := by rw [hK']
      _ = K.K (H := G) (T'.map (MulAut.conj x).toMonoidHom) :=
          (K.K_conj (P := T') (g := x)).symm
      _ = K.K (H := G) T' := by rw [hmapT']
      _ = K' := hK'.symm
  have hW_le_M₁ : W ≤ M₁ := hWleT'.trans (hWT'_le_NK'.trans hM₁𝒯.1)
  have h71M₁ : L ⊔ (N ⊓ M₁) = N := by
    apply le_antisymm
    · exact sup_le hL_le_N (inf_le_left : N ⊓ M₁ ≤ N)
    · have hB_le_NM₁ : B ≤ N ⊓ M₁ :=
        le_inf (le_trans (inf_le_left : B ≤ N ⊓ M) (inf_le_left : N ⊓ M ≤ N)) hB_le_M₁
      calc
        N = L ⊔ B := h73
        _ ≤ L ⊔ (N ⊓ M₁) := sup_le_sup_left (c := L) hB_le_NM₁
  have hM₁chain : pPart p (Nat.card (↥M₁)) ≤ pPart p (Nat.card (↥M)) :=
    hMmax' M₁ hM₁Mp hW_le_M₁ h71M₁
  -- Sylow-counting chain: |T| = |M|_p ≥ |M₁|_p ≥ |N_G(K')|_p ≥ |N_G(T')|_p ≥ |T'| = |T|
  let NG' : Subgroup G := Subgroup.normalizer (T' : Set G)
  have hT'card : Nat.card (↥T') = Nat.card (↥T) := by
    dsimp [T']
    exact Subgroup.card_map_of_injective (K := (T : Subgroup ↥M)) (f := M.subtype) M.subtype_injective
  have hT'p : IsPGroup p T' := by
    dsimp [T']
    exact IsPGroup.map (H := (T : Subgroup ↥M)) T.isPGroup' M.subtype
  have hT'ppart : pPart p (Nat.card (↥T')) = Nat.card (↥T') := by
    rcases hT'p.exists_card_eq with ⟨n, hn⟩
    unfold pPart
    rw [hn, padicValNat.prime_pow]
  have hT'dvd : Nat.card (↥T') ∣ Nat.card (↥NG') :=
    Subgroup.card_dvd_of_le (H := T') (K := NG') (Subgroup.le_normalizer (H := T'))
  have hT'le_part : Nat.card (↥T') ≤ pPart p (Nat.card (↥NG')) := by
    rw [← hT'ppart]
    exact pPart_mono (hb := ne_of_gt (Nat.card_pos (α := ↥NG'))) (hab := hT'dvd)
  have hpart_ge : pPart p (Nat.card (↥NG')) ≤ pPart p (Nat.card (↥NK')) := by
    exact pPart_mono (hb := ne_of_gt (Nat.card_pos (α := ↥NK')))
      (Subgroup.card_dvd_of_le (H := NG') (K := NK') hNGT'_le_NK')
  have hpart_ge' : pPart p (Nat.card (↥NK')) ≤ pPart p (Nat.card (↥M₁)) := by
    exact pPart_mono (hb := ne_of_gt (Nat.card_pos (α := ↥M₁)))
      (Subgroup.card_dvd_of_le (H := NK') (K := M₁) hM₁𝒯.1)
  have hTcardM : pPart p (Nat.card (↥M)) = Nat.card (↥T) :=
    pPart_card_eq_card_of_sylow (G := ↥M) T
  have hchain : pPart p (Nat.card (↥NG')) = Nat.card (↥T') := by
    apply le_antisymm
    · calc
        pPart p (Nat.card (↥NG')) ≤ pPart p (Nat.card (↥NK')) := hpart_ge
        _ ≤ pPart p (Nat.card (↥M₁)) := hpart_ge'
        _ ≤ pPart p (Nat.card (↥M)) := hM₁chain
        _ = Nat.card (↥T) := hTcardM
        _ = Nat.card (↥T') := hT'card.symm
    · exact hT'le_part
  -- T' is a Sylow p-subgroup of its own normalizer
  have hT'sub_p : IsPGroup p (T'.subgroupOf NG') := by
    exact IsPGroup.of_equiv (hG := hT'p)
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := T'))).symm
  have hTne2 : (T : Subgroup ↥M) ≠ ⊥ := by
    intro hbot
    apply hWne
    calc
      W = WM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hWM).symm
      _ = (⊥ : Subgroup ↥M).map M.subtype := by
        exact congrArg (fun X : Subgroup ↥M => X.map M.subtype)
          (le_bot_iff.mp (hWT.trans (le_of_eq hbot)))
      _ = ⊥ := by simp
  have hT'ne : T' ≠ ⊥ := by
    intro hb
    apply hTne2
    apply Subgroup.map_injective (f := M.subtype) M.subtype_injective
    simpa [T'] using hb
  obtain ⟨Q, hT'Q⟩ := hT'sub_p.exists_le_sylow
  have hQcard : Nat.card (↥(Q : Subgroup ↥NG')) = Nat.card (↥T') := by
    calc
      Nat.card (↥(Q : Subgroup ↥NG')) = pPart p (Nat.card (↥NG')) := by
        exact (pPart_card_eq_card_of_sylow (G := ↥NG') Q).symm
      _ = Nat.card (↥T') := hchain
  have hT'card2 : Nat.card (↥(T'.subgroupOf NG')) = Nat.card (↥T') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := T'))).toEquiv
  have hT'Qeq : T'.subgroupOf NG' = (Q : Subgroup ↥NG') :=
    Subgroup.eq_of_le_of_card_ge hT'Q (by
      rw [hQcard]
      rw [hT'card2])
  let TN' : Sylow p ↥NG' := Q
  have hTN'_eq : (TN' : Subgroup ↥NG') = T'.subgroupOf NG' := hT'Qeq.symm
  -- T' ∈ Sylow p G
  obtain ⟨Tg, hTg_eq⟩ := isSylow_of_sylow_normalizer (T := T') (p := p) hT'p TN' hTN'_eq
  -- g with T'.map (conj g) = S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Tg S
  have hg' : (S : Subgroup G) = T'.map (MulAut.conj g).toMonoidHom := by
    have hco : ↑(g • Tg : Sylow p G) = T'.map (MulAut.conj g).toMonoidHom := by
      rw [Sylow.coe_subgroup_smul]
      rw [hTg_eq]
      rfl
    have htmp : T'.map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
      simpa [hco] using congrArg (fun X : Sylow p G => (X : Subgroup G)) hg
    exact htmp.symm
  -- (C_p) applied at g⁻¹: W.map (conj g) = conjSubgroup g⁻¹ W ≤ S
  have hWg_le_S : conjSubgroup g⁻¹ W ≤ (S : Subgroup G) := by
    intro x hx
    rcases (Subgroup.mem_map.mp hx) with ⟨w, hwW, rfl⟩
    have hxS : (MulAut.conj g).toMonoidHom w ∈ (S : Subgroup G) := by
      rw [hg']
      refine Subgroup.mem_map.mpr ⟨w, hWleT' hwW, rfl⟩
    simpa [inv_inv] using hxS
  have hCpSub : CpSubgroup K S := cpSubgroup_of_cp K S (hCp S)
  rcases hCpSub W hWp hWleS (g⁻¹) hWg_le_S with ⟨c, n, hcC, hnN, hcn⟩
  have hcN : c ∈ N := (Subgroup.centralizer_le_normalizer (W : Set G)) hcC
  -- (7.3)-form: N = L ⊔ (N ⊓ NK')
  have hN_eq : N = L ⊔ (N ⊓ NK') := by
    apply le_antisymm
    · have hB_le : B ≤ N ⊓ NK' := by
        refine le_inf ?_ ?_
        · exact le_trans (inf_le_left : B ≤ N ⊓ M) (inf_le_left : N ⊓ M ≤ N)
        · exact inf_le_right
      calc
        N = L ⊔ B := h73
        _ ≤ L ⊔ (N ⊓ NK') := sup_le_sup_left (c := L) hB_le
    · exact sup_le hL_le_N (inf_le_left : N ⊓ NK' ≤ N)
  -- K'^c = K(S): the conjugation chain of the paper
  have hKcg : K'.map (MulAut.conj g).toMonoidHom = K.K (H := G) (S : Subgroup G) := by
    calc
      K'.map (MulAut.conj g).toMonoidHom
          = (K.K (H := G) T').map (MulAut.conj g).toMonoidHom := by rw [hK']
      _ = K.K (H := G) (T'.map (MulAut.conj g).toMonoidHom) :=
          (K.K_conj (P := T') (g := g)).symm
      _ = K.K (H := G) (S : Subgroup G) := by rw [hg']
  have hcn' : g = n⁻¹ * c⁻¹ := by
    calc
      g = (c * n)⁻¹ := by rw [← hcn]; group
      _ = n⁻¹ * c⁻¹ := by group
  have hKc : K'.map (MulAut.conj c⁻¹).toMonoidHom = K.K (H := G) (S : Subgroup G) := by
    -- K'.map (conj c⁻¹) = K(S): from c⁻¹ = n·g we get conj c⁻¹ = conj n ∘ conj g,
    -- and K'.map (conj g) = K(S); then n ∈ N_G(K(S)) fixes K(S).
    have hcomp' : (MulAut.conj c⁻¹).toMonoidHom =
        (MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      have hng : c⁻¹ = n * g := by rw [hcn']; group
      rw [hng, MulAut.conj.map_mul]
      rfl
    calc
      K'.map (MulAut.conj c⁻¹).toMonoidHom
          = K'.map ((MulAut.conj n).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
              rw [hcomp']
      _ = (K'.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n).toMonoidHom := by
              rw [← Subgroup.map_map]
      _ = (K.K (H := G) (S : Subgroup G)).map (MulAut.conj n).toMonoidHom := by
              rw [hKcg]
      _ = K.K (H := G) (S : Subgroup G) := by
              exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN)
  -- N^c = N, L^c = L, and the join-conjugation of (7.3)-form N = L ⊔ (N ⊓ NK')
  have hNmap : N.map (MulAut.conj c⁻¹).toMonoidHom = N := by
    ext x
    constructor
    · intro hx
      rcases (Subgroup.mem_map.mp hx) with ⟨y, hyN, rfl⟩
      simpa using (Subgroup.mul_mem N (Subgroup.mul_mem N (Subgroup.inv_mem N hcN) hyN) hcN)
    · intro hx
      refine Subgroup.mem_map.mpr ⟨c * x * c⁻¹, ?_, ?_⟩
      · exact Subgroup.mul_mem N (Subgroup.mul_mem N hcN hx) (Subgroup.inv_mem N hcN)
      · change (MulAut.conj (c⁻¹)) (c * x * c⁻¹) = x
        rw [MulAut.conj_apply]
        group
  have hL_normal_G : ∀ n : G, n ∈ N → ∀ l : G, l ∈ L → n * l * n⁻¹ ∈ L := by
    intro n hn l hl
    rcases (Subgroup.mem_map.mp hl) with ⟨p₀, hp₀, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨n, hn⟩ : ↥N) * p₀ * (⟨n, hn⟩ : ↥N)⁻¹, ?_, ?_⟩
    · exact (pPrimeCore_normal (p := p) (G := ↥N)).conj_mem p₀ hp₀ (⟨n, hn⟩ : ↥N)
    · simp [mul_assoc]
  have hLmap : L.map (MulAut.conj c⁻¹).toMonoidHom = L := by
    ext x
    constructor
    · intro hx
      rcases (Subgroup.mem_map.mp hx) with ⟨y, hyL, rfl⟩
      exact hL_normal_G (c⁻¹) (Subgroup.inv_mem N hcN) y hyL
    · intro hx
      refine Subgroup.mem_map.mpr ⟨c * x * c⁻¹, hL_normal_G c hcN x hx, ?_⟩
      · change (MulAut.conj (c⁻¹)) (c * x * c⁻¹) = x
        rw [MulAut.conj_apply]
        group
  -- the conjugation of N ⊓ NK' and the normalizer
  have hNKc : NK'.map (MulAut.conj c⁻¹).toMonoidHom =
      Subgroup.normalizer (K'.map (MulAut.conj c⁻¹).toMonoidHom : Set G) := by
    dsimp [NK']
    exact Subgroup.map_normalizer_eq_of_bijective K'
      (f := (MulAut.conj c⁻¹).toMonoidHom)
      (by simpa using (MulAut.conj c⁻¹).bijective)
  have hmap_inf : (N ⊓ NK').map (MulAut.conj c⁻¹).toMonoidHom =
      N.map (MulAut.conj c⁻¹).toMonoidHom ⊓ NK'.map (MulAut.conj c⁻¹).toMonoidHom := by
    ext x
    constructor
    · intro hx
      rcases (Subgroup.mem_map.mp hx) with ⟨y, hy, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨y, hy.1, rfl⟩, Subgroup.mem_map.mpr ⟨y, hy.2, rfl⟩⟩
    · intro hx
      rcases (Subgroup.mem_inf.mp hx) with ⟨hxN, hxK⟩
      rcases (Subgroup.mem_map.mp hxN) with ⟨y, hyN, hyx⟩
      rcases (Subgroup.mem_map.mp hxK) with ⟨z, hzK, hzx⟩
      have hyz : y = z := by
        have h : (MulAut.conj c⁻¹).toMonoidHom y = (MulAut.conj c⁻¹).toMonoidHom z := by
          rw [hyx, hzx]
        exact (MulAut.conj c⁻¹).injective h
      refine Subgroup.mem_map.mpr ⟨y, ⟨hyN, ?_⟩, hyx⟩
      simpa [hyz] using hzK
  -- N = L ⊔ (N ⊓ N_G(K(S))): conjugate (7.3)-form by c
  have hfin : N = L ⊔ (N ⊓ Subgroup.normalizer ((K.K (H := G) (S : Subgroup G) : Subgroup G) : Set G)) := by
    calc
      N = N.map (MulAut.conj c⁻¹).toMonoidHom := hNmap.symm
      _ = (L ⊔ (N ⊓ NK')).map (MulAut.conj c⁻¹).toMonoidHom := by
            conv_lhs => rw [hN_eq]
      _ = L.map (MulAut.conj c⁻¹).toMonoidHom ⊔ (N ⊓ NK').map (MulAut.conj c⁻¹).toMonoidHom := by
            rw [Subgroup.map_sup]
      _ = L ⊔ (N ⊓ NK').map (MulAut.conj c⁻¹).toMonoidHom := by rw [hLmap]
      _ = L ⊔ (N.map (MulAut.conj c⁻¹).toMonoidHom ⊓ NK'.map (MulAut.conj c⁻¹).toMonoidHom) := by
            rw [hmap_inf]
      _ = L ⊔ (N ⊓ NK'.map (MulAut.conj c⁻¹).toMonoidHom) := by rw [hNmap]
      _ = L ⊔ (N ⊓ Subgroup.normalizer (K'.map (MulAut.conj c⁻¹).toMonoidHom : Set G)) := by
            rw [hNKc]
      _ = L ⊔ (N ⊓ Subgroup.normalizer ((K.K (H := G) (S : Subgroup G) : Subgroup G) : Set G)) := by
            rw [hKc]
  -- the goal unfolds the lets N and L
  simpa [N, L] using hfin


end CFSG.Glauberman

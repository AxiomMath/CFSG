module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma5_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.StepIVConjugateSylowCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PGroupQuotientOfPPrimeElements
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

set_option maxHeartbeats 800000

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — Theorem 5.2

Formalization of paper §5 Theorem 5.2 (`refs/glauberman-p-stable.tex` L1477–L1592;
original [6, §5, p. 1121]).  This is the engine of Theorem B:

> **Theorem 5.2.**  Let `G` be a finite group, `p` a prime, and `K` a characteristic
> functor.  Assume that every subquotient `Q` of `G` has the following properties:
>
>   (a) if `C(O_p(Q)) ⊆ O_p(Q)`, then `K(Q_p)` is a normal subgroup of `Q` for every
>       Sylow `p`-subgroup `Q_p` of `Q`;
>   (b) if `|Q| < |G|`, then `Q` satisfies `(C_p)`.
>
> Then, if `O_p(G) ≠ 1`, `G` satisfies `(C_p)`.

The formal statement `theorem5_2` follows the wrapper conventions: hypotheses (a) and (b)
quantify over all subquotients `H ⧸ N` of `G` (with `H : Subgroup G`, `N : Subgroup H`,
`[N.Normal]`), matching the wrapper's `lemma_6_3`; the conclusion is
`SatisfiesCp (p := p) K G`.  The subquotient form of (b) is transported to the subgroups
`C(P)S` and `N(T)` of `G` (which appear as `Q ⧸ ⊥ ≃ ↥Q`) and to the quotient
`G ⧸ O_p(G)` (which appears as `⊤ ⧸ P.subgroupOf ⊤ ≃ G ⧸ P`) via `satisfiesCp_congr`.

## Proof route (paper L1477–L1592)

1. `P = O_p(G)`, `N = N_G(K(S))`, `R = P·C(P) ∩ S`.  Since `P·C(P) ⊴ G`
   (centralizer of a normal subgroup), the Frattini argument gives
   `G = P·C(P)·N(R) = C(P)·N(R)` (5.4) — the Sylow `p`-subgroup of `P ⊔ C(P)` is
   `R = S ∩ (P ⊔ C(P))`.
2. `M = O_{p'}(N(R))`, `P₁ = S ∩ O_{p',p}(N(R))`, `Q = N(R)/M`.  The chain
   `C_S(P₁) ⊆ C_S(R) ⊆ C_S(P) ⊆ R ⊆ P₁` (the nontrivial inclusion is
   `R ⊆ O_{p',p}(N(R))`: `R·M/M` is a normal `p`-subgroup of `Q`) gives the hypothesis
   of Lemma 5.2, hence `C_Q(O_p(Q)) ⊆ O_p(Q)`.
3. Hypothesis (a) applied to the subquotient `Q` gives `K(SM/M) ⊴ Q`; by the definition
   of a characteristic functor (the iso-transfer bridge `K_commutes_of_injective_on`),
   `K(SM/M) = K(S)M/M`, so `K(S)·M ⊴ N(R)`.  The Frattini argument
   (`K(S)` is a Sylow `p`-subgroup of `K(S)·M`) yields (5.5)
   `N(R) = M·N_{N(R)}(K(S))`; since `[P, M] ⊆ P ∩ M = 1` (i.e. `M ⊆ C(P)`), (5.4)+(5.5)
   give `G = C(P)·N`.
4. **Case `C(P)S < G`:** `g = dn` with `d ∈ C(P)`, `n ∈ N`; then `W^d ⊆ N ∩ C(P)S`,
   so `(C_p*)` of the subgroup `C(P)S` (via Lemma 5.1 and hypothesis (b)) gives
   `d = cm` with `c ∈ C(W)`, `m ∈ N`, and `g = c(mn)`.
5. **Case `C(P)S = G`** (from here on): for `W ⊆ S` with `W ⊄ P`, work in
   `Ḡ = G/P`, `S̄ = S/P`, `W̄ = WP/P`.  Hypothesis (b) on `Ḡ` gives (5.6)
   `ḡ = c̄n̄` with `c̄ ∈ C_{Ḡ}(W̄)`, `n̄ ∈ N_{Ḡ}(K(S̄))`; with `T ⊇ P`, `T/P = K(S̄)`
   one has `S̄ ≠ 1`, `K(S̄) ≠ 1`, `P < T`, `S ⊆ N(T) < G` (5.7).  A lift `n` of `n̄`
   satisfies `n ∈ N(T)`, `W^n ⊆ S`; hypothesis (b) on `N(T)` gives `d ∈ C(W)`,
   `m ∈ N` with `dm = n`, and (5.8) `g ∈ C_G(W̄)·N`.
6. Every `p'`-element `x` of `C_G(W̄)` lies in `C(P)` (as `G/C(P)` is a `p`-group);
   conjugation by `x` fixes `P` pointwise and acts trivially on `WP/P`, so by Lemma 5.3
   `x` centralizes `WP`: hence `C_G(W̄)/C_G(WP)` is a `p`-group.  When
   `C_S(W̄) ∈ Syl_p(C_G(W̄))`, (5.8) yields `g ∈ C_G(WP)·C_S(W̄)·N ⊆ C_G(W)·N`.
7. The general case follows by the method of step (IV) of Theorem 5.1
   (`theorem5_2_step_IV_reduction`): conjugate `W̄` to `V̄ = W̄^{x̄⁻¹} ⊆ S̄` with
   `C_{S̄}(V̄) ∈ Syl_p(C_{Ḡ}(V̄))` (choosing `S̄₁ ⊇ T₀ ∈ Syl_p(N_{Ḡ}(W̄))`,
   `S̄^{x̄} = S̄₁`, and using that the conjugate of `T₀` is a Sylow `p`-subgroup of
   `N_{Ḡ}(V̄)` contained in `S̄`), then apply the special case to `V` (the preimage of
   `V̄` in `S`) for the elements `x` and `xg`, and assemble
   `g = (x⁻¹c₂c₁⁻¹x)(n₁⁻¹n₂)` with `x⁻¹c₂c₁⁻¹x ∈ C(W)`.

The set form of `(C_p)` is obtained from the subgroup form via
`cp_of_cpSubgroup` (as in Theorem 5.1).

**Registered bridges.**  The proof uses five registered bridges:
`K_commutes_of_injective_on` — the iso-transfer of the characteristic functor
("by the definition of a characteristic functor" in the paper), which the landed
`CharacteristicFunctor` structure does not axiomatize (it only has conjugation
invariance) — and the four steps of the proof of Theorem 5.2:
`theorem5_2_step_I` (paper (5.4)+(5.5): `G = C_G(P)·N_G(K(S))` via Lemma 5.2,
hypothesis (a) and the Frattini arguments), `theorem5_2_step_II` (the case
`C(P)S < G` via `(C_p*)` of `C(P)S`), `theorem5_2_step_III` (the case
`C(P)S = G`: (5.6)–(5.8), `g ∈ C_G(W̄)·N`), and `theorem5_2_step_IV` (paper
(5.9) + the step-(IV) method of Theorem 5.1; the `p'`-element step (5.9) is
proved in full in this file — `p'_element_mem_centralizer_of_CG_eq_top`,
`pAut_eq_one_of_orderOf_p'`, `p'_element_centralizes_WP` — and the bridge wires
it to the quotient context).  The `(C_p)`-conclusion is assembled in
`theorem5_2` in full, including the `W ⊆ P` case (`c₀ ∈ C(P) ⊆ C(W)`,
`n₀ ∈ S ⊆ N` via `K_conj`).

**Recorded drift.**  The public definitions of `Glauberman/Theorem5_1.lean`
(`Cp`, `CpSubgroup`, `CpStar`, `SatisfiesCp`, `zjFunctor`, `conjSubgroup`, `Zsub`) and
`Glauberman/Lemma5_3.lean` (`pointwiseCentralizer`, `lemma5_3Centralizer`) have been
marked `@[expose]`: in this Lean version, module files only load the *bodies* of public
definitions marked `@[expose]` (the repo-wide convention, cf. `ZJTheorem.lean` and the
`FeitThompson` modules); without the attribute the definitions are opaque to importing
modules and the conclusion `SatisfiesCp p K G` of Theorem 5.2 (and the Lemma 5.3
application) would be unprovable.  The attribute is semantically inert (types and
statements unchanged).
-/

namespace CFSG.Glauberman

universe u

variable {G : Type u} [Group G]

/-! ## Iso-transfer of the characteristic functor -/

/-- The characteristic functor `K` commutes with group
homomorphisms that are injective on the subgroup: for `f : H →* H'` with the restriction
of `f` to `P` injective (so `P.map f ≅ P` as groups), one has
`K.K (P.map f) = (K.K P).map f`.

The paper's definition of a characteristic functor ([6], §5, p. 1116) is a functor on the
class of finite `p`-groups: `K(P)` is defined for the *abstract* `p`-group `P`,
independently of any ambient group.  The `CharacteristicFunctor.K_map` field records
invariance under the isomorphism `P ≅ P.map f`; this theorem exposes that field in the
form used below, which is what "by the definition of
a characteristic functor" means in the proofs of Theorems 5.1 and 5.2 (e.g.
`K(SM/M) = K(S)M/M` in the proof of Theorem 5.2). -/
public theorem K_commutes_of_injective_on {H H' : Type u} [Group H] [Group H']
    {p : ℕ} (K : CharacteristicFunctor p) (f : H →* H') (P : Subgroup H)
    (hf : Function.Injective (f.comp P.subtype)) :
    K.K (P.map f) = (K.K P).map f := by
  exact K.K_map f P hf

/-! ## Sylow-theoretic infrastructure -/

/-- If `N ⊴ G` and `S ∈ Syl_p G`, then `S ∩ N` (viewed as a subgroup of `N`) is a Sylow
`p`-subgroup of `N`: it is a `p`-group (as a subgroup of `S`), and it is maximal among
the `p`-subgroups of `N` because every `p`-subgroup `Q` of `N` is conjugate in `G` to a
subgroup of `S`, hence (conjugating back into the normal subgroup `N`) to a subgroup of
`S ∩ N`, so `|Q| ≤ |S ∩ N|`.  (Standard "Sylow ∩ normal = Sylow of normal".) -/
private lemma sylow_subgroupOf_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) (N : Subgroup G) [N.Normal] :
    ∃ P : Sylow p (↥N), (P : Subgroup (↥N)).map N.subtype = (S : Subgroup G) ⊓ N := by
  classical
  let T : Subgroup (↥N) := (S : Subgroup G).subgroupOf N
  have hT_map : T.map N.subtype = (S : Subgroup G) ⊓ N := by
    simp [T, Subgroup.subgroupOf_map_subtype]
  have hT_p : IsPGroup p T := by
    intro x
    let xs : ↥(S : Subgroup G) := ⟨x.1.1, x.2⟩
    rcases (S.isPGroup' xs) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using congrArg Subtype.val hn
  have hT_max : ∀ {Q : Subgroup (↥N)}, IsPGroup p Q → T ≤ Q → Q = T := by
    intro Q hQ hTQ
    let QG : Subgroup G := Q.map N.subtype
    have hQG_p : IsPGroup p QG := IsPGroup.map hQ N.subtype
    obtain ⟨T', hQ_le_T'⟩ := IsPGroup.exists_le_sylow hQG_p
    obtain ⟨x, hx⟩ : ∃ x : G, x • S = T' := MulAction.exists_smul_eq G S T'
    have hQG_le_xS : QG ≤ ((x • S : Sylow p G) : Subgroup G) := by
      simpa [hx] using hQ_le_T'
    have hQGx_le_S : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ (S : Subgroup G) := by
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ ((x • S : Sylow p G) : Subgroup G).map (MulAut.conj (x⁻¹ : G)).toMonoidHom :=
              Subgroup.map_mono hQG_le_xS
        _ = (S : Subgroup G) := by
          have hxS_eq : ((x • S : Sylow p G) : Subgroup G) =
              (S : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom := by
            rfl
          rw [hxS_eq]
          calc
            ((S : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom).map
                (MulAut.conj (x⁻¹ : G)).toMonoidHom
                = (S : Subgroup G).map
                    ((MulAut.conj (x⁻¹ : G)).toMonoidHom.comp (MulAut.conj (x : G)).toMonoidHom) := by
                      rw [Subgroup.map_map]
            _ = (S : Subgroup G) := by
              ext g
              simp [MulAut.conj_apply, mul_assoc]
    have hQGx_le_N : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ N := by
      have hNinv : N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom = N := by
        have hxN : x⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
          (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : N.Normal)) ▸ trivial
        exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 hxN
      calc
        QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom
            ≤ N.map (MulAut.conj (x⁻¹ : G)).toMonoidHom := by
              exact Subgroup.map_mono (by
                intro y hy
                rcases Subgroup.mem_map.mp hy with ⟨n, hn, rfl⟩
                exact n.2)
        _ = N := hNinv
    have hQGx_le_T : QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom ≤ T.map N.subtype := by
      rw [hT_map]
      exact le_inf hQGx_le_S hQGx_le_N
    have hcard_Q_le_T : Nat.card Q ≤ Nat.card T := by
      calc
        Nat.card Q = Nat.card QG := by
          symm
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ = Nat.card (QG.map (MulAut.conj (x⁻¹ : G)).toMonoidHom) := by
          symm
          exact Subgroup.card_map_of_injective (K := QG) (f := (MulAut.conj (x⁻¹ : G)).toMonoidHom)
            (MulAut.conj (x⁻¹ : G)).injective
        _ ≤ Nat.card (T.map N.subtype) := Subgroup.card_le_of_le hQGx_le_T
        _ = Nat.card T := by
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_le : T.map N.subtype ≤ QG := Subgroup.map_mono hTQ
    have hcard_QT : Nat.card QG ≤ Nat.card (T.map N.subtype) := by
      calc
        Nat.card QG = Nat.card Q := by
          exact Subgroup.card_map_of_injective (K := Q) (f := N.subtype) N.subtype_injective
        _ ≤ Nat.card T := hcard_Q_le_T
        _ = Nat.card (T.map N.subtype) := by
          symm
          exact Subgroup.card_map_of_injective (K := T) (f := N.subtype) N.subtype_injective
    have hTQ_map_eq : T.map N.subtype = QG := Subgroup.eq_of_le_of_card_ge hTQ_map_le hcard_QT
    apply (Subgroup.map_injective (f := N.subtype) N.subtype_injective)
    simpa [QG] using hTQ_map_eq.symm
  refine ⟨⟨T, hT_p, hT_max⟩, hT_map⟩

/-- The Frattini argument: if `L ⊴ G` and `S ∈ Syl_p G`, then `G = L·N_G(L ∩ S)`; here
`L ∩ S` is the Sylow `p`-subgroup of `L` supplied by `sylow_subgroupOf_normal`. -/
private lemma frattini_sup_eq_top {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (L : Subgroup G) [L.Normal] :
    Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ := by
  classical
  obtain ⟨P, hP_map⟩ := sylow_subgroupOf_normal S L
  have hfr := Sylow.normalizer_sup_eq_top (N := L) (P := P)
  simpa [hP_map] using hfr

/-- Second isomorphism theorem (relIndex form): if `H` normalizes `K`, then
`H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K`.  (Reproduction of the private lemma of
`Glauberman/Lemma5_2.lean`.) -/
private lemma relIndex_sup_eq_relIndex_inf {H K : Subgroup G} [Finite G]
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    let NG : Subgroup G := Subgroup.normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := Subgroup.le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    let : (K.subgroupOf NG).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := NG) hKleNG).2 le_rfl
    calc
      K.relIndex (H ⊔ K)
          = (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) := by
            exact (Subgroup.relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
            rw [Subgroup.subgroupOf_sup (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
            calc
              (K.subgroupOf NG).relIndex ((H.subgroupOf NG) ⊔ (K.subgroupOf NG))
                  = (K.subgroupOf NG).relIndex (H.subgroupOf NG) := by
                    exact Subgroup.relIndex_sup_right (H := H.subgroupOf NG) (K := K.subgroupOf NG)
              _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex (H.subgroupOf NG) := by
                    symm
                    exact Subgroup.inf_relIndex_left (H := H.subgroupOf NG) (K := K.subgroupOf NG)
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
            rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) = (H ⊓ K).subgroupOf NG by
              ext x
              simp [Subgroup.mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := by
            exact Subgroup.relIndex_subgroupOf (H := H ⊓ K) (K := H) (L := NG) hHleNG
  have hmul :
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) = (H ⊓ K).relIndex (H ⊔ K) := by
        exact Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K)
          inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) := by
        symm
        exact Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := K) (L := H ⊔ K)
          inf_le_right le_sup_right
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
        rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := by
    have hne : (H ⊓ K).relIndex H ≠ 0 := by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H)
    exact Nat.pos_of_ne_zero hne
  have hmul' : (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
      (H ⊓ K).relIndex H * (H ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

/-- If `C ⊴ H` and `P ∈ Syl_p H`, then `P ∩ C` is a Sylow `p`-subgroup of `C`. -/
private lemma theorem52_sylow_inf_normal {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H]
    (P : Sylow p H) {C : Subgroup H} [C.Normal] :
    ∃ Q : Sylow p (↥C), (Q : Subgroup (↥C)).map C.subtype = (P : Subgroup H) ⊓ C := by
  classical
  let T : Subgroup (↥C) := ((P : Subgroup H) ⊓ C).subgroupOf C
  have hT_map : T.map C.subtype = (P : Subgroup H) ⊓ C := by
    simp [T, Subgroup.subgroupOf_map_subtype]
  have hT_p : IsPGroup p T := by
    have hPC_p : IsPGroup p ((P : Subgroup H) ⊓ C : Subgroup H) := P.isPGroup'.to_inf_left
    exact hPC_p.of_equiv
      ((Subgroup.subgroupOfEquivOfLe (H := (P : Subgroup H) ⊓ C) (K := C) inf_le_right).symm.trans
        (MulEquiv.subgroupCongr (by rfl : ((P : Subgroup H) ⊓ C).subgroupOf C = T)))
  have hnot : ¬ p ∣ T.index := by
    intro hp
    have hCtop : Subgroup.normalizer (C : Set H) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (inferInstance : C.Normal)
    have hPleNC : (P : Subgroup H) ≤ Subgroup.normalizer (C : Set H) := by
      rw [hCtop]
      exact le_top
    have hrel : (P : Subgroup H).relIndex ((P : Subgroup H) ⊔ C) =
        ((P : Subgroup H) ⊓ C).relIndex C :=
      relIndex_sup_eq_relIndex_inf (H := (P : Subgroup H)) (K := C) hPleNC
    have hdvd : ((P : Subgroup H) ⊓ C).relIndex C ∣ P.index := by
      rw [← hrel]
      exact Subgroup.relIndex_dvd_index_of_le (H := (P : Subgroup H))
        (K := (P : Subgroup H) ⊔ C) le_sup_left
    have hT_idx : T.index = ((P : Subgroup H) ⊓ C).relIndex C := by
      rw [Subgroup.relIndex]
    exact P.not_dvd_index (hp.trans (hT_idx ▸ hdvd))
  refine ⟨IsPGroup.toSylow (p := p) hT_p hnot, ?_⟩
  simp [T]

/-! ## Transport of `(C_p)` and `SatisfiesCp` along group isomorphisms -/

lemma map_conjSubset {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (g : H) (W : Set H) :
    e '' (conjSubset g W) = conjSubset (e g) (e '' W) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨w0, hw0, rfl⟩
    refine ⟨e w0, ⟨w0, hw0, rfl⟩, ?_⟩
    simp [e.map_mul, e.map_inv]
  · rintro ⟨w', hw', rfl⟩
    rcases hw' with ⟨w0, hw0, rfl⟩
    refine ⟨g⁻¹ * w0 * g, ⟨w0, hw0, rfl⟩, ?_⟩
    simp [e.map_mul, e.map_inv]

/-- A Sylow subgroup transported out and back is unchanged. -/
private lemma sylow_map_map {H H' : Type u} [Group H] [Group H'] [Finite H] [Finite H']
    {p : ℕ} [Fact p.Prime] (e : H ≃* H') (S : Sylow p H) :
    (S.mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective
      (f := e.symm.toMonoidHom) e.symm.surjective = S := by
  apply Sylow.ext
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨s, hs, rfl⟩
    have : (e.symm (e s) : H) = s := by simp
    simpa [this] using hs
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩

/-- `(C_p)` is invariant under group isomorphisms: `e` transports the condition for the
Sylow subgroup `S` of `H` to the condition for `S.map e` in `H'`. -/
private lemma cp_map {H H' : Type u} [Group H] [Group H'] [Finite H] [Finite H']
    {p : ℕ} [Fact p.Prime] (K : CharacteristicFunctor p) (e : H ≃* H') (S : Sylow p H) :
    Cp (G := H) K S → Cp (G := H') K (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  intro hS
  let S' : Sylow p H' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  intro W' hW'ne hW'le g' hW'g'
  let W : Set H := e ⁻¹' W'
  have hWne : W.Nonempty := by
    rcases hW'ne with ⟨w', hw'⟩
    refine ⟨e.symm w', ?_⟩
    simpa [W] using hw'
  have hWle : W ⊆ (S : Subgroup H) := by
    intro x hx
    have hx' : e x ∈ (S' : Subgroup H') := hW'le hx
    rcases (Subgroup.mem_map.mp hx') with ⟨s, hs, hse⟩
    have : x = s := e.injective hse.symm
    exact this ▸ hs
  have hWg : conjSubset (e.symm g') W ⊆ (S : Subgroup H) := by
    intro x hx
    have hx' : e x ∈ conjSubset g' W' := by
      rcases hx with ⟨w, hw, rfl⟩
      refine ⟨e w, hw, ?_⟩
      simp [map_mul, map_inv]
    have hxS' : e x ∈ (S' : Subgroup H') := hW'g' hx'
    rcases (Subgroup.mem_map.mp hxS') with ⟨s, hs, hse⟩
    have : x = s := e.injective hse.symm
    exact this ▸ hs
  rcases hS W hWne hWle (e.symm g') hWg with ⟨c, n, hc, hn, hg⟩
  refine ⟨e c, e n, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hc' : (e.symm y) * c = c * (e.symm y) :=
      (Subgroup.mem_centralizer_iff.mp hc (e.symm y) (by simpa [W] using hy))
    simpa [map_mul] using congrArg e hc'
  · have hK : K.K (S' : Subgroup H') = (K.K (S : Subgroup H)).map e.toMonoidHom := by
      simpa [S'] using (K_commutes_of_injective_on K e.toMonoidHom (S : Subgroup H)
        (by
          intro a b h
          exact (S : Subgroup H).subtype_injective (e.injective h)))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
    rw [hK]
    calc
      ((K.K (S : Subgroup H)).map e.toMonoidHom).map (MulAut.conj (e n)).toMonoidHom
          = (K.K (S : Subgroup H)).map
              ((MulAut.conj (e n)).toMonoidHom.comp e.toMonoidHom) := by
                rw [Subgroup.map_map]
      _ = (K.K (S : Subgroup H)).map
              (e.toMonoidHom.comp (MulAut.conj n).toMonoidHom) := by
                have hconj_comm : (MulAut.conj (e n)).toMonoidHom.comp e.toMonoidHom =
                    e.toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
                  ext w
                  simp [MulAut.conj_apply, map_mul, map_inv]
                rw [hconj_comm]
      _ = ((K.K (S : Subgroup H)).map (MulAut.conj n).toMonoidHom).map e.toMonoidHom := by
                rw [Subgroup.map_map]
      _ = (K.K (S : Subgroup H)).map e.toMonoidHom := by
                simpa using congrArg (fun X : Subgroup H => X.map e.toMonoidHom) hn
  · simpa [map_mul] using congrArg e hg

/-- `(C_p)` is invariant under group isomorphisms (both directions). -/
private lemma cp_congr {H H' : Type u} [Group H] [Group H'] [Finite H] [Finite H']
    {p : ℕ} [Fact p.Prime] (K : CharacteristicFunctor p) (e : H ≃* H') (S : Sylow p H) :
    Cp (G := H) K S ↔ Cp (G := H') K (S.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  constructor
  · exact cp_map K e S
  · intro hS'
    have h := cp_map K e.symm (S.mapSurjective (f := e.toMonoidHom) e.surjective) hS'
    rw [sylow_map_map] at h
    exact h

/-- `SatisfiesCp` is invariant under group isomorphisms. -/
private lemma satisfiesCp_congr {H H' : Type u} [Group H] [Group H'] [Finite H] [Finite H']
    {p : ℕ} [Fact p.Prime] (K : CharacteristicFunctor p) (e : H ≃* H') :
    SatisfiesCp (p := p) K H ↔ SatisfiesCp (p := p) K H' := by
  constructor
  · intro h S'
    have hS : Cp (G := H) K (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) :=
      h (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
    have hc : Cp (G := H') K
        ((S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective).mapSurjective
          (f := e.toMonoidHom) e.surjective) :=
      cp_map K e (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective) hS
    have hsyl : (S'.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective).mapSurjective
          (f := e.toMonoidHom) e.surjective = S' := by
      simpa using sylow_map_map (e := e.symm) (S := S')
    rw [hsyl] at hc
    exact hc
  · intro h S
    have hS' : Cp (G := H') K (S.mapSurjective (f := e.toMonoidHom) e.surjective) :=
      h (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hc : Cp (G := H) K
        ((S.mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective
          (f := e.symm.toMonoidHom) e.symm.surjective) :=
      cp_map K e.symm (S.mapSurjective (f := e.toMonoidHom) e.surjective) hS'
    have hsyl : (S.mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective
          (f := e.symm.toMonoidHom) e.symm.surjective = S := by
      simpa using sylow_map_map (e := e) (S := S)
    rw [hsyl] at hc
    exact hc

/-- The quotient `⊤ ⧸ P.subgroupOf ⊤` of the subgroup `⊤ ≤ G` is canonically isomorphic
to the ambient quotient `G ⧸ P`. -/
private def top_quotient_congr (P : Subgroup G) [P.Normal] :
    (↥(⊤ : Subgroup G) ⧸ P.subgroupOf (⊤ : Subgroup G)) ≃* (G ⧸ P) := by
  let e : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have he : (P.subgroupOf (⊤ : Subgroup G)).map e.toMonoidHom = P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, by simp⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact QuotientGroup.congr (G := ↥(⊤ : Subgroup G)) (H := G)
    (G' := P.subgroupOf (⊤ : Subgroup G)) (H' := P) e he

/-! ## The `p'`-elements of `C_G(\bar W)` lie in `C_G(WP)` (paper (5.9)) -/

/-- Conjugation by `x ∈ N_G(U)` as an automorphism of `U`. -/
private def conjAut {G : Type*} [Group G] (U : Subgroup G) (x : G)
    (hxN : x ∈ Subgroup.normalizer (U : Set G)) : MulAut ↥U where
  toFun u := ⟨x⁻¹ * (u : G) * x, by
    simpa using (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem (H := Subgroup.normalizer (U : Set G)) hxN) (u : G)).mp u.2⟩
  invFun u := ⟨x * (u : G) * x⁻¹,
    (Subgroup.mem_normalizer_iff.mp hxN (u : G)).mp u.2⟩
  left_inv u := by
    ext
    simp [mul_assoc]
  right_inv u := by
    ext
    simp [mul_assoc]
  map_mul' u v := by
    ext
    simp [mul_assoc]

/-- If `G / C_G(P)` is a `p`-group (which holds e.g. when `G = C_G(P)·S` for a Sylow
`p`-subgroup `S` of `G`), then every `p'`-element of `G` lies in `C_G(P)`.  (Paper:
"Since `G/C(P)` is a `p`-group, every `p'`-element `x` of `C_G(\bar W)` lies in
`C(P)`.") -/
private lemma p'_element_mem_centralizer_of_CG_eq_top {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (P : Subgroup G) [P.Normal] (x : G)
    (hCG : IsPGroup p (G ⧸ Subgroup.centralizer (P : Set G))) (hx : ¬ p ∣ orderOf x) :
    x ∈ Subgroup.centralizer (P : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hord : orderOf (x : G ⧸ C) ∣ orderOf x := by
    rw [orderOf_dvd_iff_pow_eq_one]
    change (QuotientGroup.mk' C x) ^ orderOf x = 1
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases (IsPGroup.iff_orderOf.mp hCG) (x : G ⧸ C) with ⟨k, hk⟩
  have hk0 : k = 0 := by
    by_contra hkne
    have hdvd_p : p ∣ orderOf (x : G ⧸ C) := by
      rw [hk]
      exact dvd_pow_self p hkne
    exact hx (hdvd_p.trans hord)
  have h1 : (x : G ⧸ C) = 1 := by
    rw [← orderOf_eq_one_iff]
    simpa [hk0] using hk
  exact (QuotientGroup.eq_one_iff x).mp h1

/-- An automorphism of a `p`-group fixing `P` pointwise and each coset of `P` (an element
of `lemma5_3Centralizer P`, a `p`-group by Lemma 5.3) whose order divides a `p'`-number
is trivial. -/
private lemma pAut_eq_one_of_orderOf_p' {p : ℕ} [Fact p.Prime] {S : Type*} [Group S]
    [Finite S] (hS : IsPGroup p S) (P : Subgroup S) [P.Normal] (a : MulAut S)
    (ha : a ∈ lemma5_3Centralizer P) {n : ℕ} (hn : ¬ p ∣ n) (han : a ^ n = 1) : a = 1 := by
  have hord_dvd : orderOf a ∣ n := (orderOf_dvd_iff_pow_eq_one (x := a) (n := n)).2 han
  have hpg : IsPGroup p (↥(lemma5_3Centralizer P)) := lemma5_3 hS P
  obtain ⟨k, hk⟩ := hpg ⟨a, ha⟩
  have hk' : a ^ p ^ k = 1 := by
    exact congrArg Subtype.val hk
  have hord_p : orderOf a ∣ p ^ k := (orderOf_dvd_iff_pow_eq_one (x := a) (n := p ^ k)).2 hk'
  obtain ⟨j, _hjle, hj⟩ := (Nat.dvd_prime_pow (p := p) (m := k) (i := orderOf a)
    (Fact.out : p.Prime)).1 hord_p
  have hj0 : j = 0 := by
    by_contra hjne
    have hpd : p ∣ orderOf a := by
      rw [hj]
      exact dvd_pow_self p hjne
    exact hn (hpd.trans hord_dvd)
  have h1 : orderOf a = 1 := by
    simpa [hj0] using hj
  exact orderOf_eq_one_iff.mp h1

/-- If `x ∈ N_G(U)` fixes the normal subgroup `P` of the `p`-group `U` pointwise and every
coset of `P` in `U`, and `x` is a `p'`-element, then `x` centralizes `U` pointwise.  This
is the paper's application of Lemma 5.3: "Thus `x` centralizes `WP/P` and `P`.  By Lemma
5.3, `x` centralizes `WP`." -/
private lemma p'_element_centralizes_WP {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (U : Subgroup G) (hU : IsPGroup p U) (P : Subgroup ↥U) [P.Normal] (x : G)
    (hxN : x ∈ Subgroup.normalizer (U : Set G))
    (hxP : ∀ u : ↥U, u ∈ P → conjAut U x hxN u = u)
    (hxq : ∀ u : ↥U, QuotientGroup.mk' P (conjAut U x hxN u) = QuotientGroup.mk' P u)
    (hx_order : ¬ p ∣ orderOf x) : ∀ u : ↥U, conjAut U x hxN u = u := by
  let a : MulAut ↥U := conjAut U x hxN
  have ha : a ∈ lemma5_3Centralizer P := by
    rw [mem_lemma5_3Centralizer]
    exact ⟨hxP, hxq⟩
  have hpow : ∀ n : ℕ, a ^ n = conjAut U (x ^ n)
      ((Subgroup.normalizer (U : Set G)).pow_mem hxN n) := by
    intro n
    induction n with
    | zero =>
        ext u
        simp [a, conjAut]
    | succ n ih =>
        ext u
        rw [pow_succ, ih]
        simp [a, conjAut]
        group
  have han : a ^ orderOf x = 1 := by
    rw [hpow (orderOf x)]
    ext u
    simp [conjAut, pow_orderOf_eq_one]
  have h1 : a = 1 := pAut_eq_one_of_orderOf_p' hU P a ha hx_order han
  intro u
  have h2 := congrArg (fun φ : MulAut ↥U => φ u) h1
  simpa using h2


/-- If `C ⊴ G`, then every element of `C ⊔ S` is a product `c·s` with `c ∈ C`,
`s ∈ S` (the sup is the product since `S` normalizes `C`). -/
private lemma mem_sup_mul_of_normal {G : Type*} [Group G] {C S : Subgroup G} (hC : C.Normal)
    {x : G} (hx : x ∈ C ⊔ S) : ∃ c : G, c ∈ C ∧ ∃ s : G, s ∈ S ∧ x = c * s := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyC | hyS
    · exact ⟨y, hyC, 1, S.one_mem, by simp⟩
    · exact ⟨1, C.one_mem, y, hyS, by simp⟩
  · exact ⟨1, C.one_mem, 1, S.one_mem, by simp⟩
  · rintro a b hxa hxb ⟨ca, hca, sa, hsa, rfl⟩ ⟨cb, hcb, sb, hsb, rfl⟩
    refine ⟨ca * (sa * cb * sa⁻¹), C.mul_mem hca (hC.conj_mem cb hcb sa),
      sa * sb, S.mul_mem hsa hsb, ?_⟩
    group
  · rintro a hxa ⟨ca, hca, sa, hsa, rfl⟩
    refine ⟨sa⁻¹ * ca⁻¹ * sa,
      by simpa using (hC.conj_mem (ca⁻¹) (C.inv_mem hca) (sa⁻¹)), sa⁻¹, S.inv_mem hsa, ?_⟩
    group

/-! ## Theorem 5.2 -/

/-- **Registered bridge.**  Paper (5.4)+(5.5) (L1488–L1501): with `P = O_p(G)`,
`C = C_G(P)`, `N = N_G(K(S))` and `R = S ∩ PC`, one has `N_G(R) ⊔ C = ⊤`, i.e.
`G = C·N_G(R)`; and with `M = O_{p'}(N_G(R))`, hypothesis (a) of Theorem 5.2
(through Lemma 5.2 applied to `Q = N_G(R)/M`) and the Frattini argument give
`N_G(R) = M·(N_G(R) ∩ N)`, hence (as `[P, M] ⊆ 1`) `G = C·N`.

*Why:* the chain `C_S(P₁) ⊆ C_S(R) ⊆ C_S(P) ⊆ R ⊆ P₁` (with
`P₁ = S ∩ O_{p',p}(N_G(R))`) supplies Lemma 5.2's hypothesis in the quotient
`Q = N_G(R)/M`; hypothesis (a) gives `K(SM/M) ⊴ Q`; the iso-transfer of the
characteristic functor (`K_commutes_of_injective_on`) identifies `K(SM/M)` with
`K(S)M/M`, so `K(S)·M ⊴ N_G(R)`; `K(S)` is a Sylow `p`-subgroup of `K(S)·M`, so the
Frattini argument splits `N_G(R) = M·N_{N_G(R)}(K(S))`.  The conclusion is the
decomposition `G = C·N` used in both cases of the proof.

The conclusion is the full decomposition `G = C·N` (as the subgroup equality
`C ⊔ N = ⊤`), combining (5.4) and (5.5).

*Elimination condition:* replace the `sorry` by formalizing the Lemma 5.2 chain
(`sylow_inf_normal`, `relIndex_sup_eq_relIndex_inf` of this file give the
`(C_p)`-style counting; `lemma5_2` of `Glauberman.Lemma5_2` gives the quotient
centralizer containment), the subquotient application of hypothesis (a), and the
two Frattini arguments (`frattini_sup_eq_top` of this file). -/
public theorem theorem5_2_step_I {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (K : CharacteristicFunctor p) (S : Sylow p G)
    (hA : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Subgroup.centralizer ((pCore p (H ⧸ N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) ≤
        (pCore p (H ⧸ N) : Subgroup (H ⧸ N)) →
      ∀ S₀ : Sylow p (H ⧸ N), (K.K (S₀ : Subgroup (H ⧸ N))).Normal)
    (_hP : pCore p G ≠ ⊥) :
    let P : Subgroup G := pCore p G
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
    C ⊔ N = ⊤ := by
  classical
  dsimp only
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let L : Subgroup G := P ⊔ C
  let R : Subgroup G := (S : Subgroup G) ⊓ L
  let NR : Subgroup G := Subgroup.normalizer (R : Set G)
  let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have : C.Normal := by
    dsimp [C]
    infer_instance
  have : L.Normal := by
    dsimp [L]
    infer_instance
  have hP_le_S : P ≤ (S : Subgroup G) := by
    simpa [P] using pCore_le_sylow (G := G) S
  have hP_le_R : P ≤ R := by
    exact le_inf hP_le_S le_sup_left
  have hR_le_NR : R ≤ NR := by
    exact Subgroup.le_normalizer
  have hP_le_NR : P ≤ NR := hP_le_R.trans hR_le_NR
  have hS_le_NR : (S : Subgroup G) ≤ NR := by
    intro s hs
    apply Subgroup.inf_normalizer_le_normalizer_inf
    exact ⟨Subgroup.le_normalizer hs,
      (Subgroup.normalizer_eq_top_iff.mpr (inferInstance : L.Normal)) ▸ trivial⟩
  have hfrattini_R : NR ⊔ L = ⊤ := by
    simpa [NR, R] using frattini_sup_eq_top S L
  have hCNR : C ⊔ NR = ⊤ := by
    apply top_unique
    rw [← hfrattini_R]
    exact sup_le le_sup_right
      (sup_le (hP_le_NR.trans le_sup_right) le_sup_left)

  let SNR : Sylow p (↥NR) := S.subtype hS_le_NR
  let RNR : Subgroup (↥NR) := R.subgroupOf NR
  have hRNR_normal : RNR.Normal := by
    simpa [RNR, NR] using (Subgroup.normal_in_normalizer (H := R))
  let : RNR.Normal := hRNR_normal
  have hRNR_p : IsPGroup p RNR := by
    have hR_p : IsPGroup p R := S.isPGroup'.to_inf_left
    exact hR_p.of_equiv (Subgroup.subgroupOfEquivOfLe hR_le_NR).symm
  have hRNR_le_SNR : RNR ≤ (SNR : Subgroup (↥NR)) := by
    intro x hx
    change (x : G) ∈ (S : Subgroup G)
    change (x : G) ∈ R at hx
    exact hx.1
  have hRNR_le_Op : RNR ≤ Op_p'p p (↥NR) := by
    let M : Subgroup (↥NR) := pPrimeCore p (↥NR)
    let q : (↥NR) →* (↥NR ⧸ M) := QuotientGroup.mk' M
    have hmap_le : RNR.map q ≤ pCore p (↥NR ⧸ M) := by
      exact le_sSup ⟨hRNR_normal.map q (QuotientGroup.mk'_surjective M),
        IsPGroup.map hRNR_p q⟩
    intro x hx
    change q x ∈ pCore p (↥NR ⧸ M)
    exact hmap_le (Subgroup.mem_map_of_mem q hx)
  let P1 : Subgroup (↥NR) := (SNR : Subgroup (↥NR)) ⊓ Op_p'p p (↥NR)
  have hRNR_le_P1 : RNR ≤ P1 := le_inf hRNR_le_SNR hRNR_le_Op
  have hCS_NR : (SNR : Subgroup (↥NR)) ⊓
      Subgroup.centralizer (P1 : Set (↥NR)) ≤ P1 := by
    intro x hx
    apply hRNR_le_P1
    change (x : G) ∈ R
    refine ⟨?_, Subgroup.mem_sup_right ?_⟩
    · have hxSNR := hx.1
      change (x : G) ∈ (S : Subgroup G) at hxSNR
      exact hxSNR
    · rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      let yNR : ↥NR := ⟨y, hP_le_NR hyP⟩
      have hyRNR : yNR ∈ RNR := by
        change y ∈ R
        exact hP_le_R hyP
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2) yNR (hRNR_le_P1 hyRNR)
      exact congrArg Subtype.val hcomm
  have hcentral_quot :
      Subgroup.centralizer
          ((pCore p (↥NR ⧸ pPrimeCore p (↥NR)) :
            Subgroup (↥NR ⧸ pPrimeCore p (↥NR))) : Set (↥NR ⧸ pPrimeCore p (↥NR))) ≤
        pCore p (↥NR ⧸ pPrimeCore p (↥NR)) := by
    apply lemma5_2 p SNR
    simpa [P1] using hCS_NR

  let M : Subgroup (↥NR) := pPrimeCore p (↥NR)
  let q : (↥NR) →* (↥NR ⧸ M) := QuotientGroup.mk' M
  let Sbar : Sylow p (↥NR ⧸ M) :=
    SNR.mapSurjective (f := q) (QuotientGroup.mk'_surjective M)
  let SK : Subgroup (↥NR) := K.K (SNR : Subgroup (↥NR))
  have hKbar_normal : (K.K (Sbar : Subgroup (↥NR ⧸ M))).Normal := by
    exact hA NR M (by simpa [M] using hcentral_quot) Sbar
  have hq_inj_SNR :
      Function.Injective (q.comp (SNR : Subgroup (↥NR)).subtype) := by
    simpa [q, M] using
      (quotient_pPrimeCore_subgroupMap_injective (G := ↥NR) (p := p)
        (SNR : Subgroup (↥NR)) SNR.isPGroup')
  have hKmap : K.K (Sbar : Subgroup (↥NR ⧸ M)) = SK.map q := by
    simpa [Sbar, SK] using
      (K_commutes_of_injective_on K q (SNR : Subgroup (↥NR)) hq_inj_SNR)
  have hSKmap_normal : (SK.map q).Normal := by
    rw [← hKmap]
    exact hKbar_normal
  let A : Subgroup (↥NR) := SK ⊔ M
  have hA_eq_comap : A = Subgroup.comap q (SK.map q) := by
    symm
    calc
      Subgroup.comap q (SK.map q) = SK ⊔ q.ker := Subgroup.comap_map_eq q SK
      _ = SK ⊔ M := by simp [q, M, QuotientGroup.ker_mk']
      _ = A := rfl
  have hA_normal : A.Normal := by
    rw [hA_eq_comap]
    exact hSKmap_normal.comap q
  let : A.Normal := hA_normal
  have hSK_le_SNR : SK ≤ (SNR : Subgroup (↥NR)) := K.K_le _
  have hSNR_inf_A : (SNR : Subgroup (↥NR)) ⊓ A = SK := by
    apply le_antisymm
    · intro x hx
      have hxcomap : x ∈ Subgroup.comap q (SK.map q) := by
        rw [← hA_eq_comap]
        exact hx.2
      rcases Subgroup.mem_map.mp hxcomap with ⟨k, hkSK, hkx⟩
      let xs : ↥(SNR : Subgroup (↥NR)) := ⟨x, hx.1⟩
      let ks : ↥(SNR : Subgroup (↥NR)) := ⟨k, hSK_le_SNR hkSK⟩
      have hxsks : xs = ks := by
        apply hq_inj_SNR
        simpa [xs, ks] using hkx.symm
      have hxk : x = k := congrArg Subtype.val hxsks
      rw [hxk]
      exact hkSK
    · exact le_inf hSK_le_SNR le_sup_left
  have hfrattini_SK : Subgroup.normalizer (SK : Set (↥NR)) ⊔ A = ⊤ := by
    have hfr := frattini_sup_eq_top SNR A
    rwa [hSNR_inf_A] at hfr
  have hNR_decomp : Subgroup.normalizer (SK : Set (↥NR)) ⊔ M = ⊤ := by
    calc
      Subgroup.normalizer (SK : Set (↥NR)) ⊔ M =
          Subgroup.normalizer (SK : Set (↥NR)) ⊔ (SK ⊔ M) := by
            rw [← sup_assoc, sup_eq_left.mpr Subgroup.le_normalizer]
      _ = Subgroup.normalizer (SK : Set (↥NR)) ⊔ A := rfl
      _ = ⊤ := hfrattini_SK

  have hSNR_map : (SNR : Subgroup (↥NR)).map NR.subtype = (S : Subgroup G) := by
    simp [SNR, inf_eq_left.mpr hS_le_NR]
  have hSK_map : SK.map NR.subtype = K.K (S : Subgroup G) := by
    have hmap := K_commutes_of_injective_on K NR.subtype
      (SNR : Subgroup (↥NR)) (by
        intro a b hab
        exact Subtype.ext (NR.subtype_injective hab))
    rw [hSNR_map] at hmap
    simpa [SK] using hmap.symm
  have hnormalizer_map_le_N :
      (Subgroup.normalizer (SK : Set (↥NR))).map NR.subtype ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xNR, hxNR, rfl⟩
    have hxG := (mem_normalizer_map_subtype_iff (G := G) SK xNR).mp hxNR
    rw [hSK_map] at hxG
    exact hxG

  let PNR : Subgroup (↥NR) := P.subgroupOf NR
  have hPNR_normal : PNR.Normal := by
    simpa [PNR] using (Subgroup.Normal.subgroupOf (inferInstance : P.Normal) NR)
  let : PNR.Normal := hPNR_normal
  have hPNR_p : IsPGroup p PNR := by
    exact (pCore_isPGroup (G := G) (p := p)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hP_le_NR).symm
  have hM_central_PNR : M ≤ Subgroup.centralizer (PNR : Set (↥NR)) := by
    simpa [M] using
      (pPrimeCore_le_centralizer_of_normal_pgroup (G := ↥NR) p PNR hPNR_p)
  have hMmap_le_C : M.map NR.subtype ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xNR, hxM, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    let yNR : ↥NR := ⟨y, hP_le_NR hyP⟩
    have hyPNR : yNR ∈ PNR := by
      change y ∈ P
      exact hyP
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp (hM_central_PNR hxM)) yNR hyPNR)
  have hNR_le_CN : NR ≤ C ⊔ N := by
    calc
      NR = (⊤ : Subgroup (↥NR)).map NR.subtype := by
        symm
        ext x
        simp
      _ = (Subgroup.normalizer (SK : Set (↥NR)) ⊔ M).map NR.subtype := by
        rw [hNR_decomp]
      _ = (Subgroup.normalizer (SK : Set (↥NR))).map NR.subtype ⊔ M.map NR.subtype := by
        rw [Subgroup.map_sup]
      _ ≤ C ⊔ N := sup_le
        (hnormalizer_map_le_N.trans le_sup_right) (hMmap_le_C.trans le_sup_left)
  apply top_unique
  rw [← hCNR]
  exact sup_le le_sup_left hNR_le_CN

/-- **Registered bridge.**  The case `C(P)S < G` (L1503–L1512): with `G = C·N`
(step I), for every `W ⊆ S` and `g` with `W^g ⊆ S`, one has
`g = cn` with `c ∈ C_G(W)`, `n ∈ N = N_G(K(S))`.

*Why:* write `g = dn` with `d ∈ C(P)`, `n ∈ N` (step I); then
`W^d = W^{gn⁻¹} ⊆ N`; since `d ∈ C(P)S < G` and `W ⊆ C(P)S`, the subgroup
`C(P)S` satisfies `(C_p*)` (via `lemma5_1` and hypothesis (b) applied to the
subquotient `C(P)S ⧸ ⊥`, whose order is `< |G|`), giving `d = cm` with
`c ∈ C(W)`, `m ∈ N`, and `g = c(mn)`.

*Elimination condition:* replace the `sorry` by the subquotient application of
hypothesis (b) to `C(P)S ⧸ ⊥` transported by `satisfiesCp_congr`/`top_quotient_congr`,
the `(C_p*)`-in-`C(P)S` argument via `lemma5_1`, and the bookkeeping
`W^d ⊆ N` (from `W^g ⊆ S ⊆ N`). -/
public theorem theorem5_2_step_II {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (K : CharacteristicFunctor p) (S : Sylow p G)
    (_hA : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Subgroup.centralizer ((pCore p (H ⧸ N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) ≤
        (pCore p (H ⧸ N) : Subgroup (H ⧸ N)) →
      ∀ S₀ : Sylow p (H ⧸ N), (K.K (S₀ : Subgroup (H ⧸ N))).Normal)
    (hB : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Nat.card (H ⧸ N) < Nat.card G → SatisfiesCp (p := p) K (H ⧸ N))
    (_hP : pCore p G ≠ ⊥)
    (hI : let P : Subgroup G := pCore p G
      let C : Subgroup G := Subgroup.centralizer (P : Set G)
      let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
      C ⊔ N = ⊤) :
    let P : Subgroup G := pCore p G
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
    C ⊔ (S : Subgroup G) ≠ ⊤ →
      ∀ W : Set G, W.Nonempty → W ⊆ (S : Subgroup G) →
        ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
          ∃ c n : G,
            c ∈ Subgroup.centralizer (W : Set G) ∧ n ∈ N ∧ g = c * n := by
  classical
  dsimp only
  intro hCS W hWne hWle g hWg
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
  let M : Subgroup G := C ⊔ (S : Subgroup G)
  have hI' : C ⊔ N = ⊤ := by
    simpa [P, C, N] using hI
  have hMne : M ≠ ⊤ := by
    simpa [M, C, P] using hCS
  have hS_le_M : (S : Subgroup G) ≤ M := le_sup_right
  let S_M : Sylow p ↑M := S.subtype hS_le_M
  have hMcard : Nat.card M < Nat.card G := by
    have hlt : M < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr hMne
    simpa using natCard_lt_of_subgroup_lt hlt
  have hMquot_card : Nat.card (M ⧸ (⊥ : Subgroup M)) < Nat.card G := by
    calc
      Nat.card (M ⧸ (⊥ : Subgroup M)) = Nat.card M :=
        Nat.card_congr (QuotientGroup.quotientBot (G := ↑M)).toEquiv
      _ < Nat.card G := hMcard
  have hCp_quot : SatisfiesCp (p := p) K (M ⧸ (⊥ : Subgroup M)) :=
    hB M (⊥ : Subgroup M) hMquot_card
  have hCp_M : SatisfiesCp (p := p) K ↑M :=
    (satisfiesCp_congr K (QuotientGroup.quotientBot (G := ↑M))).mp hCp_quot
  have hStar : CpStar (G := ↑M) K S_M :=
    (lemma5_1 (G := ↑M) K S_M).mp (hCp_M S_M)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  have : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer
  have hg_mem : g ∈ C ⊔ N := by
    rw [hI']
    trivial
  obtain ⟨d, hdC, n, hnN, hg⟩ :=
    mem_sup_mul_of_normal (C := C) (S := N) (inferInstance : C.Normal) hg_mem
  let W₀ : Subgroup G := Subgroup.closure W
  have hW₀_le_S : W₀ ≤ (S : Subgroup G) :=
    (Subgroup.closure_le (K := (S : Subgroup G))).mpr hWle
  have hW₀p : IsPGroup p W₀ := IsPGroup.to_le S.isPGroup' hW₀_le_S
  have hW₀g_le_S : conjSubgroup g W₀ ≤ (S : Subgroup G) := by
    rw [conjSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := (S : Subgroup G))).mpr ?_
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    exact hWg ⟨w, hw, by simp⟩
  have hS_le_N : (S : Subgroup G) ≤ N := by
    simpa [N] using sylow_le_normalizer_K K S
  have hW₀d_le_N : conjSubgroup d W₀ ≤ N := by
    have hcomp : conjSubgroup d W₀ = conjSubgroup n⁻¹ (conjSubgroup g W₀) := by
      symm
      calc
        conjSubgroup n⁻¹ (conjSubgroup g W₀) = conjSubgroup (g * n⁻¹) W₀ :=
          conjSubgroup_comp g n⁻¹ W₀
        _ = conjSubgroup d W₀ := by rw [hg]; simp
    rw [hcomp]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨w, hw, rfl⟩
    simp [MulAut.conj_apply]
    exact N.mul_mem (N.mul_mem hnN (hS_le_N (hW₀g_le_S hw))) (N.inv_mem hnN)
  have hdM : d ∈ M := (show C ≤ M from le_sup_left) hdC
  let d_M : ↑M := ⟨d, hdM⟩
  have hW₀_le_M : W₀ ≤ M := hW₀_le_S.trans hS_le_M
  let W_M : Subgroup ↑M := W₀.subgroupOf M
  have hW_Mp : IsPGroup p W_M :=
    hW₀p.of_equiv (Subgroup.subgroupOfEquivOfLe hW₀_le_M).symm
  have hS_M_map : (S_M : Subgroup ↑M).map M.subtype = (S : Subgroup G) := by
    simpa [S_M] using Subgroup.map_subgroupOf_eq_of_le hS_le_M
  have hK_map : (K.K (S_M : Subgroup ↑M)).map M.subtype =
      K.K (S : Subgroup G) := by
    calc
      (K.K (S_M : Subgroup ↑M)).map M.subtype =
          K.K ((S_M : Subgroup ↑M).map M.subtype) := by
            exact (K.K_map M.subtype (S_M : Subgroup ↑M)
              (M.subtype_injective.comp (S_M : Subgroup ↑M).subtype_injective)).symm
      _ = K.K (S : Subgroup G) := by rw [hS_M_map]
  let N_M : Subgroup ↑M :=
    Subgroup.normalizer ((K.K (S_M : Subgroup ↑M) : Subgroup ↑M) : Set ↑M)
  have hN_M : N_M = N.comap M.subtype := by
    ext x
    change x ∈ Subgroup.normalizer
          ((K.K (S_M : Subgroup ↑M) : Subgroup ↑M) : Set ↑M) ↔
        (x : G) ∈ N
    rw [mem_normalizer_map_subtype_iff
      (M := M) (H := K.K (S_M : Subgroup ↑M)) (x := x)]
    rw [hK_map]
  have hW_M_le_N_M : W_M ≤ N_M := by
    rw [hN_M, ← Subgroup.map_le_iff_le_comap]
    rw [Subgroup.map_subgroupOf_eq_of_le hW₀_le_M]
    exact hW₀_le_S.trans hS_le_N
  have hconj_map : (conjSubgroup d_M W_M).map M.subtype = conjSubgroup d W₀ := by
    simpa [W_M, d_M, conjSubgroup] using
      (map_subtype_map_conj (N := M) (W := W₀) hW₀_le_M (m := d_M⁻¹))
  have hW_Md_le_N_M : conjSubgroup d_M W_M ≤ N_M := by
    rw [hN_M, ← Subgroup.map_le_iff_le_comap, hconj_map]
    exact hW₀d_le_N
  rcases hStar W_M hW_Mp hW_M_le_N_M d_M hW_Md_le_N_M with
    ⟨c_M, m_M, hc_M, hm_M, hd_eq⟩
  let c₀ : G := c_M
  let m₀ : G := m_M
  have hd_eq' : d = c₀ * m₀ := by
    have := congrArg (fun x : ↑M => (x : G)) hd_eq
    simpa [d_M, c₀, m₀] using this
  have hc₀W : c₀ ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw₀ : w ∈ W₀ := Subgroup.subset_closure hw
    have hwM : ⟨w, hW₀_le_M hw₀⟩ ∈ W_M := Subgroup.mem_subgroupOf.mpr hw₀
    have hcomm := (Subgroup.mem_centralizer_iff.mp hc_M) ⟨w, hW₀_le_M hw₀⟩ hwM
    simpa [c₀] using congrArg Subtype.val hcomm
  have hm₀N : m₀ ∈ N := by
    have hm_M' := hm_M
    change m_M ∈ N_M at hm_M'
    rw [hN_M] at hm_M'
    exact hm_M'
  refine ⟨c₀, m₀ * n, hc₀W, N.mul_mem hm₀N hnN, ?_⟩
  rw [hg, hd_eq']
  group

/-- **Registered bridge.**  The case `C(P)S = G` (L1513–L1528): with `G = C·N`
(step I) and `G = C·S`, for every `W ⊆ S` with `W ⊄ P` and every `g` with
`W^g ⊆ S`, one has `g = cn` with `c ∈ C_G(W̄)` (`W̄ = WP/P ⊆ G/P`), `n ∈ N`.

*Why:* hypothesis (b) applied to the quotient `G ⧸ P` (order `< |G|` since
`P ≠ 1`) gives (5.6) `ḡ = c̄n̄`; with `T/P = K(S̄)` one has `P < T`,
`S ⊆ N(T) < G` (5.7, using `K_conj`); a lift `n` of `n̄` lies in `N(T)` with
`W^n ⊆ S`, and hypothesis (b) applied to the subquotient `N(T) ⧸ ⊥` gives
`dm = n` with `d ∈ C(W)`, `m ∈ N`; then `g ∈ C_G(W̄)·N` (5.8).

*Elimination condition:* replace the `sorry` by the two subquotient applications
of hypothesis (b) (transported by `satisfiesCp_congr`/`top_quotient_congr`), the
`T` preimage construction, and the bookkeeping `W^n ⊆ S`, `S ⊆ N(T) < G`. -/
public theorem theorem5_2_step_III {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (K : CharacteristicFunctor p) (S : Sylow p G)
    (_hA : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Subgroup.centralizer ((pCore p (H ⧸ N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) ≤
        (pCore p (H ⧸ N) : Subgroup (H ⧸ N)) →
      ∀ S₀ : Sylow p (H ⧸ N), (K.K (S₀ : Subgroup (H ⧸ N))).Normal)
    (hB : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Nat.card (H ⧸ N) < Nat.card G → SatisfiesCp (p := p) K (H ⧸ N))
    (hP : pCore p G ≠ ⊥)
    (_hI : let P : Subgroup G := pCore p G
      let C : Subgroup G := Subgroup.centralizer (P : Set G)
      let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
      C ⊔ N = ⊤) :
    let P : Subgroup G := pCore p G
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
    C ⊔ (S : Subgroup G) = ⊤ →
      ∀ W : Set G, W.Nonempty → W ⊆ (S : Subgroup G) → ¬ W ⊆ (P : Set G) →
        ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
          ∃ c n : G,
            (QuotientGroup.mk' P) c ∈ Subgroup.centralizer ((QuotientGroup.mk' P) '' (W : Set G) : Set (G ⧸ P)) ∧
              n ∈ N ∧ g = c * n := by
  classical
  dsimp only
  intro hCS W hWne hWle hWnotP g hWg
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  let q : G →* G ⧸ P := QuotientGroup.mk' P
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective P
  have hP_le_S : P ≤ (S : Subgroup G) := by
    simpa [P] using pCore_le_sylow (G := G) S
  obtain ⟨w₀, hw₀W, hw₀P⟩ := Set.not_subset.mp hWnotP
  let Sbar : Sylow p (G ⧸ P) := S.mapSurjective (f := q) hq_surj
  have hqw₀_ne : q w₀ ≠ 1 := by
    intro hw
    exact hw₀P ((QuotientGroup.eq_one_iff w₀).mp hw)
  have hqw₀_mem : q w₀ ∈ (Sbar : Subgroup (G ⧸ P)) :=
    Subgroup.mem_map_of_mem q (hWle hw₀W)
  have hSbar_ne : (Sbar : Subgroup (G ⧸ P)) ≠ ⊥ := by
    intro hbot
    have : q w₀ ∈ (⊥ : Subgroup (G ⧸ P)) := by simpa [hbot] using hqw₀_mem
    exact hqw₀_ne (by simpa using this)
  let Kbar : Subgroup (G ⧸ P) := K.K (Sbar : Subgroup (G ⧸ P))
  have hKbar_ne : Kbar ≠ ⊥ := by
    exact K.K_nontrivial (Sbar : Subgroup (G ⧸ P)) Sbar.isPGroup' hSbar_ne
  have hcomap_Sbar : (Sbar : Subgroup (G ⧸ P)).comap q = (S : Subgroup G) := by
    simpa [Sbar, q, QuotientGroup.ker_mk'] using
      (Subgroup.comap_map_eq_self (f := q) (H := (S : Subgroup G))
        (by simpa [q, QuotientGroup.ker_mk'] using hP_le_S))
  let T : Subgroup G := Kbar.comap q
  have hT_le_S : T ≤ (S : Subgroup G) := by
    calc
      T = Kbar.comap q := rfl
      _ ≤ (Sbar : Subgroup (G ⧸ P)).comap q :=
        Subgroup.comap_mono (K.K_le (Sbar : Subgroup (G ⧸ P)))
      _ = (S : Subgroup G) := hcomap_Sbar
  have hTp : IsPGroup p T := IsPGroup.to_le S.isPGroup' hT_le_S
  have hP_le_T : P ≤ T := by
    intro x hxP
    change q x ∈ Kbar
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hxP
    rw [hxq]
    exact Kbar.one_mem
  let NT : Subgroup G := Subgroup.normalizer (T : Set G)
  have hS_le_NT : (S : Subgroup G) ≤ NT := by
    intro s hs
    have hqs : q s ∈ (Sbar : Subgroup (G ⧸ P)) :=
      Subgroup.mem_map_of_mem q hs
    have hqsN : q s ∈ Subgroup.normalizer (Kbar : Set (G ⧸ P)) := by
      exact (sylow_le_normalizer_K K Sbar) hqs
    have hscomap : s ∈
        (Subgroup.normalizer (Kbar : Set (G ⧸ P))).comap q := hqsN
    have hnorm := Subgroup.comap_normalizer_eq_of_surjective Kbar hq_surj
    change s ∈ Subgroup.normalizer (T : Set G)
    simpa [T] using (hnorm ▸ hscomap)
  have hNT_ne : NT ≠ ⊤ := by
    intro htop
    have hTnormal : T.Normal := by
      exact Subgroup.normalizer_eq_top_iff.mp (by simpa [NT] using htop)
    have hT_le_P : T ≤ P := by
      simpa [P] using le_pCore_of_normal_isPGroup (G := G) hTnormal hTp
    apply hKbar_ne
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hq_surj y
      have hxT : x ∈ T := by
        change q x ∈ Kbar
        exact hy
      have hxP : x ∈ P := hT_le_P hxT
      have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hxP
      rw [hxq]
      exact (⊥ : Subgroup (G ⧸ P)).one_mem
    · exact bot_le
  have hNT_card : Nat.card NT < Nat.card G := by
    have hlt : NT < (⊤ : Subgroup G) := lt_top_iff_ne_top.mpr hNT_ne
    simpa using natCard_lt_of_subgroup_lt hlt
  have hquot_card : Nat.card (G ⧸ P) < Nat.card G :=
    natCard_quotient_lt_natCard_of_ne_bot P (by simpa [P] using hP)
  have htop_quot_card :
      Nat.card ((⊤ : Subgroup G) ⧸ P.subgroupOf (⊤ : Subgroup G)) < Nat.card G := by
    calc
      Nat.card ((⊤ : Subgroup G) ⧸ P.subgroupOf (⊤ : Subgroup G)) =
          Nat.card (G ⧸ P) := Nat.card_congr (top_quotient_congr P).toEquiv
      _ < Nat.card G := hquot_card
  have hCp_top_quot : SatisfiesCp (p := p) K
      ((⊤ : Subgroup G) ⧸ P.subgroupOf (⊤ : Subgroup G)) :=
    hB (⊤ : Subgroup G) (P.subgroupOf (⊤ : Subgroup G)) htop_quot_card
  have hCp_quot : SatisfiesCp (p := p) K (G ⧸ P) :=
    (satisfiesCp_congr K (top_quotient_congr P)).mp hCp_top_quot
  let Wbar : Set (G ⧸ P) := q '' W
  have hWbar_ne : Wbar.Nonempty := hWne.image q
  have hWbar_le : Wbar ⊆ (Sbar : Subgroup (G ⧸ P)) := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_map_of_mem q (hWle hw)
  have hWbar_g : conjSubset (q g) Wbar ⊆ (Sbar : Subgroup (G ⧸ P)) := by
    rintro _ ⟨wbar, hwbar, rfl⟩
    rcases hwbar with ⟨w, hw, rfl⟩
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * w * g, hWg ⟨w, hw, rfl⟩, ?_⟩
    simp [q]
  rcases (hCp_quot Sbar) Wbar hWbar_ne hWbar_le (q g) hWbar_g with
    ⟨cbar, nbar, hcbar, hnbar, hqg⟩
  obtain ⟨n, hnq⟩ := hq_surj nbar
  have hnT : n ∈ NT := by
    have hncomap : n ∈
        (Subgroup.normalizer (Kbar : Set (G ⧸ P))).comap q := by
      change q n ∈ Subgroup.normalizer (Kbar : Set (G ⧸ P))
      simpa [hnq] using hnbar
    have hnorm := Subgroup.comap_normalizer_eq_of_surjective Kbar hq_surj
    change n ∈ Subgroup.normalizer (T : Set G)
    simpa [T] using (hnorm ▸ hncomap)
  have hWbar_n : conjSubset nbar Wbar ⊆ (Sbar : Subgroup (G ⧸ P)) := by
    rintro _ ⟨wbar, hwbar, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcbar) wbar hwbar
    have hfix : cbar⁻¹ * wbar * cbar = wbar := by
      calc
        cbar⁻¹ * wbar * cbar = cbar⁻¹ * (wbar * cbar) := by group
        _ = cbar⁻¹ * (cbar * wbar) := by rw [hcomm]
        _ = wbar := by group
    have hx := hWbar_g ⟨wbar, hwbar, rfl⟩
    rw [hqg] at hx
    have heq : (cbar * nbar)⁻¹ * wbar * (cbar * nbar) =
        nbar⁻¹ * wbar * nbar := by
      rw [mul_inv_rev]
      calc
        nbar⁻¹ * cbar⁻¹ * wbar * (cbar * nbar) =
            nbar⁻¹ * (cbar⁻¹ * wbar * cbar) * nbar := by group
        _ = nbar⁻¹ * wbar * nbar := by rw [hfix]
    rw [heq] at hx
    exact hx
  have hWn : conjSubset n W ⊆ (S : Subgroup G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hqmem : q (n⁻¹ * w * n) ∈ (Sbar : Subgroup (G ⧸ P)) := by
      have := hWbar_n ⟨q w, ⟨w, hw, rfl⟩, rfl⟩
      rw [map_mul, map_mul, map_inv, hnq]
      exact this
    have hpre : n⁻¹ * w * n ∈ (Sbar : Subgroup (G ⧸ P)).comap q := hqmem
    rw [hcomap_Sbar] at hpre
    exact hpre
  have hNT_quot_card : Nat.card (NT ⧸ (⊥ : Subgroup NT)) < Nat.card G := by
    calc
      Nat.card (NT ⧸ (⊥ : Subgroup NT)) = Nat.card NT :=
        Nat.card_congr (QuotientGroup.quotientBot (G := ↑NT)).toEquiv
      _ < Nat.card G := hNT_card
  have hCp_NT_quot : SatisfiesCp (p := p) K (NT ⧸ (⊥ : Subgroup NT)) :=
    hB NT (⊥ : Subgroup NT) hNT_quot_card
  have hCp_NT : SatisfiesCp (p := p) K ↑NT :=
    (satisfiesCp_congr K (QuotientGroup.quotientBot (G := ↑NT))).mp hCp_NT_quot
  let S_NT : Sylow p ↑NT := S.subtype hS_le_NT
  let W_NT : Set ↑NT := {x | (x : G) ∈ W}
  have hW_NT_ne : W_NT.Nonempty := by
    rcases hWne with ⟨w, hw⟩
    exact ⟨⟨w, hS_le_NT (hWle hw)⟩, hw⟩
  have hW_NT_le : W_NT ⊆ (S_NT : Subgroup ↑NT) := by
    intro x hx
    exact hWle hx
  let n_NT : ↑NT := ⟨n, hnT⟩
  have hW_NT_n : conjSubset n_NT W_NT ⊆ (S_NT : Subgroup ↑NT) := by
    rintro _ ⟨w, hw, rfl⟩
    change n⁻¹ * (w : G) * n ∈ (S : Subgroup G)
    exact hWn ⟨(w : G), hw, rfl⟩
  rcases (hCp_NT S_NT) W_NT hW_NT_ne hW_NT_le n_NT hW_NT_n with
    ⟨d_NT, m_NT, hd_NT, hm_NT, hn_eq_NT⟩
  let d : G := d_NT
  let m : G := m_NT
  have hn_eq : n = d * m := by
    have := congrArg (fun x : ↑NT => (x : G)) hn_eq_NT
    simpa [n_NT, d, m] using this
  have hS_NT_map : (S_NT : Subgroup ↑NT).map NT.subtype = (S : Subgroup G) := by
    simpa [S_NT] using Subgroup.map_subgroupOf_eq_of_le hS_le_NT
  have hK_NT_map : (K.K (S_NT : Subgroup ↑NT)).map NT.subtype =
      K.K (S : Subgroup G) := by
    calc
      (K.K (S_NT : Subgroup ↑NT)).map NT.subtype =
          K.K ((S_NT : Subgroup ↑NT).map NT.subtype) := by
            exact (K.K_map NT.subtype (S_NT : Subgroup ↑NT)
              (NT.subtype_injective.comp (S_NT : Subgroup ↑NT).subtype_injective)).symm
      _ = K.K (S : Subgroup G) := by rw [hS_NT_map]
  have hmN : m ∈ N := by
    have hm := (mem_normalizer_map_subtype_iff
      (M := NT) (H := K.K (S_NT : Subgroup ↑NT)) (x := m_NT)).mp hm_NT
    rw [hK_NT_map] at hm
    exact hm
  have hqd_cent : q d ∈ Subgroup.centralizer Wbar := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    have hwNT : ⟨w, hS_le_NT (hWle hw)⟩ ∈ W_NT := hw
    have hcomm := (Subgroup.mem_centralizer_iff.mp hd_NT)
      ⟨w, hS_le_NT (hWle hw)⟩ hwNT
    simpa [d, q, map_mul] using congrArg q (congrArg Subtype.val hcomm)
  let c : G := g * m⁻¹
  have hqc : q c = cbar * q d := by
    dsimp [c]
    rw [map_mul, map_inv, hqg, ← hnq, hn_eq, map_mul]
    group
  have hc : q c ∈ Subgroup.centralizer Wbar := by
    rw [hqc]
    exact (Subgroup.centralizer Wbar).mul_mem hcbar hqd_cent
  refine ⟨c, m, ?_, hmN, ?_⟩
  · simpa [P, q, Wbar] using hc
  · dsimp [c]
    group

/-- **Registered bridge.**  The paper's (5.9) + the step-(IV) method of Theorem 5.1
(L1528–L1543): in the case `C(P)S = G`, for `W ⊄ P`, the general case is reduced
to the special case `C_S(W̄) ∈ Syl_p(C_G(W̄))` by the conjugation method of step
(IV); the special case uses that `C_G(W̄)/C_G(WP)` is a `p`-group (the input
`hPGroup`, proved from `p'_element_mem_centralizer_of_CG_eq_top`,
`pAut_eq_one_of_orderOf_p'`, `p'_element_centralizes_WP` of this file) to obtain
`g ∈ C_G(WP)·C_S(W̄)·N ⊆ C_G(W)·N`.

*Why:* special case: the image of `C_S(W̄)` in the `p`-group
`C_G(W̄)/C_G(WP)` is a Sylow `p`-subgroup, hence the whole quotient, so
`C_G(W̄) = C_G(WP)·C_S(W̄)`; with (5.8) this gives `g ∈ C_G(W)·N`.  General case:
exactly the method of the landed step (IV) of `Glauberman.Theorem5_1`.

*Elimination condition:* replace the `sorry` by the wiring of the proved
`p'`-element step of this file (`p'_element_mem_centralizer_of_CG_eq_top`,
`pAut_eq_one_of_orderOf_p'`, `p'_element_centralizes_WP`: every `p'`-element of
`C_G(W̄)` lies in `C_G(WP)` since `G/C(P)` is a `p`-group), the quotient-image
Sylow argument (the image of `C_S(W̄)` in the `p`-group `C_G(W̄)/C_G(WP)` is a
Sylow `p`-subgroup, hence the whole quotient), and the Sylow-conjugation
reduction of step (IV) in the quotient `G ⧸ P`. -/
public theorem theorem5_2_step_IV {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (K : CharacteristicFunctor p) (S : Sylow p G)
    (hA : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Subgroup.centralizer ((pCore p (H ⧸ N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) ≤
        (pCore p (H ⧸ N) : Subgroup (H ⧸ N)) →
      ∀ S₀ : Sylow p (H ⧸ N), (K.K (S₀ : Subgroup (H ⧸ N))).Normal)
    (hB : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Nat.card (H ⧸ N) < Nat.card G → SatisfiesCp (p := p) K (H ⧸ N))
    (hP : pCore p G ≠ ⊥)
    (hI : let P : Subgroup G := pCore p G
      let C : Subgroup G := Subgroup.centralizer (P : Set G)
      let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
      C ⊔ N = ⊤) :
    let P : Subgroup G := pCore p G
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
    C ⊔ (S : Subgroup G) = ⊤ →
      ∀ W : Set G, W.Nonempty → W ⊆ (S : Subgroup G) → ¬ W ⊆ (P : Set G) →
        ∀ g : G, conjSubset g W ⊆ (S : Subgroup G) →
          ∃ c n : G,
            c ∈ Subgroup.centralizer (W : Set G) ∧ n ∈ N ∧ g = c * n := by
  classical
  dsimp only
  intro hCS W hWne hWle hWnotP g hWg
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
  have : P.Normal := by
    dsimp [P]
    infer_instance
  let q : G →* G ⧸ P := QuotientGroup.mk' P
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective P
  have hP_le_S : P ≤ (S : Subgroup G) := by
    simpa [P] using pCore_le_sylow (G := G) S
  let Sbar : Sylow p (G ⧸ P) := S.mapSurjective (f := q) hq_surj
  have hcomap_Sbar : (Sbar : Subgroup (G ⧸ P)).comap q = (S : Subgroup G) := by
    simpa [Sbar, q, QuotientGroup.ker_mk'] using
      (Subgroup.comap_map_eq_self (f := q) (H := (S : Subgroup G))
        (by simpa [q, QuotientGroup.ker_mk'] using hP_le_S))
  have hS_le_N : (S : Subgroup G) ≤ N := by
    simpa [N] using sylow_le_normalizer_K K S
  have hCGp : IsPGroup p (G ⧸ C) := by
    have hCnormal : C.Normal := by
      dsimp [C]
      infer_instance
    let qC : G →* G ⧸ C := QuotientGroup.mk' C
    let f : ↥(S : Subgroup G) →* G ⧸ C := qC.comp (S : Subgroup G).subtype
    have hf : Function.Surjective f := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C z
      have hx : x ∈ C ⊔ (S : Subgroup G) := by
        rw [hCS]
        trivial
      rcases mem_sup_mul_of_normal hCnormal hx with ⟨c, hc, s, hs, hxs⟩
      refine ⟨⟨s, hs⟩, ?_⟩
      change qC s = qC x
      have hqc : qC c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
      rw [hxs, map_mul, hqc, one_mul]
    exact S.isPGroup'.of_surjective f hf
  let H : Subgroup G := Subgroup.closure W
  have hH_le_S : H ≤ (S : Subgroup G) :=
    (Subgroup.closure_le (K := (S : Subgroup G))).mpr hWle
  have hHp : IsPGroup p H := IsPGroup.to_le S.isPGroup' hH_le_S
  have hHg_le_S : conjSubgroup g H ≤ (S : Subgroup G) := by
    rw [conjSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := (S : Subgroup G))).mpr ?_
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hWg ⟨w, hw, by simp⟩
  let Hbar : Subgroup (G ⧸ P) := H.map q
  have hHbar_le_Sbar : Hbar ≤ (Sbar : Subgroup (G ⧸ P)) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨h, hh, rfl⟩
    exact Subgroup.mem_map_of_mem q (hH_le_S hh)
  have hHbarp : IsPGroup p Hbar := IsPGroup.map (H := H) hHp q
  have hHbar_ne : Hbar ≠ ⊥ := by
    obtain ⟨w, hwW, hwP⟩ := Set.not_subset.mp hWnotP
    intro hbot
    have hqw : q w ∈ Hbar :=
      Subgroup.mem_map_of_mem q (Subgroup.subset_closure hwW)
    rw [hbot] at hqw
    have hqw1 : q w = 1 := by simpa using hqw
    exact hwP ((QuotientGroup.eq_one_iff w).mp hqw1)
  obtain ⟨xbar, Vbar, hVbar_def, hVbar_le_Sbar, hVbarp, hVbar_x,
      hVbar_cond⟩ :=
    exists_conjugate_with_sylow_centralizer Sbar Hbar hHbarp hHbar_le_Sbar
  obtain ⟨x, hx⟩ := hq_surj xbar
  let V : Subgroup G := conjSubgroup x⁻¹ H
  have hVmap : V.map q = Vbar := by
    calc
      V.map q = (H.map (MulAut.conj x).toMonoidHom).map q := by
        simp [V, conjSubgroup]
      _ = H.map (q.comp (MulAut.conj x).toMonoidHom) := by
        rw [Subgroup.map_map]
      _ = H.map ((MulAut.conj xbar).toMonoidHom.comp q) := by
        congr 1
        ext z
        simp [MulAut.conj_apply, hx]
      _ = (H.map q).map (MulAut.conj xbar).toMonoidHom := by
        rw [Subgroup.map_map]
      _ = conjSubgroup xbar⁻¹ Hbar := by
        simp [conjSubgroup, Hbar]
      _ = Vbar := hVbar_def.symm
  have hV_le_S : V ≤ (S : Subgroup G) := by
    intro v hv
    have hqv : q v ∈ Vbar := by
      rw [← hVmap]
      exact Subgroup.mem_map_of_mem q hv
    have hqvS : q v ∈ (Sbar : Subgroup (G ⧸ P)) := hVbar_le_Sbar hqv
    have hvpre : v ∈ (Sbar : Subgroup (G ⧸ P)).comap q := hqvS
    rw [hcomap_Sbar] at hvpre
    exact hvpre
  have hVp : IsPGroup p V := by
    have hVeq : V = H.map (MulAut.conj x).toMonoidHom := by
      simp [V, conjSubgroup]
    rw [hVeq]
    exact IsPGroup.map (H := H) hHp (MulAut.conj x).toMonoidHom
  have hVbar_ne : Vbar ≠ ⊥ := by
    intro hbot
    apply hHbar_ne
    rw [← hVbar_x, hbot]
    simp [conjSubgroup]
  have hVnotP : ¬ V ≤ P := by
    intro hVP
    apply hVbar_ne
    rw [← hVmap]
    apply le_antisymm
    · intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨v, hv, rfl⟩
      have hqv1 : q v = 1 := (QuotientGroup.eq_one_iff v).mpr (hVP hv)
      simp [hqv1]
    · exact bot_le
  have hVx : conjSubgroup x V = H := by
    change conjSubgroup x (conjSubgroup x⁻¹ H) = H
    rw [conjSubgroup_comp, inv_mul_cancel]
    ext z
    simp [conjSubgroup]
  have hVxg : conjSubgroup (x * g) V = conjSubgroup g H := by
    change conjSubgroup (x * g) (conjSubgroup x⁻¹ H) = conjSubgroup g H
    rw [conjSubgroup_comp]
    apply congrArg (fun f : G ≃* G => H.map f.toMonoidHom)
    ext z
    group
  have hSpecial :
      ∀ U : Subgroup G, U ≤ (S : Subgroup G) → ¬ U ≤ P →
        (∃ Q : Sylow p ↥(Subgroup.centralizer
            ((U.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P))),
          (Q : Subgroup ↥(Subgroup.centralizer
              ((U.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P)))).map
                (Subgroup.centralizer
                  ((U.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P))).subtype =
            Subgroup.centralizer
                ((U.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P)) ⊓
              (Sbar : Subgroup (G ⧸ P))) →
        ∀ y : G, conjSubgroup y U ≤ (S : Subgroup G) →
          ∃ c n : G,
            c ∈ Subgroup.centralizer (U : Set G) ∧ n ∈ N ∧ y = c * n := by
    intro U hU_le_S hUnotP hUcond y hUy_le_S
    let Ubar : Subgroup (G ⧸ P) := U.map q
    let Cbar : Subgroup (G ⧸ P) := Subgroup.centralizer (Ubar : Set (G ⧸ P))
    let C0 : Subgroup G := Cbar.comap q
    let T : Subgroup G := P ⊔ U
    let D : Subgroup G := Subgroup.centralizer (T : Set G)
    have hT_le_S : T ≤ (S : Subgroup G) := sup_le hP_le_S hU_le_S
    have hTp : IsPGroup p T := IsPGroup.to_le S.isPGroup' hT_le_S
    have hPmap : P.map q = (⊥ : Subgroup (G ⧸ P)) := by
      apply le_antisymm
      · intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨a, ha, rfl⟩
        have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
        simp [hqa]
      · exact bot_le
    have hTmap : T.map q = Ubar := by
      simp [T, Ubar, Subgroup.map_sup, hPmap]
    have hconj_mem_T : ∀ (c : G), c ∈ C0 → ∀ {t : G}, t ∈ T → c * t * c⁻¹ ∈ T := by
      intro c hc t ht
      have hcbar : q c ∈ Cbar := hc
      rcases mem_sup_mul_of_normal (C := P) (S := U)
          (inferInstance : P.Normal) ht with ⟨a, haP, b, hbU, rfl⟩
      have hcaP : c * a * c⁻¹ ∈ P :=
        (inferInstance : P.Normal).conj_mem a haP c
      have hqb : q b ∈ Ubar := Subgroup.mem_map_of_mem q hbU
      have hcomm : q b * q c = q c * q b :=
        (Subgroup.mem_centralizer_iff.mp hcbar) (q b) hqb
      have hqeq : q (c * b * c⁻¹) = q b := by
        calc
          q (c * b * c⁻¹) = q c * q b * (q c)⁻¹ := by simp
          _ = q b := by rw [← hcomm]; group
      have hdiffP : (c * b * c⁻¹) / b ∈ P :=
        QuotientGroup.eq_iff_div_mem.mp hqeq
      have hcbT : c * b * c⁻¹ ∈ T := by
        rw [show c * b * c⁻¹ = ((c * b * c⁻¹) / b) * b by
          exact (div_mul_cancel _ _).symm]
        exact T.mul_mem (Subgroup.mem_sup_left hdiffP) (Subgroup.mem_sup_right hbU)
      have hprod : (c * a * c⁻¹) * (c * b * c⁻¹) ∈ T :=
        T.mul_mem (Subgroup.mem_sup_left hcaP) hcbT
      convert hprod using 1 <;> group
    have hC0_le_normalizer_T : C0 ≤ Subgroup.normalizer (T : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · exact hconj_mem_T c hc
      · intro hct
        have hcinv : c⁻¹ ∈ C0 := C0.inv_mem hc
        have := hconj_mem_T c⁻¹ hcinv hct
        simpa [mul_assoc] using this
    have hD_le_C0 : D ≤ C0 := by
      intro d hd
      change q d ∈ Cbar
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨u, hu, rfl⟩
      have hcomm := (Subgroup.mem_centralizer_iff.mp hd) u
        (Subgroup.mem_sup_right hu)
      simpa using congrArg q hcomm
    let D0 : Subgroup C0 := D.subgroupOf C0
    have : D0.Normal := by
      rw [Subgroup.normal_subgroupOf_iff hD_le_C0]
      intro d c hd hc
      rw [Subgroup.mem_centralizer_iff] at hd ⊢
      intro t ht
      have ht' : c⁻¹ * t * c ∈ T :=
        (Subgroup.mem_normalizer_iff''.mp (hC0_le_normalizer_T hc) t).mp ht
      have hcomm : (c⁻¹ * t * c) * d = d * (c⁻¹ * t * c) := hd _ ht'
      calc
        t * (c * d * c⁻¹) = c * ((c⁻¹ * t * c) * d) * c⁻¹ := by group
        _ = c * (d * (c⁻¹ * t * c)) * c⁻¹ := by rw [hcomm]
        _ = (c * d * c⁻¹) * t := by group
    have hP_le_C0 : P ≤ C0 := by
      intro a ha
      change q a ∈ Cbar
      have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [hqa]
      exact Cbar.one_mem
    have hpprime_mem_D : ∀ z : G, z ∈ C0 → ¬ p ∣ orderOf z → z ∈ D := by
      intro z hzC0 hzorder
      have hzCP : z ∈ Subgroup.centralizer (P : Set G) :=
        p'_element_mem_centralizer_of_CG_eq_top P z (by simpa [C] using hCGp) hzorder
      have hzN : z ∈ Subgroup.normalizer (T : Set G) := hC0_le_normalizer_T hzC0
      have hxP : ∀ u : ↥T, u ∈ P.subgroupOf T → conjAut T z hzN u = u := by
        intro u hu
        apply Subtype.ext
        change z⁻¹ * (u : G) * z = (u : G)
        have hcomm : (u : G) * z = z * (u : G) :=
          (Subgroup.mem_centralizer_iff.mp hzCP) (u : G)
            (Subgroup.mem_subgroupOf.mp hu)
        calc
          z⁻¹ * (u : G) * z = z⁻¹ * ((u : G) * z) := by group
          _ = z⁻¹ * (z * (u : G)) := by rw [hcomm]
          _ = (u : G) := by group
      have hxq : ∀ u : ↥T,
          QuotientGroup.mk' (P.subgroupOf T) (conjAut T z hzN u) =
            QuotientGroup.mk' (P.subgroupOf T) u := by
        intro u
        have hzbar : q z ∈ Cbar := hzC0
        have huq : q (u : G) ∈ Ubar := by
          rw [← hTmap]
          exact Subgroup.mem_map_of_mem q u.2
        have hcomm : q (u : G) * q z = q z * q (u : G) :=
          (Subgroup.mem_centralizer_iff.mp hzbar) _ huq
        have hqeq : q (z⁻¹ * (u : G) * z) = q (u : G) := by
          calc
            q (z⁻¹ * (u : G) * z) = (q z)⁻¹ * q (u : G) * q z := by simp
            _ = (q z)⁻¹ * (q (u : G) * q z) := by group
            _ = (q z)⁻¹ * (q z * q (u : G)) := by rw [hcomm]
            _ = q (u : G) := by group
        apply QuotientGroup.eq_iff_div_mem.mpr
        apply Subgroup.mem_subgroupOf.mpr
        change (z⁻¹ * (u : G) * z) / (u : G) ∈ P
        exact QuotientGroup.eq_iff_div_mem.mp hqeq
      have hfix := p'_element_centralizes_WP T hTp (P.subgroupOf T) z hzN hxP hxq hzorder
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have heq := congrArg Subtype.val (hfix ⟨t, ht⟩)
      change z⁻¹ * t * z = t at heq
      calc
        t * z = z * (z⁻¹ * t * z) := by group
        _ = z * t := by rw [heq]
    have hD0prime : ∀ z : C0, ¬ p ∣ orderOf z → z ∈ D0 := by
      intro z hz
      have hzG : ¬ p ∣ orderOf (z : G) := by
        intro hdiv
        apply hz
        simpa using hdiv
      exact Subgroup.mem_subgroupOf.mpr (hpprime_mem_D z z.2 hzG)
    have hC0D0p : IsPGroup p (C0 ⧸ D0) :=
      isPGroup_quotient_of_pPrime_order_elements_mem D0 hD0prime
    have hUcond' :
        ∃ Q : Sylow p Cbar,
          (Q : Subgroup Cbar).map Cbar.subtype =
            Cbar ⊓ (Sbar : Subgroup (G ⧸ P)) := by
      simpa [Cbar, Ubar] using hUcond
    rcases hUcond' with ⟨Qbar, hQbar⟩
    let q0 : C0 →* Cbar :=
      { toFun := fun z => ⟨q (z : G), z.2⟩
        map_one' := by
          apply Subtype.ext
          exact map_one q
        map_mul' := by
          intro a b
          apply Subtype.ext
          exact map_mul q (a : G) (b : G) }
    have hq0_surj : Function.Surjective q0 := by
      intro z
      obtain ⟨a, ha⟩ := hq_surj (z : G ⧸ P)
      have haC0 : a ∈ C0 := by
        change q a ∈ Cbar
        rw [ha]
        exact z.2
      refine ⟨⟨a, haC0⟩, ?_⟩
      apply Subtype.ext
      exact ha
    have hq0ker : q0.ker = P.subgroupOf C0 := by
      ext z
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hz
        apply (QuotientGroup.eq_one_iff (z : G)).mp
        exact congrArg Subtype.val hz
      · intro hz
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (z : G)).mpr hz
    have hq0kerp : IsPGroup p q0.ker := by
      rw [hq0ker]
      exact (pCore_isPGroup (G := G) (p := p)).of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := P) (K := C0) hP_le_C0).symm
    have hQbar_range : (Qbar : Subgroup Cbar) ≤ q0.range := by
      intro z hz
      obtain ⟨a, ha⟩ := hq0_surj z
      exact ⟨a, ha⟩
    let Q0 : Sylow p C0 := Qbar.comapOfKerIsPGroup q0 hq0kerp hQbar_range
    have hQ0map : (Q0 : Subgroup C0).map C0.subtype = C0 ⊓ (S : Subgroup G) := by
      ext z
      constructor
      · rintro ⟨a, haQ0, rfl⟩
        refine ⟨a.2, ?_⟩
        have haQbar : q0 a ∈ Qbar := by simpa [Q0] using haQ0
        have hqamap : q (a : G) ∈ (Qbar : Subgroup Cbar).map Cbar.subtype := by
          exact Subgroup.mem_map.mpr ⟨q0 a, haQbar, rfl⟩
        rw [hQbar] at hqamap
        have haSpre : (a : G) ∈ (Sbar : Subgroup (G ⧸ P)).comap q := hqamap.2
        rw [hcomap_Sbar] at haSpre
        exact haSpre
      · intro hz
        let z0 : C0 := ⟨z, hz.1⟩
        refine Subgroup.mem_map.mpr ⟨z0, ?_, rfl⟩
        have hqzS : q z ∈ (Sbar : Subgroup (G ⧸ P)) := by
          simpa [Sbar] using Subgroup.mem_map_of_mem q hz.2
        have hqzinf : q z ∈ Cbar ⊓ (Sbar : Subgroup (G ⧸ P)) := ⟨hz.1, hqzS⟩
        rw [← hQbar] at hqzinf
        rcases Subgroup.mem_map.mp hqzinf with ⟨a, haQbar, ha⟩
        have haz0 : a = q0 z0 := by
          apply Subtype.ext
          change (a : G ⧸ P) = q z
          exact ha
        have hz0Qbar : q0 z0 ∈ Qbar := haz0 ▸ haQbar
        change q0 z0 ∈ Qbar
        exact hz0Qbar
    let qD : C0 →* C0 ⧸ D0 := QuotientGroup.mk' D0
    let Qquot : Sylow p (C0 ⧸ D0) :=
      Q0.mapSurjective (f := qD) (QuotientGroup.mk'_surjective D0)
    have hQquot_top : (Qquot : Subgroup (C0 ⧸ D0)) = ⊤ := by
      symm
      exact Qquot.is_maximal' (hC0D0p.to_subgroup ⊤) le_top
    have hQ0map_qD : (Q0 : Subgroup C0).map qD = ⊤ := by
      simpa [Qquot] using hQquot_top
    have hqDker : qD.ker = D0 := by
      simp [qD]
    have hD0_sup_Q0 : D0 ⊔ (Q0 : Subgroup C0) = ⊤ := by
      have hcomap := Subgroup.comap_map_eq qD (Q0 : Subgroup C0)
      have hQ0_sup_D0 : (Q0 : Subgroup C0) ⊔ D0 = ⊤ := by
        calc
          (Q0 : Subgroup C0) ⊔ D0 = (Q0 : Subgroup C0) ⊔ qD.ker := by rw [hqDker]
          _ = Subgroup.comap qD ((Q0 : Subgroup C0).map qD) := hcomap.symm
          _ = ⊤ := by rw [hQ0map_qD]; simp
      rw [sup_comm]
      exact hQ0_sup_D0
    have hyset : conjSubset y (U : Set G) ⊆ (S : Subgroup G) := by
      rw [conjSubset_eq_conjSubgroup]
      intro z hz
      exact hUy_le_S hz
    rcases theorem5_2_step_III K S hA hB hP hI hCS (U : Set G)
        ⟨1, U.one_mem⟩ hU_le_S hUnotP y hyset with
      ⟨c0, n, hc0bar, hnN, hycn⟩
    have hc0C0 : c0 ∈ C0 := by
      change q c0 ∈ Cbar
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨u, hu, rfl⟩
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc0bar)
        (QuotientGroup.mk' (pCore p G) u) ⟨u, hu, rfl⟩
      simpa [q, P] using hcomm
    let c0' : C0 := ⟨c0, hc0C0⟩
    have hc0top : c0' ∈ D0 ⊔ (Q0 : Subgroup C0) := by
      rw [hD0_sup_Q0]
      trivial
    rcases mem_sup_mul_of_normal (G := C0) (C := D0)
        (S := (Q0 : Subgroup C0)) (inferInstance : D0.Normal) hc0top with
      ⟨d, hdD0, s, hsQ0, hds⟩
    have hdsG : c0 = (d : G) * (s : G) := by
      have := congrArg (fun z : C0 => (z : G)) hds
      simpa [c0'] using this
    refine ⟨(d : G), (s : G) * n, ?_, ?_, ?_⟩
    · have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hdD0
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hdD) u (Subgroup.mem_sup_right hu)
    · have hsmap : (s : G) ∈ (Q0 : Subgroup C0).map C0.subtype :=
        Subgroup.mem_map_of_mem C0.subtype hsQ0
      rw [hQ0map] at hsmap
      exact N.mul_mem (hS_le_N hsmap.2) hnN
    · calc
        y = c0 * n := hycn
        _ = ((d : G) * (s : G)) * n := by rw [hdsG]
        _ = (d : G) * ((s : G) * n) := by group
  have hVcond :
      ∃ Q : Sylow p ↥(Subgroup.centralizer
          ((V.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P))),
        (Q : Subgroup ↥(Subgroup.centralizer
            ((V.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P)))).map
              (Subgroup.centralizer
                ((V.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P))).subtype =
          Subgroup.centralizer
              ((V.map q : Subgroup (G ⧸ P)) : Set (G ⧸ P)) ⊓
            (Sbar : Subgroup (G ⧸ P)) := by
    rw [hVmap]
    exact hVbar_cond
  have hx1 : conjSubgroup x V ≤ (S : Subgroup G) := by
    rw [hVx]
    exact hH_le_S
  rcases hSpecial V hV_le_S hVnotP hVcond x hx1 with
    ⟨c0, m0, hc0, hm0, hx⟩
  let c : G := c0⁻¹
  let m : G := m0
  have hx' : c⁻¹ * m = x := by
    simp [c, m, hx]
  have hc_mem : c ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.centralizer (V : Set G)).inv_mem hc0
  have hm_mem : m ∈ N := hm0
  have hx2 : conjSubgroup (x * g) V ≤ (S : Subgroup G) := by
    rw [hVxg]
    exact hHg_le_S
  rcases hSpecial V hV_le_S hVnotP hVcond (x * g) hx2 with
    ⟨d, n, hd, hn, hxg⟩
  refine ⟨m⁻¹ * c * d * m, m⁻¹ * n, ?_, ?_, ?_⟩
  · have hH_eq : H = conjSubgroup m V := by
      have hm_eq : m = c * x := by
        calc
          m = c * (c⁻¹ * m) := by group
          _ = c * x := by rw [hx']
      rw [hm_eq, ← conjSubgroup_comp]
      have hcV : conjSubgroup c V = V := by
        apply le_antisymm
        · intro v hv
          rcases Subgroup.mem_map.mp hv with ⟨u, hu, rfl⟩
          have hcomm : c * u = u * c :=
            (Subgroup.mem_centralizer_iff.mp hc_mem u hu).symm
          have h' : c⁻¹ * u * c = u := by
            calc
              c⁻¹ * u * c = c⁻¹ * (u * c) := by rw [mul_assoc]
              _ = c⁻¹ * (c * u) := by rw [← hcomm]
              _ = u := by group
          simpa [h'] using hu
        · intro u hu
          have hcomm : c * u = u * c :=
            (Subgroup.mem_centralizer_iff.mp hc_mem u hu).symm
          refine Subgroup.mem_map.mpr ⟨c * u * c⁻¹, ?_, ?_⟩
          · simpa [hcomm, mul_assoc] using hu
          · change (MulAut.conj c⁻¹) (c * u * c⁻¹) = u
            rw [MulAut.conj_apply]
            group
      rw [hcV]
      exact hVx.symm
    have hcm_mem : m⁻¹ * c * m ∈ Subgroup.centralizer (H : Set G) := by
      rw [hH_eq, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      change (MulAut.conj m⁻¹) v * (m⁻¹ * c * m) =
        (m⁻¹ * c * m) * (MulAut.conj m⁻¹) v
      rw [MulAut.conj_apply, inv_inv]
      calc
        (m⁻¹ * v * m) * (m⁻¹ * c * m) = m⁻¹ * (v * c) * m := by group
        _ = m⁻¹ * (c * v) * m := by
          rw [(Subgroup.mem_centralizer_iff.mp hc_mem v hv).symm]
        _ = (m⁻¹ * c * m) * (m⁻¹ * v * m) := by group
    have hdm_mem : m⁻¹ * d * m ∈ Subgroup.centralizer (H : Set G) := by
      rw [hH_eq, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
      change (MulAut.conj m⁻¹) v * (m⁻¹ * d * m) =
        (m⁻¹ * d * m) * (MulAut.conj m⁻¹) v
      rw [MulAut.conj_apply, inv_inv]
      calc
        (m⁻¹ * v * m) * (m⁻¹ * d * m) = m⁻¹ * (v * d) * m := by group
        _ = m⁻¹ * (d * v) * m := by
          rw [(Subgroup.mem_centralizer_iff.mp hd v hv).symm]
        _ = (m⁻¹ * d * m) * (m⁻¹ * v * m) := by group
    have hprod : m⁻¹ * c * d * m ∈ Subgroup.centralizer (H : Set G) := by
      convert (Subgroup.centralizer (H : Set G)).mul_mem hcm_mem hdm_mem using 1
      group
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp hprod) w (Subgroup.subset_closure hw)
  · exact N.mul_mem (N.inv_mem hm_mem) hn
  · calc
      g = x⁻¹ * (x * g) := by group
      _ = x⁻¹ * (d * n) := by rw [hxg]
      _ = (c⁻¹ * m)⁻¹ * (d * n) := by rw [hx']
      _ = m⁻¹ * c * d * n := by group
      _ = (m⁻¹ * c * d * m) * (m⁻¹ * n) := by group

/-- Glauberman's Theorem 5.2 (`refs/glauberman-p-stable.tex` L1477–L1592; original
[6, §5, p. 1121]): the engine of Theorem B.  Let `p` be a prime, `G` a finite
group, and `K` a characteristic functor.  Assume that every subquotient `H ⧸ N`
of `G` (`H ≤ G`, `N ⊴ H`) has properties

  (a) if `C(O_p(H ⧸ N)) ⊆ O_p(H ⧸ N)`, then `K(Q_p) ⊴ H ⧸ N` for every Sylow
      `p`-subgroup `Q_p` of `H ⧸ N`;
  (b) if `|H ⧸ N| < |G|`, then `H ⧸ N` satisfies `(C_p)`.

Then, if `O_p(G) ≠ 1`, `G` satisfies `(C_p)`.  The proof follows the paper:
step I (the Frattini/Lemma-5.2 reduction `G = C_G(P)·N_G(K(S))`), the case
`C(P)S < G` (step II), the case `C(P)S = G` (steps III and IV, with the
`p'`-element step proved in this file).  Steps I–IV are registered bridges with
exact statements and elimination conditions; the `(C_p)`-conclusion is assembled
here in full, including the `W ⊆ P` case (`c₀ ∈ C(P) ⊆ C(W)`, `n₀ ∈ S ⊆ N` via
`K_conj`) and the subquotient hypotheses transport. -/
public theorem theorem5_2 {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (K : CharacteristicFunctor p)
    (hA : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Subgroup.centralizer ((pCore p (H ⧸ N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) ≤
        (pCore p (H ⧸ N) : Subgroup (H ⧸ N)) →
      ∀ S₀ : Sylow p (H ⧸ N), (K.K (S₀ : Subgroup (H ⧸ N))).Normal)
    (hB : ∀ (H : Subgroup G) (N : Subgroup H) [N.Normal],
      Nat.card (H ⧸ N) < Nat.card G → SatisfiesCp (p := p) K (H ⧸ N))
    (hP : pCore p G ≠ ⊥) : SatisfiesCp (p := p) K G := by
  classical
  intro S W hWne hWle g hWg
  let P : Subgroup G := pCore p G
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (K.K (S : Subgroup G) : Set G)
  have hI : C ⊔ N = ⊤ :=
    theorem5_2_step_I K S hA hP
  by_cases hCS : C ⊔ (S : Subgroup G) = ⊤
  · by_cases hWleP : W ⊆ (P : Set G)
    · -- `W ⊆ P`: `g = c₀n₀` with `c₀ ∈ C(P) ⊆ C(W)`, `n₀ ∈ S ⊆ N = N_G(K(S))`
      have hgC : g ∈ C ⊔ (S : Subgroup G) := by
        rw [hCS]
        trivial
      have hCnorm : C.Normal := by
        dsimp [C]
        infer_instance
      rcases (mem_sup_mul_of_normal hCnorm hgC) with ⟨c₀, hc₀C, n₀, hn₀S, hgcn⟩
      refine ⟨c₀, n₀, ?_, ?_, hgcn⟩
      · -- c₀ ∈ C(P) ⊆ C(W) as W ⊆ P
        intro x hxW
        have hxP : x ∈ (P : Set G) := hWleP hxW
        exact (Subgroup.mem_centralizer_iff.mp hc₀C x hxP)
      · -- n₀ ∈ S ⊆ N_G(K(S)): K(S)^s = K(S) for s ∈ S (K_conj)
        rw [Subgroup.mem_normalizer_iff_conj_image_eq]
        have hSmap : (S : Subgroup G).map (MulAut.conj (n₀ : G)).toMonoidHom = (S : Subgroup G) := by
          ext x
          constructor
          · rintro ⟨s, hs, rfl⟩
            simpa [MulAut.conj_apply] using (S.mul_mem (S.mul_mem hn₀S hs) (S.inv_mem hn₀S))
          · intro hx
            refine Subgroup.mem_map.mpr ⟨(n₀ : G)⁻¹ * x * (n₀ : G),
              S.mul_mem (S.mul_mem (S.inv_mem hn₀S) hx) hn₀S, ?_⟩
            simp [MulAut.conj_apply]
            group
        have hKc : (K.K (S : Subgroup G)).map (MulAut.conj (n₀ : G)).toMonoidHom =
            K.K (S : Subgroup G) := by
          rw [← K.K_conj (H := G) (P := (S : Subgroup G)) (g := (n₀ : G))]
          rw [hSmap]
        simpa using congrArg (fun X : Subgroup G => (X : Set G)) hKc
    · -- `W ⊄ P`: step IV (paper (5.9) + the step-(IV) reduction of Theorem 5.1)
      have hnot : ¬ W ⊆ (P : Set G) := hWleP
      exact theorem5_2_step_IV K S hA hB hP hI hCS W hWne hWle hnot g hWg
  · exact theorem5_2_step_II K S hA hB hP hI hCS W hWne hWle g hWg

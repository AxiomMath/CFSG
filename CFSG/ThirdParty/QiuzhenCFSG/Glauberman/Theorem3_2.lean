module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem3_1
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.pStability
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman, "A Characteristic Subgroup of a p-Stable Group" — §3, Theorem 3.2 and companions

Statements and proofs of Lemma 3.5, Theorem 3.2, Lemma 3.7, and Corollaries 3.4/3.5 of
George Glauberman, *A Characteristic Subgroup of a p-Stable Group*, Canadian Journal of
Mathematics 20 (1968), 1101–1135 — reference [6] of the dihedral-Sylow project — following
the validated transcription in `refs/glauberman-p-stable.tex`:

* Lemma 3.5 (tex L571–L593): for `S ∈ Syl_p G`, (a) `A ∈ A(S)`, `A ≤ P ≤ S` ⟹
  `Z(J(S)) ≤ A` and `Z(J(S)) ≤ Z(J(P))`; (b) `P` a `p`-subgroup of `G` with `J(S) ≤ P`
  ⟹ `J(S) = J(P)`.
* Theorem 3.2 (tex L606–L695): `p` odd, `S ∈ Syl_p G`, `B ⊴ G` an Abelian `p`-subgroup,
  `G` `p`-stable ⟹ `Z(J(S)) ∩ B ⊴ G`.  The proof follows the paper: `L` is the normal core
  of `N_G(C)` (`C = Z(J(S)) ∩ B`); the Frattini argument gives `G = L·N(L∩S) = L·N(X)`
  with `X = Z(J(L∩S))`; `(3.5)` (an `A ∈ A(S)` with `[C₁,A,A] = 1` for a normal `p`-subgroup
  `C₁ ⊇ C` lies in `L`) is derived from the `p`-stability hypothesis via the local plumbing
  `pStableLocal_apply_of_normal_pSubgroup` (the paper's `(3.4)` containment
  `O_p(G/C(C₁)) ⊆ L/C(C₁)`); the normal closure `V = ⟨C^G⟩` satisfies `V ⊆ X` ("(3.8)")
  because every conjugate of `C` by `g = ln` (`l ∈ L`, `n ∈ N(X)`) collapses to a conjugate
  by `n` (`L ≤ N(C)`); the Thompson Replacement Theorem applied to `(V, A)` for `A ∈ A(S)`
  with `A ⊄ L` and `A ∩ V` maximal yields the contradiction `[V,A,A] ≠ 1` vs.
  `[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`.
* Lemma 3.7 (tex L699–L733): `H ≤ Z(J(S))` ⟹ `N(H) = C(H)(N(J(S)) ∩ N(H))`.
* Corollary 3.4 (tex L697–L709): (a) `Z(J(S)) ⊴ G` iff `Z(J(S))` is contained in a normal
  Abelian subgroup of `G`; (b) if `O_p(G)` contains an element of `A(S)`, then `Z(J(S)) ⊴ G`.
* Corollary 3.5 (tex L735–L745): `G` `p`-stable, `C(O_p(G)) ⊆ O_p(G)` ⟹
  `G = C(Z(S))·N(J(S))`.

The infrastructure lemmas of `FeitThompson/Gorenstein/Chapter8_2.lean` and
`Glauberman/Theorem5_1.lean` that are used here (`thompsonSubgroup_le`,
`thompsonCenter_isMulCommutative`, `exists_mem_thompsonAbelianSubgroups`, the
conjugation-invariance of `A(P)`) are `module`-private there; they are reproduced locally
at the top of this file.  The `p`-stability plumbing
`pStableLocal_apply_of_core_normal` of `Glauberman/pStability.lean` is generalized here
to arbitrary normal `p`-subgroups `P` (`pStableLocal_apply_of_normal_pSubgroup`), which is
exactly the paper's use of `p`-stability in `(3.5)`.

No `axiom`/`opaque`/unregistered `sorry` is used.
-/

open scoped Pointwise commutatorElement

namespace CFSG.Glauberman

variable {G : Type*} [Group G]

/-! ## Local infrastructure (module-private copies of Chapter8_2 / Theorem5_1 helpers) -/

/-- `J(P) ≤ P`. -/
private lemma thompsonSubgroup_le (P : Subgroup G) :
    thompsonSubgroup (G := G) P ≤ P := by
  refine sSup_le ?_
  intro A hA
  exact hA.1

/-- `Z(J(P)) ≤ P`. -/
private lemma thompsonCenter_le (P : Subgroup G) :
    thompsonCenter (G := G) P ≤ P := by
  calc
    thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
      exact inf_le_left
    _ ≤ P := thompsonSubgroup_le (G := G) P

/-- `Z(J(P))` is Abelian. -/
private lemma thompsonCenter_isMulCommutative (P : Subgroup G) :
    IsMulCommutative (thompsonCenter (G := G) P) := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := thompsonCenter (G := G) P)).1 ?_
  have hle_left : thompsonCenter (G := G) P ≤ thompsonSubgroup (G := G) P := by
    exact inf_le_left
  have hle_right :
      thompsonCenter (G := G) P ≤
        Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  exact hle_right.trans <|
    Subgroup.centralizer_le
      (show (thompsonCenter (G := G) P : Set G) ⊆ (thompsonSubgroup (G := G) P : Set G) from
        hle_left)

/-- The Abelian subgroups of `S` of maximal order form a non-empty set (finite `S`). -/
private theorem exists_mem_thompsonAbelianSubgroups (S : Subgroup G) [Finite ↥S] :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) S := by
  classical
  let s : Set (Subgroup G) := {A | A ≤ S ∧ IsMulCommutative A}
  have hsfin : s.Finite := by
    have hinj :
        Function.Injective (fun A : ↥s => ((A : Subgroup G).subgroupOf S : Subgroup ↥S)) := by
      intro A B h
      apply Subtype.ext
      have h' := congrArg (fun X : Subgroup ↥S => X.map S.subtype) h
      calc
        A.1 = (A.1.subgroupOf S).map S.subtype := by
          exact (Subgroup.map_subgroupOf_eq_of_le (H := A.1) (K := S) A.2.1).symm
        _ = (B.1.subgroupOf S).map S.subtype := h'
        _ = B.1 := by
          exact Subgroup.map_subgroupOf_eq_of_le (H := B.1) (K := S) B.2.1
    have : Finite ↥s := Finite.of_injective _ hinj
    exact Set.finite_coe_iff.mp inferInstance
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    refine ⟨bot_le, ?_⟩
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := ⊥)).1 bot_le
  obtain ⟨A, hA, hAmax⟩ :=
    Set.exists_max_image s (fun C : Subgroup G => Nat.card C) hsfin hsne
  exact ⟨A, hA.1, hA.2, fun B hB_le hB_comm => hAmax B ⟨hB_le, hB_comm⟩⟩

/-- Conjugation by a normalizer element preserves `A(P)`: if `g ∈ N_G(P)`, then the map
`A ↦ A^g` is a bijection of `A(P)` onto itself.  This is the content of the first half of
the proof of `thompsonCenter_normal_subgroupOf_sylow` in `Chapter8_2.lean`, generalised
from `g ∈ S` to `g ∈ N_G(P)`; it is exactly "J is characteristic in P". -/
private lemma thompsonSubgroup_map_conj_of_normalizer (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P := by
  classical
  let e : G ≃* G := MulAut.conj g
  let e' : G ≃* G := MulAut.conj (g⁻¹ : G)
  have hg' : (P : Subgroup G).map e.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hg'inv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.normalizer (P : Set G)).inv_mem hg
  have hg'inv' : (P : Subgroup G).map e'.toMonoidHom = P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg'inv
  have himage :
      (MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P =
        thompsonAbelianSubgroups (G := G) P := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · change A.map e.toMonoidHom ≤ P
        exact (Subgroup.map_mono hA.1).trans hg'.le
      · let : IsMulCommutative A := hA.2.1
        exact Subgroup.map_isMulCommutative (H := A) e.toMonoidHom
      · intro C hC hCcomm
        have hCpre_le : C.map e'.toMonoidHom ≤ P :=
          (Subgroup.map_mono hC).trans hg'inv'.le
        have hCpre_comm : IsMulCommutative (C.map e'.toMonoidHom) := by
          infer_instance
        have hAmax := hA.2.2 (C.map e'.toMonoidHom) hCpre_le hCpre_comm
        calc
          Nat.card C = Nat.card (C.map e'.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := C) e'.injective
          _ ≤ Nat.card A := hAmax
          _ = Nat.card (A.map e.toMonoidHom) := by
            symm
            exact Subgroup.card_map_of_injective (K := A) e.injective
    · intro hB
      refine ⟨B.map e'.toMonoidHom, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · exact (Subgroup.map_mono hB.1).trans hg'inv'.le
        · let : IsMulCommutative B := hB.2.1
          exact Subgroup.map_isMulCommutative (H := B) e'.toMonoidHom
        · intro C hC hCcomm
          have hCpre_le : C.map e.toMonoidHom ≤ P :=
            (Subgroup.map_mono hC).trans hg'.le
          have hCpre_comm : IsMulCommutative (C.map e.toMonoidHom) := by
            infer_instance
          have hBmax := hB.2.2 (C.map e.toMonoidHom) hCpre_le hCpre_comm
          calc
            Nat.card C = Nat.card (C.map e.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := C) e.injective
            _ ≤ Nat.card B := hBmax
            _ = Nat.card (B.map e'.toMonoidHom) := by
              symm
              exact Subgroup.card_map_of_injective (K := B) e'.injective
      · ext x
        simp [e, e', mul_assoc]
  calc
    (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom
        = (MulEquiv.mapSubgroup e) (sSup (thompsonAbelianSubgroups (G := G) P)) := rfl
    _ = sSup ((MulEquiv.mapSubgroup e) '' thompsonAbelianSubgroups (G := G) P) := by
      simp
    _ = thompsonSubgroup (G := G) P := by
      simpa [thompsonSubgroup] using congrArg sSup himage

/-- If `P` is a subgroup of `G`, then `N_G(P) ≤ N_G(J(P))`: `J(P)` is characteristic in `P`. -/
private lemma normalizer_le_normalizer_of_thompsonSubgroup (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).2 (thompsonSubgroup_map_conj_of_normalizer P hg)

/-- If `P` is a subgroup of `G`, then `N_G(J(P)) ≤ N_G(Z(J(P)))`: `Z(J(P))` is
characteristic in `J(P)`. -/
private lemma normalizer_le_normalizer_of_thompsonCenter (P : Subgroup G) :
    Subgroup.normalizer ((thompsonSubgroup (G := G) P : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thompsonCenter (G := G) P : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hJ : (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom =
      thompsonSubgroup (G := G) P :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hg
  have hcen : (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    rw [map_centralizer_eq_of_equiv (G := G) (G' := G) (e := MulAut.conj g)
      (P := thompsonSubgroup (G := G) P), hJ]
  calc
    (thompsonCenter (G := G) P).map (MulAut.conj g).toMonoidHom
        = ((thompsonSubgroup (G := G) P ⊓
            Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)) : Subgroup G).map
            (MulAut.conj g).toMonoidHom := rfl
    _ = (thompsonSubgroup (G := G) P).map (MulAut.conj g).toMonoidHom ⊓
        (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G)).map
          (MulAut.conj g).toMonoidHom := by
          exact Subgroup.map_inf (thompsonSubgroup (G := G) P)
            (Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    _ = thompsonCenter (G := G) P := by
      rw [hJ, hcen]
      rfl

/-- The centralizer of `H` is contained in the normalizer of `H`. -/
private lemma centralizer_le_normalizer (H : Subgroup G) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (H : Set G) :=
  Subgroup.centralizer_le_normalizer (H : Set G)

/-! ## The `pStableLocal` application for arbitrary normal `p`-subgroups -/

/-- The `pStable` application shape for an arbitrary normal `p`-subgroup: if `G` is
`p`-stable and `O_p(G) ≠ ⊥` (so that `⊤ ∈ M_p(G)`), then for every normal `p`-subgroup
`P` of `G` and every `x ∈ G` with `[P,x,x] = 1`, the coset of `x` modulo `C_G(P)` lies in
`O_p(G/C_G(P))`.  This generalises `pStableLocal_apply_of_core_normal`
(`Glauberman/pStability.lean`, the case `P = O_p(G)`) to arbitrary normal `p`-subgroups,
which is exactly how the `p`-stability hypothesis is used in the proof of `(3.5)` of
Theorem 3.2 (`refs/glauberman-p-stable.tex` L683–L689): there `P := C₁` is any normal
`p`-subgroup of `G` containing `C`, and the conclusion is fed into the containment
`O_p(G/C(C₁)) ⊆ L/C(C₁)` ("(3.4)"). -/
public theorem pStableLocal_apply_of_normal_pSubgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hstab : pStable p G) (hPne : pCore p G ≠ ⊥)
    {P : Subgroup G} (hPp : IsPGroup p P) (hPnorm : P.Normal) :
    ∀ x : G, ⁅⁅P, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ →
      QuotientGroup.mk' (Subgroup.centralizer (P : Set G)) x ∈
        pCore p (G ⧸ Subgroup.centralizer (P : Set G)) := by
  classical
  intro x hcomm
  -- `⊤ ∈ M_p(G)` because `O_p(⊤) ≅ O_p(G) ≠ ⊥`
  have hMtop : (⊤ : Subgroup G) ∈ MpSet p G := by
    change pCore p (↥(⊤ : Subgroup G)) ≠ ⊥ ∧
      ∀ K : Subgroup G, pCore p (↥K) ≠ ⊥ → (⊤ : Subgroup G) ≤ K → K = (⊤ : Subgroup G)
    constructor
    · intro hbot
      apply hPne
      have hmap := pCore_map_iso (G := ↥(⊤ : Subgroup G)) (G' := G) (p := p)
        (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G))
      simpa [hbot] using hmap.symm
    · intro K hKne htople
      exact le_antisymm le_top htople
  have hstabTop : pStableLocal p (G := ↥(⊤ : Subgroup G)) := hstab (⊤ : Subgroup G) hMtop
  -- work in the isomorphic copy `T := ↥(⊤ : Subgroup G)` of `G`
  let T := ↥(⊤ : Subgroup G)
  let e : T ≃* G := Subgroup.topEquiv
  have hP0p : IsPGroup p (P.map e.symm.toMonoidHom) :=
    IsPGroup.map hPp e.symm.toMonoidHom
  have hP0_normal : (P.map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hPnorm e.symm.toMonoidHom e.symm.surjective
  have hP0n : (pPrimeCore p T ⊔ P.map e.symm.toMonoidHom).Normal := by
    have hp' : pPrimeCore p T = (pPrimeCore p G).map e.symm.toMonoidHom := by
      exact (pPrimeCore_map_iso (G := G) (G' := T) (p := p) (f := e.symm)).symm
    rw [hp']
    dsimp
    rw [← Subgroup.map_sup (pPrimeCore p G) P (e.symm : G →* T)]
    exact Subgroup.Normal.map (Subgroup.sup_normal (pPrimeCore p G) P) e.symm.toMonoidHom
      e.symm.surjective
  let x0 : T := ⟨x, by simp⟩
  have hx0 : x0 ∈ Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hP0_normal]
    trivial
  -- the commutator hypothesis in `G` transports to `T`
  have hP0_map : (P.map e.symm.toMonoidHom).map e.toMonoidHom = P := by
    dsimp
    have hcomp : (e : T →* G).comp (e.symm : G →* T) = MonoidHom.id G := by
      ext g
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZ0_map : (Subgroup.zpowers x0).map e.toMonoidHom = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    congr 1
  have hcomm0 : ⁅⁅P.map e.symm.toMonoidHom, Subgroup.zpowers x0⁆, Subgroup.zpowers x0⁆ = ⊥ := by
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hP0_map, hZ0_map, hcomm,
      Subgroup.map_bot]
  -- the `pStableLocal` conclusion, with `N = N_T(P₀) = ⊤` and `C = C_T(P₀)`
  let N0 : Subgroup T := Subgroup.normalizer ((P.map e.symm.toMonoidHom) : Set T)
  let C0 : Subgroup T := Subgroup.centralizer ((P.map e.symm.toMonoidHom) : Set T)
  have hN0 : N0 = ⊤ := by simpa [N0] using (Subgroup.normalizer_eq_top_iff.mpr hP0_normal)
  have hC0_normal : C0.Normal := Subgroup.normal_centralizer (H := P.map e.symm.toMonoidHom)
  have : (C0.subgroupOf N0).Normal := Subgroup.Normal.subgroupOf hC0_normal N0
  have : (C0.subgroupOf (⊤ : Subgroup T)).Normal :=
    Subgroup.Normal.subgroupOf hC0_normal (⊤ : Subgroup T)
  have hconcl0 : QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩ ∈ pCore p (N0 ⧸ C0.subgroupOf N0) := by
    simpa [N0, C0] using (hstabTop (P.map e.symm.toMonoidHom) hP0p hP0n x0 hx0 hcomm0)
  -- step 1: transport `N0 ⧸ C0.subgroupOf N0` to `⊤ ⧸ C0.subgroupOf ⊤` (ambient `↥⊤`)
  let eN0 : ↥N0 ≃* ↥(⊤ : Subgroup T) :=
    { toEquiv := Equiv.subtypeEquivRight (fun y : T => by rw [hN0])
      map_mul' := by intro a b; rfl }
  have heN0 : (C0.subgroupOf N0).map (eN0 : ↥N0 →* ↥(⊤ : Subgroup T)) =
      C0.subgroupOf (⊤ : Subgroup T) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp [hN0]⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using (Subgroup.mem_subgroupOf.mp hy))
      · apply Subtype.ext
        rfl
  let Φ₀ : ↥N0 ⧸ C0.subgroupOf N0 ≃* ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) :=
    QuotientGroup.congr (G := ↥N0) (H := ↥(⊤ : Subgroup T))
      (G' := C0.subgroupOf N0) (H' := C0.subgroupOf (⊤ : Subgroup T)) eN0 heN0
  have hcore₀ : (pCore p (↥N0 ⧸ C0.subgroupOf N0)).map Φ₀.toMonoidHom =
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) :=
    pCore_map_iso (G := ↥N0 ⧸ C0.subgroupOf N0) (G' := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))
      (p := p) (f := Φ₀)
  have hmem₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [← hcore₀]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩, hconcl0, rfl⟩
  have happly₀ : Φ₀ (QuotientGroup.mk' (C0.subgroupOf N0) ⟨x0, hx0⟩) =
      QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T)) ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ := by
    dsimp [Φ₀]
    rfl
  have hconcl1 : QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩ ∈
      pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) := by
    rw [happly₀] at hmem₀
    exact hmem₀
  -- step 2: transport `⊤ ⧸ C0.subgroupOf ⊤` to `G ⧸ C` along `e : T ≃* G`
  have : (Subgroup.centralizer (P : Set G)).Normal := Subgroup.normal_centralizer (H := P)
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let eT : ↥(⊤ : Subgroup T) ≃* T := Subgroup.topEquiv
  let eTot : ↥(⊤ : Subgroup T) ≃* G := eT.trans e
  have he_subgroupOf : (C0.subgroupOf (⊤ : Subgroup T)).map eT.toMonoidHom = C0 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [eT] using (Subgroup.mem_subgroupOf.mp hz)
    · intro hy
      refine ⟨⟨y, by simp⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (by simpa using hy)
      · rfl
  have he_centralizer : C0.map e.toMonoidHom = C := by
    calc
      C0.map e.toMonoidHom =
          Subgroup.centralizer (((P.map e.symm.toMonoidHom).map e.toMonoidHom : Subgroup G) : Set G) := by
        exact map_centralizer_eq_of_equiv (e := e) (P := P.map e.symm.toMonoidHom)
      _ = C := by
        rw [hP0_map]
  have hcomp₁ : eTot.toMonoidHom = e.toMonoidHom.comp eT.toMonoidHom := by
    dsimp [eTot]
  have heTot : (C0.subgroupOf (⊤ : Subgroup T)).map eTot.toMonoidHom = C := by
    rw [hcomp₁, ← Subgroup.map_map, he_subgroupOf, he_centralizer]
  let Φ₁ : ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T) ≃* G ⧸ C :=
    QuotientGroup.congr (G := ↥(⊤ : Subgroup T)) (H := G)
      (G' := C0.subgroupOf (⊤ : Subgroup T)) (H' := C) eTot heTot
  have hcore₁ : (pCore p (↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T))).map Φ₁.toMonoidHom =
      pCore p (G ⧸ C) :=
    pCore_map_iso (G := ↥(⊤ : Subgroup T) ⧸ C0.subgroupOf (⊤ : Subgroup T)) (G' := G ⧸ C)
      (p := p) (f := Φ₁)
  have hmem₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) ∈ pCore p (G ⧸ C) := by
    rw [← hcore₁]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩, hconcl1, rfl⟩
  have happly₁ : Φ₁ (QuotientGroup.mk' (C0.subgroupOf (⊤ : Subgroup T))
      ⟨x0, (by simp : x0 ∈ (⊤ : Subgroup T))⟩) = QuotientGroup.mk' C x := by
    dsimp [Φ₁]
    rfl
  have hconcl : QuotientGroup.mk' C x ∈ pCore p (G ⧸ C) := by
    rw [happly₁] at hmem₁
    exact hmem₁
  simpa [C] using hconcl

/-! ## Lemma 3.5 (tex L571–L593) -/

/-- If `A ∈ A(P)` then `Z(J(P)) ≤ A`: `Z(J(P))·A` is Abelian (the centre of `J(P)`
commutes with `A ⊆ J(P)`) and contained in `P`, so maximality of `|A|` forces
`Z(J(P)) ⊆ A`.  This is the first conclusion of Lemma 3.5(a), stated for an arbitrary
subgroup `P` (no Sylow hypothesis needed). -/
private lemma lemma3_5a [Finite G] {P A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups (G := G) P) :
    thompsonCenter (G := G) P ≤ A := by
  classical
  let Z := thompsonCenter (G := G) P
  have hZ_le_P : Z ≤ P := thompsonCenter_le (G := G) P
  have hZ_cent_J : Z ≤ Subgroup.centralizer (thompsonSubgroup (G := G) P : Set G) := by
    exact inf_le_right
  have hA_le_J : A ≤ thompsonSubgroup (G := G) P := by
    exact le_sSup hA
  have hZA_comm : IsMulCommutative ((Z ⊔ A : Subgroup G)) := by
    rw [Subgroup.sup_eq_closure]
    let : IsMulCommutative Z := thompsonCenter_isMulCommutative (G := G) P
    let : IsMulCommutative A := hA.2.1
    refine Subgroup.isMulCommutative_closure (k := ((Z : Subgroup G) : Set G) ∪ ((A : Subgroup G) : Set G)) (Set.Pairwise.of_forall₂ ?_)
    intro y hy z hz
    show y * z = z * y
    rcases hy with hyZ | hyA
    · rcases hz with hzZ | hzA
      · exact setLike_mul_comm (s := Z) hyZ hzZ
      · exact (Subgroup.mem_centralizer_iff.mp (hZ_cent_J hyZ) z (hA_le_J hzA)).symm
    · rcases hz with hzZ | hzA
      · exact Subgroup.mem_centralizer_iff.mp (hZ_cent_J hzZ) y (hA_le_J hyA)
      · exact setLike_mul_comm (s := A) hyA hzA
  have hZA_le_P : Z ⊔ A ≤ P := sup_le hZ_le_P hA.1
  have hcard : Nat.card (Z ⊔ A : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (Z ⊔ A : Subgroup G) hZA_le_P hZA_comm
  have hA_le_ZA : A ≤ Z ⊔ A := le_sup_right
  have hZA_eq_A : A = Z ⊔ A := Subgroup.eq_of_le_of_card_ge hA_le_ZA hcard
  exact hZA_eq_A ▸ le_sup_left

/-- Within a Sylow `p`-subgroup `T`, if `J(T) ≤ P ≤ T` then `J(P) = J(T)`: every
`A ∈ A(T)` is an element of `A(P)` (it lies in `J(T) ≤ P`), and every `A ∈ A(P)` has
order `d(T)` hence lies in `A(T)`, so `J(P)` and `J(T)` are generated by the same set. -/
private lemma j_eq_of_sylow_le {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (T : Sylow p G) {P : Subgroup G}
    (hJ_le_P : thompsonSubgroup (T : Subgroup G) ≤ P) (hP_le_T : P ≤ (T : Subgroup G)) :
    thompsonSubgroup (G := G) P = thompsonSubgroup (T : Subgroup G) := by
  classical
  obtain ⟨A0, hA0⟩ := exists_mem_thompsonAbelianSubgroups (S := (T : Subgroup G))
  have hA0_le_J : A0 ≤ thompsonSubgroup (T : Subgroup G) := le_sSup hA0
  have hA0_le_P : A0 ≤ P := hA0_le_J.trans hJ_le_P
  have hA0_in_AP : A0 ∈ thompsonAbelianSubgroups (G := G) P := by
    refine ⟨hA0_le_P, hA0.2.1, ?_⟩
    intro B hB hBcomm
    exact hA0.2.2 B (hB.trans hP_le_T) hBcomm
  have hAP_card : ∀ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) P →
      Nat.card A = Nat.card A0 := by
    intro A hA
    have hle1 : Nat.card A ≤ Nat.card A0 := hA0.2.2 A (hA.1.trans hP_le_T) hA.2.1
    have hle2 : Nat.card A0 ≤ Nat.card A := hA.2.2 A0 hA0_le_P hA0.2.1
    exact le_antisymm hle1 hle2
  have hJTeP : thompsonSubgroup (T : Subgroup G) ≤ thompsonSubgroup (G := G) P := by
    refine sSup_le ?_
    intro A hA
    have hA_le_P : A ≤ P := (le_sSup hA).trans hJ_le_P
    have hA_in_AP : A ∈ thompsonAbelianSubgroups (G := G) P := by
      refine ⟨hA_le_P, hA.2.1, ?_⟩
      intro B hB hBcomm
      exact hA.2.2 B (hB.trans hP_le_T) hBcomm
    exact le_sSup hA_in_AP
  have hJPeT : thompsonSubgroup (G := G) P ≤ thompsonSubgroup (T : Subgroup G) := by
    refine sSup_le ?_
    intro A hA
    have hA_in_AT : A ∈ thompsonAbelianSubgroups (G := G) (T : Subgroup G) := by
      refine ⟨hA.1.trans hP_le_T, hA.2.1, ?_⟩
      intro B hB hBcomm
      have hcard : Nat.card B ≤ Nat.card A0 := hA0.2.2 B hB hBcomm
      rw [← hAP_card A hA] at hcard
      exact hcard
    exact le_sSup hA_in_AT
  exact le_antisymm hJPeT hJTeP

/-- Lemma 3.5 ([6], §3, p. 1108; `refs/glauberman-p-stable.tex` L571–L593): let `S` be a
Sylow `p`-subgroup of a finite group `G`.  Then:

(a) if `A ∈ A(S)` and `A ≤ P ≤ S`, then `Z(J(S)) ≤ A` and `Z(J(S)) ≤ Z(J(P))`;
(b) if `P` is a `p`-subgroup of `G` that contains `J(S)`, then `J(S) = J(P)`.

Route of the paper: (a) `Z(J(S))·A` is Abelian and `|A| = d(S)`, so maximality of `|A|`
gives `Z(J(S)) ⊆ A`; then `d(P) = |A| = d(S)` and `Z(J(S)) ⊆ A ⊆ J(P) ⊆ J(S)` give
`Z(J(S)) ⊆ Z(J(P))`.  (b) extend `P` to a Sylow `p`-subgroup `T` of `G`; then
`J(S) = J(T)` by the Sylow version (`thompsonSubgroup_eq_of_sylow_le`), and
`J(T) = J(P)` by the argument of (a) inside `T`. -/
public lemma lemma3_5 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) :
    (∀ {A P : Subgroup G}, A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) →
      A ≤ P → P ≤ (S : Subgroup G) → thompsonCenter (G := G) (S : Subgroup G) ≤ A) ∧
    (∀ {A P : Subgroup G}, A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) →
      A ≤ P → P ≤ (S : Subgroup G) → thompsonCenter (G := G) (S : Subgroup G) ≤
        thompsonCenter (G := G) P) ∧
    (∀ {P : Subgroup G}, IsPGroup p P → thompsonSubgroup (G := G) (S : Subgroup G) ≤ P →
      thompsonSubgroup (G := G) (S : Subgroup G) = thompsonSubgroup (G := G) P) := by
  classical
  constructor
  · intro A P hA hAP hPS
    exact lemma3_5a hA
  constructor
  · intro A P hA hAP hPS
    have hA_in_AP : A ∈ thompsonAbelianSubgroups (G := G) P := by
      refine ⟨hAP, hA.2.1, ?_⟩
      intro B hB hBcomm
      exact hA.2.2 B (hB.trans hPS) hBcomm
    have hA_le_JP : A ≤ thompsonSubgroup (G := G) P := le_sSup hA_in_AP
    have hJP_le_JS : thompsonSubgroup (G := G) P ≤ thompsonSubgroup (G := G) (S : Subgroup G) := by
      refine sSup_le ?_
      intro A' hA'
      have hA'_in_AS : A' ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) := by
        refine ⟨hA'.1.trans hPS, hA'.2.1, ?_⟩
        intro B hB hBcomm
        have hle1 : Nat.card B ≤ Nat.card A := hA.2.2 B hB hBcomm
        have hcardA' : Nat.card A' = Nat.card A := by
          have hle2 : Nat.card A' ≤ Nat.card A := hA.2.2 A' (hA'.1.trans hPS) hA'.2.1
          have hle3 : Nat.card A ≤ Nat.card A' := hA'.2.2 A hAP hA.2.1
          exact le_antisymm hle2 hle3
        rw [← hcardA'] at hle1
        exact hle1
      exact le_sSup hA'_in_AS
    intro z hz
    refine ⟨?_, ?_⟩
    · exact hA_le_JP (lemma3_5a hA hz)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy =>
        (Subgroup.mem_centralizer_iff.mp hz.2) y (hJP_le_JS hy))
  · intro P hPp hJS_le_P
    obtain ⟨T, hP_le_T⟩ := IsPGroup.exists_le_sylow hPp
    have hJS_le_T : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (T : Subgroup G) :=
      hJS_le_P.trans hP_le_T
    have hJS_eq_JS : thompsonSubgroup (G := G) (S : Subgroup G) =
        thompsonSubgroup (G := G) (T : Subgroup G) :=
      thompsonSubgroup_eq_of_sylow_le T S hJS_le_T
    have hJT_le_P : thompsonSubgroup (G := G) (T : Subgroup G) ≤ P := by
      simpa [hJS_eq_JS] using hJS_le_P
    have hJT_eq_JP : thompsonSubgroup (G := G) P = thompsonSubgroup (G := G) (T : Subgroup G) :=
      j_eq_of_sylow_le T hJT_le_P hP_le_T
    exact hJS_eq_JS.trans hJT_eq_JP.symm

/-! ## Sylow subgroups of normal subgroups and the Frattini argument -/

/-- If `N ⊴ G` and `S ∈ Syl_p G`, then `S ∩ N` (viewed as a subgroup of `N`) is a Sylow
`p`-subgroup of `N`: it is a `p`-group (as a subgroup of `S`), and it is maximal among the
`p`-subgroups of `N` because every `p`-subgroup `Q` of `N` is conjugate in `G` to a
subgroup of `S`, hence (conjugating back into the normal subgroup `N`) to a subgroup of
`S ∩ N`, so `|Q| ≤ |S ∩ N|`.  This is the standard "Sylow ∩ normal = Sylow of normal". -/
private lemma sylow_subgroupOf_normal {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (N : Subgroup G) [N.Normal] :
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
          rw [sylow_smul_subgroup_eq_map_conj x S]
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
`L ∩ S` is the Sylow `p`-subgroup of `L` supplied by `sylow_subgroupOf_normal`.  This is
Lemma 3.6 of the paper (`refs/glauberman-p-stable.tex` L595–L604), stated in the ambient
group `G`. -/
private lemma frattini_sup_eq_top {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (L : Subgroup G) [L.Normal] :
    Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ := by
  classical
  obtain ⟨P, hP_map⟩ := sylow_subgroupOf_normal S L
  have hfr := Sylow.normalizer_sup_eq_top (N := L) (P := P)
  simpa [hP_map] using hfr

/-! ## Theorem 3.2 (tex L606–L695) -/

/-- Theorem 3.2 ([6], §3, Theorem 3.2, p. 1109; `refs/glauberman-p-stable.tex` L606–L695):
let `p` be an odd prime and `S` a Sylow `p`-subgroup of a finite group `G`.  Suppose that
`B` is an Abelian normal `p`-subgroup of `G`.  If `G` is `p`-stable, then
`Z(J(S)) ∩ B` is a normal subgroup of `G`.

The proof follows the paper verbatim: `C = Z(J(S)) ∩ B`, `L` is the normal core of
`N_G(C)`; the Frattini argument (`frattini_sup_eq_top`) gives `G = L·N(L∩S)`; if
`J(S) ⊆ L∩S`, then `J(S) = J(L∩S)` by Lemma 3.5(b) and `G = L·N(J(S)) ⊆ N(C)`, so
`C ⊴ G`.  Otherwise `(3.3)`; the `p`-stability hypothesis yields `(3.5)` (an
`A ∈ A(S)` with `[C₁,A,A] = 1` for a normal `p`-subgroup `C₁ ⊇ C` lies in `L`), via the
containment `O_p(G/C(C₁)) ⊆ L/C(C₁)` ("(3.4)", the pullback of `O_p(G/C(C₁))` is
`C(C₁)·(M∩S) ⊆ N(C)`) and the local plumbing
`pStableLocal_apply_of_normal_pSubgroup`; Corollary 3.1 applied to `B` gives
`A₀ ∈ A(S)` with `A₀ ⊆ L`, hence `C ⊆ Z(J(S)) ⊆ Z(J(L∩S)) = X` ("(3.6)") and, again by
Frattini, `G = L·N(X)` ("(3.7)").  The normal closure `V = ⟨C^G⟩` satisfies `V ⊆ X`
("(3.8)": every conjugate of `C` by `g = ln`, `l ∈ L`, `n ∈ N(X)`, collapses via
`L ≤ N(C)` to a conjugate by `n`).  Choosing `A ∈ A(S)`, `A ⊄ L`, with `A ∩ V` maximal,
`(3.5)` applied to `C₁ := V` gives `[V,A,A] ≠ 1` ("(3.9)"); the Replacement Theorem
(theorem3_1b) applied to `(V,A)` yields `A* ∈ A(S)` with `A ∩ V < A* ∩ V` and
`[A*,A,A] = 1`; maximality forces `A* ⊆ L∩S`, so `X ⊆ A*` by Lemma 3.5(a) and
`[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`, contradicting `(3.9)`. -/
public theorem theorem3_2 {p : ℕ} [Fact p.Prime] (_hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) {B : Subgroup G} (hB_norm : B.Normal)
    (hB_p : IsPGroup p B) (hB_comm : IsMulCommutative B) (hstab : pStable p G) :
    ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G).Normal) := by
  classical
  let C : Subgroup G := ZJ (G := G) (S : Subgroup G) ⊓ B
  let L : Subgroup G := (Subgroup.normalizer (C : Set G)).normalCore
  have hL_normal : L.Normal := Subgroup.normalCore_normal _
  have : L.Normal := hL_normal
  have hL_le_NC : L ≤ Subgroup.normalizer (C : Set G) := Subgroup.normalCore_le _
  by_cases hB1 : B = ⊥
  · have hC_bot : C = ⊥ := by
      simp [C, hB1]
    simp [C, hC_bot]
  -- `B ≠ ⊥`, so `O_p(G) ≠ ⊥` (and `⊤ ∈ M_p(G)` below)
  have hOpne : pCore p G ≠ ⊥ := by
    have hB_le_core : B ≤ pCore p G := le_sSup ⟨hB_norm, hB_p⟩
    intro hbot
    apply hB1
    apply le_antisymm
    · intro b hb
      have hb' : b ∈ pCore p G := hB_le_core hb
      rw [hbot] at hb'
      exact Subgroup.mem_bot.mp hb'
    · exact bot_le
  -- `B ≤ S` (`B` is a normal `p`-subgroup)
  have hB_le_S : B ≤ (S : Subgroup G) := IsPGroup.le_sylow_of_normal (N := B) hB_p S
  -- `S` normalizes `Z(J(S))`, `B`, hence `C`
  have hS_le_NZJ : S ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
    calc
      S ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := Subgroup.le_normalizer
      _ ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonSubgroup (S : Subgroup G)
      _ ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonCenter (S : Subgroup G)
  have hS_le_NC : S ≤ Subgroup.normalizer (C : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      C.map (MulAut.conj s).toMonoidHom
          = ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G)).map (MulAut.conj s).toMonoidHom := rfl
      _ = (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj s).toMonoidHom ⊓
          B.map (MulAut.conj s).toMonoidHom := by
            exact Subgroup.map_inf (ZJ (G := G) (S : Subgroup G)) B (MulAut.conj s).toMonoidHom
              (MulAut.conj s).injective
      _ = ZJ (G := G) (S : Subgroup G) ⊓ B := by
        have hZJ : (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj s).toMonoidHom =
            ZJ (G := G) (S : Subgroup G) :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hS_le_NZJ hs))
        have hB : B.map (MulAut.conj s).toMonoidHom = B :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer_eq_top_iff.mpr hB_norm) ▸ trivial))
        rw [hZJ, hB]
  -- the Frattini argument: `G = L·N(L∩S)`
  have hfrattini : Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L = ⊤ :=
    frattini_sup_eq_top S L
  -- `N(L∩S) ≤ N(J(L∩S)) ≤ N(Z(J(L∩S)))`
  have hNL_le_NJL : Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_of_thompsonSubgroup ((S : Subgroup G) ⊓ L)
  have hNJL_le_NZL : Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((ZJ (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
    normalizer_le_normalizer_of_thompsonCenter ((S : Subgroup G) ⊓ L)
  let X : Subgroup G := ZJ (G := G) ((S : Subgroup G) ⊓ L)
  have hX_le_LS : X ≤ (S : Subgroup G) ⊓ L := thompsonCenter_le (G := G) ((S : Subgroup G) ⊓ L)
  -- `(3.5)`: `A ∈ A(S)`, `C ≤ C₁ ⊴ G` a `p`-subgroup, `[C₁,A,A] = 1` ⟹ `A ≤ L`
  have h35 : ∀ (A C1 : Subgroup G),
      A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) → C ≤ C1 → C1.Normal →
      IsPGroup p C1 → ⁅⁅C1, A⁆, A⁆ = ⊥ → A ≤ L := by
    intro A C1 hA hC_le_C1 hC1_norm hC1_p hC1AA
    have : C1.Normal := hC1_norm
    let C1cen : Subgroup G := Subgroup.centralizer (C1 : Set G)
    have : C1cen.Normal := Subgroup.normal_centralizer (H := C1)
    let q : G →* G ⧸ C1cen := QuotientGroup.mk' C1cen
    let M : Subgroup G := (pCore p (G ⧸ C1cen)).comap q
    have hM_normal : M.Normal := Subgroup.Normal.comap (pCore_normal (G := G ⧸ C1cen)) q
    have : M.Normal := hM_normal
    -- `C(C₁) ≤ N(C)`: `C ⊆ C₁`, so centralizing `C₁` centralizes `C`
    have hC1cen_le_NC : C1cen ≤ Subgroup.normalizer (C : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hx_eq : c * x * c⁻¹ = x := by
          calc
            c * x * c⁻¹ = x * c * c⁻¹ := by
              rw [Subgroup.mem_centralizer_iff.mp hc x (hC_le_C1 hx)]
            _ = x := by group
        rw [hx_eq]
        exact hx
      · intro hx'
        have hyC1 : c * x * c⁻¹ ∈ C1 := hC_le_C1 hx'
        have hcinv_x : c⁻¹ * (c * x * c⁻¹) = (c * x * c⁻¹) * c⁻¹ :=
          (Subgroup.mem_centralizer_iff.mp (C1cen.inv_mem hc) (c * x * c⁻¹) hyC1).symm
        have hx_eq : x = c⁻¹ * (c * x * c⁻¹) * c := by group
        have hx'C : c⁻¹ * (c * x * c⁻¹) * c ∈ C := by
          have h1 : c⁻¹ * (c * x * c⁻¹) * c = c * x * c⁻¹ := by
            calc
              c⁻¹ * (c * x * c⁻¹) * c = (c * x * c⁻¹) * (c⁻¹ * c) := by
                rw [hcinv_x]
                group
              _ = c * x * c⁻¹ := by group
          rw [h1]
          exact hx'
        rw [← hx_eq] at hx'C
        exact hx'C
    -- `M ≤ N(C)`: `M = C(C₁)·(M∩S)` (the image of `M` in `G/C(C₁)` is `O_p`, which lies
    -- in the image of `S`), and both `C(C₁)` and `S` lie in `N(C)`
    have hM_le_NC : M ≤ Subgroup.normalizer (C : Set G) := by
      let Sbar : Sylow p (G ⧸ C1cen) := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective C1cen)
      have hSbar : (Sbar : Subgroup (G ⧸ C1cen)) = (S : Subgroup G).map q := by
        simp [Sbar]
      have hO_le_Sbar : pCore p (G ⧸ C1cen) ≤ (Sbar : Subgroup (G ⧸ C1cen)) :=
        IsPGroup.le_sylow_of_normal (N := pCore p (G ⧸ C1cen)) (pCore_isPGroup (G := G ⧸ C1cen)) Sbar
      have hM_le_C1cenS : M ≤ C1cen ⊔ (S : Subgroup G) := by
        intro m hm
        have hqm : q m ∈ (S : Subgroup G).map q := by
          exact hO_le_Sbar (by simpa [hSbar] using (Subgroup.mem_comap.mp hm))
        rcases Subgroup.mem_map.mp hqm with ⟨s, hs, hqs⟩
        have hms : s⁻¹ * m ∈ C1cen := (QuotientGroup.eq.mp hqs)
        have hm_mem : s * (s⁻¹ * m) ∈ C1cen ⊔ (S : Subgroup G) := by
          rw [← sup_comm (S : Subgroup G) C1cen]
          exact Subgroup.mul_mem_sup hs hms
        rw [show m = s * (s⁻¹ * m) by group]
        exact hm_mem
      intro m hm
      have hm' : m ∈ (S : Subgroup G) ⊔ C1cen := by
        rw [sup_comm]
        exact hM_le_C1cenS hm
      rcases (Subgroup.mem_sup_of_normal_right (s := (S : Subgroup G)) (t := C1cen) (x := m)).1 hm'
        with ⟨s, hs, c, hc, hms⟩
      -- `m = s·c`, `s ∈ S ⊆ N(C)`, `c ∈ C(C₁) ⊆ N(C)`
      have hs_NC : s ∈ Subgroup.normalizer (C : Set G) := hS_le_NC hs
      have hc_NC : c ∈ Subgroup.normalizer (C : Set G) := hC1cen_le_NC hc
      have hm_mem : s * c ∈ Subgroup.normalizer (C : Set G) :=
        (Subgroup.normalizer (C : Set G)).mul_mem hs_NC hc_NC
      rw [show m = s * c by exact hms.symm]
      exact hm_mem
    -- `(3.4)`: `O_p(G/C(C₁)) ⊆ L/C(C₁)`
    have h34 : pCore p (G ⧸ C1cen) ≤ L.map q := by
      calc
        pCore p (G ⧸ C1cen) = M.map q := by
          exact (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective C1cen)
            (pCore p (G ⧸ C1cen))).symm
        _ ≤ L.map q := Subgroup.map_mono (Subgroup.normal_le_normalCore.mpr hM_le_NC)
    -- for `x ∈ A`: `[C₁,x,x] = 1`, so the `p`-stability plumbing applies
    intro x hxA
    have hx_comm : ⁅⁅C1, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ :=
      commutator_zpowers_le_of_mem hC1AA hxA
    have hx_core : QuotientGroup.mk' C1cen x ∈ pCore p (G ⧸ C1cen) :=
      pStableLocal_apply_of_normal_pSubgroup (p := p) hstab hOpne hC1_p hC1_norm x hx_comm
    have hx_Lmap : QuotientGroup.mk' C1cen x ∈ L.map q := h34 hx_core
    rcases Subgroup.mem_map.mp hx_Lmap with ⟨l, hl, hxl⟩
    have hxl_inv : l⁻¹ * x ∈ C1cen := (QuotientGroup.eq.mp hxl)
    have hC1cen_le_L : C1cen ≤ L := (Subgroup.normal_le_normalCore.mpr hC1cen_le_NC)
    rw [show x = l * (l⁻¹ * x) by group]
    exact L.mul_mem hl (hC1cen_le_L hxl_inv)
  -- Corollary 3.1 applied to `B ⊆ S`: `∃ A₀ ∈ A(S)` with `[B,A₀,A₀] = 1`
  obtain ⟨A0, hA0_AS, _hA0_norm, hA0_BAA⟩ := corollary3_1 (P := (S : Subgroup G)) S.isPGroup' (B := B)
    hB_le_S hB_comm (Subgroup.Normal.subgroupOf hB_norm (S : Subgroup G))
  -- `(3.5)` with `C₁ := B`: `A₀ ≤ L`
  have hC_le_B : C ≤ B := inf_le_right
  have hA0_le_L : A0 ≤ L := h35 A0 B hA0_AS hC_le_B hB_norm hB_p hA0_BAA
  -- `(3.6)`: `Z(J(S)) ⊆ Z(J(L∩S)) = X`
  have hA0_le_LS : A0 ≤ (S : Subgroup G) ⊓ L := le_inf hA0_AS.1 hA0_le_L
  have hZS_le_X : ZJ (G := G) (S : Subgroup G) ≤ X := by
    exact (lemma3_5 S).2.1 hA0_AS hA0_le_LS (inf_le_left : (S : Subgroup G) ⊓ L ≤ (S : Subgroup G))
  have hC_le_X : C ≤ X := (inf_le_left : C ≤ ZJ (G := G) (S : Subgroup G)).trans hZS_le_X
  -- `(3.7)`: `G = L·N(X)` (Frattini again, since `X` is characteristic in `L∩S`)
  have hG_eq_LNX : Subgroup.normalizer (X : Set G) ⊔ L = ⊤ := by
    apply le_antisymm
    · exact le_top
    · calc
        (⊤ : Subgroup G) = Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L := hfrattini.symm
        _ ≤ Subgroup.normalizer (X : Set G) ⊔ L := by
          exact sup_le_sup (hNL_le_NJL.trans hNJL_le_NZL) le_rfl
  -- `V = ⟨C^G⟩` (the normal closure of `C`)
  let V : Subgroup G := Subgroup.normalClosure (C : Set G)
  have hV_normal : V.Normal := Subgroup.normalClosure_normal
  have : V.Normal := hV_normal
  have hC_le_V : C ≤ V := Subgroup.le_normalClosure
  -- `(3.8)`: `V ⊆ X`
  have hV_le_X : V ≤ X := by
    dsimp [V, Subgroup.normalClosure]
    refine (Subgroup.closure_le (K := X)).2 ?_
    intro y hy
    rcases (Group.mem_conjugatesOfSet_iff).1 hy with ⟨a, ha, hconj⟩
    rcases isConj_iff.1 hconj with ⟨c, hy_eq⟩
    have hc_mem : c ∈ Subgroup.normalizer (X : Set G) ⊔ L := by
      rw [hG_eq_LNX]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (X : Set G)) (t := L)
      (x := c)).1 hc_mem with ⟨n, hn, l, hl, hcl⟩
    have hla : l * a * l⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hL_le_NC hl) a).1 ha
    have hnal : n * (l * a * l⁻¹) * n⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hn (l * a * l⁻¹)).1 (hC_le_X hla)
    have hcalc : y = n * (l * a * l⁻¹) * n⁻¹ := by
      calc
        y = c * a * c⁻¹ := hy_eq.symm
        _ = (n * l) * a * (n * l)⁻¹ := by rw [hcl]
        _ = n * (l * a * l⁻¹) * n⁻¹ := by group
    rw [hcalc]
    exact hnal
  -- `V` is a `p`-subgroup (it lies in `X ≤ L∩S ≤ S`)
  have hV_p : IsPGroup p V := by
    have hV_le_S : V ≤ (S : Subgroup G) := (hV_le_X.trans hX_le_LS).trans inf_le_left
    exact IsPGroup.to_le S.isPGroup' hV_le_S
  have hV_comm : IsMulCommutative V := by
    let : IsMulCommutative X := thompsonCenter_isMulCommutative (G := G) ((S : Subgroup G) ⊓ L)
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact setLike_mul_comm (s := X) (hV_le_X a.2) (hV_le_X b.2)
  -- `V ≤ S` (for the Replacement Theorem)
  have hV_le_S : V ≤ (S : Subgroup G) := (hV_le_X.trans hX_le_LS).trans inf_le_left
  have hA_le_NV (A : Subgroup G) : A ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hV_normal]
    exact le_top
  -- split on `J(S) ⊆ L∩S`
  by_cases hJS_le_LS : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (S : Subgroup G) ⊓ L
  · -- `J(S) ⊆ L∩S`: `J(S) = J(L∩S)` by Lemma 3.5(b), so `G = L·N(J(S)) ⊆ N(C)`
    have hJS_eq : thompsonSubgroup (G := G) (S : Subgroup G) =
        thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) :=
      (lemma3_5 S).2.2
        (IsPGroup.to_le S.isPGroup' (inf_le_left : (S : Subgroup G) ⊓ L ≤ (S : Subgroup G))) hJS_le_LS
    have hG_le_NC : (⊤ : Subgroup G) ≤ Subgroup.normalizer (C : Set G) := by
      calc
        (⊤ : Subgroup G) = Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ⊔ L := hfrattini.symm
        _ ≤ Subgroup.normalizer (C : Set G) := by
          refine sup_le ?_ ?_
          · calc
              Subgroup.normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G)
                  ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) ((S : Subgroup G) ⊓ L) : Subgroup G) : Set G) :=
                    hNL_le_NJL
              _ = Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
                    rw [hJS_eq]
              _ ≤ Subgroup.normalizer ((ZJ (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
                    normalizer_le_normalizer_of_thompsonCenter (S : Subgroup G)
              _ ≤ Subgroup.normalizer (C : Set G) := by
                intro n hn
                rw [Subgroup.mem_normalizer_iff_map_conj_eq]
                calc
                  C.map (MulAut.conj n).toMonoidHom
                      = ((ZJ (G := G) (S : Subgroup G) ⊓ B : Subgroup G)).map (MulAut.conj n).toMonoidHom := rfl
                  _ = (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj n).toMonoidHom ⊓
                      B.map (MulAut.conj n).toMonoidHom := by
                        exact Subgroup.map_inf (ZJ (G := G) (S : Subgroup G)) B (MulAut.conj n).toMonoidHom
                          (MulAut.conj n).injective
                  _ = ZJ (G := G) (S : Subgroup G) ⊓ B := by
                    have hZJ : (ZJ (G := G) (S : Subgroup G)).map (MulAut.conj n).toMonoidHom =
                        ZJ (G := G) (S : Subgroup G) :=
                      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
                    have hB : B.map (MulAut.conj n).toMonoidHom = B :=
                      (Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer_eq_top_iff.mpr hB_norm) ▸ trivial))
                    rw [hZJ, hB]
          · exact hL_le_NC
    have hNC_top : Subgroup.normalizer (C : Set G) = ⊤ := top_le_iff.mp hG_le_NC
    have hC_normal : C.Normal := (Subgroup.normalizer_eq_top_iff.mp hNC_top)
    simpa [C] using hC_normal
  · -- `(3.3)`: `J(S) ⊄ L∩S`; the long argument
    -- there is `A ∈ A(S)` with `A ⊄ L`
    have h_exists_A_notL : ∃ A : Subgroup G,
        A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) ∧ ¬ A ≤ L := by
      by_contra hnone
      have hJS_le_LS' : thompsonSubgroup (G := G) (S : Subgroup G) ≤ (S : Subgroup G) ⊓ L := by
        refine le_inf (thompsonSubgroup_le (G := G) (S : Subgroup G)) ?_
        refine sSup_le ?_
        intro A hA
        by_contra hAL
        exact hnone ⟨A, hA, hAL⟩
      exact hJS_le_LS hJS_le_LS'
    -- choose `A` with `A ∩ V` maximal among the `A ∈ A(S)` with `A ⊄ L`
    let t : Set (Subgroup G) := {A' : Subgroup G |
      A' ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) ∧ ¬ A' ≤ L}
    have ht_fin : t.Finite := Set.toFinite t
    have ht_ne : t.Nonempty := by
      rcases h_exists_A_notL with ⟨A', hA', hA'_notL⟩
      exact ⟨A', hA', hA'_notL⟩
    obtain ⟨A, hA_t, hA_max⟩ :=
      Set.exists_max_image t (fun A' : Subgroup G => Nat.card ((A' ⊓ V : Subgroup G))) ht_fin ht_ne
    have hA_AS : A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) := hA_t.1
    have hA_notL : ¬ A ≤ L := hA_t.2
    -- `(3.9)`: `[V,A,A] ≠ 1` by `(3.5)` with `C₁ := V`
    have hVAA_ne : ⁅⁅V, A⁆, A⁆ ≠ ⊥ := by
      intro hVAA
      exact hA_notL (h35 A V hA_AS hC_le_V hV_normal hV_p hVAA)
    -- the Replacement Theorem applied to `(V, A)`
    obtain ⟨Astar, hAstar_AS, hlt, hAstarAA⟩ := theorem3_1b (P := (S : Subgroup G)) S.isPGroup'
      hA_AS hV_le_S hV_comm (hA_le_NV A) hVAA_ne
    -- maximality of `A ∩ V` forces `A* ⊆ L ∩ S`
    have hAstar_le_LS : Astar ≤ (S : Subgroup G) ⊓ L := by
      have hAstar_le_L : Astar ≤ L := by
        by_contra hnot
        have hcard : Nat.card ((A ⊓ V : Subgroup G)) < Nat.card ((Astar ⊓ V : Subgroup G)) := by
          have hle : Nat.card ((A ⊓ V : Subgroup G)) ≤ Nat.card ((Astar ⊓ V : Subgroup G)) :=
            Subgroup.card_le_of_le hlt.le
          refine lt_of_le_of_ne hle ?_
          intro hEq
          have hEq' : A ⊓ V = Astar ⊓ V := Subgroup.eq_of_le_of_card_ge hlt.le (Nat.le_of_eq hEq.symm)
          exact hlt.ne hEq'
        exact (not_lt_of_ge (hA_max Astar ⟨hAstar_AS, hnot⟩)) hcard
      exact le_inf hAstar_AS.1 hAstar_le_L
    -- `X ≤ A*` (Lemma 3.5(a) with `P := L∩S`)
    have hAstar_in_ALS : Astar ∈ thompsonAbelianSubgroups (G := G) ((S : Subgroup G) ⊓ L) := by
      refine ⟨hAstar_le_LS, hAstar_AS.2.1, ?_⟩
      intro B' hB' hB'comm
      exact hAstar_AS.2.2 B' (le_trans hB' inf_le_left) hB'comm
    have hX_le_Astar : X ≤ Astar := lemma3_5a hAstar_in_ALS
    -- `[V,A,A] ⊆ [X,A,A] ⊆ [A*,A,A] = 1`, contradicting `(3.9)`
    have hVX_le : ⁅⁅V, A⁆, A⁆ ≤ ⁅⁅X, A⁆, A⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hV_le_X le_rfl) le_rfl
    have hXA_le : ⁅⁅X, A⁆, A⁆ ≤ ⁅⁅Astar, A⁆, A⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hX_le_Astar le_rfl) le_rfl
    have hVAA_le : ⁅⁅V, A⁆, A⁆ ≤ ⁅⁅Astar, A⁆, A⁆ := hVX_le.trans hXA_le
    have hVAA_bot : ⁅⁅V, A⁆, A⁆ = ⊥ := by
      refine le_bot_iff.mp (hVAA_le.trans (le_of_eq hAstarAA))
    exfalso
    exact hVAA_ne hVAA_bot

/-! ## Lemma 3.7 (tex L699–L733) -/

/-- Lemma 3.7 ([6], §3, Lemma 3.7, p. 1110; `refs/glauberman-p-stable.tex` L699–L733):
let `S` be a Sylow `p`-subgroup of a finite group `G` and let `H` be a subgroup of
`Z(J(S))`.  Then
`N(H) = C(H)(N(J(S)) ∩ N(H))`.

Proof of the paper: `C(H)` is normal in `N(H)`; let `T` be a Sylow `p`-subgroup of
`C(H)` containing `J(S)` (possible since `H ≤ Z(J(S)) ⊆ C(J(S))`, so `J(S) ≤ C(H)`).
The Frattini argument gives `N(H) = C(H)(N(T) ∩ N(H))`; by Lemma 3.5(b), `J(S) = J(T)`,
and `J(S)` is characteristic in `T`, so `N(T) ⊆ N(J(S))`.  The statement is given in the
equivalent sup form (the product is a subgroup because `C(H) ⊴ N(H)`). -/
public lemma lemma3_7 {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) {H : Subgroup G} (hH : H ≤ ZJ (G := G) (S : Subgroup G)) :
    Subgroup.normalizer (H : Set G) =
      Subgroup.centralizer (H : Set G) ⊔
        (Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (H : Set G)) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  -- `J(S) ≤ C(H)`: `H ⊆ Z(J(S)) ⊆ C(J(S))`
  have hJS_le_C : thompsonSubgroup (G := G) (S : Subgroup G) ≤ C := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hz : h ∈ ZJ (G := G) (S : Subgroup G) := hH hh
    exact (Subgroup.mem_centralizer_iff.mp hz.2 j hj).symm
  -- a Sylow `p`-subgroup `T₀` of `C(H)` containing `J(S)`
  have hJSsub_p : IsPGroup p ((thompsonSubgroup (G := G) (S : Subgroup G)).subgroupOf C) := by
    have hJS_p : IsPGroup p (thompsonSubgroup (G := G) (S : Subgroup G)) :=
      IsPGroup.to_le S.isPGroup' (thompsonSubgroup_le (G := G) (S : Subgroup G))
    exact hJS_p.of_equiv (Subgroup.subgroupOfEquivOfLe hJS_le_C).symm
  obtain ⟨T0, hJT0⟩ := IsPGroup.exists_le_sylow hJSsub_p
  -- `T = T₀` viewed in `G`
  let T : Subgroup G := (T0 : Subgroup (↥C)).map C.subtype
  have hJS_le_T : thompsonSubgroup (G := G) (S : Subgroup G) ≤ T := by
    intro j hj
    have hjC : j ∈ C := hJS_le_C hj
    have hjT0 : (⟨j, hjC⟩ : ↥C) ∈ (T0 : Subgroup (↥C)) := by
      exact hJT0 (Subgroup.mem_subgroupOf.mpr hj)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjC⟩, hjT0, rfl⟩
  -- `N_G(T) ≤ N_G(J(S))`: `J(T) = J(S)` (Lemma 3.5(b)) and `J(T)` characteristic in `T`
  have hJT_eq_JS : thompsonSubgroup (G := G) T = thompsonSubgroup (G := G) (S : Subgroup G) := by
    have hT_p : IsPGroup p T := IsPGroup.map T0.isPGroup' C.subtype
    exact ((lemma3_5 S).2.2 hT_p hJS_le_T).symm
  have hNT_le_NJ : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
    calc
      Subgroup.normalizer (T : Set G)
          ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) T : Subgroup G) : Set G) :=
            normalizer_le_normalizer_of_thompsonSubgroup T
      _ = Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
            rw [hJT_eq_JS]
  -- `N(H) ≤ N(C(H))` (for the Sylow transport below)
  have hN_le_NC : Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      C.map (MulAut.conj n).toMonoidHom
          = Subgroup.centralizer ((H : Subgroup G).map (MulAut.conj n).toMonoidHom : Set G) := by
            exact map_centralizer_eq_of_equiv (e := MulAut.conj n) (P := H)
      _ = C := by
        have hH' : (H : Subgroup G).map (MulAut.conj n).toMonoidHom = H :=
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn)
        rw [hH']
  refine le_antisymm ?_ ?_
  · -- `N(H) ⊆ C(H) ⊔ (N(J(S)) ∩ N(H))`
    intro n hn
    -- the automorphism of `C(H)` induced by `n`
    let e : ↥C ≃* ↥C :=
      { toFun := fun c => ⟨n * (c : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp (hN_le_NC hn) (c : G)).1 c.2⟩
        invFun := fun c => ⟨n⁻¹ * (c : G) * n, (Subgroup.mem_normalizer_iff''.mp (hN_le_NC hn) (c : G)).1 c.2⟩
        left_inv := by
          intro c
          apply Subtype.ext
          group
        right_inv := by
          intro c
          apply Subtype.ext
          group
        map_mul' := by
          intro c d
          apply Subtype.ext
          simp [mul_assoc] }
    -- `T' = n•T` as a Sylow `p`-subgroup of `C(H)`
    let T' : Sylow p (↥C) := T0.mapSurjective (f := e.toMonoidHom) e.surjective
    have hT'_map : (T' : Subgroup (↥C)).map C.subtype = T.map (MulAut.conj n).toMonoidHom := by
      -- `T' = T₀·e`, and `subtype ∘ e = (conj n) ∘ subtype`
      have hT' : (T' : Subgroup (↥C)) = (T0 : Subgroup (↥C)).map e.toMonoidHom := rfl
      have hsub_comp : C.subtype.comp e.toMonoidHom = (MulAut.conj n).toMonoidHom.comp C.subtype := by
        ext x
        simp [e, MulAut.conj_apply, mul_assoc]
      calc
        (T' : Subgroup (↥C)).map C.subtype
            = ((T0 : Subgroup (↥C)).map e.toMonoidHom).map C.subtype := by rw [hT']
        _ = (T0 : Subgroup (↥C)).map (C.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
        _ = (T0 : Subgroup (↥C)).map ((MulAut.conj n).toMonoidHom.comp C.subtype) := by rw [hsub_comp]
        _ = ((T0 : Subgroup (↥C)).map C.subtype).map (MulAut.conj n).toMonoidHom := by rw [Subgroup.map_map]
        _ = T.map (MulAut.conj n).toMonoidHom := rfl
    -- Sylow conjugacy in `C(H)`: `∃ c ∈ C(H)`, `c • T' = T₀`
    obtain ⟨c, hcT'⟩ : ∃ c : ↥C, c • T' = T0 := MulAction.exists_smul_eq (↥C) T' T0
    -- `c•(n•T) = T` in `G`
    have hcT : (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj (c : G)).toMonoidHom = T := by
      have hmap_smul : ((c • T' : Sylow p (↥C)) : Subgroup (↥C)).map C.subtype = T := by
        rw [hcT']
      have hcomp : ((c • T' : Sylow p (↥C)) : Subgroup (↥C)).map C.subtype =
          ((T' : Subgroup (↥C)).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
        rw [sylow_smul_subgroup_eq_map_conj c T']
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr ⟨C.subtype z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
          refine Subgroup.mem_map.mpr ⟨(MulAut.conj (c : ↥C)).toMonoidHom z,
            Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
          simp [MulAut.conj_apply, mul_assoc]
      have h1 : ((T' : Subgroup (↥C)).map C.subtype).map (MulAut.conj (c : G)).toMonoidHom = T := by
        rw [← hcomp]
        exact hmap_smul
      rw [← hT'_map]
      exact h1
    -- `c·n ∈ N(T)`
    have hcn_mem : (c : G) * n ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      calc
        T.map (MulAut.conj ((c : G) * n)).toMonoidHom
            = (T.map (MulAut.conj n).toMonoidHom).map (MulAut.conj (c : G)).toMonoidHom := by
              ext x
              constructor
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                refine Subgroup.mem_map.mpr ⟨(MulAut.conj n).toMonoidHom y,
                  Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, ?_⟩
                simp [MulAut.conj_apply, mul_assoc]
              · intro hx
                rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
                rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
                refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
                simp [MulAut.conj_apply, mul_assoc]
        _ = T := hcT
    -- `n = c⁻¹·(c·n) ∈ C(H)·(N(J(S)) ∩ N(H))`
    have hc_inv_mem : (c : G)⁻¹ ∈ C := C.inv_mem c.2
    have hcn_NH : (c : G) * n ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).mul_mem (centralizer_le_normalizer H c.2) hn
    have hcn_NJ : (c : G) * n ∈ Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) :=
      hNT_le_NJ hcn_mem
    let K : Subgroup G :=
      Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
        Subgroup.normalizer (H : Set G)
    have hc_inv_mem' : (c : G)⁻¹ ∈ C ⊔ K := (le_sup_left : C ≤ C ⊔ K) hc_inv_mem
    have hcn_mem' : (c : G) * n ∈ C ⊔ K := (le_sup_right : K ≤ C ⊔ K) ⟨hcn_NJ, hcn_NH⟩
    rw [show n = (c : G)⁻¹ * ((c : G) * n) by group]
    exact (C ⊔ K).mul_mem hc_inv_mem' hcn_mem'
  · -- `C(H) ⊔ (N(J(S)) ∩ N(H)) ≤ N(H)`
    refine sup_le ?_ ?_
    · exact centralizer_le_normalizer H
    · intro x hx
      exact hx.2

/-! ## Corollaries 3.4 and 3.5 (tex L697–L745) -/

/-- Corollary 3.4 ([6], §3, Corollary 3.4, p. 1110; `refs/glauberman-p-stable.tex`
L697–L709): let `p` be an odd prime and `S` a Sylow `p`-subgroup of a finite `p`-stable
group `G`.  Then (a) `Z(J(S)) ⊴ G` iff `Z(J(S))` is contained in a normal Abelian
subgroup of `G`; (b) if `O_p(G)` contains an element of `A(S)`, then `Z(J(S)) ⊴ G`.

Route of the paper: (a) one part is trivial; conversely, for a normal Abelian `B ⊇ Z(J(S))`
one applies Theorem 3.2 to the `p`-part `O_p(B)` of `B` (which contains `Z(J(S))` since
`Z(J(S)) ⊆ B` is a `p`-subgroup), so `Z(J(S)) = Z(J(S)) ∩ O_p(B) ⊴ G`.  (b) By Lemma
3.5(a), `Z(J(S)) ⊆ Z(J(O_p(G)))`, and `Z(J(O_p(G)))` is a normal Abelian subgroup of `G`,
so (a) applies. -/
public theorem corollary3_4 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) (hstab : pStable p G) :
    ((ZJ (G := G) (S : Subgroup G)).Normal ↔
      ∃ B : Subgroup G, B.Normal ∧ IsMulCommutative B ∧ ZJ (G := G) (S : Subgroup G) ≤ B) ∧
    ((∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (G := G) (S : Subgroup G) ∧
      A ≤ pCore p G) → (ZJ (G := G) (S : Subgroup G)).Normal) := by
  classical
  have hiff_a : (ZJ (G := G) (S : Subgroup G)).Normal ↔
      ∃ B : Subgroup G, B.Normal ∧ IsMulCommutative B ∧ ZJ (G := G) (S : Subgroup G) ≤ B := by
    constructor
    · intro hZ_normal
      refine ⟨ZJ (G := G) (S : Subgroup G), hZ_normal, ?_, le_rfl⟩
      exact thompsonCenter_isMulCommutative (G := G) (S : Subgroup G)
    · rintro ⟨B, hB_norm, hB_comm, hZ_le_B⟩
      -- apply Theorem 3.2 to the `p`-part `B' = O_p(B)` of `B`
      let B' : Subgroup G := (pCore p (↥B)).map B.subtype
      have hB'_le_B : B' ≤ B := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact y.2
      have hB'_norm : B'.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]
        apply le_antisymm
        · exact le_top
        · intro g hg
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          have hψ : (pCore p (↥B)).map (MulAut.conjNormal g).toMonoidHom = pCore p (↥B) :=
            (Subgroup.characteristic_iff_map_eq.mp (pCore_characteristic (G := ↥B) (p := p)))
              (MulAut.conjNormal g)
          calc
            B'.map (MulAut.conj g).toMonoidHom
                = ((pCore p (↥B)).map B.subtype).map (MulAut.conj g).toMonoidHom := rfl
            _ = (pCore p (↥B)).map ((MulAut.conj g).toMonoidHom.comp B.subtype) := by
                  rw [Subgroup.map_map]
            _ = (pCore p (↥B)).map (B.subtype.comp (MulAut.conjNormal g).toMonoidHom) := by
                  have hcomp : (MulAut.conj g).toMonoidHom.comp B.subtype =
                      B.subtype.comp (MulAut.conjNormal g).toMonoidHom := by
                    ext x
                    simp [MulAut.conjNormal_apply, mul_assoc]
                  rw [hcomp]
            _ = ((pCore p (↥B)).map (MulAut.conjNormal g).toMonoidHom).map B.subtype := by
                  rw [Subgroup.map_map]
            _ = (pCore p (↥B)).map B.subtype := by rw [hψ]
      have hB'_p : IsPGroup p B' :=
        IsPGroup.map (pCore_isPGroup (G := ↥B) (p := p)) B.subtype
      have hB'_comm : IsMulCommutative B' := by
        let : IsMulCommutative B := hB_comm
        rw [isMulCommutative_iff]
        intro a b
        apply Subtype.ext
        exact setLike_mul_comm (s := B) (hB'_le_B a.2) (hB'_le_B b.2)
      have hZ_le_B' : ZJ (G := G) (S : Subgroup G) ≤ B' := by
        intro z hz
        have hzB : z ∈ B := hZ_le_B hz
        have hzS : z ∈ (S : Subgroup G) := thompsonCenter_le (G := G) (S : Subgroup G) hz
        have hz_order : ∃ k : ℕ, orderOf (⟨z, hzB⟩ : ↥B) = p ^ k := by
          rcases (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨z, hzS⟩ with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have h1 : orderOf (⟨z, hzS⟩ : ↥S) = orderOf z := by
            change orderOf (⟨z, hzS⟩ : ↥S) = orderOf ((⟨z, hzS⟩ : ↥S) : G)
            exact (orderOf_injective (f := (S : Subgroup G).subtype) ((S : Subgroup G).subtype_injective)
              ⟨z, hzS⟩).symm
          calc
            orderOf (⟨z, hzB⟩ : ↥B) = orderOf z := by
              exact (orderOf_injective B.subtype B.subtype_injective ⟨z, hzB⟩).symm
            _ = orderOf (⟨z, hzS⟩ : ↥S) := h1.symm
            _ = p ^ k := hk
        let : IsMulCommutative (↥B) := hB_comm
        have hzp_normal : (Subgroup.zpowers (⟨z, hzB⟩ : ↥B)).Normal :=
          Subgroup.normal_of_isMulCommutative (Subgroup.zpowers (⟨z, hzB⟩ : ↥B))
        have hzp_p : IsPGroup p (Subgroup.zpowers (⟨z, hzB⟩ : ↥B)) := by
          rcases hz_order with ⟨k, hk⟩
          exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
        have hz_core : (⟨z, hzB⟩ : ↥B) ∈ pCore p (↥B) := by
          have hz_le : Subgroup.zpowers (⟨z, hzB⟩ : ↥B) ≤ pCore p (↥B) :=
            le_sSup (show (Subgroup.zpowers (⟨z, hzB⟩ : ↥B)).Normal ∧
              IsPGroup p (Subgroup.zpowers (⟨z, hzB⟩ : ↥B)) from ⟨hzp_normal, hzp_p⟩)
          exact hz_le (Subgroup.mem_zpowers (⟨z, hzB⟩ : ↥B))
        exact Subgroup.mem_map.mpr ⟨⟨z, hzB⟩, hz_core, rfl⟩
      have hZ_normal : (ZJ (G := G) (S : Subgroup G) ⊓ B' : Subgroup G).Normal :=
        theorem3_2 (p := p) hpodd S hB'_norm hB'_p hB'_comm hstab
      have hZ_eq : ZJ (G := G) (S : Subgroup G) ⊓ B' = ZJ (G := G) (S : Subgroup G) :=
        inf_eq_left.mpr hZ_le_B'
      simpa [hZ_eq] using hZ_normal
  refine ⟨hiff_a, ?_⟩
  -- (b): `B := Z(J(O_p(G)))` is a normal Abelian subgroup containing `Z(J(S))`
  intro hA0
  rcases hA0 with ⟨A, hA_AS, hA_le_core⟩
  let B : Subgroup G := ZJ (G := G) (pCore p G)
  have hB_le_core : B ≤ pCore p G := thompsonCenter_le (G := G) (pCore p G)
  have hB_norm : B.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply le_antisymm
    · exact le_top
    · calc
        (⊤ : Subgroup G) = Subgroup.normalizer ((pCore p G : Subgroup G) : Set G) := by
          exact (Subgroup.normalizer_eq_top_iff.mpr (pCore_normal (G := G) (p := p))).symm
        _ ≤ Subgroup.normalizer ((thompsonSubgroup (G := G) (pCore p G) : Subgroup G) : Set G) :=
              normalizer_le_normalizer_of_thompsonSubgroup (pCore p G)
        _ ≤ Subgroup.normalizer ((ZJ (G := G) (pCore p G) : Subgroup G) : Set G) :=
              normalizer_le_normalizer_of_thompsonCenter (pCore p G)
  have hB_comm : IsMulCommutative B :=
    thompsonCenter_isMulCommutative (G := G) (pCore p G)
  have hcore_le_S : pCore p G ≤ (S : Subgroup G) :=
    IsPGroup.le_sylow_of_normal (N := pCore p G) (pCore_isPGroup (G := G) (p := p)) S
  have hZ_le_B : ZJ (G := G) (S : Subgroup G) ≤ B :=
    (lemma3_5 S).2.1 hA_AS hA_le_core hcore_le_S
  exact hiff_a.2 ⟨B, hB_norm, hB_comm, hZ_le_B⟩

/-- Corollary 3.5 ([6], §3, Corollary 3.5, p. 1110; `refs/glauberman-p-stable.tex`
L735–L745): let `p` be an odd prime and `S` a Sylow `p`-subgroup of a finite group `G`.
Suppose that `G` is `p`-stable and that `C(O_p(G)) ⊆ O_p(G)`.  Then
`G = C(Z(S))·N(J(S))` (stated in the equivalent sup form).

Route of the paper: with `P = O_p(G)`, `Z(S) ⊆ C(P) ⊆ P` gives `Z(S) ⊆ Z(P)`; also
`Z(S) ⊆ Z(J(S))` (every element of `Z(S)` lies in every maximal Abelian subgroup of `S`,
because `Z(S)·A` is Abelian, and centralizes `J(S)`).  Theorem 3.2 applied to the Abelian
normal `p`-subgroup `B := Z(P)` gives `H := Z(P) ∩ Z(J(S)) ⊴ G`; Lemma 3.7 with `H`
gives `G = C(H)·N(J(S)) ⊆ C(Z(S))·N(J(S)) ⊆ G`. -/
public theorem corollary3_5 {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (S : Sylow p G) (hstab : pStable p G)
    (hCS : Subgroup.centralizer ((pCore p G : Subgroup G) : Set G) ≤ pCore p G) :
    Subgroup.centralizer ((centerIn (G := G) (S : Subgroup G)) : Set G) ⊔
        Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) = ⊤ := by
  classical
  let P : Subgroup G := pCore p G
  have hP_norm : P.Normal := pCore_normal (G := G) (p := p)
  have : P.Normal := hP_norm
  have hP_p : IsPGroup p P := pCore_isPGroup (G := G) (p := p)
  have hP_le_S : P ≤ (S : Subgroup G) :=
    IsPGroup.le_sylow_of_normal (N := P) hP_p S
  -- `Z(S) ⊆ C(P) ⊆ P`, hence `Z(S) ⊆ Z(P)`
  have hZS_le_CP : centerIn (G := G) (S : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr (fun p hp =>
      (Subgroup.mem_centralizer_iff.mp hz.2 p (hP_le_S hp)))
  have hZS_le_P : centerIn (G := G) (S : Subgroup G) ≤ P := hZS_le_CP.trans hCS
  have hZS_le_ZP : centerIn (G := G) (S : Subgroup G) ≤ centerIn (G := G) P := by
    intro z hz
    refine ⟨hZS_le_P hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun p hp =>
      (Subgroup.mem_centralizer_iff.mp hz.2 p (hP_le_S hp)))
  -- `Z(S) ⊆ J(S)`: `Z(S)·A` is Abelian for every `A ∈ A(S)`, so maximality of `|A|`
  -- gives `Z(S) ⊆ A`
  have hZS_le_JS : centerIn (G := G) (S : Subgroup G) ≤ thompsonSubgroup (G := G) (S : Subgroup G) := by
    intro z hz
    obtain ⟨A, hA⟩ := exists_mem_thompsonAbelianSubgroups (S := (S : Subgroup G))
    let ZS := centerIn (G := G) (S : Subgroup G)
    have hZ_comm : IsMulCommutative (ZS ⊔ A : Subgroup G) := by
      rw [Subgroup.sup_eq_closure]
      let : IsMulCommutative ZS := by
        rw [isMulCommutative_iff]
        intro a b
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp a.2.2 (b : G) b.2.1).symm
      let : IsMulCommutative A := hA.2.1
      refine Subgroup.isMulCommutative_closure
        (k := ((ZS : Subgroup G) : Set G) ∪ ((A : Subgroup G) : Set G)) (Set.Pairwise.of_forall₂ ?_)
      intro y hy z' hz'
      show y * z' = z' * y
      rcases hy with hyZ | hyA
      · rcases hz' with hzZ | hzA
        · exact setLike_mul_comm (s := ZS) hyZ hzZ
        · exact (Subgroup.mem_centralizer_iff.mp hyZ.2 z' (hA.1 hzA)).symm
      · rcases hz' with hzZ | hzA
        · exact Subgroup.mem_centralizer_iff.mp hzZ.2 y (hA.1 hyA)
        · exact setLike_mul_comm (s := A) hyA hzA
    have hZS_le_A : ZS ≤ A := by
      have hZA_le_S : ZS ⊔ A ≤ (S : Subgroup G) :=
        sup_le (by
          intro x hx
          exact hx.1) hA.1
      have hcard : Nat.card (ZS ⊔ A : Subgroup G) ≤ Nat.card A := hA.2.2 (ZS ⊔ A) hZA_le_S hZ_comm
      have hA_le_ZA : A ≤ ZS ⊔ A := le_sup_right
      have hZA_eq : A = ZS ⊔ A := Subgroup.eq_of_le_of_card_ge hA_le_ZA hcard
      exact hZA_eq ▸ le_sup_left
    exact (le_sSup hA) (hZS_le_A ⟨hz.1, hz.2⟩)
  -- `Z(S) ⊆ Z(J(S))`
  have hZS_le_ZJS : centerIn (G := G) (S : Subgroup G) ≤ ZJ (G := G) (S : Subgroup G) := by
    intro z hz
    refine ⟨hZS_le_JS hz, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hz.2 y (thompsonSubgroup_le (G := G) (S : Subgroup G) hy)))
  -- `H := Z(P) ∩ Z(J(S)) ⊴ G` by Theorem 3.2 applied to `B := Z(P)`
  let H : Subgroup G := centerIn (G := G) P ⊓ ZJ (G := G) (S : Subgroup G)
  have hZP_norm : (centerIn (G := G) P).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply le_antisymm
    · exact le_top
    · intro g hg
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hP_map : P.map (MulAut.conj g).toMonoidHom = P :=
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp ((Subgroup.normalizer_eq_top_iff.mpr hP_norm) ▸ trivial))
      calc
        (centerIn (G := G) P).map (MulAut.conj g).toMonoidHom
            = (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G).map (MulAut.conj g).toMonoidHom := rfl
        _ = P.map (MulAut.conj g).toMonoidHom ⊓
            (Subgroup.centralizer (P : Set G)).map (MulAut.conj g).toMonoidHom := by
              exact Subgroup.map_inf P (Subgroup.centralizer (P : Set G)) (MulAut.conj g).toMonoidHom
                (MulAut.conj g).injective
        _ = P ⊓ Subgroup.centralizer (P : Set G) := by
          rw [hP_map]
          rw [map_centralizer_eq_of_equiv (e := MulAut.conj g) (P := P), hP_map]
        _ = centerIn (G := G) P := rfl
  have hZP_p : IsPGroup p (centerIn (G := G) P) := IsPGroup.to_le hP_p (by
    intro z hz
    exact hz.1)
  have hZP_comm : IsMulCommutative (centerIn (G := G) P) := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp a.2.2 (b : G) b.2.1).symm
  have hT32 : (ZJ (G := G) (S : Subgroup G) ⊓ centerIn (G := G) P : Subgroup G).Normal :=
    theorem3_2 (p := p) hpodd S hZP_norm hZP_p hZP_comm hstab
  have hH_normal : H.Normal := by
    simpa [H, inf_comm] using hT32
  -- `Z(S) ⊆ H`
  have hZS_le_H : centerIn (G := G) (S : Subgroup G) ≤ H := by
    intro z hz
    exact ⟨hZS_le_ZP hz, hZS_le_ZJS hz⟩
  -- Lemma 3.7 with `H`
  have h37 := lemma3_7 (p := p) S (H := H) (by
    intro z hz
    exact hz.2)
  have hN : Subgroup.normalizer (H : Set G) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hH_normal
  have hG : (⊤ : Subgroup G) =
      Subgroup.centralizer (H : Set G) ⊔
        (Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
          Subgroup.normalizer (H : Set G)) := by
    rw [← hN]
    exact h37
  apply le_antisymm
  · exact le_top
  · calc
      (⊤ : Subgroup G) = Subgroup.centralizer (H : Set G) ⊔
          (Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) ⊓
            Subgroup.normalizer (H : Set G)) := hG
      _ = Subgroup.centralizer (H : Set G) ⊔
          Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
            rw [hN]
            simp
      _ ≤ Subgroup.centralizer ((centerIn (G := G) (S : Subgroup G)) : Set G) ⊔
          Subgroup.normalizer ((thompsonSubgroup (G := G) (S : Subgroup G) : Subgroup G) : Set G) := by
            exact sup_le_sup (Subgroup.centralizer_le hZS_le_H) le_rfl

module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_6

namespace CFSG
end CFSG
open CFSG

/-! # Gorenstein 5.4.15 support for BG Section 4 -/

section Main

open scoped FixedPoints IsMulCommutative commutatorElement
public theorem CFSG.exists_maximal_normal_abelian_subgroup_local'
    {G : Type*} [Group G] [Finite G] :
    ∃ A : Subgroup G,
      A.Normal ∧
        IsMulCommutative A ∧
        ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A := by
  classical
  let s : Set (Subgroup G) := {A | A.Normal ∧ IsMulCommutative A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor <;> infer_instance
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximal hsne
  refine ⟨A, hAmax.1.1, hAmax.1.2, ?_⟩
  intro B hBnorm hBcomm hAB
  exact le_antisymm (hAmax.2 ⟨hBnorm, hBcomm⟩ hAB) hAB

private theorem CFSG.exists_max_generatorRank_normal_abelian_subgroup_local
    {G : Type*} [Group G] [Finite G] :
    ∃ A : Subgroup G,
      A.Normal ∧
        IsMulCommutative A ∧
        ∀ B : Subgroup G, B.Normal → IsMulCommutative B →
          generatorRank B ≤ generatorRank A := by
  classical
  let s : Set (Subgroup G) := {A | A.Normal ∧ IsMulCommutative A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor <;> infer_instance
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximalFor (fun A : Subgroup G => generatorRank A) s hsne
  refine ⟨A, hAmax.1.1, hAmax.1.2, ?_⟩
  intro B hBnorm hBcomm
  exact hAmax.le ⟨hBnorm, hBcomm⟩

public theorem CFSG.generatorRank_le_card {G : Type*} [Group G] [Finite G] :
    generatorRank G ≤ Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let e : Fin (Nat.card G) ≃ G :=
    (finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm
  unfold generatorRank
  refine Nat.sInf_le ?_
  refine ⟨fun i => e i, ?_⟩
  apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range fun i : Fin (Nat.card G) => e i))).2
  intro x
  exact Subgroup.subset_closure ⟨e.symm x, by simp [e]⟩

private theorem CFSG.groupRank_le_generatorRank_finite {G : Type*} [Group G] [Finite G] :
    Group.rank G ≤ generatorRank G := by
  classical
  by_cases hgen :
      {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤}.Nonempty
  · have hsInf_mem :
        sInf {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} ∈
          {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} :=
      Nat.sInf_mem hgen
    rcases hsInf_mem with ⟨s, hs⟩
    let t : Finset G := Finset.univ.image s
    have ht_closure : Subgroup.closure (t : Set G) = ⊤ := by
      rw [Fintype.coe_image_univ]
      simpa [t] using hs
    calc
      Group.rank G ≤ t.card := Group.rank_le ht_closure
      _ ≤ Fintype.card (Fin (sInf {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤})) :=
        Finset.card_image_le
      _ = generatorRank G := by simp [generatorRank]
  · have hempty :
        {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hgen
    have hfalse : False := by
      refine hgen ?_
      refine ⟨Nat.card G, ?_⟩
      let : Fintype G := Fintype.ofFinite G
      let e : Fin (Nat.card G) → G := fun i =>
        ((finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm) i
      refine ⟨e, ?_⟩
      apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range e))).2
      intro x
      refine Subgroup.subset_closure ?_
      let e' : Fin (Nat.card G) ≃ G :=
        (finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm
      exact ⟨e'.symm x, by simp [e, e']⟩
    exact False.elim hfalse

private theorem CFSG.not_isCyclic_of_two_lt_generatorRank {G : Type*} [Group G]
    (hrank : 2 < generatorRank G) : ¬ IsCyclic G := by
  intro hcyc
  have hle : generatorRank G ≤ 1 := generatorRank_le_one_of_isCyclic (G := G) hcyc
  have hle' : generatorRank G ≤ 2 := le_trans hle (by decide)
  exact (not_lt_of_ge hle') hrank

private theorem CFSG.generatorRank_le_of_surjective {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    generatorRank H ≤ generatorRank G := by
  classical
  unfold generatorRank
  by_cases hgen :
      {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤}.Nonempty
  · have hsInf_mem :
        sInf {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} ∈
          {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} :=
      Nat.sInf_mem hgen
    rcases hsInf_mem with ⟨s, hs⟩
    refine Nat.sInf_le ?_
    refine ⟨fun i => f (s i), ?_⟩
    apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range fun i => f (s i)))).2
    intro y
    rcases hf y with ⟨x, rfl⟩
    have hx : x ∈ Subgroup.closure (Set.range s) := by simp [hs]
    change f x ∈ Subgroup.closure (Set.range fun i => f (s i))
    refine Subgroup.closure_induction (k := Set.range s)
      (p := fun z _ => f z ∈ Subgroup.closure (Set.range fun i => f (s i))) (x := x) ?_ ?_ ?_ ?_ hx
    · rintro z ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simp
    · intro a b _ _ ha hb
      simpa [map_mul] using (Subgroup.closure (Set.range fun i => f (s i))).mul_mem ha hb
    · intro a _ ha
      simpa [MonoidHom.map_inv] using (Subgroup.closure (Set.range fun i => f (s i))).inv_mem ha
  · have hempty :
        {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hgen
    have hfalse : False := by
      refine hgen ?_
      refine ⟨Nat.card G, ?_⟩
      let : Fintype G := Fintype.ofFinite G
      let e : Fin (Nat.card G) → G := fun i =>
        ((finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm) i
      refine ⟨e, ?_⟩
      apply (Subgroup.eq_top_iff' (H := Subgroup.closure (Set.range e))).2
      intro x
      refine Subgroup.subset_closure ?_
      let e' : Fin (Nat.card G) ≃ G :=
        (finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm
      exact ⟨e'.symm x, by simp [e, e']⟩
    exact False.elim hfalse

private theorem CFSG.primeRank_le_card {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  let S : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A))
  by_cases hS : S.Nonempty
  · have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hS hSbdd
    rcases hsSup_mem with ⟨A, _hAq, _hAcomm, hsSup_le⟩
    rw [primeRank]
    exact le_trans hsSup_le (le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A))
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hSet :
        {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} = ∅ := by
      simpa [S] using hSempty
    rw [primeRank, hSet]
    simp

public theorem CFSG.primeRank_le_groupRank {R : Type*} [Group R] [Finite R] {q : ℕ}
    (hq : Nat.Prime q) :
    primeRank q R ≤ groupRank R := by
  let S : Set ℕ := {n : ℕ | ∃ q' : ℕ, Nat.Prime q' ∧ n ≤ primeRank q' R}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q', _hq', hnq'⟩
    exact le_trans hnq' (primeRank_le_card (R := R) q')
  have hmem : primeRank q R ∈ S := ⟨q, hq, le_rfl⟩
  simpa [groupRank, S] using (le_csSup hSbdd hmem)

public theorem CFSG.generatorRank_le_groupRank_of_isPGroup_abelian_subgroup
    {R : Type*} [Group R] [Finite R] {q : ℕ} [Fact q.Prime]
    {A : Subgroup R} (hAq : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
    exact le_trans hnB (le_trans (generatorRank_le_card (G := B)) (Subgroup.card_le_card_group B))
  have hmem : generatorRank A ∈ T := ⟨A, hAq, hAcomm, le_rfl⟩
  have hprimeRank : generatorRank A ≤ primeRank q R := by
    simpa [primeRank, T] using (le_csSup hTbdd hmem)
  exact hprimeRank.trans (primeRank_le_groupRank (R := R) (q := q) Fact.out)

public theorem CFSG.generatorRank_le_of_equiv {G H : Type*} [Group G] [Finite G] [Group H]
    (e : G ≃* H) :
    generatorRank H ≤ generatorRank G := by
  exact generatorRank_le_of_surjective (G := G) (H := H) e.toMonoidHom e.surjective

public theorem CFSG.primeRank_le_of_subgroup {R : Type*} [Group R] [Finite R] (S : Subgroup R)
    (q : ℕ) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA <|
      le_trans (generatorRank_le_card (G := A)) <|
        le_trans (Subgroup.card_le_card_group A) (Subgroup.card_le_card_group S)
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map S.subtype
    have hA'q : IsPGroup q A' := IsPGroup.map (p := q) (H := A) hAq S.subtype
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hcard_eq : Nat.card A' = Nat.card A := by
      exact Subgroup.card_map_of_injective (K := A) (f := S.subtype) S.subtype_injective
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let e : A ≃* A' := Subgroup.equivMapOfInjective A S.subtype S.subtype_injective
      exact generatorRank_le_of_equiv (G := A') (H := A) e.symm
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      simpa [primeRank] using le_csSup
        (show BddAbove {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
            n ≤ generatorRank B} from
          ⟨Nat.card R, by
            intro n hn
            rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
            exact le_trans hnB (le_trans (generatorRank_le_card (G := B))
              (Subgroup.card_le_card_group B))⟩)
        hmem
    rw [primeRank]
    exact le_trans hsSup_le hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp


public theorem CFSG.groupRank_le_of_subgroup {R : Type*} [Group R] [Finite R] (S : Subgroup R) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact le_trans hnq <|
      le_trans (primeRank_le_of_subgroup (S := S) q) (primeRank_le_card (R := R) q)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R :=
      (primeRank_le_of_subgroup (S := S) q).trans (primeRank_le_groupRank (R := R) hq)
    rw [groupRank]
    exact le_trans hsSup_le hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

private theorem CFSG.primeRank_le_of_equiv {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A))
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' := IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' := Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      exact generatorRank_le_of_equiv (G := A') (H := A) eA.symm
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      simpa [primeRank] using le_csSup
        (show BddAbove {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
            n ≤ generatorRank B} from
          ⟨Nat.card R, by
            intro n hn
            rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
            exact le_trans hnB (le_trans (generatorRank_le_card (G := B))
              (Subgroup.card_le_card_group B))⟩)
        hmem
    rw [primeRank]
    exact le_trans hsSup_le hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

public theorem CFSG.groupRank_le_of_equiv {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := S) q)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R :=
      (primeRank_le_of_equiv (R := R) (S := S) q e).trans (primeRank_le_groupRank (R := R) hq)
    rw [groupRank]
    exact le_trans hsSup_le hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

private theorem CFSG.generatorRank_le_primeRank_of_isPGroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hRcomm : IsMulCommutative R) :
    generatorRank R ≤ primeRank p R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A))
  have htop_p : IsPGroup p (⊤ : Subgroup R) := by
    simpa using hRp.to_subgroup (⊤ : Subgroup R)
  have htop_comm : IsMulCommutative (⊤ : Subgroup R) := by
    let : IsMulCommutative R := hRcomm
    infer_instance
  have hgen_le_top : generatorRank R ≤ generatorRank (⊤ : Subgroup R) := by
    exact generatorRank_le_of_equiv (G := (⊤ : Subgroup R)) (H := R) Subgroup.topEquiv
  have hmem : generatorRank R ∈ T := ⟨⊤, htop_p, htop_comm, hgen_le_top⟩
  simpa [primeRank, T] using (le_csSup hTbdd hmem)


private theorem CFSG.groupRank_le_primeRank_of_isPGroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) :
    groupRank R ≤ primeRank p R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := R) q)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    let : Fact q.Prime := ⟨hq⟩
    have hqrank_le : primeRank q R ≤ primeRank p R := by
      by_cases hT :
          {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A}.Nonempty
      · have hTbdd : BddAbove
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} := by
          refine ⟨Nat.card R, ?_⟩
          intro n hn
          rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
          exact le_trans hnA (le_trans (generatorRank_le_card (G := A))
            (Subgroup.card_le_card_group A))
        have hsT_mem : sSup
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} ∈
            {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} :=
          Nat.sSup_mem hT hTbdd
        rcases hsT_mem with ⟨A, hAq, hAcomm, hsT_le⟩
        have hAp : IsPGroup p A := hRp.to_subgroup A
        have hgen_le_p : generatorRank A ≤ primeRank p R :=
          generatorRank_le_primeRank_of_isPGroup (R := A) (p := p) hAp hAcomm |>.trans
            (primeRank_le_of_subgroup (R := R) (S := A) p)
        rw [primeRank]
        exact le_trans hsT_le hgen_le_p
      · have hTempty :
          {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
              n ≤ generatorRank A} = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
        rw [primeRank, hTempty]
        simp
    rw [groupRank]
    exact le_trans hsSup_le hqrank_le
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

public theorem CFSG.groupRank_le_two_of_primeRank_le_two_of_isPGroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hrank : primeRank p R ≤ 2) :
    groupRank R ≤ 2 :=
  (groupRank_le_primeRank_of_isPGroup (R := R) (p := p) hRp).trans hrank

private theorem CFSG.exists_abelian_subgroup_three_le_generatorRank_of_two_lt_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 < groupRank R) :
    ∃ A : Subgroup R, IsMulCommutative A ∧ 3 ≤ generatorRank A := by
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hrank' : 2 < sSup S := by
    simpa [groupRank, S] using hrank
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := R) q)
  have hSnonempty : S.Nonempty := by
    by_contra hS
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have : ¬ 2 < sSup S := by simp [hSempty]
    exact this hrank'
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, _hqprime, hsSup_le⟩
  have hqrank : 2 < primeRank q R := lt_of_lt_of_le hrank' hsSup_le
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hqrank' : 2 < sSup T := by
    simpa [primeRank, T] using hqrank
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact le_trans hnA (le_trans (generatorRank_le_card (G := A)) (Subgroup.card_le_card_group A))
  have hTnonempty : T.Nonempty := by
    by_contra hT
    have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have : ¬ 2 < sSup T := by simp [hTempty]
    exact this hqrank'
  have htSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases htSup_mem with ⟨A, _hAq, hAcomm, htSup_le⟩
  refine ⟨A, hAcomm, Nat.succ_le_of_lt ?_⟩
  exact lt_of_lt_of_le hqrank' htSup_le

private theorem CFSG.three_le_groupRank_of_mem_selfCentralizingAbelianSubgroupsAtLeast
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hRp : IsPGroup p R) {A : Subgroup R}
    (hA : A ∈ selfCentralizingAbelianSubgroupsAtLeast R 3) :
    3 ≤ groupRank R := by
  have hAcomm : IsMulCommutative A := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 <|
      by simp [hA.1.2]
  have hprimeRank : 3 ≤ primeRank p R := by
    let S : Set ℕ :=
      {n : ℕ | ∃ A : Subgroup R, IsPGroup p A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
    have hSbdd : BddAbove S := by
      refine ⟨Nat.card R, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact le_trans hnB (le_trans (generatorRank_le_card (G := B)) (Subgroup.card_le_card_group B))
    have hmem :
        3 ∈ S :=
      ⟨A, hRp.to_subgroup A, hAcomm, hA.2⟩
    simpa [primeRank, S] using (le_csSup hSbdd hmem)
  have hmem :
      primeRank p R ∈ {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R} :=
    ⟨p, Fact.out, le_rfl⟩
  let T : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact le_trans hnq (primeRank_le_card (R := R) q)
  exact le_trans hprimeRank <|
    by simpa [groupRank, T] using (le_csSup hTbdd hmem)

public theorem CFSG.selfCentralizingAbelianSubgroupsAtLeast_eq_empty_of_groupRank_le_two
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hRp : IsPGroup p R) (hrank : groupRank R ≤ 2) :
    selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false]
  constructor
  · intro hA
    have hthree : 3 ≤ groupRank R :=
      three_le_groupRank_of_mem_selfCentralizingAbelianSubgroupsAtLeast (R := R) (p := p) hRp hA
    have hlt : groupRank R < 3 := lt_of_le_of_lt hrank (by decide)
    exact (not_le_of_gt hlt) hthree
  · intro hA
    exact False.elim hA

public theorem CFSG.exists_normal_elementaryAbelian_subgroup_order_p_sq_of_two_lt_groupRank
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R) (hrank : 2 < groupRank R) :
    ∃ A : Subgroup R, A.Normal ∧ Nat.card A = p ^ 2 ∧ IsElementaryAbelian p A := by
  classical
  let : Fact (IsPGroup p R) := ⟨hRp⟩
  obtain ⟨B, _hBcomm, hBrank⟩ :=
    exists_abelian_subgroup_three_le_generatorRank_of_two_lt_groupRank (R := R) hrank
  have hB_noncyclic : ¬ IsCyclic B := by
    apply not_isCyclic_of_two_lt_generatorRank
    exact lt_of_lt_of_le (by decide) hBrank
  let N : Subgroup R := Subgroup.normalClosure (↑B : Set R)
  have hN_noncyclic : ¬ IsCyclic N := by
    intro hNcyc
    let : IsCyclic N := hNcyc
    have hB_le_N : B ≤ N := by
      simpa [N] using (Subgroup.le_normalClosure (H := B))
    exact hB_noncyclic (Subgroup.isCyclic_of_le hB_le_N)
  let : N.Normal := by
    dsimp [N]
    infer_instance
  obtain ⟨A, hA_normal, hA_le_N, hAcard, hAelem⟩ :=
    proposition_4_6 (R := R) (p := p) hpodd N hN_noncyclic
  exact ⟨A, hA_normal, hAcard, hAelem⟩


private theorem CFSG.isMulCommutative_of_contains_normal_subgroup_le_centralizer_and_prime_quotient
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    {E B : Subgroup R} (hEnorm : E.Normal) (hB_le_cent : B ≤ Subgroup.centralizer (E : Set R))
    (hquot_card : Nat.card (B ⧸ E.subgroupOf B) = p) :
    IsMulCommutative B := by
  classical
  have : (E.subgroupOf B).Normal := by
    exact Subgroup.Normal.subgroupOf (G := R) (hH := hEnorm) B
  have hEsub_le_center : E.subgroupOf B ≤ Subgroup.center B := by
    intro e he
    rw [Subgroup.mem_center_iff]
    intro b
    have heE : ((e : B) : R) ∈ E := by simpa [Subgroup.mem_subgroupOf] using he
    have hbcent : ((b : B) : R) ∈ Subgroup.centralizer (E : Set R) := hB_le_cent b.2
    have hcomm : (e : R) * (b : R) = (b : R) * (e : R) :=
      (Subgroup.mem_centralizer_iff.mp hbcent) (e : R) heE
    apply Subtype.ext
    exact hcomm.symm
  have hquot_cyc : IsCyclic (B ⧸ E.subgroupOf B) := by
    exact isCyclic_of_prime_card (α := B ⧸ E.subgroupOf B) hquot_card
  let : IsCyclic (B ⧸ E.subgroupOf B) := hquot_cyc
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (E.subgroupOf B))
    (by simpa [QuotientGroup.ker_mk'] using hEsub_le_center)

private theorem CFSG.lift_order_p_quotient_subgroup_to_normal_prime_index_overgroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    {E : Subgroup R} (hEnorm : E.Normal)
    {Kbar : Subgroup (R ⧸ E)} (hKbar_norm : Kbar.Normal) (hKbar_card : Nat.card Kbar = p) :
    ∃ B : Subgroup R, E ≤ B ∧ B.Normal ∧
      Nat.card (B ⧸ E.subgroupOf B) = p ∧
      B.map (QuotientGroup.mk' E) = Kbar := by
  classical
  let : E.Normal := hEnorm
  let q : R →* R ⧸ E := QuotientGroup.mk' E
  let B : Subgroup R := Kbar.comap q
  have hE_le_B : E ≤ B := by
    intro x hx
    change q x ∈ Kbar
    have hx1 : q x = 1 := (QuotientGroup.eq_one_iff (N := E) (x := x)).2 hx
    simp [hx1]
  have hB_normal : B.Normal := by
    dsimp [B]
    exact Subgroup.Normal.comap hKbar_norm q
  have hB_map : B.map q = Kbar := by
    dsimp [B, q]
    exact Subgroup.map_comap_eq_self_of_surjective (f := QuotientGroup.mk' E)
      (QuotientGroup.mk'_surjective E) Kbar
  have : (E.subgroupOf B).Normal := by
    exact Subgroup.Normal.subgroupOf (G := R) (hH := hEnorm) B
  have hquot_card : Nat.card (B ⧸ E.subgroupOf B) = p := by
    let e : (B ⧸ E.subgroupOf B) ≃* Kbar :=
      (quotientSubgroupRangeEquiv B E).trans (MulEquiv.subgroupCongr hB_map)
    calc
      Nat.card (B ⧸ E.subgroupOf B) = Nat.card Kbar := Nat.card_congr e.toEquiv
      _ = p := hKbar_card
  exact ⟨B, hE_le_B, hB_normal, hquot_card, hB_map⟩

private theorem CFSG.exists_abelian_normal_prime_index_overgroup_between_of_lt
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)]
    {E L : Subgroup R} (hEnorm : E.Normal) (_hEcomm : IsMulCommutative E)
    (hLnorm : L.Normal) (hE_le_L : E ≤ L)
    (hL_le_cent : L ≤ Subgroup.centralizer (E : Set R)) (hlt : E < L) :
    ∃ B : Subgroup R, E ≤ B ∧ B.Normal ∧ IsMulCommutative B ∧
      Nat.card (B ⧸ E.subgroupOf B) = p ∧ B ≤ L := by
  classical
  let : E.Normal := hEnorm
  let q : R →* R ⧸ E := QuotientGroup.mk' E
  let Lbar : Subgroup (R ⧸ E) := L.map q
  have hLbar_normal : Lbar.Normal := by
    dsimp [Lbar, q]
    exact Subgroup.Normal.map (H := L) hLnorm (QuotientGroup.mk' E)
      (QuotientGroup.mk'_surjective E)
  let : Lbar.Normal := hLbar_normal
  let Esub : Subgroup L := E.subgroupOf L
  have hEsub_normal : Esub.Normal := by
    exact Subgroup.Normal.subgroupOf (G := R) (hH := hEnorm) L
  let : Esub.Normal := hEsub_normal
  have hLbar_card : Nat.card Lbar = Nat.card (L ⧸ Esub) := by
    simpa [Lbar, Esub, q] using natCard_map_mk'_eq (K := L) (N := E)
  have hEsub_lt_top : Esub < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    have hL_le_E : L ≤ E := by
      intro x hx
      have hxEsub : (⟨x, hx⟩ : L) ∈ Esub := by simp [htop]
      simpa [Esub, Subgroup.mem_subgroupOf] using hxEsub
    exact hlt.2 hL_le_E
  have hquot_nontriv : Nontrivial (L ⧸ Esub) :=
    (QuotientGroup.nontrivial_iff (G := L) (N := Esub)).2 hEsub_lt_top.ne
  have hLbar_nontriv : Nontrivial Lbar := by
    have hcard_gt : 1 < Nat.card (L ⧸ Esub) :=
      Finite.one_lt_card_iff_nontrivial.mpr hquot_nontriv
    have hcard_gt_bar : 1 < Nat.card Lbar := by simpa [hLbar_card] using hcard_gt
    exact Finite.one_lt_card_iff_nontrivial.mp hcard_gt_bar
  have : Fact (IsPGroup p (R ⧸ E)) := ⟨(Fact.out : IsPGroup p R).to_quotient E⟩
  have hLbar_p : IsPGroup p Lbar := (Fact.out : IsPGroup p (R ⧸ E)).to_subgroup Lbar
  obtain ⟨k, hk_pos, hLbar_card_pow⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := Lbar) hLbar_p).mp hLbar_nontriv
  obtain ⟨Kbar, hKbar_norm, hKbar_le, hKbar_card⟩ :=
    lemma_1_22 (G := R ⧸ E) p Lbar hLbar_normal k hLbar_card_pow 1
      (Nat.succ_le_of_lt hk_pos)
  obtain ⟨B, hE_le_B, hB_norm, hquot_card, hB_map⟩ :=
    lift_order_p_quotient_subgroup_to_normal_prime_index_overgroup
      (R := R) (p := p) (E := E) hEnorm hKbar_norm
      (by simpa [pow_one] using hKbar_card)
  have hB_le_L : B ≤ L := by
    intro b hb
    have hq_mem : q b ∈ Kbar := by
      rw [← hB_map]
      exact Subgroup.mem_map_of_mem q hb
    have hq_L : q b ∈ L.map q := hKbar_le hq_mem
    rcases Subgroup.mem_map.mp hq_L with ⟨l, hlL, hl_eq⟩
    have hblE : b * l⁻¹ ∈ E := by
      have hquot : q (b * l⁻¹) = 1 := by
        calc
          q (b * l⁻¹) = q b * (q l)⁻¹ := by simp
          _ = 1 := by simp [hl_eq]
      exact (QuotientGroup.eq_one_iff (N := E) (x := b * l⁻¹)).1 hquot
    have hblL : b * l⁻¹ ∈ L := hE_le_L hblE
    have hb_eq : b = (b * l⁻¹) * l := by simp [mul_assoc]
    rw [hb_eq]
    exact L.mul_mem hblL hlL
  have hB_comm : IsMulCommutative B :=
    isMulCommutative_of_contains_normal_subgroup_le_centralizer_and_prime_quotient
      (R := R) (p := p) (E := E) (B := B) hEnorm
      (hB_le_L.trans hL_le_cent) hquot_card
  exact ⟨B, hE_le_B, hB_norm, hB_comm, hquot_card, hB_le_L⟩


public theorem CFSG.natCard_abelian_subgroup_le_p_sq_of_rank_le_two_and_exponent_dvd_p
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    {A : Subgroup R} (hAq : IsPGroup p A) (hAcomm : IsMulCommutative A)
    (hAle : generatorRank A ≤ 2) (hexp : Monoid.exponent A ∣ p) :
    Nat.card A ≤ p ^ 2 := by
  let : IsMulCommutative A := hAcomm
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hpow : ∀ a : A, a ^ p = 1 := by
    intro a
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp a
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A :=
    card_dvd_exponent_pow_rank' (G := A) (n := p) hpow
  have hGrank_le : Group.rank A ≤ generatorRank A :=
    groupRank_le_generatorRank_finite (G := A)
  have hGrank_le_two : Group.rank A ≤ 2 := hGrank_le.trans hAle
  have hpow_dvd : p ^ Group.rank A ∣ p ^ 2 :=
    (Nat.pow_dvd_pow_iff_le_right ((Fact.out : Nat.Prime p).one_lt)).2 hGrank_le_two
  have hcard_dvd_sq : Nat.card A ∣ p ^ 2 := dvd_trans hcard_dvd hpow_dvd
  obtain ⟨n, hn⟩ := hAq.exists_card_eq
  rw [hn]
  exact Nat.le_of_dvd (pow_pos ((Fact.out : Nat.Prime p).pos) 2) <| by
    simpa [hn] using hcard_dvd_sq


set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p A] {P : Subgroup (MulAut A)} (hPp : IsPGroup p P)
    (hAcard : Nat.card A ≤ p ^ 2) :
    Nat.card P ≤ p := by
  let hp_prime : Nat.Prime p := Fact.out
  let Q := Additive A
  let : AddCommGroup Q := Additive.addCommGroup
  let : Module (ZMod p) Q := inferInstance
  let : Finite Q := inferInstance
  let : FiniteDimensional (ZMod p) Q := Module.Finite.of_finite
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have hcardQ : Nat.card A = p ^ Module.finrank (ZMod p) Q := by
    calc
      Nat.card A = Nat.card Q := Nat.card_congr Additive.ofMul
      _ = p ^ Module.finrank (ZMod p) Q :=
        by simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q))
  have hdim_le_two : Module.finrank (ZMod p) Q ≤ 2 := by
    have hpow_le : p ^ Module.finrank (ZMod p) Q ≤ p ^ 2 := by
      simpa [hcardQ] using hAcard
    exact (Nat.pow_le_pow_iff_right hp_one_lt).1 hpow_le
  let ψfun : P → LinearMap.GeneralLinearGroup (ZMod p) Q := fun a =>
    let eAdd : Q ≃+ Q := MulEquiv.toAdditive (a : MulAut A)
    let eLin : Q ≃ₗ[ZMod p] Q :=
      eAdd.toLinearEquiv (fun c x => by
        simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
    LinearMap.GeneralLinearGroup.ofLinearEquiv eLin
  let ψ : P →* LinearMap.GeneralLinearGroup (ZMod p) Q := {
    toFun := ψfun
    map_one' := by
      ext x
      rfl
    map_mul' := by
      intro a b
      ext x
      rfl
  }
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    ext x
    have hx :=
      congrArg
        (fun f : LinearMap.GeneralLinearGroup (ZMod p) Q => (f : Q → Q) (Additive.ofMul x))
        hab
    simpa [ψ, ψfun, Q] using hx
  let n := Module.finrank (ZMod p) Q
  let b : Module.Basis (Fin n) (ZMod p) Q := Module.finBasis (ZMod p) Q
  let χ : P →* GL (Fin n) (ZMod p) := ((Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom).comp ψ
  have hχ_inj : Function.Injective χ := by
    exact (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hψ_inj
  have hcard_dvd_GL : Nat.card P ∣ Nat.card (GL (Fin n) (ZMod p)) :=
    Subgroup.card_dvd_of_injective χ hχ_inj
  have hp_not_dvd_pred : ¬ p ∣ p - 1 := by
    intro h
    have hdiv1 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) h
    have hsub : p - (p - 1) = 1 := by
      have hp_eq : p = (p - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hp_prime.pos).symm
      rw [hp_eq]
      exact Nat.add_sub_cancel_left (p - 1) 1
    rw [hsub] at hdiv1
    exact hp_prime.not_dvd_one hdiv1
  have hp_not_dvd_sq_sub_one : ¬ p ∣ p ^ 2 - 1 := by
    intro h
    have hp_dvd_sq : p ∣ p ^ 2 := by
      simp [pow_two]
    have hdiv1 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub hp_dvd_sq h
    have hsub : p ^ 2 - (p ^ 2 - 1) = 1 := by
      have hp2_eq : p ^ 2 = (p ^ 2 - 1) + 1 := by
        simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos (pow_pos hp_prime.pos 2)).symm
      rw [hp2_eq]
      exact Nat.add_sub_cancel_left (p ^ 2 - 1) 1
    rw [hsub] at hdiv1
    exact hp_prime.not_dvd_one hdiv1
  have hp_sq_not_dvd_GL : ¬ p ^ 2 ∣ Nat.card (GL (Fin n) (ZMod p)) := by
    have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hn_cases with hn | hn | hn
    · intro hdiv
      have hcard_GL0 : Nat.card (GL (Fin 0) (ZMod p)) = 1 := by
        simp
      rw [hn] at hdiv
      rw [hcard_GL0] at hdiv
      have hp_dvd_one : p ∣ 1 := dvd_trans (by simp [pow_two]) hdiv
      exact hp_prime.not_dvd_one hp_dvd_one
    · intro hdiv
      have hcard_GL1 : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
        simpa [pow_one] using (Matrix.card_GL_field (𝔽 := ZMod p) 1)
      rw [hn] at hdiv
      rw [hcard_GL1] at hdiv
      have hp_dvd_pred : p ∣ p - 1 := dvd_trans (by simp [pow_two]) hdiv
      exact hp_not_dvd_pred hp_dvd_pred
    · intro hdiv
      have hcard_GL2 : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
        simpa [Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := ZMod p) 2)
      rw [hn] at hdiv
      rw [hcard_GL2] at hdiv
      have hsq_sub : p ^ 2 - p = p * (p - 1) := by
        calc
          p ^ 2 - p = p * p - p * 1 := by rw [pow_two, Nat.mul_one]
          _ = p * (p - 1) := by rw [Nat.mul_sub_left_distrib]
      have hrewrite : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
        calc
          (p ^ 2 - 1) * (p ^ 2 - p) = (p ^ 2 - 1) * (p * (p - 1)) := by rw [hsq_sub]
          _ = ((p ^ 2 - 1) * p) * (p - 1) := by rw [Nat.mul_assoc]
          _ = (p * (p ^ 2 - 1)) * (p - 1) := by rw [Nat.mul_comm (p ^ 2 - 1) p]
          _ = p * ((p ^ 2 - 1) * (p - 1)) := by rw [← Nat.mul_assoc]
      have hdiv' : p * p ∣ p * ((p ^ 2 - 1) * (p - 1)) := by
        rw [pow_two] at hdiv ⊢
        convert hdiv using 1
        simpa [pow_two] using hrewrite.symm
      have hcancel : p ∣ (p ^ 2 - 1) * (p - 1) :=
        Nat.dvd_of_mul_dvd_mul_left hp_prime.pos hdiv'
      exact (hp_prime.dvd_mul.mp hcancel).elim hp_not_dvd_sq_sub_one hp_not_dvd_pred
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have hm_le_one : m ≤ 1 := by
    by_contra hm_gt
    have htwo_le_m : 2 ≤ m := by omega
    have hp_sq_dvd_cardP : p ^ 2 ∣ Nat.card P := by
      rw [hm]
      exact (Nat.pow_dvd_pow_iff_le_right hp_one_lt).2 htwo_le_m
    exact hp_sq_not_dvd_GL (dvd_trans hp_sq_dvd_cardP hcard_dvd_GL)
  calc
    Nat.card P = p ^ m := hm
    _ ≤ p ^ 1 := (Nat.pow_le_pow_iff_right hp_one_lt).2 hm_le_one
    _ = p := by simp

set_option backward.isDefEq.respectTransparency false in
private theorem CFSG.prime_dvd_natCard_mulAut_of_elementaryAbelian_card_le_p_sq
    {A : Type*} [Group A] [Finite A] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsElementaryAbelian p A] (hAcard : Nat.card A ≤ p ^ 2)
    (hqAut : q ∣ Nat.card (MulAut A)) (hq_ne : q ≠ p) :
    q ∣ p ^ 2 - 1 := by
  let hp_prime : Nat.Prime p := Fact.out
  let hq_prime : Nat.Prime q := Fact.out
  let Q := Additive A
  let : AddCommGroup Q := Additive.addCommGroup
  let : Module (ZMod p) Q := inferInstance
  let : Finite Q := inferInstance
  let : FiniteDimensional (ZMod p) Q := Module.Finite.of_finite
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have hcardQ : Nat.card A = p ^ Module.finrank (ZMod p) Q := by
    calc
      Nat.card A = Nat.card Q := Nat.card_congr Additive.ofMul
      _ = p ^ Module.finrank (ZMod p) Q :=
        by simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Q))
  have hdim_le_two : Module.finrank (ZMod p) Q ≤ 2 := by
    have hpow_le : p ^ Module.finrank (ZMod p) Q ≤ p ^ 2 := by
      simpa [hcardQ] using hAcard
    exact (Nat.pow_le_pow_iff_right hp_one_lt).1 hpow_le
  let ψfun : MulAut A → LinearMap.GeneralLinearGroup (ZMod p) Q := fun a =>
    let eAdd : Q ≃+ Q := MulEquiv.toAdditive a
    let eLin : Q ≃ₗ[ZMod p] Q :=
      eAdd.toLinearEquiv (fun c x => by
        simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
    LinearMap.GeneralLinearGroup.ofLinearEquiv eLin
  let ψ : MulAut A →* LinearMap.GeneralLinearGroup (ZMod p) Q := {
    toFun := ψfun
    map_one' := by
      ext x
      rfl
    map_mul' := by
      intro a b
      ext x
      rfl
  }
  have hψ_inj : Function.Injective ψ := by
    intro a b hab
    ext x
    have hx :=
      congrArg
        (fun f : LinearMap.GeneralLinearGroup (ZMod p) Q => (f : Q → Q) (Additive.ofMul x))
        hab
    simpa [ψ, ψfun, Q] using hx
  let n := Module.finrank (ZMod p) Q
  let b : Module.Basis (Fin n) (ZMod p) Q := Module.finBasis (ZMod p) Q
  let χ : MulAut A →* GL (Fin n) (ZMod p) :=
    ((Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom).comp ψ
  have hχ_inj : Function.Injective χ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hψ_inj
  have hcard_dvd_GL : Nat.card (MulAut A) ∣ Nat.card (GL (Fin n) (ZMod p)) :=
    Subgroup.card_dvd_of_injective χ hχ_inj
  have hq_dvd_GL : q ∣ Nat.card (GL (Fin n) (ZMod p)) :=
    hqAut.trans hcard_dvd_GL
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    simpa [pow_two, Nat.mul_comm] using (Nat.pow_two_sub_pow_two p 1)
  rcases hn_cases with hn | hn | hn
  · have hq_dvd_GL0 := hq_dvd_GL
    rw [hn] at hq_dvd_GL0
    have hcard_GL0 : Nat.card (GL (Fin 0) (ZMod p)) = 1 := by
      simp
    have hq_one : q ∣ 1 := by
      rw [hcard_GL0] at hq_dvd_GL0
      exact hq_dvd_GL0
    exact False.elim (hq_prime.not_dvd_one hq_one)
  · have hq_dvd_GL1 := hq_dvd_GL
    rw [hn] at hq_dvd_GL1
    have hcard_GL1 : Nat.card (GL (Fin 1) (ZMod p)) = p - 1 := by
      simpa [pow_one] using (Matrix.card_GL_field (𝔽 := ZMod p) 1)
    have hq_pred : q ∣ p - 1 := by
      rw [hcard_GL1] at hq_dvd_GL1
      exact hq_dvd_GL1
    simpa [hsq] using dvd_mul_of_dvd_left hq_pred (p + 1)
  · have hq_dvd_GL2 := hq_dvd_GL
    rw [hn] at hq_dvd_GL2
    have hcard_GL2 : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
      simpa [Fin.prod_univ_two] using (Matrix.card_GL_field (𝔽 := ZMod p) 2)
    have hsq_sub : p ^ 2 - p = p * (p - 1) := by
      calc
        p ^ 2 - p = p * p - p * 1 := by rw [pow_two, Nat.mul_one]
        _ = p * (p - 1) := by rw [Nat.mul_sub_left_distrib]
    have hrewrite : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
      calc
        (p ^ 2 - 1) * (p ^ 2 - p) = (p ^ 2 - 1) * (p * (p - 1)) := by
          rw [hsq_sub]
        _ = ((p ^ 2 - 1) * p) * (p - 1) := by rw [Nat.mul_assoc]
        _ = (p * (p ^ 2 - 1)) * (p - 1) := by rw [Nat.mul_comm (p ^ 2 - 1) p]
        _ = p * ((p ^ 2 - 1) * (p - 1)) := by rw [← Nat.mul_assoc]
    have hq_dvd_rewrite : q ∣ p * ((p ^ 2 - 1) * (p - 1)) := by
      rw [hcard_GL2, hrewrite] at hq_dvd_GL2
      exact hq_dvd_GL2
    rcases hq_prime.dvd_mul.mp hq_dvd_rewrite with hq_p | hq_rest
    · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).1 hq_p
      exact False.elim (hq_ne hqp)
    · rcases hq_prime.dvd_mul.mp hq_rest with hq_sq | hq_pred
      · exact hq_sq
      · simpa [hsq] using dvd_mul_of_dvd_left hq_pred (p + 1)

private theorem CFSG.prime_order_mulAut_dvd_of_elementaryAbelian_card_le_p_sq
    {A : Type*} [Group A] [Finite A] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsElementaryAbelian p A] (hAcard : Nat.card A ≤ p ^ 2)
    (ψ : MulAut A) (hψ_order : orderOf ψ = q) (hq_ne : q ≠ p) :
    q ∣ p ^ 2 - 1 := by
  have hqAut : q ∣ Nat.card (MulAut A) := by
    rw [← hψ_order]
    exact orderOf_dvd_natCard ψ
  exact prime_dvd_natCard_mulAut_of_elementaryAbelian_card_le_p_sq
    (A := A) (p := p) (q := q) hAcard hqAut hq_ne

private theorem CFSG.prime_lt_of_dvd_odd_prime_sq_sub_one
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpodd : p ≠ 2) (_hq_ne : q ≠ p) (hdvd : q ∣ p ^ 2 - 1) :
    q < p := by
  have hfac : q ∣ (p - 1) * (p + 1) := by
    have hsq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      simpa [pow_two, Nat.mul_comm] using (Nat.pow_two_sub_pow_two p 1)
    simpa [hsq] using hdvd
  rcases (Fact.out : Nat.Prime q).dvd_mul.mp hfac with hq_pminus | hq_pplus
  · have hpos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hq_le_pred : q ≤ p - 1 := Nat.le_of_dvd hpos hq_pminus
    omega
  · by_cases hqtwo : q = 2
    · subst hqtwo
      have hp_two_lt : 2 < p := by
        have hp_two_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
        omega
      simpa using hp_two_lt
    · have hq_odd : Odd q := (Fact.out : Nat.Prime q).odd_of_ne_two hqtwo
      have hp_odd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hpodd
      have h_even : 2 ∣ p + 1 := by
        simpa [even_iff_two_dvd] using hp_odd.add_one
      have hq_coprime_two : Nat.Coprime q 2 := hq_odd.coprime_two_right
      have htwoq : 2 * q ∣ p + 1 :=
        hq_coprime_two.symm.mul_dvd_of_dvd_of_dvd h_even hq_pplus
      have hle : 2 * q ≤ p + 1 := Nat.le_of_dvd (Nat.succ_pos p) htwoq
      have hq_two_le : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
      omega


set_option maxHeartbeats 800000 in
private theorem CFSG.elementaryAbelian_card_ge_pow_generatorRank_local
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    p ^ generatorRank G ≤ Nat.card G := by
  have hcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    calc
      Nat.card G = Nat.card (Additive G) := Nat.card_congr Additive.ofMul
      _ = p ^ Module.finrank (ZMod p) (Additive G) :=
        by simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G))
  have hgr_le_finrank : generatorRank G ≤ Module.finrank (ZMod p) (Additive G) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) G
  rw [hcard]
  exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hgr_le_finrank


private theorem CFSG.omega₁_isElementaryAbelian_of_commutative_local
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [IsMulCommutative G] :
    IsElementaryAbelian p (omega₁ (G := G) (p := p)) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact
    Subgroup.closure_induction (k := {y : G | y ^ (p ^ 1) = 1})
      (p := fun z _hz => z ^ p = 1) (x := x) (by
        intro y hy
        simpa [pow_one] using hy) (by simp) (by
        intro y z _ _ hy hz
        calc
          (y * z) ^ p = y ^ p * z ^ p := by
            simpa using mul_pow y z p
          _ = 1 := by simp [hy, hz]) (by
        intro y _ hy
        simp [hy]) x.property

private theorem CFSG.omega₁_card_eq_card_quotient_frattini_of_commutative_local
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)] :
    Nat.card (omega₁ (G := G) (p := p)) = Nat.card (G ⧸ frattini G) := by
  classical
  let : CommGroup G := IsMulCommutative.instCommGroup
  let φ : G →* G := powMonoidHom p
  have hφker : φ.ker = omega₁ (G := G) (p := p) := by
    ext x
    constructor
    · intro hx
      change x ∈ Subgroup.closure {y : G | y ^ (p ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [φ, pow_one] using hx
    · intro hx
      refine
        Subgroup.closure_induction (k := {y : G | y ^ (p ^ 1) = 1})
          (p := fun z _hz => z ∈ φ.ker) (x := x) (by
            intro y hy
            simpa [φ, pow_one] using hy) (by simp [φ]) (by
            intro y z _ _ hy hz
            have hy' : y ^ p = 1 := by simpa [φ] using hy
            have hz' : z ^ p = 1 := by simpa [φ] using hz
            simp [φ, mul_pow, hy', hz']) (by
            intro y _ hy
            exact φ.ker.inv_mem hy) hx
  have hφrange : φ.range = frattini G := by
    have hcomm_top :
        (⊤ : Subgroup G) ≤ Subgroup.centralizer (((⊤ : Subgroup G) : Set G)) := by
      intro x _hx
      rw [Subgroup.mem_centralizer_iff]
      intro y _hy
      exact mul_comm y x
    have hcomm_bot : _root_.commutator G = ⊥ := by
      have htop_comm_bot : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hcomm_top
      simpa [_root_.commutator_def] using htop_comm_bot
    have hderived_bot : derivedSubgroup G = ⊥ := by
      change _root_.commutator G = ⊥
      exact hcomm_bot
    have hrange :
        Set.range (fun x : G => x ^ p) = ((φ.range : Subgroup G) : Set G) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, by simp [φ]⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, by simpa [φ] using hx⟩
    have hfrattini : frattini G = φ.range := by
      calc
        frattini G =
            Subgroup.closure ((derivedSubgroup G : Set G) ∪ Set.range (fun x : G => x ^ p)) := by
              simpa using (lemma_1_7_d (R := G) (p := p))
        _ = Subgroup.closure (Set.range (fun x : G => x ^ p)) := by
              rw [hderived_bot]
              simp
        _ = Subgroup.closure ((φ.range : Subgroup G) : Set G) := by rw [hrange]
        _ = φ.range := by simpa using (Subgroup.closure_eq (K := φ.range))
    exact hfrattini.symm
  have hcard_range :
      Nat.card (G ⧸ φ.ker) = Nat.card φ.range := by
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hmul_ker :
      Nat.card G = Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) := by
    calc
      Nat.card G = Nat.card (G ⧸ φ.ker) * Nat.card φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
      _ = Nat.card φ.range * Nat.card φ.ker := by rw [hcard_range]
      _ = Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) := by
        rw [hφrange, hφker]
  have hmul_frattini :
      Nat.card G = Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
    calc
      Nat.card G = Nat.card (G ⧸ frattini G) * Nat.card (frattini G) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (s := frattini G)
      _ = Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
        rw [Nat.mul_comm]
  have hΦpos : 0 < Nat.card (frattini G) := by
    exact Nat.card_pos (α := frattini G)
  have hmul_eq :
      Nat.card (frattini G) * Nat.card (omega₁ (G := G) (p := p)) =
        Nat.card (frattini G) * Nat.card (G ⧸ frattini G) := by
    exact hmul_ker.symm.trans hmul_frattini
  exact Nat.eq_of_mul_eq_mul_left hΦpos hmul_eq

private theorem CFSG.elementaryAbelian_finrank_le_generatorRank_local
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    Module.finrank (ZMod p) (Additive G) ≤ generatorRank G := by
  classical
  let n := generatorRank G
  have hnonempty :
      {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤}.Nonempty := by
    refine ⟨Nat.card G, ?_⟩
    let : Fintype G := Fintype.ofFinite G
    let e : Fin (Nat.card G) ≃ G :=
      (finCongr (Nat.card_eq_fintype_card (α := G))).trans (Fintype.equivFin G).symm
    refine ⟨fun i => e i, ?_⟩
    apply (Subgroup.eq_top_iff'
      (H := Subgroup.closure (Set.range fun i : Fin (Nat.card G) => e i))).2
    intro x
    exact Subgroup.subset_closure ⟨e.symm x, by simp [e]⟩
  have hn_mem :
      n ∈ {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤} := by
    simpa [n, generatorRank] using (Nat.sInf_mem hnonempty)
  rcases hn_mem with ⟨t, ht_top⟩
  let sAdd : Fin n → Additive G := fun i => Additive.ofMul (t i)
  have hadd_top : AddSubgroup.closure (Set.range sAdd) = ⊤ := by
    have hpre : Additive.ofMul ⁻¹' Set.range sAdd = Set.range t := by
      ext g
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, Additive.ofMul.injective hi⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    have htoSub_top :
        (AddSubgroup.closure (Set.range sAdd)).toSubgroup' = (⊤ : Subgroup G) := by
      calc
        (AddSubgroup.closure (Set.range sAdd)).toSubgroup' =
            Subgroup.closure (Additive.ofMul ⁻¹' Set.range sAdd) := by
              simpa using AddSubgroup.toSubgroup'_closure (Set.range sAdd)
        _ = Subgroup.closure (Set.range t) := by rw [hpre]
        _ = ⊤ := ht_top
    apply eq_top_iff.2
    intro a _ha
    have hmul : Additive.toMul a ∈ (AddSubgroup.closure (Set.range sAdd)).toSubgroup' := by
      simp [htoSub_top]
    simpa using hmul
  have hint_span_top :
      Submodule.span ℤ (Set.range sAdd) = (⊤ : Submodule ℤ (Additive G)) := by
    rw [← Submodule.toAddSubgroup_eq_top]
    simpa [Submodule.span_int_eq_addSubgroupClosure] using hadd_top
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    simpa using (ZMod.intCast_surjective (n := p))
  have hrestrict_top :
      (Submodule.span (ZMod p) (Set.range sAdd)).restrictScalars ℤ =
        (⊤ : Submodule ℤ (Additive G)) := by
    calc
      (Submodule.span (ZMod p) (Set.range sAdd)).restrictScalars ℤ =
          Submodule.span ℤ (Set.range sAdd) := by
            simpa using
              (Submodule.restrictScalars_span (R := ℤ) (A := ZMod p) hsurj
                (Set.range sAdd))
      _ = ⊤ := hint_span_top
  have hspan_top :
      Submodule.span (ZMod p) (Set.range sAdd) = (⊤ : Submodule (ZMod p) (Additive G)) := by
    exact (Submodule.restrictScalars_eq_top_iff ℤ (ZMod p) (Additive G)).1 hrestrict_top
  simpa [n] using
    (finrank_le_of_span_eq_top (R := ZMod p) (M := Additive G) (v := sAdd) hspan_top)

private theorem CFSG.elementaryAbelian_card_eq_pow_generatorRank_local
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    Nat.card G = p ^ generatorRank G := by
  have hcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    calc
      Nat.card G = Nat.card (Additive G) := Nat.card_congr Additive.ofMul
      _ = p ^ Module.finrank (ZMod p) (Additive G) :=
        by simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G))
  have hfin_le_gen :
      Module.finrank (ZMod p) (Additive G) ≤ generatorRank G :=
    elementaryAbelian_finrank_le_generatorRank_local (p := p) G
  have hgen_le_fin :
      generatorRank G ≤ Module.finrank (ZMod p) (Additive G) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) G
  have hfin_eq : Module.finrank (ZMod p) (Additive G) = generatorRank G :=
    le_antisymm hfin_le_gen hgen_le_fin
  simpa [hfin_eq] using hcard

public theorem CFSG.omega₁_card_eq_pow_generatorRank_of_commutative_pgroup
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G] [Fact (IsPGroup p G)] :
    Nat.card (omega₁ (G := G) (p := p)) = p ^ generatorRank G := by
  let Q : Type _ := G ⧸ frattini G
  have hΩquot :
      Nat.card (omega₁ (G := G) (p := p)) = Nat.card Q := by
    simpa [Q] using omega₁_card_eq_card_quotient_frattini_of_commutative_local (p := p) G
  have hQelem : IsElementaryAbelian p Q :=
    isElementaryAbelian_quotient_frattini (R := G) (p := p)
  let : IsElementaryAbelian p Q := hQelem
  have hQcard : Nat.card Q = p ^ generatorRank Q :=
    elementaryAbelian_card_eq_pow_generatorRank_local (p := p) Q
  have hQ_le_G : generatorRank Q ≤ generatorRank G :=
    generatorRank_le_of_surjective
      (G := G) (H := Q) (QuotientGroup.mk' (frattini G))
      (QuotientGroup.mk'_surjective (frattini G))
  have hG_le_Q : generatorRank G ≤ generatorRank Q :=
    generatorRank_le_generatorRank_quotient_frattini (p := p) G
  have hgen_eq : generatorRank Q = generatorRank G :=
    le_antisymm hQ_le_G hG_le_Q
  calc
    Nat.card (omega₁ (G := G) (p := p)) = Nat.card Q := hΩquot
    _ = p ^ generatorRank Q := hQcard
    _ = p ^ generatorRank G := by rw [hgen_eq]

private theorem CFSG.generatorRank_le_of_le_commutative_pgroup_local
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)]
    {H K : Subgroup R} (hHcomm : IsMulCommutative H) (hKcomm : IsMulCommutative K)
    (hHK : H ≤ K) :
    generatorRank H ≤ generatorRank K := by
  have : Fact (IsPGroup p H) := ⟨(Fact.out : IsPGroup p R).to_subgroup H⟩
  have : Fact (IsPGroup p K) := ⟨(Fact.out : IsPGroup p R).to_subgroup K⟩
  have hΩHcard :
      Nat.card (omega₁ (G := H) (p := p)) = p ^ generatorRank H := by
    exact omega₁_card_eq_pow_generatorRank_of_commutative_pgroup
      (p := p) H
  have hΩKcard :
      Nat.card (omega₁ (G := K) (p := p)) = p ^ generatorRank K := by
    exact omega₁_card_eq_pow_generatorRank_of_commutative_pgroup
      (p := p) K
  have hmap_le :
      (omega₁ (G := H) (p := p)).map H.subtype ≤
        (omega₁ (G := K) (p := p)).map K.subtype :=
    by
      rw [omega₁, omega, MonoidHom.map_closure]
      refine (Subgroup.closure_le
        (K := (omega₁ (G := K) (p := p)).map K.subtype)).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      let xK : K := ⟨(x : R), hHK x.2⟩
      have hxG : (x : R) ^ p = 1 := by
        simpa using congrArg H.subtype hx
      have hxΩK : xK ∈ omega₁ (G := K) (p := p) := by
        change xK ∈ Subgroup.closure {y : K | y ^ (p ^ 1) = 1}
        exact Subgroup.subset_closure (by simpa [xK, pow_one] using hxG)
      exact Subgroup.mem_map_of_mem K.subtype hxΩK
  have hcard_le :
      Nat.card (omega₁ (G := H) (p := p)) ≤ Nat.card (omega₁ (G := K) (p := p)) := by
    calc
      Nat.card (omega₁ (G := H) (p := p)) =
          Nat.card ((omega₁ (G := H) (p := p)).map H.subtype) := by
            exact (Subgroup.card_map_of_injective
              (K := omega₁ (G := H) (p := p)) (f := H.subtype)
              H.subtype_injective).symm
      _ ≤ Nat.card ((omega₁ (G := K) (p := p)).map K.subtype) :=
            Subgroup.card_le_of_le hmap_le
      _ = Nat.card (omega₁ (G := K) (p := p)) := by
            exact Subgroup.card_map_of_injective
              (K := omega₁ (G := K) (p := p)) (f := K.subtype)
              K.subtype_injective
  have hpow_le : p ^ generatorRank H ≤ p ^ generatorRank K := by
    simpa [hΩHcard, hΩKcard] using hcard_le
  exact (Nat.pow_le_pow_iff_right (Fact.out : Nat.Prime p).one_lt).1 hpow_le

public theorem CFSG.groupRank_le_generatorRank_of_commutative_pgroup
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hRcomm : IsMulCommutative R) :
    groupRank R ≤ generatorRank R := by
  classical
  have : Fact (IsPGroup p R) := ⟨hRp⟩
  rw [groupRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, p, Fact.out, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨q, hq, hnq⟩
    rw [primeRank] at hnq
    refine hnq.trans ?_
    refine csSup_le ?_ ?_
    · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := R), inferInstance, Nat.zero_le _⟩
    · intro m hm
      rcases hm with ⟨A, _hAq, hAcomm, hmA⟩
      have htop_comm : IsMulCommutative (⊤ : Subgroup R) := by
        let : IsMulCommutative R := hRcomm
        infer_instance
      have hgen_A_le_top : generatorRank A ≤ generatorRank (⊤ : Subgroup R) :=
        generatorRank_le_of_le_commutative_pgroup_local
          (R := R) (p := p) (H := A) (K := ⊤) hAcomm htop_comm le_top
      have hgen_top_le_R : generatorRank (⊤ : Subgroup R) ≤ generatorRank R :=
        generatorRank_le_of_equiv (G := R) (H := (⊤ : Subgroup R)) Subgroup.topEquiv.symm
      exact hmA.trans (hgen_A_le_top.trans hgen_top_le_R)


public theorem CFSG.isElementaryAbelian_zpowers_of_pow_eq_one_local
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] {x : G} (hxpow : x ^ p = 1) :
    IsElementaryAbelian p (Subgroup.zpowers x) := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro y
  apply Subtype.ext
  have hy_dvd : orderOf ((y : Subgroup.zpowers x) : G) ∣ p := by
    exact (orderOf_dvd_of_mem_zpowers y.2).trans (orderOf_dvd_of_pow_eq_one hxpow)
  simpa using (orderOf_dvd_iff_pow_eq_one.mp hy_dvd)

public theorem CFSG.isElementaryAbelian_sup_of_le_centralizer_local
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    {E C : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p C]
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ C) := by
  classical
  let s : Set G := (E : Set G) ∪ (C : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxC
    · rcases hy with hyE | hyC
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hCE hyC)) x hxE
    · rcases hy with hyE | hyC
      · exact ((Subgroup.mem_centralizer_iff.mp (hCE hxC)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := C)).comm ⟨x, hxC⟩ ⟨y, hyC⟩)
  have hsup : E ⊔ C = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E C)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyC
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyC⟩ : C) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p C) ⟨y, hyC⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          let : IsMulCommutative (Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_s x hx y hy)
          let : CommGroup (Subgroup.closure s) := IsMulCommutative.instCommGroup
          show y * z = z * y
          simpa using congrArg Subtype.val
            (mul_comm (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

private theorem CFSG.isElementaryAbelian_map_of_injective_local
    {p : ℕ} [Fact p.Prime]
    {G H : Type*} [Group G] [Group H] {K : Subgroup G}
    [IsElementaryAbelian p K] (f : G →* H) (_hf : Function.Injective f) :
    IsElementaryAbelian p (K.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := K))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyK, hyx⟩
  let yK : K := ⟨y, hyK⟩
  have hypow : yK ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p K) yK
  change (x : H) ^ p = 1
  calc
    (x : H) ^ p = f y ^ p := by rw [hyx]
    _ = f (y ^ p) := by simp
    _ = 1 := by
      have hy_one : y ^ p = 1 := by
        simpa [yK] using congrArg Subtype.val hypow
      simp [hy_one]

private theorem CFSG.mem_omega₁_map_subtype_of_mem_pow_eq_one
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {x : G}
    (hxA : x ∈ A) (hxpow : x ^ p = 1) :
    x ∈ (omega₁ (G := A) (p := p)).map A.subtype := by
  let xA : A := ⟨x, hxA⟩
  have hxA_omega : xA ∈ omega₁ (G := A) (p := p) := by
    change xA ∈ Subgroup.closure {y : A | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [xA, pow_one] using hxpow
  exact Subgroup.mem_map_of_mem A.subtype hxA_omega

private theorem CFSG.mem_omega₁_centralizer_map_of_mem_pow_eq_one
    {G : Type*} [Group G] {p : ℕ} {Ω : Subgroup G} {x : G}
    (hxC : x ∈ Subgroup.centralizer (Ω : Set G)) (hxpow : x ^ p = 1) :
    x ∈
      (omega₁ (G := Subgroup.centralizer (Ω : Set G)) (p := p)).map
        (Subgroup.centralizer (Ω : Set G)).subtype := by
  let C : Subgroup G := Subgroup.centralizer (Ω : Set G)
  let xC : C := ⟨x, hxC⟩
  have hxCpow : xC ^ p = 1 := by
    apply Subtype.ext
    simpa [xC] using hxpow
  have hxCOmega : xC ∈ omega₁ (G := C) (p := p) := by
    change xC ∈ Subgroup.closure {y : C | y ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    simpa [pow_one] using hxCpow
  exact Subgroup.mem_map_of_mem C.subtype hxCOmega

private theorem CFSG.subgroup_le_omega₁_centralizer_map_of_isElementaryAbelian
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {Ω : Subgroup G}
    [IsElementaryAbelian p Ω] :
    Ω ≤
      (omega₁ (G := Subgroup.centralizer (Ω : Set G)) (p := p)).map
        (Subgroup.centralizer (Ω : Set G)).subtype := by
  intro x hxΩ
  have hxC : x ∈ Subgroup.centralizer (Ω : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact setLike_mul_comm (s := Ω) hy hxΩ
  have hxpow : x ^ p = 1 := by
    let xΩ : Ω := ⟨x, hxΩ⟩
    have hxΩpow : xΩ ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Ω) xΩ
    simpa [xΩ] using congrArg Subtype.val hxΩpow
  exact mem_omega₁_centralizer_map_of_mem_pow_eq_one (Ω := Ω) hxC hxpow

private theorem CFSG.omega₁_centralizer_map_normal_of_normal
    {G : Type*} [Group G] {p : ℕ} {Ω : Subgroup G} [Ω.Normal] :
    ((omega₁ (G := Subgroup.centralizer (Ω : Set G)) (p := p)).map
        (Subgroup.centralizer (Ω : Set G)).subtype).Normal := by
  let C : Subgroup G := Subgroup.centralizer (Ω : Set G)
  have hCnorm : C.Normal := by infer_instance
  let : C.Normal := hCnorm
  let ΩC : Subgroup C := omega₁ (G := C) (p := p)
  have hΩCchar : ΩC.Characteristic := by
    simpa [ΩC] using (omega₁_characteristic (G := C) (p := p))
  let : ΩC.Characteristic := hΩCchar
  simpa [C, ΩC] using (inferInstance : (ΩC.map C.subtype).Normal)

private theorem CFSG.exists_elementaryAbelian_subgroup_order_p_cubed_of_two_lt_groupRank
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hRp : IsPGroup p R) (hrank : 2 < groupRank R) :
    ∃ X : Subgroup R, Nat.card X = p ^ 3 ∧ IsElementaryAbelian p X := by
  classical
  obtain ⟨A, hAcomm, hArank⟩ :=
    exists_abelian_subgroup_three_le_generatorRank_of_two_lt_groupRank (R := R) hrank
  have hAp : IsPGroup p A := hRp.to_subgroup A
  let : Fact (IsPGroup p A) := ⟨hAp⟩
  let : IsMulCommutative A := hAcomm
  let ΩA : Subgroup A := omega₁ (G := A) (p := p)
  have hΩAelem : IsElementaryAbelian p ΩA :=
    omega₁_isElementaryAbelian_of_commutative_local (p := p) A
  let : IsElementaryAbelian p ΩA := hΩAelem
  have hΩAcard_eq :
      Nat.card ΩA = Nat.card (A ⧸ frattini A) :=
    omega₁_card_eq_card_quotient_frattini_of_commutative_local (p := p) A
  have hquot_rank : 3 ≤ generatorRank (A ⧸ frattini A) :=
    hArank.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A)
  have hquot_elem : IsElementaryAbelian p (A ⧸ frattini A) :=
    isElementaryAbelian_quotient_frattini (R := A) (p := p)
  have hpow_le_quot : p ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    let : IsElementaryAbelian p (A ⧸ frattini A) := hquot_elem
    calc
      p ^ 3 ≤ p ^ generatorRank (A ⧸ frattini A) :=
        Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquot_rank
      _ ≤ Nat.card (A ⧸ frattini A) :=
        elementaryAbelian_card_ge_pow_generatorRank_local (p := p) (A ⧸ frattini A)
  have hpow_le_ΩA : p ^ 3 ≤ Nat.card ΩA := by
    rw [hΩAcard_eq]
    exact hpow_le_quot
  have hΩAp : IsPGroup p ΩA := IsElementaryAbelian.isPGroup p ΩA
  rcases hΩAp.exists_card_eq with ⟨k, hk⟩
  have hk_three : 3 ≤ k := by
    rw [hk] at hpow_le_ΩA
    exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le_ΩA
  let : Fact (IsPGroup p ΩA) := ⟨hΩAp⟩
  have htop_card : Nat.card (⊤ : Subgroup ΩA) = p ^ k := by
    calc
      Nat.card (⊤ : Subgroup ΩA) = Nat.card ΩA :=
        Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ΩA) ≃* ΩA).toEquiv
      _ = p ^ k := hk
  obtain ⟨K, _hKnorm, hKle, hKcard⟩ :=
    lemma_1_22 (G := ΩA) p (⊤ : Subgroup ΩA) (by infer_instance) k htop_card 3 hk_three
  have hKelem : IsElementaryAbelian p K := by
    refine
      { toIsMulCommutative := by
          exact
            { is_comm := ⟨fun x y =>
                Subtype.ext <|
                  (IsMulCommutative.is_comm (M := ΩA)).comm (x : ΩA) (y : ΩA)⟩ }
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    let xΩ : ΩA := (x : K)
    have hxpow : xΩ ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p ΩA) xΩ
    simpa [xΩ] using hxpow
  let : IsElementaryAbelian p K := hKelem
  let KA : Subgroup A := K.map ΩA.subtype
  have hKAelem : IsElementaryAbelian p KA :=
    isElementaryAbelian_map_of_injective_local (p := p) ΩA.subtype ΩA.subtype_injective
  let : IsElementaryAbelian p KA := hKAelem
  let X : Subgroup R := KA.map A.subtype
  have hXelem : IsElementaryAbelian p X :=
    isElementaryAbelian_map_of_injective_local (p := p) A.subtype A.subtype_injective
  have hKAcard : Nat.card KA = p ^ 3 := by
    calc
      Nat.card KA = Nat.card K := by
        exact Subgroup.card_map_of_injective (K := K) (f := ΩA.subtype) ΩA.subtype_injective
      _ = p ^ 3 := hKcard
  have hXcard : Nat.card X = p ^ 3 := by
    calc
      Nat.card X = Nat.card KA := by
        exact Subgroup.card_map_of_injective (K := KA) (f := A.subtype) A.subtype_injective
      _ = p ^ 3 := hKAcard
  exact ⟨X, hXcard, hXelem⟩


public theorem CFSG.natCard_le_p_cubed_of_groupRank_le_two_and_exponent_p_local
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hrank : groupRank R ≤ 2) (hexp : Monoid.exponent R = p) :
    Nat.card R ≤ p ^ 3 := by
  classical
  obtain ⟨A, hAnorm, hAcomm, hAmax⟩ := exists_maximal_normal_abelian_subgroup_local' (G := R)
  let : A.Normal := hAnorm
  have hAcent_le : Subgroup.centralizer (A : Set R) ≤ A :=
    maximal_normal_abelian_selfCentralizing_local (G := R) (p := p) A hAnorm hAcomm hAmax
  have hA_le_cent : A ≤ Subgroup.centralizer (A : Set R) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  have hAself : Subgroup.centralizer (A : Set R) = A := le_antisymm hAcent_le hA_le_cent
  have hAq : IsPGroup p A := (Fact.out : IsPGroup p R).to_subgroup A
  have hArank : generatorRank A ≤ 2 :=
    (generatorRank_le_groupRank_of_isPGroup_abelian_subgroup (R := R) (q := p) hAq hAcomm).trans
      hrank
  have hAexp_dvd : Monoid.exponent A ∣ p := by
    rw [← Subgroup.exponent_toSubmonoid]
    exact (Monoid.exponent_submonoid_dvd A.toSubmonoid).trans (by simp [hexp])
  have hAcard : Nat.card A ≤ p ^ 2 :=
    natCard_abelian_subgroup_le_p_sq_of_rank_le_two_and_exponent_dvd_p
      (R := R) (p := p) hAq hAcomm hArank hAexp_dvd
  have hAelem : IsElementaryAbelian p A := {
    toIsMulCommutative := hAcomm
    exponent_dvd_p := hAexp_dvd
  }
  let : IsElementaryAbelian p A := hAelem
  let φ : R →* MulAut A := MulAut.conjNormal (H := A)
  have hker_eq_cent : φ.ker = Subgroup.centralizer (A : Set R) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx a ha
      have hx_apply : (φ x) ⟨a, ha⟩ = ⟨a, ha⟩ := by
        simp [hx]
      have hconj : x * a * x⁻¹ = a := by
        simpa [φ] using congrArg Subtype.val hx_apply
      have := congrArg (fun t : R => t * x) hconj
      simpa [mul_assoc] using this.symm
    · intro hx
      ext a
      have hcomm : (a : R) * x = x * a := hx a a.2
      have hconj : x * (a : R) * x⁻¹ = a := by
        calc
          x * (a : R) * x⁻¹ = ((a : R) * x) * x⁻¹ := by rw [hcomm]
          _ = a := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
  have hker_eq_A : φ.ker = A := by rw [hker_eq_cent, hAself]
  have hφ_range_p : IsPGroup p φ.range := by
    have hRtop : IsPGroup p (⊤ : Subgroup R) := by
      simpa using (Fact.out : IsPGroup p R).to_subgroup (⊤ : Subgroup R)
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup R)) hRtop φ
  have hquot_card : Nat.card (R ⧸ A) = Nat.card φ.range := by
    calc
      Nat.card (R ⧸ A) = Nat.card (R ⧸ φ.ker) := by rw [hker_eq_A]
      _ = Nat.card φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hφcard : Nat.card φ.range ≤ p :=
    natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
      (A := A) (p := p) hφ_range_p hAcard
  calc
    Nat.card R = Nat.card (R ⧸ A) * Nat.card A := by
      simpa [Nat.mul_comm] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := A))
    _ = Nat.card φ.range * Nat.card A := by rw [hquot_card]
    _ ≤ p * p ^ 2 := Nat.mul_le_mul hφcard hAcard
    _ = p ^ 3 := by
      simp [pow_succ, Nat.mul_comm]

public theorem CFSG.generatorRank_at_least_three_of_elementaryAbelian_card_p3_for_415
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 3) :
    3 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  rw [hA] at hcard_dvd
  have hle_rank : 3 ≤ Group.rank A := by
    exact (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_dvd
  simpa [generatorRank_eq_group_rank] using hle_rank

public theorem CFSG.natCard_frattini_quotient_le_p_sq_of_groupRank_le_two_and_exponent_p
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hrank : groupRank R ≤ 2) (hexp : Monoid.exponent R = p) :
    Nat.card (R ⧸ frattini R) ≤ p ^ 2 := by
  classical
  let Q : Type _ := R ⧸ frattini R
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hRcard_le : Nat.card R ≤ p ^ 3 :=
    natCard_le_p_cubed_of_groupRank_le_two_and_exponent_p_local
      (R := R) (p := p) hrank hexp
  have hQ_le_R : Nat.card Q ≤ Nat.card R := by
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := frattini R)
    calc
      Nat.card Q ≤ Nat.card Q * Nat.card (frattini R) :=
        Nat.le_mul_of_pos_right _ (Nat.card_pos (α := frattini R))
      _ = Nat.card R := by simpa [Q] using hmul.symm
  by_contra hnot
  have hQ_gt : p ^ 2 < Nat.card Q := Nat.lt_of_not_ge hnot
  have hQp : IsPGroup p Q := (Fact.out : IsPGroup p R).to_quotient (frattini R)
  obtain ⟨n, hnQ⟩ := hQp.exists_card_eq
  have hn_gt_two : 2 < n := by
    by_contra hnnot
    have hn_le_two : n ≤ 2 := le_of_not_gt hnnot
    have hQ_le_two : Nat.card Q ≤ p ^ 2 := by
      rw [hnQ]
      exact Nat.pow_le_pow_right hp_pos hn_le_two
    exact (not_le_of_gt hQ_gt) hQ_le_two
  have hn_le_three : n ≤ 3 := by
    have hpow_le : p ^ n ≤ p ^ 3 := by
      rw [← hnQ]
      exact hQ_le_R.trans hRcard_le
    exact (Nat.pow_le_pow_iff_right hp_one_lt).1 hpow_le
  have hn_eq_three : n = 3 := by omega
  have hQcard : Nat.card Q = p ^ 3 := by simp [hnQ, hn_eq_three]
  have hmul :
      Nat.card R = Nat.card Q * Nat.card (frattini R) := by
    simpa [Q] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := R) (s := frattini R))
  have hΦ_le_one : Nat.card (frattini R) ≤ 1 := by
    have hmul_le : p ^ 3 * Nat.card (frattini R) ≤ p ^ 3 * 1 := by
      simpa [hmul, hQcard] using hRcard_le
    exact Nat.le_of_mul_le_mul_left hmul_le (pow_pos hp_pos 3)
  have hΦ_card : Nat.card (frattini R) = 1 :=
    le_antisymm hΦ_le_one (Nat.succ_le_of_lt (Nat.card_pos (α := frattini R)))
  have hΦ_bot : frattini R = ⊥ := by
    apply eq_bot_iff.2
    intro x hx
    have hsub : Subsingleton (frattini R) := (Nat.card_eq_one_iff_unique.mp hΦ_card).1
    let : Subsingleton (frattini R) := hsub
    have hx_one : (⟨x, hx⟩ : frattini R) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val hx_one
  have hRelem : IsElementaryAbelian p R :=
    (frattini_eq_bot_iff_isElementaryAbelian (R := R) (p := p)).1 hΦ_bot
  have hRcard : Nat.card R = p ^ 3 := by
    have hmul' : Nat.card R = p ^ 3 * 1 := by simp [hmul, hQcard, hΦ_card]
    simpa using hmul'
  let : IsElementaryAbelian p R := hRelem
  have hgen_three : 3 ≤ generatorRank R :=
    generatorRank_at_least_three_of_elementaryAbelian_card_p3_for_415 (p := p) (A := R) hRcard
  have hgen_le_rank : generatorRank R ≤ groupRank R :=
    (generatorRank_le_primeRank_of_isPGroup (R := R) (p := p)
      (Fact.out : IsPGroup p R) hRelem.toIsMulCommutative).trans
      (primeRank_le_groupRank (R := R) (q := p) Fact.out)
  have hthree_rank : 3 ≤ groupRank R := hgen_three.trans hgen_le_rank
  exact (by decide : ¬ 3 ≤ (2 : ℕ)) (hthree_rank.trans hrank)

private theorem CFSG.mulAut_commute_of_trivial_on_subgroup_and_quotient
    {G : Type*} [Group G] {H : Subgroup G} (hHcomm : IsMulCommutative H)
    {φ ψ : MulAut G}
    (hφH : ∀ h : H, φ (h : G) = h)
    (hψH : ∀ h : H, ψ (h : G) = h)
    (hφquot : ∀ g : G, φ g * g⁻¹ ∈ H)
    (hψquot : ∀ g : G, ψ g * g⁻¹ ∈ H) :
    φ * ψ = ψ * φ := by
  ext g
  let y : H := ⟨φ g * g⁻¹, hφquot g⟩
  let z : H := ⟨ψ g * g⁻¹, hψquot g⟩
  have hφg : φ g = (y : G) * g := by
    simp [y, mul_assoc]
  have hψg : ψ g = (z : G) * g := by
    simp [z, mul_assoc]
  have hφz : φ (z : G) = z := hφH z
  have hψy : ψ (y : G) = y := hψH y
  have hyz : (y : G) * (z : G) = (z : G) * (y : G) := by
    simpa using congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := H)).comm y z)
  calc
    (φ * ψ) g = φ (ψ g) := rfl
    _ = φ ((z : G) * g) := by rw [hψg]
    _ = (z : G) * ((y : G) * g) := by simp [map_mul, hφz, hφg]
    _ = (y : G) * ((z : G) * g) := by
      calc
        (z : G) * ((y : G) * g) = ((z : G) * (y : G)) * g := by simp [mul_assoc]
        _ = ((y : G) * (z : G)) * g := by rw [← hyz]
        _ = (y : G) * ((z : G) * g) := by simp [mul_assoc]
    _ = ψ ((y : G) * g) := by simp [map_mul, hψy, hψg]
    _ = (ψ * φ) g := by rw [← hφg]; rfl


private theorem CFSG.conjNormal_ker_eq_centralizer_local
    {R : Type*} [Group R] {A : Subgroup R} [A.Normal] :
    (MulAut.conjNormal (H := A)).ker = Subgroup.centralizer (A : Set R) := by
  let φ : R →* MulAut A := MulAut.conjNormal (H := A)
  ext x
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
  constructor
  · intro hx a ha
    have hx_apply : φ x ⟨a, ha⟩ = ⟨a, ha⟩ := by
      change (MulAut.conjNormal (H := A) x) ⟨a, ha⟩ = ⟨a, ha⟩
      rw [hx]
      rfl
    have hconj : x * a * x⁻¹ = a := by
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hx_apply
    have := congrArg (fun t : R => t * x) hconj
    simpa [mul_assoc] using this.symm
  · intro hx
    ext a
    have hcomm : (a : R) * x = x * a := hx a a.2
    have hconj : x * (a : R) * x⁻¹ = a := by
      calc
        x * (a : R) * x⁻¹ = ((a : R) * x) * x⁻¹ := by rw [hcomm]
        _ = a := by simp [mul_assoc]
    simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj

private theorem CFSG.commutator_mem_centralizer_of_conjNormal_commute
    {R : Type*} [Group R] {A : Subgroup R} [A.Normal] {x y : R}
    (hxy :
      MulAut.conjNormal (H := A) x * MulAut.conjNormal (H := A) y =
        MulAut.conjNormal (H := A) y * MulAut.conjNormal (H := A) x) :
    ⁅x, y⁆ ∈ Subgroup.centralizer (A : Set R) := by
  let φ : R →* MulAut A := MulAut.conjNormal (H := A)
  have hcomm : Commute (φ x) (φ y) := hxy
  have hmap : φ ⁅x, y⁆ = 1 := by
    calc
      φ ⁅x, y⁆ = ⁅φ x, φ y⁆ := map_commutatorElement (f := φ) (g₁ := x) (g₂ := y)
      _ = 1 := commutatorElement_eq_one_iff_commute.mpr hcomm
  have hker : ⁅x, y⁆ ∈ φ.ker := by
    simpa [φ] using hmap
  simpa [φ, conjNormal_ker_eq_centralizer_local (A := A)] using hker

private theorem CFSG.commutator_mem_centralizer_of_stabilizes_omega_series
    {R : Type*} [Group R] {A Ω : Subgroup R} [A.Normal]
    (_hΩ_le_A : Ω ≤ A) (hΩcomm : IsMulCommutative Ω)
    {x y : R}
    (hxΩC : x ∈ Subgroup.centralizer (Ω : Set R))
    (hyΩC : y ∈ Subgroup.centralizer (Ω : Set R))
    (hxquot : ∀ a : R, a ∈ A → ⁅x, a⁆ ∈ Ω)
    (hyquot : ∀ a : R, a ∈ A → ⁅y, a⁆ ∈ Ω) :
    ⁅x, y⁆ ∈ Subgroup.centralizer (A : Set R) := by
  let Ωsub : Subgroup A := Ω.subgroupOf A
  have hΩsub_comm : IsMulCommutative Ωsub := by
    refine ⟨⟨fun u v => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm
      (s := Ω) (show (u : R) ∈ Ω from u.2) (show (v : R) ∈ Ω from v.2)
  let φx : MulAut A := MulAut.conjNormal (H := A) x
  let φy : MulAut A := MulAut.conjNormal (H := A) y
  have hφx_fix : ∀ h : Ωsub, φx (h : A) = h := by
    intro h
    apply Subtype.ext
    have hcomm : (h : R) * x = x * (h : R) :=
      (Subgroup.mem_centralizer_iff.mp hxΩC (h : R) h.2)
    calc
      ((φx (h : A) : A) : R) = x * (h : R) * x⁻¹ := by
        simp [φx, MulAut.conjNormal_apply]
      _ = ((h : R) * x) * x⁻¹ := by rw [← hcomm]
      _ = h := by simp [mul_assoc]
  have hφy_fix : ∀ h : Ωsub, φy (h : A) = h := by
    intro h
    apply Subtype.ext
    have hcomm : (h : R) * y = y * (h : R) :=
      (Subgroup.mem_centralizer_iff.mp hyΩC (h : R) h.2)
    calc
      ((φy (h : A) : A) : R) = y * (h : R) * y⁻¹ := by
        simp [φy, MulAut.conjNormal_apply]
      _ = ((h : R) * y) * y⁻¹ := by rw [← hcomm]
      _ = h := by simp [mul_assoc]
  have hφx_quot : ∀ a : A, φx a * a⁻¹ ∈ Ωsub := by
    intro a
    change ((φx a : A) * a⁻¹ : R) ∈ Ω
    simpa [φx, MulAut.conjNormal_apply, MulAut.conj_apply, commutatorElement_def, mul_assoc]
      using hxquot (a : R) a.2
  have hφy_quot : ∀ a : A, φy a * a⁻¹ ∈ Ωsub := by
    intro a
    change ((φy a : A) * a⁻¹ : R) ∈ Ω
    simpa [φy, MulAut.conjNormal_apply, MulAut.conj_apply, commutatorElement_def, mul_assoc]
      using hyquot (a : R) a.2
  have hφ_comm : φx * φy = φy * φx :=
    mulAut_commute_of_trivial_on_subgroup_and_quotient
      (G := A) (H := Ωsub) hΩsub_comm hφx_fix hφy_fix hφx_quot hφy_quot
  exact
    commutator_mem_centralizer_of_conjNormal_commute
      (A := A) (x := x) (y := y) (by simpa [φx, φy] using hφ_comm)

private theorem CFSG.closure_pair_conj_lt_top_of_not_isCyclic_pgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p G)] {x y : G} (hncyc : ¬ IsCyclic G) :
    Subgroup.closure ({y, x * y * x⁻¹} : Set G) < ⊤ := by
  classical
  let L : Subgroup G := Subgroup.closure ({y, x * y * x⁻¹} : Set G)
  refine lt_of_le_of_ne le_top ?_
  intro hLtop
  apply hncyc
  let Φ : Subgroup G := frattini G
  have : Φ.Normal := by
    dsimp [Φ]
    infer_instance
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  have hcomm_mem : ⁅x, y⁆ ∈ Φ := by
    have hcomm_top : ⁅x, y⁆ ∈ _root_.commutator G := by
      simpa [_root_.commutator_def] using
        (Subgroup.commutator_mem_commutator
          (G := G) (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
          (g₁ := x) (g₂ := y) (h₁ := by simp) (h₂ := by simp))
    change ⁅x, y⁆ ∈ frattini G
    rw [frattini_eq_closure_commutator_union_powers (R := G) (p := p)]
    exact Subgroup.subset_closure (Or.inl hcomm_top)
  have hq_conj : q (x * y * x⁻¹) = q y := by
    apply (QuotientGroup.eq_iff_div_mem).2
    simpa [q, Φ, div_eq_mul_inv, commutatorElement_def, mul_assoc] using hcomm_mem
  have hLmap_le : L.map q ≤ Subgroup.zpowers (q y) := by
    dsimp [L]
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := Subgroup.zpowers (q y))).2 ?_
    rintro z ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · rw [hw]
      exact Subgroup.mem_zpowers (q y)
    · have hw_eq : w = x * y * x⁻¹ := by simpa using hw
      rw [hw_eq, hq_conj]
      exact Subgroup.mem_zpowers (q y)
  have hLmap_top : L.map q = ⊤ := by
    change (Subgroup.closure ({y, x * y * x⁻¹} : Set G)).map q = ⊤
    rw [hLtop]
    exact Subgroup.map_top_of_surjective (f := q) (QuotientGroup.mk'_surjective Φ)
  have hq_y_top : Subgroup.zpowers (q y) = ⊤ :=
    top_unique (by simpa [hLmap_top] using hLmap_le)
  have hy_sup_frattini : Subgroup.zpowers y ⊔ Φ = ⊤ := by
    have hcomap :
        Subgroup.comap q (Subgroup.zpowers (q y)) =
          Subgroup.zpowers y ⊔ Φ := by
      calc
        Subgroup.comap q (Subgroup.zpowers (q y))
            = Subgroup.comap q ((Subgroup.zpowers y).map q) := by
                rw [MonoidHom.map_zpowers]
        _ = Subgroup.zpowers y ⊔ q.ker := by
                simpa using
                  (Subgroup.comap_map_eq (f := q) (H := Subgroup.zpowers y))
        _ = Subgroup.zpowers y ⊔ Φ := by
                simp [q, Φ, QuotientGroup.ker_mk']
    calc
      Subgroup.zpowers y ⊔ Φ =
          Subgroup.comap q (Subgroup.zpowers (q y)) := hcomap.symm
      _ = ⊤ := by simp [hq_y_top]
  have hy_top : Subgroup.zpowers y = ⊤ :=
    lemma_1_7_a (R := G) (p := p) (H := Subgroup.zpowers y)
      (by simpa [Φ] using hy_sup_frattini)
  exact (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨y, hy_top⟩

private theorem CFSG.closure_pair_conj_lt_closure_pair_of_not_isCyclic
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] {x y : R}
    (hncyc : ¬ IsCyclic (Subgroup.closure ({x, y} : Set R))) :
    Subgroup.closure ({y, x * y * x⁻¹} : Set R) <
      Subgroup.closure ({x, y} : Set R) := by
  classical
  let T : Subgroup R := Subgroup.closure ({x, y} : Set R)
  let L : Subgroup R := Subgroup.closure ({y, x * y * x⁻¹} : Set R)
  have hxT : x ∈ T := by
    dsimp [T]
    exact Subgroup.subset_closure (by simp)
  have hyT : y ∈ T := by
    dsimp [T]
    exact Subgroup.subset_closure (by simp)
  have hconjT : x * y * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hxT hyT) (T.inv_mem hxT)
  have hL_le_T : L ≤ T := by
    dsimp [L]
    refine (Subgroup.closure_le (K := T)).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact hyT
    · have hz_eq : z = x * y * x⁻¹ := by simpa using hz
      simpa [hz_eq] using hconjT
  refine lt_of_le_of_ne hL_le_T ?_
  intro hLT
  let xT : T := ⟨x, hxT⟩
  let yT : T := ⟨y, hyT⟩
  let cT : T := ⟨x * y * x⁻¹, hconjT⟩
  let Lsub : Subgroup T := Subgroup.closure ({yT, cT} : Set T)
  have hxyT_top : Subgroup.closure ({xT, yT} : Set T) = ⊤ := by
    apply (Subgroup.eq_top_iff' (Subgroup.closure ({xT, yT} : Set T))).2
    intro z
    refine Subgroup.closure_induction
      (p := fun r _hr => ∀ hrT : r ∈ T,
        (⟨r, hrT⟩ : T) ∈ Subgroup.closure ({xT, yT} : Set T))
      (x := (z : R)) ?_ ?_ ?_ ?_ z.2 z.2
    · intro r hr hrT
      rcases hr with rfl | hr
      · exact Subgroup.subset_closure (by simp [xT])
      · have hr_eq : r = y := by simpa using hr
        subst r
        exact Subgroup.subset_closure (by simp [yT])
    · intro h1T
      change (1 : T) ∈ Subgroup.closure ({xT, yT} : Set T)
      exact (Subgroup.closure ({xT, yT} : Set T)).one_mem
    · intro a b haT hbT ha hb _habT
      simpa using (Subgroup.closure ({xT, yT} : Set T)).mul_mem (ha haT) (hb hbT)
    · intro a haT ha _haInvT
      change ((⟨a, haT⟩ : T)⁻¹) ∈ Subgroup.closure ({xT, yT} : Set T)
      exact (Subgroup.closure ({xT, yT} : Set T)).inv_mem (ha haT)
  have hmem_Lsub_of_mem_L :
      ∀ {z : R}, z ∈ L → ∀ hzT : z ∈ T, (⟨z, hzT⟩ : T) ∈ Lsub := by
    intro z hzL
    refine Subgroup.closure_induction
      (p := fun r _hr => ∀ hrT : r ∈ T, (⟨r, hrT⟩ : T) ∈ Lsub)
      (x := z) ?_ ?_ ?_ ?_ hzL
    · intro r hr hrT
      rcases hr with rfl | hr
      · exact Subgroup.subset_closure (by simp [yT])
      · have hr_eq : r = x * y * x⁻¹ := by simpa using hr
        subst r
        exact Subgroup.subset_closure (by simp [cT])
    · intro h1T
      change (1 : T) ∈ Lsub
      exact Lsub.one_mem
    · intro a b _ha _hb ha hb habT
      have haT : a ∈ T := by
        have : a * b * b⁻¹ ∈ T := T.mul_mem habT (T.inv_mem (hL_le_T _hb))
        simpa [mul_assoc] using this
      have hbT : b ∈ T := hL_le_T _hb
      simpa using Lsub.mul_mem (ha haT) (hb hbT)
    · intro a _ha ha haT
      have haT' : a ∈ T := by
        simpa using T.inv_mem haT
      change ((⟨a, haT'⟩ : T)⁻¹) ∈ Lsub
      exact Lsub.inv_mem (ha haT')
  have hxT_mem_Lsub : xT ∈ Lsub := by
    have hxL : x ∈ L := by
      change x ∈ Subgroup.closure ({y, x * y * x⁻¹} : Set R)
      rw [hLT]
      exact hxT
    simpa [xT] using hmem_Lsub_of_mem_L hxL hxT
  have hyT_mem_Lsub : yT ∈ Lsub := by
    exact Subgroup.subset_closure (by simp [yT])
  have hLsub_top : Lsub = ⊤ := by
    apply top_unique
    rw [← hxyT_top]
    refine (Subgroup.closure_le (K := Lsub)).2 ?_
    intro z hz
    rcases hz with rfl | hz
    · exact hxT_mem_Lsub
    · have hz_eq : z = yT := by simpa using hz
      simpa [hz_eq] using hyT_mem_Lsub
  have : Fact (IsPGroup p T) := ⟨(Fact.out : IsPGroup p R).to_subgroup T⟩
  have hproper :=
    closure_pair_conj_lt_top_of_not_isCyclic_pgroup
      (G := T) (p := p) (x := xT) (y := yT) hncyc
  have hcT_eq : cT = xT * yT * xT⁻¹ := by
    apply Subtype.ext
    simp [xT, yT, cT, mul_assoc]
  have hproper' : Lsub < ⊤ := by
    simpa [Lsub, hcT_eq] using hproper
  exact hproper'.ne hLsub_top

private theorem CFSG.mem_center_closure_pair_of_commute_generators
    {G : Type*} [Group G] {x y z : G}
    (hzT : z ∈ Subgroup.closure ({x, y} : Set G))
    (hzx : Commute z x) (hzy : Commute z y) :
    (⟨z, hzT⟩ : Subgroup.closure ({x, y} : Set G)) ∈
      Subgroup.center (Subgroup.closure ({x, y} : Set G)) := by
  let T : Subgroup G := Subgroup.closure ({x, y} : Set G)
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  change (w : G) * z = z * (w : G)
  refine Subgroup.closure_induction
    (p := fun t _ht => t * z = z * t)
    (x := (w : G)) ?_ ?_ ?_ ?_ w.2
  · intro t ht
    rcases ht with rfl | ht
    · exact hzx.symm.eq
    · have hty : t = y := by simpa using ht
      rw [hty]
      exact hzy.symm.eq
  · simp
  · intro a b _ha _hb haz hbz
    calc
      (a * b) * z = a * (b * z) := by simp [mul_assoc]
      _ = a * (z * b) := by rw [hbz]
      _ = (a * z) * b := by simp [mul_assoc]
      _ = (z * a) * b := by rw [haz]
      _ = z * (a * b) := by simp [mul_assoc]
  · intro a _ha haz
    have hcomm : Commute a z := haz
    exact hcomm.inv_left.eq

private theorem CFSG.pth_mul_eq_one_of_commutator_centralizes_pair
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hcx : Commute ⁅y, x⁆ x) (hcy : Commute ⁅y, x⁆ y) :
    (x * y) ^ p = 1 := by
  let T : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let xT : T := ⟨x, Subgroup.subset_closure (by simp)⟩
  let yT : T := ⟨y, Subgroup.subset_closure (by simp)⟩
  have hcommT_mem : ⁅y, x⁆ ∈ T := by
    dsimp [T]
    rw [commutatorElement_def]
    exact
      (Subgroup.closure ({x, y} : Set G)).mul_mem
        ((Subgroup.closure ({x, y} : Set G)).mul_mem
          ((Subgroup.closure ({x, y} : Set G)).mul_mem
            (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))
          ((Subgroup.closure ({x, y} : Set G)).inv_mem
            (Subgroup.subset_closure (by simp))))
        ((Subgroup.closure ({x, y} : Set G)).inv_mem
          (Subgroup.subset_closure (by simp)))
  have hcommT_center : ⁅yT, xT⁆ ∈ Subgroup.center T := by
    have hcenter :
        (⟨⁅y, x⁆, hcommT_mem⟩ : T) ∈ Subgroup.center T :=
      mem_center_closure_pair_of_commute_generators
        (G := G) (x := x) (y := y) (z := ⁅y, x⁆) hcommT_mem hcx hcy
    have hcommT_eq : ⁅yT, xT⁆ = (⟨⁅y, x⁆, hcommT_mem⟩ : T) := by
      apply Subtype.ext
      simp [xT, yT, commutatorElement_def, mul_assoc]
    simpa [hcommT_eq] using hcenter
  have hxT : xT ^ p = 1 := by
    apply Subtype.ext
    simpa [xT] using hx
  have hyT : yT ^ p = 1 := by
    apply Subtype.ext
    simpa [yT] using hy
  have hpowT : (xT * yT) ^ p = 1 :=
    pth_mul_eq_one_of_class2 (G := T) (p := p) hpodd xT yT hcommT_center hxT hyT
  simpa [xT, yT] using congrArg Subtype.val hpowT

private theorem CFSG.omega₁_map_subtype_normal_of_normal
    {R : Type*} [Group R] {p : ℕ} {A : Subgroup R} [A.Normal] :
    ((omega₁ (G := A) (p := p)).map A.subtype).Normal := by
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
  have : Ωsub.Characteristic := by
    simpa [Ωsub] using (omega₁_characteristic (G := A) (p := p))
  simpa [Ωsub] using (inferInstance : (Ωsub.map A.subtype).Normal)

private theorem CFSG.closure_omega_adjoin_eq_sup_zpowers
    {R : Type*} [Group R] {p : ℕ} {A : Subgroup R} {x : R} :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    B₁ = ΩA ⊔ Subgroup.zpowers x := by
  classical
  intro ΩA B₁
  apply le_antisymm
  · refine (Subgroup.closure_le (K := ΩA ⊔ Subgroup.zpowers x)).2 ?_
    intro y hy
    rcases hy with hyΩ | hyx
    · exact (le_sup_left : ΩA ≤ ΩA ⊔ Subgroup.zpowers x) hyΩ
    · have hy_eq : y = x := by simpa using hyx
      rw [hy_eq]
      exact (le_sup_right : Subgroup.zpowers x ≤ ΩA ⊔ Subgroup.zpowers x)
        (Subgroup.mem_zpowers x)
  · rw [Subgroup.sup_eq_closure]
    refine (Subgroup.closure_le (K := B₁)).2 ?_
    intro y hy
    rcases hy with hyΩ | hyz
    · exact Subgroup.subset_closure (Or.inl hyΩ)
    · have hxB₁_gen : x ∈ B₁ :=
        Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
      exact (Subgroup.zpowers_le).2 hxB₁_gen hyz


private theorem CFSG.closure_adjoin_eq_sup_closure_omega_adjoin
    {R : Type*} [Group R] {p : ℕ} {A : Subgroup R} {x : R} :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    Subgroup.closure ((A : Set R) ∪ {x}) = A ⊔ B₁ := by
  classical
  intro ΩA B₁
  have hΩ_le_A : ΩA ≤ A := by
    simpa [ΩA] using Subgroup.map_subtype_le (omega₁ (G := A) (p := p))
  apply le_antisymm
  · refine (Subgroup.closure_le (K := A ⊔ B₁)).2 ?_
    intro y hy
    rcases hy with hyA | hyx
    · exact (le_sup_left : A ≤ A ⊔ B₁) hyA
    · have hy_eq : y = x := by simpa using hyx
      rw [hy_eq]
      exact (le_sup_right : B₁ ≤ A ⊔ B₁)
        (Subgroup.subset_closure (Or.inr (Set.mem_singleton x)))
  · rw [Subgroup.sup_eq_closure]
    refine (Subgroup.closure_le (K := Subgroup.closure ((A : Set R) ∪ {x}))).2 ?_
    intro y hy
    rcases hy with hyA | hyB
    · exact Subgroup.subset_closure (Or.inl hyA)
    · refine Subgroup.closure_induction
        (p := fun z _hz => z ∈ Subgroup.closure ((A : Set R) ∪ {x}))
        (x := y) ?_ ?_ ?_ ?_ hyB
      · intro z hz
        rcases hz with hzΩ | hzx
        · exact Subgroup.subset_closure (Or.inl (hΩ_le_A hzΩ))
        · have hz_eq : z = x := by simpa using hzx
          rw [hz_eq]
          exact Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
      · exact (Subgroup.closure ((A : Set R) ∪ {x})).one_mem
      · intro u v _hu _hv hu hv
        exact (Subgroup.closure ((A : Set R) ∪ {x})).mul_mem hu hv
      · intro z _hz hz
        exact (Subgroup.closure ((A : Set R) ∪ {x})).inv_mem hz

private theorem CFSG.closure_omega_adjoin_isMulCommutative
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime]
    {A : Subgroup R} (hAcomm : IsMulCommutative A) {x : R}
    (hxC :
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R))) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    IsMulCommutative B₁ := by
  classical
  intro ΩA B₁
  have hΩcomm : IsMulCommutative ΩA := by
    let : IsMulCommutative A := hAcomm
    dsimp [ΩA]
    exact Subgroup.map_isMulCommutative (f := A.subtype) (H := omega₁ (G := A) (p := p))
  have hcomm_generators :
      ∀ y ∈ ((ΩA : Set R) ∪ {x}), ∀ z ∈ ((ΩA : Set R) ∪ {x}), y * z = z * y := by
    intro y hy z hz
    rcases hy with hyΩ | hyx
    · rcases hz with hzΩ | hzx
      · exact setLike_mul_comm (s := ΩA) hyΩ hzΩ
      · have hz_eq : z = x := by simpa using hzx
        rw [hz_eq]
        exact (Subgroup.mem_centralizer_iff.mp hxC) y hyΩ
    · have hy_eq : y = x := by simpa using hyx
      rw [hy_eq]
      rcases hz with hzΩ | hzx
      · exact ((Subgroup.mem_centralizer_iff.mp hxC) z hzΩ).symm
      · have hz_eq : z = x := by simpa using hzx
        rw [hz_eq]
  exact Subgroup.isMulCommutative_closure (fun x hx y hy _ => hcomm_generators x hx y hy)

private theorem CFSG.intermediate_inf_A_sup_closure_omega_adjoin_eq_top
    {R : Type*} [Group R] {p : ℕ} {A : Subgroup R} [A.Normal] {x : R}
    {M : Subgroup R}
    (hB₁_le_M :
      (Subgroup.closure
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R) ∪ {x})) ≤ M)
    (hM_le_H : M ≤ Subgroup.closure ((A : Set R) ∪ {x})) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    ((A ⊓ M).subgroupOf M) ⊔ (B₁.subgroupOf M) = ⊤ := by
  classical
  intro ΩA B₁
  have hB₁_le_M' : B₁ ≤ M := by
    simpa [ΩA, B₁] using hB₁_le_M
  have hH_eq : Subgroup.closure ((A : Set R) ∪ {x}) = A ⊔ B₁ := by
    simpa [ΩA, B₁] using
      closure_adjoin_eq_sup_closure_omega_adjoin (R := R) (p := p) (A := A) (x := x)
  have hC_norm : ((A ⊓ M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (H := A ⊓ M) (K := M) inf_le_right]
    intro a m ha hm
    exact
      ⟨(inferInstance : A.Normal).conj_mem a ha.1 m,
        M.mul_mem (M.mul_mem hm ha.2) (M.inv_mem hm)⟩
  let : ((A ⊓ M).subgroupOf M).Normal := hC_norm
  apply eq_top_iff.2
  intro m _hm
  have hmH : (m : R) ∈ A ⊔ B₁ := by
    have hmH' : (m : R) ∈ Subgroup.closure ((A : Set R) ∪ {x}) := hM_le_H m.2
    rw [hH_eq] at hmH'
    exact hmH'
  rcases (Subgroup.mem_sup_of_normal_left
      (x := (m : R)) (s := A) (t := B₁)).1 hmH with
    ⟨a, haA, b, hbB, hab_eq⟩
  have hbM : b ∈ M := hB₁_le_M' hbB
  have haM : a ∈ M := by
    have ha_eq : a = (m : R) * b⁻¹ := by
      rw [← hab_eq]
      simp [mul_assoc]
    rw [ha_eq]
    exact M.mul_mem m.2 (M.inv_mem hbM)
  let aM : M := ⟨a, haM⟩
  let bM : M := ⟨b, hbM⟩
  have haC : aM ∈ (A ⊓ M).subgroupOf M := by
    exact ⟨haA, haM⟩
  have hbBsub : bM ∈ B₁.subgroupOf M := by
    exact hbB
  have hm_eq : aM * bM = m := by
    apply Subtype.ext
    exact hab_eq
  rw [← hm_eq]
  exact
    (Subgroup.mem_sup_of_normal_left
      (s := (A ⊓ M).subgroupOf M) (t := B₁.subgroupOf M)).2
      ⟨aM, haC, bM, hbBsub, rfl⟩

set_option maxHeartbeats 800000 in
private theorem CFSG.intermediate_nilpotencyClassLe_two_of_closure_omega_normal
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime]
    {A : Subgroup R} [A.Normal] (hAcomm : IsMulCommutative A) {x : R}
    (hxC :
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)))
    {M : Subgroup R}
    (hB₁_le_M :
      (let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
       Subgroup.closure ((ΩA : Set R) ∪ {x})) ≤ M)
    (hM_le_H : M ≤ Subgroup.closure ((A : Set R) ∪ {x}))
    (hB₁_norm_M :
      let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
      let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
      (B₁.subgroupOf M).Normal) :
    NilpotencyClassLe 2 M := by
  classical
  let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
  let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
  let Bsub : Subgroup M := B₁.subgroupOf M
  let Csub : Subgroup M := (A ⊓ M).subgroupOf M
  have hΩ_le_B₁ : ΩA ≤ B₁ := by
    intro y hy
    exact Subgroup.subset_closure (Or.inl hy)
  have hB₁_le_M' : B₁ ≤ M := by
    simpa [ΩA, B₁] using hB₁_le_M
  have hBsub_norm : Bsub.Normal := by
    simpa [Bsub, ΩA, B₁] using hB₁_norm_M
  let : Bsub.Normal := hBsub_norm
  have hCsub_norm : Csub.Normal := by
    rw [Subgroup.normal_subgroupOf_iff (H := A ⊓ M) (K := M) inf_le_right]
    intro a m ha hm
    exact
      ⟨(inferInstance : A.Normal).conj_mem a ha.1 m,
        M.mul_mem (M.mul_mem hm ha.2) (M.inv_mem hm)⟩
  let : Csub.Normal := hCsub_norm
  have hCB_top : Csub ⊔ Bsub = ⊤ := by
    simpa [ΩA, B₁, Bsub, Csub] using
      intermediate_inf_A_sup_closure_omega_adjoin_eq_top
        (R := R) (p := p) (A := A) (x := x) (M := M)
        (by simpa [ΩA, B₁] using hB₁_le_M') hM_le_H
  have hBC_top : Bsub ⊔ Csub = ⊤ := by
    simpa [sup_comm] using hCB_top
  have hB₁comm : IsMulCommutative B₁ := by
    simpa [ΩA, B₁] using
      closure_omega_adjoin_isMulCommutative
        (R := R) (p := p) (A := A) hAcomm (x := x) hxC
  have hBsubcomm : IsMulCommutative Bsub := by
    let : IsMulCommutative B₁ := hB₁comm
    infer_instance
  have hCsubcomm : IsMulCommutative Csub := by
    refine ⟨⟨fun y z => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((y : M) : R) * ((z : M) : R) = ((z : M) : R) * ((y : M) : R)
    have hyA : ((y : M) : R) ∈ A := by
      exact y.2.1
    have hzA : ((z : M) : R) ∈ A := by
      exact z.2.1
    exact setLike_mul_comm (s := A) hyA hzA
  have hcomm_le_B : _root_.commutator M ≤ Bsub :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := Bsub) (H := Csub) hBC_top hCsubcomm
  have hcomm_le_C : _root_.commutator M ≤ Csub :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      (N := Csub) (H := Bsub) hCB_top hBsubcomm
  have hcomm_le_inf : _root_.commutator M ≤ Bsub ⊓ Csub :=
    le_inf hcomm_le_B hcomm_le_C
  have hinf_le_center : Bsub ⊓ Csub ≤ Subgroup.center M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hw_sup : w ∈ Csub ⊔ Bsub := by
      simp [hCB_top]
    rcases (Subgroup.mem_sup_of_normal_left
        (x := w) (s := Csub) (t := Bsub)).1 hw_sup with
      ⟨c, hcC, b, hbB, hcb_eq⟩
    have hzB : z ∈ Bsub := hz.1
    have hzC : z ∈ Csub := hz.2
    have hzc : c * z = z * c := by
      apply Subtype.ext
      change ((c : M) : R) * ((z : M) : R) = ((z : M) : R) * ((c : M) : R)
      have hcA : ((c : M) : R) ∈ A := hcC.1
      have hzA : ((z : M) : R) ∈ A := hzC.1
      exact setLike_mul_comm (s := A) hcA hzA
    have hzb : b * z = z * b := by
      apply Subtype.ext
      change ((b : M) : R) * ((z : M) : R) = ((z : M) : R) * ((b : M) : R)
      have hbB₁ : ((b : M) : R) ∈ B₁ := hbB
      have hzB₁ : ((z : M) : R) ∈ B₁ := hzB
      exact setLike_mul_comm (s := B₁) hbB₁ hzB₁
    calc
      w * z = (c * b) * z := by rw [hcb_eq]
      _ = c * (b * z) := by simp [mul_assoc]
      _ = c * (z * b) := by rw [hzb]
      _ = (c * z) * b := by simp [mul_assoc]
      _ = (z * c) * b := by rw [hzc]
      _ = z * (c * b) := by simp [mul_assoc]
      _ = z * w := by rw [hcb_eq]
  have hcomm_center : _root_.commutator M ≤ Subgroup.center M :=
    hcomm_le_inf.trans hinf_le_center
  have hL1_le_center :
      (Subgroup.lowerCentralSeries (⊤ : Subgroup M) 1) ≤ Subgroup.center M := by
    rw [Subgroup.top_lowerCentralSeries_one]
    exact hcomm_center
  have hL2_bot : Subgroup.lowerCentralSeries (⊤ : Subgroup M) 2 = ⊥ := by
    simpa using
      (Subgroup.lowerCentralSeries_succ_eq_bot (⊤ : Subgroup M) hL1_le_center)
  have hnil : Group.IsNilpotent M :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := M)).2 ⟨2, hL2_bot⟩
  let : Group.IsNilpotent M := hnil
  have hclass : Group.nilpotencyClass M ≤ 2 :=
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le (G := M)).1 hL2_bot
  unfold NilpotencyClassLe
  exact (Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le (G := M)).2 hclass

private theorem CFSG.closure_omega_adjoin_pow_eq_one
    {R : Type*} [Group R] {p : ℕ} [Fact p.Prime]
    {A : Subgroup R} (hAcomm : IsMulCommutative A) {x : R}
    (hxC :
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)))
    (hxpow : x ^ p = 1) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    ∀ b : B₁, b ^ p = 1 := by
  classical
  intro ΩA B₁ b
  have hB₁comm : IsMulCommutative B₁ := by
    simpa [ΩA, B₁] using
      closure_omega_adjoin_isMulCommutative
        (R := R) (p := p) (A := A) hAcomm (x := x) hxC
  let : IsMulCommutative B₁ := hB₁comm
  have hΩelem : IsElementaryAbelian p ΩA := by
    let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
    have hΩsub_elem : IsElementaryAbelian p Ωsub := by
      let : IsMulCommutative A := hAcomm
      simpa [Ωsub] using omega₁_isElementaryAbelian_of_commutative_local (p := p) A
    let : IsElementaryAbelian p Ωsub := hΩsub_elem
    simpa [ΩA, Ωsub] using
      isElementaryAbelian_map_of_injective_local
        (p := p) A.subtype A.subtype_injective
  let : IsElementaryAbelian p ΩA := hΩelem
  apply Subtype.ext
  change (b : R) ^ p = 1
  refine Subgroup.closure_induction
    (p := fun y _hy => y ^ p = 1)
    (x := (b : R)) ?_ ?_ ?_ ?_ b.2
  · intro y hy
    rcases hy with hyΩ | hyx
    · let yΩ : ΩA := ⟨y, hyΩ⟩
      have hyΩpow : yΩ ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p ΩA) yΩ
      simpa [yΩ] using congrArg Subtype.val hyΩpow
    · have hy_eq : y = x := by simpa using hyx
      simpa [hy_eq] using hxpow
  · simp
  · intro y z hyB hzB hypow hzpow
    have hcomm : Commute y z := by
      change y * z = z * y
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := B₁)).comm ⟨y, hyB⟩ ⟨z, hzB⟩)
    calc
      (y * z) ^ p = y ^ p * z ^ p := by simpa using hcomm.mul_pow p
      _ = 1 := by simp [hypow, hzpow]
  · intro y _hy hypow
    simpa [inv_pow] using congrArg Inv.inv hypow

private theorem CFSG.closure_omega_adjoin_inf_A_le_omega
    {R : Type*} [Group R] [Finite R] {p : ℕ}
    {A : Subgroup R} [A.Normal] {x : R} (hxpow : x ^ p = 1) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    B₁ ⊓ A ≤ ΩA := by
  classical
  intro ΩA B₁
  have hΩ_le_A : ΩA ≤ A := by
    simpa [ΩA] using Subgroup.map_subtype_le (omega₁ (G := A) (p := p))
  have : ΩA.Normal := by
    simpa [ΩA] using omega₁_map_subtype_normal_of_normal (A := A) (p := p)
  have hB₁_eq : B₁ = ΩA ⊔ Subgroup.zpowers x := by
    simpa [ΩA, B₁] using
      closure_omega_adjoin_eq_sup_zpowers (R := R) (p := p) (A := A) (x := x)
  intro y hy
  rcases hy with ⟨hyB₁, hyA⟩
  have hy_sup : y ∈ ΩA ⊔ Subgroup.zpowers x := by
    simpa [hB₁_eq] using hyB₁
  rcases (Subgroup.mem_sup_of_normal_left
      (x := y) (s := ΩA) (t := Subgroup.zpowers x)).1 hy_sup with
    ⟨ω, hωΩ, z, hzx, hy_eq⟩
  have hzpow : z ^ p = 1 := by
    have hz_order_dvd : orderOf z ∣ p :=
      (orderOf_dvd_of_mem_zpowers hzx).trans
        ((orderOf_dvd_iff_pow_eq_one).2 hxpow)
    exact (orderOf_dvd_iff_pow_eq_one).1 hz_order_dvd
  have hzA : z ∈ A := by
    have hωA : ω ∈ A := hΩ_le_A hωΩ
    have hz_eq : z = ω⁻¹ * (ω * z) := by simp
    rw [hz_eq]
    exact A.mul_mem (A.inv_mem hωA) (by simpa [← hy_eq] using hyA)
  have hzΩ : z ∈ ΩA :=
    mem_omega₁_map_subtype_of_mem_pow_eq_one (A := A) hzA hzpow
  have hy_eq' : y = ω * z := hy_eq.symm
  rw [hy_eq']
  exact ΩA.mul_mem hωΩ hzΩ

set_option maxHeartbeats 800000 in
private theorem CFSG.intermediate_order_p_mem_closure_omega_adjoin_of_normal
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpodd : p ≠ 2)
    {A : Subgroup R} [A.Normal] (hAcomm : IsMulCommutative A) {x : R}
    (hxC :
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)))
    (hxpow : x ^ p = 1)
    {M : Subgroup R}
    (hB₁_le_M :
      (let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
       Subgroup.closure ((ΩA : Set R) ∪ {x})) ≤ M)
    (hM_le_H : M ≤ Subgroup.closure ((A : Set R) ∪ {x}))
    (hB₁_norm_M :
      let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
      let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
      (B₁.subgroupOf M).Normal) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    ∀ z : R, z ∈ M → z ^ p = 1 → z ∈ B₁ := by
  classical
  intro ΩA B₁ z hzM hzpow
  let Bsub : Subgroup M := B₁.subgroupOf M
  let Csub : Subgroup M := (A ⊓ M).subgroupOf M
  have hΩ_le_B₁ : ΩA ≤ B₁ := by
    intro y hy
    exact Subgroup.subset_closure (Or.inl hy)
  have hB₁_le_M' : B₁ ≤ M := by
    simpa [ΩA, B₁] using hB₁_le_M
  have hBsub_norm : Bsub.Normal := by
    simpa [Bsub, ΩA, B₁] using hB₁_norm_M
  let : Bsub.Normal := hBsub_norm
  have hCsub_norm : Csub.Normal := by
    rw [Subgroup.normal_subgroupOf_iff (H := A ⊓ M) (K := M) inf_le_right]
    intro a m ha hm
    exact
      ⟨(inferInstance : A.Normal).conj_mem a ha.1 m,
        M.mul_mem (M.mul_mem hm ha.2) (M.inv_mem hm)⟩
  let : Csub.Normal := hCsub_norm
  have hclassM : NilpotencyClassLe 2 M := by
    simpa [ΩA, B₁, Bsub] using
      intermediate_nilpotencyClassLe_two_of_closure_omega_normal
        (R := R) (p := p) (A := A) hAcomm (x := x) hxC
        (M := M) (by simpa [ΩA, B₁] using hB₁_le_M')
        hM_le_H (by simpa [ΩA, B₁, Bsub] using hBsub_norm)
  have hCB_top : Csub ⊔ Bsub = ⊤ := by
    simpa [ΩA, B₁, Csub, Bsub] using
      intermediate_inf_A_sup_closure_omega_adjoin_eq_top
        (R := R) (p := p) (A := A) (x := x) (M := M)
        (by simpa [ΩA, B₁] using hB₁_le_M') hM_le_H
  have hBpow : ∀ b : B₁, b ^ p = 1 := by
    simpa [ΩA, B₁] using
      closure_omega_adjoin_pow_eq_one
        (R := R) (p := p) (A := A) hAcomm (x := x) hxC hxpow
  let zM : M := ⟨z, hzM⟩
  have hzM_top : zM ∈ Csub ⊔ Bsub := by
    simp [hCB_top]
  rcases (Subgroup.mem_sup_of_normal_left
      (x := zM) (s := Csub) (t := Bsub)).1 hzM_top with
    ⟨aM, haC, bM, hbB, hab_eq⟩
  have hzMpow : zM ^ p = 1 := by
    apply Subtype.ext
    simpa [zM] using hzpow
  have hbB₁ : ((bM : M) : R) ∈ B₁ := hbB
  have hbpowR : ((bM : M) : R) ^ p = 1 := by
    have hbpowB : (⟨((bM : M) : R), hbB₁⟩ : B₁) ^ p = 1 :=
      hBpow ⟨((bM : M) : R), hbB₁⟩
    simpa using congrArg Subtype.val hbpowB
  have hbInvPowM : bM⁻¹ ^ p = 1 := by
    apply Subtype.ext
    change (((bM : M) : R)⁻¹) ^ p = 1
    simpa [inv_pow] using congrArg Inv.inv hbpowR
  have hcomm_le :
      ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ ≤ Subgroup.center M :=
    commutator_le_center_of_le_upperCentralSeries_two (G := M) (⊤ : Subgroup M)
      (by simpa [hclassM])
  have hcomm_mem : ⁅bM⁻¹, zM⁆ ∈ Subgroup.center M := by
    exact hcomm_le (Subgroup.commutator_mem_commutator (by simp) (by simp))
  have haMpow : aM ^ p = 1 := by
    have hzb_pow : (zM * bM⁻¹) ^ p = 1 :=
      pth_mul_eq_one_of_class2
        (G := M) (p := p) hpodd zM bM⁻¹ hcomm_mem hzMpow hbInvPowM
    have hzb_eq : zM * bM⁻¹ = aM := by
      rw [← hab_eq]
      simp [mul_assoc]
    simpa [hzb_eq] using hzb_pow
  have haRpow : ((aM : M) : R) ^ p = 1 := by
    simpa using congrArg Subtype.val haMpow
  have haΩ : ((aM : M) : R) ∈ ΩA :=
    mem_omega₁_map_subtype_of_mem_pow_eq_one (A := A) haC.1 haRpow
  have hz_eq : z = ((aM : M) : R) * ((bM : M) : R) := by
    exact (congrArg Subtype.val hab_eq).symm
  rw [hz_eq]
  exact B₁.mul_mem (hΩ_le_B₁ haΩ) hbB₁

private theorem CFSG.closure_omega_adjoin_order_p_normalized_by_closure_adjoin
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpodd : p ≠ 2)
    {A : Subgroup R} [A.Normal] (hAcomm : IsMulCommutative A)
    {x : R}
    (hxC :
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)))
    (hxpow : x ^ p = 1) :
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
    Subgroup.closure ((A : Set R) ∪ {x}) ≤ Subgroup.normalizer (B₁ : Set R) := by
  classical
  let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
  let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
  let H : Subgroup R := Subgroup.closure ((A : Set R) ∪ {x})
  change H ≤ Subgroup.normalizer (B₁ : Set R)
  have hΩ_norm : ΩA.Normal := by
    simpa [ΩA] using omega₁_map_subtype_normal_of_normal (A := A) (p := p)
  have hΩ_le_B₁ : ΩA ≤ B₁ := by
    intro y hy
    exact Subgroup.subset_closure (Or.inl hy)
  have hxB₁ : x ∈ B₁ := by
    exact Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
  have hA_conj_x : ∀ a : R, a ∈ A → a * x * a⁻¹ ∈ B₁ := by
    have hΩ_le_A : ΩA ≤ A := by
      simpa [ΩA] using Subgroup.map_subtype_le (omega₁ (G := A) (p := p))
    have hB₁_le_H : B₁ ≤ H := by
      refine (Subgroup.closure_le (K := H)).2 ?_
      intro y hy
      rcases hy with hyΩ | hyx
      · exact Subgroup.subset_closure (Or.inl (hΩ_le_A hyΩ))
      · have hy_eq : y = x := by simpa using hyx
        rw [hy_eq]
        exact Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
    have hBpow : ∀ b : B₁, b ^ p = 1 := by
      simpa [ΩA, B₁] using
        closure_omega_adjoin_pow_eq_one
          (R := R) (p := p) (A := A) hAcomm (x := x) hxC hxpow
    let N : Subgroup R := H ⊓ Subgroup.normalizer (B₁ : Set R)
    let Nsub : Subgroup H := N.subgroupOf H
    have hB₁_le_norm : B₁ ≤ Subgroup.normalizer (B₁ : Set R) := B₁.le_normalizer
    have hB₁_le_N : B₁ ≤ N := le_inf hB₁_le_H hB₁_le_norm
    have hB₁_norm_N : (B₁.subgroupOf N).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hB₁_le_N]
      exact inf_le_right
    have hconj_B₁_of_norm_Nsub :
        ∀ g : H, g ∈ Subgroup.normalizer (Nsub : Set H) →
          ∀ y : R, y ∈ B₁ → (g : R) * y * (g : R)⁻¹ ∈ B₁ := by
      intro g hg_norm y hyB₁
      let yH : H := ⟨y, hB₁_le_H hyB₁⟩
      have hyNsub : yH ∈ Nsub := by
        change y ∈ N
        exact hB₁_le_N hyB₁
      have hconjNsub : g * yH * g⁻¹ ∈ Nsub :=
        (Subgroup.mem_normalizer_iff.mp hg_norm yH).1 hyNsub
      have hconjN : (g : R) * y * (g : R)⁻¹ ∈ N := by
        have hconjNraw : ((g * yH * g⁻¹ : H) : R) ∈ N := by
          change ((g * yH * g⁻¹ : H) : R) ∈ N at hconjNsub
          exact hconjNsub
        have hconjN' : (g : R) * (y * (g : R)⁻¹) ∈ N := by
          simpa [yH, mul_assoc] using hconjNraw
        simpa [mul_assoc] using hconjN'
      have hypow : y ^ p = 1 := by
        have hyBpow : (⟨y, hyB₁⟩ : B₁) ^ p = 1 := hBpow ⟨y, hyB₁⟩
        simpa using congrArg Subtype.val hyBpow
      have hconjpow : ((g : R) * y * (g : R)⁻¹) ^ p = 1 := by
        have hconjpow' : ((MulAut.conj (g : R)).toMonoidHom y) ^ p = 1 := by
          calc
            ((MulAut.conj (g : R)).toMonoidHom y) ^ p =
                (MulAut.conj (g : R)).toMonoidHom (y ^ p) := by
                  exact (map_pow (MulAut.conj (g : R)).toMonoidHom y p).symm
            _ = 1 := by simp [hypow]
        simpa [MulAut.conj_apply, mul_assoc] using hconjpow'
      exact
        intermediate_order_p_mem_closure_omega_adjoin_of_normal
          (R := R) (p := p) hpodd (A := A) hAcomm (x := x) hxC hxpow
          (M := N) (by simpa [ΩA, B₁] using hB₁_le_N)
          (by exact inf_le_left)
          (by simpa [ΩA, B₁, N] using hB₁_norm_N)
          ((g : R) * y * (g : R)⁻¹) hconjN hconjpow
    have hNsub_norm_le : Subgroup.normalizer (Nsub : Set H) ≤ Nsub := by
      intro g hg_norm
      have hg_norm_B₁ : (g : R) ∈ Subgroup.normalizer (B₁ : Set R) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hyB₁
          exact hconj_B₁_of_norm_Nsub g hg_norm y hyB₁
        · intro hy_conj
          have hg_inv_norm : g⁻¹ ∈ Subgroup.normalizer (Nsub : Set H) :=
            (Subgroup.normalizer (Nsub : Set H)).inv_mem hg_norm
          have hback :=
            hconj_B₁_of_norm_Nsub g⁻¹ hg_inv_norm
              ((g : R) * y * (g : R)⁻¹) hy_conj
          simpa [mul_assoc] using hback
      change (g : R) ∈ N
      exact ⟨g.2, hg_norm_B₁⟩
    have hNsub_self : Subgroup.normalizer (Nsub : Set H) = Nsub :=
      le_antisymm hNsub_norm_le Nsub.le_normalizer
    have : Fact (IsPGroup p H) := ⟨(Fact.out : IsPGroup p R).to_subgroup H⟩
    have hH_nil : Group.IsNilpotent H :=
      IsPGroup.isNilpotent (p := p) (G := H) (h := Fact.out)
    let : Group.IsNilpotent H := hH_nil
    have hnc : NormalizerCondition H := Group.normalizerCondition_of_isNilpotent (G := H)
    have hNsub_top : Nsub = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc)
        Nsub hNsub_self
    have hH_le_norm_B₁ : H ≤ Subgroup.normalizer (B₁ : Set R) := by
      intro y hyH
      let yH : H := ⟨y, hyH⟩
      have hyNsub : yH ∈ Nsub := by
        rw [hNsub_top]
        simp
      change y ∈ N at hyNsub
      exact hyNsub.2
    intro a ha
    have haH : a ∈ H := Subgroup.subset_closure (Or.inl ha)
    exact (Subgroup.mem_normalizer_iff.mp (hH_le_norm_B₁ haH) x).1 hxB₁
  have hA_le_norm_B₁ : A ≤ Subgroup.normalizer (B₁ : Set R) := by
    refine subgroup_le_normalizer_of_conj_mem B₁ A ?_
    intro a y hyB₁
    refine Subgroup.closure_induction
      (p := fun y _hy => (a : R) * y * (a : R)⁻¹ ∈ B₁)
      (x := y) ?_ ?_ ?_ ?_ hyB₁
    · intro y hy
      rcases hy with hyΩ | hyx
      · exact hΩ_le_B₁ (hΩ_norm.conj_mem y hyΩ (a : R))
      · have hy_eq : y = x := by simpa using hyx
        rw [hy_eq]
        exact hA_conj_x (a : R) a.2
    · simp
    · intro y z _hy _hz hy_conj hz_conj
      simpa [mul_assoc] using B₁.mul_mem hy_conj hz_conj
    · intro y _hy hy_conj
      simpa [mul_assoc] using B₁.inv_mem hy_conj
  have hx_norm_B₁ : x ∈ Subgroup.normalizer (B₁ : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyB₁
      refine Subgroup.closure_induction
        (p := fun y _hy => x * y * x⁻¹ ∈ B₁)
        (x := y) ?_ ?_ ?_ ?_ hyB₁
      · intro y hy
        rcases hy with hyΩ | hyx
        · have hcomm : y * x = x * y :=
            (Subgroup.mem_centralizer_iff.mp hxC) y hyΩ
          have hconj_eq : x * y * x⁻¹ = y := by
            calc
              x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [hcomm]
              _ = y := by simp [mul_assoc]
          rw [hconj_eq]
          exact hΩ_le_B₁ hyΩ
        · have hy_eq : y = x := by simpa using hyx
          rw [hy_eq]
          simpa [mul_assoc] using hxB₁
      · simp
      · intro y z _hy _hz hy_conj hz_conj
        simpa [mul_assoc] using B₁.mul_mem hy_conj hz_conj
      · intro y _hy hy_conj
        simpa [mul_assoc] using B₁.inv_mem hy_conj
    · intro hyB₁
      have hback : ∀ z : R, z ∈ B₁ → x⁻¹ * z * x ∈ B₁ := by
        intro z hzB₁
        refine Subgroup.closure_induction
          (p := fun z _hz => x⁻¹ * z * x ∈ B₁)
          (x := z) ?_ ?_ ?_ ?_ hzB₁
        · intro z hz
          rcases hz with hzΩ | hzx
          · have hcomm : z * x = x * z :=
              (Subgroup.mem_centralizer_iff.mp hxC) z hzΩ
            have hconj_eq : x⁻¹ * z * x = z := by
              calc
                x⁻¹ * z * x = x⁻¹ * (z * x) := by simp [mul_assoc]
                _ = x⁻¹ * (x * z) := by rw [hcomm]
                _ = z := by simp
            rw [hconj_eq]
            exact hΩ_le_B₁ hzΩ
          · have hz_eq : z = x := by simpa using hzx
            rw [hz_eq]
            simpa [mul_assoc] using hxB₁
        · simp
        · intro u v _hu _hv hu_conj hv_conj
          simpa [mul_assoc] using B₁.mul_mem hu_conj hv_conj
        · intro z _hz hz_conj
          simpa [mul_assoc] using B₁.inv_mem hz_conj
      have hy_eq : y = x⁻¹ * (x * y * x⁻¹) * x := by
        simp [mul_assoc]
      rw [hy_eq]
      exact hback (x * y * x⁻¹) hyB₁
  refine (Subgroup.closure_le (K := Subgroup.normalizer (B₁ : Set R))).2 ?_
  intro y hy
  rcases hy with hyA | hyx
  · exact hA_le_norm_B₁ hyA
  · have hy_eq : y = x := by simpa using hyx
    rw [hy_eq]
    exact hx_norm_B₁

private theorem CFSG.order_p_centralizer_stabilizes_omega₁_quotient
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hpodd : p ≠ 2)
    {A : Subgroup R} [A.Normal] (hAcomm : IsMulCommutative A) :
    ∀ x : R,
      x ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)) →
      x ^ p = 1 →
      ∀ a : R, a ∈ A → ⁅x, a⁆ ∈ (omega₁ (G := A) (p := p)).map A.subtype := by
  classical
  -- Gorenstein 5.4, Lemma 4.14 stabilization step.  For
  -- `B₁ = ⟨Ω₁(A), x⟩`, the replacement proof builds an index-`p`
  -- chain from `B₁` to `⟨A, x⟩`, proves `B₁` normal at each stage by
  -- identifying it with `Ω₁` of the current stage, and then reads the
  -- final normality statement as trivial action on `A / Ω₁(A)`.
  intro x hxC hxpow a ha
  let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
  let B₁ : Subgroup R := Subgroup.closure ((ΩA : Set R) ∪ {x})
  let H : Subgroup R := Subgroup.closure ((A : Set R) ∪ {x})
  by_cases hxA : x ∈ A
  · have hxΩ : x ∈ ΩA :=
      mem_omega₁_map_subtype_of_mem_pow_eq_one (A := A) hxA hxpow
    have hcomm : Commute x a :=
      setLike_mul_comm (s := A) hxA ha
    have hcomm_eq_one : ⁅x, a⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr hcomm
    rw [hcomm_eq_one]
    exact ΩA.one_mem
  have hB₁_inf_A_le : B₁ ⊓ A ≤ ΩA := by
    simpa [ΩA, B₁] using
      closure_omega_adjoin_inf_A_le_omega (R := R) (p := p) (A := A) (x := x) hxpow
  have hH_norm_B₁ : H ≤ Subgroup.normalizer (B₁ : Set R) := by
    simpa [ΩA, B₁, H] using
      closure_omega_adjoin_order_p_normalized_by_closure_adjoin
        (R := R) (p := p) hpodd (A := A) hAcomm hxC hxpow
  have hxB₁ : x ∈ B₁ := by
    exact Subgroup.subset_closure (Or.inr (by simp))
  have haH : a ∈ H := by
    exact Subgroup.subset_closure (Or.inl ha)
  have hconjB₁ : a * x * a⁻¹ ∈ B₁ :=
    (Subgroup.mem_normalizer_iff.mp (hH_norm_B₁ haH) x).1 hxB₁
  have hcomm_ax_B₁ : ⁅a, x⁆ ∈ B₁ := by
    rw [commutatorElement_def]
    exact B₁.mul_mem hconjB₁ (B₁.inv_mem hxB₁)
  have hcomm_xa_B₁ : ⁅x, a⁆ ∈ B₁ := by
    have hinv : ⁅x, a⁆ = ⁅a, x⁆⁻¹ := by
      exact (commutatorElement_inv a x).symm
    rw [hinv]
    exact B₁.inv_mem hcomm_ax_B₁
  have hcomm_xa_A : ⁅x, a⁆ ∈ A := by
    have hconjA : x * a * x⁻¹ ∈ A :=
      (inferInstance : A.Normal).conj_mem a ha x
    rw [commutatorElement_def]
    exact A.mul_mem hconjA (A.inv_mem ha)
  exact hB₁_inf_A_le ⟨hcomm_xa_B₁, hcomm_xa_A⟩

private theorem CFSG.pairwise_mul_pow_eq_one_of_order_p_centralizer_stabilizes_omega₁
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)]
    (hpodd : p ≠ 2) {A : Subgroup R} [A.Normal]
    (hAself : Subgroup.centralizer (A : Set R) = A)
    (hΩcomm : IsMulCommutative ((omega₁ (G := A) (p := p)).map A.subtype))
    (hstabilize :
      ∀ x : R,
        x ∈ Subgroup.centralizer
          ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)) →
        x ^ p = 1 →
        ∀ a : R, a ∈ A → ⁅x, a⁆ ∈ (omega₁ (G := A) (p := p)).map A.subtype) :
    ∀ u : R,
      u ∈ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)) →
      ∀ v : R,
        v ∈ Subgroup.centralizer
          ((((omega₁ (G := A) (p := p)).map A.subtype : Subgroup R) : Set R)) →
        u ^ p = 1 → v ^ p = 1 → (u * v) ^ p = 1 := by
  classical
  let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
  let C : Subgroup R := Subgroup.centralizer (ΩA : Set R)
  have hΩ_le_A : ΩA ≤ A := by
    simpa [ΩA] using Subgroup.map_subtype_le (omega₁ (G := A) (p := p))
  have hΩcomm' : IsMulCommutative ΩA := by
    simpa [ΩA] using hΩcomm
  have hmain :
      ∀ n : ℕ,
        ∀ u : R, u ∈ C → ∀ v : R, v ∈ C →
          u ^ p = 1 → v ^ p = 1 →
          Nat.card (Subgroup.closure ({u, v} : Set R)) ≤ n →
          (u * v) ^ p = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u huC v hvC hup hvp hcard_le
      by_contra hbad
      let T : Subgroup R := Subgroup.closure ({u, v} : Set R)
      have huT : u ∈ T := by
        dsimp [T]
        exact Subgroup.subset_closure (by simp)
      have hvT : v ∈ T := by
        dsimp [T]
        exact Subgroup.subset_closure (by simp)
      have hT_noncyc : ¬ IsCyclic T := by
        intro hTcyc
        let uT : T := ⟨u, huT⟩
        let vT : T := ⟨v, hvT⟩
        have hcomm_uv : Commute uT vT := by
          let : IsCyclic T := hTcyc
          exact (IsCyclic.isMulCommutative (α := T)).is_comm.comm uT vT
        have huTp : uT ^ p = 1 := by
          apply Subtype.ext
          simpa [uT] using hup
        have hvTp : vT ^ p = 1 := by
          apply Subtype.ext
          simpa [vT] using hvp
        have hprodT : (uT * vT) ^ p = 1 := by
          simpa [huTp, hvTp] using hcomm_uv.mul_pow p
        exact hbad (by simpa [uT, vT] using congrArg Subtype.val hprodT)
      let L : Subgroup R := Subgroup.closure ({v, u * v * u⁻¹} : Set R)
      let P : Subgroup R := Subgroup.closure ({u * v * u⁻¹, v⁻¹} : Set R)
      have hL_lt_T : L < T := by
        simpa [L, T] using
          (closure_pair_conj_lt_closure_pair_of_not_isCyclic
            (R := R) (p := p) (x := u) (y := v) hT_noncyc)
      have hP_le_L : P ≤ L := by
        dsimp [P, L]
        refine (Subgroup.closure_le (K := Subgroup.closure ({v, u * v * u⁻¹} : Set R))).2 ?_
        intro z hz
        rcases hz with hz | hz
        · have hz_eq : z = u * v * u⁻¹ := by simpa using hz
          rw [hz_eq]
          exact Subgroup.subset_closure (by simp)
        · have hz_eq : z = v⁻¹ := by simpa using hz
          rw [hz_eq]
          exact (Subgroup.closure ({v, u * v * u⁻¹} : Set R)).inv_mem
            (Subgroup.subset_closure (by simp))
      have hcard_L_lt_T : Nat.card L < Nat.card T := by
        have hle : Nat.card L ≤ Nat.card T := Subgroup.card_le_of_le hL_lt_T.le
        refine lt_of_le_of_ne hle ?_
        intro hcard_eq
        exact hL_lt_T.ne <|
          Subgroup.eq_of_le_of_card_ge hL_lt_T.le (le_of_eq hcard_eq.symm)
      have hcard_P_lt_T : Nat.card P < Nat.card T :=
        lt_of_le_of_lt (Subgroup.card_le_of_le hP_le_L) hcard_L_lt_T
      have hcard_P_lt_n : Nat.card P < n := lt_of_lt_of_le hcard_P_lt_T hcard_le
      have hconjC : u * v * u⁻¹ ∈ C := C.mul_mem (C.mul_mem huC hvC) (C.inv_mem huC)
      have hconjp : (u * v * u⁻¹) ^ p = 1 := by
        calc
          (u * v * u⁻¹) ^ p = u * v ^ p * u⁻¹ := by
            exact conj_pow
          _ = 1 := by simp [hvp]
      have hvInvC : v⁻¹ ∈ C := C.inv_mem hvC
      have hvInvp : v⁻¹ ^ p = 1 := by
        simpa [inv_pow] using congrArg Inv.inv hvp
      have hsmall :
          ((u * v * u⁻¹) * v⁻¹) ^ p = 1 :=
        ih (Nat.card P) hcard_P_lt_n
          (u * v * u⁻¹) hconjC v⁻¹ hvInvC hconjp hvInvp le_rfl
      have huv_pow : ⁅u, v⁆ ^ p = 1 := by
        simpa [commutatorElement_def, mul_assoc] using hsmall
      have hvu_pow : ⁅v, u⁆ ^ p = 1 := by
        have hinv : ⁅v, u⁆ = ⁅u, v⁆⁻¹ := by
          exact (commutatorElement_inv u v).symm
        rw [hinv, inv_pow, huv_pow]
        simp
      have hv_stab : ∀ a : R, a ∈ A → ⁅v, a⁆ ∈ ΩA := by
        simpa [ΩA, C] using hstabilize v hvC hvp
      have hu_stab : ∀ a : R, a ∈ A → ⁅u, a⁆ ∈ ΩA := by
        simpa [ΩA, C] using hstabilize u huC hup
      have hcomm_centA : ⁅v, u⁆ ∈ Subgroup.centralizer (A : Set R) :=
        commutator_mem_centralizer_of_stabilizes_omega_series
          (A := A) (Ω := ΩA) hΩ_le_A hΩcomm' hvC huC hv_stab hu_stab
      have hcommA : ⁅v, u⁆ ∈ A := by
        simpa [hAself] using hcomm_centA
      have hcommΩ : ⁅v, u⁆ ∈ ΩA := by
        simpa [ΩA] using
          mem_omega₁_map_subtype_of_mem_pow_eq_one (A := A) hcommA hvu_pow
      have hcomm_u : Commute ⁅v, u⁆ u :=
        Subgroup.mem_centralizer_iff.mp huC ⁅v, u⁆ hcommΩ
      have hcomm_v : Commute ⁅v, u⁆ v :=
        Subgroup.mem_centralizer_iff.mp hvC ⁅v, u⁆ hcommΩ
      exact hbad <|
        pth_mul_eq_one_of_commutator_centralizes_pair
          (G := R) (p := p) hpodd hup hvp hcomm_u hcomm_v
  intro u hu v hv hup hvp
  exact hmain (Nat.card (Subgroup.closure ({u, v} : Set R)))
    u (by simpa [C, ΩA] using hu) v (by simpa [C, ΩA] using hv) hup hvp le_rfl

private theorem CFSG.omega₁_map_subtype_pow_eq_one_of_pairwise_mul
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hpair :
      ∀ x : G, x ∈ H → ∀ y : G, y ∈ H →
        x ^ p = 1 → y ^ p = 1 → (x * y) ^ p = 1) :
    ∀ d : (omega₁ (G := H) (p := p)).map H.subtype, d ^ p = 1 := by
  intro d
  rcases Subgroup.mem_map.mp d.2 with ⟨z, hzΩ, hzd⟩
  apply Subtype.ext
  change (d : G) ^ p = 1
  rw [← hzd]
  change ((z : G) ^ p = 1)
  refine Subgroup.closure_induction
    (k := {u : H | u ^ (p ^ 1) = 1})
    (p := fun u _hu => ((u : H) : G) ^ p = 1)
    (x := z) ?_ ?_ ?_ ?_ hzΩ
  · intro u hu
    simpa [pow_one] using congrArg Subtype.val hu
  · simp
  · intro u v _hu _hv hup hvp
    exact hpair (u : G) u.2 (v : G) v.2 hup hvp
  · intro u _hu hup
    simpa [inv_pow] using congrArg Inv.inv hup

private theorem CFSG.gorenstein_5_4_14_centralizer_control_for_maximal_normal_abelian
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (_hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    {A : Subgroup R}
    (hAnorm : A.Normal) (hAcomm : IsMulCommutative A)
    (hAself : Subgroup.centralizer (A : Set R) = A)
    (_hArank : generatorRank A ≤ 2)
    (hAmaxRank :
      ∀ B : Subgroup R, B.Normal → IsMulCommutative B →
        generatorRank B ≤ generatorRank A)
    (hΩnorm : ((omega₁ (G := A) (p := p)).map A.subtype).Normal)
    (hΩelem : IsElementaryAbelian p ((omega₁ (G := A) (p := p)).map A.subtype))
    (_hΩcard : Nat.card ((omega₁ (G := A) (p := p)).map A.subtype) ≤ p ^ 2)
    {E : Subgroup R} (_hEcard : Nat.card E = p ^ 3) (hEelem : IsElementaryAbelian p E) :
    E ⊓ Subgroup.centralizer
        ((((omega₁ (G := A) (p := p)).map A.subtype) : Subgroup R) : Set R) ≤
      ((omega₁ (G := A) (p := p)).map A.subtype) := by
  -- This is the centralizer-control/replacement step cited in the text as the
  -- preceding Gorenstein lemma. The hypotheses above isolate exactly the
  -- maximal-normal-abelian and Ω₁(A) package already proved locally.
  intro x hx
  have hxpow : x ^ p = 1 := by
    let xE : E := ⟨x, hx.1⟩
    have hxEpow : xE ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p E) xE
    simpa [xE] using congrArg Subtype.val hxEpow
  have hxA : x ∈ A := by
    -- Remaining replacement step: an order-`p` element of the elementary
    -- abelian rank-three subgroup that centralizes `Ω₁(A)` must centralize
    -- `A`, hence lies in `A = C_R(A)`.
    by_contra hxnotA
    let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
    let D : Subgroup R :=
      (omega₁ (G := Subgroup.centralizer (ΩA : Set R)) (p := p)).map
        (Subgroup.centralizer (ΩA : Set R)).subtype
    have hxD : x ∈ D := by
      have hxC : x ∈ Subgroup.centralizer (ΩA : Set R) := by
        simpa [ΩA] using hx.2
      simpa [D] using
        mem_omega₁_centralizer_map_of_mem_pow_eq_one (Ω := ΩA) hxC hxpow
    have hΩ_le_D : ΩA ≤ D := by
      let : IsElementaryAbelian p ΩA := by
        simpa [ΩA] using hΩelem
      simpa [D] using
        subgroup_le_omega₁_centralizer_map_of_isElementaryAbelian
          (p := p) (Ω := ΩA)
    have hDnorm : D.Normal := by
      have : ΩA.Normal := by
        simpa [ΩA] using hΩnorm
      simpa [D] using omega₁_centralizer_map_normal_of_normal (p := p) (Ω := ΩA)
    have hΩ_le_A : ΩA ≤ A := by
      simpa [ΩA] using Subgroup.map_subtype_le (omega₁ (G := A) (p := p))
    have hx_not_Ω : x ∉ ΩA := fun hxΩ => hxnotA (hΩ_le_A hxΩ)
    have hΩ_ne_D : ΩA ≠ D := by
      intro hΩD
      exact hx_not_Ω (by simpa [hΩD] using hxD)
    have hΩ_lt_D : ΩA < D := lt_of_le_of_ne hΩ_le_D hΩ_ne_D
    have hD_le_C : D ≤ Subgroup.centralizer (ΩA : Set R) := by
      simpa [D] using
        Subgroup.map_subtype_le
          (omega₁ (G := Subgroup.centralizer (ΩA : Set R)) (p := p))
    have hΩ_lt_C : ΩA < Subgroup.centralizer (ΩA : Set R) :=
      lt_of_lt_of_le hΩ_lt_D hD_le_C
    let : Fact (IsPGroup p R) := ⟨hRp⟩
    have hΩcomm : IsMulCommutative ΩA := hΩelem.toIsMulCommutative
    obtain ⟨B, hΩ_le_B, hBnorm, hBcomm, hBquot_card, hB_le_D⟩ :=
      exists_abelian_normal_prime_index_overgroup_between_of_lt
        (R := R) (p := p) (E := ΩA) (L := D)
        (by simpa [ΩA] using hΩnorm) hΩcomm hDnorm hΩ_le_D hD_le_C hΩ_lt_D
    have hΩcard_eq : Nat.card ΩA = p ^ generatorRank A := by
      have : Fact (IsPGroup p A) := ⟨hRp.to_subgroup A⟩
      let : IsMulCommutative A := hAcomm
      calc
        Nat.card ΩA = Nat.card (omega₁ (G := A) (p := p)) := by
          simpa [ΩA] using (Subgroup.card_map_of_injective
            (K := omega₁ (G := A) (p := p)) (f := A.subtype)
            A.subtype_injective)
        _ = p ^ generatorRank A :=
          omega₁_card_eq_pow_generatorRank_of_commutative_pgroup (p := p) A
    have hBcard_eq : Nat.card B = p ^ (generatorRank A + 1) := by
      have : (ΩA.subgroupOf B).Normal := by
        exact Subgroup.Normal.subgroupOf (G := R)
          (hH := by simpa [ΩA] using hΩnorm) B
      have hmul :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (α := B) (s := ΩA.subgroupOf B)
      have hΩsubB_card : Nat.card (ΩA.subgroupOf B) = Nat.card ΩA := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := ΩA) (K := B) hΩ_le_B).toEquiv
      calc
        Nat.card B = Nat.card (B ⧸ ΩA.subgroupOf B) * Nat.card (ΩA.subgroupOf B) := by
          simpa using hmul
        _ = p * Nat.card ΩA := by rw [hBquot_card, hΩsubB_card]
        _ = p * p ^ generatorRank A := by rw [hΩcard_eq]
        _ = p ^ (generatorRank A + 1) := by
          rw [pow_succ']
    have hDpow : ∀ d : D, d ^ p = 1 := by
      -- Thompson replacement core from `docs/G_5_4.tex`, Lemma 4.14:
      -- every order-`p` element of `C_R(Ω₁(A))` stabilizes
      -- `A ≥ Ω₁(A) ≥ 1`; Lemma 4.13 then forces commutators of such
      -- elements into `C_R(A)=A`, and the minimal-pair argument shows
      -- `D = Ω₁(C_R(Ω₁(A)))` has exponent `p`.
      let C : Subgroup R := Subgroup.centralizer (ΩA : Set R)
      have hstabilize :
          ∀ x : R, x ∈ C → x ^ p = 1 → ∀ a : R, a ∈ A → ⁅x, a⁆ ∈ ΩA := by
        intro y hyC hypow a ha
        simpa [C, ΩA] using
          order_p_centralizer_stabilizes_omega₁_quotient
            (R := R) (p := p) hpodd (A := A) hAcomm
            y (by simpa [C, ΩA] using hyC) hypow a ha
      have hpair :
          ∀ u : R, u ∈ C → ∀ v : R, v ∈ C →
            u ^ p = 1 → v ^ p = 1 → (u * v) ^ p = 1 := by
        intro u huC v hvC hup hvp
        simpa [C, ΩA] using
          pairwise_mul_pow_eq_one_of_order_p_centralizer_stabilizes_omega₁
            (R := R) (p := p) hpodd (A := A) hAself
            (by simpa [ΩA] using hΩcomm)
            (by simpa [C, ΩA] using hstabilize)
            u (by simpa [C, ΩA] using huC)
            v (by simpa [C, ΩA] using hvC) hup hvp
      simpa [D, C] using
        omega₁_map_subtype_pow_eq_one_of_pairwise_mul
          (G := R) (p := p) (H := C) hpair
    have hBpow : ∀ b : B, b ^ p = 1 := by
      intro b
      have hbD : (b : R) ∈ D := hB_le_D b.2
      have hbpowR : (b : R) ^ p = 1 := by
        exact congrArg (fun d : D => (d : R)) (hDpow ⟨(b : R), hbD⟩)
      apply Subtype.ext
      exact hbpowR
    have hBelem : IsElementaryAbelian p B := by
      refine
        { toIsMulCommutative := hBcomm
          exponent_dvd_p := ?_ }
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hBpow
    let : IsElementaryAbelian p B := hBelem
    have hBcard_pow : Nat.card B = p ^ generatorRank B :=
      elementaryAbelian_card_eq_pow_generatorRank_local (p := p) B
    have hBgen_eq : generatorRank B = generatorRank A + 1 := by
      have hpow_eq : p ^ generatorRank B = p ^ (generatorRank A + 1) := by
        calc
          p ^ generatorRank B = Nat.card B := hBcard_pow.symm
          _ = p ^ (generatorRank A + 1) := hBcard_eq
      exact (Nat.pow_right_injective (show 2 ≤ p from (Fact.out : Nat.Prime p).two_le)) hpow_eq
    have hBgen_le_A : generatorRank B ≤ generatorRank A :=
      hAmaxRank B hBnorm hBcomm
    omega
  exact mem_omega₁_map_subtype_of_mem_pow_eq_one (A := A) hxA hxpow

private theorem CFSG.gorenstein_5_4_15_preceding_lemma_package
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅) :
    ∃ A : Subgroup R,
      A.Normal ∧ IsMulCommutative A ∧ Subgroup.centralizer (A : Set R) = A ∧
        generatorRank A ≤ 2 ∧
        ((omega₁ (G := A) (p := p)).map A.subtype).Normal ∧
        IsElementaryAbelian p ((omega₁ (G := A) (p := p)).map A.subtype) ∧
        Nat.card ((omega₁ (G := A) (p := p)).map A.subtype) ≤ p ^ 2 ∧
        ∀ {E : Subgroup R}, Nat.card E = p ^ 3 → IsElementaryAbelian p E →
          E ⊓ Subgroup.centralizer
              ((((omega₁ (G := A) (p := p)).map A.subtype) : Subgroup R) : Set R) ≤
            ((omega₁ (G := A) (p := p)).map A.subtype) := by
  classical
  let : Fact (IsPGroup p R) := ⟨hRp⟩
  obtain ⟨A0, hA0norm, hA0comm, hA0maxRank⟩ :=
    exists_max_generatorRank_normal_abelian_subgroup_local (G := R)
  obtain ⟨A, hA0_le_A, hAnorm, hAcomm, hAmax⟩ :=
    exists_maximal_normal_abelian_subgroup_containing (G := R) A0 hA0norm hA0comm
  let : A.Normal := hAnorm
  have hAcent_le : Subgroup.centralizer (A : Set R) ≤ A :=
    maximal_normal_abelian_selfCentralizing_local (G := R) (p := p) A hAnorm hAcomm hAmax
  have hA_le_cent : A ≤ Subgroup.centralizer (A : Set R) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  have hAself : Subgroup.centralizer (A : Set R) = A := le_antisymm hAcent_le hA_le_cent
  have hA0_rank_le_A : generatorRank A0 ≤ generatorRank A :=
    generatorRank_le_of_le_commutative_pgroup_local
      (R := R) (p := p) hA0comm hAcomm hA0_le_A
  have hAmaxRank :
      ∀ B : Subgroup R, B.Normal → IsMulCommutative B →
        generatorRank B ≤ generatorRank A := by
    intro B hBnorm hBcomm
    exact (hA0maxRank B hBnorm hBcomm).trans hA0_rank_le_A
  have hArank : generatorRank A ≤ 2 := by
    by_contra hnot
    have hA_rank_three : 3 ≤ generatorRank A := by omega
    have hA_mem : A ∈ selfCentralizingAbelianSubgroupsAtLeast R 3 := by
      exact ⟨⟨hAnorm, hAself⟩, hA_rank_three⟩
    have hA_empty : A ∈ (∅ : Set (Subgroup R)) := by
      rw [hA3] at hA_mem
      exact hA_mem
    exact hA_empty
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
  let ΩA : Subgroup R := Ωsub.map A.subtype
  have hΩnorm : ΩA.Normal := by
    let : Ωsub.Characteristic := by
      simpa [Ωsub] using (omega₁_characteristic (G := A) (p := p))
    simpa [ΩA, Ωsub] using (inferInstance : (Ωsub.map A.subtype).Normal)
  have hΩsub_elem : IsElementaryAbelian p Ωsub := by
    let : IsMulCommutative A := hAcomm
    simpa [Ωsub] using omega₁_isElementaryAbelian_of_commutative_local (p := p) A
  let : IsElementaryAbelian p Ωsub := hΩsub_elem
  have hΩelem : IsElementaryAbelian p ΩA := by
    simpa [ΩA, Ωsub] using
      isElementaryAbelian_map_of_injective_local (p := p) A.subtype A.subtype_injective
  have hΩcard : Nat.card ΩA ≤ p ^ 2 := by
    have hΩcard_eq : Nat.card ΩA = Nat.card Ωsub := by
      simpa [ΩA, Ωsub] using
        (Subgroup.card_map_of_injective (K := Ωsub) (f := A.subtype) A.subtype_injective)
    have : Fact (IsPGroup p A) := ⟨hRp.to_subgroup A⟩
    have hΩsub_card_eq :
        Nat.card Ωsub = Nat.card (A ⧸ frattini A) := by
      let : IsMulCommutative A := hAcomm
      simpa [Ωsub] using
        omega₁_card_eq_card_quotient_frattini_of_commutative_local (p := p) A
    have hquot_gen_le : generatorRank (A ⧸ frattini A) ≤ generatorRank A :=
      generatorRank_le_of_surjective
        (G := A) (H := A ⧸ frattini A) (QuotientGroup.mk' (frattini A))
        (QuotientGroup.mk'_surjective (frattini A))
    have hquot_gen_le_two : generatorRank (A ⧸ frattini A) ≤ 2 :=
      hquot_gen_le.trans hArank
    have hquot_elem : IsElementaryAbelian p (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p)
    let : IsElementaryAbelian p (A ⧸ frattini A) := hquot_elem
    have hquot_card_le : Nat.card (A ⧸ frattini A) ≤ p ^ 2 := by
      let Q : Type _ := A ⧸ frattini A
      have hpow : ∀ q : Q, q ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p Q)
      have hcard_dvd : Nat.card Q ∣ p ^ Group.rank Q :=
        card_dvd_exponent_pow_rank' (G := Q) (n := p) hpow
      have hGrank_le_two : Group.rank Q ≤ 2 := by
        simpa [Q, generatorRank_eq_group_rank] using hquot_gen_le_two
      have hpow_dvd : p ^ Group.rank Q ∣ p ^ 2 :=
        (Nat.pow_dvd_pow_iff_le_right (Fact.out : Nat.Prime p).one_lt).2 hGrank_le_two
      have hcard_dvd_sq : Nat.card Q ∣ p ^ 2 := hcard_dvd.trans hpow_dvd
      exact Nat.le_of_dvd (pow_pos (Fact.out : Nat.Prime p).pos 2) hcard_dvd_sq
    calc
      Nat.card ΩA = Nat.card Ωsub := hΩcard_eq
      _ = Nat.card (A ⧸ frattini A) := hΩsub_card_eq
      _ ≤ p ^ 2 := hquot_card_le
  refine ⟨A, hAnorm, hAcomm, hAself, hArank, ?_, ?_, ?_, ?_⟩
  · simpa [ΩA, Ωsub] using hΩnorm
  · simpa [ΩA, Ωsub] using hΩelem
  · simpa [ΩA, Ωsub] using hΩcard
  · intro E hEcard hEelem
    exact
      gorenstein_5_4_14_centralizer_control_for_maximal_normal_abelian
        (R := R) (p := p) hpodd hRp hA3 hAnorm hAcomm hAself hArank
        hAmaxRank
        (by simpa [ΩA, Ωsub] using hΩnorm)
        (by simpa [ΩA, Ωsub] using hΩelem)
        (by simpa [ΩA, Ωsub] using hΩcard)
        hEcard hEelem

private theorem CFSG.not_exists_elementaryAbelian_order_p_cubed_of_A3_empty
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅) :
    ¬ ∃ E : Subgroup R, Nat.card E = p ^ 3 ∧ IsElementaryAbelian p E := by
  classical
  let : Fact (IsPGroup p R) := ⟨hRp⟩
  obtain ⟨A, _hAnorm, _hAcomm, _hAself, _hArank, hΩnorm, hΩelem, hΩcard, hcentral⟩ :=
    gorenstein_5_4_15_preceding_lemma_package (R := R) (p := p) hpodd hRp hA3
  let ΩA : Subgroup R := (omega₁ (G := A) (p := p)).map A.subtype
  have hΩnorm' : ΩA.Normal := by
    simpa [ΩA] using hΩnorm
  let : ΩA.Normal := hΩnorm'
  have hΩelem' : IsElementaryAbelian p ΩA := by
    simpa [ΩA] using hΩelem
  let : IsElementaryAbelian p ΩA := hΩelem'
  have hΩcard' : Nat.card ΩA ≤ p ^ 2 := by
    simpa [ΩA] using hΩcard
  rintro ⟨E, hEcard, hEelem⟩
  let : IsElementaryAbelian p E := hEelem
  let φ : E →* MulAut ΩA := (MulAut.conjNormal (H := ΩA)).comp E.subtype
  have hφ_range_p : IsPGroup p φ.range := by
    have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
    have hEtop : IsPGroup p (⊤ : Subgroup E) := by
      simpa using hEp.to_subgroup (⊤ : Subgroup E)
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup E)) hEtop φ
  have hφcard : Nat.card φ.range ≤ p :=
    natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
      (A := ΩA) (p := p) hφ_range_p hΩcard'
  have hquot_card : Nat.card (E ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hker_ge : p ^ 2 ≤ Nat.card φ.ker := by
    have hmul :
        Nat.card E = Nat.card (E ⧸ φ.ker) * Nat.card φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (s := φ.ker)
    have hmul_le : p ^ 3 ≤ p * Nat.card φ.ker := by
      calc
        p ^ 3 = Nat.card E := hEcard.symm
        _ = Nat.card (E ⧸ φ.ker) * Nat.card φ.ker := hmul
        _ = Nat.card φ.range * Nat.card φ.ker := by rw [hquot_card]
        _ ≤ p * Nat.card φ.ker := Nat.mul_le_mul_right _ hφcard
    have hmul_le' : p * (p ^ 2) ≤ p * Nat.card φ.ker := by
      simpa [pow_succ', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul_le
    exact Nat.le_of_mul_le_mul_left hmul_le' (Fact.out : Nat.Prime p).pos
  have hcentral' : E ⊓ Subgroup.centralizer (ΩA : Set R) ≤ ΩA := by
    simpa [ΩA] using hcentral (E := E) hEcard hEelem
  have hker_image_le_inf :
      φ.ker.map E.subtype ≤ E ⊓ Subgroup.centralizer (ΩA : Set R) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨e, heker, rfl⟩
    refine ⟨e.2, ?_⟩
    change (e : R) ∈ Subgroup.centralizer (ΩA : Set R)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yΩ : ΩA := ⟨y, hy⟩
    have hfix : φ e yΩ = yΩ := by
      have heq : φ e = 1 := by
        simpa [MonoidHom.mem_ker] using heker
      simp [heq]
    have hconj : (e : R) * y * (e : R)⁻¹ = y := by
      simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hfix
    have hmul : (e : R) * y = y * (e : R) := by
      simpa [mul_assoc] using congrArg (fun t : R => t * (e : R)) hconj
    exact hmul.symm
  have hker_image_le : φ.ker.map E.subtype ≤ ΩA :=
    hker_image_le_inf.trans hcentral'
  have hker_image_card :
      Nat.card (φ.ker.map E.subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective (K := φ.ker) (f := E.subtype) E.subtype_injective
  have hker_card_le_Ω : Nat.card φ.ker ≤ Nat.card ΩA := by
    rw [← hker_image_card]
    exact Subgroup.card_le_of_le hker_image_le
  have hker_card_eq : Nat.card φ.ker = p ^ 2 :=
    le_antisymm (hker_card_le_Ω.trans hΩcard') hker_ge
  have hΩ_card_eq : Nat.card ΩA = p ^ 2 := by
    apply le_antisymm hΩcard'
    calc
      p ^ 2 ≤ Nat.card φ.ker := hker_ge
      _ = Nat.card (φ.ker.map E.subtype) := hker_image_card.symm
      _ ≤ Nat.card ΩA := Subgroup.card_le_of_le hker_image_le
  have hΩ_card_le_ker_image : Nat.card ΩA ≤ Nat.card (φ.ker.map E.subtype) := by
    rw [hΩ_card_eq, hker_image_card, hker_card_eq]
  have hker_image_eq_Ω : φ.ker.map E.subtype = ΩA :=
    Subgroup.eq_of_le_of_card_ge hker_image_le hΩ_card_le_ker_image
  have htop_le_ker : (⊤ : Subgroup E) ≤ φ.ker := by
    intro e _he
    rw [MonoidHom.mem_ker]
    ext y
    have hyker : (y : R) ∈ φ.ker.map E.subtype := by
      simp [hker_image_eq_Ω, y.2]
    rcases Subgroup.mem_map.mp hyker with ⟨k, hkker, hky⟩
    have hcommE : e * k = k * e :=
      (IsMulCommutative.is_comm (M := E)).comm e k
    have hcommR : (e : R) * (k : R) = (k : R) * (e : R) :=
      congrArg Subtype.val hcommE
    have hconj : (e : R) * (y : R) * (e : R)⁻¹ = (y : R) := by
      rw [← hky]
      calc
        (e : R) * (k : R) * (e : R)⁻¹ =
            ((k : R) * (e : R)) * (e : R)⁻¹ := by rw [hcommR]
        _ = (k : R) := by simp [mul_assoc]
    simpa [φ, MulAut.conjNormal_apply] using hconj
  have hker_top : φ.ker = ⊤ := top_unique htop_le_ker
  have htop_card : Nat.card (⊤ : Subgroup E) = Nat.card E :=
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv
  have hp2_eq_p3 : p ^ 2 = p ^ 3 := by
    calc
      p ^ 2 = Nat.card φ.ker := hker_card_eq.symm
      _ = Nat.card (⊤ : Subgroup E) := by rw [hker_top]
      _ = Nat.card E := htop_card
      _ = p ^ 3 := hEcard
  have h23 : (2 : Nat) = 3 :=
    (Nat.pow_right_injective (show 2 ≤ p from (Fact.out : Nat.Prime p).two_le)) hp2_eq_p3
  omega

private theorem CFSG.exists_selfCentralizingAbelianSubgroupAtLeast_three_of_two_lt_groupRank
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R) (hrank : 2 < groupRank R) :
    ∃ A : Subgroup R, A ∈ selfCentralizingAbelianSubgroupsAtLeast R 3 := by
  classical
  by_contra hnone
  have hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅ := by
    ext A
    simp only [Set.mem_empty_iff_false]
    constructor
    · intro hA
      exact False.elim (hnone ⟨A, hA⟩)
    · intro hA
      exact False.elim hA
  have hnoE :
      ¬ ∃ E : Subgroup R, Nat.card E = p ^ 3 ∧ IsElementaryAbelian p E :=
    not_exists_elementaryAbelian_order_p_cubed_of_A3_empty
      (R := R) (p := p) hpodd hRp hA3
  obtain ⟨E, hEcard, hEelem⟩ :=
    exists_elementaryAbelian_subgroup_order_p_cubed_of_two_lt_groupRank
      (R := R) (p := p) hRp hrank
  exact hnoE ⟨E, hEcard, hEelem⟩

private theorem CFSG.gorenstein_theorem_5_4_15_rank
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅) :
    groupRank R ≤ 2 := by
  by_contra hrank_not
  have hrank_gt : 2 < groupRank R := lt_of_not_ge hrank_not
  obtain ⟨A, hA⟩ :=
    exists_selfCentralizingAbelianSubgroupAtLeast_three_of_two_lt_groupRank
      (R := R) (p := p) hpodd hRp hrank_gt
  have hAempty : A ∈ (∅ : Set (Subgroup R)) := by
    simp [hA3] at hA
  exact hAempty

private theorem CFSG.gorenstein_theorem_5_4_15_automorphism_dvd
    {R : Type*} [Group R] [Finite R] {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    (ψ : MulAut R) (hψ_order : orderOf ψ = q) (hq_ne : q ≠ p) :
    q ∣ p ^ 2 - 1 := by
  classical
  by_cases hRsub : Subsingleton R
  · let : Subsingleton R := hRsub
    have hψ_one : ψ = 1 := by
      ext x
      exact Subsingleton.elim _ _
    have hq_one : q = 1 := by simpa [hψ_one] using hψ_order.symm
    exact False.elim ((Fact.out : Nat.Prime q).ne_one hq_one)
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hRsub
    let : Fact (IsPGroup p R) := ⟨hRp⟩
    have hrank : groupRank R ≤ 2 :=
      gorenstein_theorem_5_4_15_rank (R := R) (p := p) hpodd hRp hA3
    obtain ⟨H, hHchar, _hHcomm, _hHnil, hHexp, hHfix_p⟩ :=
      theorem_1_13 (G := R) (p := p) hpodd
    let : H.Characteristic := hHchar
    let : H.Normal := inferInstance
    have hHp : IsPGroup p H := hRp.to_subgroup H
    let : Fact (IsPGroup p H) := ⟨hHp⟩
    have hHrank : groupRank H ≤ 2 :=
      (groupRank_le_of_subgroup (R := R) H).trans hrank
    have hHquot_card : Nat.card (H ⧸ frattini H) ≤ p ^ 2 :=
      natCard_frattini_quotient_le_p_sq_of_groupRank_le_two_and_exponent_p
        (R := H) (p := p) hHrank hHexp
    have hψ_not_fix_H : ¬ ∀ x : R, x ∈ H → ψ x = x := by
      intro hfix
      let Afix : Subgroup (MulAut R) := fixingSubgroup (M := MulAut R) (α := R) (H : Set R)
      have hψ_mem : ψ ∈ Afix := by
        exact (mem_fixingSubgroup_iff (M := MulAut R) (s := (H : Set R))).2 hfix
      let ψfix : Afix := ⟨ψ, hψ_mem⟩
      have hψfix_order : orderOf ψfix = q := by
        calc
          orderOf ψfix = orderOf (ψfix : MulAut R) := (Subgroup.orderOf_coe (H := Afix) ψfix).symm
          _ = orderOf ψ := rfl
          _ = q := hψ_order
      have hq_dvd_Afix : q ∣ Nat.card Afix := by
        rw [← hψfix_order]
        exact orderOf_dvd_natCard ψfix
      obtain ⟨n, hAfix_card⟩ := hHfix_p.exists_card_eq
      have hAfix_card' : Nat.card Afix = p ^ n := by
        simpa [Afix] using hAfix_card
      have hq_dvd_pow : q ∣ p ^ n := by simpa [hAfix_card'] using hq_dvd_Afix
      have hq_eq_p : q = p :=
        Nat.prime_eq_prime_of_dvd_pow (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p) hq_dvd_pow
      exact hq_ne hq_eq_p
    let Aψ : Subgroup (MulAut R) := Subgroup.zpowers ψ
    let : MulDistribMulAction Aψ R := inferInstance
    have hAψ_card : Nat.card Aψ = q := by
      change Nat.card (Subgroup.zpowers ψ) = q
      rw [Nat.card_zpowers, hψ_order]
    have hcop_Aψ_H : Nat.Coprime (Nat.card Aψ) (Nat.card H) := by
      obtain ⟨n, hHcard⟩ := hHp.exists_card_eq
      have hq_coprime_p : Nat.Coprime q p :=
        (Nat.coprime_primes (Fact.out : Nat.Prime q) (Fact.out : Nat.Prime p)).2 hq_ne
      simpa [hAψ_card, hHcard] using hq_coprime_p.pow_right n
    have hHinv : IsInvariant Aψ R H :=
      isInvariant_of_characteristic (A := Aψ) (G := R) H
    let : IsInvariant Aψ R H := hHinv
    let : MulDistribMulAction Aψ H := inferInstance
    have hΦinv : IsInvariant Aψ H (frattini H) :=
      isInvariant_of_characteristic (A := Aψ) (G := H) (frattini H)
    let : MulDistribMulAction Aψ (H ⧸ frattini H) :=
      quotientMulDistribMulAction (A := Aψ) (G := H) (frattini H) hΦinv
    let aψ : Aψ := ⟨ψ, Subgroup.mem_zpowers ψ⟩
    let σbar : MulAut (H ⧸ frattini H) :=
      MulDistribMulAction.toMulAut Aψ (H ⧸ frattini H) aψ
    have hσ_dvd_q : orderOf σbar ∣ q := by
      have hmap_dvd :
          orderOf (MulDistribMulAction.toMulAut Aψ (H ⧸ frattini H) aψ) ∣ orderOf aψ :=
        orderOf_map_dvd (MulDistribMulAction.toMulAut Aψ (H ⧸ frattini H)) aψ
      have haψ_order : orderOf aψ = q := by
        calc
          orderOf aψ = orderOf (aψ : MulAut R) := (Subgroup.orderOf_coe (H := Aψ) aψ).symm
          _ = orderOf ψ := rfl
          _ = q := hψ_order
      simpa [σbar, haψ_order] using hmap_dvd
    have hσ_ne_one : σbar ≠ 1 := by
      intro hσ_one
      have hquot_triv : ActsTrivially (A := Aψ) (G := H ⧸ frattini H) := by
        intro a x
        let ρ : Aψ →* MulAut (H ⧸ frattini H) :=
          MulDistribMulAction.toMulAut Aψ (H ⧸ frattini H)
        rcases Subgroup.mem_zpowers_iff.mp a.2 with ⟨n, hn⟩
        have ha_eq : a = aψ ^ n := by
          apply Subtype.ext
          simpa [aψ] using hn.symm
        have hρa : ρ a = 1 := by
          calc
            ρ a = ρ (aψ ^ n) := by rw [ha_eq]
            _ = ρ aψ ^ n := by simp
            _ = 1 := by simp [ρ, σbar, hσ_one]
        have hx := congrArg (fun f : MulAut (H ⧸ frattini H) => f x) hρa
        simpa [ρ, MulDistribMulAction.toMulAut_apply] using hx
      have htrivH : ActsTrivially (A := Aψ) (G := H) :=
        theorem_1_8 (R := H) (A := Aψ) (p := p) hcop_Aψ_H (by simpa using hquot_triv)
      have hψ_fix_H : ∀ x : R, x ∈ H → ψ x = x := by
        intro x hx
        let xH : H := ⟨x, hx⟩
        have hxfix := htrivH aψ xH
        exact congrArg Subtype.val hxfix
      exact hψ_not_fix_H hψ_fix_H
    have hσ_order : orderOf σbar = q := by
      have hσ_order_ne_one : orderOf σbar ≠ 1 := by
        intro horder
        exact hσ_ne_one (orderOf_eq_one_iff.mp horder)
      rcases (Nat.dvd_prime (Fact.out : Nat.Prime q)).1 hσ_dvd_q with horder_one | horder_q
      · exact False.elim (hσ_order_ne_one horder_one)
      · exact horder_q
    have hQelem : IsElementaryAbelian p (H ⧸ frattini H) :=
      isElementaryAbelian_quotient_frattini (R := H) (p := p)
    let : IsElementaryAbelian p (H ⧸ frattini H) := hQelem
    exact prime_order_mulAut_dvd_of_elementaryAbelian_card_le_p_sq
      (A := H ⧸ frattini H) (p := p) (q := q) hHquot_card σbar hσ_order hq_ne

private theorem CFSG.gorenstein_theorem_5_4_15_automorphism
    {R : Type*} [Group R] [Finite R] {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    (ψ : MulAut R) (hψ_order : orderOf ψ = q) (hq_ne : q ≠ p) :
    q ∣ (p ^ 2 - 1) ∧ q < p := by
  have hdvd : q ∣ p ^ 2 - 1 :=
    gorenstein_theorem_5_4_15_automorphism_dvd
      (R := R) (p := p) (q := q) hpodd hRp hA3 ψ hψ_order hq_ne
  exact ⟨hdvd, prime_lt_of_dvd_odd_prime_sq_sub_one (p := p) (q := q) hpodd hq_ne hdvd⟩

/-- Gorenstein, Theorem 5.4.15, in the form used by Section 4.

Here `selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅` is the local formal
proxy for the hypothesis `d_n(R) ≤ 2`; the conclusion `groupRank R ≤ 2`
is the local version of `d(R) ≤ 2`. -/
public theorem CFSG.gorenstein_theorem_5_4_15
    {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅) :
    groupRank R ≤ 2 ∧
      ∀ {q : ℕ} [Fact q.Prime] (ψ : MulAut R),
        orderOf ψ = q → q ≠ p → q ∣ (p ^ 2 - 1) ∧ q < p := by
  have hrank : groupRank R ≤ 2 :=
    gorenstein_theorem_5_4_15_rank (R := R) (p := p) hpodd hRp hA3
  refine ⟨hrank, ?_⟩
  intro q _hq ψ hψ_order hq_ne
  exact gorenstein_theorem_5_4_15_automorphism
    (R := R) (p := p) (q := q) hpodd hRp hA3 ψ hψ_order hq_ne

public theorem CFSG.gorenstein_theorem_5_4_15_prime_dvd_aut
    {R : Type*} [Group R] [Finite R] {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hpodd : p ≠ 2) (hRp : IsPGroup p R)
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    (hqAut : q ∣ Nat.card (MulAut R)) (hq_ne : q ≠ p) :
    q ∣ (p ^ 2 - 1) ∧ q < p := by
  classical
  let : Fintype (MulAut R) := Fintype.ofFinite (MulAut R)
  have hqAut' : q ∣ Fintype.card (MulAut R) := by
    simpa [Nat.card_eq_fintype_card] using hqAut
  obtain ⟨ψ, hψ_order⟩ := exists_prime_orderOf_dvd_card q hqAut'
  exact (gorenstein_theorem_5_4_15
    (R := R) (p := p) hpodd hRp hA3).2 ψ hψ_order hq_ne


end Main

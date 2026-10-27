module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Frattini
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative Subgroup

/-- The minimal number of generators of a group. -/
@[expose] public noncomputable def CFSG.generatorRank (G : Type*) [Group G] : ℕ :=
  sInf { n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤ }

/-- A group is metacyclic if it has a cyclic normal subgroup with cyclic quotient. -/
@[expose] public def CFSG.IsMetacyclic (G : Type*) [Group G] : Prop :=
  ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic N ∧ IsCyclic (G ⧸ N)

public theorem CFSG.generatorRank_eq_group_rank
    (G : Type*) [Group G] [Finite G] :
    generatorRank G = Group.rank G := by
  classical
  let T : Set ℕ := { n : ℕ | ∃ t : Fin n → G, Subgroup.closure (Set.range t) = ⊤ }
  have hT_nonempty : T.Nonempty := by
    obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec G
    refine ⟨Group.rank G, ?_⟩
    rw [← hS_card]
    refine ⟨fun i => ((S.equivFin.symm i : S) : G), ?_⟩
    have hrange :
        Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : G)) = (S : Set G) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hg
        refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
        simp
    simpa [hrange]
  refine le_antisymm ?_ ?_
  · obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec G
    refine Nat.sInf_le ?_
    rw [← hS_card]
    refine ⟨fun i => ((S.equivFin.symm i : S) : G), ?_⟩
    have hrange :
        Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : G)) = (S : Set G) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hg
        refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
        simp
    simpa [hrange] using hS_top
  · rcases (Nat.sInf_mem hT_nonempty) with ⟨t, ht_top⟩
    let U : Finset G := Finset.univ.image t
    have hU_top : Subgroup.closure (U : Set G) = ⊤ := by
      simpa [U, Finset.coe_image, Finset.coe_univ, Set.image_univ] using ht_top
    have hU_card : U.card ≤ generatorRank G := by
      simpa [generatorRank, T] using (Finset.card_image_le (f := t) (s := Finset.univ))
    exact (Group.rank_le hU_top).trans hU_card


set_option maxHeartbeats 800000 in
public theorem CFSG.generatorRank_le_finrank_of_elementaryAbelian
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    generatorRank G ≤ Module.finrank (ZMod p) (Additive G) := by
  classical
  let b := Module.finBasis (ZMod p) (Additive G)
  let s : Fin (Module.finrank (ZMod p) (Additive G)) → G := fun i => Additive.toMul (b i)
  have hadd_top : AddSubgroup.closure (Set.range fun i => b i) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.toAddSubgroup_eq_top]
    have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
      simpa using (ZMod.intCast_surjective (n := p))
    calc
      Submodule.span ℤ (Set.range fun i => b i)
          = (Submodule.span (ZMod p) (Set.range fun i => b i)).restrictScalars ℤ := by
              symm
              simpa using
                (Submodule.restrictScalars_span (R := ℤ) (A := ZMod p) hsurj
                  (Set.range fun i => b i))
      _ = ⊤ := by simp [b.span_eq]
  have hgroup_top : Subgroup.closure (Set.range s) = ⊤ := by
    have hrange :
        Additive.ofMul ⁻¹' Set.range (fun i => b i) = Set.range s := by
      ext g
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by simpa [s] using congrArg Additive.toMul hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, by simpa [s] using congrArg Additive.ofMul hi⟩
    calc
      Subgroup.closure (Set.range s)
          = (AddSubgroup.closure (Set.range fun i => b i)).toSubgroup' := by
              symm
              rw [AddSubgroup.toSubgroup'_closure, hrange]
      _ = ⊤ := by simp [hadd_top]
  let S : Finset G := Finset.univ.image s
  have hS_top : Subgroup.closure (S : Set G) = ⊤ := by
    simpa [S, s, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgroup_top
  have hrank_le : Group.rank G ≤ S.card :=
    Group.rank_le hS_top
  have hS_card : S.card ≤ Module.finrank (ZMod p) (Additive G) := by
    simpa [S, s] using (Finset.card_image_le (f := s) (s := Finset.univ))
  simpa [generatorRank_eq_group_rank] using hrank_le.trans hS_card

set_option maxHeartbeats 800000 in
public theorem CFSG.elementaryAbelian_finrank_le_generatorRank
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    Module.finrank (ZMod p) (Additive G) ≤ generatorRank G := by
  classical
  let n := generatorRank G
  have hnonempty :
      {n : ℕ | ∃ s : Fin n → G, Subgroup.closure (Set.range s) = ⊤}.Nonempty := by
    refine ⟨Nat.card G, ?_⟩
    letI : Fintype G := Fintype.ofFinite G
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

public theorem CFSG.elementaryAbelian_card_eq_pow_generatorRank
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [IsElementaryAbelian p G] :
    Nat.card G = p ^ generatorRank G := by
  have hcard : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    calc
      Nat.card G = Nat.card (Additive G) := (Nat.card_congr Additive.toMul).symm
      _ = p ^ Module.finrank (ZMod p) (Additive G) := by
        simpa [ZMod.card] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G))
  have hfin_le_gen :
      Module.finrank (ZMod p) (Additive G) ≤ generatorRank G :=
    elementaryAbelian_finrank_le_generatorRank (p := p) G
  have hgen_le_fin :
      generatorRank G ≤ Module.finrank (ZMod p) (Additive G) :=
    generatorRank_le_finrank_of_elementaryAbelian (p := p) G
  have hfin_eq : Module.finrank (ZMod p) (Additive G) = generatorRank G :=
    le_antisymm hfin_le_gen hgen_le_fin
  simpa [hfin_eq] using hcard

public theorem CFSG.exists_two_generators_of_generatorRank_le_two
    (G : Type*) [Group G] [Finite G] (hG : generatorRank G ≤ 2) :
    ∃ x y : G, Subgroup.closure ({x, y} : Set G) = ⊤ := by
  classical
  let T : Set ℕ := { n : ℕ | ∃ t : Fin n → G, Subgroup.closure (Set.range t) = ⊤ }
  have hT_nonempty : T.Nonempty := by
    obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec G
    refine ⟨Group.rank G, ?_⟩
    rw [← hS_card]
    refine ⟨fun i => ((S.equivFin.symm i : S) : G), ?_⟩
    have hrange :
        Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : G)) = (S : Set G) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hg
        refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
        simp
    simpa [hrange] using hS_top
  let n := generatorRank G
  have hn_mem : n ∈ T := by
    simpa [n, generatorRank, T] using (Nat.sInf_mem hT_nonempty)
  rcases hn_mem with ⟨t, ht_top⟩
  have hn_le : n ≤ 2 := by simpa [n] using hG
  let u : Fin 2 → G := fun i =>
    if h : (i : ℕ) < n then t ⟨i, h⟩ else 1
  have htu : Set.range t ⊆ Set.range u := by
    intro g hg
    rcases hg with ⟨i, rfl⟩
    refine ⟨Fin.castLE hn_le i, ?_⟩
    simp [u]
  have hu_top : Subgroup.closure (Set.range u) = ⊤ := by
    apply top_le_iff.mp
    rw [← ht_top]
    exact Subgroup.closure_mono htu
  let x : G := u 0
  let y : G := u 1
  have hrange_u : Set.range u = ({x, y} : Set G) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [x, y]
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  exact ⟨x, y, by simpa [hrange_u, x, y] using hu_top⟩

public theorem CFSG.isMetacyclic_of_generatorRank_le_two_of_commutative
    (G : Type*) [Group G] [Finite G] [IsMulCommutative G]
    (hG : generatorRank G ≤ 2) :
    IsMetacyclic G := by
  classical
  obtain ⟨x, y, hxy_top⟩ := exists_two_generators_of_generatorRank_le_two G hG
  let N : Subgroup G := Subgroup.zpowers x
  have hNnorm : N.Normal := by
    exact Subgroup.normal_of_isMulCommutative N
  refine ⟨N, hNnorm, inferInstance, ?_⟩
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hclosure_img_top : Subgroup.closure (q '' ({x, y} : Set G)) = ⊤ := by
    calc
      Subgroup.closure (q '' ({x, y} : Set G))
          = (Subgroup.closure ({x, y} : Set G)).map q := by
            symm
            exact MonoidHom.map_closure q ({x, y} : Set G)
      _ = (⊤ : Subgroup (G ⧸ N)) := by
            rw [hxy_top]
            exact Subgroup.map_top_of_surjective q hq_surj
  have himage_le : q '' ({x, y} : Set G) ⊆ Subgroup.zpowers (q y) := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    have hw' : w = x ∨ w = y := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hw
    cases hw' with
    | inl hwx =>
      rw [hwx]
      have hqx : q x = 1 := by
        exact (QuotientGroup.eq_one_iff (N := N) x).2 (Subgroup.mem_zpowers x)
      rw [hqx]
      simp
    | inr hwy =>
      rw [hwy]
      exact Subgroup.mem_zpowers (q y)
  have hzpow_top : Subgroup.zpowers (q y) = ⊤ := by
    apply top_le_iff.mp
    rw [← hclosure_img_top, Subgroup.closure_le]
    exact himage_le
  exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨q y, hzpow_top⟩

public theorem CFSG.generatorRank_le_generatorRank_quotient_frattini
    {p : ℕ} [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [Fact (IsPGroup p G)] :
    generatorRank G ≤ generatorRank (G ⧸ frattini G) := by
  classical
  let T : Set ℕ :=
    { n : ℕ | ∃ t : Fin n → (G ⧸ frattini G), Subgroup.closure (Set.range t) = ⊤ }
  have hT_nonempty : T.Nonempty := by
    obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec (G ⧸ frattini G)
    refine ⟨Group.rank (G ⧸ frattini G), ?_⟩
    rw [← hS_card]
    refine ⟨fun i => ((S.equivFin.symm i : S) : (G ⧸ frattini G)), ?_⟩
    have hrange :
        Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : (G ⧸ frattini G))) =
          (S : Set (G ⧸ frattini G)) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hg
        refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
        simp
    simpa [hrange] using hS_top
  let n := generatorRank (G ⧸ frattini G)
  have hn_mem : n ∈ T := by
    simpa [n, generatorRank, T] using (Nat.sInf_mem hT_nonempty)
  rcases hn_mem with ⟨t, ht_top⟩
  choose s hs using fun i : Fin n => QuotientGroup.mk'_surjective (frattini G) (t i)
  let H : Subgroup G := Subgroup.closure (Set.range s)
  have hmap_top : H.map (QuotientGroup.mk' (frattini G)) = ⊤ := by
    calc
      H.map (QuotientGroup.mk' (frattini G))
          = Subgroup.closure ((QuotientGroup.mk' (frattini G)) '' Set.range s) := by
            simpa [H] using
              (MonoidHom.map_closure (QuotientGroup.mk' (frattini G)) (Set.range s))
      _ = Subgroup.closure (Set.range t) := by
            congr
            ext x
            constructor
            · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
              exact ⟨i, by simpa using (hs i).symm⟩
            · rintro ⟨i, rfl⟩
              exact ⟨s i, ⟨i, rfl⟩, by simpa using (hs i)⟩
      _ = ⊤ := ht_top
  have hsup : H ⊔ frattini G = ⊤ := by
    have hcomap :
        Subgroup.comap (QuotientGroup.mk' (frattini G))
            (H.map (QuotientGroup.mk' (frattini G))) =
          H ⊔ frattini G := by
      simpa using (Subgroup.comap_map_eq (f := QuotientGroup.mk' (frattini G)) (H := H))
    calc
      H ⊔ frattini G =
          Subgroup.comap (QuotientGroup.mk' (frattini G))
            (H.map (QuotientGroup.mk' (frattini G))) := hcomap.symm
      _ = ⊤ := by simp [hmap_top]
  have hH_top : H = ⊤ :=
    frattini_nongenerating (G := G) hsup
  have hn_memG :
      n ∈ { n : ℕ | ∃ t : Fin n → G, Subgroup.closure (Set.range t) = ⊤ } :=
    ⟨s, hH_top⟩
  change sInf {m : ℕ | ∃ t : Fin m → G, Subgroup.closure (Set.range t) = ⊤} ≤ n
  exact Nat.sInf_le hn_memG

public theorem CFSG.generatorRank_le_one_of_isCyclic {G : Type*} [Group G] (hcyc : IsCyclic G) :
    generatorRank G ≤ 1 := by
  classical
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := G)).1 hcyc
  let s : Fin 1 → G := fun _ => g
  have hs : Subgroup.closure (Set.range s) = ⊤ := by
    have hrange : Set.range s = ({g} : Set G) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        simp [s]
      · intro hx
        refine ⟨0, ?_⟩
        simpa [s] using hx.symm
    calc
      Subgroup.closure (Set.range s) = Subgroup.closure ({g} : Set G) := by rw [hrange]
      _ = Subgroup.zpowers g := by rw [← Subgroup.zpowers_eq_closure]
      _ = ⊤ := hg
  unfold generatorRank
  exact Nat.sInf_le ⟨s, hs⟩

public theorem CFSG.isCyclic_of_generatorRank_le_one
    {G : Type*} [Group G] [Finite G] (hG : generatorRank G ≤ 1) :
    IsCyclic G := by
  classical
  let T : Set ℕ := { n : ℕ | ∃ t : Fin n → G, Subgroup.closure (Set.range t) = ⊤ }
  have hT_nonempty : T.Nonempty := by
    obtain ⟨S, hS_card, hS_top⟩ := Group.rank_spec G
    refine ⟨Group.rank G, ?_⟩
    rw [← hS_card]
    refine ⟨fun i => ((S.equivFin.symm i : S) : G), ?_⟩
    have hrange :
        Set.range (fun i : Fin S.card => ((S.equivFin.symm i : S) : G)) = (S : Set G) := by
      ext g
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hg
        refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
        simp
    simpa [hrange] using hS_top
  let n := generatorRank G
  have hn_mem : n ∈ T := by
    simpa [n, generatorRank, T] using (Nat.sInf_mem hT_nonempty)
  rcases hn_mem with ⟨t, ht_top⟩
  have hn_le : n ≤ 1 := by simpa [n] using hG
  let u : Fin 1 → G := fun i =>
    if h : (i : ℕ) < n then t ⟨i, h⟩ else 1
  have htu : Set.range t ⊆ Set.range u := by
    intro g hg
    rcases hg with ⟨i, rfl⟩
    refine ⟨0, ?_⟩
    have h0n : 0 < n := lt_of_le_of_lt (Nat.zero_le i) i.isLt
    dsimp [u]
    rw [dif_pos h0n]
    exact congrArg t (Fin.ext (by omega))
  have hu_top : Subgroup.closure (Set.range u) = ⊤ := by
    apply top_le_iff.mp
    rw [← ht_top]
    exact Subgroup.closure_mono htu
  let x : G := u 0
  have hrange_u : Set.range u = ({x} : Set G) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      simp [x]
    · intro hg
      refine ⟨0, ?_⟩
      simpa [x] using hg.symm
  exact (isCyclic_iff_exists_zpowers_eq_top (α := G)).2 ⟨x, by
    calc
      Subgroup.zpowers x = Subgroup.closure ({x} : Set G) := by
        rw [Subgroup.zpowers_eq_closure]
      _ = ⊤ := by simpa [hrange_u] using hu_top⟩

public theorem CFSG.exists_maximal_normal_abelian_subgroup_containing
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hEnorm : E.Normal) (hEcomm : IsMulCommutative E) :
    ∃ A : Subgroup G,
      E ≤ A ∧
        A.Normal ∧
        IsMulCommutative A ∧
        ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A := by
  classical
  let s : Set (Subgroup G) := {A | E ≤ A ∧ A.Normal ∧ IsMulCommutative A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    exact ⟨E, le_rfl, hEnorm, hEcomm⟩
  obtain ⟨A, hAmax⟩ := hsfin.exists_maximal hsne
  refine ⟨A, hAmax.1.1, hAmax.1.2.1, hAmax.1.2.2, ?_⟩
  intro B hBnorm hBcomm hAB
  have hBmem : B ∈ s := ⟨hAmax.1.1.trans hAB, hBnorm, hBcomm⟩
  exact le_antisymm (hAmax.2 hBmem hAB) hAB

public theorem CFSG.quotient_isCyclic_of_sup_cyclic_right
    {R : Type*} [Group R] {R₁ R₂ : Subgroup R} [R₁.Normal]
    (hsup : R₁ ⊔ R₂ = ⊤) (hR₂cyc : IsCyclic R₂) :
    IsCyclic (R ⧸ R₁) := by
  let q : R₂ →* R ⧸ R₁ := (QuotientGroup.mk' R₁).comp R₂.subtype
  have hq_surj : Function.Surjective q := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective R₁ x
    have hr_sup : r ∈ R₁ ⊔ R₂ := by
      rw [hsup]
      exact Subgroup.mem_top r
    rcases (Subgroup.mem_sup_of_normal_left (x := r) (s := R₁) (t := R₂)).1 hr_sup with
      ⟨y, hy, z, hz, hyz⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    change QuotientGroup.mk' R₁ z = QuotientGroup.mk' R₁ r
    rw [← hyz]
    have hy_one : QuotientGroup.mk' R₁ y = 1 :=
      (QuotientGroup.eq_one_iff (N := R₁) (x := y)).2 hy
    calc
      QuotientGroup.mk' R₁ z = 1 * QuotientGroup.mk' R₁ z := by simp
      _ = QuotientGroup.mk' R₁ y * QuotientGroup.mk' R₁ z := by rw [hy_one]
      _ = QuotientGroup.mk' R₁ (y * z) := by simp
  letI : IsCyclic R₂ := hR₂cyc
  exact isCyclic_of_surjective q hq_surj

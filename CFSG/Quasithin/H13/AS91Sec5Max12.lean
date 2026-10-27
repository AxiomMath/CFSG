module

public import CFSG.Quasithin.H13.AS91Sec7Delta
public import CFSG.Quasithin.H13.AS91Sec5Prim

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise BigOperators
open CFSG.ASVolI.ChH (IsTrio IsSextet M24g S24)

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G}

theorem deltaSize_sum_dvd (I : Finset (Fin 5)) :
    (0 : Fin 5) ∈ I → (∑ i ∈ I, deltaSize i) ∣ 3795 →
    (∑ i ∈ I, deltaSize i) = 1 ∨ (∑ i ∈ I, deltaSize i) = 3795 := by
  revert I
  decide

variable (c : Loc49 G z)

theorem stabilizer_l0_of_le {L : Subgroup G} (hL : L ≤ c.G1) :
    MulAction.stabilizer ↥L c.l0 = (c.G1 ⊓ c.G2).subgroupOf L := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    refine ⟨hL x.2, ?_⟩
    have h' : (x : G)⁻¹ * 1 ∈ c.G2 :=
      (c.smul_l0_eq_iff (x : G) 1).1 (by simpa [Subgroup.smul_def] using hx)
    simpa using h'
  · rintro ⟨-, hxG2⟩
    have h' : (x : G)⁻¹ * 1 ∈ c.G2 := by simpa using hxG2
    have hx := (c.smul_l0_eq_iff (x : G) 1).2 h'
    simpa [Subgroup.smul_def] using hx

theorem lnsX_eq_orbit : c.lnsX = MulAction.orbit ↥c.G1 c.l0 := by
  ext n
  constructor
  · intro hn
    obtain ⟨h, rfl⟩ := c.exists_G1_smul_l0 hn.symm'
    exact MulAction.mem_orbit _ h
  · rintro ⟨h, rfl⟩
    exact (c.cInc_x0_smul_l0 h).symm'

theorem lnsX_ncard_eq_relIndex :
    c.lnsX.ncard = (c.G1 ⊓ c.G2).relIndex c.G1 := by
  rw [c.lnsX_eq_orbit]
  calc (MulAction.orbit ↥c.G1 c.l0).ncard
      = (MulAction.stabilizer ↥c.G1 c.l0).index :=
        (MulAction.index_stabilizer ↥c.G1 c.l0).symm
    _ = ((c.G1 ⊓ c.G2).subgroupOf c.G1).index := by rw [c.stabilizer_l0_of_le le_rfl]
    _ = (c.G1 ⊓ c.G2).relIndex c.G1 := rfl

theorem mem_delta_zero (ρ : ResM24 c) :
    c.l0 ∈ c.delta 0 := by
  refine (ρ.mem_delta_iff 0).2 ⟨?_, ?_⟩
  · simpa using c.cInc_x0_smul_l0 (1 : ↥c.G1)
  · rw [ρ.trio_l0]
    rfl

theorem exists_mem_delta (ρ : ResM24 c)
    (i : Fin 5) : (c.delta i).Nonempty := by
  have hpos : 0 < {k | IsTrio k ∧ M24G.Delta ρ.l₀ k i}.ncard := by
    rw [M24G.ncard_delta ρ.isTrio_l₀ i]
    fin_cases i <;> norm_num
  obtain ⟨k, hkT, hki⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    {k | IsTrio k ∧ M24G.Delta ρ.l₀ k i}.ncard ≠ 0)
  obtain ⟨g, hg, hgk⟩ := M24G.trio_transitive hkT
  obtain ⟨h, hh, hhl⟩ := M24G.trio_transitive ρ.isTrio_l₀
  have hσ : g⁻¹ * h ∈ M24g := M24g.mul_mem (M24g.inv_mem hg) hh
  have hσl : (g⁻¹ * h) • ρ.l₀ = k := by
    rw [mul_smul, hhl, ← hgk, inv_smul_smul]
  obtain ⟨n, hn, hnk⟩ := ρ.exists_trio_eq hσ
  have hnk' : ρ.trio n = k := hnk.trans hσl
  refine ⟨n, (ρ.mem_delta_iff i).2 ⟨hn, ?_⟩⟩
  rwa [hnk']

theorem orbit_eq_delta_of_mem (ρ : ResM24 c)
    (i : Fin 5) {n : G ⧸ c.G2} (hn : n ∈ c.delta i) :
    MulAction.orbit ↥(c.G1 ⊓ c.G2) n = c.delta i := by
  have hn' := (ρ.mem_delta_iff i).1 hn
  refine Set.Subset.antisymm ?_ ?_
  · rintro m ⟨g, rfl⟩
    exact (c.smul_mem_delta g.2 i).2 hn
  · intro m hm
    have hm' := (ρ.mem_delta_iff i).1 hm
    have himg : ρ.trio '' (MulAction.orbit ↥(c.G1 ⊓ c.G2) n) =
        {k | IsTrio k ∧ M24G.Delta ρ.l₀ k i} := by
      rw [ρ.trio_image_orbit hn'.1]
      exact ρ.orbit_eq_delta (ρ.isTrio_trio hn'.1) hn'.2
    have hmem : ρ.trio m ∈ ρ.trio '' (MulAction.orbit ↥(c.G1 ⊓ c.G2) n) := by
      rw [himg]
      exact ⟨ρ.isTrio_trio hm'.1, hm'.2⟩
    obtain ⟨l, hl, hlm⟩ := hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hl
    have hgl : CInc c.G1 c.G2 c.x0 (g • n) := (c.cInc_x0_smul g.2.1).2 hn'.1
    have hml : g • n = m := ρ.trio_injOn hgl hm'.1 hlm
    rw [← hml]
    exact MulAction.mem_orbit _ g

theorem ncard_delta (ρ : ResM24 c)
    (i : Fin 5) : (c.delta i).ncard = deltaSize i := by
  obtain ⟨n, hn⟩ := c.exists_mem_delta ρ i
  rw [← c.orbit_eq_delta_of_mem ρ i hn]
  have hn' := (ρ.mem_delta_iff i).1 hn
  rw [ρ.ncard_orbit_G12 hn'.1, ρ.orbit_eq_delta (ρ.isTrio_trio hn'.1) hn'.2,
    M24G.ncard_delta ρ.isTrio_l₀]
  rfl

theorem delta_disjoint (ρ : ResM24 c) :
    Pairwise (Function.onFun Disjoint c.delta) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro n hi hj
  have h1 := c.orbit_eq_delta_of_mem ρ i hi
  have h2 := c.orbit_eq_delta_of_mem ρ j hj
  have hsize : deltaSize i = deltaSize j := by
    rw [← c.ncard_delta ρ i, ← c.ncard_delta ρ j, ← h1, ← h2]
  exact hij (deltaSize_injective hsize)

theorem iUnion_delta (ρ : ResM24 c) :
    (⋃ i : Fin 5, c.delta i) = c.lnsX := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
    exact ((ρ.mem_delta_iff i).1 hi).1.symm'
  · intro hn
    have hn' : CInc c.G1 c.G2 c.x0 n := hn.symm'
    obtain ⟨i, hi, -⟩ := M24G.delta_existsUnique ρ.isTrio_l₀ (ρ.isTrio_trio hn')
    exact Set.mem_iUnion.mpr ⟨i, (ρ.mem_delta_iff i).2 ⟨hn', hi⟩⟩

theorem ncard_lnsX (ρ : ResM24 c) :
    c.lnsX.ncard = 3795 := by
  rw [← c.iUnion_delta ρ, Set.ncard_iUnion_of_finite (fun i => Set.toFinite _)
    (c.delta_disjoint ρ), finsum_eq_sum_of_fintype, Fin.sum_univ_five]
  simp [deltaSize, c.ncard_delta ρ]

theorem relIndex_G12_eq (ρ : ResM24 c) :
    (c.G1 ⊓ c.G2).relIndex c.G1 = 3795 := by
  rw [← c.lnsX_ncard_eq_relIndex, c.ncard_lnsX ρ]

theorem max_of_resM24 (ρ : ResM24 c) :
    ∀ L : Subgroup G, c.G1 ⊓ c.G2 ≤ L → L ≤ c.G1 →
      L = c.G1 ⊓ c.G2 ∨ L = c.G1 := by
  intro L hHL hLG
  classical
  let O : Set (G ⧸ c.G2) := MulAction.orbit ↥L c.l0
  have hO_sub : O ⊆ c.lnsX := by
    intro n hn
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hn
    exact (c.cInc_x0_smul_l0 ⟨(g : G), hLG g.2⟩).symm'
  have hO_smul : ∀ x : ↥(c.G1 ⊓ c.G2), ∀ m ∈ O, x • m ∈ O := by
    intro x m hm
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hm
    rw [← hg]
    refine MulAction.mem_orbit_iff.mpr
      ⟨⟨(x : G) * (g : G), L.mul_mem (hHL x.2) g.2⟩, ?_⟩
    exact mul_smul (x : G) (g : G) c.l0
  let J : Set (Fin 5) := {i | (c.delta i ∩ O).Nonempty}
  have hO_eq : O = ⋃ i ∈ J, c.delta i := by
    ext n
    constructor
    · intro hn
      have hn' : CInc c.G1 c.G2 c.x0 n := (hO_sub hn).symm'
      obtain ⟨i, hi, -⟩ := M24G.delta_existsUnique ρ.isTrio_l₀ (ρ.isTrio_trio hn')
      have hnd : n ∈ c.delta i := (ρ.mem_delta_iff i).2 ⟨hn', hi⟩
      refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨?_, hnd⟩⟩
      exact ⟨n, hnd, hn⟩
    · intro hn
      obtain ⟨i, hiJ, hnd⟩ := by simpa only [Set.mem_iUnion] using hn
      obtain ⟨m, hm⟩ := hiJ
      obtain ⟨hmd, hmO⟩ := hm
      have horb : MulAction.orbit ↥(c.G1 ⊓ c.G2) m = c.delta i :=
        c.orbit_eq_delta_of_mem ρ i hmd
      have hnm : n ∈ MulAction.orbit ↥(c.G1 ⊓ c.G2) m := by rwa [horb]
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hnm
      rw [← hg]
      exact hO_smul g m hmO
  have h0O : c.l0 ∈ O := MulAction.mem_orbit_self c.l0
  have h0J : (0 : Fin 5) ∈ J := by
    refine ⟨c.l0, ?_⟩
    exact ⟨c.mem_delta_zero ρ, h0O⟩
  have hO_card : O.ncard = (c.G1 ⊓ c.G2).relIndex L := by
    calc O.ncard = (MulAction.stabilizer ↥L c.l0).index :=
          (MulAction.index_stabilizer ↥L c.l0).symm
      _ = ((c.G1 ⊓ c.G2).subgroupOf L).index := by rw [c.stabilizer_l0_of_le hLG]
      _ = (c.G1 ⊓ c.G2).relIndex L := rfl
  have hpair : J.PairwiseDisjoint c.delta := by
    intro i _ j _ hij
    exact c.delta_disjoint ρ hij
  have hO_sum : O.ncard = ∑ᶠ i ∈ J, deltaSize i := by
    rw [hO_eq, (Set.toFinite J).ncard_biUnion (fun i _ => Set.toFinite (c.delta i)) hpair,
      finsum_mem_congr rfl (fun i _ => c.ncard_delta ρ i)]
  let Jf : Finset (Fin 5) := (Set.toFinite J).toFinset
  have hsum_eq : (∑ᶠ i ∈ J, deltaSize i) = ∑ i ∈ Jf, deltaSize i := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite J)]
  have h0Jf : (0 : Fin 5) ∈ Jf := (Set.toFinite J).mem_toFinset.mpr h0J
  have hsum_dvd : (∑ i ∈ Jf, deltaSize i) ∣ 3795 := by
    rw [← hsum_eq, ← hO_sum]
    rw [hO_card, ← c.relIndex_G12_eq ρ,
      ← Subgroup.relIndex_mul_relIndex (c.G1 ⊓ c.G2) L c.G1 hHL hLG]
    exact dvd_mul_right _ _
  rcases deltaSize_sum_dvd Jf h0Jf hsum_dvd with h1 | h1
  · left
    have hO1 : O.ncard = 1 := by rw [hO_sum, hsum_eq, h1]
    have hrel : (c.G1 ⊓ c.G2).relIndex L = 1 := by rw [← hO_card, hO1]
    exact le_antisymm ((Subgroup.relIndex_eq_one (H := c.G1 ⊓ c.G2) (K := L)).1 hrel) hHL
  · right
    have hO2 : O.ncard = 3795 := by rw [hO_sum, hsum_eq, h1]
    have hrel : (c.G1 ⊓ c.G2).relIndex L = 3795 := by rw [← hO_card, hO2]
    have hmul := Subgroup.relIndex_mul_relIndex (c.G1 ⊓ c.G2) L c.G1 hHL hLG
    rw [hrel, c.relIndex_G12_eq ρ] at hmul
    have hLidx : L.relIndex c.G1 = 1 := by omega
    exact le_antisymm hLG ((Subgroup.relIndex_eq_one (H := L) (K := c.G1)).1 hLidx)

theorem not_le_normalizer_of_resM24 (ρ : ResM24 c) :
    ¬ c.G1 ≤ Subgroup.normalizer ((c.G1 ⊓ c.G2 : Subgroup G) : Set G) := by
  intro hN
  have hne : (c.delta 1).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [c.ncard_delta ρ 1]
    norm_num [deltaSize]
  obtain ⟨n, hn⟩ := hne
  have hn' := (ρ.mem_delta_iff 1).1 hn
  have horb := c.orbit_eq_delta_of_mem ρ 1 hn
  have hsing : MulAction.orbit ↥(c.G1 ⊓ c.G2) n = {n} := by
    obtain ⟨h, hh, rfl⟩ := c.exists_G1_smul_l0 hn'.1
    ext m
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_singleton_iff]
      beta_reduce
      have hconj : (h : G)⁻¹ * (x : G) * h ∈ c.G1 ⊓ c.G2 := by
        refine Subgroup.mem_inf.mpr ⟨c.G1.mul_mem (c.G1.mul_mem (c.G1.inv_mem h.2) x.2.1)
          h.2, ?_⟩
        have hxN : ((h : G)⁻¹) ∈
            Subgroup.normalizer ((c.G1 ⊓ c.G2 : Subgroup G) : Set G) :=
          hN (c.G1.inv_mem h.2)
        simpa using
          (Subgroup.mem_inf.mp ((Subgroup.mem_normalizer_iff.mp hxN (x : G)).mp x.2)).2
      have hfix : ((h : G)⁻¹ * (x : G) * h) • c.l0 = c.l0 := by
        have hmem : (⟨(h : G)⁻¹ * (x : G) * h, hconj.1⟩ : ↥c.G1) ∈
            MulAction.stabilizer ↥c.G1 c.l0 := by
          rw [c.stabilizer_l0_of_le le_rfl]
          exact Subgroup.mem_subgroupOf.mpr hconj
        have := MulAction.mem_stabilizer_iff.mp hmem
        simpa [Subgroup.smul_def] using this
      rw [Subgroup.smul_def, ← mul_smul]
      calc ((x : G) * (h : G)) • c.l0 =
            ((h : G) * ((h : G)⁻¹ * (x : G) * h)) • c.l0 := by
            congr 1
            group
        _ = (h : G) • (((h : G)⁻¹ * (x : G) * h) • c.l0) := mul_smul _ _ _
        _ = (h : G) • c.l0 := by rw [hfix]
    · intro hm
      rw [Set.mem_singleton_iff] at hm
      rw [hm]
      exact MulAction.mem_orbit_self _
  have hcard1 : (c.delta 1).ncard = 1 := by
    rw [← horb, hsing, Set.ncard_singleton]
  rw [c.ncard_delta ρ 1] at hcard1
  norm_num [deltaSize] at hcard1

theorem max12_of_resM24
    (ρ : ResM24 c) :
    (∀ L : Subgroup G, c.G1 ⊓ c.G2 ≤ L → L ≤ c.G1 →
      L = c.G1 ⊓ c.G2 ∨ L = c.G1) ∧
    ∃ g ∈ c.G1, g ∉ Subgroup.normalizer ((c.G1 ⊓ c.G2 : Subgroup G) : Set G) := by
  refine ⟨c.max_of_resM24 ρ, ?_⟩
  by_contra h
  apply c.not_le_normalizer_of_resM24 ρ
  intro g hg
  by_contra hgN
  exact h ⟨g, hg, hgN⟩

end Loc49

theorem stmt5_max12_of
    (hres : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      Nonempty (ResM24 c)) :
    Stmt5_Max12 := by
  intro G _ _ z hJ c
  obtain ⟨ρ⟩ := hres G z hJ c
  exact c.max12_of_resM24 ρ

end CFSG.Quasithin.H13.AS91

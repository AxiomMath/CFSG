module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data calC)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (Thin8 IsProdOfCalC)
open scoped Pointwise

private lemma r869rep_one_mem_list_prod {α : Type*} [Monoid α] {l : List (Set α)}
    (h1 : ∀ t ∈ l, (1 : α) ∈ t) : (1 : α) ∈ l.prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.prod_cons]
    simpa using Set.mul_mem_mul (h1 hd List.mem_cons_self)
      (ih (fun t ht => h1 t (List.mem_cons_of_mem _ ht)))

private lemma r869rep_subset_list_prod {α : Type*} [Monoid α] {l : List (Set α)} {s : Set α}
    (hs : s ∈ l) (h1 : ∀ t ∈ l, (1 : α) ∈ t) : s ⊆ l.prod := by
  induction l with
  | nil => simp at hs
  | cons hd tl ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp hs with hsd | hs'
    · intro x hx
      rw [hsd] at hx
      simpa using Set.mul_mem_mul hx
        (r869rep_one_mem_list_prod (l := tl) (fun t ht => h1 t (List.mem_cons_of_mem _ ht)))
    · intro x hx
      have hx' : x ∈ tl.prod :=
        ih hs' (fun t ht => h1 t (List.mem_cons_of_mem _ ht)) hx
      simpa using Set.mul_mem_mul (h1 hd List.mem_cons_self) hx'

private theorem r869rep_perfect_of_isProdOfCalC {G : Type} [Group G] {M L : Subgroup G}
    (h : IsProdOfCalC M L) : ⁅L, L⁆ = L := by
  obtain ⟨k, S, hS, hLset⟩ := h
  have hsil : ∀ i, S i ≤ L := by
    intro i
    have hmem : (S i : Set G) ∈ List.ofFn (fun j : Fin k => (S j : Set G)) :=
      List.mem_ofFn.2 ⟨i, rfl⟩
    have hsub := r869rep_subset_list_prod hmem (fun t ht => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 ht
      exact (S j).one_mem)
    rwa [← hLset] at hsub
  have hle : L ≤ ⨆ i : Fin k, S i := by
    intro x hx
    have hx' : x ∈ (List.ofFn fun j : Fin k => (S j : Set G)).prod := by
      rw [← hLset]; exact hx
    obtain ⟨f, hf⟩ := (Set.mem_prod_list_ofFn).1 hx'
    rw [← hf]
    refine Subgroup.list_prod_mem _ (fun j hj => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hj
    exact le_iSup (fun i : Fin k => S i) i (f i).2
  have hEq : L = ⨆ i : Fin k, S i := le_antisymm hle (iSup_le hsil)
  rw [hEq]
  exact CFSG.Quasithin.A3.commutator_iSup_eq_of_perfect S (fun i => (hS i).2.1)

private theorem r869rep_sup_perfectCore_inf_sup_eq {G : Type} [Group G] [Finite G]
    {L L' X N : Subgroup G} (hN : N = pCoreOf 2 L)
    (hL'L : L' ≤ L) (hL'perf : ⁅L', L'⁆ = L')
    (hXL : X ≤ L) (hXsup : X ⊔ N = L) :
    CFSG.Quasithin.perfectCore (X ⊓ (L' ⊔ N)) ⊔ N = L' ⊔ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := L' ⊔ N with hY
  have hNL : N ≤ L := by rw [hN]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLnormN : L ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hL'Y : L' ≤ Y := by rw [hY]; exact le_sup_left
  have hNY : N ≤ Y := by rw [hY]; exact le_sup_right
  have hYL : Y ≤ L := by rw [hY]; exact sup_le hL'L hNL
  have hXnormN : X ≤ Subgroup.normalizer (N : Set G) := hXL.trans hLnormN
  have hXN : (X : Set G) * (N : Set G) = (L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X N hXnormN, hXsup]
  have hX''supN : (X ⊓ Y) ⊔ N = Y := by
    refine le_antisymm (sup_le inf_le_right hNY) ?_
    intro y hy
    have hyL : y ∈ L := hYL hy
    have hyXN : y ∈ (X : Set G) * (N : Set G) := by rw [hXN]; exact hyL
    obtain ⟨x, hxX, n, hnN, hxn⟩ := hyXN
    have hxY : x ∈ Y := by
      have hxeq : x = y * n⁻¹ := by rw [← hxn]; group
      rw [hxeq]
      exact Y.mul_mem hy (Y.inv_mem (hNY hnN))
    rw [← hxn]
    exact Subgroup.mul_mem_sup ⟨hxX, hxY⟩ hnN
  set N' : Subgroup ↥Y := N.subgroupOf Y with hN'
  have : N'.Normal := by
    rw [hN']
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr (hYL.trans hLnormN)
  let K := ↥Y ⧸ N'
  let q : ↥Y →* K := QuotientGroup.mk' N'
  have hL'normN : L' ≤ Subgroup.normalizer (N : Set G) := hL'L.trans hLnormN
  let φ : ↥L' →* K := q.comp (Subgroup.inclusion hL'Y)
  have hφ_surj : Function.Surjective φ := by
    intro k
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' k
    have hyY : (y : G) ∈ L' ⊔ N := hY.le y.2
    have hy : (y : G) ∈ (L' : Set G) * (N : Set G) := by
      have hyY' : (y : G) ∈ (↑(L' ⊔ N) : Set G) := hyY
      rwa [Subgroup.coe_mul_of_left_le_normalizer_right L' N hL'normN] at hyY'
    obtain ⟨l, hlL', n, hnN, hln⟩ := hy
    refine ⟨⟨l, hlL'⟩, ?_⟩
    show q (Subgroup.inclusion hL'Y ⟨l, hlL'⟩) = q y
    have hy_eq : y = Subgroup.inclusion hL'Y ⟨l, hlL'⟩ *
        Subgroup.inclusion hNY ⟨n, hnN⟩ := by
      ext
      rw [Subgroup.coe_mul, Subgroup.coe_inclusion, Subgroup.coe_inclusion]
      exact hln.symm
    rw [hy_eq, map_mul]
    have hnN' : Subgroup.inclusion hNY ⟨n, hnN⟩ ∈ N' := by
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact hnN
    have hq1 : q (Subgroup.inclusion hNY ⟨n, hnN⟩) = 1 :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hNY ⟨n, hnN⟩)).mpr hnN'
    rw [hq1, mul_one]
  have : Group.IsPerfect ↥L' := Subgroup.isPerfect_iff.mpr hL'perf
  have hKperf : Group.IsPerfect K := Group.IsPerfect.ofSurjective hφ_surj
  have hcoretop : CFSG.Quasithin.perfectCore (⊤ : Subgroup K) = ⊤ := by
    apply CFSG.Quasithin.perfectCore_eq_self_of_perfect
    exact (Subgroup.isPerfect_iff (H := (⊤ : Subgroup K))).mp
      (Group.IsPerfect.top_iff.mpr hKperf)
  have hX''normN : X ⊓ Y ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hXnormN
  let ι : ↥(X ⊓ Y) →* ↥Y := Subgroup.inclusion (inf_le_right : X ⊓ Y ≤ Y)
  let ψ : ↥(X ⊓ Y) →* K := q.comp ι
  have hψ_surj : Function.Surjective ψ := by
    intro k
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N' k
    have hy : (y : G) ∈ (X ⊓ Y) ⊔ N := hX''supN.ge y.2
    have hy' : (y : G) ∈ (X ⊓ Y : Set G) * (N : Set G) := by
      have hy'' : (y : G) ∈ (↑((X ⊓ Y) ⊔ N) : Set G) := hy
      rwa [Subgroup.coe_mul_of_left_le_normalizer_right (X ⊓ Y) N hX''normN] at hy''
    obtain ⟨x, hxX'', n, hnN, hxn⟩ := hy'
    refine ⟨⟨x, hxX''⟩, ?_⟩
    show q (ι ⟨x, hxX''⟩) = q y
    have hy_eq : y = ι ⟨x, hxX''⟩ * Subgroup.inclusion hNY ⟨n, hnN⟩ := by
      ext
      rw [Subgroup.coe_mul, Subgroup.coe_inclusion, Subgroup.coe_inclusion]
      exact hxn.symm
    rw [hy_eq, map_mul]
    have hnN' : Subgroup.inclusion hNY ⟨n, hnN⟩ ∈ N' := by
      rw [hN', Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact hnN
    have hq1 : q (Subgroup.inclusion hNY ⟨n, hnN⟩) = 1 :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hNY ⟨n, hnN⟩)).mpr hnN'
    rw [hq1, mul_one]
  have hPmap : (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(X ⊓ Y))).map ψ = ⊤ := by
    rw [CFSG.Quasithin.map_perfectCore ψ (⊤ : Subgroup ↥(X ⊓ Y)),
        Subgroup.map_top_of_surjective ψ hψ_surj]
    exact hcoretop
  have hQmap : ((CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(X ⊓ Y))).map ι).map q = ⊤ := by
    rw [Subgroup.map_map]
    exact hPmap
  have hQsup : (CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(X ⊓ Y))).map ι ⊔ N' = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : q y ∈ ((CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(X ⊓ Y))).map ι).map q := by
      rw [hQmap]; exact Subgroup.mem_top _
    obtain ⟨z, hzQ, hzq⟩ := Subgroup.mem_map.mp hy
    have hzy : z⁻¹ * y ∈ N' := by
      have h1 : q (z⁻¹ * y) = 1 := by rw [map_mul, map_inv, hzq, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (z⁻¹ * y)).mp h1
    rw [show y = z * (z⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup hzQ hzy
  have hQmapG : ((CFSG.Quasithin.perfectCore (⊤ : Subgroup ↥(X ⊓ Y))).map ι).map Y.subtype
      = CFSG.Quasithin.perfectCore (X ⊓ Y) := by
    rw [Subgroup.map_map]
    have hcomp : Y.subtype.comp ι = (X ⊓ Y).subtype :=
      Subgroup.subtype_comp_inclusion (inf_le_right : X ⊓ Y ≤ Y)
    rw [hcomp, CFSG.Quasithin.map_perfectCore (X ⊓ Y).subtype (⊤ : Subgroup ↥(X ⊓ Y)),
        Subgroup.map_top, Subgroup.range_subtype]
  have h := congrArg (Subgroup.map Y.subtype) hQsup
  rw [Subgroup.map_sup, hQmapG, hN', Subgroup.map_subgroupOf_eq_of_le hNY, Subgroup.map_top,
      Subgroup.range_subtype] at h
  exact h

theorem r869_replace_false {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (hmin : MinCex869 D L X H) {L' : Subgroup G} (hL'L : L' ≤ L)
    (hnorm : L ≤ Subgroup.normalizer (L' : Set G))
    (hsh : L' ∈ calC D.M ∨
      (L' ≤ D.M ∧ D.M ≤ Subgroup.normalizer (L' : Set G) ∧ IsProdOfCalC D.M L'))
    (hnt : ¬ Thin8 L') (hne : ¬ L ≤ L' ⊔ pCoreOf 2 L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL'perf : ⁅L', L'⁆ = L' := by
    rcases hsh with h | ⟨-, -, hprod⟩
    · exact h.2.1
    · exact r869rep_perfect_of_isProdOfCalC hprod
  set N : Subgroup G := pCoreOf 2 L with hN
  set Y : Subgroup G := L' ⊔ N with hY
  set X'' : Subgroup G := X ⊓ Y with hX''
  set X' : Subgroup G := CFSG.Quasithin.perfectCore X'' with hX'
  have hX'perf : X' ⊔ N = Y := by
    rw [hX', hX'', hY]
    exact r869rep_sup_perfectCore_inf_sup_eq rfl hL'L hL'perf hmin.hyp.2.1 hmin.hyp.2.2.1
  have hNL : N ≤ L := by rw [hN]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLnormN : L ≤ Subgroup.normalizer (N : Set G) := by
    rw [hN]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hL'normN : L' ≤ Subgroup.normalizer (N : Set G) := hL'L.trans hLnormN
  have hL'Y : L' ≤ Y := by rw [hY]; exact le_sup_left
  have hNY : N ≤ Y := by rw [hY]; exact le_sup_right
  have hYnormL' : Y ≤ Subgroup.normalizer (L' : Set G) := by
    rw [hY]; exact sup_le Subgroup.le_normalizer (hNL.trans hnorm)
  have hpN : IsPGroup 2 N := by
    rw [hN]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hNsolv : Group.IsSolvable ↥N := by
    have : Group.IsNilpotent ↥N := hpN.isNilpotent
    infer_instance
  have hcore_le : CFSG.Quasithin.perfectCore Y ≤ L' :=
    CFSG.Quasithin.perfectCore_le_of_sup_solvable (A := L') (B := N) (Y := Y)
      hL'Y ((Subgroup.normal_subgroupOf_iff_le_normalizer hL'Y).mpr hYnormL') hY hNsolv
  have hX'leL' : X' ≤ L' :=
    (CFSG.Quasithin.perfectCore_mono (inf_le_right : X ⊓ Y ≤ Y)).trans hcore_le
  have hX'leY : X' ≤ Y := (CFSG.Quasithin.perfectCore_le X'').trans inf_le_right
  have hcoreLe : L' ⊓ N ≤ pCoreOf 2 L' := by
    have hnorm : L' ≤ Subgroup.normalizer ((L' ⊓ N : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer hL'normN).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      (hpN.to_le inf_le_right)
  have hL'eq : L' = X' ⊔ (L' ⊓ N) := by
    have hLN' : X' ≤ Subgroup.normalizer (N : Set G) := hX'leL'.trans hL'normN
    have hLP : X' ≤ L' ⊓ Y := le_inf hX'leL' hX'leY
    have hP : L' ⊓ Y ≤ X' ⊔ N := by rw [← hX'perf]; exact inf_le_right
    have hded := CFSG.Quasithin.A3.eq_sup_inf_of_le_sup hLN' hLP hP
    rw [inf_assoc, inf_eq_right.mpr hNY] at hded
    calc L' = L' ⊓ Y := (inf_eq_left.mpr hL'Y).symm
      _ = X' ⊔ (L' ⊓ N) := hded
  have hX'supCore : X' ⊔ pCoreOf 2 L' = L' := by
    refine le_antisymm (sup_le hX'leL' (CFSG.LieType.BorelTits.pCoreOf_le 2 L')) ?_
    calc L' = X' ⊔ (L' ⊓ N) := hL'eq
      _ ≤ X' ⊔ pCoreOf 2 L' := sup_le_sup_left hcoreLe X'
  have hX'leX : X' ≤ X := (CFSG.Quasithin.perfectCore_le X'').trans inf_le_left
  have hX'neX : X' ≠ X := by
    intro hEq
    apply hne
    have hXleL' : X ≤ L' := hEq ▸ hX'leL'
    calc L = X ⊔ pCoreOf 2 L := hmin.hyp.2.2.1.symm
      _ ≤ L' ⊔ pCoreOf 2 L := sup_le_sup_right hXleL' (pCoreOf 2 L)
  have hcard : Nat.card X' < Nat.card X := by
    have hssub : (X' : Set G) ⊂ (X : Set G) := by
      rw [ssubset_iff_subset_ne]
      exact ⟨fun x hx => hX'leX hx, fun h => hX'neX (SetLike.coe_injective h)⟩
    have h := Set.ncard_lt_ncard hssub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
    exact h
  have hHyp : Hyp869 D L' X' := ⟨hsh, hX'leL', hX'supCore, hnt⟩
  have hHmem : H ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calNOf X' :=
    ⟨hmin.mem.1, hX'leX.trans hmin.mem.2⟩
  rw [hmin.minimal L' X' hHyp hcard] at hHmem
  exact hmin.ne (Set.mem_singleton_iff.mp hHmem)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

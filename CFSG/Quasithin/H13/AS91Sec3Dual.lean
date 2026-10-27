module

public import CFSG.Quasithin.H13.AS91Sec3Orbit
public import CFSG.Quasithin.H13.AS91Sec2Abstract
public import Certificates.Certificate89017
public import CFSG.Quasithin.H13.AS91Sec3Transport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

open Classical in
@[expose] noncomputable def triosOf (U : Finset (Finset (Fin 24))) :
    Finset (Finset (Finset (Fin 24))) :=
  (octsOf U).powerset.filter IsTrio

open Classical in
@[expose] noncomputable def spreadsOf (U : Finset (Finset (Fin 24))) :
    Finset (Finset (Finset (Finset (Fin 24)))) :=
  (triosOf U).powerset.filter fun D => D.card = 5 ∧ ∀ k ∈ D, ∀ k' ∈ D, k ≠ k' → Disjoint k k'

variable {U : Finset (Finset (Fin 24))}

theorem mem_triosOf {k : Finset (Finset (Fin 24))} : k ∈ triosOf U ↔ IsTrio k ∧ TrioIn k U := by
  classical
  rw [triosOf, Finset.mem_filter, Finset.mem_powerset]
  exact and_comm

theorem mem_spreadsOf {D : Finset (Finset (Finset (Fin 24)))} : D ∈ spreadsOf U ↔
    D.card = 5 ∧ ∀ k ∈ D, IsTrio k ∧ TrioIn k U ∧ ∀ k' ∈ D, k ≠ k' → Disjoint k k' := by
  rw [spreadsOf, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hc, hd⟩
    exact ⟨hc, fun k hk => ⟨(mem_triosOf.1 (hsub hk)).1, (mem_triosOf.1 (hsub hk)).2, hd k hk⟩⟩
  · rintro ⟨hc, h⟩
    exact ⟨fun k hk => mem_triosOf.2 ⟨(h k hk).1, (h k hk).2.1⟩, hc, fun k hk => (h k hk).2.2⟩

theorem triosOf_smul {g : S24} (hg : g ∈ M24g) : triosOf (g • U) = g • triosOf U := by
  ext k
  rw [mem_triosOf, Finset.mem_smul_finset]
  constructor
  · rintro ⟨hk, hkU⟩
    refine ⟨g⁻¹ • k, mem_triosOf.2 ⟨?_, ?_⟩, smul_inv_smul g k⟩
    · exact (isTrio_smul_iff hg).1 (by rwa [smul_inv_smul])
    · exact (trioIn_smul_iff g).1 (by rwa [smul_inv_smul])
  · rintro ⟨k₀, hk₀, rfl⟩
    obtain ⟨h1, h2⟩ := mem_triosOf.1 hk₀
    exact ⟨(isTrio_smul_iff hg).2 h1, (trioIn_smul_iff g).2 h2⟩

theorem spreadsOf_smul {g : S24} (hg : g ∈ M24g) : spreadsOf (g • U) = g • spreadsOf U := by
  ext D
  rw [mem_spreadsOf, Finset.mem_smul_finset]
  constructor
  · intro h
    refine ⟨g⁻¹ • D, mem_spreadsOf.2 ?_, smul_inv_smul g D⟩
    have h' := (isOval_smul_iff hg (U := U) (D := g⁻¹ • D)).1
    rw [smul_inv_smul] at h'
    exact h' h
  · rintro ⟨D₀, hD₀, rfl⟩
    exact (isOval_smul_iff hg).2 (mem_spreadsOf.1 hD₀)

namespace Dual

theorem filter_smul_finset {α : Type*} [DecidableEq α] [MulAction S24 α] (g : S24) (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (g • s).filter p = g • s.filter fun x => p (g • x) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_smul_finset]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hp⟩
    exact ⟨y, ⟨hy, hp⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hp⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hp⟩

theorem card_filter_smul_finset {α : Type*} [DecidableEq α] [MulAction S24 α] (g : S24)
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((g • s).filter p).card = (s.filter fun x => p (g • x)).card := by
  rw [filter_smul_finset, Finset.card_smul_finset]

theorem card_filter_toFinset_map_of_injOn {α β : Type*} [DecidableEq β] {L : List α} (f : α → β)
    (hnd : L.Nodup) (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) (P : β → Prop)
    [DecidablePred P] (Q : α → Bool) (hPQ : ∀ x ∈ L, (P (f x) ↔ Q x = true)) :
    ((L.map f).toFinset.filter P).card = (L.filter Q).length := by
  have hM : (L.map f).Nodup := hnd.map_on hinj
  rw [hM.card_eq_countP, List.countP_map, List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  rw [Function.comp_apply, Bool.eq_iff_iff, decide_eq_true_eq]
  exact hPQ x hx

theorem nodup_combs {l : List ℕ} (hl : l.Nodup) (k : ℕ) : (Native.combs k l).Nodup := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => simp [Native.combs]
    | succ k => simp [Native.combs]
  | cons a l ih =>
    have hal : a ∉ l := (List.nodup_cons.1 hl).1
    have hl' : l.Nodup := (List.nodup_cons.1 hl).2
    cases k with
    | zero => simp [Native.combs]
    | succ k =>
      simp only [Native.combs]
      rw [List.nodup_append]
      refine ⟨(ih hl' k).map fun x y h => (List.cons.inj h).2, ih hl' (k + 1), ?_⟩
      intro x hx y hy hxy
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      have hy' := (mem_combs.1 hy).1
      rw [← hxy] at hy'
      exact hal (hy'.subset List.mem_cons_self)

@[expose] def sprOf (Dl : List ℕ) : Finset (Finset (Finset (Fin 24))) := (Dl.map trioFin).toFinset

@[expose] noncomputable def baseTrios : List ℕ := Native.sextTrios (Native.trioSexts ()) 0

@[expose] noncomputable def baseSpreads : List (List ℕ) :=
  (Native.combs 5 baseTrios).filter fun D =>
    D.all fun d => D.all fun k =>
      d == k || !Native.meets (Native.trioList ())[d]! (Native.trioList ())[k]!

theorem baseTrios_sorted : baseTrios.Pairwise (· < ·) := by
  unfold baseTrios Native.sextTrios
  exact pairwise_lt_filter_range _ _

theorem baseTrios_nodup : baseTrios.Nodup := baseTrios_sorted.imp fun h => ne_of_lt h

section Lists


theorem mem_baseTrios {p : ℕ} : p ∈ baseTrios ↔ p < 3795 ∧ TrioIn (trioFin p) (sextFin 0) :=
  sextTrios_iff (by norm_num)

theorem mem_triosOf_base {k : Finset (Finset (Fin 24))} :
    k ∈ triosOf (sextFin 0) ↔ ∃ p ∈ baseTrios, trioFin p = k := by
  rw [mem_triosOf]
  constructor
  · rintro ⟨hk, hkU⟩
    obtain ⟨p, hp, rfl⟩ := (isTrio_iff k).1 hk
    exact ⟨p, mem_baseTrios.2 ⟨hp, hkU⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hp1, hp2⟩ := mem_baseTrios.1 hp
    exact ⟨isTrio_trioFin hp1, hp2⟩

theorem triosOf_base : triosOf (sextFin 0) = sprOf baseTrios := by
  ext k
  rw [mem_triosOf_base, sprOf, List.mem_toFinset, List.mem_map]

theorem mem_sprOf_iff {Dl : List ℕ} (hDl : ∀ x ∈ Dl, x < 3795) {p : ℕ} (hp : p < 3795) :
    trioFin p ∈ sprOf Dl ↔ p ∈ Dl := by
  rw [sprOf, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← trioFin_injective (hDl x hx) hp h]
  · intro h
    exact ⟨p, h, rfl⟩

theorem lt_of_mem_baseTrios {p : ℕ} (hp : p ∈ baseTrios) : p < 3795 := (mem_baseTrios.1 hp).1

theorem meets_eq_false_iff {d k : ℕ} (hd : d < 3795) (hk : k < 3795) :
    Native.meets (Native.trioList ())[d]! (Native.trioList ())[k]! = false ↔
      Disjoint (trioFin d) (trioFin k) := by
  rw [Bool.eq_false_iff, ne_eq, meets_iff hd hk, not_not, disjoint_comm]

theorem mem_baseSpreads {Dl : List ℕ} : Dl ∈ baseSpreads ↔
    (Dl.Sublist baseTrios ∧ Dl.length = 5) ∧
      ∀ d ∈ Dl, ∀ k ∈ Dl, d = k ∨ Disjoint (trioFin d) (trioFin k) := by
  unfold baseSpreads
  rw [List.mem_filter, mem_combs]
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨hc, fun d hd k hk => ?_⟩
    rw [← meets_eq_false_iff (lt_of_mem_baseTrios (hc.1.subset hd))
      (lt_of_mem_baseTrios (hc.1.subset hk))]
    exact hall d hd k hk
  · rintro ⟨hc, hall⟩
    refine ⟨hc, fun d hd k hk => ?_⟩
    rw [meets_eq_false_iff (lt_of_mem_baseTrios (hc.1.subset hd))
      (lt_of_mem_baseTrios (hc.1.subset hk))]
    exact hall d hd k hk

theorem baseSpreads_nodup : baseSpreads.Nodup :=
  (nodup_combs baseTrios_nodup 5).filter _

theorem baseSpreads_sorted {Dl : List ℕ} (hDl : Dl ∈ baseSpreads) : Dl.Pairwise (· < ·) :=
  baseTrios_sorted.sublist (mem_baseSpreads.1 hDl).1.1

theorem nodup_of_mem_baseSpreads {Dl : List ℕ} (hDl : Dl ∈ baseSpreads) : Dl.Nodup :=
  (baseSpreads_sorted hDl).imp fun h => ne_of_lt h

theorem lt_of_mem_baseSpreads {Dl : List ℕ} (hDl : Dl ∈ baseSpreads) :
    ∀ x ∈ Dl, x < 3795 := fun _ hx =>
  lt_of_mem_baseTrios ((mem_baseSpreads.1 hDl).1.1.subset hx)

theorem trioFin_injOn_baseSpread {Dl : List ℕ} (hDl : Dl ∈ baseSpreads) :
    ∀ x ∈ Dl, ∀ y ∈ Dl, trioFin x = trioFin y → x = y := fun x hx y hy h =>
  trioFin_injective (lt_of_mem_baseSpreads hDl x hx) (lt_of_mem_baseSpreads hDl y hy) h

theorem sprOf_injOn {Dl Dl' : List ℕ} (hDl : Dl ∈ baseSpreads) (hDl' : Dl' ∈ baseSpreads)
    (h : sprOf Dl = sprOf Dl') : Dl = Dl' := by
  apply List.Pairwise.eq_of_mem_iff (baseSpreads_sorted hDl) (baseSpreads_sorted hDl')
  intro x
  constructor
  · intro hx
    rw [← mem_sprOf_iff (lt_of_mem_baseSpreads hDl') (lt_of_mem_baseSpreads hDl x hx), ← h,
      mem_sprOf_iff (lt_of_mem_baseSpreads hDl) (lt_of_mem_baseSpreads hDl x hx)]
    exact hx
  · intro hx
    rw [← mem_sprOf_iff (lt_of_mem_baseSpreads hDl) (lt_of_mem_baseSpreads hDl' x hx), h,
      mem_sprOf_iff (lt_of_mem_baseSpreads hDl') (lt_of_mem_baseSpreads hDl' x hx)]
    exact hx

theorem exists_idx_finset {D : Finset (Finset (Finset (Fin 24)))}
    (hD : ∀ k ∈ D, k ∈ triosOf (sextFin 0)) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p ∈ baseTrios) ∧ S.image trioFin = D := by
  refine ⟨baseTrios.toFinset.filter fun p => trioFin p ∈ D, fun p hp => ?_, ?_⟩
  · exact List.mem_toFinset.1 (Finset.mem_filter.1 hp).1
  · ext k
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨p, ⟨-, hp⟩, rfl⟩
      exact hp
    · intro hk
      obtain ⟨p, hp, rfl⟩ := mem_triosOf_base.1 (hD k hk)
      exact ⟨p, ⟨hp, hk⟩, rfl⟩

theorem sprOf_mem_spreadsOf {Dl : List ℕ} (hDl : Dl ∈ baseSpreads) :
    sprOf Dl ∈ spreadsOf (sextFin 0) := by
  obtain ⟨⟨hsub, hlen⟩, hdisj⟩ := mem_baseSpreads.1 hDl
  refine mem_spreadsOf.2 ⟨?_, fun k hk => ?_⟩
  · rw [sprOf, List.toFinset_card_of_nodup ((nodup_of_mem_baseSpreads hDl).map_on
      (trioFin_injOn_baseSpread hDl)), List.length_map, hlen]
  · rw [sprOf, List.mem_toFinset, List.mem_map] at hk
    obtain ⟨d, hd, rfl⟩ := hk
    obtain ⟨hd1, hd2⟩ := mem_baseTrios.1 (hsub.subset hd)
    refine ⟨isTrio_trioFin hd1, hd2, fun k' hk' hne => ?_⟩
    rw [sprOf, List.mem_toFinset, List.mem_map] at hk'
    obtain ⟨k, hk, rfl⟩ := hk'
    rcases hdisj d hd k hk with h | h
    · exact absurd (by rw [h]) hne
    · exact h

theorem exists_baseSpread {D : Finset (Finset (Finset (Fin 24)))}
    (hD : D ∈ spreadsOf (sextFin 0)) : ∃ Dl ∈ baseSpreads, sprOf Dl = D := by
  obtain ⟨hcard, hD⟩ := mem_spreadsOf.1 hD
  obtain ⟨S, hSb, hSD⟩ := exists_idx_finset (D := D) fun k hk =>
    mem_triosOf.2 ⟨(hD k hk).1, (hD k hk).2.1⟩
  have hSl : ∀ p ∈ S, p < 3795 := fun p hp => lt_of_mem_baseTrios (hSb p hp)
  have hScard : S.card = 5 := by
    rw [← hcard, ← hSD, Finset.card_image_of_injOn]
    intro x hx y hy h
    exact trioFin_injective (hSl x hx) (hSl y hy) h
  have hcomb := sort_mem_combs baseTrios_sorted hSb
  rw [hScard] at hcomb
  have hmemD : ∀ p ∈ S, trioFin p ∈ D := fun p hp => by
    rw [← hSD]
    exact Finset.mem_image_of_mem _ hp
  refine ⟨S.sort, ?_, ?_⟩
  · rw [mem_baseSpreads]
    refine ⟨⟨(mem_combs.1 hcomb).1, (mem_combs.1 hcomb).2⟩, fun d hd k hk => ?_⟩
    rw [Finset.mem_sort] at hd hk
    by_cases hdk : d = k
    · exact Or.inl hdk
    · exact Or.inr ((hD _ (hmemD d hd)).2.2 _ (hmemD k hk)
        fun e => hdk (trioFin_injective (hSl d hd) (hSl k hk) e))
  · rw [sprOf, ← hSD]
    ext k
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Finset.mem_sort]

theorem spreadsOf_base : spreadsOf (sextFin 0) = (baseSpreads.map sprOf).toFinset := by
  ext D
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨exists_baseSpread, fun ⟨_, hDl, h⟩ => h ▸ sprOf_mem_spreadsOf hDl⟩

end Lists

section Facts


theorem sextDual_parts :
    baseTrios.length = 15 ∧ baseSpreads.length = 6 ∧
      (∀ l ∈ baseTrios, (baseSpreads.filter (·.contains l)).length = 2) ∧
      (∀ D ∈ baseSpreads, ∀ D' ∈ baseSpreads, D = D' ∨ (D.filter (D'.contains ·)).length = 1) ∧
      (∀ D ∈ baseSpreads, ∀ o ∈ Native.octsS (Native.sextList ())[0]!,
        (D.filter fun k => (Native.octsT (Native.trioList ())[k]!).contains o).length = 1) ∧
      (∀ c ∈ Native.combs 3 baseTrios,
        (c.all fun a => c.all fun b =>
          a == b || Native.meets (Native.trioList ())[a]! (Native.trioList ())[b]!) = false ∨
        ((Native.octsS (Native.sextList ())[0]!).any fun o =>
          c.all fun k => (Native.octsT (Native.trioList ())[k]!).contains o) = true) ∧
      (∀ a ∈ baseTrios, ∀ b ∈ baseTrios, a = b ∨
        Native.meets (Native.trioList ())[a]! (Native.trioList ())[b]! =
          !(baseSpreads.any fun D => D.contains a && D.contains b)) := by
  have h : Native.sextDualCheck () = true := Certificates.certificate89017
  simp only [Native.sextDualCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem card_triosOf_base : (triosOf (sextFin 0)).card = 15 := by
  obtain ⟨h1, -⟩ := sextDual_parts
  rw [triosOf_base, sprOf, List.toFinset_card_of_nodup, List.length_map, h1]
  exact baseTrios_nodup.map_on fun x hx y hy h =>
    trioFin_injective (lt_of_mem_baseTrios hx) (lt_of_mem_baseTrios hy) h

theorem card_spreadsOf_base : (spreadsOf (sextFin 0)).card = 6 := by
  obtain ⟨-, h2, -⟩ := sextDual_parts
  rw [spreadsOf_base, List.toFinset_card_of_nodup, List.length_map, h2]
  exact baseSpreads_nodup.map_on fun x hx y hy h => sprOf_injOn hx hy h

theorem card_spreads_through_base :
    ∀ k ∈ triosOf (sextFin 0), ((spreadsOf (sextFin 0)).filter (k ∈ ·)).card = 2 := by
  obtain ⟨-, -, h3, -⟩ := sextDual_parts
  intro k hk
  obtain ⟨l, hl, rfl⟩ := mem_triosOf_base.1 hk
  rw [spreadsOf_base, card_filter_toFinset_map_of_injOn sprOf baseSpreads_nodup
    (fun x hx y hy h => sprOf_injOn hx hy h) (trioFin l ∈ ·) (fun Dl => Dl.contains l)]
  · exact h3 l hl
  · intro Dl hDl
    rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl) (lt_of_mem_baseTrios hl), List.contains_eq_mem,
      decide_eq_true_eq]

theorem card_inter_spreads_base :
    ∀ D ∈ spreadsOf (sextFin 0), ∀ D' ∈ spreadsOf (sextFin 0), D ≠ D' → (D ∩ D').card = 1 := by
  obtain ⟨-, -, -, h4, -⟩ := sextDual_parts
  intro D hD D' hD' hne
  rw [spreadsOf_base] at hD hD'
  obtain ⟨Dl, hDl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hD)
  obtain ⟨Dl', hDl', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hD')
  have h := (h4 Dl hDl Dl' hDl').resolve_left fun e => hne (by rw [e])
  have hsp : sprOf Dl = (Dl.map trioFin).toFinset := rfl
  rw [← Finset.filter_mem_eq_inter, hsp, card_filter_toFinset_map_of_injOn trioFin
    (nodup_of_mem_baseSpreads hDl) (trioFin_injOn_baseSpread hDl) (· ∈ sprOf Dl')
    (fun x => Dl'.contains x)]
  · exact h
  · intro x hx
    rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl') (lt_of_mem_baseSpreads hDl x hx),
      List.contains_eq_mem, decide_eq_true_eq]

theorem card_spread_pencil_base :
    ∀ D ∈ spreadsOf (sextFin 0), ∀ o ∈ octsOf (sextFin 0), (D.filter (o ∈ ·)).card = 1 := by
  obtain ⟨-, -, -, -, h5, -⟩ := sextDual_parts
  intro D hD o ho
  rw [spreadsOf_base] at hD
  obtain ⟨Dl, hDl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hD)
  rw [octsOf_sextFin (by norm_num), List.mem_toFinset, List.mem_map] at ho
  obtain ⟨m, hm, rfl⟩ := ho
  have hmlt := octsS_lt (sextList_lt (by norm_num)) m hm
  rw [sprOf, card_filter_toFinset_map_of_injOn trioFin (nodup_of_mem_baseSpreads hDl)
    (trioFin_injOn_baseSpread hDl) (maskFin m ∈ ·)
    (fun k => (Native.octsT (Native.trioList ())[k]!).contains m)]
  · exact h5 Dl hDl m hm
  · intro k hk
    rw [maskFin_mem_trioFin (lt_of_mem_baseSpreads hDl k hk) hmlt, List.contains_eq_mem,
      decide_eq_true_eq]

theorem exists_mem_combs_three {pa pb pc : ℕ} (hpa : pa ∈ baseTrios) (hpb : pb ∈ baseTrios)
    (hpc : pc ∈ baseTrios) (hab : pa ≠ pb) (hac : pa ≠ pc) (hbc : pb ≠ pc) :
    ∃ c ∈ Native.combs 3 baseTrios, ∀ x, x ∈ c ↔ x = pa ∨ x = pb ∨ x = pc := by
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = {pa, pb, pc} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ x = pa ∨ x = pb ∨ x = pc := fun x => by rw [hS]; simp
  have hScard : S.card = 3 := by
    rw [hS]
    exact Finset.card_eq_three.2 ⟨pa, pb, pc, hab, hac, hbc, rfl⟩
  have hcomb := sort_mem_combs baseTrios_sorted (S := S) fun x hx => by
    rcases (hmem x).1 hx with rfl | rfl | rfl <;> assumption
  rw [hScard] at hcomb
  exact ⟨_, hcomb, fun x => by rw [Finset.mem_sort, hmem]⟩

theorem exists_common_octad_base {a b c : Finset (Finset (Fin 24))}
    (ha : a ∈ triosOf (sextFin 0)) (hb : b ∈ triosOf (sextFin 0)) (hc : c ∈ triosOf (sextFin 0))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h₁ : ¬ Disjoint a b) (h₂ : ¬ Disjoint a c)
    (h₃ : ¬ Disjoint b c) : ∃ o ∈ octsOf (sextFin 0), o ∈ a ∧ o ∈ b ∧ o ∈ c := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := sextDual_parts
  obtain ⟨pa, hpa, rfl⟩ := mem_triosOf_base.1 ha
  obtain ⟨pb, hpb, rfl⟩ := mem_triosOf_base.1 hb
  obtain ⟨pc, hpc, rfl⟩ := mem_triosOf_base.1 hc
  obtain ⟨l, hl, hlmem⟩ := exists_mem_combs_three hpa hpb hpc (fun e => hab (by rw [e]))
    (fun e => hac (by rw [e])) (fun e => hbc (by rw [e]))
  have hlb : ∀ x ∈ l, x ∈ baseTrios := fun x hx => by
    rcases (hlmem x).1 hx with rfl | rfl | rfl <;> assumption
  have hm : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ¬ Disjoint (trioFin x) (trioFin y) := by
    intro x hx y hy hxy
    rcases (hlmem x).1 hx with rfl | rfl | rfl <;> rcases (hlmem y).1 hy with rfl | rfl | rfl <;>
      first | exact absurd rfl hxy | assumption | (rw [disjoint_comm]; assumption)
  rcases h6 l hl with h | h
  · refine absurd h ?_
    rw [Bool.not_eq_false, List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro y hy
    rw [Bool.or_eq_true, beq_iff_eq]
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ((meets_iff (lt_of_mem_baseTrios (hlb x hx))
        (lt_of_mem_baseTrios (hlb y hy))).2 (hm y hy x hx (Ne.symm hxy)))
  · obtain ⟨m, hmo, hall⟩ := List.any_eq_true.1 h
    have hmlt := octsS_lt (sextList_lt (by norm_num)) m hmo
    have hcont : ∀ k ∈ l, maskFin m ∈ trioFin k := fun k hk => by
      rw [maskFin_mem_trioFin (lt_of_mem_baseTrios (hlb k hk)) hmlt]
      simpa using List.all_eq_true.1 hall k hk
    refine ⟨maskFin m, (maskFin_mem_octsOf_sextFin (by norm_num) hmlt).2 hmo,
      hcont pa ((hlmem pa).2 (Or.inl rfl)), hcont pb ((hlmem pb).2 (Or.inr (Or.inl rfl))),
      hcont pc ((hlmem pc).2 (Or.inr (Or.inr rfl)))⟩

theorem not_disjoint_iff_base {a b : Finset (Finset (Fin 24))} (ha : a ∈ triosOf (sextFin 0))
    (hb : b ∈ triosOf (sextFin 0)) (hab : a ≠ b) :
    ¬ Disjoint a b ↔ ∀ D ∈ spreadsOf (sextFin 0), ¬ (a ∈ D ∧ b ∈ D) := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := sextDual_parts
  obtain ⟨pa, hpa, rfl⟩ := mem_triosOf_base.1 ha
  obtain ⟨pb, hpb, rfl⟩ := mem_triosOf_base.1 hb
  have h := (h7 pa hpa pb hpb).resolve_left fun e => hab (by rw [e])
  have hpa3 := lt_of_mem_baseTrios hpa
  have hpb3 := lt_of_mem_baseTrios hpb
  rw [disjoint_comm, ← meets_iff hpa3 hpb3, h, Bool.not_eq_true']
  constructor
  · intro hany D hD
    rw [spreadsOf_base] at hD
    obtain ⟨Dl, hDl, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hD)
    rintro ⟨h1, h2⟩
    rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl) hpa3] at h1
    rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl) hpb3] at h2
    have hany' : (baseSpreads.any fun D => D.contains pa && D.contains pb) = true :=
      List.any_eq_true.2 ⟨Dl, hDl, by simp [h1, h2]⟩
    rw [hany] at hany'
    simp at hany'
  · intro hall
    rw [Bool.eq_false_iff, ne_eq, List.any_eq_true]
    rintro ⟨Dl, hDl, hc⟩
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hc
    have hmem : sprOf Dl ∈ spreadsOf (sextFin 0) := by
      rw [spreadsOf_base]
      exact List.mem_toFinset.2 (List.mem_map.2 ⟨Dl, hDl, rfl⟩)
    refine hall (sprOf Dl) hmem ⟨?_, ?_⟩
    · rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl) hpa3]
      exact hc.1
    · rw [mem_sprOf_iff (lt_of_mem_baseSpreads hDl) hpb3]
      exact hc.2

end Facts

end Dual

section Final

open Dual


theorem card_triosOf (hU : IsSextet U) : (triosOf U).card = 15 := by
  refine forall_sextet_of_base (P := fun U => (triosOf U).card = 15) ?_ card_triosOf_base hU
  intro g hg U h
  show (triosOf (g • U)).card = 15
  rw [triosOf_smul hg, Finset.card_smul_finset]
  exact h

theorem card_spreadsOf (hU : IsSextet U) : (spreadsOf U).card = 6 := by
  refine forall_sextet_of_base (P := fun U => (spreadsOf U).card = 6) ?_ card_spreadsOf_base hU
  intro g hg U h
  show (spreadsOf (g • U)).card = 6
  rw [spreadsOf_smul hg, Finset.card_smul_finset]
  exact h

theorem stmt2_1_1_triosOf (hU : IsSextet U) :
    (∀ k ∈ triosOf U, ((spreadsOf U).filter (k ∈ ·)).card = 2) ∧
      ∀ D ∈ spreadsOf U, ∀ D' ∈ spreadsOf U, D ≠ D' → (D ∩ D').card = 1 := by
  refine forall_sextet_of_base (P := fun U =>
    (∀ k ∈ triosOf U, ((spreadsOf U).filter (k ∈ ·)).card = 2) ∧
      ∀ D ∈ spreadsOf U, ∀ D' ∈ spreadsOf U, D ≠ D' → (D ∩ D').card = 1) ?_
    ⟨card_spreads_through_base, card_inter_spreads_base⟩ hU
  rintro g hg U ⟨h1, h2⟩
  refine ⟨fun k hk => ?_, fun D hD D' hD' hne => ?_⟩
  · rw [triosOf_smul hg] at hk
    obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_smul_finset.1 hk
    rw [spreadsOf_smul hg, card_filter_smul_finset]
    simpa only [Finset.smul_mem_smul_finset_iff] using h1 k₀ hk₀
  · rw [spreadsOf_smul hg] at hD hD'
    obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_smul_finset.1 hD
    obtain ⟨D₁, hD₁, rfl⟩ := Finset.mem_smul_finset.1 hD'
    rw [← Finset.smul_finset_inter, Finset.card_smul_finset]
    exact h2 D₀ hD₀ D₁ hD₁ fun e => hne (by rw [e])

theorem stmt2_1_2_triosOf (hU : IsSextet U) :
    ∀ D ∈ spreadsOf U, ∀ o ∈ octsOf U, (D.filter (o ∈ ·)).card = 1 := by
  refine forall_sextet_of_base (P := fun U =>
    ∀ D ∈ spreadsOf U, ∀ o ∈ octsOf U, (D.filter (o ∈ ·)).card = 1) ?_ card_spread_pencil_base hU
  intro g hg U h D hD o ho
  rw [spreadsOf_smul hg] at hD
  rw [octsOf_smul] at ho
  obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_smul_finset.1 hD
  obtain ⟨o₀, ho₀, rfl⟩ := Finset.mem_smul_finset.1 ho
  rw [card_filter_smul_finset]
  simpa only [Finset.smul_mem_smul_finset_iff] using h D₀ hD₀ o₀ ho₀

theorem card_pencil (hU : IsSextet U) {o : Finset (Fin 24)} (ho : o ∈ octsOf U) :
    ((triosOf U).filter (o ∈ ·)).card = 3 := by
  have h2 := (stmt2_1_1_triosOf hU).1
  have h5 := stmt2_1_2_triosOf hU
  have h6 := card_spreadsOf hU
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (D : Finset (Finset (Finset (Fin 24)))) (k : Finset (Finset (Fin 24))) => k ∈ D)
    (s := spreadsOf U) (t := (triosOf U).filter (o ∈ ·))
  have hL : ∑ D ∈ spreadsOf U, (((triosOf U).filter (o ∈ ·)).bipartiteAbove
      (fun (D : Finset (Finset (Finset (Fin 24)))) (k : Finset (Finset (Fin 24))) => k ∈ D)
        D).card = ∑ _D ∈ spreadsOf U, 1 := by
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [← h5 D hD o ho]
    congr 1
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, hok⟩, hkD⟩
      exact ⟨hkD, hok⟩
    · rintro ⟨hkD, hok⟩
      obtain ⟨hk1, hk2, -⟩ := (mem_spreadsOf.1 hD).2 k hkD
      exact ⟨⟨mem_triosOf.2 ⟨hk1, hk2⟩, hok⟩, hkD⟩
  have hR : ∑ k ∈ (triosOf U).filter (o ∈ ·), ((spreadsOf U).bipartiteBelow
      (fun (D : Finset (Finset (Finset (Fin 24)))) (k : Finset (Finset (Fin 24))) => k ∈ D)
        k).card = ∑ _k ∈ (triosOf U).filter (o ∈ ·), 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← h2 k (Finset.mem_filter.1 hk).1]
    rfl
  rw [hL, hR] at key
  simp only [Finset.sum_const, smul_eq_mul] at key
  omega

theorem exists_common_octad (hU : IsSextet U) {a b c : Finset (Finset (Fin 24))}
    (ha : a ∈ triosOf U) (hb : b ∈ triosOf U) (hc : c ∈ triosOf U) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h₁ : ¬ Disjoint a b) (h₂ : ¬ Disjoint a c) (h₃ : ¬ Disjoint b c) :
    ∃ o ∈ octsOf U, o ∈ a ∧ o ∈ b ∧ o ∈ c := by
  have h := forall_sextet_of_base (P := fun U =>
    ∀ a ∈ triosOf U, ∀ b ∈ triosOf U, ∀ c ∈ triosOf U, a ≠ b → a ≠ c → b ≠ c → ¬ Disjoint a b →
      ¬ Disjoint a c → ¬ Disjoint b c → ∃ o ∈ octsOf U, o ∈ a ∧ o ∈ b ∧ o ∈ c) ?_
    (fun a ha b hb c hc hab hac hbc h₁ h₂ h₃ =>
      exists_common_octad_base ha hb hc hab hac hbc h₁ h₂ h₃) hU
  · exact h a ha b hb c hc hab hac hbc h₁ h₂ h₃
  · intro g hg U h a ha b hb c hc hab hac hbc h₁ h₂ h₃
    rw [triosOf_smul hg] at ha hb hc
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_smul_finset.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_smul_finset.1 hb
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_smul_finset.1 hc
    rw [disjoint_smul_finset_iff] at h₁ h₂ h₃
    obtain ⟨o, ho, h1, h2, h3⟩ := h a₀ ha₀ b₀ hb₀ c₀ hc₀ (fun e => hab (by rw [e]))
      (fun e => hac (by rw [e])) (fun e => hbc (by rw [e])) h₁ h₂ h₃
    refine ⟨g • o, ?_, Finset.smul_mem_smul_finset h1, Finset.smul_mem_smul_finset h2,
      Finset.smul_mem_smul_finset h3⟩
    rw [octsOf_smul]
    exact Finset.smul_mem_smul_finset ho

theorem not_disjoint_iff_spreadsOf (hU : IsSextet U) {a b : Finset (Finset (Fin 24))}
    (ha : a ∈ triosOf U) (hb : b ∈ triosOf U) (hab : a ≠ b) :
    ¬ Disjoint a b ↔ ∀ D ∈ spreadsOf U, ¬ (a ∈ D ∧ b ∈ D) := by
  have h := forall_sextet_of_base (P := fun U =>
    ∀ a ∈ triosOf U, ∀ b ∈ triosOf U, a ≠ b →
      (¬ Disjoint a b ↔ ∀ D ∈ spreadsOf U, ¬ (a ∈ D ∧ b ∈ D))) ?_
    (fun a ha b hb hab => not_disjoint_iff_base ha hb hab) hU
  · exact h a ha b hb hab
  · intro g hg U h a ha b hb hab
    rw [triosOf_smul hg] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_smul_finset.1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_smul_finset.1 hb
    rw [disjoint_smul_finset_iff, spreadsOf_smul hg,
      h a₀ ha₀ b₀ hb₀ fun e => hab (by rw [e])]
    constructor
    · intro hall D hD
      obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_smul_finset.1 hD
      rw [Finset.smul_mem_smul_finset_iff, Finset.smul_mem_smul_finset_iff]
      exact hall D₀ hD₀
    · intro hall D₀ hD₀
      have h' := hall (g • D₀) (Finset.smul_mem_smul_finset hD₀)
      rwa [Finset.smul_mem_smul_finset_iff, Finset.smul_mem_smul_finset_iff] at h'

theorem stmt2_2_triosOf (hU : IsSextet U) {S : Finset (Finset (Finset (Fin 24)))}
    (hSP : S ⊆ triosOf U) (hS : S.Nonempty)
    (h3 : ∀ D ∈ spreadsOf U, ¬ Disjoint D S → (D ∩ S).card = 3) :
    (∃ d ∈ triosOf U, S = (triosOf U).filter (fun k => k ≠ d ∧ ¬ Disjoint k d) ∧ S.card = 6 ∧
        ((spreadsOf U).filter fun D => ¬ Disjoint D S).card = 4) ∨ S.card = 9 := by
  have h2 := stmt2_1_1_triosOf hU
  rcases Sp4.six_blocks (triosOf U) (spreadsOf U) (card_spreadsOf hU)
      (fun D hD k hk => mem_triosOf.2 ⟨((mem_spreadsOf.1 hD).2 k hk).1,
        ((mem_spreadsOf.1 hD).2 k hk).2.1⟩) h2.1 h2.2 S hSP hS h3 with
      ⟨d, hd, hSd, h6, h4⟩ | h9
  · refine Or.inl ⟨d, hd, ?_, h6, h4⟩
    rw [hSd]
    ext k
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hk, hno⟩
      have hkd : k ≠ d := by
        rintro rfl
        obtain ⟨D, hD⟩ : ∃ D, D ∈ (spreadsOf U).filter (k ∈ ·) :=
          Finset.card_pos.1 (by rw [h2.1 k hk]; norm_num)
        obtain ⟨hDB, hkD⟩ := Finset.mem_filter.1 hD
        exact hno D hDB ⟨hkD, hkD⟩
      refine ⟨hk, hkd, ?_⟩
      rw [not_disjoint_iff_spreadsOf hU hk hd hkd]
      rintro D hDB ⟨hk', hd'⟩
      exact hno D hDB ⟨hd', hk'⟩
    · rintro ⟨hk, hkd, hnd⟩
      refine ⟨hk, fun D hDB ⟨hd', hk'⟩ => ?_⟩
      exact (not_disjoint_iff_spreadsOf hU hk hd hkd).1 hnd D hDB ⟨hk', hd'⟩
  · exact Or.inr h9

end Final

end CFSG.Quasithin.H13.AS91.M24G

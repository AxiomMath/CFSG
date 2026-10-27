module

public import CFSG.Quasithin.H13.AS91Sec3Defs
public import CFSG.Quasithin.Background.H153Sext

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem disjoint_smul_finset_iff {β : Type*} [DecidableEq β] [MulAction S24 β] (g : S24)
    {s t : Finset β} : Disjoint (g • s) (g • t) ↔ Disjoint s t :=
  Finset.disjoint_image (MulAction.injective g)

theorem exists_smul_iff {β : Type*} [MulAction S24 β] (g : S24) (P : β → Prop) :
    (∃ x, P (g • x)) ↔ ∃ x, P x :=
  (MulAction.surjective g).exists.symm

theorem forall_smul_iff {β : Type*} [MulAction S24 β] (g : S24) (P : β → Prop) :
    (∀ x, P (g • x)) ↔ ∀ x, P x :=
  (MulAction.surjective g).forall.symm

theorem isOctad_smul_iff {g : S24} (hg : g ∈ M24g) {O : Finset (Fin 24)} :
    IsOctad (g • O) ↔ IsOctad O :=
  ⟨fun h => by simpa using CFSG.Quasithin.H153.isOctad_smul (M24g.inv_mem hg) h,
    CFSG.Quasithin.H153.isOctad_smul hg⟩

theorem isTrio_smul {g : S24} (hg : g ∈ M24g) {l : Finset (Finset (Fin 24))}
    (h : IsTrio l) : IsTrio (g • l) := by
  obtain ⟨hc, ho, hd, hu⟩ := h
  refine ⟨by rw [Finset.card_smul_finset]; exact hc, ?_, ?_, ?_⟩
  · intro O hO
    obtain ⟨O₁, hO₁, rfl⟩ := Finset.mem_smul_finset.1 hO
    exact (isOctad_smul_iff hg).2 (ho O₁ hO₁)
  · intro O hO O' hO' hne
    obtain ⟨O₁, hO₁, rfl⟩ := Finset.mem_smul_finset.1 hO
    obtain ⟨O₂, hO₂, rfl⟩ := Finset.mem_smul_finset.1 hO'
    have h12 : O₁ ≠ O₂ := fun e => hne (by rw [e])
    exact (disjoint_smul_finset_iff g).2 (hd O₁ hO₁ O₂ hO₂ h12)
  · ext x
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    have hx : g⁻¹ x ∈ l.biUnion id := by rw [hu]; exact Finset.mem_univ _
    obtain ⟨O₁, hO₁, hxO⟩ := Finset.mem_biUnion.1 hx
    exact ⟨g • O₁, Finset.mem_smul_finset.2 ⟨O₁, hO₁, rfl⟩,
      Finset.mem_smul_finset.2 ⟨g⁻¹ x, hxO, by simp⟩⟩

theorem isTrio_smul_iff {g : S24} (hg : g ∈ M24g) {l : Finset (Finset (Fin 24))} :
    IsTrio (g • l) ↔ IsTrio l :=
  ⟨fun h => by simpa using isTrio_smul (M24g.inv_mem hg) h, isTrio_smul hg⟩

theorem isSextet_smul_iff {g : S24} (hg : g ∈ M24g) {S : Finset (Finset (Fin 24))} :
    IsSextet (g • S) ↔ IsSextet S :=
  ⟨fun h => by simpa using CFSG.Quasithin.H153.isSextet_smul (M24g.inv_mem hg) h,
    CFSG.Quasithin.H153.isSextet_smul hg⟩

theorem mem_octsOf {S : Finset (Finset (Fin 24))} {x : Finset (Fin 24)} :
    x ∈ octsOf S ↔ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∪ b = x := by
  simp only [octsOf, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩
    exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩

theorem octsOf_smul (g : S24) (S : Finset (Finset (Fin 24))) :
    octsOf (g • S) = g • octsOf S := by
  ext x
  rw [mem_octsOf, Finset.mem_smul_finset]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    obtain ⟨a₁, ha₁, rfl⟩ := Finset.mem_smul_finset.1 ha
    obtain ⟨b₁, hb₁, rfl⟩ := Finset.mem_smul_finset.1 hb
    exact ⟨a₁ ∪ b₁, mem_octsOf.2 ⟨a₁, ha₁, b₁, hb₁, fun e => hab (by rw [e]), rfl⟩,
      Finset.smul_finset_union⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_octsOf.1 hy
    exact ⟨g • a, Finset.smul_mem_smul_finset ha, g • b, Finset.smul_mem_smul_finset hb,
      fun e => hab (smul_left_cancel g e), Finset.smul_finset_union.symm⟩

theorem trioIn_smul_iff (g : S24) {l S : Finset (Finset (Fin 24))} :
    TrioIn (g • l) (g • S) ↔ TrioIn l S := by
  unfold TrioIn
  rw [octsOf_smul, Finset.smul_finset_subset_smul_finset_iff]

theorem coplanar_smul_iff {g : S24} (hg : g ∈ M24g) {l k : Finset (Finset (Fin 24))} :
    Coplanar (g • l) (g • k) ↔ Coplanar l k := by
  unfold Coplanar
  rw [← exists_smul_iff g]
  exact exists_congr fun _ => and_congr (isSextet_smul_iff hg)
    (and_congr (trioIn_smul_iff g) (trioIn_smul_iff g))

theorem inZeta_smul_iff (g : S24) {l : Finset (Finset (Fin 24))} {O : Finset (Fin 24)} :
    InZeta (g • l) (g • O) ↔ InZeta l O := by
  unfold InZeta
  rw [Finset.smul_mem_smul_finset_iff]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u, hu, hd⟩
    obtain ⟨u₁, hu₁, rfl⟩ := Finset.mem_smul_finset.1 hu
    exact ⟨u₁, hu₁, (disjoint_smul_finset_iff g).1 hd⟩
  · rintro ⟨u, hu, hd⟩
    exact ⟨g • u, Finset.smul_mem_smul_finset hu, (disjoint_smul_finset_iff g).2 hd⟩

theorem filter_inZeta_smul (g : S24) (l k : Finset (Finset (Fin 24))) :
    (g • k).filter (InZeta (g • l)) = g • k.filter (InZeta l) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hz⟩ := Finset.mem_filter.1 hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
    exact Finset.mem_smul_finset.2 ⟨y, Finset.mem_filter.2 ⟨hy, (inZeta_smul_iff g).1 hz⟩, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
    rw [Finset.mem_filter] at hy
    exact Finset.mem_filter.2 ⟨Finset.smul_mem_smul_finset hy.1, (inZeta_smul_iff g).2 hy.2⟩

theorem delta_smul_iff {g : S24} (hg : g ∈ M24g) {l k : Finset (Finset (Fin 24))} (i : Fin 5) :
    Delta (g • l) (g • k) i ↔ Delta l k i := by
  match i with
  | 0 => exact smul_left_cancel_iff g
  | 1 =>
    exact and_congr (not_congr (smul_left_cancel_iff g)) (not_congr (disjoint_smul_finset_iff g))
  | 2 => exact and_congr (disjoint_smul_finset_iff g) (coplanar_smul_iff hg)
  | 3 =>
    show ((g • k).filter (InZeta (g • l))).card = 1 ↔ (k.filter (InZeta l)).card = 1
    rw [filter_inZeta_smul, Finset.card_smul_finset]
  | 4 =>
    show ((g • k).filter (InZeta (g • l))).card = 0 ↔ (k.filter (InZeta l)).card = 0
    rw [filter_inZeta_smul, Finset.card_smul_finset]

theorem xi_smul_iff {g : S24} (_hg : g ∈ M24g) {U W : Finset (Finset (Fin 24))} (i : Fin 4) :
    Xi (g • U) (g • W) i ↔ Xi U W i := by
  match i with
  | 0 => exact smul_left_cancel_iff g
  | 1 =>
    show (octsOf (g • W) ∩ octsOf (g • U)).card = 3 ↔ (octsOf W ∩ octsOf U).card = 3
    rw [octsOf_smul, octsOf_smul, ← Finset.smul_finset_inter, Finset.card_smul_finset]
  | 2 =>
    show (octsOf (g • W) ∩ octsOf (g • U)).card = 1 ↔ (octsOf W ∩ octsOf U).card = 1
    rw [octsOf_smul, octsOf_smul, ← Finset.smul_finset_inter, Finset.card_smul_finset]
  | 3 =>
    show Disjoint (octsOf (g • W)) (octsOf (g • U)) ↔ Disjoint (octsOf W) (octsOf U)
    rw [octsOf_smul, octsOf_smul, disjoint_smul_finset_iff]

theorem exists_sextet_xi_one_smul_iff {g : S24} (hg : g ∈ M24g) {U l : Finset (Finset (Fin 24))} :
    (∃ W, IsSextet W ∧ Xi (g • U) W 1 ∧ TrioIn (g • l) W) ↔
      ∃ W, IsSextet W ∧ Xi U W 1 ∧ TrioIn l W := by
  rw [← exists_smul_iff g]
  exact exists_congr fun _ => and_congr (isSextet_smul_iff hg)
    (and_congr (xi_smul_iff hg 1) (trioIn_smul_iff g))

theorem kappa_smul_iff {g : S24} (hg : g ∈ M24g) {U l : Finset (Finset (Fin 24))} (i : Fin 4) :
    Kappa (g • U) (g • l) i ↔ Kappa U l i := by
  match i with
  | 0 => exact trioIn_smul_iff g
  | 1 =>
    show ((g • l) ∩ octsOf (g • U)).card = 1 ↔ (l ∩ octsOf U).card = 1
    rw [octsOf_smul, ← Finset.smul_finset_inter, Finset.card_smul_finset]
  | 2 =>
    show Disjoint (g • l) (octsOf (g • U)) ∧ (∃ W, IsSextet W ∧ Xi (g • U) W 1 ∧
        TrioIn (g • l) W) ↔ Disjoint l (octsOf U) ∧ ∃ W, IsSextet W ∧ Xi U W 1 ∧ TrioIn l W
    rw [octsOf_smul, disjoint_smul_finset_iff, exists_sextet_xi_one_smul_iff hg]
  | 3 =>
    show Disjoint (g • l) (octsOf (g • U)) ∧ ¬ (∃ W, IsSextet W ∧ Xi (g • U) W 1 ∧
        TrioIn (g • l) W) ↔ Disjoint l (octsOf U) ∧ ¬ ∃ W, IsSextet W ∧ Xi U W 1 ∧ TrioIn l W
    rw [octsOf_smul, disjoint_smul_finset_iff, exists_sextet_xi_one_smul_iff hg]

theorem isDisc_smul_iff {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} :
    (∃ d, IsTrio d ∧ TrioIn d (g • U) ∧
        ∀ k, k ∈ g • D ↔ IsTrio k ∧ TrioIn k (g • U) ∧ k ≠ d ∧ ¬ Disjoint k d) ↔
      ∃ d, IsTrio d ∧ TrioIn d U ∧
        ∀ k, k ∈ D ↔ IsTrio k ∧ TrioIn k U ∧ k ≠ d ∧ ¬ Disjoint k d := by
  rw [← exists_smul_iff g]
  refine exists_congr fun _ => and_congr (isTrio_smul_iff hg) (and_congr (trioIn_smul_iff g) ?_)
  rw [← forall_smul_iff g]
  refine forall_congr' fun _ => ?_
  rw [Finset.smul_mem_smul_finset_iff]
  exact iff_congr Iff.rfl (and_congr (isTrio_smul_iff hg) (and_congr (trioIn_smul_iff g)
    (and_congr (not_congr (smul_left_cancel_iff g)) (not_congr (disjoint_smul_finset_iff g)))))

theorem isOval_smul_iff {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} :
    ((g • D).card = 5 ∧ ∀ k ∈ g • D, IsTrio k ∧ TrioIn k (g • U) ∧
        ∀ k' ∈ g • D, k ≠ k' → Disjoint k k') ↔
      D.card = 5 ∧ ∀ k ∈ D, IsTrio k ∧ TrioIn k U ∧ ∀ k' ∈ D, k ≠ k' → Disjoint k k' := by
  rw [Finset.card_smul_finset]
  refine and_congr Iff.rfl ?_
  rw [← forall_smul_iff g]
  refine forall_congr' fun _ => ?_
  rw [Finset.smul_mem_smul_finset_iff]
  refine imp_congr Iff.rfl (and_congr (isTrio_smul_iff hg) (and_congr (trioIn_smul_iff g) ?_))
  rw [← forall_smul_iff g]
  refine forall_congr' fun _ => ?_
  rw [Finset.smul_mem_smul_finset_iff]
  exact imp_congr Iff.rfl
    (imp_congr (not_congr (smul_left_cancel_iff g)) (disjoint_smul_finset_iff g))

theorem isDiscOrOval_smul_iff {g : S24} (hg : g ∈ M24g) {U : Finset (Finset (Fin 24))}
    {D : Finset (Finset (Finset (Fin 24)))} :
    IsDiscOrOval (g • U) (g • D) ↔ IsDiscOrOval U D :=
  or_congr (isDisc_smul_iff hg) (isOval_smul_iff hg)

end CFSG.Quasithin.H13.AS91.M24G

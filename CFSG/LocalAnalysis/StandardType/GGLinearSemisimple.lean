module

public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimpleBasic

public section

namespace CFSG.StandardType

open CFSG.SeitzReduction.LinearPilot Matrix
open scoped commutatorElement

namespace LinSemisimple

variable {m : ℕ} {F : Type} [Field F] {ι : Type*}

section Quasisimple

variable {G : Type*} [Group G]

theorem false_of_isQuasisimple_of_commute {L : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple L)
    (h : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) : False := by
  obtain ⟨-, -, a, b, hab⟩ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  have hL : ∀ x y : L, x * y = y * x := fun x y => Subtype.ext (h _ x.2 _ y.2)
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL a b]

theorem false_of_isQuasisimple_of_le_isSolvable {L S : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple L) (hLS : L ≤ S) [Group.IsSolvable S] : False := by
  have : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLS)
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial L).ne hq.1

theorem commutator_eq_self_of_isQuasisimple {L : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple L) : ⁅L, L⁆ = L := by
  have h := congrArg (Subgroup.map L.subtype) hq.1
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

end Quasisimple

theorem natCard_ne_three [Finite F] [CharP F 2] : Nat.card F ≠ 3 := by
  intro h3
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  rw [← Nat.card_eq_fintype_card, h3] at h
  exact absurd h (by decide)

section Centralizer

variable {G : Type*} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
  {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}

theorem exists_lift_of_mem_centralizer
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) {x : G}
    (hx : x ∈ ψ.range ⊓ Subgroup.centralizer (Set.range b)) :
    ∃ u, ψ u = x ∧ ∀ k, u⁻¹ * InnerDiagA.conjSL (InnerDiagA.diagGL (d k)) u ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  obtain ⟨⟨u, rfl⟩, hxb⟩ := Subgroup.mem_inf.mp hx
  refine ⟨u, rfl, fun k => hker ?_⟩
  have hk : b k * ψ u = ψ u * b k := Subgroup.mem_centralizer_iff.mp hxb (b k) ⟨k, rfl⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← LinFusion.mem_ggInducedPairs.mp (hb k) u, hk,
    mul_inv_cancel_right, inv_mul_cancel]

theorem commutator_le_map_diagCentSL
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) :
    ⁅ψ.range ⊓ Subgroup.centralizer (Set.range b),
      ψ.range ⊓ Subgroup.centralizer (Set.range b)⁆ ≤ (diagCentSL d).map ψ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨u, rfl, hu⟩ := exists_lift_of_mem_centralizer hker hb hx
  obtain ⟨v, rfl, hv⟩ := exists_lift_of_mem_centralizer hker hb hy
  exact ⟨⁅u, v⁆, commutatorElement_mem_diagCentSL hu hv, map_commutatorElement ψ u v⟩

theorem map_diagCentSL_le
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) :
    (diagCentSL d).map ψ ≤ ψ.range ⊓ Subgroup.centralizer (Set.range b) := by
  rintro _ ⟨u, hu, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, rfl⟩
  have h1 := LinFusion.mem_ggInducedPairs.mp (hb k) u
  rw [mem_diagCentSL.mp hu k] at h1
  calc b k * ψ u = b k * ψ u * (b k)⁻¹ * b k := by group
    _ = ψ u * b k := by rw [h1]

theorem normal_subgroupOf_map_blockSpecialLinear
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G) (d : ι → Fin (m + 1) → Fˣ)
    (i : Fin (m + 1)) :
    (((blockSpecialLinear (eigClass d i)).map ψ).subgroupOf ((diagCentSL d).map ψ)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨s, hs, hsn⟩ := hn
  obtain ⟨u, hu, hug⟩ := g.2
  refine ⟨u * s * u⁻¹, conj_mem_blockSpecialLinear_eigClass hu i hs, ?_⟩
  simp only [map_mul, map_inv, hsn, hug, Subgroup.coe_mul, Subgroup.coe_inv]

theorem le_or_commutator_eq_bot [Finite G] {L₁ : Subgroup G} (hLC : L₁ ≤ (diagCentSL d).map ψ)
    (hcomp : CFSG.Assembly.IsComponentOf L₁ ((diagCentSL d).map ψ)) (i : Fin (m + 1)) :
    L₁ ≤ (blockSpecialLinear (eigClass d i)).map ψ ∨
      ⁅L₁, (blockSpecialLinear (eigClass d i)).map ψ⁆ = ⊥ := by
  have hc :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLC).mp hcomp
  rcases CFSG.LocalAnalysis.ComponentInitial.component_normal_subgroup hc
      (normal_subgroupOf_map_blockSpecialLinear ψ d i) with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hLC h)
  · right
    have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLC h
    rwa [inf_eq_left.mpr (Subgroup.map_mono (blockSpecialLinear_eigClass_le_diagCentSL d i))]
      at h'

end Centralizer

theorem isQuasisimple_specialLinearGroup_finset [Finite F] [CharP F 2] {n : ℕ}
    {I : Finset (Fin n)} (h2 : 2 ≤ I.card) (h22 : I.card ≠ 2 ∨ Nat.card F ≠ 2) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup I F) :=
  (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (reindexSpecialLinear (K := F) I.equivFin)).2
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple I.card F h2
      h22 (Or.inr natCard_ne_three))

section Blocks

variable {G : Type*} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem map_blockSpecialLinear_eq_range (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (I : Finset (Fin (m + 1))) :
    (blockSpecialLinear I).map ψ = (ψ.comp (blockEmbed I)).range := by
  rw [MonoidHom.range_comp, range_blockEmbed]

theorem two_le_card_of_isQuasisimple_le [Finite F] [CharP F 2] {I : Finset (Fin (m + 1))}
    {L₁ : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple L₁)
    (hL : L₁ ≤ (blockSpecialLinear I).map ψ) : 2 ≤ I.card ∧ (I.card ≠ 2 ∨ Nat.card F ≠ 2) := by
  classical
  refine ⟨?_, ?_⟩
  · by_contra h1
    refine false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hL hx
    obtain ⟨s', hs', rfl⟩ := hL hy
    rw [← map_mul, ← map_mul, blockSpecialLinear_commute_of_card_le_one (by omega) hs hs']
  · by_contra h22
    rw [not_or, not_not, not_not] at h22
    have : Group.IsSolvable (GL (Fin 2) F) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
        (Or.inl h22.2)
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
      Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
    have : Group.IsSolvable (Matrix.SpecialLinearGroup I F) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (reindexSpecialLinear (K := F) (I.equivFin.trans (finCongr h22.1))).toMonoidHom)
        (reindexSpecialLinear (K := F) (I.equivFin.trans (finCongr h22.1))).injective
    have hS : Group.IsSolvable (ψ.comp (blockEmbed I)).range :=
      Group.isSolvable_of_surjective (ψ.comp (blockEmbed I)).rangeRestrict_surjective
    rw [← map_blockSpecialLinear_eq_range] at hS
    exact false_of_isQuasisimple_of_le_isSolvable hq hL

theorem eq_of_isComponentOf_map_blockSpecialLinear [Finite F] [CharP F 2]
    {I : Finset (Fin (m + 1))} {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ ((blockSpecialLinear I).map ψ)) :
    L₁ = (blockSpecialLinear I).map ψ := by
  classical
  have hq := hL.2.2
  obtain ⟨h2, h22⟩ := two_le_card_of_isQuasisimple_le hq hL.1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images
      (isQuasisimple_specialLinearGroup_finset (F := F) h2 h22) (ψ.comp (blockEmbed I)) with h | h
  · exfalso
    rw [← map_blockSpecialLinear_eq_range] at h
    refine false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
    have hx1 : x = 1 := by
      have := hL.1 hx
      rwa [h, Subgroup.mem_bot] at this
    have hy1 : y = 1 := by
      have := hL.1 hy
      rwa [h, Subgroup.mem_bot] at this
    rw [hx1, hy1]
  · rw [← map_blockSpecialLinear_eq_range] at h
    have hc :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL.1).mp hL
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups h hc.2 with h' | h'
    · exact le_antisymm hL.1 (Subgroup.subgroupOf_eq_top.mp h')
    · exfalso
      refine false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      have hxc : (⟨x, hL.1 hx⟩ : (blockSpecialLinear I).map ψ) ∈
          Subgroup.center ((blockSpecialLinear I).map ψ) :=
        h' (Subgroup.mem_subgroupOf.mpr hx)
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hL.1 hy⟩)).symm

theorem isQuasisimple_map_blockSpecialLinear [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {I : Finset (Fin (m + 1))} (h2 : 2 ≤ I.card) (h22 : I.card ≠ 2 ∨ Nat.card F ≠ 2) :
    CFSG.Assembly.IsQuasisimple ((blockSpecialLinear I).map ψ) := by
  classical
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images
      (isQuasisimple_specialLinearGroup_finset (F := F) h2 h22) (ψ.comp (blockEmbed I)) with h | h
  · exfalso
    rw [← map_blockSpecialLinear_eq_range] at h
    obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
    have ht : ψ (Matrix.SpecialLinearGroup.transvection hjl (1 : F)) ∈
        (blockSpecialLinear I).map ψ :=
      Subgroup.mem_map_of_mem ψ (transvection_mem_blockSpecialLinear hjl hj hl 1)
    rw [h, Subgroup.mem_bot] at ht
    exact one_ne_zero
      (InnerDiagA.eq_zero_of_transvection_mem_center hjl (hker (MonoidHom.mem_ker.mpr ht)))
  · rw [← map_blockSpecialLinear_eq_range] at h
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr h

end Blocks

section Components

variable {G : Type*} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem false_of_forall_commutator_eq_bot [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {d : ι → Fin (m + 1) → Fˣ} {L₁ : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple L₁)
    (hLC : L₁ ≤ (diagCentSL d).map ψ)
    (h : ∀ i, ⁅L₁, (blockSpecialLinear (eigClass d i)).map ψ⁆ = ⊥) : False := by
  have hdiag : ∀ w ∈ diagCentSL d, ψ w ∈ L₁ →
      (w : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
    intro w hw hwL
    refine isDiag_of_commute_transvection hw fun j l hjl hd => ?_
    refine commute_of_commutatorElement_transvection_mem_center hjl (hker ?_)
    have hmem : ⁅ψ w, ψ (Matrix.SpecialLinearGroup.transvection hjl (1 : F))⁆ ∈
        ⁅L₁, (blockSpecialLinear (eigClass d j)).map ψ⁆ :=
      Subgroup.commutator_mem_commutator hwL
        (Subgroup.mem_map_of_mem ψ (transvection_mem_blockSpecialLinear_eigClass hjl hd 1))
    rw [h j, Subgroup.mem_bot, ← map_commutatorElement] at hmem
    exact MonoidHom.mem_ker.mpr hmem
  refine false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
  obtain ⟨u, hu, rfl⟩ := hLC hx
  obtain ⟨v, hv, rfl⟩ := hLC hy
  rw [← map_mul, ← map_mul, mul_comm_of_isDiag (hdiag u hu hx) (hdiag v hv hy)]

theorem exists_eq_map_blockSpecialLinear_of_isComponentOf [Finite G] [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer (Set.range b))) :
    ∃ i, L₁ = (blockSpecialLinear (eigClass d i)).map ψ := by
  have hq := hL.2.2
  have hLC : L₁ ≤ (diagCentSL d).map ψ :=
    calc L₁ = ⁅L₁, L₁⁆ := (commutator_eq_self_of_isQuasisimple hq).symm
      _ ≤ ⁅ψ.range ⊓ Subgroup.centralizer (Set.range b),
          ψ.range ⊓ Subgroup.centralizer (Set.range b)⁆ :=
        Subgroup.commutator_mono hL.1 hL.1
      _ ≤ (diagCentSL d).map ψ := commutator_le_map_diagCentSL hker hb
  have hcomp :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hLC (map_diagCentSL_le hb)
  by_cases hex : ∃ i, L₁ ≤ (blockSpecialLinear (eigClass d i)).map ψ
  · obtain ⟨i, hi⟩ := hex
    exact ⟨i, eq_of_isComponentOf_map_blockSpecialLinear
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hi
        (Subgroup.map_mono (blockSpecialLinear_eigClass_le_diagCentSL d i)))⟩
  · exfalso
    exact false_of_forall_commutator_eq_bot hker hq hLC fun i =>
      (le_or_commutator_eq_bot hLC hcomp i).resolve_left fun h => hex ⟨i, h⟩

theorem isComponentOf_map_blockSpecialLinear [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) (i : Fin (m + 1))
    (h2 : 2 ≤ (eigClass d i).card) (h22 : (eigClass d i).card ≠ 2 ∨ Nat.card F ≠ 2) :
    CFSG.Assembly.IsComponentOf ((blockSpecialLinear (eigClass d i)).map ψ)
      (ψ.range ⊓ Subgroup.centralizer (Set.range b)) := by
  have hNC : (blockSpecialLinear (eigClass d i)).map ψ ≤ (diagCentSL d).map ψ :=
    Subgroup.map_mono (blockSpecialLinear_eigClass_le_diagCentSL d i)
  have hCH := map_diagCentSL_le hb
  have hCnormal : (((diagCentSL d).map ψ).subgroupOf
      (ψ.range ⊓ Subgroup.centralizer (Set.range b))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨u, hu, hun⟩ := hn
    obtain ⟨v, hvg, hv⟩ := exists_lift_of_mem_centralizer hker hb g.2
    refine ⟨v * u * v⁻¹, conj_mem_diagCentSL hu hv, ?_⟩
    simp only [map_mul, map_inv, hun, hvg, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨hNC.trans hCH, ?_, isQuasisimple_map_blockSpecialLinear hker h2 h22⟩
  exact CFSG.Assembly.IsSubnormal.step hNC (normal_subgroupOf_map_blockSpecialLinear ψ d i)
    (CFSG.Assembly.IsSubnormal.step hCH hCnormal (CFSG.Assembly.IsSubnormal.refl _))

theorem isComponentOf_iff_exists_eq_map_blockSpecialLinear [Finite G] [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}
    (hb : ∀ k, (b k, InnerDiagA.diagGL (d k)) ∈ LinFusion.ggInducedPairs ψ) {L₁ : Subgroup G} :
    CFSG.Assembly.IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer (Set.range b)) ↔
      ∃ i, 2 ≤ (eigClass d i).card ∧ ((eigClass d i).card ≠ 2 ∨ Nat.card F ≠ 2) ∧
        L₁ = (blockSpecialLinear (eigClass d i)).map ψ := by
  constructor
  · intro hL
    obtain ⟨i, hi⟩ := exists_eq_map_blockSpecialLinear_of_isComponentOf hker hb hL
    obtain ⟨h2, h22⟩ := two_le_card_of_isQuasisimple_le hL.2.2 hi.le
    exact ⟨i, h2, h22, hi⟩
  · rintro ⟨i, h2, h22, rfl⟩
    exact isComponentOf_map_blockSpecialLinear hker hb i h2 h22

end Components

section Frame

variable {G : Type*} [Group G] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

theorem range_comp_conjSL (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (A : GL (Fin (m + 1)) F) : (ψ.comp (InnerDiagA.conjSL A)).range = ψ.range := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨InnerDiagA.conjSL A⁻¹ u, ?_⟩
    rw [MonoidHom.comp_apply, ← LinFusion.conjSL_mul, mul_inv_cancel, LinFusion.conjSL_one]

theorem mem_ggInducedPairs_comp_conjSL {P : GL (Fin (m + 1)) F} {e : Fin (m + 1) → Fˣ} {g : G}
    (hg : (g, LinFusion.ggFrameDiag P e) ∈ LinFusion.ggInducedPairs ψ) :
    (g, InnerDiagA.diagGL e) ∈ LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) := by
  intro u
  show g * ψ (InnerDiagA.conjSL P⁻¹ u) * g⁻¹ =
    ψ (InnerDiagA.conjSL P⁻¹ (InnerDiagA.conjSL (InnerDiagA.diagGL e) u))
  rw [LinFusion.mem_ggInducedPairs.mp hg, LinFusion.ggFrameDiag, ← LinFusion.conjSL_mul,
    ← LinFusion.conjSL_mul,
    show P⁻¹ * InnerDiagA.diagGL e * P * P⁻¹ = P⁻¹ * InnerDiagA.diagGL e by group]

theorem exists_eq_ggFrameBlock_of_isComponentOf [Finite G] [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (P : GL (Fin (m + 1)) F) {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}
    (hb : ∀ k, (b k, LinFusion.ggFrameDiag P (d k)) ∈ LinFusion.ggInducedPairs ψ)
    {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer (Set.range b))) :
    ∃ I : Finset (Fin (m + 1)), L₁ = LinFusion.ggFrameBlock F ψ P I ∧
      ∀ k, ∀ i ∈ I, ∀ j ∈ I, d k i = d k j := by
  rw [← range_comp_conjSL ψ P⁻¹] at hL
  obtain ⟨i, hi⟩ := exists_eq_map_blockSpecialLinear_of_isComponentOf
    (LinFusion.ker_comp_conjSL_le_center hker P⁻¹) (fun k => mem_ggInducedPairs_comp_conjSL (hb k))
    hL
  exact ⟨eigClass d i, hi, fun k j hj l hl => eq_of_mem_eigClass hj hl k⟩

theorem isComponentOf_iff_exists_eq_ggFrameBlock [Finite G] [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (P : GL (Fin (m + 1)) F) {d : ι → Fin (m + 1) → Fˣ} {b : ι → G}
    (hb : ∀ k, (b k, LinFusion.ggFrameDiag P (d k)) ∈ LinFusion.ggInducedPairs ψ)
    {L₁ : Subgroup G} :
    CFSG.Assembly.IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer (Set.range b)) ↔
      ∃ i, 2 ≤ (eigClass d i).card ∧ ((eigClass d i).card ≠ 2 ∨ Nat.card F ≠ 2) ∧
        L₁ = LinFusion.ggFrameBlock F ψ P (eigClass d i) := by
  rw [← range_comp_conjSL ψ P⁻¹]
  exact isComponentOf_iff_exists_eq_map_blockSpecialLinear
    (LinFusion.ker_comp_conjSL_le_center hker P⁻¹) (fun k => mem_ggInducedPairs_comp_conjSL (hb k))

theorem exists_eq_ggFrameBlock_of_le_ggFrameTorus [Finite G] [Finite F] [CharP F 2]
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (P : GL (Fin (m + 1)) F) {D : Subgroup G} (hD : D ≤ LinFusion.ggFrameTorus F ψ P)
    {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ I : Finset (Fin (m + 1)), L₁ = LinFusion.ggFrameBlock F ψ P I ∧
      ∀ g ∈ D, ∃ e : Fin (m + 1) → Fˣ, (g, LinFusion.ggFrameDiag P e) ∈
        LinFusion.ggInducedPairs ψ ∧ ∀ i ∈ I, ∀ j ∈ I, e i = e j := by
  have hD' : ∀ g : D, ∃ e : Fin (m + 1) → Fˣ,
      ((g : G), LinFusion.ggFrameDiag P e) ∈ LinFusion.ggInducedPairs ψ := fun g => hD g.2
  choose e he using hD'
  have hr : Set.range (fun g : D => (g : G)) = (D : Set G) := Subtype.range_coe
  rw [← hr] at hL
  obtain ⟨I, hI, hc⟩ := exists_eq_ggFrameBlock_of_isComponentOf hker P he hL
  exact ⟨I, hI, fun g hg => ⟨e ⟨g, hg⟩, he ⟨g, hg⟩, hc ⟨g, hg⟩⟩⟩

end Frame

end LinSemisimple

theorem ggLinearSemisimpleComponentInput_holds : GGLinearSemisimpleComponentInput := by
  intro G _ _ m f ψ hker P d b hb L₁ hL
  have hL' : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer (Set.range fun _ : Unit => b)) := by
    rwa [Set.range_const]
  obtain ⟨I, hI, hc⟩ := LinSemisimple.exists_eq_ggFrameBlock_of_isComponentOf hker P
    (d := fun _ : Unit => d) (b := fun _ => b) (fun _ => hb) hL'
  exact ⟨I, hI, hc ()⟩

section Inputs

theorem ggStepTwoLinearFusionInput_of_frameInput (hL : GGLinearFrameInput)
    (hU : GGStepTwoUnitaryFusionInput) : GGStepTwoLinearFusionInput :=
  ggStepTwoLinearFusionInput_of_frame ggLinearSemisimpleComponentInput_holds hL hU

theorem ggStepTwoLinearFusionInput_of_frameEqInput (hL : GGLinearFrameEqInput)
    (hU : GGStepTwoUnitaryFusionInput) : GGStepTwoLinearFusionInput :=
  ggStepTwoLinearFusionInput_of_frameEq ggLinearSemisimpleComponentInput_holds hL hU

end Inputs

end CFSG.StandardType

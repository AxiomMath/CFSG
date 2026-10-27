module

public import CFSG.Quasithin.H13.NQCoreEscapingOrbit
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin

theorem isCComponent_perfectResidual_of_isSimpleGroup {Q : Type} [Group Q] [Finite Q]
    {J : Subgroup Q} [J.Normal] (hJ : Group.IsSolvable J)
    [IsSimpleGroup ↥((CFSG.perfectResidual Q).map (QuotientGroup.mk' J))]
    (hna : ¬ IsMulCommutative ↥((CFSG.perfectResidual Q).map (QuotientGroup.mk' J))) :
    CFSG.IsCComponent (CFSG.perfectResidual Q) := by
  obtain ⟨-, hYc, hYp, -, -, -⟩ := CFSG.perfect_residual_characterization (G := Q)
  have hYn : (CFSG.perfectResidual Q).Normal := inferInstance
  have hSn : ((CFSG.perfectResidual Q).map (QuotientGroup.mk' J)).Normal :=
    hYn.map _ (QuotientGroup.mk'_surjective J)
  have hSC := isCComponent_of_isSimpleGroup hna hSn.isSubnormal
  obtain ⟨hC, -⟩ := (NQBlock.Ccomponent_solvable_quotient_bijection J hJ).2 _ hSC
  set K := ((CFSG.perfectResidual Q).map (QuotientGroup.mk' J)).comap (QuotientGroup.mk' J)
    with hK
  have hYK : CFSG.perfectResidual Q ≤ K := le_comap_map _ _
  have hlift : (CFSG.perfectResidual ↥K).map K.subtype = CFSG.perfectResidual Q := by
    refine le_antisymm ((CFSG.perfect_residual_transport (MonoidHom.id Q)).2.1 K) ?_
    have hperf : Group.IsPerfect ↥((CFSG.perfectResidual Q).subgroupOf K) := by
      rw [Subgroup.isPerfect_iff]
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYK]
      exact Subgroup.isPerfect_iff.mp hYp
    have h1 := Subgroup.map_mono (f := K.subtype)
      ((CFSG.perfect_residual_transport (MonoidHom.id ↥K)).2.2 _ hperf)
    rwa [Subgroup.map_subgroupOf_eq_of_le hYK] at h1
  rwa [hlift] at hC

theorem nonempty_quotient_center_equiv {Q : Type*} [Group Q] {Y J : Subgroup Q} [J.Normal]
    {q : Subgroup ↥Y} [q.Normal] (hq : q ≤ (Y ⊓ J).subgroupOf Y)
    (hC : ((Y ⊓ J).subgroupOf Y).map (QuotientGroup.mk' q) = center (↥Y ⧸ q)) :
    Nonempty ((↥Y ⧸ q) ⧸ center (↥Y ⧸ q) ≃* ↥(Y.map (QuotientGroup.mk' J))) := by
  set f := (QuotientGroup.mk' J).subgroupMap Y with hf
  have hker : f.ker = (Y ⊓ J).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro hy
      have h1 : QuotientGroup.mk' J (y : Q) = 1 := congrArg Subtype.val hy
      exact ⟨y.2, (QuotientGroup.eq_one_iff _).mp h1⟩
    · intro hy
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hy.2)
  have hqf : q ≤ f.ker := hker ▸ hq
  set g := QuotientGroup.lift q f hqf with hg
  have hgs : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective q f (MonoidHom.subgroupMap_surjective _ _) hqf
  have hgker : g.ker = center (↥Y ⧸ q) := by
    rw [hg, QuotientGroup.ker_lift, hker, hC]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩

theorem nonempty_quotient_pCore_map_equiv {G : Type*} [Group G] (H : Subgroup G)
    (Y : Subgroup ↥H) :
    Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ≃*
      (↥(Y.map H.subtype) ⧸ CFSG.pCore 2 ↥(Y.map H.subtype))) :=
  ⟨QuotientGroup.congr _ _ (Y.equivMapOfInjective H.subtype H.subtype_injective)
    (CFSG.pCore_map_iso 2 (Y.equivMapOfInjective H.subtype H.subtype_injective))⟩

theorem map_center_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') :
    (center Q).map e.toMonoidHom = center Q' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hx
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    show e g' * e x = e x * e g'
    rw [← map_mul, ← map_mul, hx g']
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_center_iff] at hy
    rw [SetLike.mem_coe, mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy (e g)]

theorem isPerfect_of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : Group.IsPerfect Q) : Group.IsPerfect Q' := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ commutator Q := h.commutator_eq_top ▸ mem_top x
  have h1 := Subgroup.mem_map_of_mem e.toMonoidHom hx
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr e.surjective, ← _root_.commutator_def] at h1

theorem qt13Five_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : QT13Five Q) : QT13Five Q' := by
  rcases h with h5 | hL | h6 | ⟨hp, hc, he6⟩ | hU
  · obtain ⟨e5⟩ := h5
    exact Or.inl ⟨e.symm.trans e5⟩
  · exact Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL))
  · obtain ⟨e6⟩ := h6
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans e6⟩))
  · obtain ⟨e6⟩ := he6
    have hZ := map_center_mulEquiv e
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨isPerfect_of_mulEquiv e hp, ?_, ?_⟩)))
    · rw [← hZ, Subgroup.card_map_of_injective e.injective, hc]
    · exact ⟨(QuotientGroup.congr _ _ e hZ).symm.trans e6⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hU))))

theorem center_eq_bot_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hna : ∃ a b : Q, a * b ≠ b * a) : center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ center Q := h ▸ mem_top b
    exact hab (mem_center_iff.mp hb a)

theorem card_center_of_qt13Five
    {Q : Type} [Group Q] (h : QT13Five Q) (hna : ∃ a b : Q, a * b ≠ b * a) :
    center Q = ⊥ ∨ (Nat.card (center Q) = 3 ∧ Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 6)))
    := by
  rcases h with h5 | hL | h6 | ⟨-, hc, he⟩ | hU
  · obtain ⟨e5⟩ := h5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
    have : IsSimpleGroup Q := e5.isSimpleGroup
    exact Or.inl (center_eq_bot_of_isSimpleGroup hna)
  · have : IsSimpleGroup Q := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL
    exact Or.inl (center_eq_bot_of_isSimpleGroup hna)
  · obtain ⟨e6⟩ := h6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Q := e6.isSimpleGroup
    exact Or.inl (center_eq_bot_of_isSimpleGroup hna)
  · exact Or.inr ⟨hc, he⟩
  · have : IsSimpleGroup Q := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
    exact Or.inl (center_eq_bot_of_isSimpleGroup hna)

end CFSG.Quasithin.H13.NQCore

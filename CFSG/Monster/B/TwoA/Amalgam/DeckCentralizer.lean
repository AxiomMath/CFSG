module

public import CFSG.Monster.B.TwoA.Amalgam.DeckLift
public import CFSG.Monster.B.TwoA.Amalgam.DeckIdent
public import CFSG.Monster.B.TwoA.Amalgam.Lifted

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

theorem liftParabolic_le_coverHt
    (a : chamberCS.Cover baseChamber) (i : Fin 4) :
    liftParabolic chamberCS chamberCS_adj_iff a i ≤ coverHt :=
  inf_le_left

theorem exists_surj_liftParabolic
    {a : chamberCS.Cover baseChamber}
    (ha : chamberCS.coverProj baseChamber a = baseChamber) (i : Fin 4) :
    ∃ φ : Pc i →* liftParabolic chamberCS chamberCS_adj_iff a i, Function.Surjective φ ∧
      ∀ g : Pc i, chamberCS.liftProj baseChamber (φ g : chamberCS.LiftPair baseChamber) =
        coverRho (Subgroup.inclusion (Pc_le_Eam i) g) := by
  obtain ⟨e, he⟩ := (short_F4_lifted_parabolic_stabilizers a ha).2.1 i
  exact exists_surj_of_mulEquiv_quotient_subgroupOf (Pc_le_Eam i) _ coverRho e he

theorem liftProj_injective_liftParabolic
    {a : chamberCS.Cover baseChamber}
    (ha : chamberCS.coverProj baseChamber a = baseChamber) (i : Fin 4)
    {z z' : liftParabolic chamberCS chamberCS_adj_iff a i}
    (h : chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) =
      chamberCS.liftProj baseChamber (z' : chamberCS.LiftPair baseChamber)) : z = z' := by
  obtain ⟨e, he⟩ := (short_F4_lifted_parabolic_stabilizers a ha).2.1 i
  exact eq_of_mulEquiv_quotient _ coverRho e he h

theorem liftParabolic_compat
    {a : chamberCS.Cover baseChamber}
    (ha : chamberCS.coverProj baseChamber a = baseChamber)
    {φ₁ : Pc 0 →* liftParabolic chamberCS chamberCS_adj_iff a 0}
    (hφ₁ : ∀ g : Pc 0, chamberCS.liftProj baseChamber (φ₁ g : chamberCS.LiftPair baseChamber) =
      coverRho (Subgroup.inclusion (Pc_le_Eam 0) g))
    {φ₄ : P4 →* liftParabolic chamberCS chamberCS_adj_iff a 3}
    (hφ₄ : ∀ g : P4, chamberCS.liftProj baseChamber (φ₄ g : chamberCS.LiftPair baseChamber) =
      coverRho (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g))
    (x : Dfull) (h₀ : x ∈ Pc 0) (h₃ : x ∈ P4) :
    (φ₁ ⟨x, h₀⟩ : chamberCS.LiftPair baseChamber) = φ₄ ⟨x, h₃⟩ := by
  obtain ⟨e, he⟩ := (short_F4_lifted_parabolic_stabilizers a ha).2.2.2.1 0 3 (by decide)
  have hg : (⟨x, Pc_le_Eam 0 h₀⟩ : Eam) ∈ (Pc 0 ⊓ Pc 3).subgroupOf Eam :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h₀, h₃⟩)
  have hz := (he (e.symm (QuotientGroup.mk ⟨_, hg⟩)) ⟨_, hg⟩).1 (e.apply_symm_apply _)
  have h1 := liftProj_injective_liftParabolic ha 0
    (z := ⟨_, (Subgroup.mem_inf.1 (e.symm (QuotientGroup.mk ⟨_, hg⟩)).2).1⟩)
    (hz.trans (hφ₁ ⟨x, h₀⟩).symm)
  have h4 := liftProj_injective_liftParabolic ha 3
    (z := ⟨_, (Subgroup.mem_inf.1 (e.symm (QuotientGroup.mk ⟨_, hg⟩)).2).2⟩)
    (hz.trans (hφ₄ ⟨x, h₃⟩).symm)
  exact (congrArg Subtype.val h1).symm.trans (congrArg Subtype.val h4)

theorem liftBorel_le_liftParabolic
    {a : chamberCS.Cover baseChamber}
    (ha : chamberCS.coverProj baseChamber a = baseChamber) (i : Fin 4) :
    liftBorel chamberCS chamberCS_adj_iff a ≤ liftParabolic chamberCS chamberCS_adj_iff a i :=
  (le_of_eq (short_F4_lifted_parabolic_stabilizers a ha).2.2.2.2.2.1.symm).trans
    (iInf_le (fun j : Fin 4 => liftParabolic chamberCS chamberCS_adj_iff a j) i)

theorem liftBorel_subgroupOf_liftParabolic
    {a : chamberCS.Cover baseChamber}
    (ha : chamberCS.coverProj baseChamber a = baseChamber) (i : Fin 4)
    {φ : Pc i →* liftParabolic chamberCS chamberCS_adj_iff a i}
    (hφ : ∀ g : Pc i, chamberCS.liftProj baseChamber (φ g : chamberCS.LiftPair baseChamber) =
      coverRho (Subgroup.inclusion (Pc_le_Eam i) g)) :
    (liftBorel chamberCS chamberCS_adj_iff a).subgroupOf
        (liftParabolic chamberCS chamberCS_adj_iff a i) = (Bam.subgroupOf (Pc i)).map φ := by
  obtain ⟨eB, heB⟩ := (short_F4_lifted_parabolic_stabilizers a ha).2.2.1
  obtain ⟨hB1, hB2⟩ := exists_of_mulEquiv_quotient _ coverRho eB heB
  refine subgroupOf_eq_map_of_lift (chamberCS.liftProj baseChamber)
    (liftBorel_le_liftParabolic ha i) (fun z z' h => liftProj_injective_liftParabolic ha i h)
    (ρ := fun g => coverRho (Subgroup.inclusion (Pc_le_Eam i) g)) hφ (fun z hz => ?_)
    (fun g hg => ?_)
  · obtain ⟨b, hb⟩ := hB1 z hz
    have hbB : ((b : Eam) : Dfull) ∈ Bam := Subgroup.mem_subgroupOf.1 b.2
    exact ⟨⟨(b : Eam), Bam_le_Pc i hbB⟩, Subgroup.mem_subgroupOf.2 hbB, hb⟩
  · obtain ⟨z, hz, hpz⟩ := hB2 ⟨Subgroup.inclusion (Pc_le_Eam i) g, Subgroup.mem_subgroupOf.2 hg⟩
    exact ⟨z, hz, hpz⟩

theorem short_F4_deck_centralizer_classical_images
    (a : chamberCS.Cover baseChamber)
    (ha : chamberCS.coverProj baseChamber a = baseChamber)
    (α₁ : liftParabolic chamberCS chamberCS_adj_iff a 0 →* SigmaU6)
    (hα₁ : ∀ (z : liftParabolic chamberCS chamberCS_adj_iff a 0) (g : Pc 0),
      chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) =
        coverRho (Subgroup.inclusion (Pc_le_Eam 0) g) → α₁ z = rhoP1 g)
    (α₄ : liftParabolic chamberCS chamberCS_adj_iff a 3 →* OA8)
    (hα₄ : ∀ (z : liftParabolic chamberCS chamberCS_adj_iff a 3) (g : P4),
      chamberCS.liftProj baseChamber (z : chamberCS.LiftPair baseChamber) =
        coverRho (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g) → α₄ z = p4Proj g) :
    ((deckCent coverHt coverK).subgroupOf coverHt).Normal ∧
      psuSub.comap α₁ ≤
        (deckCent coverHt coverK).subgroupOf (liftParabolic chamberCS chamberCS_adj_iff a 0) ∧
      orthD ≤ ((deckCent coverHt coverK).subgroupOf
        (liftParabolic chamberCS chamberCS_adj_iff a 3)).map α₄ ∧
      psuSub ⊓ flagStabU ≤
        ((deckCent coverHt coverK ⊓ liftBorel chamberCS chamberCS_adj_iff a).subgroupOf
          (liftParabolic chamberCS chamberCS_adj_iff a 0)).map α₁ ∧
      orthD ⊓ flagStabO ≤
        ((deckCent coverHt coverK ⊓ liftBorel chamberCS chamberCS_adj_iff a).subgroupOf
          (liftParabolic chamberCS chamberCS_adj_iff a 3)).map α₄ := by
  obtain ⟨-, -, -, -, -, -, -, -, hHt, hK, -, -, -, -, -, hPK⟩ := short_F4_universal_building_cover
  have := hHt
  have := hK
  have : Finite (liftParabolic chamberCS chamberCS_adj_iff a 0) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (liftParabolic_le_coverHt a 0))
  obtain ⟨φ₁, hφ₁s, hφ₁⟩ := exists_surj_liftParabolic ha 0
  obtain ⟨φ₄, hφ₄s, hφ₄⟩ := exists_surj_liftParabolic ha 3
  exact deck_centralizer_classical_images_of
    (fun g _ k hk => (MonoidHom.normal_ker _).conj_mem k hk g) (Dvd.intro_left _ hPK)
    (liftParabolic_le_coverHt a 0) (liftParabolic_le_coverHt a 3) φ₁ hφ₁s φ₄ hφ₄s
    (liftParabolic_compat ha hφ₁ hφ₄) α₁ (fun g => hα₁ _ g (hφ₁ g)) α₄
    (fun g => hα₄ _ g (hφ₄ g)) (liftBorel_subgroupOf_liftParabolic ha 0 hφ₁)
    (liftBorel_subgroupOf_liftParabolic ha 3 hφ₄)

end CFSG.Monster.B.TwoA.Amalgam

module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamily
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyPair
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FieldCT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6 E6Neighbour amalgamRoots amalgamPlacement)

local instance twistedE6PilotQ2FamilyMembersNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotQ2FamilyMembersNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def memPair : E6Neighbour → Fin 6 → Fin 6 × Fin 6
  | .high => ![(0, 1), (0, 0), (1, 4), (4, 5), (5, 2), (2, 3)]
  | .six => ![(3, 4), (0, 1), (2, 3), (1, 2), (0, 0), (0, 0)]
  | .three => ![(0, 0), (4, 5), (0, 0), (0, 0), (3, 1), (2, 3)]

@[expose] def nbAct : E6Neighbour → (Fin TwistTag.E6.tag.rank → ℤ) → Fin TwistTag.E6.tag.rank → ℤ
  | .high => id
  | .six => twistedE6RelAct triWord2
  | .three => twistedE6RelAct triWord3

set_option maxRecDepth 100000 in
theorem memPair_check (N : E6Neighbour) : ∀ j ∈ N.nodes,
    (memPair N j).1 ≠ (memPair N j).2 ∧
      nbAct N (matRoot (memPair N j).1 (memPair N j).2) =
        triangleWord.foldr (fun i v => reflect TwistTag.E6.tag i v) (Pi.single j 1) ∧
      nbAct N (matRoot (memPair N j).2 (memPair N j).1) =
        triangleWord.foldr (fun i v => reflect TwistTag.E6.tag i v) (-Pi.single j 1) := by
  cases N <;> decide +kernel

@[expose] def memCoords (N : E6Neighbour) (J : Finset (Fin (Tag.rank .E6))) : Finset (Fin 6) :=
  J.biUnion fun j => {(memPair N j).1, (memPair N j).2}

theorem card_memCoords_le (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))} (hJ : J.card ≤ 2) :
    (memCoords N J).card ≤ 4 := by
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ j ∈ J, ({(memPair N j).1, (memPair N j).2} : Finset (Fin 6)).card ≤ ∑ _j ∈ J, 2 :=
        Finset.sum_le_sum fun j _ => Finset.card_le_two
    _ = 2 * J.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ 4 := by omega

theorem exists_not_mem_memCoords (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J.card ≤ 2) : ∃ x : Fin 6, x ∉ memCoords N J := by
  by_contra h
  have h1 : (Finset.univ : Finset (Fin 6)) ⊆ memCoords N J := fun x _ => by
    by_contra hx
    exact h ⟨x, hx⟩
  have h2 := Finset.card_le_card h1
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have := card_memCoords_le N hJ
  omega

section Block

variable {K : Type} [Field K]

theorem realize_comp_blockSL_injective_of_not_mem (h2 : (2 : K) = 0) {T : Finset (Fin 6)}
    {x : Fin 6} (hx : x ∉ T) :
    Function.Injective ((realize h2).comp (LinearPilot.blockSpecialLinear (K := K) T).subtype) := by
  rw [injective_iff_map_eq_one]
  intro B hB
  have hk : (B : SpecialLinearGroup (Fin 6) K) ∈ (realize h2).ker := hB
  obtain ⟨l, -, hl⟩ := (mem_ker_realize h2 _).1 hk
  have h1 := B.2 x x (Or.inl hx)
  rw [hl, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  apply Subtype.ext
  apply Subtype.ext
  rw [hl, h1, map_one]
  rfl

end Block

section Members


variable (K : Type) [Field K]

noncomputable abbrev triW : ModGL TwistTag.E6.tag K :=
  (triangleWord.map fun i => weylElt TwistTag.E6.tag K i 1).prod

@[expose] noncomputable def memModel (J : Finset (Fin (Tag.rank .E6))) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (rootSpan TwistTag.E6.tag K (amalgamRoots J)).map (MulAut.conj (triW K)).toMonoidHom

@[expose] noncomputable def memHom (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* ModGL TwistTag.E6.tag K :=
  (MulAut.conj (triW K)).toMonoidHom.comp ((adjointGroup .E6 K).subtype.comp
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).subtype)

variable {K}

theorem memHom_apply (J : Finset (Fin (Tag.rank .E6)))
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    memHom K J x = MulAut.conj (triW K) ((x : adjointGroup .E6 K) : ModGL .E6 K) :=
  rfl

theorem map_subtype_levi_eq_rootSpan (J : Finset (Fin (Tag.rank .E6))) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).map (adjointGroup .E6 K).subtype =
      rootSpan TwistTag.E6.tag K (amalgamRoots J) :=
  E6Pilot.map_subtype_levi_adjDatumE6 J

theorem coe_mem_rootSpan_amalgamRoots {J : Finset (Fin (Tag.rank .E6))}
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    (((x : adjointGroup .E6 K) : ModGL .E6 K) : ModGL TwistTag.E6.tag K) ∈
      rootSpan TwistTag.E6.tag K (amalgamRoots J) := by
  have h : ((x : adjointGroup .E6 K) : ModGL .E6 K) ∈
      (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).map (adjointGroup .E6 K).subtype :=
    ⟨x, x.2, rfl⟩
  rw [map_subtype_levi_eq_rootSpan] at h
  exact h

@[expose] noncomputable def memIncl (J : Finset (Fin (Tag.rank .E6))) :
    CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →* memModel K J :=
  (memHom K J).codRestrict (memModel K J) fun x => ⟨_, coe_mem_rootSpan_amalgamRoots x, rfl⟩

theorem coe_memIncl (J : Finset (Fin (Tag.rank .E6)))
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J) :
    ((memIncl J x : memModel K J) : ModGL TwistTag.E6.tag K) = memHom K J x :=
  rfl

theorem memIncl_surjective (J : Finset (Fin (Tag.rank .E6))) :
    Function.Surjective (memIncl (K := K) J) := by
  rintro ⟨_, z, hz, rfl⟩
  have hz' : z ∈ (CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J).map
      (adjointGroup .E6 K).subtype := by
    rw [map_subtype_levi_eq_rootSpan]
    exact hz
  obtain ⟨x, hx, rfl⟩ := hz'
  exact ⟨⟨x, hx⟩, rfl⟩

theorem memIncl_injective (J : Finset (Fin (Tag.rank .E6))) :
    Function.Injective (memIncl (K := K) J) := by
  intro x y hxy
  have h := congrArg Subtype.val hxy
  rw [coe_memIncl, coe_memIncl, memHom_apply, memHom_apply] at h
  exact Subtype.ext (Subtype.ext (Units.ext (congrArg Units.val
    ((MulAut.conj (triW K)).injective h))))

theorem range_memHom (J : Finset (Fin (Tag.rank .E6))) : (memHom K J).range = memModel K J := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact (memIncl J x).2
  · intro hy
    obtain ⟨x, hx⟩ := memIncl_surjective J ⟨y, hy⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem memModel_mono {J J' : Finset (Fin (Tag.rank .E6))} (h : J ⊆ J') :
    memModel K J ≤ memModel K J' := by
  refine Subgroup.map_mono (iSup₂_le fun α hα => ?_)
  obtain ⟨j, hj, hα'⟩ := hα
  exact le_iSup₂_of_le (f := fun α (_ : α ∈ amalgamRoots J') => rootSubgroup TwistTag.E6.tag K α)
    α ⟨j, h hj, hα'⟩ le_rfl

theorem memModel_perfect [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K)
    {J : Finset (Fin (Tag.rank .E6))} (hJ2 : J.card ≤ 2) :
    ⁅memModel K J, memModel K J⁆ = memModel K J := by
  rw [← range_memHom]
  exact range_perfect_of_perfect (E6Pilot.commutator_levi_adjDatumE6 hK hJ2) _

theorem memModel_le_map_blockSL [CharP K 2] (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ N.nodes) (ρ : SpecialLinearGroup (Fin 6) K →* ModGL TwistTag.E6.tag K)
    (hρ : ∀ {a b : Fin 6} (hab : a ≠ b) (c : K), ρ (SpecialLinearGroup.transvection hab c) =
      pinnedX TwistTag.E6.tag K (nbAct N (matRoot a b)) c) :
    memModel K J ≤ (LinearPilot.blockSpecialLinear (K := K) (memCoords N J)).map ρ := by
  have hcl : rootSpan TwistTag.E6.tag K (amalgamRoots J) = closure
      {g | ∃ α ∈ amalgamRoots J, ∃ c : K, pinnedX TwistTag.E6.tag K α c = g} :=
    rootSpan_eq_closure K (amalgamRoots J)
  rw [memModel, hcl, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨α, ⟨j, hj, hα⟩, c, rfl⟩, rfl⟩
  obtain ⟨hab, h1, h3⟩ := memPair_check N j (hJ hj)
  have ha : (memPair N j).1 ∈ memCoords N J :=
    Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_insert_self _ _⟩
  have hb : (memPair N j).2 ∈ memCoords N J :=
    Finset.mem_biUnion.2 ⟨j, hj, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hα with rfl | rfl
  · rw [twistedE6_list_weylElt_conj_pinnedX triangleWord (isRoot_single _ j) c]
    have hmem : ρ (SpecialLinearGroup.transvection hab c) ∈
        (LinearPilot.blockSpecialLinear (K := K) (memCoords N J)).map ρ :=
      ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hab ha hb c, rfl⟩
    rw [hρ hab c, h1] at hmem
    exact hmem
  · rw [twistedE6_list_weylElt_conj_pinnedX triangleWord (isRoot_neg_single _ j) c]
    have hmem : ρ (SpecialLinearGroup.transvection hab.symm c) ∈
        (LinearPilot.blockSpecialLinear (K := K) (memCoords N J)).map ρ :=
      ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hab.symm hb ha c, rfl⟩
    rw [hρ hab.symm c, h3] at hmem
    exact hmem

end Members

end CFSG.SeitzReduction.TwistedE6Pilot

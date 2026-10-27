module

public import CFSG.Sporadic.Schreier.TitsCert
public import CFSG.Sporadic.Schreier.TitsIsoCheck
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLargeReeTits

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen

theorem titsU_mem_titsA (j : ℕ) : wordIn 4 titsGen (titsU j) ∈ titsA :=
  wordIn_mem (fun _ hi => titsGen_mem_titsA hi) _

theorem titsV_mem_titsA (j : ℕ) : wordIn 4 titsGen (titsV j) ∈ titsA :=
  wordIn_mem (fun _ hi => titsGen_mem_titsA hi) _

theorem titsD_le_commutator : titsD ≤ ⁅titsA, titsA⁆ :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, rfl⟩
    exact tcomm_mem_commutator (titsU_mem_titsA j) (titsV_mem_titsA j))

theorem titsE_le_commutator : titsE ≤ ⁅titsD, titsD⁆ :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, rfl⟩
    exact tcomm_mem_commutator (wordIn_mem (fun _ hi => titsDGen_mem_titsD hi) _)
      (wordIn_mem (fun _ hi => titsDGen_mem_titsD hi) _))

theorem card_subgroupOf_of_le {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) :
    Nat.card (X.subgroupOf Y) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem titsD_index : (titsD.subgroupOf titsA).index = 2 := by
  have h := Subgroup.card_mul_index (titsD.subgroupOf titsA)
  rw [card_subgroupOf_of_le titsD_le_titsA, card_titsD, card_titsA] at h
  have h' : 17971200 * (titsD.subgroupOf titsA).index = 17971200 * 2 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem map_subtype_commutator' {G : Type*} [Group G] (H : Subgroup G) :
    (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem titsA_commutator : ⁅titsA, titsA⁆ = titsD := by
  refine le_antisymm ?_ titsD_le_commutator
  have hN : (titsD.subgroupOf titsA).Normal := Subgroup.normal_of_index_eq_two titsD_index
  have hcomm : commutator titsA ≤ titsD.subgroupOf titsA := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have hc2 : Nat.card (titsA ⧸ titsD.subgroupOf titsA) = 2 := by
      rw [← Subgroup.index_eq_card, titsD_index]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic (titsA ⧸ titsD.subgroupOf titsA) := isCyclic_of_prime_card hc2
    exact ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
  rw [← map_subtype_commutator']
  refine (Subgroup.map_mono hcomm).trans ?_
  rw [Subgroup.subgroupOf_map_subtype]
  exact inf_le_left

theorem titsD_commutator : ⁅titsD, titsD⁆ = titsD := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have hE : titsE = titsD := Subgroup.eq_of_le_of_card_ge titsE_le_titsD (by
    rw [card_titsD, card_titsE])
  rw [← hE]
  exact hE ▸ titsE_le_commutator

theorem CERT_Tits_derived_perfect :
    ⁅titsA, titsA⁆ = titsD ∧ (titsD.subgroupOf titsA).index = 2 ∧ ⁅titsD, titsD⁆ = titsD :=
  ⟨titsA_commutator, titsD_index, titsD_commutator⟩

attribute [local instance] CFSG.SectionRank.TitsOrder.idxAction

section Vec

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

@[expose] def titsVecRep
    [Fact (Nat.card K = 2)] :
    reeFixed ReeTag.F4 K 0 →* Equiv.Perm (Fin 1755) :=
  MulAction.toPermHom (reeFixed ReeTag.F4 K 0) (Fin CFSG.SectionRank.Native.Tits.nPts)

theorem titsVecRep_gen
    [Fact (Nat.card K = 2)] {s : ℕ} (hs : s < 4) (x : Fin 1755) :
    (titsVecRep (genG K s) x : ℕ) =
      CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! x := by
  rw [rep_genG (K := K) hs x x.2,
    CFSG.Sporadic.Th.idx_of_lt (n := CFSG.SectionRank.Native.Tits.nPts) _ x.2]
  rfl

theorem titsVecRep_injective
    [Fact (Nat.card K = 2)] :
    Function.Injective (titsVecRep (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply sep (K := K) g
  intro t _
  by_cases hlt : CFSG.SectionRank.Native.Tits.checkPts[t]! < CFSG.SectionRank.Native.Tits.nPts
  · rw [CFSG.Sporadic.Th.idx_of_lt g hlt]
    have := DFunLike.congr_fun hg (⟨_, hlt⟩ : Fin 1755)
    exact congrArg Fin.val this
  · exact CFSG.Sporadic.Th.idx_of_not_lt g hlt

@[expose] def titsSigma : Equiv.Perm (Fin 1755) := permOfArr 1755 titsSigmaArr

theorem titsSigma_rep :
    Rep 1755 titsSigmaArr titsSigma := (rep_permOfArr titsSigma_check.1).1

@[expose] def titsVecHom
    [Fact (Nat.card K = 2)] :
    reeFixed ReeTag.F4 K 0 →* Equiv.Perm (Fin 1755) :=
  (MulAut.conj titsSigma).toMonoidHom.comp titsVecRep

theorem titsSigma_conj
    [Fact (Nat.card K = 2)] {s : ℕ} (hs : s < 4) (y : Fin 1755) :
    titsSigma (titsVecRep (genG K s) y) = titsGen s (titsSigma y) := by
  apply Fin.ext
  have h1 : (titsSigma (titsVecRep (genG K s) y) : ℕ) =
      titsSigmaArr[(titsVecRep (genG K s) y : ℕ)]! := (titsSigma_rep _).symm
  have h2 : ((titsVecRep (genG K s) y : Fin 1755) : ℕ) =
      CFSG.Sporadic.Th.Native.ap CFSG.SectionRank.Native.Tits.genTables[s]! y :=
    titsVecRep_gen hs y
  have h3 := titsSigma_check.2.2 s hs y y.2
  have h4 : (titsGen s (titsSigma y) : ℕ) = (titsGenArrs[s]!)[(titsSigma y : ℕ)]! :=
    (titsGen_rep hs _).symm
  have h5 : (titsSigma y : ℕ) = titsSigmaArr[(y : ℕ)]! := (titsSigma_rep y).symm
  rw [h1, h2, h3, h4, h5]

theorem titsVecHom_gen
    [Fact (Nat.card K = 2)] {s : ℕ} (hs : s < 4) :
    titsVecHom (genG K s) = titsGen s := by
  refine Equiv.ext fun x => ?_
  have hx : x = titsSigma (titsSigma⁻¹ x) := (perm_apply_inv _ x).symm
  show (titsSigma * titsVecRep (genG K s) * titsSigma⁻¹) x = _
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, titsSigma_conj hs, ← hx]

theorem titsVecHom_injective
    [Fact (Nat.card K = 2)] :
    Function.Injective (titsVecHom (K := K)) :=
  (MulAut.conj titsSigma).injective.comp titsVecRep_injective

theorem titsVecHom_range
    [hK : Fact (Nat.card K = 2)] : (titsVecHom (K := K)).range = titsA := by
  rw [MonoidHom.range_eq_map, ← closure_titsGens_eq_top hK.out, MonoidHom.map_closure, titsA]
  congr 1
  have e : ∀ s : Fin 4, titsVecHom (genG K s) = titsGen s := fun s => titsVecHom_gen s.2
  ext g
  simp only [gens, Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_range]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  simp only [genG] at e0 e1 e2 e3
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl] at e0
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, e0.symm⟩
    · exact ⟨1, e1.symm⟩
    · exact ⟨2, e2.symm⟩
    · exact ⟨3, e3.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl e0.symm
    · exact Or.inr (Or.inl e1.symm)
    · exact Or.inr (Or.inr (Or.inl e2.symm))
    · exact Or.inr (Or.inr (Or.inr e3.symm))

@[expose] def titsIso
    [Fact (Nat.card K = 2)] : reeFixed ReeTag.F4 K 0 ≃* titsA :=
  (MonoidHom.ofInjective titsVecHom_injective).trans (MulEquiv.subgroupCongr titsVecHom_range)

theorem titsIso_apply
    [Fact (Nat.card K = 2)] (g : reeFixed ReeTag.F4 K 0) :
    (titsIso g : Equiv.Perm (Fin 1755)) = titsVecHom g :=
  rfl

theorem titsIso_gen
    [Fact (Nat.card K = 2)] {s : ℕ} (hs : s < 4) :
    (titsIso (genG K s) : Equiv.Perm (Fin 1755)) = titsGen s := by
  rw [titsIso_apply, titsVecHom_gen hs]

end Vec

theorem map_commutator_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : (commutator G).map f = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ hf]

theorem commutator_titsA :
    commutator titsA = titsD.subgroupOf titsA := by
  apply Subgroup.map_injective titsA.subtype_injective
  rw [map_subtype_commutator', titsA_commutator, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left titsD_le_titsA]

section Derived

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

@[expose] def titsDerivedIso
    [Fact (Nat.card K = 2)] :
    commutator (reeFixed ReeTag.F4 K 0) ≃* titsD :=
  ((titsIso (K := K)).subgroupMap (commutator _)).trans
    ((MulEquiv.subgroupCongr (by
      rw [map_commutator_of_surjective _ (titsIso (K := K)).surjective, commutator_titsA])).trans
      (Subgroup.subgroupOfEquivOfLe titsD_le_titsA))

theorem commutator_reeFixed_simple
    (hK : Nat.card K = 2) :
    IsSimpleGroup (commutator (reeFixed ReeTag.F4 K 0)) := by
  have hQ := (titsData K hK).isQuasisimple hK
  have hZ := CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK
  have hs := hQ.2.1
  have e : commutator (reeFixed ReeTag.F4 K 0) ⧸ Subgroup.center
      (commutator (reeFixed ReeTag.F4 K 0)) ≃* commutator (reeFixed ReeTag.F4 K 0) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Nontrivial (commutator (reeFixed ReeTag.F4 K 0)) :=
    ⟨⟨⟨(titsData K hK).g₀, (titsData K hK).g₀_mem⟩, 1,
      fun h => (titsData K hK).g₀_ne_one (congrArg Subtype.val h)⟩⟩
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective

theorem center_commutator_reeFixed
    (hK : Nat.card K = 2) :
    Subgroup.center (commutator (reeFixed ReeTag.F4 K 0)) = ⊥ :=
  CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK

end Derived

instance titsZMod2Card : Fact (Nat.card (ZMod 2) = 2) := ⟨Nat.card_zmod 2⟩

instance titsZMod2CharP : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2

theorem titsD_nontrivial : Nontrivial titsD := by
  rw [← Finite.one_lt_card_iff_nontrivial, card_titsD]
  norm_num

theorem titsD_simple :
    IsSimpleGroup titsD := by
  have := commutator_reeFixed_simple (K := ZMod 2) (Nat.card_zmod 2)
  have := titsD_nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective (titsDerivedIso (K := ZMod 2)).toMonoidHom
    (titsDerivedIso (K := ZMod 2)).surjective

theorem titsD_center :
    Subgroup.center titsD = ⊥ := by
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv
    (titsDerivedIso (K := ZMod 2)), center_commutator_reeFixed (Nat.card_zmod 2),
    Subgroup.map_bot]

end CFSG.Sporadic.Schreier.Tits

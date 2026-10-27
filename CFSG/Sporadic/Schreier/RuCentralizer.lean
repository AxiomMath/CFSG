module

public import CFSG.Sporadic.Schreier.RuCheckTree
public import CFSG.Sporadic.Schreier.RuSylowC

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

theorem ncard_finSet {n : ℕ} {l : List ℕ} (h : PointList n l) : (finSet n l).ncard = l.length := by
  classical
  let L : List (Fin n) := l.attach.map fun x => ⟨x.1, h.lt x.1 x.2⟩
  have hL : L.Nodup := by
    refine (List.nodup_attach.2 h.sorted.nodup).map ?_
    intro x y hxy
    exact Subtype.ext (congrArg Fin.val hxy)
  have hset : finSet n l = (L.toFinset : Set (Fin n)) := by
    ext p
    simp only [finSet, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_map, List.mem_attach,
      true_and, L]
    constructor
    · intro hp
      exact ⟨⟨p, hp⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]
  simp [L]

abbrev ruFixSet : Set (Fin 4060) := {x | ruZ x = x}

theorem ruFixSet_ncard :
    ruFixSet.ncard = 92 := by
  show {x : Fin 4060 | ruZ x = x}.ncard = 92
  rw [← finSet_fixedList rep_ruZ, ncard_finSet (pointList_fixedList _)]
  exact ruTree_check.1

theorem ruTreeSets_nodup : ruTreeSets.toList.Nodup := by
  have h := ruTree_check.2.2.2.2
  rw [ruSortedStrict, decide_eq_true_eq, List.isChain_iff_pairwise] at h
  exact (List.mergeSort_perm _ _).nodup_iff.1 h.nodup

theorem rep_ruTreeGens :
    ∀ k < ruTreeGens.size, Rep 4060 ruTreeGens[k]! ([ruA0, ruA1].getD k 1) :=
  rep_pair_getD rep_ruA0 rep_ruA1

theorem ruTreeGens_size : ruTreeGens.size = 2 := by
  simp only [ruTreeGens, List.size_toArray, List.length_cons, List.length_nil]

theorem ruTreeGens_mem : ∀ k < ruTreeGens.size, [ruA0, ruA1].getD k 1 ∈ ruP := by
  intro k hk
  rw [ruTreeGens_size] at hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [List.getD_cons_zero]
    exact ruA0_mem
  · rw [List.getD_cons_succ, List.getD_cons_zero]
    exact ruA1_mem

theorem ruFix_translates :
    593775 ≤ (Set.range fun g : ruP => (g : Equiv.Perm (Fin 4060)) • ruFixSet).ncard := by
  have h := le_ncard_orbit_of_translatesOK (H := ruP) rep_ruTreeGens ruTreeGens_mem
    (pointList_fixedList ruZA) ruTree_check.2.2.2.1 ruTreeSets_nodup
  rw [ruTree_check.2.1, finSet_fixedList rep_ruZ] at h
  exact h

instance :

    Finite ruP := Nat.finite_of_card_ne_zero (by rw [card_ruP]; norm_num)

theorem ruC_le_centralizer :
    ruC ≤ ruP ⊓ Subgroup.centralizer {ruZ} :=
  le_inf ruC_le fun g hg => Subgroup.mem_centralizer_singleton_iff.2 (ruZ_central g hg)

theorem smul_ruFixSet {g : Equiv.Perm (Fin 4060)} (hg : g ∈ Subgroup.centralizer {ruZ}) :
    g • ruFixSet = ruFixSet := by
  have hc' : g⁻¹ * ruZ = ruZ * g⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.inv_mem _ hg)
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show ruZ (g⁻¹ y) = g⁻¹ y ↔ ruZ y = y
  rw [← Equiv.Perm.mul_apply ruZ g⁻¹, ← hc', Equiv.Perm.mul_apply]
  exact g⁻¹.injective.eq_iff

theorem card_centralizer_ruZ_le :
    Nat.card (ruP ⊓ Subgroup.centralizer {ruZ} : Subgroup _) ≤
    245760 := by
  set V := MulAction.stabilizer ruP ruFixSet
  have hidx : V.index = (MulAction.orbit ruP ruFixSet).ncard := MulAction.index_stabilizer _ _
  have horb : 593775 ≤ V.index := by
    rw [hidx]
    exact ruFix_translates
  have hmul := V.card_mul_index
  rw [card_ruP] at hmul
  have hV : Nat.card V ≤ 245760 := by
    by_contra hlt
    push Not at hlt
    have : 245761 * 593775 ≤ Nat.card V * V.index := Nat.mul_le_mul hlt horb
    rw [hmul] at this
    norm_num at this
  let f : (ruP ⊓ Subgroup.centralizer {ruZ} : Subgroup _) → V := fun x =>
    ⟨⟨x, x.2.1⟩, MulAction.mem_stabilizer_iff.2 (smul_ruFixSet x.2.2)⟩
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun v : V => ((v : ruP) : Equiv.Perm (Fin 4060))) h)
  exact (Nat.card_le_card_of_injective f hf).trans hV

theorem ruC_eq_centralizer :
    ruC = ruP ⊓ Subgroup.centralizer {ruZ} :=
  Subgroup.eq_of_le_of_card_ge ruC_le_centralizer (card_centralizer_ruZ_le.trans card_ruC.ge)

theorem ruC_eq_centralizer_center :
    ruC = ruP ⊓ Subgroup.centralizer ((Subgroup.center ruS).map ruS.subtype : Set _) := by
  rw [center_ruS, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact ruC_eq_centralizer

theorem AT_Ru_intrinsic_involution_centralizer :
    orderOf ruZ = 2 ∧ {x : Fin 4060 | ruZ x = x}.ncard = 92 ∧
    593775 ≤ (Set.range fun g : ruP =>
      (g : Equiv.Perm (Fin 4060)) • {x : Fin 4060 | ruZ x = x}).ncard ∧
    ruC = ruP ⊓ Subgroup.centralizer {ruZ} ∧
    ruC = ruP ⊓ Subgroup.centralizer ((Subgroup.center ruS).map ruS.subtype : Set _) :=
  ⟨orderOf_ruZ, ruFixSet_ncard, ruFix_translates, ruC_eq_centralizer, ruC_eq_centralizer_center⟩

end CFSG.Sporadic.RuSchreier

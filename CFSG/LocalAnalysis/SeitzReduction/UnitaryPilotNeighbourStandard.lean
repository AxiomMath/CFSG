module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotHsyl
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSetup
public import CFSG.LocalAnalysis.EvenSmallLie.Children

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] {L : Subgroup G}

section Transport

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem isQuasisimple_map_blockSU (e : L ≃* unitaryPSU h n) {I : Finset (Fin n)}
    (hI4 : 4 ≤ I.card) (hIn : I.card < n) :
    CFSG.IsQuasisimple (((blockSU h I).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((blockSU h I).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((blockSU h I).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (isQuasisimple_blockSU h hI4 hIn)

theorem isQuasisimple_open_map_blockSU (e : L ≃* unitaryPSU h n) {I : Finset (Fin n)}
    (hI4 : 4 ≤ I.card) (hIn : I.card < n) :
    CFSG.Open.IsQuasisimple (((blockSU h I).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_blockSU h e hI4 hIn).1.commutator_eq_top,
    (isQuasisimple_map_blockSU h e hI4 hIn).2.1⟩

theorem layer_inf_centralizer_of_le_rootSU2 (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)} (hX₀ : X₀ ≤ rootSU2 h a b)
    (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) :
    inSubgroup layer
        (L ⊓ centralizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) : Set G)) =
      ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype :=
  LinearPilot.inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (blockSU_compl_le_centralizer_of_le_rootSU2 h hX₀)
    (fun _ hg _ hg' =>
      commutator_mem_blockSU_of_mem_centralizer h (by omega) hab hX₀ hX₀o hX₀1 hg hg')
    (isQuasisimple_blockSU_compl_pair h hn hab)

theorem mem_map_blockSU_of_isPGroup_of_mem_inf_centralizer (e : L ≃* unitaryPSU h n)
    (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)}
    (hX₀ : X₀ ≤ rootSU2 h a b) (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) {z : G}
    (hz : IsPGroup 2 (zpowers z))
    (hzX : z ∈ L ⊓ centralizer (((X₀.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
      Set G)) :
    z ∈ ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype := by
  obtain ⟨k, hk⟩ := hz ⟨z, mem_zpowers z⟩
  have hzk : z ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_pow] at this
  rw [F4Pilot.inf_centralizer_map_symm] at hzX
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hzX
  have hk' : ((e.symm w : L) : G) ^ 2 ^ k = 1 := hzk
  have hw' : w ^ 2 ^ k = 1 := by
    apply e.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one, OneMemClass.coe_one, SubgroupClass.coe_pow]
    exact hk'
  have hw2 : IsPGroup 2 (zpowers w) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hw', one_zpow]
  exact ⟨e.symm w, ⟨w, mem_blockSU_of_isPGroup_of_le_rootSU2_of_five_le h hn hab hX₀ hX₀o hX₀1
    hw2 hw, rfl⟩, rfl⟩

theorem eq_one_of_fix_map_of_le_rootSU2 (e : L ≃* unitaryPSU h n) (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (unitaryPSU h n)} (hX₀ : X₀ ≤ rootSU2 h a b)
    (hX₀o : Odd (Nat.card X₀)) (hX₀1 : X₀ ≠ ⊥) {X D : Subgroup G}
    (hX : (X₀.map e.symm.toMonoidHom).map L.subtype ≤ X)
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ k : ℕ, β ^ 2 ^ k = 1 → β = 1 := by
  intro β hβX hβD k hβk
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_two_group_fix_of_five_le h hn hab hX₀ hX₀o hX₀1 (fun x hx => ?_)
      (fun x hx => ?_) (k := k) ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        hβX _ (hX ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩), MulEquiv.apply_symm_apply]
    · have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ hmem,
        MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβk, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

end Transport

section Neighbour

variable [Finite G] {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem neighbour_standard_of_le_rootSU2 (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (unitaryPSU h n)} (hX₀ : X₀ ≤ rootSU2 h a b) (hX₀o : Odd (Nat.card X₀))
    (hX₀1 : X₀ ≠ ⊥) {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    (hX : (X₀.map e.symm.toMonoidHom).map L.subtype ≤ X) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype)
    (hD : D = inSubgroup layer (L ⊓ centralizer (X : Set G))) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hcard := card_compl_pair (n := n) hab
  have hDq : CFSG.Open.IsQuasisimple D :=
    hDe ▸ isQuasisimple_open_map_blockSU h e (by omega) (by omega)
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD hDq
    (eq_one_of_fix_map_of_le_rootSU2 h e (by omega) hab hX₀ hX₀o hX₀1 hX hDe)

omit [Finite G] in
theorem neighbour_data_unitaryRootTorus (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {a b : Fin n}
    (hab : a ≠ b) {t : G} (htC : t ∈ centralizer (L : Set G)) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    X ≤ L ∧ t ∈ centralizer (X : Set G) ∧ IsCyclic X ∧ Nat.card X = 2 ^ f + 1 ∧
      X ≤ ((rootSU2 h a b).map e.symm.toMonoidHom).map L.subtype ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧
      D ≤ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ∧
      CFSG.Open.IsQuasisimple D ∧ Nonempty (D ≃* unitarySU 2 f K (n - 2)) ∧
      Odd (Nat.card (center D)) ∧ Group.IsSolvable (Outer (D ⧸ center D)) := by
  have hcard := card_compl_pair (n := n) hab
  obtain ⟨φ⟩ := blockSU_compl_pair_mulEquiv h hab
  subst hX hDe
  set ψ := LinearPilot.mapSymmMulEquiv e (blockSU h ({a, b}ᶜ : Finset (Fin n))) with hψ
  refine ⟨map_subtype_le _, LinearPilot.mem_centralizer_map_symm e _ htC,
    LinearPilot.isCyclic_map_symm e (isCyclic_unitaryRootTorus h hab),
    (LinearPilot.card_map_symm e _).trans (card_unitaryRootTorus h (by omega) hab),
    map_mono (map_mono (unitaryRootTorus_le_rootSU2 h hab)),
    (layer_inf_centralizer_of_le_rootSU2 h e hn hab (unitaryRootTorus_le_rootSU2 h hab)
      (odd_card_unitaryRootTorus h hab) (unitaryRootTorus_ne_bot h (by omega) hab)).symm,
    le_inf (LinearPilot.map_symm_le_centralizer_map_symm e
        (blockSU_compl_le_centralizer_unitaryRootTorus h hab))
      (LinearPilot.map_symm_le_centralizer_singleton e _ htC),
    isQuasisimple_open_map_blockSU h e (by omega) (by omega), ⟨ψ.trans φ⟩, ?_, ?_⟩
  · rw [Nat.card_congr (centerCongr ψ).toEquiv]
    exact odd_card_center_blockSU h (by omega)
  · exact isSolvable_outer_of_mulEquiv h (by omega)
      (fun h3 => by have := congrArg Prod.fst h3; simp only at this; omega)
      ((QuotientGroup.congr _ _ ψ (map_center_eq ψ)).trans
        (blockSUQuotientCenterEquiv h (by omega)))

theorem neighbour_standard_unitaryRootTorus (hL : standardComponentIsStandard L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  obtain ⟨-, -, -, -, -, hD, -⟩ := neighbour_data_unitaryRootTorus h e hn hab htC hX hDe
  exact neighbour_standard_of_le_rootSU2 h hL htC ht hK e hn hab
    (unitaryRootTorus_le_rootSU2 h hab) (odd_card_unitaryRootTorus h hab)
    (unitaryRootTorus_ne_bot h (by omega) hab) htX hX.ge hDe hD

end Neighbour

section Setting

variable [Finite G] {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem neighbour_standard_unitaryRootTorus_of_seitzSetting (hset : SeitzSetting G L)
    (e : L ≃* unitaryPSU h n) (hn : 6 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((unitaryRootTorus h hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSU h ({a, b}ᶜ : Finset (Fin n))).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
  neighbour_standard_unitaryRootTorus h hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers hset e (by omega) htC ht) e hn hab hX htX hDe

end Setting

end CFSG.SeitzReduction.UnitaryPilot

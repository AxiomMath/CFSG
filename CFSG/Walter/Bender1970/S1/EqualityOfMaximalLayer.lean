module

public import CFSG.Walter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectImageNormalOddIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Walter.AStar.Components
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter

open GorensteinWalter
open scoped commutatorElement

universe u

section Perfect

variable {G : Type*} [Group G]

private theorem commutatorElement_mul_left_of_commute {a c y : G} (h : Commute c y) :
    ⁅a * c, y⁆ = ⁅a, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * c * y * (c⁻¹ * a⁻¹) * y⁻¹ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by group
    _ = a * y * a⁻¹ * y⁻¹ := by rw [h.eq, mul_inv_cancel_right]

private theorem commutatorElement_mul_right_of_commute {x b d : G} (h : Commute d x) :
    ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc x * (b * d) * x⁻¹ * (d⁻¹ * b⁻¹) = x * b * (d * x⁻¹ * d⁻¹) * b⁻¹ := by group
    _ = x * b * x⁻¹ * b⁻¹ := by rw [h.inv_right.eq, mul_inv_cancel_right]

private theorem le_of_isPerfect_of_forall_eq_mul {P M : Subgroup G} (hP : Group.IsPerfect P)
    (h : ∀ x ∈ P, ∃ m ∈ M, ∃ z ∈ P ⊓ Subgroup.centralizer (P : Set G), x = m * z) :
    P ≤ M := by
  rw [← Subgroup.isPerfect_iff.mp hP, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨m, hm, z, hz, rfl⟩ := h x hx
  obtain ⟨m', hm', z', hz', rfl⟩ := h y hy
  have hmP : m ∈ P := by simpa using P.mul_mem hx (P.inv_mem hz.1)
  have h1 : Commute z (m' * z') := (Subgroup.mem_centralizer_iff.mp hz.2 _ hy).symm
  have h2 : Commute z' m := (Subgroup.mem_centralizer_iff.mp hz'.2 _ hmP).symm
  rw [commutatorElement_mul_left_of_commute h1, commutatorElement_mul_right_of_commute h2,
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

private theorem le_of_isPerfect_of_le_sup_normal {P M O : Subgroup G} [O.Normal]
    (hP : Group.IsPerfect P) (hMP : M ≤ P) (hle : P ≤ M ⊔ O)
    (hPO : P ⊓ O ≤ Subgroup.centralizer (P : Set G)) : P ≤ M := by
  refine le_of_isPerfect_of_forall_eq_mul hP fun x hx => ?_
  obtain ⟨m, hm, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle hx)
  have hoP : o ∈ P := by simpa using P.mul_mem (P.inv_mem (hMP hm)) hx
  exact ⟨m, hm, o, ⟨hoP, hPO ⟨hoP, ho⟩⟩, rfl⟩

private theorem le_of_isPerfect_of_le_sup_centralizer {P M Z : Subgroup G}
    (hP : Group.IsPerfect P) (hMP : M ≤ P) (hle : P ≤ M ⊔ Z)
    (hZ : Z ≤ Subgroup.centralizer (P : Set G)) : P ≤ M := by
  refine le_of_isPerfect_of_forall_eq_mul hP fun x hx => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := mem_sup_decompose_of_centralizes (hle hx)
    (hZ.trans (Subgroup.centralizer_le (show (M : Set G) ⊆ P from hMP)))
  have hzP : z ∈ P := by simpa using P.mul_mem (P.inv_mem (hMP hm)) hx
  exact ⟨m, hm, z, ⟨hzP, hZ hz⟩, rfl⟩

private theorem eq_bot_of_isPerfect_of_le_of_isNilpotent {P Q : Subgroup G} (hP : Group.IsPerfect P)
    (hQ : Group.IsNilpotent Q) (hPQ : P ≤ Q) : P = ⊥ := by
  by_contra hne
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Group.IsPerfect P := hP
  have : Group.IsNilpotent P := by
    have : Group.IsNilpotent (P.subgroupOf Q) := inferInstance
    exact Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hPQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPQ).surjective
  exact Group.IsPerfect.not_isNilpotent P this

private theorem normal_of_isNormalIn_top {K : Subgroup G} (h : IsNormalIn K ⊤) : K.Normal :=
  ⟨fun k hk g => h.2 g trivial k hk⟩

end Perfect

theorem le_componentLayerOf_top_of_odd_index {X : Type u} [Group X] [Finite X]
    (hodd : Odd (generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ pPrimeCore 2 X))).index)
    {P : Subgroup X} (hP : Group.IsPerfect P)
    (hPF : P ≤ Subgroup.centralizer (fittingSubgroup X : Set X)) :
    P ≤ componentLayerOf (⊤ : Subgroup X) := by
  by_cases hPbot : P = ⊥
  · rw [hPbot]
    exact bot_le
  set N : Subgroup X := Subgroup.normalClosure (P : Set X)
  have hPN : P ≤ N := Subgroup.le_normalClosure
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hNne : N ≠ ⊥ := fun h => hPbot (le_bot_iff.mp (h ▸ hPN))
  have hNperf : Group.IsPerfect N := by
    apply Subgroup.isPerfect_iff.mpr
    apply le_antisymm (Subgroup.commutator_le_left N N)
    apply Subgroup.normalClosure_le_normal
    intro x hx
    have hx' : x ∈ ⁅P, P⁆ := by
      rw [Subgroup.isPerfect_iff.mp hP]
      exact hx
    exact Subgroup.commutator_mono hPN hPN hx'
  have : (fittingSubgroup X).Normal := fittingSubgroup_normal
  have hNF : N ≤ Subgroup.centralizer (fittingSubgroup X : Set X) :=
    Subgroup.normalClosure_le_normal hPF
  set O : Subgroup X := pPrimeCore 2 X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard O hOodd
  have hFO : _root_.CFSG.fittingSubgroupOf O ≤ fittingSubgroup X :=
    fittingSubgroupOf_le_fittingSubgroup O inferInstance
  have hNOF : N ⊓ O ≤ fittingSubgroup X := by
    have h1 : N ⊓ O ≤ O ⊓ Subgroup.centralizer (_root_.CFSG.fittingSubgroupOf O : Set X) :=
      le_inf inf_le_right (inf_le_left.trans (hNF.trans
        (Subgroup.centralizer_le (show (_root_.CFSG.fittingSubgroupOf O : Set X) ⊆
          fittingSubgroup X from hFO))))
    exact h1.trans ((fact_1_2_centralizer_fitting_le_fitting O hOsolv).trans hFO)
  have hNOC : N ⊓ O ≤ Subgroup.centralizer (N : Set X) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (Subgroup.mem_centralizer_iff.mp (hNF hn) z (hNOF hz)).symm
  set q : X →* X ⧸ O := QuotientGroup.mk' O with hqdef
  have hFnormal : (generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).Normal :=
    normal_of_isNormalIn_top (generalizedFittingSubgroupOf_isNormalIn ⊤)
  obtain ⟨-, hNqperf, hNqF⟩ :=
    perfect_image_le_normal_odd_index_of_solvable_kernel N hNperf hNne O hOsolv _ hFnormal hodd
  have hNqE : N.map q ≤ componentLayerOf (⊤ : Subgroup (X ⧸ O)) := by
    have hEnormal : (componentLayerOf (⊤ : Subgroup (X ⧸ O))).Normal :=
      normal_of_isNormalIn_top (componentLayerOf_isNormalIn ⊤)
    set ρ := QuotientGroup.mk' (componentLayerOf (⊤ : Subgroup (X ⧸ O))) with hρdef
    have h1 : (N.map q).map ρ ≤ (_root_.CFSG.fittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).map ρ :=
      calc (N.map q).map ρ ≤ (generalizedFittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).map ρ :=
            Subgroup.map_mono hNqF
        _ = (_root_.CFSG.fittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).map ρ ⊔
            (componentLayerOf (⊤ : Subgroup (X ⧸ O))).map ρ := Subgroup.map_sup _ _ _
        _ = (_root_.CFSG.fittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).map ρ := by
            rw [hρdef, QuotientGroup.map_mk'_self, sup_bot_eq]
    have hnil : Group.IsNilpotent
        ((_root_.CFSG.fittingSubgroupOf (⊤ : Subgroup (X ⧸ O))).map ρ) := by
      have : Group.IsNilpotent (_root_.CFSG.fittingSubgroupOf (⊤ : Subgroup (X ⧸ O))) :=
        fittingSubgroupOf_isNilpotent ⊤
      exact Group.nilpotent_of_surjective (ρ.subgroupMap _) (ρ.subgroupMap_surjective _)
    have hperf : Group.IsPerfect ((N.map q).map ρ) := by
      have : Group.IsPerfect (N.map q) := hNqperf
      exact Group.IsPerfect.map ρ
    have hker := (Subgroup.map_eq_bot_iff _).mp
      (eq_bot_of_isPerfect_of_le_of_isNilpotent hperf hnil h1)
    rwa [hρdef, QuotientGroup.ker_mk'] at hker
  have hlift : ∀ L : Subgroup (X ⧸ O), IsComponentOf L ⊤ → L ≤ N.map q →
      L ≤ (N ⊓ componentLayerOf (⊤ : Subgroup X)).map q := by
    intro L hL hLN
    set M : Subgroup X := N ⊓ L.comap q
    let f : M →* L := (q.comp M.subtype).codRestrict L (fun x => x.2.2)
    have hf : Function.Surjective f := by
      rintro ⟨l, hl⟩
      obtain ⟨n, hn, hnl⟩ := hLN hl
      exact ⟨⟨n, hn, show q n ∈ L from hnl ▸ hl⟩, Subtype.ext hnl⟩
    have hker : f.ker ≤ Subgroup.center M := by
      intro x hx
      have hxO : (x : X) ∈ O := by
        have h1 : q x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        exact (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hNOC ⟨x.2.1, hxO⟩) y y.2.1
    have hLq : CFSG.IsQuasisimple L := ((isComponent_iff_isComponentOf_top L).mpr hL).1
    obtain ⟨-, -, hsurj⟩ := LocalCores.central_extension_derived_of_surjective f hf hker hLq.1
    have hKq := LocalCores.quasisimple_central_extension_derived_of_surjective f hf hker hLq
    set K : Subgroup X := (commutator M).map M.subtype
    have hKcomp : CFSG.IsComponent K := by
      refine ⟨LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ M.subtype_injective) hKq, ?_⟩
      have hMsub : M.IsSubnormal :=
        hNn.isSubnormal.inf ((isSubnormal_of_isComponentOf hL).comap q)
      have hc : (commutator M).Normal := inferInstance
      exact hc.isSubnormal.trans' hMsub
    have hKE : K ≤ componentLayerOf (⊤ : Subgroup X) :=
      le_sSup ((isComponent_iff_isComponentOf_top K).mp hKcomp)
    have hKN : K ≤ N := (Subgroup.map_subtype_le _).trans inf_le_left
    intro l hl
    obtain ⟨k, hk⟩ := hsurj ⟨l, hl⟩
    have hkK : ((k : M) : X) ∈ K := ⟨k, k.2, rfl⟩
    exact ⟨k, ⟨hKN hkK, hKE hkK⟩, congrArg Subtype.val hk⟩
  have hNqle : N.map q ≤ (N ⊓ componentLayerOf (⊤ : Subgroup X)).map q := by
    have hE' : N.map q ≤ sSup {L : Subgroup (X ⧸ O) | IsComponentOf L ⊤ ∧ L ≤ N.map q} := by
      refine le_of_isPerfect_of_le_sup_centralizer hNqperf (sSup_le fun L hL => hL.2)
        (Z := sSup {L : Subgroup (X ⧸ O) | IsComponentOf L ⊤ ∧ ⁅L, N.map q⁆ = ⊥}) ?_ ?_
      · refine hNqE.trans (sSup_le fun L hL => ?_)
        rcases component_le_or_commutator_eq_bot_of_normal hL
            (hNn.map q (QuotientGroup.mk'_surjective O)) with h | h
        · exact le_sup_of_le_left (le_sSup ⟨hL, h⟩)
        · exact le_sup_of_le_right (le_sSup ⟨hL, h⟩)
      · exact sSup_le fun L hL => Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL.2
    exact hE'.trans (sSup_le fun L hL => hlift L hL.1 hL.2)
  have hNle : N ≤ (N ⊓ componentLayerOf (⊤ : Subgroup X)) ⊔ O := by
    have h1 := Subgroup.map_le_iff_le_comap.mp hNqle
    rwa [Subgroup.comap_map_eq, hqdef, QuotientGroup.ker_mk'] at h1
  exact hPN.trans ((le_of_isPerfect_of_le_sup_normal hNperf inf_le_left hNle hNOC).trans
    inf_le_right)

theorem le_componentLayerOf_of_isAStar {G : Type u} [Group G] [Finite G] {B P : Subgroup G}
    (hB : IsAStar ↥B) (hPB : P ≤ B) (hP : Group.IsPerfect P)
    (hPF : P ≤ Subgroup.centralizer (_root_.CFSG.fittingSubgroupOf B : Set G)) :
    P ≤ componentLayerOf B := by
  have hP' : Group.IsPerfect (P.subgroupOf B) := by
    have : Group.IsPerfect P := hP
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPB).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPB).symm.surjective
  have hP'F : P.subgroupOf B ≤ Subgroup.centralizer (fittingSubgroup B : Set B) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hPF (Subgroup.mem_subgroupOf.mp hx)) (y : G)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  have h := le_componentLayerOf_top_of_odd_index hB.2.1 hP' hP'F
  rw [← componentLayerOf_subgroup_top_eq B]
  intro x hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hPB hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.Walter

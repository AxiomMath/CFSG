module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcEndNode
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviNonsplit
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.EPilot

namespace TableBExcTwo

section General

variable {G : Type} [Group G]

theorem centralizer_zpowers_eq (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) = Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem endNodeAt_of_centralizer_eq {t : G} {D : Subgroup G}
    (hcen : Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t ⊔ D)
    (htD : Subgroup.zpowers t ≤ Subgroup.centralizer (D : Set G)) (hD : CFSG.IsQuasisimple D)
    (hZ : Subgroup.center D = ⊥) (ht1 : t ≠ 1) {A : Subgroup G} (htA : t ∈ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : TableBF4.EndNodeAt A t := by
  have hTT : ∀ x ∈ Subgroup.zpowers t, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_add, ← zpow_add, add_comm]
  have hTD : ∀ x ∈ Subgroup.zpowers t, ∀ d ∈ D, x * d = d * x := fun x hx d hd =>
    (Subgroup.mem_centralizer_iff.mp (htD hx) d hd).symm
  obtain ⟨hlay, hcomp⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer ({t} : Set G)) (D := D) (by rw [hcen]; exact le_sup_right)
    (fun g hg h hh => by
      rw [hcen] at hg hh
      exact TableBExc.commutator_mem_of_mem_sup hTT hTD hg hh) hD
  refine ⟨htA, ht1, by rw [hlay]; exact hcomp, fun s hs => ?_⟩
  rw [hlay]
  constructor
  · intro hsD
    have hsC : s ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hA s hs t htA)
    rw [hcen, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (htD.trans (Subgroup.centralizer_le_normalizer _))] at hsC
    obtain ⟨y, hy, e, he, rfl⟩ := Set.mem_mul.1 hsC
    have hez : (⟨e, he⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      have h1 := hsD j j.2
      have h2 := hTD y hy j j.2
      show (j : G) * e = e * j
      calc (j : G) * e = y⁻¹ * (y * j) * e := by group
        _ = y⁻¹ * (j * y) * e := by rw [h2]
        _ = y⁻¹ * (j * (y * e)) := by group
        _ = y⁻¹ * (y * e * j) := by rw [h1]
        _ = e * j := by group
    rw [hZ, Subgroup.mem_bot] at hez
    have he1 : e = 1 := congrArg Subtype.val hez
    rw [he1, mul_one]
    exact hy
  · intro hst j hj
    exact hTD s hst j hj

theorem endNodeAt_of_conj {A : Subgroup G} {t : G} (g : G)
    (h : TableBF4.EndNodeAt (A.map (MulAut.conj g).toMonoidHom) (g * t * g⁻¹)) :
    TableBF4.EndNodeAt A t := by
  have h1 := h.map (MulAut.conj g).symm
  have hA : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g).symm.toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    simp
  have ht : (MulAut.conj g).symm (g * t * g⁻¹) = t := by
    rw [MulAut.conj_symm_apply]
    group
  rwa [hA, ht] at h1

theorem comm_of_mem_map_conj {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (g : G) :
    ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∀ b ∈ A.map (MulAut.conj g).toMonoidHom,
      a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hA a ha b hb]

theorem endNodeAt_of_conj_centralizer {A : Subgroup G} (hA : IsElemAbelian 3 A) {t : G}
    (htA : t ∈ A) (ht1 : t ≠ 1) (g : G) {D : Subgroup G}
    (hcen : Subgroup.centralizer ({g * t * g⁻¹} : Set G) = Subgroup.zpowers (g * t * g⁻¹) ⊔ D)
    (htD : Subgroup.zpowers (g * t * g⁻¹) ≤ Subgroup.centralizer (D : Set G))
    (hD : CFSG.IsQuasisimple D) (hZ : Subgroup.center D = ⊥) : TableBF4.EndNodeAt A t := by
  refine endNodeAt_of_conj g (endNodeAt_of_centralizer_eq hcen htD hD hZ ?_ ⟨t, htA, rfl⟩
    (comm_of_mem_map_conj (fun a ha b hb => TableB.IsElemAbelian.comm hA ha hb) g))
  intro h
  apply ht1
  have h2 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
  rw [h2, h]
  group

theorem card_zpowers_conj_eq_three {A : Subgroup G} (hA : IsElemAbelian 3 A) {t : G}
    (htA : t ∈ A) (ht1 : t ≠ 1) (g : G) :
    Nat.card (Subgroup.zpowers (g * t * g⁻¹)) = 3 := by
  have := Fact.mk Nat.prime_three
  have h3 : (g * t * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA.2 t htA, mul_one, mul_inv_cancel]
  have h1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have h2 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h2, h]
    group
  rw [Nat.card_zpowers, orderOf_eq_prime h3 h1]

end General

@[expose] def GGE7TwoRootFusionInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ A : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 A → 3 ^ 6 ≤ Nat.card A →
      ∃ t ∈ A, t ≠ 1 ∧ ∃ g : adjointGroup .E7 K,
        g * t * g⁻¹ ∈ (highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K)

@[expose] def GGE8TwoRootFusionInput :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ A : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 A → 3 ^ 7 ≤ Nat.card A →
      ∃ t ∈ A, t ≠ 1 ∧ ∃ g : adjointGroup .E8 K,
        g * t * g⁻¹ ∈ (highRootSL2 .E8 K).subgroupOf (adjointGroup .E8 K)

section E7

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggEndNodeElt_E7Two (hF : GGE7TwoRootFusionInput) (hK : Nat.card K = 2) :
    GGEndNodeElt 3 6 (adjointGroup .E7 K) := by
  intro A hA h6 _
  obtain ⟨t, htA, ht1, g, hg⟩ := hF K hK A hA h6
  have hX := card_zpowers_conj_eq_three hA htA ht1 g
  obtain ⟨hcen, -, hXD⟩ := CFSG.SeitzReduction.E7Pilot.centralizer_nonsplit_E7_of_finite
    (X := Subgroup.zpowers (g * t * g⁻¹)) (Subgroup.zpowers_le.mpr hg) (by rw [hX, hK])
    inferInstance
  rw [centralizer_zpowers_eq] at hcen
  exact ⟨t, endNodeAt_of_conj_centralizer hA htA ht1 g hcen hXD
    CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7
    CFSG.SeitzReduction.E7Pilot.center_perpLevi_E7_eq_bot⟩

theorem ggEndNode_E7Two (hF : GGE7TwoRootFusionInput) (hK : Nat.card K = 2) :
    GGEndNode 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) :=
  ggEndNode_of_elt (TableBExc.idImage_subset_inn_E7 K) (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (TableBF4.ggEndNodeElt_of_mulEquiv (TableBExc.recipeEquiv .E7 K) (ggEndNodeElt_E7Two hF hK))

end E7

section E8

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggEndNodeElt_E8Two (hF : GGE8TwoRootFusionInput) (hK : Nat.card K = 2) :
    GGEndNodeElt 3 7 (adjointGroup .E8 K) := by
  intro A hA h7 _
  obtain ⟨t, htA, ht1, g, hg⟩ := hF K hK A hA h7
  have hX := card_zpowers_conj_eq_three hA htA ht1 g
  obtain ⟨hcen, -, hXD⟩ := CFSG.SeitzReduction.E8Pilot.centralizer_nonsplit_E8
    (X := Subgroup.zpowers (g * t * g⁻¹)) (Subgroup.zpowers_le.mpr hg) (by rw [hX, hK])
    inferInstance
  rw [centralizer_zpowers_eq] at hcen
  exact ⟨t, endNodeAt_of_conj_centralizer hA htA ht1 g hcen hXD
    CFSG.SeitzReduction.E8Pilot.isQuasisimple_e7Levi
    CFSG.SeitzReduction.E8Pilot.center_e7Levi_eq_bot⟩

theorem ggEndNode_E8Two (hF : GGE8TwoRootFusionInput) (hK : Nat.card K = 2) :
    GGEndNode 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) :=
  ggEndNode_of_elt (TableBExc.idImage_subset_inn_E8 K) (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (TableBF4.ggEndNodeElt_of_mulEquiv (TableBExc.recipeEquiv .E8 K) (ggEndNodeElt_E8Two hF hK))

end E8

end TableBExcTwo

end CFSG.StandardType

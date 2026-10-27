module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbOddModule
import CFSG.Quasithin.Recognition.Stroth.Str86AbM6
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5M6Z
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str86_sq_le_relIndex_centralizerMod_Vv
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {γ δ : Str86Γ L1 L2 S} (hγ : vtype γ = true) (hδ : δ ∈ nbrs γ) {t : G}
    (htS : t ∈ pCoreOf 2 (stab γ ⊓ stab δ)) (htQ : t ∉ pCoreOf 2 (stab γ))
    (ht2 : t * t = 1) :
    (2 ^ k) ^ 2 ≤ (centralizerMod (omegaOneCenterOf (pCoreOf 2 (stab γ)))
      (Vv (Z2 L1 L2 S) γ) (Subgroup.zpowers t)).relIndex (Vv (Z2 L1 L2 S) γ) := by
  obtain ⟨-, h1, hS0, -, hV1⟩ := str86_base_values hI
  have hδlin : vtype δ = false := str86_vtype_of_mem_nbrs hγ hδ
  obtain ⟨g, rfl, rfl⟩ := F112Crit.exists_edge_conj hδlin (CosetGeom.mem_nbrs_symm hδ)
  obtain ⟨hQ, hZ, -, hV, -⟩ := str86_vertex_smul hI g
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  obtain ⟨-, -, hSedge, -, -⟩ := str86_vertex_smul hI g
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  have hZ1 : omegaOneCenterOf (pCoreOf 2 (stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)))) =
      Z1 L1 L2 S := by rw [h1]
  have hQ1 : pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
      conjSub (g : G) (Q1 L1 L2 S) := by rw [hQ, h1]
  have hSP1 : S ≤ P1 L1 L2 S := le_sup_right.trans le_sup_right
  have htS' : ((g : G)⁻¹ * t * g) ∈ S := by
    have h : t ∈ pCoreOf 2
        (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) := by
      simpa only [inf_comm] using htS
    rw [hSedge] at h
    have h' := mem_conjSub.mp h
    rwa [hS0] at h'
  have htQ' : ((g : G)⁻¹ * t * g) ∉ Q1 L1 L2 S := by
    intro h
    apply htQ
    rw [hQ1]
    exact mem_conjSub.mpr h
  have ht'2 : ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = 1 := by
    rw [show ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = (g : G)⁻¹ * (t * t) * g by
      group, ht2]
    group
  have h := str86_sq_le_relIndex_centralizerMod_z1 hI hZQ (hSP1 htS') htQ' ht'2
  have hz : Subgroup.zpowers t = conjSub (g : G)
      (Subgroup.zpowers ((g : G)⁻¹ * t * g)) := by
    rw [conjSub, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hZ, hZ1, hV, hV1, hz, ← conjSub_centralizerMod, str86_conjSub_eq_smul,
    str86_conjSub_eq_smul, Subgroup.relIndex_pointwise_smul]
  exact h

private theorem str86_false_of_commutator_Vv_pCoreOf_z
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    {γ δ : Str86Γ L1 L2 S} (hγ : vtype γ = true) (hδ : δ ∈ nbrs γ) {t : G}
    (htS : t ∈ pCoreOf 2 (stab γ ⊓ stab δ)) (htQ : t ∉ pCoreOf 2 (stab γ))
    (ht2 : t * t = 1)
    (htV : ∀ v ∈ Vv (Z2 L1 L2 S) γ,
      t * v * t⁻¹ * v⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 (stab γ))) : False := by
  obtain ⟨-, h1, hS0, -, hV1⟩ := str86_base_values hI
  have hδlin : vtype δ = false := str86_vtype_of_mem_nbrs hγ hδ
  obtain ⟨g, rfl, rfl⟩ := F112Crit.exists_edge_conj hδlin (CosetGeom.mem_nbrs_symm hδ)
  obtain ⟨hQ, hZ, -, hV, -⟩ := str86_vertex_smul hI g
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  obtain ⟨-, -, hSedge, -, -⟩ := str86_vertex_smul hI g
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  have hZ1 : omegaOneCenterOf (pCoreOf 2 (stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)))) =
      Z1 L1 L2 S := by rw [h1]
  have hQ1 : pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
      conjSub (g : G) (Q1 L1 L2 S) := by rw [hQ, h1]
  have hSP1 : S ≤ P1 L1 L2 S := le_sup_right.trans le_sup_right
  have htS' : ((g : G)⁻¹ * t * g) ∈ S := by
    have h : t ∈ pCoreOf 2
        (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) := by
      simpa only [inf_comm] using htS
    rw [hSedge] at h
    have h' := mem_conjSub.mp h
    rwa [hS0] at h'
  have htQ' : ((g : G)⁻¹ * t * g) ∉ Q1 L1 L2 S := by
    intro h
    apply htQ
    rw [hQ1]
    exact mem_conjSub.mpr h
  have ht'2 : ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = 1 := by
    rw [show ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = (g : G)⁻¹ * (t * t) * g by
      group, ht2]
    group
  have htV' : ∀ v ∈ conjClosure (Z2 L1 L2 S) L1,
      ((g : G)⁻¹ * t * g) * v * ((g : G)⁻¹ * t * g)⁻¹ * v⁻¹ ∈ Z1 L1 L2 S := by
    intro v hv
    have hw : (g : G) * v * (g : G)⁻¹ ∈ Vv (Z2 L1 L2 S)
        (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
      rw [hV, hV1]
      exact mul_mem_conjSub hv
    have hmem := htV _ hw
    rw [hZ, hZ1] at hmem
    have hmem' := mem_conjSub.mp hmem
    have e : (g : G)⁻¹ * (t * ((g : G) * v * (g : G)⁻¹) * t⁻¹ *
        ((g : G) * v * (g : G)⁻¹)⁻¹) * (g : G) =
        ((g : G)⁻¹ * t * g) * v * ((g : G)⁻¹ * t * g)⁻¹ * v⁻¹ := by group
    rwa [e] at hmem'
  exact str86_false_of_commutator_conjClosure_le_z1 hI hZQ (hSP1 htS') htQ' ht'2 htV'

private theorem exists_nbrs_not_mem_pCoreOf_of_commutator_ne_bot
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {γ : Str86Γ L1 L2 S} (hγ : vtype γ = true)
    {A : Subgroup G} (hne : ⁅A, Vv (Z2 L1 L2 S) γ⁆ ≠ ⊥) :
    ∃ a ∈ A, ∃ μ ∈ nbrs γ, a ∉ pCoreOf 2 (stab μ) := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hVle : Vv (Z2 L1 L2 S) γ ≤ Subgroup.centralizer (A : Set G) := by
    refine F112Crit.Vv_le_of_forall_mem_nbrs hγ fun μ hμ => ?_
    have hμlin : vtype μ = false := str86_vtype_of_mem_nbrs hγ hμ
    have hZμ : Vv (Z2 L1 L2 S) μ = omegaOneCenterOf (pCoreOf 2 (stab μ)) :=
      (str86_vertex_basics hI).1 μ hμlin
    rw [hZμ]
    exact Subgroup.le_centralizer_iff.mpr
      (le_trans (show A ≤ pCoreOf 2 (stab μ) from fun a ha => hcon a ha μ hμ)
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab μ)))
  exact Subgroup.le_centralizer_iff.mp hVle

private theorem str86_L311ab_OM
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    (∃ a ∈ Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))),
      ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)), a ∉ pCoreOf 2 (stab μ) ∧
        omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
          ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆) ∧
      ∃ b' ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1)),
        ∃ δ ∈ nbrs (lam 1), b' ∉ pCoreOf 2 (stab δ) ∧
          omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) =
            ⁅Vv (Z2 L1 L2 S) δ, Subgroup.zpowers b'⁆ := by
  classical
  have hM6 : Str86UnitaryM6 := fun _ _ _ _ _ _ _ _ _ _ _ hI' hZQ' _ htP htQ ht2 =>
    str86_sq_le_relIndex_conjClosure_of_mem_p1 hI' hZQ' htP htQ ht2
  obtain ⟨hO4a, hO4b⟩ := str86_critPath_odd_O4 hM6 hI hO hkm hP hodd hb3
  obtain ⟨hv1, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  obtain ⟨a, haA, μ, hμ, haQμ⟩ :=
    exists_nbrs_not_mem_pCoreOf_of_commutator_ne_bot hI hvb hO4a
  have haS : a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ) :=
    (str86_pCoreOf_le_pCoreOf_inf hI hμ) (Subgroup.mem_inf.mp haA).2
  have hOMa := str86_oddModule_edge hI hO hvb hμ
  refine ⟨⟨a, haA, μ, hμ, haQμ, (hOMa.2.1 a haS haQμ).symm⟩, ?_⟩
  obtain ⟨b', hbB, δ, hδ, hbQδ⟩ :=
    exists_nbrs_not_mem_pCoreOf_of_commutator_ne_bot hI hv1 hO4b
  have hbS : b' ∈ pCoreOf 2 (stab (lam 1) ⊓ stab δ) :=
    (str86_pCoreOf_le_pCoreOf_inf hI hδ) (Subgroup.mem_inf.mp hbB).2
  have hOMb := str86_oddModule_edge hI hO hv1 hδ
  exact ⟨b', hbB, δ, hδ, hbQδ, (hOMb.2.1 b' hbS hbQδ).symm⟩

private theorem str86_L311ab_a_Zeq
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    {a : G} {μ : Str86Γ L1 L2 S} (ha : a ∈ Vv (Z2 L1 L2 S) (lam 1))
    (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S)))
    (hZa : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
      ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆)
    (hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))) :
    omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
  obtain ⟨hv1, -, -, hvb, -, hn12, -, -, -⟩ := hP.odd_shape hI hodd hb3
  have hZa_le_Za : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
    calc omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))
        = ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆ := hZa
      _ ≤ ⁅Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)), Vv (Z2 L1 L2 S) (lam 1)⁆ :=
        Subgroup.commutator_mono (F112Crit.Vv_le_Vv_of_mem_nbrs hvb hμ)
          (Subgroup.zpowers_le.mpr ha)
      _ ≤ ⁅pCoreOf 2 (stab (lam 1)), Vv (Z2 L1 L2 S) (lam 1)⁆ :=
        Subgroup.commutator_mono hVQ le_rfl
      _ = ⁅Vv (Z2 L1 L2 S) (lam 1), pCoreOf 2 (stab (lam 1))⁆ :=
        Subgroup.commutator_comm _ _
      _ = omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) :=
        str86_commutator_Vv_pCoreOf hI hO hb3 hv1
  have hcardα' : Nat.card (omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))) =
      2 ^ m := (str86_oddModule_edge hI hO hvb hμ).1
  have hcardα : Nat.card (omegaOneCenterOf (pCoreOf 2 (stab (lam 1)))) = 2 ^ m :=
    (str86_oddModule_edge hI hO hv1 hn12).1
  exact Subgroup.eq_of_le_of_card_ge hZa_le_Za (by rw [hcardα, hcardα'])

private theorem str86_L311ab_a
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    {a : G} {μ : Str86Γ L1 L2 S} (ha : a ∈ Vv (Z2 L1 L2 S) (lam 1))
    (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S)))
    (hZa : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
      ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆)
    (hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))) :
    False := by
  obtain ⟨hGL1, -, hZQ1⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨hv1, -, -, hvb, hn01, -, -, hnb', hnb⟩ := hP.odd_shape hI hodd hb3
  have hb2 : 2 ≤ str86CritB L1 L2 S := by omega
  have hD41 : ∀ δ : Str86Γ L1 L2 S, vtype δ = false →
      Vv (Z2 L1 L2 S) δ = omegaOneCenterOf (pCoreOf 2 (stab δ)) :=
    (str86_vertex_basics hI).1
  have hZeq := str86_L311ab_a_Zeq hI hO hP hodd hb3 ha hμ hZa hVQ
  obtain ⟨t, htZβ, htQα'⟩ := SetLike.not_le_iff_exists.mp hP.critical
  have htZβ' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam 0))) := by
    rwa [hD41 (lam 0) hP.linear] at htZβ
  have ht2 : t * t = 1 := by
    have h := (SmithC27.isElemAbelian_omegaOneCenterOf
      (pCoreOf 2 (stab (lam 0)))).2 t htZβ'
    rwa [pow_two] at h
  have htVα : t ∈ Vv (Z2 L1 L2 S) (lam 1) :=
    F112Crit.Vv_le_Vv_of_mem_nbrs hv1 hn01 htZβ
  have hdist : CosetGeom.dist (lam 0) (lam (str86CritB L1 L2 S - 1)) <
      str86CritB L1 L2 S := by
    rw [hP.isGeo 0 (str86CritB L1 L2 S - 1) (Nat.zero_le _) (by omega)]
    omega
  have htQb1 : t ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) :=
    hGL1 (lam 0) (lam (str86CritB L1 L2 S - 1)) hP.linear hdist htZβ
  have htS : t ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓
      stab (lam (str86CritB L1 L2 S - 1))) := by
    rw [inf_comm]
    exact (str86_pCoreOf_le_pCoreOf_inf hI hnb') htQb1
  have htV : ∀ v ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)),
      t * v * t⁻¹ * v⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
    intro v hv
    have hmem : t * v * t⁻¹ * v⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
      have hc := Subgroup.commutator_mem_commutator
        (H₁ := Vv (Z2 L1 L2 S) (lam 1)) (H₂ := pCoreOf 2 (stab (lam 1))) htVα (hVQ hv)
      rwa [str86_commutator_Vv_pCoreOf hI hO hb3 hv1] at hc
    rwa [← hZeq] at hmem
  exact str86_false_of_commutator_Vv_pCoreOf_z hI (hZQ1 hb2) hvb hnb htS htQα' ht2 htV

private theorem str86_L311ab_b
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    {b' : G} {δ : Str86Γ L1 L2 S}
    (hb : b' ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))) (hδ : δ ∈ nbrs (lam 1))
    (hZb : omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) =
      ⁅Vv (Z2 L1 L2 S) δ, Subgroup.zpowers b'⁆) :
    omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) ≤
      Vv (Z2 L1 L2 S) (lam 1) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) := by
  obtain ⟨-, -, -, -, -, hO16, -, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hv1, -, -, -, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  calc omegaOneCenterOf (pCoreOf 2 (stab (lam 1)))
      = ⁅Vv (Z2 L1 L2 S) δ, Subgroup.zpowers b'⁆ := hZb
    _ ≤ ⁅Vv (Z2 L1 L2 S) (lam 1), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ :=
      Subgroup.commutator_mono (F112Crit.Vv_le_Vv_of_mem_nbrs hv1 hδ)
        (Subgroup.zpowers_le.mpr hb)
    _ ≤ _ := hO16

private theorem str86_L311ab_c
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    {a : G} {μ : Str86Γ L1 L2 S} (ha : a ∈ Vv (Z2 L1 L2 S) (lam 1))
    (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S)))
    (hZa : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) =
      ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆) :
    omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      Vv (Z2 L1 L2 S) (lam 1) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) := by
  obtain ⟨-, -, -, -, -, hO16, -, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨-, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  calc omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))
      = ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆ := hZa
    _ ≤ ⁅Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)), Vv (Z2 L1 L2 S) (lam 1)⁆ :=
      Subgroup.commutator_mono (F112Crit.Vv_le_Vv_of_mem_nbrs hvb hμ)
        (Subgroup.zpowers_le.mpr ha)
    _ = ⁅Vv (Z2 L1 L2 S) (lam 1), Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S))⁆ :=
      Subgroup.commutator_comm _ _
    _ ≤ _ := hO16


theorem str86_critPath_odd_L311ab
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1)) ∧
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) ≤
        Vv (Z2 L1 L2 S) (lam 1) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ∧
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
        Vv (Z2 L1 L2 S) (lam 1) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) := by
  classical
  obtain ⟨⟨a, haA, μ, hμ, -, hZa⟩, b', hbB, δ, hδ, -, hZb⟩ :=
    str86_L311ab_OM hI hO hkm hP hodd hb3
  refine ⟨?_, ?_, ?_⟩
  · intro hVQ
    exact str86_L311ab_a hI hO hP hodd hb3 (Subgroup.mem_inf.mp haA).1 hμ hZa hVQ
  · exact str86_L311ab_b hI hP hodd hb3 (Subgroup.mem_inf.mp hbB).1 hδ hZb
  · exact str86_L311ab_c hI hP hodd hb3 (Subgroup.mem_inf.mp haA).1 hμ hZa

private theorem str86_L311c_find_t
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {lam : ℕ → Str86Γ L1 L2 S}
    (hP : Str86CritPath L1 L2 S lam) (hodd : Odd (str86CritB L1 L2 S))
    (hb3 : 3 ≤ str86CritB L1 L2 S)
    (hVQ : ¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))) :
    ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)), ∃ t : G,
      t ∈ Vv (Z2 L1 L2 S) μ ∧ t ∉ pCoreOf 2 (stab (lam 1)) ∧ t * t = 1 ∧
        t ∈ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 2)) := by
  obtain ⟨-, -, hO13, -, -, -, -, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hv1, -, -, hvb, -, -, hn21, -, -⟩ := hP.odd_shape hI hodd hb3
  have hex : ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)),
      ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) := by
    by_contra hcon
    push Not at hcon
    exact hVQ (F112Crit.Vv_le_of_forall_mem_nbrs hvb hcon)
  obtain ⟨μ, hμ, hμQ⟩ := hex
  have hμlin : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
  obtain ⟨t, htZμ, htQα⟩ := SetLike.not_le_iff_exists.mp hμQ
  have htZμ' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab μ)) := by
    rwa [(str86_vertex_basics hI).1 μ hμlin] at htZμ
  have ht2 : t * t = 1 := by
    have h := (SmithC27.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (stab μ))).2 t htZμ'
    rwa [pow_two] at h
  have htVα' : t ∈ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) :=
    F112Crit.Vv_le_Vv_of_mem_nbrs hvb hμ htZμ
  have htS : t ∈ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 2)) := by
    rw [inf_comm]
    exact (str86_pCoreOf_le_pCoreOf_inf hI hn21) (hO13 htVα')
  exact ⟨μ, hμ, t, htZμ, htQα, ht2, htS⟩

private theorem str86_L311c_relIndex
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S)
    {μ : Str86Γ L1 L2 S} (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S))) {t : G}
    (htZμ : t ∈ Vv (Z2 L1 L2 S) μ)
    (htS : t ∈ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 2)))
    (hZle : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))))
    (hO17 : (Vv (Z2 L1 L2 S) (lam 1) ⊓
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))).relIndex
        (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ k) :
    (centralizerMod (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))))
      (Vv (Z2 L1 L2 S) (lam 1)) (Subgroup.zpowers t)).relIndex
      (Vv (Z2 L1 L2 S) (lam 1)) ≤ 2 ^ k := by
  obtain ⟨hv1, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  have hb2 : 2 ≤ str86CritB L1 L2 S := by omega
  have hAleC : Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ≤
      centralizerMod (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))))
        (Vv (Z2 L1 L2 S) (lam 1)) (Subgroup.zpowers t) := by
    intro x hx
    obtain ⟨hxV, hxQ⟩ := Subgroup.mem_inf.mp hx
    have hVQα : Vv (Z2 L1 L2 S) (lam 1) ≤ pCoreOf 2 (stab (lam 1)) :=
      (str86_Vv_abelian hI).1 hb2 _ hv1
    have hxN : x ∈ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) : Set G) :=
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (stab (lam 1)))
        ((pCoreOf_le 2 _) (hVQα hxV))
    have htN : t ∈ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) : Set G) :=
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (stab (lam 1)))
        ((Subgroup.mem_inf.mp ((pCoreOf_le 2 _) htS)).1)
    have hNV : Vv (Z2 L1 L2 S) (lam 1) ≤ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) : Set G) :=
      hVQα.trans ((pCoreOf_le 2 (stab (lam 1))).trans
        (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (stab (lam 1))))
    refine (mem_centralizerMod_zpowers_iff_of_normalizer (N := Vv (Z2 L1 L2 S) (lam 1))
      (L := omegaOneCenterOf (pCoreOf 2 (stab (lam 1)))) hNV htN hxV).mpr ?_
    have hOMμ := str86_oddModule_edge hI hO hvb hμ
    have hmem : x * t * x⁻¹ * t⁻¹ ∈
        omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
      have hc := Subgroup.commutator_mem_commutator
        (H₁ := pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))
        (H₂ := Vv (Z2 L1 L2 S) μ) hxQ htZμ
      rwa [Subgroup.commutator_comm, hOMμ.2.2] at hc
    exact hZle hmem
  calc (centralizerMod (omegaOneCenterOf (pCoreOf 2 (stab (lam 1))))
        (Vv (Z2 L1 L2 S) (lam 1)) (Subgroup.zpowers t)).relIndex
        (Vv (Z2 L1 L2 S) (lam 1))
      ≤ (Vv (Z2 L1 L2 S) (lam 1) ⊓
          pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))).relIndex
          (Vv (Z2 L1 L2 S) (lam 1)) :=
        Subgroup.relIndex_le_of_le_left hAleC (D15Proof.relIndex_ne_zero _ _)
    _ ≤ 2 ^ k := hO17


theorem str86_critPath_odd_L311c
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb3 : 3 ≤ str86CritB L1 L2 S) :
    ¬ omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) ≤
      omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
  classical
  obtain ⟨-, -, hZQ1⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, -, -, -, -, -, hO17, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hVQ, -, -⟩ := str86_critPath_odd_L311ab hI hO hkm hP hodd hb3
  obtain ⟨hv1, -, -, -, -, hn12, -, -, -⟩ := hP.odd_shape hI hodd hb3
  have hb2 : 2 ≤ str86CritB L1 L2 S := by omega
  obtain ⟨μ, hμ, t, htZμ, htQα, ht2, htS⟩ := str86_L311c_find_t hI hP hodd hb3 hVQ
  have hM6 := str86_sq_le_relIndex_centralizerMod_Vv hI (hZQ1 hb2) hv1 hn12 htS htQα ht2
  intro hZle
  have hrelC := str86_L311c_relIndex hI hO hP hodd hb3 hμ htZμ htS hZle hO17
  have hsq : (2 ^ k) ^ 2 ≤ 2 ^ k := hM6.trans hrelC
  have hk1 : 1 ≤ k := by have := hI.hk; omega
  have hlt : 2 ^ k < (2 ^ k) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega
end CFSG.Quasithin.Stroth

end

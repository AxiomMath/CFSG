module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphF1
import CFSG.Quasithin.Recognition.Stroth.Str86AbBase
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2E1
import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleFrame
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86_vtype_of_mem_nbrs {L1 L2 S : Subgroup G} {γ δ : Str86Γ L1 L2 S}
    (hγ : vtype γ = true) (hδ : δ ∈ nbrs γ) : vtype δ = false := by
  have h' := CosetGeom.vtype_ne_of_adj (show (graph _ _ _).Adj γ δ from hδ)
  rw [hγ] at h'
  cases h : vtype δ
  · rfl
  · exact absurd h.symm h'

theorem str86_nbrs_smul_γ₀ {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) (g : ↥(L1 ⊔ L2 ⊔ S))
    {ε : Str86Γ L1 L2 S} (hε : ε ∈ nbrs (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) :
    ∃ h : ↥(L1 ⊔ L2 ⊔ S), (h : G) ∈ P2 L1 L2 S ∧
      ε = (g * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ∧
      g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
        (g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
  obtain ⟨-, -, -, hN0, -, hB1⟩ := str86_vertex_basics hI
  have hε0 : g⁻¹ • ε ∈ nbrs (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    have h' := (CosetGeom.smul_adj g⁻¹).mpr (show (graph _ _ _).Adj _ ε from hε)
    rwa [inv_smul_smul] at h'
  obtain ⟨h, hhP, hhε⟩ := (hN0 _).mp hε0
  refine ⟨h, hhP, by rw [mul_smul, ← hhε, smul_inv_smul], ?_⟩
  have hfix : h • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
      γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
    have h0 := (str86_base_values hI).1
    exact CosetGeom.smul_eq_of_mem_stab (by rw [h0]; exact hhP)
  rw [mul_smul, hfix]

theorem str86_nbrs_smul_γ₁ {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) (g : ↥(L1 ⊔ L2 ⊔ S))
    {ε : Str86Γ L1 L2 S} (hε : ε ∈ nbrs (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) :
    ∃ h : ↥(L1 ⊔ L2 ⊔ S), (h : G) ∈ P1 L1 L2 S ∧
      ε = (g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ∧
      g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
        (g * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
  obtain ⟨-, -, hN1, -, -, -⟩ := str86_vertex_basics hI
  have hε1 : g⁻¹ • ε ∈ nbrs (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    have h' := (CosetGeom.smul_adj g⁻¹).mpr (show (graph _ _ _).Adj _ ε from hε)
    rwa [inv_smul_smul] at h'
  obtain ⟨h, hhP, hhε⟩ := (hN1 _).mp hε1
  refine ⟨h, hhP, by rw [mul_smul, ← hhε, smul_inv_smul], ?_⟩
  have hfix : h • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
      γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
    have h1 := (str86_base_values hI).2.1
    exact CosetGeom.smul_eq_of_mem_stab (by rw [h1]; exact hhP)
  rw [mul_smul, hfix]

theorem str86_edge_facts {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {γ δ : Str86Γ L1 L2 S}
    (hγ : vtype γ = true) (hδ : δ ∈ nbrs γ) :
    omegaOneCenterOf (pCoreOf 2 (stab γ)) ≤ Vv (Z2 L1 L2 S) δ ∧
      pCoreOf 2 (stab γ ⊓ stab δ) ⊓ Subgroup.centralizer (Vv (Z2 L1 L2 S) δ : Set G) =
        pCoreOf 2 (stab δ) ∧
      Vv (Z2 L1 L2 S) δ ⊓ Subgroup.centralizer (pCoreOf 2 (stab γ ⊓ stab δ) : Set G) =
        omegaOneCenterOf (pCoreOf 2 (stab γ)) ∧
      (pCoreOf 2 (stab δ)).relIndex (pCoreOf 2 (stab γ ⊓ stab δ)) = 2 ^ m ∧
      (pCoreOf 2 (stab γ)).relIndex (pCoreOf 2 (stab γ ⊓ stab δ)) = (2 ^ k) ^ 3 ∧
      omegaOneCenterOf (pCoreOf 2 (stab γ)) ≠ ⊥ ∧
      ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ pCoreOf 2 (stab γ ⊓ stab δ) →
        (A ⊓ pCoreOf 2 (stab γ)).relIndex A ≤ 2 ^ k := by
  classical
  have hF := hI.hF
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  obtain ⟨hZ1eq, hZ1Z2, -, hSCZ2, hZ2CS⟩ := str86_caseI_basics hF hI.hSB h1 hI.hB2 h2 hI.hZI
  obtain ⟨h0, h1', hS0, hV0, -⟩ := str86_base_values hI
  obtain ⟨g, rfl, rfl⟩ := F112Crit.exists_edge_conj (str86_vtype_of_mem_nbrs hγ hδ)
    (show γ ∈ nbrs δ from (show (graph _ _ _).Adj γ δ from hδ).symm)
  obtain ⟨hQγ, hZγ, hSγδ, -, -⟩ := str86_vertex_smul hI g
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  obtain ⟨hQδ, -, -, hVδ, -⟩ := str86_vertex_smul hI g
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  have eS : pCoreOf 2 (stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
      stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) = S := by
    rw [inf_comm]
    exact hS0
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  rw [hZγ, hQγ, hSγδ, hQδ, hVδ, eS, h1', h0, hV0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact conjSub_mono _ hZ1Z2
  · simp only [str86_conjSub_eq_smul]
    rw [← conj_smul_inf_centralizer, hSCZ2]
  · simp only [str86_conjSub_eq_smul]
    rw [← conj_smul_inf_centralizer, hZ2CS]
  · simp only [str86_conjSub_eq_smul]
    rw [Subgroup.relIndex_pointwise_smul]
    exact str86_relIndex_q2_s hF.toW hI.hSB hI.hm hI.hL2
  · simp only [str86_conjSub_eq_smul]
    rw [Subgroup.relIndex_pointwise_smul]
    exact str86_relIndex_q1_s hF hI.hSB hI.hk hI.hFc hI.hU3
  · rw [Ne, conjSub_eq_bot_iff]
    exact hZ1ne
  · intro A hA hAS
    simp only [str86_conjSub_eq_smul] at hAS ⊢
    set A' : Subgroup G := MulAut.conj (g : G)⁻¹ • A with hA'
    have hAA' : A = MulAut.conj (g : G) • A' := by
      rw [hA', smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    have hA'S : A' ≤ S := by
      have h' := (Subgroup.pointwise_smul_le_pointwise_smul_iff
        (a := MulAut.conj (g : G))).mp (hAA' ▸ hAS)
      exact h'
    have hA'e : IsElemAbelian 2 A' := isElemAbelian_conj_smul hA _
    rw [hAA', ← Subgroup.smul_inf, Subgroup.relIndex_pointwise_smul]
    exact str86_relIndex_inf_q1_le hF hI.hSB hI.hk hI.hFc hI.hU3 hA'S hA'e

theorem str86_graph_F1 {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    (∀ δ ε ε' : Str86Γ L1 L2 S, vtype δ = false → ε ∈ nbrs δ → ε' ∈ nbrs δ → ε ≠ ε' →
      omegaOneCenterOf (pCoreOf 2 (stab ε)) ⊓ omegaOneCenterOf (pCoreOf 2 (stab ε')) = ⊥) ∧
      ∀ γ δ δ' : Str86Γ L1 L2 S, vtype γ = true → δ ∈ nbrs γ → δ' ∈ nbrs γ → δ ≠ δ' →
        Vv (Z2 L1 L2 S) δ ≠ Vv (Z2 L1 L2 S) δ' := by
  have hc := hI.critHypN
  obtain ⟨-, h1, -, -, -⟩ := str86_base_values hI
  obtain ⟨-, -, -, -, hB0, hB1⟩ := str86_vertex_basics hI
  constructor
  · intro δ ε ε' hδ hε hε' hne
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
    obtain ⟨h, hhP, rfl, -⟩ := str86_nbrs_smul_γ₀ hI g hε
    obtain ⟨h', hh'P, rfl, -⟩ := str86_nbrs_smul_γ₀ hI g hε'
    have hxP : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∈ P2 L1 L2 S :=
      show (h : G)⁻¹ * h' ∈ P2 L1 L2 S from
        (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hhP) hh'P
    have hxB : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∉ bigB L1 L2 S := by
      intro hB
      apply hne
      have hfix := (hB1 (h⁻¹ * h') hxP).mpr hB
      calc (g * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          (g * h) • ((h⁻¹ * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by rw [hfix]
        _ = (g * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
          rw [smul_smul, mul_assoc, mul_inv_cancel_left]
    obtain ⟨-, hZ, -⟩ := str86_vertex_smul hI (g * h)
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    obtain ⟨-, hZ', -⟩ := str86_vertex_smul hI (g * h')
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    rw [hZ, hZ', h1]
    have e : ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) =
        ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) * ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) := by
      show (g : G) * h' = (g : G) * h * ((h : G)⁻¹ * h')
      group
    rw [e, conjSub_mul, ← conjSub_inf, str86_conjSub_eq_smul ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G),
      str86_z1_inf_conj_eq_bot hI hxP hxB, conjSub_bot]
  · intro γ δ δ' hγ hδ hδ' hne
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hγ
    obtain ⟨h, hhP, rfl, -⟩ := str86_nbrs_smul_γ₁ hI g hδ
    obtain ⟨h', hh'P, rfl, -⟩ := str86_nbrs_smul_γ₁ hI g hδ'
    have hxP : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∈ P1 L1 L2 S :=
      show (h : G)⁻¹ * h' ∈ P1 L1 L2 S from
        (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hhP) hh'P
    have hxB : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∉ bigB L1 L2 S := by
      intro hB
      apply hne
      have hfix := (hB0 (h⁻¹ * h') hxP).mpr hB
      calc (g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          (g * h) • ((h⁻¹ * h') • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by rw [hfix]
        _ = (g * h') • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
          rw [smul_smul, mul_assoc, mul_inv_cancel_left]
    intro hV
    rw [CosetGeom.Vv_smul_γ₀ hc.normalizes, CosetGeom.Vv_smul_γ₀ hc.normalizes] at hV
    have e : ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) =
        ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) * ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) := by
      show (g : G) * h' = (g : G) * h * ((h : G)⁻¹ * h')
      group
    rw [e, conjSub_mul, conjSub_inj] at hV
    exact str86_conj_z2_ne hI hxP hxB (by rw [← str86_conjSub_eq_smul]; exact hV.symm)

theorem str86_graph_TI {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    (∀ δ ε : Str86Γ L1 L2 S, ε ∈ nbrs δ → ∀ X : Subgroup G, IsPGroup 2 X →
      X ≤ stab δ ⊓ stab ε → X ≤ pCoreOf 2 (stab δ ⊓ stab ε)) ∧
      (∀ δ ε ε' : Str86Γ L1 L2 S, ε ∈ nbrs δ → ε' ∈ nbrs δ → ε ≠ ε' →
        pCoreOf 2 (stab δ ⊓ stab ε) ⊓ pCoreOf 2 (stab δ ⊓ stab ε') = pCoreOf 2 (stab δ)) ∧
      ∀ δ ε ε' : Str86Γ L1 L2 S, ε ∈ nbrs δ → ε' ∈ nbrs δ → ε ≠ ε' →
        ∀ x : ↥(L1 ⊔ L2 ⊔ S), (x : G) ∈ pCoreOf 2 (stab δ ⊓ stab ε) →
          (x : G) ∉ pCoreOf 2 (stab δ) → x • ε' ≠ ε' := by
  classical
  have hF := hI.hF
  obtain ⟨h0, h1, hS0, -, -⟩ := str86_base_values hI
  obtain ⟨-, -, -, -, hB0, hB1⟩ := str86_vertex_basics hI
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hPB : P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S := by
    rw [inf_comm]
    exact F1.parabolic_inf_parabolic hR
  have hsyl := F1.isSylowTwoOf_bigB_of_normal hR hI.hSB
  have hSn : (S.subgroupOf (bigB L1 L2 S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsyl.1).mpr hI.hSB
  have hedge : ∀ g : ↥(L1 ⊔ L2 ⊔ S),
      stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
        stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = conjSub (g : G) (bigB L1 L2 S) ∧
      pCoreOf 2 (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
        stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) = conjSub (g : G) S := by
    intro g
    refine ⟨by rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, h0, h1, hPB], ?_⟩
    rw [(str86_vertex_smul hI g _ _).2.2.1, hS0]
  have hbase : ∀ (g : ↥(L1 ⊔ L2 ⊔ S)) (X : Subgroup G), IsPGroup 2 X →
      X ≤ stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
        stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) →
      X ≤ pCoreOf 2 (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
        stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) := by
    intro g X hX hXB
    rw [(hedge g).1] at hXB
    rw [(hedge g).2]
    have hY : conjSub (g : G)⁻¹ X ≤ bigB L1 L2 S := by
      rw [conjSub_le_iff, inv_inv]
      exact hXB
    have hYS := le_of_isSylowTwoOf_normal hsyl hSn hY (F7.isPGroup_conjSub hX)
    rw [conjSub_le_iff, inv_inv] at hYS
    exact hYS
  have hT1 : ∀ δ ε : Str86Γ L1 L2 S, ε ∈ nbrs δ → ∀ X : Subgroup G, IsPGroup 2 X →
      X ≤ stab δ ⊓ stab ε → X ≤ pCoreOf 2 (stab δ ⊓ stab ε) := by
    intro δ ε hε X hX hXδε
    obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge (show (graph _ _ _).Adj δ ε from hε)
    · rw [← hg.1, ← hg.2] at hXδε ⊢
      exact hbase g X hX hXδε
    · rw [← hg.1, ← hg.2, inf_comm] at hXδε ⊢
      exact hbase g X hX hXδε
  have hT2 : ∀ δ ε ε' : Str86Γ L1 L2 S, ε ∈ nbrs δ → ε' ∈ nbrs δ → ε ≠ ε' →
      pCoreOf 2 (stab δ ⊓ stab ε) ⊓ pCoreOf 2 (stab δ ⊓ stab ε') = pCoreOf 2 (stab δ) := by
    intro δ ε ε' hε hε' hne
    cases hδ : vtype δ
    · obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
      obtain ⟨h, hhP, rfl, hgh⟩ := str86_nbrs_smul_γ₀ hI g hε
      obtain ⟨h', hh'P, rfl, hgh'⟩ := str86_nbrs_smul_γ₀ hI g hε'
      have hxP : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∈ P2 L1 L2 S :=
        show (h : G)⁻¹ * h' ∈ P2 L1 L2 S from
          (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).inv_mem hhP) hh'P
      have hxB : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∉ bigB L1 L2 S := by
        intro hB
        apply hne
        have hfix := (hB1 (h⁻¹ * h') hxP).mpr hB
        calc (g * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
            (g * h) • ((h⁻¹ * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
              rw [hfix]
          _ = (g * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
            rw [smul_smul, mul_assoc, mul_inv_cancel_left]
      have hTI := f112_sylow_inf_conj_eq_pCoreOf_right hF.toW hI.hSB
        (Or.inr (Or.inr ⟨m, hI.hm, hI.hL2⟩)) hxP hxB
      have e : ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) =
          ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) * ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) := by
        show (g : G) * h' = (g : G) * h * ((h : G)⁻¹ * h')
        group
      have hQ := (str86_vertex_smul hI (g * h) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
        (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1
      have hA : pCoreOf 2 (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab ((g * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) S := by
        rw [hgh]
        exact (hedge (g * h)).2
      have hA' : pCoreOf 2 (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab ((g * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) S := by
        rw [hgh']
        exact (hedge (g * h')).2
      have hQ' : pCoreOf 2 (stab (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) (Q2 L1 L2 S) := by
        rw [hgh, hQ, h0]
      rw [hA, hA', hQ', e, conjSub_mul, ← conjSub_inf,
        str86_conjSub_eq_smul ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G), hTI]
    · obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
      obtain ⟨h, hhP, rfl, hgh⟩ := str86_nbrs_smul_γ₁ hI g hε
      obtain ⟨h', hh'P, rfl, hgh'⟩ := str86_nbrs_smul_γ₁ hI g hε'
      have hxP : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∈ P1 L1 L2 S :=
        show (h : G)⁻¹ * h' ∈ P1 L1 L2 S from
          (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).inv_mem hhP) hh'P
      have hxB : ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) ∉ bigB L1 L2 S := by
        intro hB
        apply hne
        have hfix := (hB0 (h⁻¹ * h') hxP).mpr hB
        calc (g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
            (g * h) • ((h⁻¹ * h') • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
              rw [hfix]
          _ = (g * h') • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
            rw [smul_smul, mul_assoc, mul_inv_cancel_left]
      have hTI := f112_sylow_inf_conj_eq_pCoreOf_left hF.toW hI.hSB
        (Or.inr (Or.inl ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩)) hxP hxB
      have e : ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) =
          ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) * ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) := by
        show (g : G) * h' = (g : G) * h * ((h : G)⁻¹ * h')
        group
      have hQ := (str86_vertex_smul hI (g * h) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
        (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1
      have hA : pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab ((g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) S := by
        rw [hgh, inf_comm]
        exact (hedge (g * h)).2
      have hA' : pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
          stab ((g * h') • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h' : ↥(L1 ⊔ L2 ⊔ S)) : G) S := by
        rw [hgh', inf_comm]
        exact (hedge (g * h')).2
      have hQ' : pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =
          conjSub ((g * h : ↥(L1 ⊔ L2 ⊔ S)) : G) (Q1 L1 L2 S) := by
        rw [hgh, hQ, h1]
      rw [hA, hA', hQ', e, conjSub_mul, ← conjSub_inf,
        str86_conjSub_eq_smul ((h⁻¹ * h' : ↥(L1 ⊔ L2 ⊔ S)) : G), hTI]
  refine ⟨hT1, hT2, fun δ ε ε' hε hε' hne x hx hxQ hfix => hxQ ?_⟩
  have hxδ : (x : G) ∈ stab δ := (pCoreOf_le 2 _ hx).1
  have hxε' : (x : G) ∈ stab ε' := CosetGeom.mem_stab_of_smul_eq hfix
  have hxp : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
    (pCoreOf_isPGroup 2 _).to_le (Subgroup.zpowers_le.mpr hx)
  have hx' : (x : G) ∈ pCoreOf 2 (stab δ ⊓ stab ε') :=
    hT1 δ ε' hε' _ hxp (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hxδ, hxε'⟩))
      (Subgroup.mem_zpowers _)
  rw [← hT2 δ ε ε' hε hε' hne]
  exact Subgroup.mem_inf.mpr ⟨hx, hx'⟩

theorem str86_Vv_abelian {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    (2 ≤ str86CritB L1 L2 S → ∀ γ : Str86Γ L1 L2 S, vtype γ = true →
      Vv (Z2 L1 L2 S) γ ≤ pCoreOf 2 (stab γ)) ∧
      (3 ≤ str86CritB L1 L2 S → ∀ γ : Str86Γ L1 L2 S, vtype γ = true →
        IsElemAbelian 2 (Vv (Z2 L1 L2 S) γ)) ∧
      (3 ≤ str86CritB L1 L2 S →
        ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x) ∧
      (3 ≤ str86CritB L1 L2 S → ∀ δ : Str86Γ L1 L2 S, vtype δ = false →
        str86V2 L1 L2 S δ ≤ pCoreOf 2 (stab δ)) ∧
      (5 ≤ str86CritB L1 L2 S → ∀ δ : Str86Γ L1 L2 S, vtype δ = false →
        IsElemAbelian 2 (str86V2 L1 L2 S δ)) := by
  obtain ⟨hGL, -, -⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨-, -, -, -, hV1⟩ := str86_base_values hI
  have hcomm : ∀ δ δ' : Str86Γ L1 L2 S, vtype δ = false → vtype δ' = false →
      CosetGeom.dist δ δ' < str86CritB L1 L2 S →
      ∀ x ∈ Vv (Z2 L1 L2 S) δ, ∀ y ∈ Vv (Z2 L1 L2 S) δ', x * y = y * x := by
    intro δ δ' hδ hδ' hd x hx y hy
    have hxC := SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab δ') (hGL δ δ' hδ hd hx)
    rw [← hD41 δ' hδ'] at hxC
    exact (Subgroup.mem_centralizer_iff.mp hxC y hy).symm
  have helem : ∀ δ : Str86Γ L1 L2 S, vtype δ = false → IsElemAbelian 2 (Vv (Z2 L1 L2 S) δ) := by
    intro δ hδ
    rw [hD41 δ hδ]
    exact SmithC27.isElemAbelian_omegaOneCenterOf _
  have hVsup : ∀ γ : Str86Γ L1 L2 S, vtype γ = true →
      Vv (Z2 L1 L2 S) γ = ⨆ δ : {δ // δ ∈ nbrs γ}, Vv (Z2 L1 L2 S) δ.1 := fun γ hγ =>
    le_antisymm (F112Crit.Vv_le_of_forall_mem_nbrs hγ fun δ hδ =>
        le_iSup_of_le (⟨δ, hδ⟩ : {δ // δ ∈ nbrs γ}) le_rfl)
      (iSup_le fun δ => F112Crit.Vv_le_Vv_of_mem_nbrs hγ δ.2)
  have hadj1 : ∀ u v : Str86Γ L1 L2 S, v ∈ nbrs u → CosetGeom.dist u v = 1 := fun u v huv =>
    CosetGeom.dist_eq_one_iff_adj.mpr huv
  have hd2 : ∀ γ δ δ' : Str86Γ L1 L2 S, δ ∈ nbrs γ → δ' ∈ nbrs γ →
      CosetGeom.dist δ δ' ≤ 2 := by
    intro γ δ δ' hδ hδ'
    have h := CosetGeom.dist_triangle_of_adj
      (show (graph _ _ _).Adj δ γ from (show (graph _ _ _).Adj γ δ from hδ).symm) δ'
    rw [hadj1 δ γ (show (graph _ _ _).Adj δ γ from (show (graph _ _ _).Adj γ δ from hδ).symm),
      hadj1 γ δ' hδ'] at h
    omega
  have hAB2 : 3 ≤ str86CritB L1 L2 S → ∀ γ : Str86Γ L1 L2 S, vtype γ = true →
      IsElemAbelian 2 (Vv (Z2 L1 L2 S) γ) := by
    intro hb γ hγ
    rw [hVsup γ hγ]
    exact CosetGeom.isElemAbelian_iSup _ (fun δ => helem δ.1 (str86_vtype_of_mem_nbrs hγ δ.2))
      fun δ δ' => hcomm δ.1 δ'.1 (str86_vtype_of_mem_nbrs hγ δ.2)
        (str86_vtype_of_mem_nbrs hγ δ'.2) (by have := hd2 γ δ.1 δ'.1 δ.2 δ'.2; omega)
  refine ⟨fun hb γ hγ => ?_, hAB2, fun hb x hx y hy => ?_, fun hb δ hδ => ?_, fun hb δ hδ => ?_⟩
  · refine F112Crit.Vv_le_of_forall_mem_nbrs hγ fun δ hδ => ?_
    refine hGL δ γ (str86_vtype_of_mem_nbrs hγ hδ) ?_
    rw [hadj1 δ γ (show (graph _ _ _).Adj δ γ from (show (graph _ _ _).Adj γ δ from hδ).symm)]
    omega
  · have hE := hAB2 hb (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) CosetGeom.vtype_γ₁
    rw [hV1] at hE
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · unfold str86V2
    refine iSup₂_le fun γ hγ => ?_
    have hγt : vtype γ = true := F112Crit.vtype_eq_true_of_mem_nbrs hδ hγ
    refine F112Crit.Vv_le_of_forall_mem_nbrs hγt fun ν hν => ?_
    have := hd2 γ ν δ hν (show (graph _ _ _).Adj γ δ from (show (graph _ _ _).Adj δ γ from hγ).symm)
    exact hGL ν δ (str86_vtype_of_mem_nbrs hγt hν) (by omega)
  · have hV2sup : str86V2 L1 L2 S δ = ⨆ γ : {γ // γ ∈ nbrs δ}, Vv (Z2 L1 L2 S) γ.1 := by
      unfold str86V2
      exact iSup_subtype'
    rw [hV2sup]
    refine CosetGeom.isElemAbelian_iSup _
      (fun γ => hAB2 (by omega) γ.1 (F112Crit.vtype_eq_true_of_mem_nbrs hδ γ.2)) fun γ γ' => ?_
    have hγt := F112Crit.vtype_eq_true_of_mem_nbrs hδ γ.2
    have hγ't := F112Crit.vtype_eq_true_of_mem_nbrs hδ γ'.2
    have hle : Vv (Z2 L1 L2 S) γ.1 ≤ Subgroup.centralizer (Vv (Z2 L1 L2 S) γ'.1 : Set G) := by
      refine F112Crit.Vv_le_of_forall_mem_nbrs hγt fun ν hν => ?_
      rw [Subgroup.le_centralizer_iff]
      refine F112Crit.Vv_le_of_forall_mem_nbrs hγ't fun ν' hν' => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h1 := CosetGeom.dist_triangle_of_adj
        (show (graph _ _ _).Adj ν γ.1 from (show (graph _ _ _).Adj γ.1 ν from hν).symm) ν'
      have h2 := CosetGeom.dist_triangle_of_adj
        (show (graph _ _ _).Adj γ.1 δ from (show (graph _ _ _).Adj δ γ.1 from γ.2).symm) ν'
      have h3 := CosetGeom.dist_triangle_of_adj (show (graph _ _ _).Adj δ γ'.1 from γ'.2) ν'
      rw [hadj1 ν γ.1 (show (graph _ _ _).Adj ν γ.1 from
        (show (graph _ _ _).Adj γ.1 ν from hν).symm)] at h1
      rw [hadj1 γ.1 δ (show (graph _ _ _).Adj γ.1 δ from
        (show (graph _ _ _).Adj δ γ.1 from γ.2).symm)] at h2
      rw [hadj1 δ γ'.1 γ'.2, hadj1 γ'.1 ν' hν'] at h3
      exact hcomm ν ν' (str86_vtype_of_mem_nbrs hγt hν) (str86_vtype_of_mem_nbrs hγ't hν')
        (by omega) x hx y hy
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

end CFSG.Quasithin.Stroth

end

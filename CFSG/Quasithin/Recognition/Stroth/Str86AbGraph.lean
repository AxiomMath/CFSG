module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86CritF2
import CFSG.Quasithin.Recognition.F112Crit.Lemma65
import CFSG.Quasithin.Background.GoldschmidtAmalgamL3UExt
public import CFSG.Quasithin.Recognition.Stroth.F112Tree

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem str86_conjSub_eq_smul (g : G) (H : Subgroup G) : conjSub g H = MulAut.conj g • H := by
  ext x
  rw [conjSub, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem str86_base_values {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = P2 L1 L2 S ∧
      stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = P1 L1 L2 S ∧
      pCoreOf 2 (stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
        stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) = S ∧
      Vv (Z2 L1 L2 S) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = Z2 L1 L2 S ∧
      Vv (Z2 L1 L2 S) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) =
        conjClosure (Z2 L1 L2 S) L1 := by
  have hc := hI.critHypN
  have hyp := hc.amalgam
  have hP2 : P2 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := hyp.le₁
  have hP1 : P1 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := hyp.le₂
  have h0 : stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = P2 L1 L2 S :=
    CosetGeom.stab_γ₀ hP2
  have h1 : stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = P1 L1 L2 S :=
    CosetGeom.stab_γ₁ hP1
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hI.hF.1
  have hPB : P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S := by
    rw [inf_comm]
    exact F1.parabolic_inf_parabolic hR
  have hsyl := F1.isSylowTwoOf_bigB_of_normal hR hI.hSB
  have hO : pCoreOf 2 (bigB L1 L2 S) = S :=
    le_antisymm (F7.isSylowTwoOf_pCoreOf_le hsyl)
      (le_pCoreOf_of_le_normalizer 2 hsyl.1 hI.hSB hI.hF.1.h1.pgroup)
  have hBL : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    bigB_le_normalizer_of_hyp111 hI.hF.1
  have hBZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hc.normalizes
  refine ⟨h0, h1, by rw [h0, h1, hPB, hO], CosetGeom.Vv_γ₀ hc.normalizes, ?_⟩
  rw [CosetGeom.Vv_γ₁ hP1 hc.normalizes]
  refine le_antisymm (conjClosure_le fun h hh z hz => ?_)
    (conjClosure_mono le_rfl le_sup_left)
  obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL).mp hh
  have hbz : b * z * b⁻¹ ∈ Z2 L1 L2 S := (Subgroup.mem_normalizer_iff.mp (hBZ hb) z).mp hz
  rw [show l * b * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ by group]
  exact mem_conjClosure hl hbz

theorem str86_vertex_smul {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) (g : ↥(L1 ⊔ L2 ⊔ S))
    (δ ε : Str86Γ L1 L2 S) :
    pCoreOf 2 (stab (g • δ)) = conjSub (g : G) (pCoreOf 2 (stab δ)) ∧
      omegaOneCenterOf (pCoreOf 2 (stab (g • δ))) =
        conjSub (g : G) (omegaOneCenterOf (pCoreOf 2 (stab δ))) ∧
      pCoreOf 2 (stab (g • δ) ⊓ stab (g • ε)) = conjSub (g : G) (pCoreOf 2 (stab δ ⊓ stab ε)) ∧
      Vv (Z2 L1 L2 S) (g • δ) = conjSub (g : G) (Vv (Z2 L1 L2 S) δ) ∧
      str86V2 L1 L2 S (g • δ) = conjSub (g : G) (str86V2 L1 L2 S δ) := by
  have hc := hI.critHypN
  have hQ : pCoreOf 2 (stab (g • δ)) = conjSub (g : G) (pCoreOf 2 (stab δ)) := by
    rw [CosetGeom.stab_smul, pCoreOf_conjSub]
  have hVv : ∀ γ : Str86Γ L1 L2 S,
      Vv (Z2 L1 L2 S) (g • γ) = conjSub (g : G) (Vv (Z2 L1 L2 S) γ) :=
    fun γ => CosetGeom.Vv_smul hc.normalizes g γ
  refine ⟨hQ, ?_, ?_, hVv δ, ?_⟩
  · rw [hQ]
    exact (omegaOneCenterOf_map_mulEquiv (MulAut.conj (g : G)) _).symm
  · rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, pCoreOf_conjSub]
  · unfold str86V2
    apply le_antisymm
    · refine iSup₂_le fun γ hγ => ?_
      obtain ⟨γ', rfl⟩ : ∃ γ', γ = g • γ' := ⟨g⁻¹ • γ, by simp⟩
      have hγ' : γ' ∈ nbrs δ := (CosetGeom.smul_adj g).mp hγ
      rw [hVv]
      exact conjSub_mono _ (le_iSup₂_of_le (f := fun γ (_ : γ ∈ nbrs δ) => Vv (Z2 L1 L2 S) γ)
        γ' hγ' le_rfl)
    · rw [conjSub_le_iff]
      refine iSup₂_le fun γ hγ => ?_
      rw [← conjSub_le_iff, ← hVv]
      exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ nbrs (g • δ)) => Vv (Z2 L1 L2 S) γ)
        (g • γ) ((CosetGeom.smul_adj g).mpr hγ) le_rfl

theorem str86_vertex_basics {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    (∀ δ : Str86Γ L1 L2 S, vtype δ = false →
      Vv (Z2 L1 L2 S) δ = omegaOneCenterOf (pCoreOf 2 (stab δ))) ∧
      (∀ δ : Str86Γ L1 L2 S,
        stab δ ≤ Subgroup.normalizer (str86V2 L1 L2 S δ : Set G)) ∧
      (∀ δ : Str86Γ L1 L2 S, δ ∈ nbrs (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ↔
        ∃ g : ↥(L1 ⊔ L2 ⊔ S), (g : G) ∈ P1 L1 L2 S ∧
          δ = g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ∧
      (∀ δ : Str86Γ L1 L2 S, δ ∈ nbrs (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ↔
        ∃ g : ↥(L1 ⊔ L2 ⊔ S), (g : G) ∈ P2 L1 L2 S ∧
          δ = g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ∧
      (∀ g : ↥(L1 ⊔ L2 ⊔ S), (g : G) ∈ P1 L1 L2 S →
        (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ↔ (g : G) ∈ bigB L1 L2 S)) ∧
      (∀ g : ↥(L1 ⊔ L2 ⊔ S), (g : G) ∈ P2 L1 L2 S →
        (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ↔ (g : G) ∈ bigB L1 L2 S)) := by
  obtain ⟨h0, h1, -, hV0, -⟩ := str86_base_values hI
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hI.hF.1
  have hPB : P2 L1 L2 S ⊓ P1 L1 L2 S = bigB L1 L2 S := by
    rw [inf_comm]
    exact F1.parabolic_inf_parabolic hR
  have hfix : ∀ (g : ↥(L1 ⊔ L2 ⊔ S)) (γ : Str86Γ L1 L2 S), g • γ = γ ↔ (g : G) ∈ stab γ :=
    fun g γ => ⟨CosetGeom.mem_stab_of_smul_eq, CosetGeom.smul_eq_of_mem_stab⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
    obtain ⟨-, hZ, -, hV, -⟩ := str86_vertex_smul hI g
      (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    rw [hZ, hV, hV0, h0]
  · intro δ x hx
    obtain ⟨hxG, hxδ⟩ := CosetGeom.mem_stab.mp hx
    obtain ⟨-, -, -, -, hV2⟩ := str86_vertex_smul hI ⟨x, hxG⟩ δ δ
    rw [hxδ] at hV2
    exact CosetGeom.mem_normalizer_of_conjSub_eq hV2.symm
  · intro δ
    constructor
    · intro hδ
      obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge (show (graph _ _ _).Adj
        (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) δ from hδ)
      · exfalso
        have h := congrArg vtype hg.1
        rw [CosetGeom.vtype_smul, CosetGeom.vtype_γ₀, CosetGeom.vtype_γ₁] at h
        exact absurd h (by decide)
      · refine ⟨g, ?_, hg.1.symm⟩
        have h' := (hfix g _).mp hg.2
        rwa [h1] at h'
    · rintro ⟨g, hg, rfl⟩
      have hg1 : g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := (hfix g _).mpr (by rw [h1]; exact hg)
      have h' := (CosetGeom.smul_adj g).mpr (CosetGeom.adj_γ₀_γ₁ (G₀ := L1 ⊔ L2 ⊔ S)
        (G₁ := P2 L1 L2 S) (G₂ := P1 L1 L2 S)).symm
      rw [hg1] at h'
      exact h'
  · intro δ
    constructor
    · intro hδ
      obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge (show (graph _ _ _).Adj
        (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) δ from hδ)
      · refine ⟨g, ?_, hg.2.symm⟩
        have h' := (hfix g _).mp hg.1
        rwa [h0] at h'
      · exfalso
        have h := congrArg vtype hg.2
        rw [CosetGeom.vtype_smul, CosetGeom.vtype_γ₀, CosetGeom.vtype_γ₁] at h
        exact absurd h (by decide)
    · rintro ⟨g, hg, rfl⟩
      have hg0 : g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
          γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := (hfix g _).mpr (by rw [h0]; exact hg)
      have h' := (CosetGeom.smul_adj g).mpr (CosetGeom.adj_γ₀_γ₁ (G₀ := L1 ⊔ L2 ⊔ S)
        (G₁ := P2 L1 L2 S) (G₂ := P1 L1 L2 S))
      rw [hg0] at h'
      exact h'
  · intro g hg
    rw [hfix, h0]
    exact ⟨fun h => hPB ▸ Subgroup.mem_inf.mpr ⟨h, hg⟩,
      fun h => (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) h⟩
  · intro g hg
    rw [hfix, h1]
    exact ⟨fun h => hPB ▸ Subgroup.mem_inf.mpr ⟨hg, h⟩,
      fun h => (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) h⟩

theorem str86_le_pCoreOf_stab_of_le_ballStab
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {δ : Str86Γ L1 L2 S} {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXδ : X ≤ ballStab 1 δ) : X ≤ pCoreOf 2 (stab δ) := by
  obtain ⟨h0, h1, -, -, -⟩ := str86_base_values hI
  have key : ∀ (g : ↥(L1 ⊔ L2 ⊔ S)) (γ : Str86Γ L1 L2 S), δ = g • γ →
      (∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ ballStab 1 γ → Y ≤ pCoreOf 2 (stab γ)) →
      X ≤ pCoreOf 2 (stab δ) := by
    rintro g γ rfl hγ
    obtain ⟨hQ, -⟩ := str86_vertex_smul hI g γ γ
    rw [CosetGeom.ballStab_smul] at hXδ
    have hY : conjSub (g : G)⁻¹ X ≤ ballStab 1 γ := by
      rw [conjSub_le_iff, inv_inv]
      exact hXδ
    have hYQ := hγ _ (F7.isPGroup_conjSub hX) hY
    rw [conjSub_le_iff, inv_inv] at hYQ
    rw [hQ]
    exact hYQ
  cases hδ : vtype δ
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
    refine key g _ hg fun Y hY2 hY => ?_
    rw [h0]
    exact str86_f2_linear hI.hF hI.hSB hI.hm hI.hL2 hY hY2
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
    refine key g _ hg fun Y hY2 hY => ?_
    rw [h1]
    exact str86_f2_unitary hI.hF hI.hSB hI.hk hI.hFc hI.hU3 hY hY2

theorem str86_isPGroup_Vv {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {δ : Str86Γ L1 L2 S}
    (hδ : vtype δ = false) : IsPGroup 2 (Vv (Z2 L1 L2 S) δ) := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hδ
  rw [CosetGeom.Vv_smul_γ₀ hI.critHypN.normalizes g]
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hI.hF.toW)
  exact F7.isPGroup_conjSub (hI.hF.1.h1.pgroup.to_le ((omegaOneCenterOf_le _).trans hQ2S))

theorem str86_le_pCoreOf_of_dist_lt {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    (∀ δ μ : Str86Γ L1 L2 S, vtype δ = false →
      CosetGeom.dist δ μ < str86CritB L1 L2 S → Vv (Z2 L1 L2 S) δ ≤ pCoreOf 2 (stab μ)) ∧
      (∀ γ μ : Str86Γ L1 L2 S, vtype γ = true →
        CosetGeom.dist γ μ + 1 < str86CritB L1 L2 S →
          Vv (Z2 L1 L2 S) γ ≤ pCoreOf 2 (stab μ)) ∧
      (2 ≤ str86CritB L1 L2 S → Z2 L1 L2 S ≤ Q1 L1 L2 S) := by
  have hc := hI.critHypN
  obtain ⟨-, h1, -, hV0, -⟩ := str86_base_values hI
  have hA : ∀ δ μ : Str86Γ L1 L2 S, vtype δ = false →
      CosetGeom.dist δ μ < str86CritB L1 L2 S → Vv (Z2 L1 L2 S) δ ≤ pCoreOf 2 (stab μ) :=
    fun δ μ hδ hμ => str86_le_pCoreOf_stab_of_le_ballStab hI (str86_isPGroup_Vv hI hδ)
      ((CritHypN.le_critB_iff_at hc hδ _).mp le_rfl μ hμ)
  refine ⟨hA, fun γ μ hγ hμ => ?_, fun hb => ?_⟩
  · refine F112Crit.Vv_le_of_forall_mem_nbrs hγ fun δ hδ => ?_
    have hδt : vtype δ = false := by
      have h' := CosetGeom.vtype_ne_of_adj (show (graph _ _ _).Adj γ δ from hδ)
      rw [hγ] at h'
      cases h : vtype δ
      · rfl
      · exact absurd h.symm h'
    have hd := CosetGeom.dist_triangle_of_adj
      (show (graph _ _ _).Adj δ γ from (show (graph _ _ _).Adj γ δ from hδ).symm) μ
    rw [CosetGeom.dist_eq_one_iff_adj.mpr
      (show (graph _ _ _).Adj δ γ from (show (graph _ _ _).Adj γ δ from hδ).symm)] at hd
    exact hA δ μ hδt (by omega)
  · have h' := hA (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) CosetGeom.vtype_γ₀
      (by rw [CosetGeom.dist_eq_one_iff_adj.mpr CosetGeom.adj_γ₀_γ₁]; omega)
    rwa [hV0, h1] at h'

theorem str86_one_le_critB {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    1 ≤ str86CritB L1 L2 S := by
  have hc := hI.critHypN
  obtain ⟨h0, -⟩ := str86_base_values hI
  refine (CritHypN.le_critB_iff hc 1).mpr fun μ hμ => ?_
  have hμ0 : CosetGeom.dist (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) μ = 0 := by omega
  rw [← (CosetGeom.dist_eq_zero_iff hc.amalgam.gen).mp hμ0]
  have h := CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  rw [h0] at h
  exact (omegaOneCenterOf_le _).trans h

theorem Str86CritPath.smul {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam) :
    (∀ g : ↥(L1 ⊔ L2 ⊔ S), Str86CritPath L1 L2 S (fun i => g • lam i)) ∧
      ∃ g : ↥(L1 ⊔ L2 ⊔ S), lam 0 = g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ∧
        lam 1 = g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
  refine ⟨fun g => ⟨?_, fun i j hij hj => ?_, ?_⟩, ?_⟩
  · show vtype (g • lam 0) = false
    rw [CosetGeom.vtype_smul]
    exact hP.linear
  · show CosetGeom.dist (g • lam i) (g • lam j) = j - i
    rw [CosetGeom.dist_smul]
    exact hP.isGeo i j hij hj
  · show ¬ Vv (Z2 L1 L2 S) (g • lam 0) ≤ pCoreOf 2 (stab (g • lam (str86CritB L1 L2 S)))
    obtain ⟨hQ, -⟩ := str86_vertex_smul hI g (lam (str86CritB L1 L2 S)) (lam 0)
    obtain ⟨-, -, -, hV, -⟩ := str86_vertex_smul hI g (lam 0) (lam 0)
    rw [hV, hQ, F112Crit.conjSub_le_conjSub_iff]
    exact hP.critical
  · exact F112Crit.exists_edge_conj hP.linear (hP.isGeo.adj (str86_one_le_critB hI))

theorem str86_exists_critPath {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    ∃ lam : ℕ → Str86Γ L1 L2 S, Str86CritPath L1 L2 S lam ∧
      lam 0 = γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) ∧
      lam 1 = γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
  have hc := hI.critHypN
  obtain ⟨-, -, -, hV0, -⟩ := str86_base_values hI
  obtain ⟨μ, hμd, hμ⟩ := CritHypN.exists_dist_eq_critB hc
  obtain ⟨p, hp0, hpb, hpgeo⟩ := CosetGeom.exists_geodesic hc.amalgam.gen _ _ _ hμd
  have hP : Str86CritPath L1 L2 S p := by
    refine ⟨by rw [hp0]; exact CosetGeom.vtype_γ₀, hpgeo, fun hle => hμ ?_⟩
    rw [hp0, hV0, hpb] at hle
    exact hle.trans (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam μ)
  obtain ⟨-, g, hg0, hg1⟩ := hP.smul hI
  refine ⟨fun i => g⁻¹ • p i, (hP.smul hI).1 g⁻¹, ?_, ?_⟩
  · show g⁻¹ • p 0 = _
    rw [hg0, inv_smul_smul]
  · show g⁻¹ • p 1 = _
    rw [hg1, inv_smul_smul]

theorem str86_critPath_of_walk {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hlin : vtype (lam 0) = false)
    (hadj : ∀ i, i < str86CritB L1 L2 S →
      (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam i) (lam (i + 1)))
    (hcrit : ¬ Vv (Z2 L1 L2 S) (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) :
    Str86CritPath L1 L2 S lam := by
  refine ⟨hlin, CosetGeom.isGeo_of_adj_of_dist hI.critHypN.amalgam.gen hadj ?_, hcrit⟩
  by_contra hlt
  exact hcrit ((str86_le_pCoreOf_of_dist_lt hI).1 _ _ hlin (by omega))

end CFSG.Quasithin.Stroth

end

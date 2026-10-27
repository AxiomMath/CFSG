module

public import CFSG.Quasithin.Recognition.SzVBA5Rank
public import CFSG.Quasithin.Recognition.SzVBA5EvenA
public import CFSG.Quasithin.Recognition.SzVBA5EvenB
public import CFSG.Quasithin.Recognition.SzVBA5EvenCases
public import CFSG.Quasithin.Recognition.SzVBA5Setting
public import CFSG.Quasithin.Recognition.SzVBS5Main
public import CFSG.Quasithin.Recognition.Kleidman.VBEven.Central
public import CFSG.Quasithin.Recognition.Kleidman.VBEven.CaseA
public import CFSG.Quasithin.Recognition.SzVBEvenSetting

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F204

@[expose] def A5CaseBModule : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G},
    GeoCtx G₀ G₁ G₂ T V z → A5Facts G₂ T V z → T ≤ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ →
    A5FixedW G₂ V z →
    (∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, ∀ r ∈ pCoreOf 2 G₁,
        r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z) ∧
    ∃ s ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, s ∉ V ∧
      ∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, a ∈ V ∨ a * s⁻¹ ∈ V

theorem a5CentralExists :
    ∀ {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G},
      GeoCtx G₀ G₁ G₂ T V z → ∀ {U : Subgroup G}, G₁ ≤ Subgroup.normalizer (U : Set G) → V ≤ U →
      pCoreOf 2 G₁ ≤ Subgroup.centralizer (U : Set G) → IsElemAbelian 2 U → ∀ {s₀ : G},
      s₀ ∈ U → s₀ ∉ V → (∀ a ∈ U, a ∈ V ∨ a * s₀⁻¹ ∈ V) →
      ∃ s ∈ U, s ∉ V ∧ ∀ x ∈ G₁, x * s = s * x := fun hC _ hUN hVU hQ hU2 _ hs₀ hs₀V hU =>
  CFSG.Quasithin.Kleidman.VBEven.exists_central_of_index_two hC hUN hVU hQ hU2 hs₀ hs₀V hU

theorem a5CaseAWitness :
    ∀ {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G},
      GeoCtx G₀ G₁ G₂ T V z → A5Facts G₂ T V z → T ≤ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ →
      ¬ A5FixedW G₂ V z → ∀ {w : G}, w ∈ pCoreOf 2 G₁ → w * w = 1 → w ∉ pCoreOf 2 G₂ →
      ∃ a ∈ conjClosure V G₂, a ∈ secCentr (pCoreOf 2 G₁) V ∧ w * a * w⁻¹ * a⁻¹ ≠ 1 :=
  fun hC F hTQ hA _ hw hw2 hwQ =>
  CFSG.Quasithin.Kleidman.VBEven.caseA_witness hC F hTQ hA hw hw2 hwQ

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

theorem a5_even_false_of_leaves (hL2c : A5CaseBModule)
    (hL2a : ∀ {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}, GeoCtx G₀ G₁ G₂ T
        V z → A5Facts G₂ T V z → ∀ {s : G}, s ∈ conjClosure V G₂ → s ∉ V → (∀ x ∈ G₁, x * s = s * x)
        → (∃ q ∈ pCoreOf 2 G₂, ∃ k ∈ G₂, conjSub k V ≠ V ∧ q ∈ Subgroup.centralizer (conjSub k V :
        Set G) ∧ q ∉ Subgroup.centralizer (V : Set G)) → False) (hC : GeoCtx G₀ G₁ G₂ T V z)
    (F : A5Facts G₂ T V z) (hev : Even (critDist G₀ G₁ G₂ V))
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) : False := by
  obtain ⟨u, δ, x, ω, p2, D⟩ := exists_critFacts hC hev hb
  have hLF1 : ∀ {w : G}, w ∈ G₂ → w * w = 1 → w ∉ pCoreOf 2 G₂ →
      ∀ c : G, ∃ a ∈ conjClosure V G₂, w * a * w⁻¹ * a⁻¹ ∉ ({1, c, z, c * z} : Set G) :=
    fun hw hw2 hwQ c => exists_comm_not_mem F hw hw2 hwQ c
  have hLF1u := fun {w : G} (hw : w ∈ stab u) (hw2 : w * w = 1) (hwQ : w ∉ pCoreOf 2 (stab u))
    (c : G) => hLF1_at_u hC D.t_u D.Zu hLF1 hw hw2 hwQ c
  have ha : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      Uc V (γ₀ G₀ G₁ G₂) β ≤ pCoreOf 2 (stab u) := fun β hβ => Uc_le_pCoreOf_u D hLF1u hβ
  have hUc : ∀ β β' : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β' → Uc V (γ₀ G₀ G₁ G₂) β = Uc V (γ₀ G₀ G₁ G₂) β' :=
    fun β β' hβ hβ' => Uc_eq D ha hβ hβ'
  have hTQ : T ≤ pCoreOf 2 G₁ ⊔ pCoreOf 2 G₂ :=
    (F112W.pCoreOf_sup_pCoreOf_eq hC.hyp hC.natS3 D.Vω_le_Q1 D.comm_ne).ge
  by_cases hB : A5FixedW G₂ V z
  · obtain ⟨β₂, hβ₂, hβ₂1, -⟩ := D.EV3
    have hG₁ : G₁ ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) : Set G) := by
      rw [hUc _ _ adj_γ₀_γ₁ hβ₂]
      exact normalizer_Uc D ha hβ₂ hβ₂1
    exact false_of_caseB D hG₁ (hL2c hC F hTQ hB)
      (fun {U} hUN hVU hQ hU2 {s₀} hs₀ hs₀V hU => a5CentralExists hC hUN hVU hQ hU2 hs₀ hs₀V hU)
      (fun {s} hs hsV hs1 hq => hL2a hC F hs hsV hs1 hq)
  · exact false_of_caseA D hUc (fun {w} hw hw2 hwQ => a5CaseAWitness hC F hTQ hB hw hw2 hwQ)

theorem vbEvenL24A5_of_leaves
    (hL2c : A5CaseBModule) (hL2a : ∀ {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z
        : G}, GeoCtx G₀ G₁ G₂ T V z → A5Facts G₂ T V z → ∀ {s : G}, s ∈ conjClosure V G₂ → s ∉ V →
        (∀ x ∈ G₁, x * s = s * x) → (∃ q ∈ pCoreOf 2 G₂, ∃ k ∈ G₂, conjSub k V ≠ V ∧ q ∈
        Subgroup.centralizer (conjSub k V : Set G) ∧ q ∉ Subgroup.centralizer (V : Set G)) →
        False) : VBEvenL24A5Statement := by
  intro G _ _ K1 L2 S Zs h hL hA5 hab hev
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  obtain ⟨z, hC⟩ := exists_geoCtx_of_setting hRO h
  have hb := three_le_critDist_of_comm hRO h hab
  have hab' : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S)) := by
    have := isElemAbelian_Vv_γ₁ hC.hyp (V_ne_bot hC) (by omega)
    rwa [Vv_γ₁ hC.hyp.le₂ hC.hyp.normalizes] at this
  have F := a5Facts_of_setting h hL hA5 hab' hC.klein
  exact a5_even_false_of_leaves hL2c hL2a hC F hev hb

end CFSG.Quasithin.SzVB

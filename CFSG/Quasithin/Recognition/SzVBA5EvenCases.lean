module

public import CFSG.Quasithin.Recognition.SzVBA5EvenC

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Cases

variable {u δ x ω p2 : CosetGeom G₀ G₁ G₂} (D : CritFacts G₀ G₁ G₂ T V z u δ x ω p2)

include D

theorem false_of_caseA
    (hUc : ∀ β β' : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β' → Uc V (γ₀ G₀ G₁ G₂) β = Uc V (γ₀ G₀ G₁ G₂) β')
    (hL1 : ∀ {w : G}, w ∈ pCoreOf 2 G₁ → w * w = 1 → w ∉ pCoreOf 2 G₂ →
      ∃ a ∈ conjClosure V G₂, a ∈ secCentr (pCoreOf 2 G₁) V ∧ w * a * w⁻¹ * a⁻¹ ≠ 1) :
    False := by
  obtain ⟨β, hβ, hβ1, hβnot⟩ := D.EV3
  obtain ⟨w, hwW, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hβnot
  have hw2 : w * w = 1 := by
    have := F7.isElemAbelian_pow_eq_one (D.Wβ_abel β hβ) hwW
    rwa [pow_two] at this
  obtain ⟨a, ha, hne⟩ := caseA_at_edge D.hC D.t_δ D.adj_δu hL1 (D.Wβ_le_Qδ β hβ hwW) hw2 hwQ
  apply hne
  have := commute_of_mem_Uc_u D hUc hβ hβ1 hwW ha
  rw [this]
  group

theorem false_of_caseB
    (hG₁ : G₁ ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) : Set G))
    (hL2c : (∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, ∀ r ∈ pCoreOf 2 G₁,
        r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers z) ∧
      ∃ s ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, s ∉ V ∧
        ∀ a ∈ secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂, a ∈ V ∨ a * s⁻¹ ∈ V)
    (hL2b : ∀ {U : Subgroup G}, G₁ ≤ Subgroup.normalizer (U : Set G) → V ≤ U →
      pCoreOf 2 G₁ ≤ Subgroup.centralizer (U : Set G) → IsElemAbelian 2 U → ∀ {s₀ : G},
      s₀ ∈ U → s₀ ∉ V → (∀ a ∈ U, a ∈ V ∨ a * s₀⁻¹ ∈ V) →
      ∃ s ∈ U, s ∉ V ∧ ∀ x ∈ G₁, x * s = s * x)
    (hL2a : ∀ {s : G}, s ∈ conjClosure V G₂ → s ∉ V → (∀ x ∈ G₁, x * s = s * x) →
      (∃ q ∈ pCoreOf 2 G₂, ∃ k ∈ G₂, conjSub k V ≠ V ∧
        q ∈ Subgroup.centralizer (conjSub k V : Set G) ∧ q ∉ Subgroup.centralizer (V : Set G)) →
      False) :
    False := by
  have hN := D.hC.hyp.normalizes
  have h₁ : G₁ ≤ G₀ := D.hC.hyp.le₁
  have h₂ : G₂ ≤ G₀ := D.hC.hyp.le₂
  have hU₀ : Uc V (γ₀ G₀ G₁ G₂) (γ₁ G₀ G₁ G₂) = secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂ := by
    unfold Uc
    rw [stab_γ₀ h₁, Vv_γ₀ hN, Vv_γ₁ h₂ hN]
  rw [hU₀] at hG₁
  set U₀ := secCentr (pCoreOf 2 G₁) V ⊓ conjClosure V G₂ with hU₀def
  obtain ⟨hcomm, s₀, hs₀U, hs₀V, hs₀⟩ := hL2c
  have hQN : G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) := le_normalizer_pCoreOf 2 G₁
  have hK : ⁅U₀, pCoreOf 2 G₁⁆ ≤ Subgroup.zpowers z := by
    rw [Subgroup.commutator_le]
    intro a ha r hr
    have := Subgroup.inv_mem _ (hcomm a ha r hr)
    have e : (r * a * r⁻¹ * a⁻¹)⁻¹ = a * r * a⁻¹ * r⁻¹ := by group
    rwa [e] at this
  have hKN : G₁ ≤ Subgroup.normalizer ((⁅U₀, pCoreOf 2 G₁⁆ : Subgroup G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_conjSub_eq ?_
    rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer (hG₁ hg),
      F7.conjSub_eq_of_mem_normalizer (hQN hg)]
  obtain ⟨β₂, hβ₂, hβ₂1, -⟩ := D.EV3
  have hβ₂ne : β₂ ≠ γ₁ G₀ G₁ G₂ := hβ₂1
  have h01 : γ₁ G₀ G₁ G₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := adj_γ₀_γ₁
  have hβ₂' : β₂ ∈ nbrs (γ₀ G₀ G₁ G₂) := hβ₂
  obtain ⟨g, hg, hgβ⟩ := stab_transitive_on_nbrs h01 hβ₂'
  have hgG₁ : (g : G) ∈ G₁ := by
    rw [← stab_γ₀ h₁]
    exact hg
  have hKbot : ⁅U₀, pCoreOf 2 G₁⁆ = ⊥ := by
    set K := ⁅U₀, pCoreOf 2 G₁⁆ with hKdef
    have h1 : K ≤ Zv z β₂ := by
      have h2 : conjSub (g : G) K = K := F7.conjSub_eq_of_mem_normalizer (hKN hgG₁)
      have h3 : conjSub (g : G) K ≤ conjSub (g : G) (Subgroup.zpowers z) := conjSub_mono _ hK
      rw [h2, ← Zv_smul_γ₁ (G₂_le_normalizer_zpowers D.hC) g] at h3
      have hgβ' : g • γ₁ G₀ G₁ G₂ = β₂ := hgβ
      rwa [hgβ'] at h3
    by_contra hne
    have e1 : K = Zv z β₂ :=
      eq_of_ne_bot_of_le_card_two hne h1
        (card_Zv D.hC (vtype_eq_true_of_adj hβ₂ vtype_γ₀))
    have e2 : K = Zv z (γ₁ G₀ G₁ G₂) := by
      refine eq_of_ne_bot_of_le_card_two hne ?_ (card_Zv D.hC vtype_γ₁)
      rw [Zv_γ₁ (G₂_le_normalizer_zpowers D.hC)]
      exact hK
    exact Zv_ne_of_adj D.hC vtype_γ₀ hβ₂ adj_γ₀_γ₁ hβ₂ne (e1.symm.trans e2)
  have hQcent : pCoreOf 2 G₁ ≤ Subgroup.centralizer (U₀ : Set G) := by
    rw [Subgroup.commutator_comm] at hKbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKbot
  have hVU₀ : V ≤ U₀ := by
    refine le_inf (fun v hv => ?_) (fun v hv => le_conjClosure V G₂ hv)
    refine mem_secCentr.mpr ⟨Subgroup.le_normalizer hv, fun q hq => ?_⟩
    have hqC := CosetGeom.pCoreOf_le_centralizer D.hC.hyp hq
    have := Subgroup.mem_centralizer_iff.mp hqC v hv
    have e : q * v * q⁻¹ * v⁻¹ = 1 := by
      rw [← this]
      group
    rw [e]
    exact V.one_mem
  have hVabel : IsElemAbelian 2 (conjClosure V G₂) := by
    have := D.Wβ_abel (γ₁ G₀ G₁ G₂) adj_γ₀_γ₁
    rwa [Vv_γ₁ h₂ hN] at this
  have hU₀abel : IsElemAbelian 2 U₀ := F7.isElemAbelian_mono hVabel inf_le_right
  obtain ⟨s, hsU, hsV, hsG₁⟩ := hL2b hG₁ hVU₀ hQcent hU₀abel hs₀U hs₀V hs₀
  obtain ⟨y, hyω, hyC⟩ : ∃ y ∈ Vv V ω, y ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    apply D.comm_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcon
  have h10 : γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) := (adj_γ₀_γ₁ (G₀ := G₀)).symm
  have hp2' : p2 ∈ nbrs (γ₁ G₀ G₁ G₂) := D.adj_p2
  obtain ⟨k, hk, hkp⟩ := stab_transitive_on_nbrs h10 hp2'
  have hkG₂ : (k : G) ∈ G₂ := by
    rw [← stab_γ₁ h₂]
    exact hk
  have hVk : Vv V p2 = conjSub (k : G) V := by
    rw [← hkp, Vv_smul_γ₀ hN]
  have hyQ2 : y ∈ pCoreOf 2 (stab p2) := D.Vω_le_Qp2 hyω
  have hyCk : y ∈ Subgroup.centralizer (conjSub (k : G) V : Set G) := by
    rw [← hVk]
    exact pCoreOf_le_centralizer_Vv D.hC D.t_p2 hyQ2
  refine hL2a hsU.2 hsV hsG₁ ⟨y, D.Vω_le_Q1 hyω, k, hkG₂, ?_, hyCk, hyC⟩
  intro hkV
  rw [hkV] at hyCk
  exact hyC hyCk

end Cases

end CFSG.Quasithin.SzVB

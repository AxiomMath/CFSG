module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Main
public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOff

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

variable (F : Frame L1 L2 S D X)
include F

theorem caseI_b2_false
    (hT1 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = false)
    (hb : bMin (P1 L1 L2 S) (P2 L1 L2 S) = 2)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α')
    (h : ¬ Zv α' ≤ Qv α) : False := by
  have hA := Amal.of_frame F
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  set γ₀ := CosetGeom.γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) with hγ₀
  set γ₁ := CosetGeom.γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S) with hγ₁
  have hZ2 : Zv γ₁ = Z2q L1 L2 S := Zv_γ₁_eq F
  have hZ1 : Zv γ₀ = Frame.Z1 L1 L2 S (quasithinOmegaOneCenter S) := Zv_γ₀_eq F
  have hQ0 : Qv γ₀ = Q1 L1 L2 S := by unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv γ₁ = Q2 L1 L2 S := by unfold Qv; rw [stab_γ₁ h₂]
  have hst0 : stab γ₀ = P1 L1 L2 S := stab_γ₀ h₁
  have hst1 : stab γ₁ = P2 L1 L2 S := stab_γ₁ h₂
  have hadj01 : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj γ₀ γ₁ :=
    adj_γ₀_γ₁
  obtain ⟨hvα, -, hcardα, -, -, -⟩ := H4 F hT1 hc h
  obtain ⟨-, hZFα, -⟩ := hA.caseI (fun δ => dichotomy F δ) hc h
  obtain ⟨g, hg⟩ := exists_smul_edge hc.adj
  have hg0 : g • γ₀ = β ∧ g • γ₁ = α := by
    rcases hg with ⟨hg0, hg1⟩ | hg'
    · exfalso
      have : vtype α = false := by rw [← hg0, vtype_smul]; rfl
      rw [hvα] at this; exact Bool.noConfusion this
    · exact hg'
  obtain ⟨hgβ, hgα⟩ := hg0
  have hZα : Zv α = conjSub (g : G) (Z2q L1 L2 S) := by rw [← hgα, Zv_smul, hZ2]
  have hQα : Qv α = conjSub (g : G) (Q2 L1 L2 S) := by rw [← hgα, Qv_smul, hQ1]
  have hcen0 : ZCentral γ₀ := (hT1 γ₀).mpr rfl
  have hZ1eq : Frame.Z1 L1 L2 S (quasithinOmegaOneCenter S) = quasithinOmegaOneCenter S := by
    rw [← hZ1]
    exact hcen0 S (by rw [hst0]; exact F.sylow_P1)
  have hnorm1 : ∀ p ∈ P1 L1 L2 S, ∀ z ∈ quasithinOmegaOneCenter S,
      p * z * p⁻¹ ∈ quasithinOmegaOneCenter S := by
    intro p hp z hz
    have := mem_conjClosure hp hz
    rwa [show conjClosure (quasithinOmegaOneCenter S) (P1 L1 L2 S) =
      Frame.Z1 L1 L2 S (quasithinOmegaOneCenter S) from rfl, hZ1eq] at this
  have hcard16 : Nat.card (Z2q L1 L2 S) = 16 := by
    rw [hZα, CosetGeom.card_conjSub] at hcardα
    exact hcardα
  have hZFγ : ZFaithful γ₁ := ZFaithful_of_vtype_eq (by rw [hvα]; rfl) hZFα
  have hfaith : ∀ s ∈ S, (∀ z ∈ Z2q L1 L2 S, s * z = z * s) → s ∈ Q2 L1 L2 S := by
    intro s hs hcomm
    have := hZFγ S (by rw [hst1]; exact F.sylow_P2)
    rw [hQ1, hZ2] at this
    rw [← this]
    refine ⟨hs, Subgroup.mem_centralizer_iff.mpr fun z hz => (hcomm z hz).symm⟩
  have hcrit : ∀ g' ∈ P1 L1 L2 S, g' ∉ bigB L1 L2 S → NotLe L1 L2 S g' →
      (conjSub g' (Z2q L1 L2 S) ⊓ Q2 L1 L2 S).relIndex (conjSub g' (Z2q L1 L2 S)) = 4 ∧
      (Z2q L1 L2 S ⊓ conjSub g' (Q2 L1 L2 S)).relIndex (Z2q L1 L2 S) = 4 := by
    intro g' hg' hg'B hnl
    set g'' : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨g', h₁ hg'⟩ with hg''
    have hg''0 : g'' • γ₀ = γ₀ := smul_eq_of_mem_stab (by rw [hst0]; exact hg')
    have hne : g'' • γ₁ ≠ γ₁ := by
      intro heq
      have : (g'' : G) ∈ stab γ₁ := mem_stab_of_smul_eq heq
      rw [hst1] at this
      exact hg'B (by rw [← F.P1_inf_P2]; exact ⟨hg', this⟩)
    have hZ'' : Zv (g'' • γ₁) = conjSub g' (Z2q L1 L2 S) := by rw [Zv_smul, hZ2]
    have hQ'' : Qv (g'' • γ₁) = conjSub g' (Q2 L1 L2 S) := by rw [Qv_smul, hQ1]
    have hadj : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj γ₀ (g'' • γ₁) := by
      have := (smul_adj g'' (u := γ₀) (v := γ₁)).mpr hadj01
      rwa [hg''0] at this
    have hd1 : dist γ₀ (g'' • γ₁) = 1 := dist_eq_one_iff_adj.mpr hadj
    have hcd : IsCritData γ₁ γ₀ (g'' • γ₁) :=
      { adj := hadj01.symm
        bAt_eq := by rw [← bAt_smul g γ₁, hgα]; exact hc.bAt_eq
        dist_eq := by
          have hle : dist γ₁ (g'' • γ₁) ≤ 2 := by
            have h10 : dist γ₁ γ₀ = 1 := dist_eq_one_iff_adj.mpr hadj01.symm
            have := dist_triangle_of_adj hadj01.symm (g'' • γ₁)
            rw [h10, hd1] at this
            omega
          have hev : Even (dist γ₁ (g'' • γ₁)) :=
            (vtype_eq_iff_even_dist rfl γ₁ (g'' • γ₁)).mp (vtype_smul g'' γ₁).symm
          have hne0 : dist γ₁ (g'' • γ₁) ≠ 0 := fun h0 =>
            hne ((dist_eq_zero_iff rfl).mp h0).symm
          obtain ⟨k, hk⟩ := hev
          rw [hb]; omega
        dist_eq' := by rw [hd1, hb]
        not_le := by rw [hZ2, hQ'']; exact hnl.right }
    have hh' : ¬ Zv (g'' • γ₁) ≤ Qv γ₁ := by
      rw [hZ'', hQ1]; exact hnl.left
    obtain ⟨-, -, -, -, hr1, hr2⟩ := H4 F hT1 hcd hh'
    rw [hZ2, hQ''] at hr1
    rw [hZ'', hQ1] at hr2
    exact ⟨hr2, hr1⟩
  have hexists : ∃ q ∈ P1 L1 L2 S, q ∉ bigB L1 L2 S ∧ NotLe L1 L2 S q := by
    have hadjβα' : (graph (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)).Adj β α' := by
      apply dist_eq_one_iff_adj.mp
      have := hc.dist_eq'
      rw [hb] at this
      omega
    have hα'' : g⁻¹ • α' ∈ nbrs γ₀ := by
      have := (smul_adj g⁻¹ (u := β) (v := α')).mpr hadjβα'
      rwa [← hgβ, inv_smul_smul] at this
    obtain ⟨q, hq, hqγ⟩ := stab_transitive_on_nbrs (γ := γ₀) (δ := γ₁) (δ' := g⁻¹ • α')
      hadj01 hα''
    rw [hst0] at hq
    have hα'eq : α' = (g * q) • γ₁ := by
      rw [mul_smul, hqγ, smul_inv_smul]
    have hZα' : Zv α' = conjSub (g : G) (conjSub (q : G) (Z2q L1 L2 S)) := by
      rw [hα'eq, Zv_smul, hZ2, Subgroup.coe_mul, conjSub_mul]
    have hQα' : Qv α' = conjSub (g : G) (conjSub (q : G) (Q2 L1 L2 S)) := by
      rw [hα'eq, Qv_smul, hQ1, Subgroup.coe_mul, conjSub_mul]
    refine ⟨(q : G), hq, ?_, ⟨?_, ?_⟩⟩
    · intro hqB
      have hqP2 : (q : G) ∈ stab γ₁ := by
        rw [hst1]; exact (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hqB
      have := smul_eq_of_mem_stab (g := q) hqP2
      have hα'α : α' = α := by rw [hα'eq, ← hgα, mul_smul, this]
      have h2 := hc.dist_eq
      rw [hα'α, CosetGeom.dist_self] at h2
      omega
    · intro hle
      apply h
      rw [hZα', hQα]
      exact conjSub_mono _ hle
    · intro hle
      apply hc.not_le
      rw [hZα, hQα']
      exact conjSub_mono _ hle
  obtain ⟨q, hq, hqB, hnl⟩ := hexists
  exact o1_false F ⟨hnorm1, hcard16, hfaith, hcrit, ⟨q, hq, hqB, hnl⟩⟩

end CFSG.Quasithin.Kleidman.F204

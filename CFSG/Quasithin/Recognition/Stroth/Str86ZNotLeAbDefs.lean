module

public import CFSG.Quasithin.Recognition.Stroth.Str86Crit

import CFSG.Quasithin.Recognition.Stroth.Str86CaseIBasics
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeDefs

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

@[expose] def Str86CritNotEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
      ¬ (4 ≤ str86CritB L1 L2 S ∧ Even (str86CritB L1 L2 S))

@[expose] def Str86CritNot3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
      str86CritB L1 L2 S ≠ 3

@[expose] def Str86CritNotOdd5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
    Z2 L1 L2 S ≤ Q1 L1 L2 S →
      ¬ (5 ≤ str86CritB L1 L2 S ∧ Odd (str86CritB L1 L2 S))

variable {G : Type} [Group G] [Finite G]

theorem str86_three_le_critB {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (habel : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1, ∀ y ∈ conjClosure (Z2 L1 L2 S) L1,
      x * y = y * x) :
    3 ≤ str86CritB L1 L2 S := by
  classical
  have hc := str86_critHypN hF hSB h1 hB2 h2 hZI
  have hyp := hc.amalgam
  obtain ⟨-, -, -, hSCZ2, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hP2 : P2 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := hyp.le₁
  have hP1 : P1 L1 L2 S ≤ L1 ⊔ L2 ⊔ S := hyp.le₂
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hZ2N : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hc.normalizes
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hBL1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := bigB_le_normalizer_of_hyp111 hF.1
  have hP1Q1 : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) := le_normalizer_pCoreOf 2 _
  have hQball : ∀ μ : CosetGeom (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S),
      pCoreOf 2 (stab μ) ≤ ballStab 1 μ := CosetGeom.pCoreOf_stab_le_ballStab_one hyp
  have hQ2ball : Q2 L1 L2 S ≤ ballStab 1 (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    have h := hQball (γ₀ _ _ _)
    rwa [CosetGeom.stab_γ₀ hP2] at h
  have hQ1ball : Q1 L1 L2 S ≤ ballStab 1 (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    have h := hQball (γ₁ _ _ _)
    rwa [CosetGeom.stab_γ₁ hP1] at h
  have hcomm : ∀ h ∈ P1 L1 L2 S, ∀ x ∈ Z2 L1 L2 S, ∀ z ∈ Z2 L1 L2 S,
      x * (h * z * h⁻¹) = (h * z * h⁻¹) * x := by
    intro h hh x hx z hz
    obtain ⟨l, hl, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBL1).mp hh
    have hbz : b * z * b⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hZ2N (hBP2 hb)) z).mp hz
    have hxC : x ∈ conjClosure (Z2 L1 L2 S) L1 :=
      Subgroup.subset_closure ⟨1, L1.one_mem, x, hx, by group⟩
    have hyC : l * (b * z * b⁻¹) * l⁻¹ ∈ conjClosure (Z2 L1 L2 S) L1 :=
      Subgroup.subset_closure ⟨l, hl, _, hbz, rfl⟩
    have e : l * b * z * (l * b)⁻¹ = l * (b * z * b⁻¹) * l⁻¹ := by group
    rw [e]
    exact habel x hxC _ hyC
  have hZQh : ∀ h ∈ P1 L1 L2 S, Z2 L1 L2 S ≤ conjSub h (Q2 L1 L2 S) := by
    intro h hh x hx
    rw [mem_conjSub]
    have hxS : h⁻¹ * x * h ∈ S := by
      have h' := (Subgroup.mem_normalizer_iff.mp (hP1Q1 ((P1 L1 L2 S).inv_mem hh)) x).mp (hZ hx)
      rw [inv_inv] at h'
      exact hQ1S h'
    rw [← hSCZ2]
    refine Subgroup.mem_inf.mpr ⟨hxS, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have h' := hcomm h hh x hx z hz
    calc z * (h⁻¹ * x * h) = h⁻¹ * ((h * z * h⁻¹) * x) * h := by group
      _ = h⁻¹ * (x * (h * z * h⁻¹)) * h := by rw [h']
      _ = h⁻¹ * x * h * z := by group
  rw [CritHypN.le_critB_iff hc]
  intro μ hμ
  have hG := hyp.gen
  have hmono : ∀ (k : G) {H K : Subgroup G}, H ≤ K → conjSub k H ≤ conjSub k K :=
    fun k _ _ hHK => (F112Crit.conjSub_le_conjSub_iff k).mpr hHK
  rcases (by omega : CosetGeom.dist (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) μ = 0 ∨
      CosetGeom.dist (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) μ = 1 ∨
      CosetGeom.dist (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) μ = 2) with h0 | h1' | h2'
  ·
    rw [CosetGeom.dist_eq_zero_iff hG] at h0
    rw [← h0]
    exact (omegaOneCenterOf_le _).trans hQ2ball
  ·
    have hadj := CosetGeom.dist_eq_one_iff_adj.mp h1'
    obtain ⟨g, hg0, rfl⟩ := F112Crit.exists_edge_conj (CosetGeom.vtype_γ₀) hadj
    have hgP2 : (g : G) ∈ P2 L1 L2 S := by
      have h' := CosetGeom.mem_stab_of_smul_eq hg0.symm
      rwa [CosetGeom.stab_γ₀ hP2] at h'
    rw [CosetGeom.ballStab_smul]
    have e : Z2 L1 L2 S = conjSub (g : G) (Z2 L1 L2 S) :=
      (F1.conjSub_eq_of_mem_normalizer (hZ2N hgP2)).symm
    rw [e]
    exact hmono _ (hZ.trans hQ1ball)
  ·
    obtain ⟨ν, hμν, hν⟩ := CosetGeom.exists_adj_dist_eq hG (d := 1) h2'
    obtain ⟨g, hg0, rfl⟩ := F112Crit.exists_edge_conj (CosetGeom.vtype_γ₀)
      (CosetGeom.dist_eq_one_iff_adj.mp hν)
    have hgP2 : (g : G) ∈ P2 L1 L2 S := by
      have h' := CosetGeom.mem_stab_of_smul_eq hg0.symm
      rwa [CosetGeom.stab_γ₀ hP2] at h'
    have hadj' : (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj
        (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (g⁻¹ • μ) := by
      have h' := (CosetGeom.smul_adj (g⁻¹)).mpr hμν.symm
      simpa using h'
    obtain ⟨h, hh⟩ := CosetGeom.exists_smul_edge hadj'
    rcases hh with ⟨hh1, -⟩ | ⟨hh2, hh1⟩
    · exfalso
      have hv := congrArg vtype hh1
      rw [CosetGeom.vtype_smul, CosetGeom.vtype_γ₀, CosetGeom.vtype_γ₁] at hv
      exact absurd hv (by decide)
    · have hhP1 : (h : G) ∈ P1 L1 L2 S := by
        have h' := CosetGeom.mem_stab_of_smul_eq hh1
        rwa [CosetGeom.stab_γ₁ hP1] at h'
      have hμ' : μ = g • (h • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
        rw [hh2, smul_inv_smul]
      rw [hμ', CosetGeom.ballStab_smul, CosetGeom.ballStab_smul]
      have e : Z2 L1 L2 S = conjSub (g : G) (Z2 L1 L2 S) :=
        (F1.conjSub_eq_of_mem_normalizer (hZ2N hgP2)).symm
      rw [e]
      exact hmono _ ((hZQh h hhP1).trans (hmono _ hQ2ball))

theorem str86ZNotLeAb_of_crit (hE : Str86CritNotEven)
    (h3 : Str86CritNot3) (h5 : Str86CritNotOdd5) : Str86ZNotLeAb := by
  intro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI hZ habel
  have hb := str86_three_le_critB hF hSB h1 hB2 h2 hZI hZ habel
  rcases Nat.lt_or_ge (str86CritB L1 L2 S) 4 with hlt | hge
  · exact h3 G L1 L2 S hF hSB h1 hB2 h2 hZI hZ (by omega)
  · rcases Nat.even_or_odd (str86CritB L1 L2 S) with hev | hodd
    · exact hE G L1 L2 S hF hSB h1 hB2 h2 hZI hZ ⟨hge, hev⟩
    · have h5' : 5 ≤ str86CritB L1 L2 S := by
        obtain ⟨j, hj⟩ := hodd
        omega
      exact h5 G L1 L2 S hF hSB h1 hB2 h2 hZI hZ ⟨h5', hodd⟩

end CFSG.Quasithin.Stroth

end

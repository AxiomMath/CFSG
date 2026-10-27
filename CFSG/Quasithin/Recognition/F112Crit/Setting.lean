module

public import CFSG.Quasithin.Recognition.F112WKernel
public import CFSG.Quasithin.Recognition.F112WSetup

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

structure CritAmalgam (G₀ G₁ G₂ T Z : Subgroup G) : Prop where
  amalgam : AmalgamHyp G₀ G₁ G₂ T
  charTwo₂ : CharTwo G₂
  ne_bot : Z ≠ ⊥
  isElemAbelian : IsElemAbelian 2 Z
  le_T : Z ≤ T
  centralizes : G₁ ≤ Subgroup.centralizer (Z : Set G)
  prime : Nat.Prime (G₁.relIndex G₂)

namespace CritAmalgam

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem le_left (hc : CritAmalgam G₀ G₁ G₂ T Z) : Z ≤ G₁ :=
  hc.le_T.trans (hc.amalgam.T_le.trans inf_le_left)

theorem le_right (hc : CritAmalgam G₀ G₁ G₂ T Z) : Z ≤ G₂ :=
  hc.le_T.trans (hc.amalgam.T_le.trans inf_le_right)

theorem isPGroup (hc : CritAmalgam G₀ G₁ G₂ T Z) : IsPGroup 2 Z :=
  isPGroup_of_isElemAbelian hc.isElemAbelian

theorem normalizes (hc : CritAmalgam G₀ G₁ G₂ T Z) : G₁ ≤ Subgroup.normalizer (Z : Set G) :=
  hc.centralizes.trans (Subgroup.centralizer_le_normalizer (Z : Set G))

theorem le_pCoreOf (hc : CritAmalgam G₀ G₁ G₂ T Z) : Z ≤ pCoreOf 2 G₁ :=
  le_pCoreOf_of_le_normalizer 2 hc.le_left hc.normalizes hc.isPGroup

end CritAmalgam

section Geometry

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

theorem conjSub_le_conjSub_iff (g : G) {H K : Subgroup G} :
    conjSub g H ≤ conjSub g K ↔ H ≤ K := by
  rw [conjSub_le_iff, conjSub_conjSub_inv]

theorem exists_edge_conj {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false) (hδ : δ ∈ nbrs γ) :
    ∃ g : ↥G₀, γ = g • γ₀ G₀ G₁ G₂ ∧ δ = g • γ₁ G₀ G₁ G₂ := by
  obtain ⟨g, hg | hg⟩ := CosetGeom.exists_smul_edge (show (graph G₀ G₁ G₂).Adj γ δ from hδ)
  · exact ⟨g, hg.1.symm, hg.2.symm⟩
  · exfalso
    have h := congrArg vtype hg.2
    rw [CosetGeom.vtype_smul, CosetGeom.vtype_γ₁, hγ] at h
    exact absurd h (by decide)

theorem Zv_smul_γ₀ (hc : CritAmalgam G₀ G₁ G₂ T Z) (g : ↥G₀) :
    Vv Z (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) Z :=
  CosetGeom.Vv_smul_γ₀ hc.normalizes g

theorem Zv_le_ballStab_smul_iff (hc : CritAmalgam G₀ G₁ G₂ T Z) (g : ↥G₀)
    (μ : CosetGeom G₀ G₁ G₂) :
    Vv Z (g • γ₀ G₀ G₁ G₂) ≤ ballStab 1 (g • μ) ↔ Z ≤ ballStab 1 μ := by
  rw [Zv_smul_γ₀ hc, CosetGeom.ballStab_smul, conjSub_le_conjSub_iff]

@[expose] noncomputable def critB (G₀ G₁ G₂ Z : Subgroup G) : ℕ :=
  sInf {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ}

section Finite

variable [Finite G]

theorem critB_set_nonempty (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ}.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h : ∀ μ : CosetGeom G₀ G₁ G₂, Z ≤ ballStab 1 μ := fun μ => by
    by_contra hμ
    have : CosetGeom.dist (γ₀ G₀ G₁ G₂) μ ∈
        {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ} := ⟨μ, rfl, hμ⟩
    rw [hne] at this
    exact this
  obtain ⟨n, -, hbot⟩ := CosetGeom.exists_ballStab_eq_bot hc.amalgam
  have hZ : Z ≤ ballStab n (γ₀ G₀ G₁ G₂) := fun x hx =>
    CosetGeom.mem_ballStab.mpr fun δ _ => CosetGeom.ballStab_le_stab 1 δ (h δ hx)
  rw [hbot] at hZ
  exact hc.ne_bot (le_bot_iff.mp hZ)

theorem lt_critB_imp (hc : CritAmalgam G₀ G₁ G₂ T Z) {μ : CosetGeom G₀ G₁ G₂}
    (hμ : CosetGeom.dist (γ₀ G₀ G₁ G₂) μ < critB G₀ G₁ G₂ Z) : Z ≤ ballStab 1 μ := by
  by_contra h
  exact absurd (Nat.sInf_le (s := {n : ℕ | ∃ μ ∈ sphere n (γ₀ G₀ G₁ G₂), ¬ Z ≤ ballStab 1 μ})
    ⟨μ, rfl, h⟩) (not_le.mpr hμ)

theorem exists_dist_eq_critB (hc : CritAmalgam G₀ G₁ G₂ T Z) :
    ∃ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ = critB G₀ G₁ G₂ Z ∧
      ¬ Z ≤ ballStab 1 μ := by
  obtain ⟨μ, hμ, hμ'⟩ := Nat.sInf_mem (critB_set_nonempty hc)
  exact ⟨μ, hμ, hμ'⟩

theorem le_critB_iff (hc : CritAmalgam G₀ G₁ G₂ T Z) (k : ℕ) :
    k ≤ critB G₀ G₁ G₂ Z ↔
      ∀ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist (γ₀ G₀ G₁ G₂) μ < k → Z ≤ ballStab 1 μ := by
  refine ⟨fun hk μ hμ => lt_critB_imp hc (lt_of_lt_of_le hμ hk), fun h => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨μ, hμ, hμ'⟩ := exists_dist_eq_critB hc
  exact hμ' (h μ (hμ ▸ hlt))

theorem le_critB_iff_at (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) (k : ℕ) :
    k ≤ critB G₀ G₁ G₂ Z ↔
      ∀ μ : CosetGeom G₀ G₁ G₂, CosetGeom.dist γ μ < k → Vv Z γ ≤ ballStab 1 μ := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
  rw [le_critB_iff hc]
  constructor
  · intro h μ hμ
    obtain ⟨μ', rfl⟩ : ∃ μ', μ = g • μ' := ⟨g⁻¹ • μ, by simp⟩
    rw [CosetGeom.dist_smul] at hμ
    exact (Zv_le_ballStab_smul_iff hc g μ').mpr (h μ' hμ)
  · intro h μ' hμ'
    refine (Zv_le_ballStab_smul_iff hc g μ').mp (h (g • μ') ?_)
    rwa [CosetGeom.dist_smul]

end Finite

end Geometry

abbrev P₁ (L₁ L₂ S : Subgroup G) : Subgroup G := L₁ ⊔ bigB L₁ L₂ S

abbrev P₂ (L₁ L₂ S : Subgroup G) : Subgroup G := L₂ ⊔ bigB L₁ L₂ S

structure Setting (L₁ L₂ S Z : Subgroup G) : Prop where
  hyp : Hyp111R L₁ L₂ S
  S_le : S ≤ L₁
  ne_bot : Z ≠ ⊥
  isElemAbelian : IsElemAbelian 2 Z
  le_S : Z ≤ S
  centralizes : P₂ L₁ L₂ S ≤ Subgroup.centralizer (Z : Set G)
  prime : Nat.Prime ((borelOf L₁ S).relIndex L₁)
  cyclic : ∀ X : Subgroup (oTwoQuot ↥L₁), IsPGroup 2 X → IsCyclic ↥X

namespace Setting

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

theorem relIndex_P₂_P₁ (h : Hyp111R L₁ L₂ S) :
    (P₂ L₁ L₂ S).relIndex (P₁ L₁ L₂ S) = (borelOf L₁ S).relIndex L₁ := by
  rw [← Subgroup.inf_relIndex_right, F112W.inf_alpha_beta h,
    F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left h).1,
    F1.inf_bigB_eq_borelOf h]

theorem toCritAmalgam (hs : Setting L₁ L₂ S Z) :
    CritAmalgam (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) S Z where
  amalgam := F112W.amalgamHyp_alpha hs.hyp
  charTwo₂ := F112W.charTwo_beta hs.hyp
  ne_bot := hs.ne_bot
  isElemAbelian := hs.isElemAbelian
  le_T := hs.le_S
  centralizes := hs.centralizes
  prime := by rw [relIndex_P₂_P₁ hs.hyp]; exact hs.prime

end Setting

end CFSG.Quasithin.F112Crit

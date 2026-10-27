module

public import CFSG.Quasithin.Recognition.SzVBEvenCtx
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Basic

variable (hC : GeoCtx G₀ G₁ G₂ T V z)

include hC

omit [Finite G] in
theorem V_ne_bot : V ≠ ⊥ := hC.natS3.ne_bot

omit [Finite G] in
theorem z_mul_self : z * z = 1 := by
  have := F7.isElemAbelian_pow_eq_one hC.klein.elemAbelian hC.klein.z_mem
  rwa [pow_two] at this

omit [Finite G] in
theorem isPGroup_stab_inf {x y : CosetGeom G₀ G₁ G₂} (hxy : (graph G₀ G₁ G₂).Adj x y) :
    IsPGroup 2 ↥(stab x ⊓ stab y) := by
  have hT2 : IsPGroup 2 ↥T := hC.hyp.sylow₁.2.1
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge hxy
  · rw [stab_smul, stab_smul, stab_γ₀ hC.hyp.le₁, stab_γ₁ hC.hyp.le₂, ← conjSub_inf, hC.inf_eq]
    exact F7.isPGroup_conjSub hT2
  · rw [stab_smul, stab_smul, stab_γ₀ hC.hyp.le₁, stab_γ₁ hC.hyp.le₂, ← conjSub_inf,
      inf_comm G₂ G₁, hC.inf_eq]
    exact F7.isPGroup_conjSub hT2

theorem ballStab_one_eq_pCoreOf (x : CosetGeom G₀ G₁ G₂) :
    ballStab 1 x = pCoreOf 2 (stab x) := by
  refine le_antisymm ?_ (pCoreOf_stab_le_ballStab_one hC.hyp.toAmalgamHyp x)
  obtain ⟨y, hxy⟩ := exists_adj x
  exact le_pCoreOf_of_le_normalizer 2 (ballStab_le_stab 1 x) (le_normalizer_ballStab 1 x)
    ((isPGroup_stab_inf hC hxy).to_le (le_inf (ballStab_le_stab 1 x)
      (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hxy).le)))

omit [Finite G] in
theorem G₂_le_normalizer_zpowers :
    G₂ ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  intro x hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hcx : Commute x z := hC.klein.z_cent x hx
  exact (hcx.zpow_right n).eq.symm

omit [Finite G] in
theorem card_Zv {y : CosetGeom G₀ G₁ G₂} (hy : vtype y = true) : Nat.card (Zv z y) = 2 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hy
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact z_mul_self hC
  rw [Zv_smul_γ₁ (G₂_le_normalizer_zpowers hC), card_conjSub, Nat.card_zpowers]
  exact orderOf_eq_prime hz2 hC.klein.z_ne_one

theorem pCoreOf_fixes_conj {c : G} (hc : c ∈ pCoreOf 2 G₂) (hcG : c ∈ G₂)
    (U : ConjSet G₂ V) : (⟨c, hcG⟩ : ↥G₂) • U = U := by
  obtain ⟨x, hx, hU⟩ := U.2
  have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 G₂ : Set G) := le_normalizer_pCoreOf 2 G₂ hx
  have hc' : x⁻¹ * c * x ∈ pCoreOf 2 G₂ := (Subgroup.mem_normalizer_iff''.mp hxN c).mp hc
  have hk : x⁻¹ * c * x ∈ Subgroup.normalizer (V : Set G) :=
    hC.hyp.normalizes (hC.hyp.sylow₁.1 (isSylowTwoOf_pCoreOf_le hC.hyp.sylow₂ hc'))
  apply Subtype.ext
  show conjSub c U.1 = U.1
  have e : c * x = x * (x⁻¹ * c * x) := by group
  rw [hU, ← conjSub_mul, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer hk]

theorem commutator_conjClosure_pCoreOf_le :
    ⁅conjClosure V G₂, pCoreOf 2 G₂⁆ ≤ Subgroup.zpowers z := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro c hc a ha
  have hcG : c ∈ G₂ := pCoreOf_le 2 G₂ hc
  rw [commutatorElement_def]
  rcases commutator_mem_of_fixes hC.klein hcG (pCoreOf_fixes_conj hC hc hcG) ha with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact Subgroup.mem_zpowers z

theorem commutator_Vv_pCoreOf_le_Zv {y : CosetGeom G₀ G₁ G₂} (hy : vtype y = true) :
    ⁅Vv V y, pCoreOf 2 (stab y)⁆ ≤ Zv z y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hy
  rw [Vv_smul hC.hyp.normalizes, stab_smul, stab_γ₁ hC.hyp.le₂, pCoreOf_conjSub,
    Zv_smul_γ₁ (G₂_le_normalizer_zpowers hC), conjSub_commutator,
    Vv_γ₁ hC.hyp.le₂ hC.hyp.normalizes]
  exact conjSub_mono _ (commutator_conjClosure_pCoreOf_le hC)

theorem isElemAbelian_Vv_of_vtype {y : CosetGeom G₀ G₁ G₂} (hy : vtype y = true)
    (hb : 3 ≤ critDist G₀ G₁ G₂ V) : IsElemAbelian 2 (Vv V y) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hy
  rw [Vv_smul hC.hyp.normalizes]
  exact F7.isElemAbelian_conjSub (isElemAbelian_Vv_γ₁ hC.hyp (V_ne_bot hC) hb)

end Basic

end CFSG.Quasithin.SzVB

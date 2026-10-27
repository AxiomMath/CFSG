module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.SzVBEvenCtx

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

section Local

variable (hC : GeoCtx G₀ G₁ G₂ T V z)

include hC

omit [Finite G] in
theorem card_Vv {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) : Nat.card (Vv V x) = 4 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  rw [Vv_smul_γ₀ hC.hyp.normalizes, card_conjSub]
  exact hC.natS3.card_eq

theorem pCoreOf_le_centralizer_Vv {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) :
    pCoreOf 2 (stab x) ≤ Subgroup.centralizer (Vv V x : Set G) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  rw [Vv_smul_γ₀ hC.hyp.normalizes, stab_smul, stab_γ₀ hC.hyp.le₁, pCoreOf_conjSub,
    conjSub_centralizer]
  exact conjSub_mono _ (pCoreOf_le_centralizer hC.hyp)

omit [Finite G] in
theorem Vv_le_pCoreOf_stab {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) :
    Vv V x ≤ pCoreOf 2 (stab x) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  rw [Vv_smul_γ₀ hC.hyp.normalizes, stab_smul, stab_γ₀ hC.hyp.le₁, pCoreOf_conjSub]
  exact conjSub_mono _ (V_le_pCoreOf hC.hyp)

omit [Finite G] hC in
private theorem relIndex_conjSub_conjSub (g : G) (H K : Subgroup G) :
    (conjSub g H).relIndex (conjSub g K) = H.relIndex K :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) H K
    (MulEquiv.injective (MulAut.conj g))

omit hC in
private theorem relIndex_le_of_isSylowTwoOf {H T Q X : Subgroup G} (hT : IsSylowTwoOf T H)
    (hQ : H ≤ Subgroup.normalizer (Q : Set G)) (hXle : X ≤ H) (hX : IsPGroup 2 X) :
    Q.relIndex X ≤ Q.relIndex T := by
  obtain ⟨y, hy, hXy⟩ := isSylowTwoOf_exists_conj_le hT hXle hX
  have h2 : conjSub y Q = Q := conjSub_eq_of_mem_normalizer (hQ hy)
  have h3 : Q.relIndex (conjSub y T) = Q.relIndex T := by
    rw [← relIndex_conjSub_conjSub y Q T, h2]
  rw [← h3]
  exact Subgroup.relIndex_le_of_le_right hXy (Subgroup.index_ne_zero_of_finite
    (H := Q.subgroupOf (conjSub y T)))

theorem relIndex_pCoreOf_le_two {x : CosetGeom G₀ G₁ G₂} (hx : vtype x = false) {X : Subgroup G}
    (hXle : X ≤ stab x) (hX : IsPGroup 2 X) : (pCoreOf 2 (stab x)).relIndex X ≤ 2 := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hx
  rw [stab_smul, stab_γ₀ hC.hyp.le₁] at hXle ⊢
  have hT : IsSylowTwoOf (conjSub (g : G) T) (conjSub (g : G) G₁) :=
    isSylowTwoOf_conj hC.hyp.sylow₁ _
  refine (relIndex_le_of_isSylowTwoOf hT (le_normalizer_pCoreOf 2 _) hXle hX).trans ?_
  rw [pCoreOf_conjSub, relIndex_conjSub_conjSub, F112W.relIndex_pCoreOf_T hC.hyp hC.natS3]

end Local

end CFSG.Quasithin.SzVB

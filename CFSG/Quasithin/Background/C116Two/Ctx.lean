module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Ctx (H T V L : Subgroup G) : Prop where
  charTwo : CharTwo H
  red : IsTwoReducedIn H V
  sylow : IsSylowTwoOf T H
  chi : IsChiBlock H L
  notCent : ¬ L ≤ Subgroup.centralizer (V : Set G)

theorem Ctx.V_le_T {H T V L : Subgroup G} (h : Ctx H T V L) : V ≤ T :=
  (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.red.1 h.red.2.1
    (B2F.isPGroup_of_isElemAbelian h.red.2.2.1)).trans (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf h.sylow)

theorem Ctx.commutator_V_eq_blockU {H T V L : Subgroup G} (h : Ctx H T V L) :
    ⁅V, L⁆ = blockU L := by
  have hVH : V ≤ H := h.red.1
  have hVN : H ≤ Subgroup.normalizer (V : Set G) := h.red.2.1
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.red.2.2.1
  have hVn : (V.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mpr hVN
  have hLH : L ≤ H := h.chi.1.2.1
  have hshort : IsShort2 L := h.chi.1.1
  have hsub : IsSubnormal L H := C1GN.isSubnormal_of_isBlock2 h.chi.1
  have hle : ⁅V, L⁆ ≤ blockU L := by
    have := L246C127.commutator_le_blockU hshort hsub hVH hVn hV2
    exact this
  have hne : ⁅V, L⁆ ≠ ⊥ := by
    intro hbot
    apply h.notCent
    have : V ≤ Subgroup.centralizer (L : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.mp (this hv) l hl)).symm
  exact le_antisymm hle
    (L246C127.blockU_le_commutator_of_ne_bot hshort (hLH.trans hVN) hV2 hle hne)

theorem Ctx.blockU_le_V {H T V L : Subgroup G} (h : Ctx H T V L) : blockU L ≤ V := by
  have hVN : H ≤ Subgroup.normalizer (V : Set G) := h.red.2.1
  have hLH : L ≤ H := h.chi.1.2.1
  rw [← h.commutator_V_eq_blockU, Subgroup.commutator_le]
  intro v hv l hl
  have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVN (hLH hl)) v⁻¹).mp
    (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact V.mul_mem hv h1

theorem mem_omegaOneCenter_of_centralizes {T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVT : V ≤ T) {u : G} (hu : u ∈ V) (hJu : ∀ j ∈ thompsonJ T, j * u = u * j) :
    u ∈ omegaOneCenterOf (thompsonJ T) := by
  rw [← (omegaOne_centralizer_thompsonJ T).1]
  refine Subgroup.subset_closure ⟨⟨hVT hu, Subgroup.mem_centralizer_iff.mpr ?_⟩, hV.2 u hu⟩
  intro j hj
  exact hJu j hj

theorem mem_normalizer_of_conj_eq {L : Subgroup G} {b : G}
    (h : L.map (MulAut.conj b).toMonoidHom = L) : b ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h2 : b * y * b⁻¹ = b * x * b⁻¹ := by simpa [MulAut.conj_apply] using hyx
      simpa using h2
    rw [← this]
    exact hy

end CFSG.Quasithin.C116Two

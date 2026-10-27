module

public import CFSG.Quasithin.EmptyFaithful.S153E58S
public import CFSG.Quasithin.EmptyFaithful.S153E58N
public import CFSG.Quasithin.EmptyFaithful.S153E58O
public import CFSG.Quasithin.EmptyFaithful.S153E58Q
public import CFSG.Quasithin.EmptyFaithful.S153E58R

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

theorem lemma_15_3_58 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
    (h09 : Input15309Two) (iTwo : Input15358Two) (iG93 : Input15358G93) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}
    (c : Chain15357 cx N₁ N₂ g s y t₁) : Concl15358 cx s := by
  obtain ⟨hs1, hcore⟩ := S153E58.core58 h09 iTwo iG93 cx c
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨K, W₁, W₂, π, hS, hperf, hπ, u₁, hu₁W, hu₁1, hu₁P⟩ := hcore
  have hK := hS.oTwoUpper_eq hπ hperf
  have hidx := hS.relIndex_eq_two hπ
  have hequiv := hS.nonempty_mulEquiv hπ
  subst hK
  refine ⟨hequiv, hs1, S153E58.isExtraspecialPlus_U cx c.toChain15356 c.h55.1 hs1, ?_⟩
  intro t₂ ht₂T ht₂
  have hUCT := S153E58.rho_mem_K_of_UCT cx (K := oTwoUpper (HStar153 T M V₁ Mc)) hu₁P
    (fun h hh hf => hS.mem_K_of_fix hπ hh hu₁W hu₁1 hf)
  have ht₂N : t₂ ∈ S153E57.NZ T := S153E57.t₁_mem_NZ cx ht₂T
  have ht₂Mc : t₂ ∈ Mc := T_le_Mc cx ht₂T
  have hnot := S153E58.rho_not_mem_K_of_not_UCT cx c.h51 c.h52 hS.KH hidx hUCT ht₂T ht₂
  have hg₀H : S153E57.rho cx ⟨t₂, ht₂N⟩ ∈ HStar153 T M V₁ Mc :=
    S153E57.rho_mem_XStar (B := Mc) cx ⟨t₂, ht₂N⟩ ht₂Mc
  have hsw := hS.swap_of_not_mem_K hπ hg₀H hnot
  have hginvH : (S153E57.rho cx ⟨t₂, ht₂N⟩)⁻¹ ∈ HStar153 T M V₁ Mc :=
    (HStar153 T M V₁ Mc).inv_mem hg₀H
  have hginvnot : (S153E57.rho cx ⟨t₂, ht₂N⟩)⁻¹ ∉ oTwoUpper (HStar153 T M V₁ Mc) := fun h =>
    hnot (by simpa using (oTwoUpper (HStar153 T M V₁ Mc)).inv_mem h)
  have hsw' := hS.swap_of_not_mem_K hπ hginvH hginvnot
  have hginv : S153E57.rho cx ⟨t₂⁻¹, S153E57.Mc_le_NZ cx (Mc.inv_mem ht₂Mc)⟩ =
      (S153E57.rho cx ⟨t₂, ht₂N⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hW₂eq : (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (S153E58.preU cx W₁) t₂)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) = W₂ := by
    ext w
    rw [S153E58.mem_tilde_conj_iff cx ht₂Mc, S153E58.tilde_preU, hginv]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hsw'.1 v hv
    · intro hw
      refine ⟨S153E57.rho cx ⟨t₂, ht₂N⟩ w, hsw.2 w hw, ?_⟩
      exact MulAut.inv_apply_self _ _ _
  have hW₁eq := S153E58.tilde_preU cx W₁
  refine ⟨π, S153E58.preU cx W₁, S153E58.Z_le_preU cx W₁, S153E58.preU_le cx W₁, ?_⟩
  rw [hW₁eq, hW₂eq]
  exact ⟨hS.dir, hπ, hS.realizes_dual hπ⟩

end S153E

end CFSG.Quasithin

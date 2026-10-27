module

public import CFSG.Quasithin.EmptyFaithful.S153E61BC
public import CFSG.Quasithin.EmptyFaithful.S153E58A
public import CFSG.Quasithin.EmptyFaithful.S153E58F
public import CFSG.Quasithin.EmptyFaithful.S153E59N

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61B

section Rank

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem rk_eq_of_card {W : Type*} [Group W] {n : ℕ} (h : Nat.card W = 2 ^ n) : rk W = n := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem map_phi_top_eq_Pt (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁)
    {a : G} (ha : a ∈ VZ T M) (haU : a ∉ UH153 T M V₁ Mc) (hN : a ∈ S153E57.NZ T) :
    letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
      commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
    (⊤ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))).map
      (S153E57.phi (S153E57.rho cx ⟨a, hN⟩)) = S153E58.Pt T M V₁ Mc := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  obtain ⟨-, hmem, huniq⟩ := rho_a_data cx c ha haU hN
  rw [← S153E57.commIn153_eq_map hmem huniq ⊤]
  exact S153E58.commIn153_eq_Pt cx c.toChain15356

theorem rho_a_mem_K (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15359 cx N₁ N₂ g s y t₁)
    {a : G} (ha : a ∈ VZ T M) (haU : a ∉ UH153 T M V₁ Mc) :
    S153E59.rho cx ⟨a, S153E59.VZ_le_Mc cx ha⟩ ∈ oTwoUpper (HStar153 T M V₁ Mc) := by
  by_contra hnot
  let _ : CommGroup ↥(S153E59.UT T M V₁ Mc) := commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have hMc : a ∈ Mc := S153E59.VZ_le_Mc cx ha
  have hN : a ∈ S153E57.NZ T := S153E57.Mc_le_NZ cx hMc
  have hH := S153E59.hstarFacts cx c.h58 c.ht₁.1 c.ht₁.2
  obtain ⟨W₁, W₂, hint, hsup, hcard, hswap⟩ := hH.swap
  have hs := hswap ⟨a, hMc⟩ hnot
  have hle := S153E59.rk_fix_le_of_swap hint hsup hs.1 hs.2
  have hle' := hle.trans_eq (S153E59.rk_eq_three_of_card hcard)
  rw [rho59_eq_rho57 cx ⟨a, hMc⟩] at hle'
  have hle'' : rk ↥(fixV (Subgroup.zpowers (S153E57.rho cx ⟨a, hN⟩))) ≤ 3 := hle'
  obtain ⟨-, hmem, huniq⟩ := rho_a_data cx c ha haU hN
  have hX : XStar153 T M V₁ Mc (VZ T M) = Subgroup.zpowers (S153E57.rho cx ⟨a, hN⟩) :=
    le_antisymm (fun w hw => by
      rcases huniq w hw with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _) (Subgroup.zpowers_le.2 hmem)
  have hcomm : commV (Subgroup.zpowers (S153E57.rho cx ⟨a, hN⟩)) = S153E58.Pt T M V₁ Mc := by
    rw [← hX, ← S153E58.commIn153_top_eq_commV]
    exact S153E58.commIn153_eq_Pt cx c.toChain15356
  have hrkP : rk ↥(S153E58.Pt T M V₁ Mc) = 2 := by
    refine rk_eq_of_card (n := 2) ?_
    rw [S153E58.card_Pt cx c.toChain15356]
    norm_num
  have hrkU : rk ↥(S153E59.UT T M V₁ Mc) = 6 := by
    refine rk_eq_of_card (n := 6) ?_
    have h := S153E57.card_tilde cx c.toChain15356
    rw [c.h58.two_s] at h
    exact h
  have h6 := rk_commV_add_rk_fixV (S153E57.rho cx ⟨a, hN⟩)
  rw [hcomm, hrkP, hrkU] at h6
  omega

end Rank

end S153E61B

end CFSG.Quasithin

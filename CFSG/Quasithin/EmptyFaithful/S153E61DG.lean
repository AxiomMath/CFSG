module

public import CFSG.Quasithin.EmptyFaithful.S153E56B
public import CFSG.Quasithin.EmptyFaithful.S153E58N
public import CFSG.Quasithin.EmptyFaithful.S153E59F
public import CFSG.Quasithin.EmptyFaithful.S153E61DE
public import CFSG.Quasithin.EmptyFaithful.S153E61Def

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section CardE

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem card_Pi {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    Nat.card ↥(Pi153 T Mc M V₁ N g) = 64 := by
  have h := S153E56a.card_eq_of_sumNat d.c54.h54.four_nat₁ d.pd.symm.V_le_P₂
  rw [d.hs, cx.c.hyp.card_VZ] at h
  norm_num at h
  exact h

theorem Pi_le_oTwoUpper {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    Pi153 T Mc M V₁ N g ≤ oTwoUpper Mc := by
  have hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc := d.c54.h54.one
  have h1 : Pgp153 T M V₁ Mc g ≤ T ⊓ oTwoUpper Mc := by
    rw [S153E55.P_eq hI]
    exact pCoreOf_two_le_of_isSylowTwoOf d.h59.two
  exact d.pd.symm.P₂_le_P.trans (h1.trans inf_le_right)

theorem exists_E {cx : Ctx15350 T Mc M V₁ V₂ t} (hD : S153E61.Data61 cx) (d : Dat61 cx N N' g s)
    (hel : ∀ a ∈ Pi153 T Mc M V₁ N g, ∀ b ∈ Pi153 T Mc M V₁ N g, a * b = b * a ∧ a * a = 1) :
    ∃ e ∈ Pi153 T Mc M V₁ N g, e ∈ UH153 T M V₁ Mc ∧ e ∉ VZ T M := by
  by_contra hcon
  push Not at hcon
  have hPiK := Pi_le_oTwoUpper d
  have hPiMc : Pi153 T Mc M V₁ N g ≤ Mc := hPiK.trans (oTwoUpper_le Mc)
  let f : ↥(Pi153 T Mc M V₁ N g) →* MulAut ↥(S153E59.UT T M V₁ Mc) :=
    (S153E59.rho cx).comp (Subgroup.inclusion hPiMc)
  have hker : f.ker = (Pi153 T Mc M V₁ N g ⊓ UH153 T M V₁ Mc).subgroupOf (Pi153 T Mc M V₁ N g) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show S153E59.rho cx (Subgroup.inclusion hPiMc x) = 1 ↔ _
    rw [S153E59.rho_eq_one_iff, ← d.h59.one]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      Pi153 T Mc M V₁ N g ⊓ UH153 T M V₁ Mc ≤ Pi153 T Mc M V₁ N g)).toEquiv, card_Pi d] at h1
  have hrange : Nat.card ↥f.range ≤ 4 := by
    obtain ⟨K, W₁, W₂, π, hS, hperf, hπ⟩ := hD
    let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
      commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
    have hK : oTwoUpper (HStar153 T M V₁ Mc) = K := hS.oTwoUpper_eq hπ hperf
    have hrangeK : f.range ≤ K := by
      rintro _ ⟨x, rfl⟩
      rw [← hK]
      have hx : (⟨x.1, hPiMc x.2⟩ : ↥Mc) ∈ (oTwoUpper Mc).subgroupOf Mc := hPiK x.2
      have := Subgroup.mem_map_of_mem (S153E59.rho cx) hx
      rw [S153E59.map_rho_oTwoUpper cx] at this
      exact this
    let e : ↥K ≃* ↥(StatedSL 3 (ZMod 2)) := (hS.piEquiv hπ).symm
    let A' : Subgroup ↥K := f.range.subgroupOf K
    have hA'card : Nat.card ↥A' = Nat.card ↥f.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrangeK).toEquiv
    rw [← hA'card]
    refine card_le_four_of_elemAbelian e A' ?_ ?_
    · intro a ha
      obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 ha
      have h : (a : MulAut ↥(S153E59.UT T M V₁ Mc)) * (a : MulAut ↥(S153E59.UT T M V₁ Mc)) = 1 := by
        rw [← hx, ← map_mul]
        have : x * x = 1 := Subtype.ext (hel x.1 x.2 x.1 x.2).2
        rw [this, map_one]
      exact Subtype.ext h
    · intro a ha b hb
      obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 ha
      obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.1 hb
      have h : (a : MulAut ↥(S153E59.UT T M V₁ Mc)) * (b : MulAut ↥(S153E59.UT T M V₁ Mc)) =
          (b : MulAut ↥(S153E59.UT T M V₁ Mc)) * (a : MulAut ↥(S153E59.UT T M V₁ Mc)) := by
        rw [← hx, ← hy, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hel x.1 x.2 y.1 y.2).1
      exact Subtype.ext h
  have hle : Pi153 T Mc M V₁ N g ⊓ UH153 T M V₁ Mc ≤ VZ T M ⊓ UH153 T M V₁ Mc :=
    fun x hx => ⟨hcon x hx.1 hx.2, hx.2⟩
  have h8 := Subgroup.card_le_of_le hle
  rw [card_VU d] at h8
  nlinarith

end CardE

end S153E61D

end CFSG.Quasithin

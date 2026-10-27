module

public import CFSG.Quasithin.EmptyFaithful.S146zNCtx

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Surj

variable {G : Type} [Group G] [Finite G]

theorem secRho_surjective {Z U₁ L : Subgroup G} (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hLU : L ≤ Subgroup.normalizer (U₁ : Set G)) (hU₁Z : U₁ ≤ Subgroup.normalizer (Z : Set G))
    (hel : IsElemAbelian 2 (tildeOf Z U₁)) (h8 : Nat.card (tildeOf Z U₁) = 8)
    (hC : centralizerMod Z L U₁ ≤ pCoreOf 2 L) (h168 : (pCoreOf 2 L).relIndex L = 168) :
    Function.Surjective (secRho hLZ hLU) := by
  classical
  set ρ := secRho hLZ hLU with hρ
  have hker : ρ.ker = (centralizerMod Z L U₁).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨x.2, hLZ x.2, fun u hu => commutator_mem_of_secRho_eq_one hLZ hLU hU₁Z h hu⟩
    · intro h
      exact secRho_eq_one_of_comm hLZ hLU hU₁Z h.2.2
  have hidx : ρ.ker.index = (centralizerMod Z L U₁).relIndex L := by rw [hker]; rfl
  have hcard := Subgroup.index_ker ρ
  have hge : 168 ≤ (centralizerMod Z L U₁).relIndex L := by
    have hd := Subgroup.relIndex_dvd_of_le_left L hC
    rw [h168] at hd
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)) hd
  have hAut : Nat.card (MulAut ↥(tildeOf Z U₁)) = 168 :=
    card_mulAut_of_card_eight (fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2))
      (fun a => Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)) h8
  have hrange : ρ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    rw [hAut, ← hcard, hidx]
    exact hge
  exact MonoidHom.range_eq_top.mp hrange

end Surj

end CFSG.Quasithin.ThreeC

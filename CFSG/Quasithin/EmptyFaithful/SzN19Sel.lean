module

public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.Quasithin.Background.S1549CIn
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.EmptyFaithful.SBd8SmallU33

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.S1549C
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace SzN19

section Sel

noncomputable def slEquivProjTwo (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* projectiveSL n (ZMod 2) :=
  MulEquiv.ofBijective (proj n (ZMod 2))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [ker_proj, CFSG.LieType.SteinbergBR.BinaryLinear.scalars_eq_bot (Nat.card_zmod 2)]),
      proj_surjective n (ZMod 2)⟩

theorem normalizer_inf_le_of_list
    {Ω : Type} [Group Ω] [Finite Ω] {X S : Subgroup Ω}
    (hS : IsSylowTwoOf S X)
    (hl : (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ Nonempty (↥X ≃* ↥(StatedSL n (ZMod 2)))) ∨ IsAlt 6 ↥X ∨
      IsG2TwoDerived ↥X) :
    Subgroup.normalizer (S : Set Ω) ⊓ X ≤ S := by
  have hU : IsSylowTwoOf (S.subgroupOf X) ⊤ := (SBd8.isSylowTwoOf_iff_subgroupOf hS.1).mp hS
  have hN : Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) = S.subgroupOf X := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let U : Sylow 2 ↥X := hU.2.1.toSylow hS.2.2
    have hUc : (U : Subgroup ↥X) = S.subgroupOf X := rfl
    have key : ∀ P₀ : Sylow 2 ↥X, Subgroup.normalizer (P₀ : Set ↥X) = P₀ →
        Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) = S.subgroupOf X := fun P₀ hP₀ => by
      have := CFSG.LieType.SteinbergBR.OddSylow.normalizer_eq_of_one P₀ hP₀ U
      rwa [hUc] at this
    rcases hl with ⟨n, hn3, hn5, ⟨e⟩⟩ | hA6 | hG2
    ·
      let e' : ↥X ≃* projectiveSL n (ZMod 2) :=
        e.trans ((specialLinearGroupEquivStatedSL n (ZMod 2)).symm.trans (slEquivProjTwo n))
      obtain ⟨⟨P, hP⟩, -⟩ := CFSG.LieType.SteinbergBR.BinaryLinear.binary_linear_key (k := ZMod 2)
        (n := n) hn3 (Nat.card_zmod 2)
      obtain ⟨P₀, hP₀⟩ := CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv e' P hP
      exact key P₀ hP₀
    ·
      obtain ⟨e⟩ := hA6
      obtain ⟨P, hP⟩ := CFSG.LieType.SteinbergBR.SmallAlt.exists_selfNormalizing_six
      obtain ⟨P₀, hP₀⟩ := CFSG.LieType.SteinbergBR.OddSylow.exists_selfNormalizing_of_equiv e P hP
      exact key P₀ hP₀
    ·
      exact (SBd8.trioShape_U33 hG2 hU).1
  intro x hx
  have h1 : (⟨x, hx.2⟩ : ↥X) ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    (SBd8.mem_normalizer_subgroupOf_iff hS.1 ⟨x, hx.2⟩).mpr hx.1
  rw [hN] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end Sel

end SzN19

end CFSG.Quasithin

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.GorensteinWalter

namespace Gold14610

namespace Struct

variable {D : Type} [Group D]

theorem idx2Data_of_isL2FieldExtCat {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : F6.IsL2FieldExtCat p D) : Idx2Data D := by
  obtain ⟨hp, K, _, _, hK, ⟨e⟩⟩ := h
  have hpodd : Odd p := by rw [Nat.odd_iff]; omega
  have hp3 : 3 ≤ p := by omega
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hpodd, by norm_num, hK⟩
  have hK3 : 3 < Nat.card K := by rw [hK]; nlinarith
  have hLn : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hodd hK3
  have hLS : pGammaL2PSLRange K ≤ F6.PSigmaL2 K := le_sup_left
  have hσ2 : ∀ σ : K ≃+* K, σ ^ 2 = 1 := fun σ => by
    have := CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card K hp hK
    rw [← this]
    exact pow_card_eq_one'
  have hL2 : F6.IsL2 p 2 ↥((pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K)) := by
    refine ⟨⟨hp, by norm_num, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(Subgroup.subgroupOfEquivOfLe hLS).trans ((pGammaL2PSLRangeEquiv K).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K))⟩⟩
    · intro h; simp at h; nlinarith
    · intro h; simp at h; nlinarith
  refine Idx2Data.of_mulEquiv e ⟨(pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K), inferInstance,
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp8, hL2⟩))))), fun x => ?_,
    Or.inl (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 2 hL2).2⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  obtain ⟨n, hn, r, hr, hnr⟩ := Subgroup.mem_sup_of_normal_left.1 x.2
  obtain ⟨σ, rfl⟩ := hr
  rw [← hnr]
  have hr2 : (SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inr σ = 1 := by
    rw [← map_mul, ← sq, hσ2, map_one]
  have e2 : (n * SemidirectProduct.inr σ) * (n * SemidirectProduct.inr σ) =
      n * (SemidirectProduct.inr σ * n * (SemidirectProduct.inr σ)⁻¹) *
        ((SemidirectProduct.inr σ : PGammaL2 K) * SemidirectProduct.inr σ) := by group
  rw [sq, e2, hr2, mul_one]
  exact Subgroup.mul_mem _ hn (hLn.conj_mem n hn _)

end Struct

end Gold14610

end CFSG.Quasithin

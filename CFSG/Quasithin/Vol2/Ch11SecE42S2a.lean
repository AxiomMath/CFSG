module

public import CFSG.Quasithin.Vol2.Ch11SecE42A36
public import CFSG.Quasithin.Vol2.Ch11SecE42Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

private theorem eleven_le_of_mod_five {p : ℕ} (hp : p.Prime) (h5 : p % 5 = 1 ∨ p % 5 = 4) :
    11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | omega | (exfalso; norm_num at hp)

theorem sl2NegOne_mulVec {p : ℕ} [Fact p.Prime] (v : Fin 2 → ZMod p) :
    Matrix.mulVec ((A1c.sl2NegOne p : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) v = -v := by
  ext i
  fin_cases i <;> simp [A1c.sl2NegOne, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> rfl

theorem not_isQuasisimple_of_sl2pE {X : Type} [Group X] [Finite X] (hE : IsSL2pE X) :
    ¬ CFSG.IsQuasisimple X := by
  obtain ⟨p, hp, h5, -, hF, -, -, ψ, hψs, hψk, -⟩ := hE
  have : Fact p.Prime := ⟨hp⟩
  refine not_isQuasisimple_of_fitting hF fun htop => ?_
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  apply A1c.sl2NegOne_ne_one (p := p) hp2
  obtain ⟨x, hx⟩ := hψs (A1c.sl2NegOne p)
  have hxk : x ∈ ψ.ker := by
    rw [hψk, htop]
    exact Subgroup.mem_top x
  rw [← hx]
  exact hxk

variable {G : Type} [Group G] [Finite G]

theorem exists_sl2_map_of_sl2pE {K : Subgroup G} (hE : IsSL2pE (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (φ : ↥K →* SL(2, ZMod p)), 11 ≤ p ∧ Function.Surjective φ ∧
      (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K) ∧
      (∀ k : ↥K, φ k = A1c.sl2NegOne p → ∀ o : ↥K, (o : G) ∈ oTwoTwoPrime K →
        ((k * o * k⁻¹ * o : ↥K) : G) ∈ pCoreOf 2 K) := by
  obtain ⟨p, hp, h5, -, -, ⟨eE⟩, eF, ψ, hψs, hψk, hact⟩ := hE
  have : Fact p.Prime := ⟨hp⟩
  have h11 := eleven_le_of_mod_five hp h5
  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hX
  set mk : ↥K →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hmk
  have hFodd : Odd (Nat.card (CFSG.fittingSubgroup X)) := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    exact Odd.pow (hp.odd_of_ne_two (by omega))
  have hFO : CFSG.fittingSubgroup X = CFSG.oddCore X := by
    refine le_antisymm (le_sSup ⟨inferInstance, hFodd⟩) ?_
    have hn : ((CFSG.oddCore X).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψs
    have hodd : Odd (Nat.card ((CFSG.oddCore X).map ψ)) :=
      (SecD.odd_card_oddCore X).of_dvd_nat (Subgroup.card_map_dvd _ ψ)
    have h0 := eq_bot_of_normal_odd_sl2 (by omega) hn hodd
    rw [← hψk]
    exact (Subgroup.map_eq_bot_iff _).mp h0
  refine ⟨p, ⟨hp⟩, ψ.comp mk, h11, hψs.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · intro k
    rw [SecD.mem_oTwoTwoPrime_iff, ← hFO, ← hψk, MonoidHom.mem_ker]
    rfl
  · intro k hk o ho
    have hoF : mk o ∈ CFSG.fittingSubgroup X := by
      rw [hFO]
      exact (SecD.mem_oTwoTwoPrime_iff o).mp ho
    have h1 := hact (mk k) ⟨mk o, hoF⟩
    have hk' : ψ (mk k) = A1c.sl2NegOne p := hk
    rw [hk', sl2NegOne_mulVec, ofAdd_neg, ofAdd_toAdd, ← map_inv] at h1
    have h2 := congrArg Subtype.val (eF.injective h1)
    rw [MulAut.conjNormal_apply, Subgroup.coe_inv] at h2
    have h3 : mk (k * o * k⁻¹ * o) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, h2, inv_mul_cancel]
    have h4 : k * o * k⁻¹ * o ∈ CFSG.pCore 2 ↥K := by
      rwa [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    rw [← SecD.pCoreOf_subgroupOf] at h4
    exact h4

end CFSG.Quasithin.Vol2.Ch11.SecE

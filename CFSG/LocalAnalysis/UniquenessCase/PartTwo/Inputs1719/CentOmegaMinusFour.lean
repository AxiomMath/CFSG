module

public import CFSG.ClassicalGroups.Orthogonal.EichlerCentralizerScalar
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Quasithin CFSG.Open
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

theorem k_CentOmegaMinus4 :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (L : Subgroup (MulAut W)) (a : ℕ), NatOmegaMinus L ⊤ ⊥ 4 a →
        ∀ c : MulAut W, (∀ l ∈ L, c * l = l * c) → c ^ (2 ^ a - 1) = 1 := by
  intro W _ _ hW L a hN c hc
  classical
  obtain ⟨-, K, hKfld, hKfin, b, c₀, hKcard, hirr, π, hπ⟩ := hN
  letI : Field K := hKfld
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a) (by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard)
  let Γ : Subgroup
      (Matrix.GeneralLinearGroup (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus (4 / 2) K b c₀)
  obtain ⟨β, hβsurj, hβker, hβe⟩ :=
    (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro x y hxy
    have h1 : β (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : (x * y⁻¹ : ↥(⊤ : Subgroup W)) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp ((hβker (x * y⁻¹)).1 h1))
    exact mul_inv_eq_one.1 h2
  let bW : W ≃* Multiplicative
      (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩)
  have hbW : ∀ w : W, bW w = β ⟨w, Subgroup.mem_top w⟩ := by
    intro w
    rfl
  let Yfun : (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) →
      (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) := fun x =>
    Multiplicative.toAdd (bW (c (bW.symm (Multiplicative.ofAdd x))))
  let Y : (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) →+
      (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) :=
    AddMonoidHom.mk' Yfun (by
      intro x y
      simp only [Yfun]
      rw [← toAdd_mul]
      congr 1
      rw [ofAdd_add, map_mul, map_mul, map_mul])
  have hbase : ∀ u : W,
      Y (Multiplicative.toAdd (bW u)) = Multiplicative.toAdd (bW (c u)) := by
    intro u
    change Yfun (Multiplicative.toAdd (bW u)) = Multiplicative.toAdd (bW (c u))
    simp [Yfun]
  have hcomm : ∀ (γ : ↥Γ) (x : Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K),
      Y (Multiplicative.toAdd (natAct Γ γ (Multiplicative.ofAdd x))) =
        Multiplicative.toAdd (natAct Γ γ (Multiplicative.ofAdd (Y x))) := by
    intro γ x
    obtain ⟨u, hu⟩ := bW.surjective (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (bW u) := by rw [hu, toAdd_ofAdd]
    have h1 : natAct Γ γ (bW u) = bW (((π γ : ↥L) : MulAut W) u) := by
      rw [hbW, hbW]
      exact (hβe γ ⟨u, Subgroup.mem_top u⟩ (Subgroup.mem_top _)).symm
    have h2 : natAct Γ γ (bW (c u)) = bW (((π γ : ↥L) : MulAut W) (c u)) := by
      rw [hbW, hbW]
      exact (hβe γ ⟨c u, Subgroup.mem_top _⟩ (Subgroup.mem_top _)).symm
    have hcπ : c (((π γ : ↥L) : MulAut W) u) = ((π γ : ↥L) : MulAut W) (c u) := by
      have h := congrArg (fun g : MulAut W => g u) (hc ((π γ : ↥L) : MulAut W) (π γ).2)
      simpa [MulAut.mul_apply] using h
    rw [hx, hbase u, ofAdd_toAdd, ofAdd_toAdd, h1, h2, hbase (((π γ : ↥L) : MulAut W) u),
      hcπ]
  have hcomm_eichler : ∀ (u w x : Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K),
      Y (eichler (quadMinus (4 / 2) K b c₀) u w x) =
        eichler (quadMinus (4 / 2) K b c₀) u w (Y x) := by
    intro u w x
    obtain ⟨A, hA, hAapp⟩ :=
      exists_mem_statedOmega_quadMinus_eichler (m := 4 / 2) (b := b) (c := c₀)
        (by norm_num) hirr u w
    have h1 : natAct Γ ⟨A, hA⟩ (Multiplicative.ofAdd x) =
        Multiplicative.ofAdd (eichler (quadMinus (4 / 2) K b c₀) u w x) := by
      simp only [natAct, Subtype.coe_mk, toAdd_ofAdd, hAapp x]
    have h2 : natAct Γ ⟨A, hA⟩ (Multiplicative.ofAdd (Y x)) =
        Multiplicative.ofAdd (eichler (quadMinus (4 / 2) K b c₀) u w (Y x)) := by
      simp only [natAct, Subtype.coe_mk, toAdd_ofAdd, hAapp (Y x)]
    have h := hcomm ⟨A, hA⟩ x
    rw [h1, h2] at h
    simpa using h
  let P : HypPair (quadMinus (4 / 2) K b c₀) := minusPair K b c₀ (0 : Fin (4 / 2 - 1))
  have hPe : P.e = Pi.single (Sum.inl (0 : Fin (4 / 2 - 1))) 1 := rfl
  have hPf : P.f = Pi.single (Sum.inr (Sum.inl (0 : Fin (4 / 2 - 1)))) 1 := rfl
  have hw₀ : (Pi.single (Sum.inr (Sum.inr 0)) 1 :
      Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) ∈ P.perp :=
    single_inr_inr_mem_perp (i0 := 0) P hPe hPf 0
  have hQw₀ : quadMinus (4 / 2) K b c₀ (Pi.single (Sum.inr (Sum.inr 0)) 1) ≠ 0 := by
    rw [quadMinus_single_u]
    exact one_ne_zero
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_commute_eichler
    (Q := quadMinus (4 / 2) K b c₀)
    (nondegenerate_polarBilin_quadMinus_of_finite (4 / 2) K hirr) P
    ⟨_, hw₀, hQw₀⟩ Y
    (fun w _ x => hcomm_eichler P.e w x) (fun w _ x => hcomm_eichler P.f w x)
  have hYinj : Function.Injective Y := by
    intro x y hxy
    change Multiplicative.toAdd (bW (c (bW.symm (Multiplicative.ofAdd x)))) =
      Multiplicative.toAdd (bW (c (bW.symm (Multiplicative.ofAdd y)))) at hxy
    have h1 : bW (c (bW.symm (Multiplicative.ofAdd x))) =
        bW (c (bW.symm (Multiplicative.ofAdd y))) :=
      Multiplicative.toAdd.injective hxy
    have h2 := bW.injective h1
    have h3 := c.injective h2
    have h4 := bW.symm.injective h3
    exact Multiplicative.ofAdd.injective h4
  have hx₀ : (Pi.single (Sum.inl (0 : Fin (4 / 2 - 1))) 1 :
      Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl (0 : Fin (4 / 2 - 1)))
    simp at this
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    have hx : Y (Pi.single (Sum.inl (0 : Fin (4 / 2 - 1))) 1 :
        Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) = 0 := by
      rw [hμ, hμ0, zero_smul]
    have hzero : (Pi.single (Sum.inl (0 : Fin (4 / 2 - 1))) 1 :
        Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) = 0 :=
      hYinj (by rw [hx, map_zero])
    exact hx₀ hzero
  have hμpow : μ ^ (2 ^ a - 1) = 1 := by
    have hcard : Fintype.card K = 2 ^ a := by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard
    have h := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [hcard] at h
  have hbase_c : ∀ u : W,
      bW (c u) = Multiplicative.ofAdd (μ • Multiplicative.toAdd (bW u)) := by
    intro u
    have h := hμ (Multiplicative.toAdd (bW u))
    rw [hbase u] at h
    rw [← h, ofAdd_toAdd]
  have hiter : ∀ (k : ℕ) (u : W),
      bW ((c ^ k) u) = Multiplicative.ofAdd ((μ ^ k) • Multiplicative.toAdd (bW u)) := by
    intro k
    induction k with
    | zero =>
        intro u
        simp
    | succ k ih =>
        intro u
        rw [pow_succ', MulAut.mul_apply, hbase_c ((c ^ k) u), ih u, toAdd_ofAdd,
          smul_smul, pow_succ']
  have hck : c ^ (2 ^ a - 1) = 1 := by
    ext u
    have h := hiter (2 ^ a - 1) u
    rw [hμpow, one_smul, ofAdd_toAdd] at h
    simpa using bW.injective h
  exact hck

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

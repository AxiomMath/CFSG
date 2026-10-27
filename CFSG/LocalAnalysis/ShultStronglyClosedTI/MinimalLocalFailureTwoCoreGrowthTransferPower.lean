module

public import Mathlib.GroupTheory.Transfer

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

theorem transfer_eq_quotient_power_of_power_fusion
    (S : Subgroup G) (N : Subgroup S) [N.Normal]
    [IsMulCommutative (S ⧸ N)] (x : S)
    (hfusion : ∀ (k : ℕ) (g : G) (hmem : g⁻¹ * (x : G) ^ k * g ∈ S),
      (QuotientGroup.mk' N) ⟨g⁻¹ * (x : G) ^ k * g, hmem⟩ =
        (QuotientGroup.mk' N) (x ^ k)) :
    (QuotientGroup.mk' N).transfer (x : G) =
      ((QuotientGroup.mk' N) x) ^ S.index := by
  classical
  let : Fintype (Quotient (MulAction.orbitRel
      (Subgroup.zpowers (x : G)) (G ⧸ S))) := Fintype.ofFinite _
  rw [Subgroup.index_eq_sum_minimalPeriod S (x : G),
    ← Finset.prod_pow_eq_pow_sum,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  apply Finset.prod_congr rfl
  intro q _
  exact (hfusion _ q.out.out _).trans ((QuotientGroup.mk' N).map_pow x _)

theorem power_fusion_transfer_detection
    (p : ℕ) (hp : p.Prime) (S : Sylow p G)
    (N : Subgroup (S : Subgroup G)) [N.Normal]
    [IsMulCommutative ((S : Subgroup G) ⧸ N)]
    (x : (S : Subgroup G)) (hx : x ∉ N)
    (hfusion : ∀ (k : ℕ) (g : G)
      (hmem : g⁻¹ * (x : G) ^ k * g ∈ (S : Subgroup G)),
      (QuotientGroup.mk' N) ⟨g⁻¹ * (x : G) ^ k * g, hmem⟩ =
        (QuotientGroup.mk' N) (x ^ k)) :
    let T := (QuotientGroup.mk' N).transfer
    T (x : G) = ((QuotientGroup.mk' N) x) ^ (S : Subgroup G).index ∧
      T (x : G) ≠ 1 ∧
      T.ker.Normal ∧
      (x : G) ∉ T.ker ∧
      Nontrivial (G ⧸ T.ker) ∧
      Finite (G ⧸ T.ker) ∧
      IsMulCommutative (G ⧸ T.ker) ∧
      IsPGroup p (G ⧸ T.ker) := by
  let : Fact p.Prime := ⟨hp⟩
  let Q := (S : Subgroup G) ⧸ N
  let f : (S : Subgroup G) →* Q := QuotientGroup.mk' N
  let T : G →* Q := f.transfer
  have hvalue : T (x : G) = (f x) ^ (S : Subgroup G).index :=
    transfer_eq_quotient_power_of_power_fusion (S : Subgroup G) N x hfusion
  have hnontrivial : T (x : G) ≠ 1 := by
    intro hzero
    have hpow : (f x) ^ (S : Subgroup G).index = 1 := hvalue.symm.trans hzero
    have hcard : (f x) ^ Nat.card (S : Subgroup G) = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    have hfx : f x = 1 :=
      (pow_eq_one_iff_of_coprime S.card_coprime_index).mp ⟨hcard, hpow⟩
    exact hx ((QuotientGroup.eq_one_iff x).mp hfx)
  have hxnker : (x : G) ∉ T.ker := hnontrivial
  have hquotient : Nontrivial (G ⧸ T.ker) := by
    apply nontrivial_of_ne (QuotientGroup.mk (x : G) : G ⧸ T.ker) 1
    intro hzero
    exact hxnker ((QuotientGroup.eq_one_iff (x : G)).mp hzero)
  let e : G ⧸ T.ker ≃* T.range := QuotientGroup.quotientKerEquivRange T
  have hcomm : IsMulCommutative (G ⧸ T.ker) :=
    ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hquotp : IsPGroup p (G ⧸ T.ker) :=
    ((S.isPGroup'.to_quotient N).to_subgroup T.range).of_equiv e.symm
  exact ⟨hvalue, hnontrivial, inferInstance, hxnker, hquotient,
    inferInstance, hcomm, hquotp⟩

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth

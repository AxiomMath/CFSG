module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.Background.HL3WrMParam

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace L32

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Quasithin.H.L3Wr

theorem tensorNatL32_realizesMod {V : Type*} [CommGroup V] {K : Subgroup (MulAut V)}
    (h : TensorNatL32 K) : (tensorPairModel SL32 SL32).RealizesMod K := h

theorem sup_zpowers_le_normalizer {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}
    {a : MulAut W} (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (ha2 : a ^ 2 = 1) :
    K ⊔ Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  refine sup_le Subgroup.le_normalizer ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨haN h, fun hah => ?_⟩
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have e : a * (a * h * a⁻¹) * a⁻¹ = h := by
    have e1 : a * (a * h * a⁻¹) * a⁻¹ = (a * a) * h * (a * a)⁻¹ := by group
    rw [e1, haa, inv_one, one_mul, mul_one]
  rw [← e]
  exact haN _ hah

theorem false_of_tensorNatL32 {W : Type} [CommGroup W] [Finite W] {K : Subgroup (MulAut W)}
    {a : MulAut W} (hT : TensorNatL32 K) (haN : ∀ k ∈ K, a * k * a⁻¹ ∈ K) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) (hrk : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) : False := by
  have h3 : 3 ≤ E3.mParam (K ⊔ Subgroup.zpowers a) :=
    H44_L3Wreath_mParam (tensorNatL32_realizesMod hT) (sup_zpowers_le_normalizer haN ha2)
  have h2 : E3.mParam (K ⊔ Subgroup.zpowers a) ≤ 2 :=
    mParam_le_two (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) ha1 ha2 hrk
  omega

theorem twoTensor_holds : TwoTensor := by
  intro W _ _ K L₁ L₂ S a hctx hmod
  exact false_of_tensorNatL32 hmod.2 hctx.aN hctx.a1 hctx.a2 hctx.rk

end L32

end S153G93D

end CFSG.Quasithin

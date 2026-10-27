module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem set_mul_comm_of_subgroup {A B X : Subgroup G}
    (h : (X : Set G) = (A : Set G) * (B : Set G)) : (X : Set G) = (B : Set G) * (A : Set G) := by
  have hA : A ≤ X := fun a ha => by
    rw [← SetLike.mem_coe, h]
    exact ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hB : B ≤ X := fun b hb => by
    rw [← SetLike.mem_coe, h]
    exact ⟨1, A.one_mem, b, hb, one_mul b⟩
  ext x
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ (X : Set G) := X.inv_mem hx
    rw [h] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := hx'
    refine ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, ?_⟩
    have hab' : a * b = x⁻¹ := hab
    have hx2 : x = (a * b)⁻¹ := by rw [hab', inv_inv]
    rw [hx2, mul_inv_rev]
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact X.mul_mem (hB hb) (hA ha)

theorem r16_10_2_of_out10 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D)
    (h45 : W3Lem45_2 G)
    (hout : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D V₀ V L hV →
      Out10 D V₀ V hV) :
    R16_10_2 D := by
  intro V₀ V L hV hc X S hXM hX hS hF
  have h : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hH := s16c1610_hyp6H D hx h61 h127 h1114 h
  obtain ⟨hk, hno⟩ := hout V₀ V L hV hc
  have hkr : (D.k : ℕ∞) < rMV D.M V := Sixteen24.k_lt_rMV_of_hyp125 D hSg h1219 hx h61 h
  have hconcl : Concl613 D.k V :=
    concl613_of_no_calO1 h45 hH (TwelveShort.one_le_k D) hkr hk hno
  exact set_mul_comm_of_subgroup ((hconcl X S hX hS).1 hF)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

theorem isPGroup_zpowers_of_pow_three {X : Type*} [Group X] {g : X} (hg : g ^ 3 = 1) :
    IsPGroup 3 (zpowers g) := by
  intro h
  refine ⟨1, ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h.2
  apply Subtype.ext
  rw [pow_one, SubgroupClass.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [hg]

theorem model_exists_centralizer_two
    {k₁ k₂ : GM}
    (h1 : k₁ ^ 3 = 1) (h2 : k₂ ^ 3 = 1) (h12 : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ zpowers zG) :
    ∃ x : GM, x ^ 3 = 1 ∧ x ∉ zpowers zG ∧ x * k₁ = k₁ * x ∧ x * k₂ = k₂ * x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hzN : (zpowers zG).Normal := CFSG.RankThree.PartTwo.Sec13.ON134.model_zpowers_normal
  set V : Subgroup GM := zpowers zG ⊔ zpowers k₁ with hV
  have hV3 : IsPGroup 3 V :=
    IsPGroup.to_sup_of_normal_left (isPGroup_zpowers_of_pow_three relG.xcube)
      (isPGroup_zpowers_of_pow_three h1)
  have hk₂V : zpowers k₂ ≤ normalizer (V : Set GM) := by
    rw [zpowers_le]
    refine CFSG.RankThree.PartTwo.Sec14.Item148HJ.mem_normalizer_of_conj_mem fun u hu => ?_
    have hle : V ≤ V.comap (MulAut.conj k₂).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_comap]
        show k₂ * zG * k₂⁻¹ ∈ V
        rw [← zG_central k₂, mul_inv_cancel_right]
        exact mem_sup_left (mem_zpowers zG)
      · rw [zpowers_le, mem_comap]
        show k₂ * k₁ * k₂⁻¹ ∈ V
        have hc : k₂ * k₁ * k₂⁻¹ = (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)⁻¹ * k₁ := by group
        rw [hc]
        exact mul_mem (mem_sup_left (inv_mem h12)) (mem_sup_right (mem_zpowers k₁))
    exact hle hu
  have hU3 : IsPGroup 3 (V ⊔ zpowers k₂ : Subgroup GM) :=
    IsPGroup.to_sup_of_normal_left' hV3 (isPGroup_zpowers_of_pow_three h2) hk₂V
  obtain ⟨P, hP⟩ := hU3.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  set x₀ : GM := MulAut.conj g zG with hx₀
  set v : Fin 4 → GM := fun i => MulAut.conj g (xG i) with hv
  have R : ThreeQRel x₀ v omegaZ := relG_conj g
  have hx₀z : x₀ = zG := by
    rw [hx₀, MulAut.conj_apply, ← zG_central g, mul_inv_cancel_right]
  have hk₁P : k₁ ∈ threeQ x₀ v := by
    rw [← hg]
    exact hP (mem_sup_left (mem_sup_right (mem_zpowers k₁)))
  have hk₂P : k₂ ∈ threeQ x₀ v := by
    rw [← hg]
    exact hP (mem_sup_right (mem_zpowers k₂))
  set q₁ : ↥(threeQ x₀ v) := ⟨k₁, hk₁P⟩ with hq₁
  set q₂ : ↥(threeQ x₀ v) := ⟨k₂, hk₂P⟩ with hq₂
  have := R.finite
  have hidx : ∀ q : ↥(threeQ x₀ v), (centralizer ({q} : Set ↥(threeQ x₀ v))).index ≤ 3 := by
    intro q
    by_cases hq : (q : GM) ∈ zpowers x₀
    · have htop : centralizer ({q} : Set ↥(threeQ x₀ v)) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        rw [mem_centralizer_singleton_iff]
        exact (mem_center_iff.mp ((R.mem_center_iff q).mpr hq)) y
      rw [htop, index_top]
      norm_num
    · have h81 := R.card_centralizer q hq
      have hci := (centralizer ({q} : Set ↥(threeQ x₀ v))).card_mul_index
      rw [h81, R.card_threeQ_type] at hci
      omega
  have hidx2 : (centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
      centralizer ({q₂} : Set ↥(threeQ x₀ v))).index ≤ 9 :=
    (index_inf_le).trans (Nat.mul_le_mul (hidx q₁) (hidx q₂))
  have hcard : 27 ≤ Nat.card ↥(centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
      centralizer ({q₂} : Set ↥(threeQ x₀ v))) := by
    have hm := (centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
      centralizer ({q₂} : Set ↥(threeQ x₀ v))).card_mul_index
    rw [R.card_threeQ_type] at hm
    have hpos : 0 < (centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
        centralizer ({q₂} : Set ↥(threeQ x₀ v))).index :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith
  obtain ⟨b, hb, hbz⟩ : ∃ b ∈ centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
      centralizer ({q₂} : Set ↥(threeQ x₀ v)), b ∉ center ↥(threeQ x₀ v) := by
    by_contra hall
    push Not at hall
    have hle : centralizer ({q₁} : Set ↥(threeQ x₀ v)) ⊓
        centralizer ({q₂} : Set ↥(threeQ x₀ v)) ≤ center ↥(threeQ x₀ v) := fun b hb => hall b hb
    have := card_le_of_le hle
    rw [R.card_center] at this
    omega
  refine ⟨(b : GM), R.pow_three_of_mem b.2, ?_, ?_, ?_⟩
  · intro hbz'
    apply hbz
    have hzz : zpowers x₀ = zpowers zG := by rw [hx₀z]
    rw [R.mem_center_iff, hzz]
    exact hbz'
  · have h := mem_centralizer_singleton_iff.mp (mem_inf.mp hb).1
    exact congrArg Subtype.val h
  · have h := mem_centralizer_singleton_iff.mp (mem_inf.mp hb).2
    exact congrArg Subtype.val h

theorem exists_centralizer_two
    {X : Type} [Group X]
    (ψ : X ≃* GM) {k₁ k₂ : X} (h1 : k₁ ^ 3 = 1) (h2 : k₂ ^ 3 = 1)
    (h12 : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ center X) :
    ∃ x : X, x ^ 3 = 1 ∧ x ∉ center X ∧ x * k₁ = k₁ * x ∧ x * k₂ = k₂ * x := by
  have h12' : ψ k₁ * ψ k₂ * (ψ k₁)⁻¹ * (ψ k₂)⁻¹ ∈ zpowers zG := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).mp h12
  obtain ⟨y, hy3, hyz, hy1, hy2⟩ := model_exists_centralizer_two
    (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one]) h12'
  refine ⟨ψ.symm y, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hy3, map_one]
  · intro h
    apply hyz
    have := (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).mp h
    rwa [MulEquiv.apply_symm_apply] at this
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy1]
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy2]

end CFSG.RankThree.PartTwo.Sec4.Ronan148V

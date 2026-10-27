module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.Harris.R1.QbetaData
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.LieType.BorelTits

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem zg_ne_one : g * z * g⁻¹ ≠ 1 := by
  intro h1
  apply h.hz1
  have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
  rw [this, h1]
  group

theorem cent_V_of_three {T : G} (hTV : T ∈ Subgroup.normalizer ((Z ⊔ conjSub g Z : Subgroup G) : Set G))
    (hTZ : ∀ s ∈ Z, T * s = s * T) (hT3 : T ^ 3 = 1) :
    ∀ v ∈ Z ⊔ conjSub g Z, T * v * T⁻¹ = v := by
  set z' := g * z * g⁻¹ with hz'
  have hz2 : z * z = 1 := h.z_sq
  have hzT : T * z * T⁻¹ = z := by
    rw [hTZ z h.hzZ]; group
  have hT3' : T * T * T = 1 := by
    calc T * T * T = T ^ 3 := (pow_three' T).symm
      _ = 1 := hT3
  have hz'V : z' ∈ Z ⊔ conjSub g Z := Subgroup.mem_sup_right h.zg_mem
  have hw : T * z' * T⁻¹ ∈ Z ⊔ conjSub g Z := (Subgroup.mem_normalizer_iff.mp hTV z').mp hz'V
  have hz' : T * z' * T⁻¹ = z' := by
    rcases h.V_cases hw with h1 | h1 | h1 | h1
    · exfalso
      refine h.zg_ne_one ?_
      show z' = 1
      have : z' = T⁻¹ * (T * z' * T⁻¹) * T := by group
      rw [this, h1]; group
    · exfalso
      have h2 : z' = z := by
        have : z' = T⁻¹ * (T * z' * T⁻¹) * T := by group
        rw [this, h1]
        calc T⁻¹ * z * T = T⁻¹ * (z * T) := by rw [mul_assoc]
          _ = T⁻¹ * (T * z) := by rw [← hTZ z h.hzZ]
          _ = z := by group
      have hzg : z ∈ Z ⊓ conjSub g Z := ⟨h.hzZ, by rw [← h2]; exact h.zg_mem⟩
      rw [h.hZZ, Subgroup.mem_bot] at hzg
      exact h.hz1 hzg
    · exact h1
    · exfalso
      have e1 : T * (z * z') * T⁻¹ = z' := by
        rw [show T * (z * z') * T⁻¹ = (T * z * T⁻¹) * (T * z' * T⁻¹) by group, hzT, h1,
          ← mul_assoc, hz2, one_mul]
      have e2 : T * (T * z' * T⁻¹) * T⁻¹ = z' := by rw [h1]; exact e1
      have e3 : z * z' = z' := by
        calc z * z' = T * z' * T⁻¹ := h1.symm
          _ = T * (T * (T * z' * T⁻¹) * T⁻¹) * T⁻¹ := by rw [e2]
          _ = (T * T * T) * z' * (T * T * T)⁻¹ := by group
          _ = z' := by rw [hT3']; group
      exact h.hz1 (mul_eq_right.mp e3)
  intro v hv
  rcases h.V_cases hv with h1 | h1 | h1 | h1
  · rw [h1]; group
  · rw [h1]; exact hzT
  · rw [h1]; exact hz'
  · rw [h1]
    calc T * (z * z') * T⁻¹ = (T * z * T⁻¹) * (T * z' * T⁻¹) := by group
      _ = z * z' := by rw [hzT, hz']

end QD

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem cent_le_pCore (C : FamCtx K1 L2 S Zs (Fin 5)) {c : G} (hc : c ∈ L2 ⊔ S)
    (hcV : ∀ v ∈ conjClosure Zs L2, v * c = c * v) : c ∈ pCoreOf 2 (L2 ⊔ S) := by
  have hS3 : S.relIndex (L2 ⊔ S) = 3 := F112J2.relIndex_L2S C.hR C.h.s3
  have hQ2 : (pCoreOf 2 (L2 ⊔ S)).relIndex S = 2 :=
    F112W.relIndex_pCoreOf_T C.amalgamHypV C.isNaturalS3
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := C.pCore_le_S
  have hQP : pCoreOf 2 (L2 ⊔ S) ≤ L2 ⊔ S := hQS.trans le_sup_right
  have hQ6 : (pCoreOf 2 (L2 ⊔ S)).relIndex (L2 ⊔ S) = 6 := by
    have := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (L2 ⊔ S)) S (L2 ⊔ S) hQS le_sup_right
    rw [hQ2, hS3] at this
    omega
  set A : Subgroup G := (L2 ⊔ S) ⊓ Subgroup.centralizer (conjClosure Zs L2 : Set G) with hA
  have hA6 : A.relIndex (L2 ⊔ S) = 6 := C.isNaturalS3.index_eq
  have hQA : pCoreOf 2 (L2 ⊔ S) ≤ A := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hQP hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (C.mem_pCore_iff.mp hx).2 v hv
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (L2 ⊔ S)) A (L2 ⊔ S) hQA inf_le_left
  rw [hQ6, hA6] at hmul
  have h1 : (pCoreOf 2 (L2 ⊔ S)).relIndex A = 1 := by omega
  exact (Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_inf.mpr ⟨hc, by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hcV v hv⟩)

end CFSG.Quasithin.Background.Harris.R1

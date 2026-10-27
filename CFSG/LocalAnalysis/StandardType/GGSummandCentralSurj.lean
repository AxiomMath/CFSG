module

public import CFSG.LocalAnalysis.StandardType.GGSummandStructKernel

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

private theorem exists_mul_of_mem_sup_of_le_centralizer {X : Type} [Group X]
    {T₁ T₂ : Subgroup X} (hT₂ : T₂ ≤ Subgroup.centralizer (T₁ : Set X)) {x : X}
    (hx : x ∈ T₁ ⊔ T₂) : ∃ a ∈ T₁, ∃ b ∈ T₂, x = a * b := by
  have hcomm : ∀ a ∈ T₁, ∀ t ∈ T₂, a * t = t * a := fun a ha t ht =>
    Subgroup.mem_centralizer_iff.mp (hT₂ ht) a ha
  let B : Subgroup X :=
    { carrier := {y | ∃ a ∈ T₁, ∃ b ∈ T₂, y = a * b}
      mul_mem' := by
        rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, T₁.mul_mem ha₁ ha₂, b₁ * b₂, T₂.mul_mem hb₁ hb₂, ?_⟩
        have h := hcomm a₂ ha₂ b₁ hb₁
        calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
          _ = a₁ * (a₂ * b₁) * b₂ := by rw [h]
          _ = a₁ * a₂ * (b₁ * b₂) := by group
      one_mem' := ⟨1, T₁.one_mem, 1, T₂.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, T₁.inv_mem ha, b⁻¹, T₂.inv_mem hb, ?_⟩
        have h := hcomm a ha b hb
        rw [h, mul_inv_rev] }
  have hle : T₁ ⊔ T₂ ≤ B := sup_le
    (fun t ht => ⟨t, ht, 1, T₂.one_mem, (mul_one t).symm⟩)
    (fun t ht => ⟨1, T₁.one_mem, t, ht, (one_mul t).symm⟩)
  exact hle hx

theorem ggSum_exists_central_surj {p : ℕ} {Q : Subgroup X} {𝒞 : Set (Subgroup X)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)
    {S : Subgroup X} (hS𝒞 : S ∈ 𝒞) [(Q.subgroupOf S).Normal] :
    ∃ g : ↥S ⧸ Q.subgroupOf S →* ↥(ggSumImg V E K S), Function.Surjective g ∧
      g.ker ≤ Subgroup.center (↥S ⧸ Q.subgroupOf S) ∧
      ∀ (s : X) (hs : s ∈ S) (hsH : s ∈ E ⊔ (K ⊓ V)),
        ((g (QuotientGroup.mk ⟨s, hs⟩) : ↥(ggSumImg V E K S)) : GGHypQuot (ggSumT V E K)) =
          ggSumRho V E K ⟨s, hsH⟩ := by
  obtain ⟨hSKV, hQS, -⟩ := hS.2.2 S hS𝒞
  have hSH : S ≤ E ⊔ (K ⊓ V) := hSKV.trans le_sup_right
  let ψ : ↥S →* ↥(ggSumImg V E K S) :=
    ((ggSumRho V E K).comp (Subgroup.inclusion hSH)).codRestrict (ggSumImg V E K S)
      (fun x => Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hSH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hpsi_val : ∀ x : ↥S,
      ((ψ x : ↥(ggSumImg V E K S)) : GGHypQuot (ggSumT V E K)) =
        ggSumRho V E K (Subgroup.inclusion hSH x) := fun x => rfl
  have hpsi_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨yH, hyS, hyy⟩ := Subgroup.mem_map.mp
      (show (y : GGHypQuot (ggSumT V E K)) ∈
        (S.subgroupOf (E ⊔ (K ⊓ V))).map (ggSumRho V E K) from y.2)
    refine ⟨⟨(yH : X), Subgroup.mem_subgroupOf.mp hyS⟩, ?_⟩
    apply Subtype.ext
    rw [hpsi_val ⟨(yH : X), Subgroup.mem_subgroupOf.mp hyS⟩]
    rw [show Subgroup.inclusion hSH ⟨(yH : X), Subgroup.mem_subgroupOf.mp hyS⟩ = yH
      from Subtype.ext rfl]
    exact hyy
  have hQ_le_ker : Q.subgroupOf S ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    rw [hpsi_val x]
    have hxQ : (x : X) ∈ Q := Subgroup.mem_subgroupOf.mp hx
    exact (ggSum_ker_rho V E K hp hp2 hE hEV hEK hS
      (Subgroup.inclusion hSH x)).mpr (Subgroup.mem_sup_left hxQ)
  refine ⟨QuotientGroup.lift (Q.subgroupOf S) ψ hQ_le_ker, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hpsi_surj y
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    revert hx
    refine QuotientGroup.induction_on x fun s hx => ?_
    refine QuotientGroup.induction_on y fun t => ?_
    rw [QuotientGroup.lift_mk] at hx
    have hsρ : ggSumRho V E K (Subgroup.inclusion hSH s) = 1 := by
      rw [← hpsi_val s, hx]; rfl
    have hsQU : (s : X) ∈ Q ⊔ ggRCSU V E K :=
      (ggSum_ker_rho V E K hp hp2 hE hEV hEK hS
        (Subgroup.inclusion hSH s)).mp hsρ
    have hUQ : ggRCSU V E K ≤ Subgroup.centralizer (Q : Set X) :=
      (show ggRCSU V E K ≤ Subgroup.centralizer (K : Set X) from inf_le_right).trans
        (Subgroup.centralizer_le (fun x hx => (hSKV (hQS hx)).1))
    obtain ⟨q, hqQ, u, huU, hsu⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (T₁ := Q) (T₂ := ggRCSU V E K) hUQ hsQU
    have hqS : q ∈ S := hQS hqQ
    have huS : u ∈ S := by
      have hu_eq : u = q⁻¹ * (s : X) := by rw [hsu]; group
      rw [hu_eq]
      exact S.mul_mem (S.inv_mem hqS) s.2
    let uS : ↥S := ⟨u, huS⟩
    have hsq : s = (⟨q, hqS⟩ : ↥S) * uS := Subtype.ext hsu
    have hmk : (QuotientGroup.mk s : ↥S ⧸ Q.subgroupOf S) = QuotientGroup.mk uS := by
      have hq1 : (QuotientGroup.mk (⟨q, hqS⟩ : ↥S) : ↥S ⧸ Q.subgroupOf S) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hqQ
      calc QuotientGroup.mk s = QuotientGroup.mk ((⟨q, hqS⟩ : ↥S) * uS) := by rw [hsq]
        _ = QuotientGroup.mk (⟨q, hqS⟩ : ↥S) * QuotientGroup.mk uS := rfl
        _ = (1 : ↥S ⧸ Q.subgroupOf S) * QuotientGroup.mk uS := by rw [hq1]
        _ = QuotientGroup.mk uS := one_mul _
    have htu : (t : X) * u = u * (t : X) :=
      Subgroup.mem_centralizer_iff.mp
        ((show ggRCSU V E K ≤ Subgroup.centralizer (K : Set X) from inf_le_right) huU)
        (t : X) (hSKV t.2).1
    have hcomm_quot : (QuotientGroup.mk t : ↥S ⧸ Q.subgroupOf S) * QuotientGroup.mk uS =
        QuotientGroup.mk uS * QuotientGroup.mk t := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simpa using htu
    rw [hmk]
    exact hcomm_quot
  · intro s hs hsH
    rw [QuotientGroup.lift_mk]
    exact (hpsi_val ⟨s, hs⟩).trans (congrArg (ggSumRho V E K) (Subtype.ext rfl))

end Config

end CFSG.StandardType

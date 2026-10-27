module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RootAutomorphismLayerKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernelBasic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open SuzukiModel SuzukiLayerKernel

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiU_layer_kernel
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (γ : MulAut (suzukiGroup a K)) (hγU : (suzukiU a K).map γ.toMonoidHom = suzukiU a K)
    (hγZ : ∀ v ∈ suzukiZ0 a K, γ v = v)
    (hγUZ : ∀ x ∈ suzukiU a K, x⁻¹ * γ x ∈ suzukiZ0 a K) :
    ∃ b ∈ suzukiU a K, γ = MulAut.conj b := by
  have h := suzukiPointAction_suzukiGroup hK
  have : FaithfulSMul (suzukiGroup a K) (suzukiOmegaSub hK) := faithfulSMul_suzukiOmegaSub ha hK
  have : MulAction.IsMultiplyPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) 2 :=
    h.isMultiplyPretransitive
  have : MulAction.IsPretransitive (suzukiGroup a K) (suzukiOmegaSub hK) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Finite (suzukiOmegaSub hK) := Subtype.finite
  set P : Sylow 2 (suzukiGroup a K) :=
    (suzukiU_isPGroup_index hK).1.toSylow (suzukiU_isPGroup_index hK).2 with hP
  have : ((suzukiZ0 a K).subgroupOf (P : Subgroup (suzukiGroup a K))).Characteristic :=
    suzukiZ0_characteristic hK
  have : ((suzukiZ0 a K).subgroupOf (suzukiU a K)).Normal :=
    @Subgroup.normal_of_characteristic _ _ _ (suzukiZ0_characteristic hK)
  have hΩ : 3 ≤ Nat.card (suzukiOmegaSub hK) := by
    rw [h.card_eq]
    have : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
    nlinarith
  have hPξ : (P : Subgroup (suzukiGroup a K)) ≤ MulAction.stabilizer (suzukiGroup a K)
      (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK) :=
    h.le_stabilizer_left
  refine regular_root_automorphism_layer_kernel hΩ h.ne P hPξ
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPξ).2 h.stabilizer_le_normalizer)
    (fun ω ω' h1 h2 => (h.regular ω ω' h1 h2).exists) (suzukiZ0 a K) suzukiZ0_le_suzukiU
    (suzuki_unipotent_structure hK).2.2.2.2.2.1 (suzukiU_quotient_comm hK) (Or.inr ⟨?_, ?_⟩)
    γ hγU hγZ hγUZ
  · intro t ht hfaith
    rw [h.stabilizer_inf_stabilizer] at ht
    exact suzukiT_faithful_quotient hK ht hfaith
  · intro ℓ hℓ
    rw [h.stabilizer_inf_stabilizer] at hℓ
    exact suzuki_equivariant_hom_trivial ha hK ℓ hℓ

theorem suzuki_rank_one_Sylow_layer_kernel
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (Q : Sylow 2 (suzukiGroup a K)) (V : Subgroup (suzukiGroup a K))
    (hV : V = (CFSG.omega₁ (G := (Q : Subgroup (suzukiGroup a K))) (p := 2)).map
      (Q : Subgroup (suzukiGroup a K)).subtype)
    (γ : MulAut (suzukiGroup a K))
    (hγQ : (Q : Subgroup (suzukiGroup a K)).map γ.toMonoidHom = Q)
    (hγV : ∀ v ∈ V, γ v = v) (hγQV : ∀ x ∈ (Q : Subgroup (suzukiGroup a K)), x⁻¹ * γ x ∈ V) :
    ∃ b ∈ (Q : Subgroup (suzukiGroup a K)), γ = MulAut.conj b := by
  set P : Sylow 2 (suzukiGroup a K) :=
    (suzukiU_isPGroup_index hK).1.toSylow (suzukiU_isPGroup_index hK).2 with hP
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P Q
  have hQ : ((g • P : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) =
      (suzukiU a K).map (MulAut.conj g).toMonoidHom := coe_smul_sylow' g P
  have hVZ : V = (suzukiZ0 a K).map (MulAut.conj g).toMonoidHom := by
    rw [hV, map_omega₁_subtype, ← map_omega₁_suzukiU hK, map_omega₁_subtype,
      MonoidHom.map_closure]
    congr 1
    ext x
    rw [hQ, Set.mem_ofPred_eq, Subgroup.mem_map_equiv]
    constructor
    · rintro ⟨hx, hx2⟩
      refine ⟨(MulAut.conj g).symm x, ⟨hx, ?_⟩, by simp [mul_assoc]⟩
      rw [← map_pow, hx2, map_one]
    · rintro ⟨y, ⟨hy, hy2⟩, rfl⟩
      refine ⟨by simpa [mul_assoc] using hy, ?_⟩
      rw [← map_pow, hy2, map_one]
  set γ₀ := (MulAut.conj g)⁻¹ * γ * MulAut.conj g with hγ₀
  have hγ₀_apply : ∀ x, γ₀ x = g⁻¹ * γ (g * x * g⁻¹) * g := fun x => by
    simp [hγ₀, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hmemQ : ∀ x, x ∈ suzukiU a K ↔ g * x * g⁻¹ ∈
      ((g • P : Sylow 2 (suzukiGroup a K)) : Subgroup (suzukiGroup a K)) := fun x => by
    rw [hQ, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply, mul_assoc]
  have hmemV : ∀ x, x ∈ suzukiZ0 a K ↔ g * x * g⁻¹ ∈ V := fun x => by
    rw [hVZ, Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply, mul_assoc]
  have hU : (suzukiU a K).map γ₀.toMonoidHom = suzukiU a K := by
    have e : γ₀.toMonoidHom = ((MulAut.conj g)⁻¹).toMonoidHom.comp
        (γ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) := rfl
    have e' : ((MulAut.conj g)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (suzukiGroup a K) := MonoidHom.ext fun x => by simp [mul_assoc]
    rw [e, ← Subgroup.map_map, ← Subgroup.map_map, ← hQ, hγQ, hQ, Subgroup.map_map, e',
      Subgroup.map_id]
  have hZ : ∀ v ∈ suzukiZ0 a K, γ₀ v = v := by
    intro v hv
    rw [hγ₀_apply, hγV _ ((hmemV v).1 hv)]
    group
  have hUZ : ∀ x ∈ suzukiU a K, x⁻¹ * γ₀ x ∈ suzukiZ0 a K := by
    intro x hx
    rw [hmemV]
    have h1 := hγQV _ ((hmemQ x).1 hx)
    rw [hγ₀_apply]
    convert h1 using 1
    group
  obtain ⟨b, hb, hγb⟩ := suzukiU_layer_kernel ha hK γ₀ hU hZ hUZ
  refine ⟨g * b * g⁻¹, (hmemQ b).1 hb, ?_⟩
  have : γ = MulAut.conj g * γ₀ * (MulAut.conj g)⁻¹ := by rw [hγ₀]; group
  rw [this, hγb, ← map_inv, ← map_mul, ← map_mul]

end CFSG.ShultStronglyClosedTI

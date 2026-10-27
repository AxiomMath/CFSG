module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocV
public import CFSG.LieType.Ree.LargeReeInvolutionIntermediateOddCore

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

set_option linter.unusedSectionVars false

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem entrywiseHom_rootElt (σ : K ≃+* K) (i : Idx) (u : K) :
    Units.map (entrywiseHom σ.toRingHom) (rootElt K a i u) = rootElt K a i (σ u) := by
  have hX : ∀ (r : ℕ) (c : K), Units.map (entrywiseHom (σ : K →+* K)) (sylowX K r c) =
      sylowX K r (σ c) := fun r c => units_map_entrywiseHom_pinnedX (σ : K →+* K) _ c
  have hσ : ∀ u : K, σ (largeReeSigma a u) = largeReeSigma a (σ u) := fun u => by
    simp only [largeReeSigma, map_pow]
  cases i <;>
    simp only [rootElt, sylowA, sylowB, sylowD, sylowF, sylowH, sylowJ, sylowK, sylowL, map_mul,
      RingEquiv.toRingHom_eq_coe, hX, hσ, map_add, map_mul, map_pow, map_zero]

theorem entrywiseHom_mem_S1 (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    {u : ModGL F4.tag K} (hu : u ∈ S1 K a) :
    Units.map (entrywiseHom σ.toRingHom) u ∈ S1 K a := by
  obtain ⟨g, i, rfl⟩ := exists_eq_of_mem_S1 hK hu
  rw [map_mul, entrywiseHom_rootElt, entrywiseHom_rootElt]
  exact mul_mem_S1 _ _

theorem exists_conj_fieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : MulAut (F4.reeGamma K a)) :
    ∃ (x : F4.reeGamma K a) (β : K ≃+* K),
      φ = MulAut.conj x * F4.reeGammaFieldAut K a β := by
  obtain ⟨-, h, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hp, -⟩ := h φ
  exact ⟨x, β, hp⟩

theorem coe_reeGammaFieldAut (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (β : K ≃+* K)
    (g : F4.reeGamma K a) :
    ((F4.reeGammaFieldAut K a β g : F4.reeGamma K a) : ModGL F4.tag K) =
      Units.map (entrywiseHom β.toRingHom) (g : ModGL F4.tag K) :=
  ((large_Ree_full_inner_field_automorphism_normal_form a ha K hK).1 β).1 g

theorem stabilizes_Vg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (φ : MulAut (Gm K a)) (hφ : φ (tg hK) = tg hK) : ∀ v ∈ Vg K a, φ v ∈ Vg K a := by
  obtain ⟨x, β, rfl⟩ := exists_conj_fieldAut ha hK φ
  have hβt : F4.reeGammaFieldAut K a β (tg hK) = tg hK := by
    refine Subtype.ext ?_
    rw [coe_reeGammaFieldAut ha hK]
    change Units.map (entrywiseHom β.toRingHom) (rootElt K a .i10 1) = rootElt K a .i10 1
    rw [entrywiseHom_rootElt, map_one]
  have hxt : (x : ModGL F4.tag K) * invF K a = invF K a * x := by
    have h := hφ
    rw [MulAut.mul_apply, MulAut.conj_apply, hβt] at h
    have h3 := congrArg Subtype.val (mul_inv_eq_iff_eq_mul.1 h)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tg] at h3
    exact h3
  have hxC : (x : ModGL F4.tag K) ∈ Subgroup.centralizer {invF K a} :=
    Subgroup.mem_centralizer_singleton_iff.2 hxt
  have hxN : (x : ModGL F4.tag K) ∈ Subgroup.normalizer (S1 K a : Set (ModGL F4.tag K)) :=
    centralizer_invF_le_normalizer_S1 ha hK (Subgroup.mem_inf.2 ⟨x.2, hxC⟩)
  intro v hv
  have hv' : (v : ModGL F4.tag K) ∈ S1 K a := hv
  show ((MulAut.conj x * F4.reeGammaFieldAut K a β) v : ModGL F4.tag K) ∈ S1 K a
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_reeGammaFieldAut ha hK]
  exact (Subgroup.mem_normalizer_iff.1 hxN _).1 (entrywiseHom_mem_S1 hK β hv')

end Model

end CFSG.Quasithin.H13.F431.TwoF4

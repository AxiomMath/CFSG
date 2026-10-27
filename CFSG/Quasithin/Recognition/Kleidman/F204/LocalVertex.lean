module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Alpha

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem exists_conj_le_sylow_two {K S A : Subgroup G} (hS : IsSylowTwoOf S K) (hA : A ≤ K)
    (hAp : IsPGroup 2 A) : ∃ c ∈ K, conjSub c A ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 (S.subgroupOf K) :=
    hS.2.1.comap_of_injective K.subtype K.subtype_injective
  have hE : IsPGroup 2 (A.subgroupOf K) := hAp.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨PS, hPS⟩ := hE.exists_le_sylow
  let PT : Sylow 2 K := hSp.toSylow hS.2.2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K PS PT
  refine ⟨c, c.2, fun x hx => ?_⟩
  rw [mem_conjSub] at hx
  have hxK : (c : G)⁻¹ * x * c ∈ K := hA hx
  have hx' : (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) ∈ A.subgroupOf K := hx
  have h1 : (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) ∈ (PS : Subgroup K) := hPS hx'
  have h2 : c * (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) * c⁻¹ ∈ ((c • PS : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨_, h1, by simp [MulAut.conj_apply]⟩
  rw [hc] at h2
  have h3 : c * (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) * c⁻¹ ∈ (PT : Subgroup K) := h2
  rw [show (PT : Subgroup K) = S.subgroupOf K from IsPGroup.toSylow_coe _ _] at h3
  have h4 : ((c * (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) * c⁻¹ : K) : G) ∈ S := h3
  have e : ((c * (⟨(c : G)⁻¹ * x * c, hxK⟩ : K) * c⁻¹ : K) : G) = x := by
    simp [mul_assoc]
  rwa [e] at h4

omit [Finite G] in
theorem isPGroup_two_of_sq {H : Subgroup G} (h : ∀ x ∈ H, x ^ 2 = 1) : IsPGroup 2 H := by
  intro x
  exact ⟨1, by simpa using Subtype.ext (h x x.2)⟩

omit [Finite G] in
theorem exists_conj_stab_false {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hδ : vtype δ = false) :
    ∃ g : G, conjSub g (stab δ) = P1 L1 L2 S ∧ conjSub g (Qv δ) = Q1 L1 L2 S := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hδ
  refine ⟨(g : G)⁻¹, ?_, ?_⟩
  · rw [stab_smul, stab_γ₀ h₁, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  · rw [Qv_smul, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    unfold Qv
    rw [stab_γ₀ h₁]

theorem relIndex_inf_Qv_le_two (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) {A : Subgroup G} (hA : A ≤ stab δ) (hA2 : IsElemAbelian 2 A) :
    (A ⊓ Qv δ).relIndex A ≤ 2 := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_stab_false (L1 := L1) (L2 := L2) (S := S) hδ
  have hA' : conjSub g A ≤ P1 L1 L2 S := hg1 ▸ conjSub_mono g hA
  have hsq : ∀ x ∈ A, x ^ 2 = 1 := hA2.2
  have hp' : IsPGroup 2 (conjSub g A) := by
    refine isPGroup_two_of_sq fun y hy => ?_
    rw [mem_conjSub] at hy
    have := hsq _ hy
    have hcp := conj_pow (a := g⁻¹) (b := y) (i := 2)
    simp only [inv_inv] at hcp
    have h1 : y ^ 2 = g * ((g⁻¹ * y * g) ^ 2) * g⁻¹ := by
      rw [hcp]; group
    rw [h1, this]; group
  obtain ⟨c, hcP, hc⟩ := exists_conj_le_sylow_two F.sylow_P1 hA' hp'
  rw [← conjSub_mul] at hc
  have hQ : conjSub (c * g) (Qv δ) = Q1 L1 L2 S := by
    rw [conjSub_mul, hg2]
    exact conjSub_eq_of_mem_normalizer (P1_le_normalizer_Q1 L1 L2 S hcP)
  have hE2 : ∀ e ∈ conjSub (c * g) A, e * e ∈ Q1 L1 L2 S := by
    intro e he
    rw [mem_conjSub] at he
    have h1 := hsq _ he
    have hcp := conj_pow (a := (c * g)⁻¹) (b := e) (i := 2)
    simp only [inv_inv] at hcp
    have h2 : e ^ 2 = (c * g) * (((c * g)⁻¹ * e * (c * g)) ^ 2) * (c * g)⁻¹ := by
      rw [hcp]; group
    have : e * e = 1 := by rw [← pow_two, h2, h1]; group
    rw [this]; exact (Q1 L1 L2 S).one_mem
  have := F.relIndex_inf_Q1_le_two hc hE2
  rwa [← hQ, ← conjSub_inf, relIndex_conjSub] at this

end CFSG.Quasithin.Kleidman.F204

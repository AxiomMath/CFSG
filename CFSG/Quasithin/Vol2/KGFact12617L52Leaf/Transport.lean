module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.H13.KG12617L52.Transport

open CFSG.Open CFSG.LieType.BorelTits

section Transport

variable {Γ S : Type*} [Group Γ] [Group S]

private theorem pCoreOf_map_of_injective (r : ℕ) (f : Γ →* S) (hf : Function.Injective f)
    (H : Subgroup Γ) : pCoreOf r (H.map f) = (pCoreOf r H).map f := by
  unfold pCoreOf
  let φ : H ≃* H.map f := Subgroup.equivMapOfInjective H f hf
  rw [← map_pCore_mulEquiv r φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem pCoreOf_subgroupOf {K B : Subgroup Γ} (r : ℕ) (hBK : B ≤ K) :
    pCoreOf r (B.subgroupOf K) = (pCoreOf r B).subgroupOf K := by
  have h := pCoreOf_map_of_injective r K.subtype K.subtype_injective (B.subgroupOf K)
  rw [Subgroup.map_subgroupOf_eq_of_le hBK] at h
  rw [h]
  exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm

theorem pCoreOf_map_subgroupOf {K B : Subgroup Γ} (e : ↥K ≃* S) (r : ℕ) (hBK : B ≤ K) :
    pCoreOf r ((B.subgroupOf K).map e.toMonoidHom) =
      ((pCoreOf r B).subgroupOf K).map e.toMonoidHom := by
  rw [pCoreOf_map_mulEquiv r e (B.subgroupOf K), pCoreOf_subgroupOf r hBK]

@[expose] noncomputable def transportEquiv {K B : Subgroup Γ} (e : ↥K ≃* S) (hBK : B ≤ K) :
    ↥B ≃* ↥((B.subgroupOf K).map e.toMonoidHom) :=
  (Subgroup.subgroupOfEquivOfLe hBK).symm.trans
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)

theorem commutator_map_subgroupOf {K B : Subgroup Γ} (e : ↥K ≃* S) (hBK : B ≤ K)
    (hB : ⁅B, B⁆ = B) :
    ⁅(B.subgroupOf K).map e.toMonoidHom, (B.subgroupOf K).map e.toMonoidHom⁆ =
      (B.subgroupOf K).map e.toMonoidHom := by
  have h1 : ⁅B.subgroupOf K, B.subgroupOf K⁆ = B.subgroupOf K := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBK, hB]
  rw [← Subgroup.map_commutator, h1]

theorem quasithinO2QuotientIso_map {K B : Subgroup Γ} (e : ↥K ≃* S) (hBK : B ≤ K)
    {H : Type*} [Group H] (h : CFSG.Open.quasithinO2QuotientIso B H) :
    CFSG.Open.quasithinO2QuotientIso ((B.subgroupOf K).map e.toMonoidHom) H := by
  obtain ⟨φ, hφs, hφk⟩ := h
  let ψ := transportEquiv e hBK
  have hker : (φ.comp ψ.symm.toMonoidHom).ker = (pCore 2 B).map ψ.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv, ← hφk, MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Iff.rfl
  exact ⟨φ.comp ψ.symm.toMonoidHom, hφs.comp ψ.symm.surjective,
    by rw [hker, map_pCore_mulEquiv 2 ψ]⟩

private theorem mem_normalizer_subgroupOf_iff {K Z : Subgroup Γ} (hZ : Z ≤ K) (k : ↥K) :
    k ∈ Subgroup.normalizer ((Z.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (k : Γ) ∈ Subgroup.normalizer (Z : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hg : g ∈ K
    · have := h ⟨g, hg⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hgZ
        exact absurd (hZ hgZ) hg
      · intro hkgk
        exfalso
        apply hg
        have h1 : (k : Γ) * g * (k : Γ)⁻¹ ∈ K := hZ hkgk
        have h2 := K.mul_mem (K.mul_mem (K.inv_mem k.2) h1) k.2
        simpa [mul_assoc] using h2
  · intro h x
    have := h (x : Γ)
    simpa [Subgroup.mem_subgroupOf] using this

theorem mem_normalizer_map_iff {K Z : Subgroup Γ} (e : ↥K ≃* S) (hZ : Z ≤ K) (g : S) :
    g ∈ Subgroup.normalizer (((Z.subgroupOf K).map e.toMonoidHom : Subgroup S) : Set S) ↔
      ((e.symm g : ↥K) : Γ) ∈ Subgroup.normalizer (Z : Set Γ) := by
  have h1 : Subgroup.normalizer (((Z.subgroupOf K).map e.toMonoidHom : Subgroup S) : Set S) =
      (Subgroup.normalizer ((Z.subgroupOf K : Subgroup ↥K) : Set ↥K)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq _ e).symm
  rw [h1, Subgroup.mem_map_equiv, mem_normalizer_subgroupOf_iff hZ]

end Transport

end CFSG.Quasithin.H13.KG12617L52.Transport

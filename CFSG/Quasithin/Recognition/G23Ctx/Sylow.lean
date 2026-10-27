module

public import CFSG.Quasithin.Recognition.G23Ctx.HStructure
public import CFSG.Quasithin.Recognition.G23Ctx.MSide
public import CFSG.Quasithin.Recognition.G23Ctx.Generic

public section

namespace CFSG.Quasithin.G23Type.Ctx

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {G : Type} [Group G] {H H₁ H₂ M : Subgroup G}

theorem exists_sylow_H [Finite G] (H : Subgroup G) :
    ∃ T : Subgroup G, T ≤ H ∧ quasithinIsSylowTwo (T.subgroupOf H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, ?_⟩
  have hsub : ((P : Subgroup H).map H.subtype).subgroupOf H = (P : Subgroup H) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      rw [← hxy]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold quasithinIsSylowTwo
  rw [hsub]
  exact ⟨P.isPGroup', Sylow.not_dvd_index P⟩

theorem normalizer_le_H (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {T : Subgroup G}
    (hTH : T ≤ H) (hT : quasithinIsSylowTwo (T.subgroupOf H)) :
    Subgroup.normalizer (T : Set G) ≤ H := by
  intro x hx
  have hxT : ∀ t, t ∈ T ↔ x * t * x⁻¹ ∈ T := fun t => by
    simpa using Subgroup.mem_normalizer_iff.mp hx t
  obtain ⟨s, hs, t, ht, hs4, ht4, hst⟩ := exists_comm_z hH hz
  have hsT : s ∈ T := pow4_mem_sylow hH hTH hT hs hs4
  have htT : t ∈ T := pow4_mem_sylow hH hTH hT ht ht4
  have hxs : x * s * x⁻¹ ∈ T := (hxT s).mp hsT
  have hxt : x * t * x⁻¹ ∈ T := (hxT t).mp htT
  have hz' : x * z * x⁻¹ = (x * s * x⁻¹) * (x * t * x⁻¹) * (x * s * x⁻¹)⁻¹ * (x * t * x⁻¹)⁻¹ := by
    rw [← hst]; group
  have hz'K : x * z * x⁻¹ ∈ H₁ ⊔ H₂ := by
    rw [hz']; exact commutator_mem_sup hH (hTH hxs) (hTH hxt)
  have hz'T : ∀ u ∈ T, u * (x * z * x⁻¹) = (x * z * x⁻¹) * u := by
    intro u hu
    have hu' : x⁻¹ * u * x ∈ T := by
      rw [hxT]
      have : x * (x⁻¹ * u * x) * x⁻¹ = u := by group
      rw [this]; exact hu
    have hc := IsZ.comm hH hz (hTH hu')
    calc u * (x * z * x⁻¹) = x * ((x⁻¹ * u * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * u * x)) * x⁻¹ := by rw [hc]
      _ = (x * z * x⁻¹) * u := by group
  have hQ₁ : ∀ q ∈ H₁, q ^ 4 = 1 → (x * z * x⁻¹) * q = q * (x * z * x⁻¹) := fun q hq hq4 =>
    (hz'T q (pow4_mem_sylow hH hTH hT hq hq4)).symm
  have hQ₂ : ∀ q ∈ H₂, q ^ 4 = 1 → (x * z * x⁻¹) * q = q * (x * z * x⁻¹) := fun q hq hq4 =>
    (hz'T q (pow4_mem_sylow (g23One_symm hH) hTH hT hq hq4)).symm
  rcases eq_of_centralizes hH hz hz'K hQ₁ hQ₂ with h | h
  · exfalso
    apply hz.ne_one
    have : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [this, h]; group
  · apply mem_H_of_comm hH hz
    have h' : x * z * x⁻¹ = z := h
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'

theorem sylow_G [Finite G] (hH : G23One H H₁ H₂) {z : G} (hz : IsZ H₁ H₂ z) {T : Subgroup G}
    (hTH : T ≤ H) (hT : quasithinIsSylowTwo (T.subgroupOf H)) : quasithinIsSylowTwo T :=
  sylow_of_normalizer_le hTH hT (normalizer_le_H hH hz hTH hT)

theorem exists_conj_M [Finite G] (hH : G23One H H₁ H₂) (hM : G23Two M) {z : G}
    (hz : IsZ H₁ H₂ z) {T : Subgroup G} (hTH : T ≤ H)
    (hT : quasithinIsSylowTwo (T.subgroupOf H)) :
    ∃ M' : Subgroup G, G23Two M' ∧ T ≤ M' ∧ z ∈ quasithinGenFitting M' := by
  have hTG : quasithinIsSylowTwo T := sylow_G hH hz hTH hT
  obtain ⟨S, hSM, hS⟩ := exists_sylow_H M
  have hS2 : IsPGroup 2 S :=
    hS.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSM)
  have hScard : Nat.card S = 64 := G23Two.card_sylow hM hSM hS2 hS.2
  have hcard : Nat.card S = Nat.card T := by rw [hScard, card_sylow_H hH hTH hT]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card hTG hS2 hcard
  let σ : G ≃* G := MulAut.conj g
  have hM' : G23Two (M.map σ.toMonoidHom) := g23Two_map hM σ
  have hTM' : T ≤ M.map σ.toMonoidHom := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hSM ((hg x).mp hx), ?_⟩
    simp [σ, MulAut.conj_apply, mul_assoc]
  refine ⟨M.map σ.toMonoidHom, hM', hTM', ?_⟩
  have hTidx : ¬ 2 ∣ (T.subgroupOf (M.map σ.toMonoidHom)).index := fun hd =>
    hTG.2 (dvd_trans hd (Dvd.intro _ (Subgroup.relIndex_mul_index hTM')))
  have hVT : quasithinGenFitting (M.map σ.toMonoidHom) ≤ T :=
    G23Two.fitting_le_T hM' hTM' hTG.1 hTidx
  have hzT : z ∈ T := mem_sylow_z hH hz hTH hT
  have hzC : z ∈ Subgroup.centralizer (quasithinGenFitting (M.map σ.toMonoidHom) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact IsZ.comm hH hz (hTH (hVT hv))
  have hzV : z ∈ (M.map σ.toMonoidHom) ⊓
      Subgroup.centralizer (quasithinGenFitting (M.map σ.toMonoidHom) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hTM' hzT, hzC⟩
  rwa [G23Two.inf_centralizer_fitting hM'] at hzV

end CFSG.Quasithin.G23Type.Ctx

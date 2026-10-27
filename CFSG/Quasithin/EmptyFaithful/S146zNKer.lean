module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Ker

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a6k_centralizerMod_le {Z₀ E K : Subgroup G} (hKZ : K ≤ Subgroup.normalizer (Z₀ : Set G))
    (hKE : K ≤ Subgroup.normalizer (E : Set G)) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ e ∈ E, p * e * p⁻¹ * e⁻¹ ∈ Z₀)
    (hnt : ∃ k ∈ K, ∃ e ∈ E, k * e * k⁻¹ * e⁻¹ ∉ Z₀) :
    centralizerMod Z₀ K E ≤ pCoreOf 2 K := by
  classical
  have hC₁K : centralizerMod Z₀ K E ≤ K := centralizerMod_le_left _ _ _
  have key : ∀ k ∈ K, ∀ c ∈ centralizerMod Z₀ K E, k * c * k⁻¹ ∈ centralizerMod Z₀ K E := by
    intro k hk c hc
    obtain ⟨hcK, hcN, hcu⟩ := mem_centralizerMod.mp hc
    refine mem_centralizerMod.mpr ⟨K.mul_mem (K.mul_mem hk hcK) (K.inv_mem hk),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKZ hk) hcN) (Subgroup.inv_mem _ (hKZ hk)),
      fun u hu => ?_⟩
    have hu' : k⁻¹ * u * k ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (hKE (K.inv_mem hk)) u).mp hu
      simpa using this
    have hc' := hcu _ hu'
    have e : k * c * k⁻¹ * u * (k * c * k⁻¹)⁻¹ * u⁻¹ =
        k * (c * (k⁻¹ * u * k) * c⁻¹ * (k⁻¹ * u * k)⁻¹) * k⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKZ hk) _).mp hc'
  have hnormC : K ≤ Subgroup.normalizer ((centralizerMod Z₀ K E : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => key k hk c hc, fun hc => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hc
    have e : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
    rwa [e] at h1
  have hCn : ((centralizerMod Z₀ K E).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁K).mpr hnormC
  set π : ↥K →* KBar K := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNn : (((centralizerMod Z₀ K E).subgroupOf K).map π).Normal :=
    Subgroup.Normal.map hCn π hπs
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (((centralizerMod Z₀ K E).subgroupOf K).map π) with hbot | htop
  · intro x hx
    have hxK : x ∈ K := hC₁K hx
    have h1 : π ⟨x, hxK⟩ ∈ ((centralizerMod Z₀ K E).subgroupOf K).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  · exfalso
    obtain ⟨k, hk, u, hu, hnc⟩ := hnt
    apply hnc
    have h1 : π ⟨k, hk⟩ ∈ ((centralizerMod Z₀ K E).subgroupOf K).map π := by
      rw [htop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hck⟩ := h1
    have hp : (c : G)⁻¹ * k ∈ pCoreOf 2 K :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hck)
    have hcC : (c : G) ∈ centralizerMod Z₀ K E := Subgroup.mem_subgroupOf.mp hc
    obtain ⟨-, hcN, hcu⟩ := mem_centralizerMod.mp hcC
    have hz1 := hQ _ hp u hu
    have e : k * u * k⁻¹ * u⁻¹ =
        ((c : G) * ((c : G)⁻¹ * k * u * ((c : G)⁻¹ * k)⁻¹ * u⁻¹) * (c : G)⁻¹) *
          ((c : G) * u * (c : G)⁻¹ * u⁻¹) := by group
    rw [e]
    exact Z₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN _).mp hz1) (hcu u hu)

theorem a6k_centralizerMod_H_le {Z₀ E H K T : Subgroup G} (hK : K ∈ cComp H)
    (hs : IsSimpleGroup (KBar K)) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hT2 : IsPGroup 2 T)
    (hHKT : H = K ⊔ T) (hHZ : H ≤ Subgroup.normalizer (Z₀ : Set G))
    (hHE : H ≤ Subgroup.normalizer (E : Set G))
    (hKQ : centralizerMod Z₀ K E ≤ pCoreOf 2 H) :
    centralizerMod Z₀ H E ≤ pCoreOf 2 H := by
  intro c hc
  obtain ⟨hcH, hcN, hcE⟩ := hc
  refine mem_pCoreOf_of_commutator_mem hK hs hHK hT2 hHKT hcH fun k hk => ?_
  have hkH : k ∈ H := le_of_mem_cComp hK hk
  have htriv := acts_trivially_commutator (F := Z₀) (E := E) hcN (hHE hcH) (hHZ hkH) (hHE hkH) hcE
  have hcK : c * k * c⁻¹ * k⁻¹ ∈ K := by
    have h3 := (Subgroup.mem_normalizer_iff.mp (hHK hcH) k).mp hk
    exact K.mul_mem h3 (K.inv_mem hk)
  have hcN' : c ∈ Subgroup.normalizer (Z₀ : Set G) := hHZ hcH
  have hkN' : k ∈ Subgroup.normalizer (Z₀ : Set G) := hHZ hkH
  have hN : c * k * c⁻¹ * k⁻¹ ∈ Subgroup.normalizer (Z₀ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN' hkN')
      (Subgroup.inv_mem _ hcN')) (Subgroup.inv_mem _ hkN')
  exact hKQ ⟨hcK, hN, htriv⟩

theorem a6k_mIdx_centralizerMod_le {Z₀ U E X : Subgroup G} (hU : IsPGroup 2 U) (hEU : E ≤ U) :
    mIdx E (centralizerMod Z₀ E X) ≤ mIdx U (centralizerMod Z₀ U X) := by
  have h : centralizerMod Z₀ E X = centralizerMod Z₀ U X ⊓ E := by
    ext x
    constructor
    · rintro ⟨hxE, hxN, hx⟩
      exact ⟨⟨hEU hxE, hxN, hx⟩, hxE⟩
    · rintro ⟨⟨-, hxN, hx⟩, hxE⟩
      exact ⟨hxE, hxN, hx⟩
  rw [h]
  exact ThreeC.mIdx_inf_le_mIdx hU hEU

end Ker

end CFSG.Quasithin

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.Harris.KFact2d.Corr

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P
open scoped Pointwise
open CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem le_normalizer_sup₂ {K A B : Subgroup G} (hA : K ≤ Subgroup.normalizer (A : Set G))
    (hB : K ≤ Subgroup.normalizer (B : Set G)) : K ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g ∈ K, ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
    intro g hg x hx
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
      sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hA hg) a).mp ha))
        (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hB hg) b).mp hb))
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun h => key g hg x h, fun h => ?_⟩
  have := key g⁻¹ (K.inv_mem hg) _ h
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_zOf {X : Type} [Group X] {S : Subgroup X} {x : X}
    (hx : x ∈ Subgroup.normalizer (S : Set X)) : x ∈ Subgroup.normalizer (zOf S : Set X) := by
  have key : ∀ x ∈ Subgroup.normalizer (S : Set X), ∀ y ∈ zOf S, x * y * x⁻¹ ∈ zOf S := by
    intro x hx y hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp hx y).mp hy.1, ?_⟩
    show x * y * x⁻¹ ∈ Subgroup.centralizer (S : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := Subgroup.mem_centralizer_iff.mp hy.2 (x⁻¹ * s * x)
      ((Subgroup.mem_normalizer_iff.mp hx _).mpr (by simpa [mul_assoc] using hs))
    calc s * (x * y * x⁻¹) = x * ((x⁻¹ * s * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * s * x)) * x⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun h => key x hx y h, fun h => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ h
  simpa [mul_assoc] using this

section Star

variable [Finite G] {T N K K0 : Subgroup G}

theorem star_sup_pCore (hQJ : pCoreOf 2 K ≤ kerIn N K) (hK0K : K0 ≤ K)
    (hQK : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) :
    E2.star N K (K0 ⊔ pCoreOf 2 K) = E2.star N K K0 := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have hd' := Subgroup.mem_subgroupOf.mp hd
    have hcoe : (↑(K0 ⊔ pCoreOf 2 K) : Set G) = K0 * pCoreOf 2 K :=
      Subgroup.coe_mul_of_left_le_normalizer_right K0 _ (hK0K.trans hQK)
    have hd'' : (d : G) ∈ (↑(K0 ⊔ pCoreOf 2 K) : Set G) := hd'
    rw [hcoe] at hd''
    obtain ⟨k, hk, q, hq, hkq⟩ := hd''
    have hkK : k ∈ K := hK0K hk
    have hqK : q ∈ K := pCoreOf_le 2 K hq
    have hq1 : starMap N K ⟨q, hqK⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_starMap]
      exact Subgroup.mem_subgroupOf.mpr (hQJ hq)
    have hdeq : d = ⟨k, hkK⟩ * ⟨q, hqK⟩ := Subtype.ext hkq.symm
    refine ⟨⟨k, hkK⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
    rw [hdeq, map_mul, hq1, mul_one]
  · exact star_mono le_sup_left

theorem isSylowTwoOf_star_inf (hmp : MinParabolic K T N) (hK0 : K0 ∈ cComp K) :
    IsSylowTwoOf (E2.star N K T ⊓ E2.star N K K0) (E2.star N K K0) := by
  have hKH : K0 ≤ K := le_of_mem_cComp hK0
  have hS := isSylowTwoOf_inf_of_subnormal hmp.isSylow hK0.2.2.1
  set ρ : ↥K0 →* E2.StarQuot N K := (starMap N K).comp (Subgroup.inclusion hKH) with hρ
  have hrange : ρ.range = E2.star N K K0 := by
    rw [hρ, MonoidHom.range_comp, star_def]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have himage : ((T ⊓ K0).subgroupOf K0).map ρ = E2.star N K (T ⊓ K0) := by
    rw [hρ, star_def, ← Subgroup.map_map]
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx, rfl⟩
  have hSyl := isSylowTwoOf_map_hom hS ρ
  rw [himage, hrange] at hSyl
  rw [← star_inf_T hmp.isSylow hK0.2.2.1 hKH]
  exact hSyl

end Star

end CFSG.Quasithin.Background.Harris.KFact2d

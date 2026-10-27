module

public import CFSG.Milestones.ASVolI.F431.BCoreU4
public import CFSG.Milestones.ASVolI.F431.BCoreGenQ
public import CFSG.Quasithin.H13.U4ParOuterO2

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open scoped commutatorElement

theorem burnsideF4m_U4_parP2_selfNorm {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (g : hypSU h 2 0) (hg : g ∈ Subgroup.normalizer (parP2 h : Set (hypSU h 2 0))) :
    g ∈ parP2 h := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have hyam := isYAmalgamPair_parP_parP2 h
  have hyam' : IsYAmalgamPair (hypUnitriangular h 2 0) (parP2 h) (parP h) := by
    refine ⟨hyam.1, hyam.2.1.symm, fun X => ?_⟩
    rw [hyam.2.2 X, or_comm]
  exact burnsideF4d_selfNorm hyam' g (Subgroup.mem_normalizer_iff.mp hg)

theorem burnsideF4m_U4_pCore {f : ℕ} {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) := by
  haveI := hyp.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, fK, h, Φ, -, h2⟩ := burnsideF4m_U4_chart hyp.toHypF_4_4g
  set φ : hypSU h 2 0 →* E := Gp.subtype.comp Φ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Φ.injective
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hN2 : Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) ≤ M₂ :=
    burnsideF4m_normalizer_inf_le (M₁ := M₁)
      (fun e => by
        obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
        exact ⟨n, hn, k, hk, he⟩) φ hφ hrange h2 (burnsideF4m_U4_parP2_selfNorm h)
  refine burnsideF4m_pCoreOf_eq_inf_of_le Gp M₂ ?_
  by_contra hle
  obtain ⟨r, hrR, hrG, hr2⟩ := burnsideF4m_exists_sq_mem
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₂) hle
  set Y : Subgroup E := Gp ⊔ Subgroup.zpowers r with hY
  have hGY : Gp ≤ Y := le_sup_left
  have hrY : r ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  set ψ : hypSU h 2 0 →* ↥Y := (Subgroup.inclusion hGY).comp Φ.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (Subgroup.inclusion_injective hGY).comp Φ.injective
  have hψY : ∀ g, ((ψ g : ↥Y) : E) = φ g := fun g => rfl
  have hψrange : ψ.range = Gp.subgroupOf Y := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.inclusion_range]
  have hidx : ψ.range.index = 2 := by
    rw [hψrange]
    exact burnsideF4m_index_sup_zpowers hrG hr2
  have hC : Subgroup.centralizer (ψ.range : Set ↥Y) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hy' : (y : E) ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_centralizer_iff.mp hy ⟨g, hGY hg⟩
        (by rw [hψrange]; exact Subgroup.mem_subgroupOf.mpr hg)
      exact congrArg Subtype.val this
    rw [hyp.centralizer_trivial, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (Subtype.ext hy')
  obtain ⟨y₀, hy₀, -, hact⟩ := exists_frob_elt h ψ hψ hidx hC
  have hψP2 : ∀ y : ↥Y, y ∈ (parP2 h).map ψ ↔ (y : E) ∈ Gp ⊓ M₂ := by
    intro y
    rw [h2]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, hgy⟩
      exact ⟨g, hg, Subtype.ext hgy⟩
  have hMψ : Subgroup.normalizer (((parP2 h).map ψ : Subgroup ↥Y) : Set ↥Y) ⊓ ψ.range =
      (parP2 h).map ψ := by
    refine le_antisymm ?_ (le_inf Subgroup.le_normalizer (Subgroup.map_le_range ψ _))
    rintro y ⟨hyN, g, rfl⟩
    refine Subgroup.mem_map_of_mem ψ (burnsideF4m_U4_parP2_selfNorm h g ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := (Subgroup.mem_normalizer_iff.mp hyN) (ψ x)
    rw [Subgroup.mem_map_iff_mem hψ, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hψ] at h1
    exact h1
  have hO := pCoreOf_normalizer_parP2 h hact hf hψ hidx hy₀ rfl hMψ
  set X : Subgroup ↥Y := (pCoreOf 2 M₂).subgroupOf Y with hX
  have hXN : X ≤ Subgroup.normalizer (((parP2 h).map ψ : Subgroup ↥Y) : Set ↥Y) := by
    intro y hy
    have hyM : (y : E) ∈ M₂ := CFSG.LieType.BorelTits.pCoreOf_le 2 M₂ (Subgroup.mem_subgroupOf.mp hy)
    have hyN := burnsideF4m_mem_normalizer_inf (Gp := Gp) hyM
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hψP2, hψP2]
    exact (Subgroup.mem_normalizer_iff.mp hyN) x
  have hNX : Subgroup.normalizer (((parP2 h).map ψ : Subgroup ↥Y) : Set ↥Y) ≤
      Subgroup.normalizer (X : Set ↥Y) := by
    intro y hy
    have hyE : (y : E) ∈ Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxY : x ∈ Y := hGY hx.1
        have := (Subgroup.mem_normalizer_iff.mp hy ⟨x, hxY⟩).mp ((hψP2 ⟨x, hxY⟩).mpr hx)
        exact (hψP2 _).mp this
      · intro hx
        have hxG : x ∈ Gp := by
          have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hx.1 (y : E)⁻¹
          simpa [mul_assoc] using this
        have hxY : x ∈ Y := hGY hxG
        have := (Subgroup.mem_normalizer_iff.mp hy ⟨x, hxY⟩).mpr ((hψP2 _).mpr hx)
        exact (hψP2 _).mp this
    have hyM := hN2 hyE
    have hyR := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₂ hyM
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hX, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hyR) x
  have hXp : IsPGroup 2 X :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₂).comap_of_injective Y.subtype
      Y.subtype_injective
  have hXO := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXN hNX hXp
  rw [hO] at hXO
  have hr : (⟨r, hrY⟩ : ↥Y) ∈ (radQ2 h).map ψ := hXO (Subgroup.mem_subgroupOf.mpr hrR)
  obtain ⟨g, -, hg⟩ := hr
  apply hrG
  have hgr : φ g = r := by
    have := congrArg Subtype.val hg
    rw [hψY] at this
    exact this
  rw [← hgr, ← hrange]
  exact ⟨g, rfl⟩

end CFSG.ASVolI

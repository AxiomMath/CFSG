module

public import CFSG.RankThree.PartOne.Q1327Z.Block
public import CFSG.RankThree.PartOne.Q1327T.CAlg
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.Q1327.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T

@[expose] def NoncommOK (p : ℕ) {P : Type} [Group P] (T : Subgroup P) : Prop :=
  ∀ g ∈ Subgroup.normalizer (T : Set P), ∀ S : Subgroup P, S ≤ T → S.relIndex T = p →
    (∀ x ∈ S, g * x * g⁻¹ = x) → (∃ x ∈ T, g * x * g⁻¹ ≠ x) →
    (∀ x ∈ T, g * (g * x * g⁻¹) * g⁻¹ = x) →
    (∀ x ∈ T, ∀ x' ∈ T, g * x * g⁻¹ * x⁻¹ ≠ 1 →
      ∃ k : ℕ, g * x' * g⁻¹ * x'⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ k) →
    ∀ c ∈ T, c ∉ S → g * c * g⁻¹ = c⁻¹ →
      ∃ y ∈ Subgroup.centralizer (S : Set P), ¬ Commute c (y * c * y⁻¹)

variable {G : Type} [Group G]

theorem range_eq_map_subgroupOf {X F : Subgroup G} (hFX : F ≤ X) {P : Type} [Group P]
    (ε : ↥X →* P) : (ε.comp (Subgroup.inclusion hFX)).range = (F.subgroupOf X).map ε := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f, hFX f.2⟩, f.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

variable [Finite G]

theorem refl_of_quotient {p : ℕ} {X A₀ F : Subgroup G} (h : Q1327.T123Base p X A₀ F) {P : Type}
    [Group P] (ε : ↥X →* P) (hε : Function.Surjective ε) (hker : ε.ker ≤ Subgroup.center ↥X)
    (hmodel : NoncommOK p ((F.subgroupOf X).map ε)) {t : MulAut ↥F} (ht : t ∈ torusImage F X)
    (hrefl : IsAutReflection p F t) {c₀ : G} (hc₀ : c₀ ∈ autMovedInG F t) (hc₀1 : c₀ ≠ 1) :
    ∃ y ∈ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G), ¬ Commute c₀ (y * c₀ * y⁻¹) := by
  classical
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hZ := h.center_pPrime
  have hFX : F ≤ X := h.F_le
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.F_elem
  let ι : ↥F →* ↥X := Subgroup.inclusion hFX
  let θ : ↥F →* P := ε.comp ι
  rw [← range_eq_map_subgroupOf hFX ε] at hmodel
  have hFp : ∀ f : F, f ^ p = 1 := hd.pow
  have hθker : ∀ f : F, θ f = 1 → f = 1 := by
    intro f hf
    have h1 : ι f ∈ ε.ker := MonoidHom.mem_ker.2 hf
    have h2 : (ι f) ^ p = 1 := by rw [← map_pow, hFp f, map_one]
    have h3 : ι f = 1 := eq_one_of_mem_center hp hZ (hker h1) h2
    exact Subgroup.inclusion_injective hFX (h3.trans (map_one ι).symm)
  have hθinj : Function.Injective θ := (injective_iff_map_eq_one θ).2 hθker
  obtain ⟨g, hgX, hgN, hgt⟩ := Sec12Three.mem_torusImage_iff.1 ht
  have hconj : ∀ f : F, ((t f : F) : G) = g * (f : G) * g⁻¹ := fun f => by
    have := Equivariance.coe_conjAut hgN f
    rwa [show conjAut F g hgN = t from hgt] at this
  let g' : ↥X := ⟨g, hgX⟩
  let γ : P := ε g'
  have hconjX : ∀ f : F, g' * ι f * g'⁻¹ = ι (t f) := fun f =>
    Subtype.ext (by simpa [ι, g'] using (hconj f).symm)
  have hγθ : ∀ f : F, γ * θ f * γ⁻¹ = θ (t f) := fun f => by
    show ε g' * ε (ι f) * (ε g')⁻¹ = ε (ι (t f))
    rw [← map_inv, ← map_mul, ← map_mul, hconjX f]
  have hγN : γ ∈ Subgroup.normalizer (θ.range : Set P) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨t f, (hγθ f).symm⟩
    · rintro ⟨f', hf'⟩
      refine ⟨t.symm f', ?_⟩
      have h1 := hγθ (t.symm f')
      rw [MulEquiv.apply_symm_apply, hf'] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hSle : (autFixed F t).map θ ≤ θ.range := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have hSidx : ((autFixed F t).map θ).relIndex θ.range = p := by
    have h1 : (autFixed F t).relIndex ⊤ = p := by
      have := RefFacts.relIndex_inf_fixed hd hrefl (B := ⊤) le_top
      simpa using this
    have h2 := Subgroup.relIndex_map_map_of_injective (f := θ) (autFixed F t) (⊤ : Subgroup F)
      hθinj
    rw [← MonoidHom.range_eq_map, h1] at h2
    exact h2
  have hγfix : ∀ x ∈ (autFixed F t).map θ, γ * x * γ⁻¹ = x := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hγθ s]
    have : t s = s := hs
    rw [this]
  have hγnc : ∃ x ∈ θ.range, γ * x * γ⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    have ht1 : t = 1 := by
      refine MulEquiv.ext fun f => ?_
      apply hθinj
      rw [← hγθ f]
      exact hcon (θ f) ⟨f, rfl⟩
    have h2 := hrefl.1
    rw [ht1, orderOf_one] at h2
    omega
  obtain ⟨c', hc', hc'G⟩ := Subgroup.mem_map.1 hc₀
  have hc'G' : (c' : G) = c₀ := hc'G
  have htc : t c' = c'⁻¹ := RefFacts.t_apply_inv_of_mem_autMoved hd hrefl hc'
  have hcbarS : θ c' ∉ (autFixed F t).map θ := by
    rintro ⟨s, hs, hsc⟩
    have hs' : s = c' := hθinj hsc
    rw [hs'] at hs
    have h1 : t c' = c'⁻¹ := htc
    have h2 : t c' = c' := hs
    have h3 : c' = c'⁻¹ := h2.symm.trans h1
    have hc2 : c' ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 h3
    have hc'1 : c' = 1 := eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 hc2 (hFp c')
    exact hc₀1 (by rw [← hc'G', hc'1]; rfl)
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hrefl.1, sq] at this
  have hγinv : ∀ x ∈ θ.range, γ * (γ * x * γ⁻¹) * γ⁻¹ = x := by
    rintro _ ⟨f, rfl⟩
    rw [hγθ f, hγθ (t f)]
    have : t (t f) = f := by
      rw [← MulAut.mul_apply, htt, MulAut.one_apply]
    rw [this]
  have hγc : γ * θ c' * γ⁻¹ = (θ c')⁻¹ := by
    rw [hγθ c', htc, map_inv]
  have hγcyc : ∀ x ∈ θ.range, ∀ x' ∈ θ.range, γ * x * γ⁻¹ * x⁻¹ ≠ 1 →
      ∃ k : ℕ, γ * x' * γ⁻¹ * x'⁻¹ = (γ * x * γ⁻¹ * x⁻¹) ^ k := by
    rintro _ ⟨f, rfl⟩ _ ⟨f', rfl⟩ hne
    have hmv : ∀ f : F, γ * θ f * γ⁻¹ * (θ f)⁻¹ = θ (t f * f⁻¹) := fun f => by
      rw [hγθ f, map_mul, map_inv]
    let mv : F → ↥(autMoved F t) := fun f => ⟨t f * f⁻¹, Subgroup.subset_closure ⟨f, rfl⟩⟩
    have hmvne : mv f ≠ 1 := fun h1 => hne (by
      rw [hmv f]
      have : t f * f⁻¹ = 1 := congrArg Subtype.val h1
      rw [this, map_one])
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1
      (mem_powers_of_prime_card hrefl.2 hmvne (g' := mv f'))
    refine ⟨n, ?_⟩
    rw [hmv f', hmv f, ← map_pow]
    congr 1
    simpa using (congrArg Subtype.val hn).symm
  obtain ⟨yb, hyb, hnc⟩ := hmodel γ hγN _ hSle hSidx hγfix hγnc hγinv hγcyc (θ c') ⟨c', rfl⟩ hcbarS
    hγc
  obtain ⟨y', rfl⟩ := hε yb
  refine ⟨(y' : G), Subgroup.mem_inf.2 ⟨y'.2, ?_⟩, ?_⟩
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs
    have hcomm : θ s₀ * ε y' = ε y' * θ s₀ :=
      Subgroup.mem_centralizer_iff.1 hyb (θ s₀) ⟨s₀, hs₀, rfl⟩
    have hc1 : ε (y' * ι s₀ * y'⁻¹ * (ι s₀)⁻¹) = 1 := by
      have : ε (y' * ι s₀ * y'⁻¹ * (ι s₀)⁻¹) = ε y' * θ s₀ * (ε y')⁻¹ * (θ s₀)⁻¹ := by
        simp [θ]
      rw [this, ← hcomm]
      group
    have hz : y' * ι s₀ * y'⁻¹ * (ι s₀)⁻¹ ∈ Subgroup.center ↥X := hker (MonoidHom.mem_ker.2 hc1)
    have hx : (ι s₀) ^ p = 1 := by rw [← map_pow, hFp s₀, map_one]
    have hy := commute_of_commutator_mem_center hp hZ hx hz
    have hyG : (y' : G) * (s₀ : G) * (y' : G)⁻¹ = (s₀ : G) := congrArg Subtype.val hy
    exact (mul_inv_eq_iff_eq_mul.1 hyG).symm
  ·
    intro hcomm
    apply hnc
    have h1 : ι c' * (y' * ι c' * y'⁻¹) = (y' * ι c' * y'⁻¹) * ι c' :=
      Subtype.ext (by simpa [ι, hc'G'] using hcomm.eq)
    have h2 := congrArg ε h1
    have h3 : θ c' * (ε y' * θ c' * (ε y')⁻¹) = (ε y' * θ c' * (ε y')⁻¹) * θ c' := by
      simpa [θ, map_mul, map_inv] using h2
    exact h3

end CFSG.RankThree.PartOne.Q1327Z

module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveModel
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenT2
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_normalizer_centralizer_of_mem {G : Type*} [Group G] {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : g⁻¹ * r * g ∈ S := (Subgroup.mem_normalizer_iff''.mp hg r).mp hr
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hr'
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * r := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def x₃ : G := E.ι x3m

@[expose] def f₁ : G := E.ι fm

theorem x₃_cube : E.x₃ ^ 3 = 1 := by
  rw [pow_three']
  show E.ι x3m * E.ι x3m * E.ι x3m = 1
  rw [← map_mul, ← map_mul, x3m_cube, map_one]

theorem x₃_ne_one : E.x₃ ≠ 1 := fun h => x3m_ne_one (E.injective (by rw [map_one]; exact h))

theorem orderOf_x₃ : orderOf E.x₃ = 3 :=
  orderOf_eq_prime E.x₃_cube E.x₃_ne_one

theorem x₃_mem_normalizer : E.x₃ ∈ Subgroup.normalizer (E.E₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨x3m * u * x3m⁻¹, x3m_norm u hu, by simp only [map_mul, map_inv]; rfl⟩
  · rintro ⟨u, hu, hu'⟩
    refine ⟨x3m⁻¹ * u * x3m, x3m_norm_inv u hu, ?_⟩
    have h1 : E.ι (x3m⁻¹ * u * x3m) = E.x₃⁻¹ * E.ι u * E.x₃ := by
      simp only [map_mul, map_inv]; rfl
    rw [h1, hu']
    group

theorem x₃_mem_normalizer_HH : E.x₃ ∈ Subgroup.normalizer (E.HH : Set G) :=
  normalizer_le_normalizer_oTwoUpper E.CE (mem_normalizer_centralizer_of_mem E.x₃_mem_normalizer)

theorem x₃_comm_H₁ {y : G} (hy : y ∈ E.H₁) : E.x₃ * y = y * E.x₃ := by
  obtain ⟨m, hm, rfl⟩ := hy
  show E.ι x3m * E.ι m = E.ι m * E.ι x3m
  rw [← map_mul, ← map_mul, x3m_comm_H1m m hm]

theorem x₃_not_mem_CE : E.x₃ ∉ E.CE := by
  intro h
  obtain ⟨e, he, hne⟩ := x3m_not_cent
  apply hne
  apply E.injective
  rw [map_mul, map_mul]
  exact (E.mem_CE.1 h (E.ι e) ⟨e, he, rfl⟩).symm

theorem x₃_not_mem_HH : E.x₃ ∉ E.HH := fun h => E.x₃_not_mem_CE (E.HH_le_CE h)

theorem x₃_centralizes_HH [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {c : G}
    (hcs : E.Acts false c s3) (hc3 : c ^ 3 = 1) (hEc : ∀ x ∈ E.E₀, x * c = c * x)
    (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W false, x * w = w * x)
    (e : ↥E.HH ≃* alternatingGroup (Fin 6)) : ∀ y ∈ E.HH, E.x₃ * y = y * E.x₃ := by
  have hT₂H : E.T₂ ≤ E.HH := E.T₂_le_HH hcs hc3 hEc hEW
  let γ : MulAut ↥E.HH := CFSG.Quasithin.conjAct E.HH ⟨E.x₃, E.x₃_mem_normalizer_HH⟩
  have hγ3 : γ ^ 3 = 1 := by
    show (CFSG.Quasithin.conjAct E.HH) ⟨E.x₃, E.x₃_mem_normalizer_HH⟩ ^ 3 = 1
    rw [← map_pow]
    have : (⟨E.x₃, E.x₃_mem_normalizer_HH⟩ : Subgroup.normalizer (E.HH : Set G)) ^ 3 = 1 :=
      Subtype.ext E.x₃_cube
    rw [this, map_one]
  obtain ⟨h, hh⟩ := CFSG.Quasithin.A10.mem_inner_of_pow_three e hγ3
  have hγapply : ∀ y : ↥E.HH, ((γ y : ↥E.HH) : G) = E.x₃ * y * E.x₃⁻¹ := fun y => rfl
  have hhapply : ∀ y : ↥E.HH, ((MulAut.conj h y : ↥E.HH) : G) = h * y * (h : G)⁻¹ := fun y => rfl
  have hH₁ : ∀ y ∈ E.H₁, (h : G) * y = y * (h : G) := by
    intro y hy
    have hyH : y ∈ E.HH := E.H₁_le_HH hy
    have h1 := congrArg (fun φ : MulAut ↥E.HH => ((φ ⟨y, hyH⟩ : ↥E.HH) : G)) hh
    simp only [hγapply, hhapply] at h1
    have h2 : E.x₃ * y * E.x₃⁻¹ = y := by
      rw [E.x₃_comm_H₁ hy]
      group
    rw [h2] at h1
    calc (h : G) * y = h * y * (h : G)⁻¹ * h := by group
      _ = y * h := by rw [h1]
  have htz : (h : G) * E.tz = E.tz * (h : G) := hH₁ E.tz ⟨t0', V2_le_H1m t0'_mem_V2, rfl⟩
  have hT₂ : (h : G) ∈ E.T₂ := E.mem_T₂_of_centralizes_tz hEven hT hM hT₂H h.2 htz
  obtain ⟨w, hw, hwh⟩ := hT₂
  have hw1 : w = 1 := by
    apply T2h_cent_H1m w hw
    intro y hy
    apply E.injective
    rw [map_mul, map_mul, hwh]
    exact hH₁ (E.ι y) ⟨y, hy, rfl⟩
  have h1 : (h : G) = 1 := by rw [← hwh, hw1, map_one]
  have hγ1 : γ = 1 := by
    rw [← hh]
    have : h = 1 := Subtype.ext h1
    rw [this, map_one]
  intro y hy
  have h2 := congrArg (fun φ : MulAut ↥E.HH => ((φ ⟨y, hy⟩ : ↥E.HH) : G)) hγ1
  simp only [hγapply] at h2
  have h3 : E.x₃ * y * E.x₃⁻¹ = y := h2
  calc E.x₃ * y = E.x₃ * y * E.x₃⁻¹ * E.x₃ := by group
    _ = y * E.x₃ := by rw [h3]

end Emb

end CFSG.Quasithin.A10

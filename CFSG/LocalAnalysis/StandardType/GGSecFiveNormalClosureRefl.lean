module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

section Forced

theorem ggAutomizer_subgroupOf_normal_of_normalizer_le {H X Bs : Subgroup G} (hXH : X ≤ H)
    (hN : Subgroup.normalizer (Bs : Set G) ⊓ H ≤ Subgroup.normalizer (X : Set G)) :
    ((ggAutomizer X Bs).subgroupOf (ggAutomizer H Bs)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (ggAutomizer_mono Bs hXH)]
  intro ψ φ hψ hφ
  obtain ⟨n, hnX, hnBs, hnψ⟩ := mem_ggAutomizer_iff.mp hψ
  obtain ⟨g, hgH, hgBs, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
  have hgX : g ∈ Subgroup.normalizer (X : Set G) := hN ⟨hgBs, hgH⟩
  refine mem_ggAutomizer_iff.mpr ⟨g * n * g⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgX n).mp hnX
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgBs hnBs) (Subgroup.inv_mem _ hgBs)
  · intro b
    simp only [MulAut.mul_apply]
    rw [hgφ, hnψ, inv_apply_of_forall hgφ]
    group

theorem ggAutomizer_conj_mem_of_normalizer_le {H X J Bs : Subgroup G} (hXH : X ≤ H) (hJX : J ≤ X)
    (hN : Subgroup.normalizer (Bs : Set G) ⊓ H ≤ Subgroup.normalizer (X : Set G))
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer H Bs) (hψ : ψ ∈ ggAutomizer J Bs) :
    φ * ψ * φ⁻¹ ∈ ggAutomizer X Bs := by
  have hnormal := ggAutomizer_subgroupOf_normal_of_normalizer_le (H := H) (X := X) hXH hN
  exact (Subgroup.normal_subgroupOf_iff (ggAutomizer_mono Bs hXH)).mp hnormal ψ φ
    (ggAutomizer_mono Bs hJX hψ) hφ

theorem mem_normalizer_ggAutomizer_of_mem_ggInduced_of_normal {H Bs : Subgroup G}
    [H.Normal] {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs) :
    φ ∈ Subgroup.normalizer (ggAutomizer H Bs : Set (MulAut ↥Bs)) := by
  classical
  have hN : Subgroup.normalizer (Bs : Set G) ⊓ ⊤ ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.normalizer_eq_top H]
    exact le_top
  have hφA : φ ∈ ggAutomizer ⊤ Bs := Subgroup.subset_closure hφ
  refine Subgroup.mem_normalizer_iff.mpr fun ψ => ⟨fun hψ => ?_, fun hψ => ?_⟩
  · exact ggAutomizer_conj_mem_of_normalizer_le (H := ⊤) (X := H) (J := H) le_top le_rfl hN
      hφA hψ
  · have h := ggAutomizer_conj_mem_of_normalizer_le (H := ⊤) (X := H) (J := H)
      le_top le_rfl hN (Subgroup.inv_mem _ hφA) hψ
    convert h using 1
    group

theorem mem_ggAutomizer_centralizer_of_apply_eq {Bs : Subgroup G} {z : G} (hz : z ∈ Bs)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (hfix : φ ⟨z, hz⟩ = ⟨z, hz⟩) :
    φ ∈ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hφ
  have hgz : g * z = z * g := by
    have h1 : g * z * g⁻¹ = z := by
      have h2 := hg ⟨z, hz⟩
      rw [hfix] at h2
      simpa using h2.symm
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h1]
  exact mem_ggAutomizer_iff.mpr
    ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hgz, hgN, hg⟩

theorem ggAutomizer_orbit_le_of_normalizer_le {Bs X J : Subgroup G} {z : G} (hz : z ∈ Bs)
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) (hJX : J ≤ X)
    (hN : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (X : Set G))
    {R S : Set (MulAut ↥Bs)} (hR : ∀ r ∈ R, r ∈ ggAutomizer ⊤ Bs ∧ r ⟨z, hz⟩ = ⟨z, hz⟩)
    (hS : S ⊆ (ggAutomizer J Bs : Set (MulAut ↥Bs))) :
    {ψ | ∃ r ∈ Subgroup.closure R, ∃ s ∈ S, ψ = r * s * r⁻¹} ⊆
        (ggAutomizer X Bs : Set (MulAut ↥Bs)) ∧
      Subgroup.closure {ψ | ∃ r ∈ Subgroup.closure R, ∃ s ∈ S, ψ = r * s * r⁻¹} ≤
        ggAutomizer X Bs := by
  have hclosureR : Subgroup.closure R ≤ ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs := by
    refine (Subgroup.closure_le (ggAutomizer (Subgroup.centralizer ({z} : Set G)) Bs)).mpr
      fun r hr => ?_
    exact mem_ggAutomizer_centralizer_of_apply_eq hz (hR r hr).1 (hR r hr).2
  have hmain : ∀ r ∈ Subgroup.closure R, ∀ s ∈ S, r * s * r⁻¹ ∈ ggAutomizer X Bs := by
    intro r hr s hs
    exact ggAutomizer_conj_mem_of_normalizer_le (H := Subgroup.centralizer ({z} : Set G))
      hXz hJX hN (hclosureR hr) (hS hs)
  refine ⟨?_, (Subgroup.closure_le (ggAutomizer X Bs)).mpr ?_⟩
  · rintro ψ ⟨r, hr, s, hs, rfl⟩
    exact hmain r hr s hs
  · rintro ψ ⟨r, hr, s, hs, rfl⟩
    exact hmain r hr s hs

end Forced

end CFSG.StandardType

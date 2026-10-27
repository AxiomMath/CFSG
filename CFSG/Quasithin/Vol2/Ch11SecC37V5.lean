module

public import CFSG.Quasithin.Vol2.Ch11SecC37V4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem eq_conj (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {g' : G}
    (s' : Set37 T L I n V₁ H g') :
    conjSubgroup (fsuV T I) g = conjSubgroup (fsuV T I) g' := by
  have hG2 := i.hKF.2.2.2
  obtain ⟨u, hu, huA⟩ := s.exists_u
  have hc := s.comm_iff i.hAS i.hF i.h1102 hG2 i.h1122 i.h1134 i.h1135 i.h1136 hu
  have hc' := s'.comm_iff i.hAS i.hF i.h1102 hG2 i.h1122 i.h1134 i.h1135 i.h1136 hu
  have huA' : u ∉ Subgroup.centralizer (conjSubgroup (fsuV T I) g' : Set G) := by
    intro huC
    apply huA
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨t, ht, hta⟩ := (hc _).mp ⟨a, ha, rfl⟩
    obtain ⟨a', ha', hta'⟩ := (hc' _).mpr ⟨t, ht, rfl⟩
    have h1 : u * a' * u⁻¹ * a'⁻¹ = 1 := by
      rw [← Subgroup.mem_centralizer_iff.mp huC a' ha']
      group
    have h2 : u * a * u⁻¹ * a⁻¹ = 1 := by rw [hta, hta', h1]
    calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * (u * a) := by group
      _ = u * a := by rw [h2, inv_one, one_mul]
  obtain ⟨y₁, hy₁A, hy₁P⟩ := s.point_of_u i hTVS hTVP hVL hu huA
  obtain ⟨y₂, hy₂A, hy₂P⟩ := s'.point_of_u i hTVS hTVP hVL hu huA'
  have hP : ∀ x : G, y₁⁻¹ * x * y₁ ∈ V₁ ↔ y₂⁻¹ * x * y₂ ∈ V₁ := fun x => by
    rw [← hy₁P, ← hy₂P, hc, hc']
  have hcN : y₂⁻¹ * y₁ ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have := hP (y₁ * v * y₁⁻¹)
    have e1 : y₁⁻¹ * (y₁ * v * y₁⁻¹) * y₁ = v := by group
    have e2 : y₂⁻¹ * (y₁ * v * y₁⁻¹) * y₂ = y₂⁻¹ * y₁ * v * (y₂⁻¹ * y₁)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  have hcV := ((i.h1134 G T L I n V₁ H g s.hyp s.hV₁ s.h31 s.hnot s.hAT s.hAC).2.2.2 hcN).2
  ext x
  rw [hy₁A, hy₂A]
  have e : y₂⁻¹ * x * y₂ = (y₂⁻¹ * y₁) * (y₁⁻¹ * x * y₁) * (y₂⁻¹ * y₁)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hcV _

theorem T_le_normalizer_A (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    T ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  intro t ht
  have hHV : t ∈ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_VZ T H (s.T_le ht)
  have hmem : ∀ x, x ∈ conjSubgroup (fsuV T I) (g * t⁻¹) ↔
      t⁻¹ * x * t ∈ conjSubgroup (fsuV T I) g := fun x => by
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have e : g * t⁻¹ * x * (g * t⁻¹)⁻¹ = g * (t⁻¹ * x * t) * g⁻¹ := by group
    rw [e]
  have s' : Set37 T L I n V₁ H (g * t⁻¹) :=
    { hyp := s.hyp, hV₁ := s.hV₁, h31 := s.h31, hnot := s.hnot
      hAT := fun x hx => by
        have := s.hAT ((hmem x).mp hx)
        have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
        rw [e]
        exact T.mul_mem (T.mul_mem ht this) (T.inv_mem ht)
      hAC := fun hle => s.hAC fun a ha => by
        have h1 : t * a * t⁻¹ ∈ conjSubgroup (fsuV T I) (g * t⁻¹) := by
          rw [hmem]
          have e : t⁻¹ * (t * a * t⁻¹) * t = a := by group
          rw [e]
          exact ha
        have h2 := hle h1
        rw [Subgroup.mem_centralizer_iff] at h2 ⊢
        intro w hw
        have hw' : t * w * t⁻¹ ∈ VZ T H := (Subgroup.mem_normalizer_iff.mp hHV w).mp hw
        have h3 := h2 _ hw'
        have : t * (w * a) * t⁻¹ = t * (a * w) * t⁻¹ := by
          calc t * (w * a) * t⁻¹ = t * w * t⁻¹ * (t * a * t⁻¹) := by group
            _ = t * a * t⁻¹ * (t * w * t⁻¹) := h3
            _ = t * (a * w) * t⁻¹ := by group
        exact mul_left_cancel (mul_right_cancel this) }
  have heq := s.eq_conj i hTVS hTVP hVL s'
  have hA : ∀ x, x ∈ conjSubgroup (fsuV T I) g ↔ t⁻¹ * x * t ∈ conjSubgroup (fsuV T I) g :=
    fun x => by rw [← hmem, ← heq]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hA (t * x * t⁻¹)]
  have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
  rw [e]

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC

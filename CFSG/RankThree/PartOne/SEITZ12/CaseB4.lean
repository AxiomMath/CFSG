module

public import CFSG.RankThree.PartOne.SEITZ12.CaseB2

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open Subgroup

variable {G : Type*} [Group G]

theorem phi4B_isPGroup_of_pow {H : Subgroup G} {k : ℕ} (hH : ∀ x ∈ H, x ^ (2 ^ k) = 1) :
    IsPGroup 2 H := fun x => ⟨k, Subtype.ext (by simpa using hH x.1 x.2)⟩

namespace phi4B_Ctx

variable {D X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ} {cls : G → Prop}

theorem B4 [Finite D] (h : phi4B_Ctx D X₂ S₂ Z₂ t q cls) :
    ∃ d ∈ D, ∃ x ∈ conjSub Z₂ t, x ≠ 1 ∧ d * t * d⁻¹ = x := by
  have hc := h.core
  obtain ⟨y, hyD, hyy⟩ := h.sq
  have hy4 : y ^ 4 = 1 := by rw [phi4B_pow_four, hyy]; exact hc.t_sq
  have hy : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hy4)
  obtain ⟨d, hdD, hdS⟩ := phi4B_sylow_conj h.S_le_D hc.isPGroup_S
    (fun T hT hTp hST => h.B2 hT hTp hST) hyD hy
  set u := d * y * d⁻¹ with hu
  have huu : u * u = d * t * d⁻¹ := by
    rw [← hyy, hu]
    group
  have hΩ : d * t * d⁻¹ ∈ phi4B_Om Z₂ t := by
    rw [← huu]
    rcases hdS with hB | ⟨b, hb, hub⟩
    · exact hc.B0_sq_mem_Om hB
    · have hm : u * u ∈ phi4B_B0 S₂ t := by
        have e : u * u = b * (t * b * t) := by rw [hub]; simp only [mul_assoc]
        rw [e]
        exact mul_mem hb (hc.tau_B0 hb)
      apply hc.inv_mem_Om hm
      rw [huu]
      calc d * t * d⁻¹ * (d * t * d⁻¹) = d * (t * t) * d⁻¹ := by group
        _ = 1 := by rw [hc.t_sq]; group
  have hne : d * t * d⁻¹ ≠ 1 := by
    intro e
    apply hc.t_ne_one
    calc t = d⁻¹ * (d * t * d⁻¹) * d := by group
      _ = 1 := by rw [e]; group
  have hcl : cls (d * t * d⁻¹) := h.cls_conj d hdD t h.cls_t
  rcases h.pure_of_cls hΩ hcl with h1 | h2
  · exact ⟨d, hdD, d * t * d⁻¹, h1, hne, rfl⟩
  · refine ⟨t * d, mul_mem h.tD hdD, t * (d * t * d⁻¹) * t, phi4B_tau_mem hc.t_sq h2,
      hc.tau_ne_one hne, ?_⟩
    rw [mul_inv_rev, phi4B_inv_eq hc.t_sq]
    simp only [mul_assoc]

end phi4B_Ctx

end CFSG.RankThree.PartOne.SEITZ12

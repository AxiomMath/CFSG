module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSet
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSyl
import CFSG.GF2Type.Smith1979.CaseIIExclL52

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G]

theorem cen_inv (x : G) : Cen x⁻¹ = Cen x := by
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => Commute.inv_right_iff.mp h, fun h => Commute.inv_right h⟩

theorem conjBy_cen_inf (n x y : G) :
    conjBy n (Cen x ⊓ Cen y) = Cen (n * x * n⁻¹) ⊓ Cen (n * y * n⁻¹) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · calc n * w * n⁻¹ * (n * x * n⁻¹) = n * (w * x) * n⁻¹ := by group
        _ = n * (x * w) * n⁻¹ := by rw [h1]
        _ = n * x * n⁻¹ * (n * w * n⁻¹) := by group
    · calc n * w * n⁻¹ * (n * y * n⁻¹) = n * (w * y) * n⁻¹ := by group
        _ = n * (y * w) * n⁻¹ := by rw [h2]
        _ = n * y * n⁻¹ * (n * w * n⁻¹) := by group
  · rintro ⟨h1, h2⟩
    refine ⟨n⁻¹ * z * n, ⟨?_, ?_⟩, by group⟩
    · calc n⁻¹ * z * n * x = n⁻¹ * (z * (n * x * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * x * n⁻¹) * z) * n := by rw [h1]
        _ = x * (n⁻¹ * z * n) := by group
    · calc n⁻¹ * z * n * y = n⁻¹ * (z * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * y * n⁻¹) * z) * n := by rw [h2]
        _ = y * (n⁻¹ * z * n) := by group

theorem cen_beta_gamma (b₁ b₂ : G) :
    Cen (b₁ * b₂) ⊓ Cen (b₁ ^ 2 * b₂) = Cen b₁ ⊓ Cen b₂ := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hb₁ : z * b₁ = b₁ * z := by
      have hc : Commute z (b₁ ^ 2 * b₂ * (b₁ * b₂)⁻¹) :=
        Commute.mul_right h2 (Commute.inv_right h1)
      have e : b₁ ^ 2 * b₂ * (b₁ * b₂)⁻¹ = b₁ := by group
      rw [e] at hc
      exact hc
    refine ⟨hb₁, ?_⟩
    have hc : Commute z (b₁⁻¹ * (b₁ * b₂)) := Commute.mul_right (Commute.inv_right hb₁) h1
    have e : b₁⁻¹ * (b₁ * b₂) = b₂ := by group
    rw [e] at hc
    exact hc
  · rintro ⟨h1, h2⟩
    exact ⟨Commute.mul_right h1 h2, Commute.mul_right (Commute.pow_right h1 2) h2⟩

variable [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}

theorem lay_H_cen (h4 : FF79Sec4 b J B b₁ b₂) (x : G) :
    Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen x) = Lay (Cen (b₁ * b₂) ⊓ Cen x) := by
  refine (lay_eq_of_perfect (C := OUp 3 (Cen (b₁ * b₂)) ⊓ Cen x) (Y := Cen (b₁ * b₂) ⊓ Cen x)
    (inf_le_inf_right _ (OUp_le _)) ?_ ?_).symm
  · intro y hy c hc
    exact ⟨OUp_conj_mem hy.1 hc.1,
      (Cen x).mul_mem ((Cen x).mul_mem hy.2 hc.2) ((Cen x).inv_mem hy.2)⟩
  · intro S hS hP
    exact le_inf (perfect_le_OUp_cen_beta h4 (hS.trans inf_le_left) hP) (hS.trans inf_le_right)

theorem cen_le_nor_J (h4 : FF79Sec4 b J B b₁ b₂) (hJ5 : FF79_JL5) : Cen b ≤ Nor J := by
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two
    (hJ5 G b J h4.hyp)
  exact (setup_of_sec4 h4 e).cen_le_nor

theorem K_eq (h4 : FF79Sec4 b J B b₁ b₂) (hJ5 : FF79_JL5) (h41 : FF79_4_1) :
    Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen b) = Lay (J ⊓ Cen (b₁ * b₂)) := by
  rw [lay_H_cen h4, lay_eq_lay_J_inf h4 hJ5 h41 (inf_le_right : Cen (b₁ * b₂) ⊓ Cen b ≤ Cen b)]
  congr 1
  ext z
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, h4.hyp.std.1 h.1⟩⟩

theorem L_conj (h4 : FF79Sec4 b J B b₁ b₂) (hJ5 : FF79_JL5) (h41 : FF79_4_1) :
    ∃ n : G, n * b * n⁻¹ = b₁ ∧
      conjBy n (Lay (OUp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ ^ 2 * b₂))) = Lay (J ⊓ Cen b₂) := by
  obtain ⟨n, -, hn1, hn2, hn3⟩ := h4.mono.2.2.2.2.1
  refine ⟨n, hn1, ?_⟩
  rw [lay_H_cen h4, cen_beta_gamma, ← lay_conjBy, conjBy_cen_inf, hn2, hn3,
    lay_eq_lay_J_inf h4 hJ5 h41 (inf_le_left : Cen b ⊓ Cen b₂ ≤ Cen b)]
  congr 1
  ext z
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h4.hyp.std.1 h.1, h.2⟩⟩

theorem sec4_swap (h4 : FF79Sec4 b J B b₁ b₂) :
    ∃ n ∈ Cen b, n * b₁ * n⁻¹ = b₂ := by
  obtain ⟨c, -, hc1, hc2, hc3⟩ := h4.mono.2.2.2.2.2
  obtain ⟨a, -, ha1, ha2, ha3⟩ := h4.mono.2.2.2.2.1
  have key : ∀ x y z w : G, c⁻¹ * x * c = y → a * y * a⁻¹ = z → c * z * c⁻¹ = w →
      (c * a * c⁻¹) * x * (c * a * c⁻¹)⁻¹ = w := by
    intro x y z w h1 h2 h3
    rw [← h3, ← h2, ← h1]
    group
  have ci : ∀ x y : G, c * x * c⁻¹ = y → c⁻¹ * y * c = x := by
    intro x y h
    rw [← h]
    group
  have hb : (c * a * c⁻¹) * b * (c * a * c⁻¹)⁻¹ = b := key b b₂ b₂ b (ci _ _ hc3) ha3 hc3
  refine ⟨c * a * c⁻¹, ?_, key b₁ b b₁ b₂ (ci _ _ hc1) ha1 hc2⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.mp hb

theorem typ_swap (h4 : FF79Sec4 b J B b₁ b₂) (hJ5 : FF79_JL5) (a p f : ℕ) :
    IsLnq a p f (Lay (J ⊓ Cen b₂)) ↔ IsLnq a p f (Lay (J ⊓ Cen b₁)) := by
  obtain ⟨n, hn, hnb⟩ := sec4_swap h4
  have h1 := conjBy_inf_cen (cen_le_nor_J h4 hJ5 hn) b₁
  rw [hnb] at h1
  rw [← h1, lay_conjBy, isLnq_conjBy_iff]

end CFSG.RankThree.PartTwo.Sec21.FF79

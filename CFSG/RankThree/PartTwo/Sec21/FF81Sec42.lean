module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec42Q
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79KStmt
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open Q42

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

theorem conj_inv_of_conj {a x y : G} (h : a * x * a⁻¹ = y) : a⁻¹ * y * a = x := by
  rw [← h]; group

section Sec4

variable (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀)
include h4

theorem FF81Sec4.levi1 (hLevi : KF_Sp6Levi) :
    L ⊓ Cen (b₁ * b₂) ≤ Nor (Subgroup.closure {b₁, b₂}) := by
  have hS : ({b₃, b₁, b₂} : Set G) = {b₁, b₂, b₃} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hS6 : ({b₃, b₃⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) = {b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  exact (hLevi G L h4.basis.hyp.model b₃ b₁ b₂ h4.basis.hb₃ h4.basis.hb₁ h4.basis.hb₂
    (by rw [hS]; exact h4.basis.elem) (by rw [hS]; exact h4.basis.selfcen)
    (by rw [hS, hS6]; exact h4.basis.monoL_stab)).2

theorem FF81Sec4.conc₀ (hFS : Prop2At (Q (b * b₂))) (hLevi : KF_Sp6Levi) :
    Conc (b * b₂) (Subgroup.closure {b, b₂}) := by
  obtain ⟨⟨J, hJ, ⟨φ⟩, hb₁J, hb₃J, hJdec⟩, hL23⟩ :=
    hLevi G L h4.basis.hyp.model b₁ b₂ b₃ h4.basis.hb₁ h4.basis.hb₂ h4.basis.hb₃ h4.basis.elem
      h4.basis.selfcen h4.basis.monoL_stab
  have hL3 : L ⊓ Cen (b₃ * b₂) ≤ Nor (Subgroup.closure {b₃, b₂}) := by
    rw [← h4.basis.b_facts.2.2.2.2.2, Set.pair_comm]; exact hL23
  obtain ⟨t, ht2, htb, htb₂, htJ⟩ := h4.exists_t hJ φ hb₁J hb₃J hJdec
  obtain ⟨-, -, -, ⟨τ₁, -, hτ0, hτ1, hτ2, hτ3⟩, ⟨c, -, hc0, hc1, hc2, hc3⟩⟩ := h4.caseI.1.1
  have hτ₃b : (c⁻¹ * τ₁ * c) * b * (c⁻¹ * τ₁ * c)⁻¹ = b₃ := by
    calc (c⁻¹ * τ₁ * c) * b * (c⁻¹ * τ₁ * c)⁻¹ = c⁻¹ * (τ₁ * (c * b * c⁻¹) * τ₁⁻¹) * c := by group
      _ = b₃ := by rw [hc0, hτ1, conj_inv_of_conj hc3]
  have hτ₃c : (c⁻¹ * τ₁ * c) * b₃ * (c⁻¹ * τ₁ * c)⁻¹ = b := by
    calc (c⁻¹ * τ₁ * c) * b₃ * (c⁻¹ * τ₁ * c)⁻¹ = c⁻¹ * (τ₁ * (c * b₃ * c⁻¹) * τ₁⁻¹) * c := by
          group
      _ = b := by rw [hc3, hτ0, conj_inv_of_conj hc0]
  have hτ₃2 : (c⁻¹ * τ₁ * c) * b₂ * (c⁻¹ * τ₁ * c)⁻¹ = b₂ := by
    calc (c⁻¹ * τ₁ * c) * b₂ * (c⁻¹ * τ₁ * c)⁻¹ = c⁻¹ * (τ₁ * (c * b₂ * c⁻¹) * τ₁⁻¹) * c := by
          group
      _ = b₂ := by rw [hc2, hτ3, conj_inv_of_conj hc2]
  exact Data42.conc (J := J) (t := t) (τ₁ := τ₁) (τ₃ := c⁻¹ * τ₁ * c)
    ⟨h4, hJ, ⟨φ⟩, hb₁J, hb₃J, hJdec, h4.levi1 hLevi, hL3, ht2, htb, htb₂, htJ, hτ0, hτ1, hτ2,
      hτ₃b, hτ₃c, hτ₃2⟩ hFS

theorem FF81Sec4.conc4_2 (hFS : Prop2At (Q (b * b₂))) (hLevi : KF_Sp6Levi) :
    FF81Conc4_2 b₂ b₃ := by
  have h0 := h4.conc₀ hFS hLevi
  obtain ⟨-, -, -, -, ⟨c, -, hc0, -, hc2, -⟩⟩ := h4.caseI.1.1
  obtain ⟨-, -, -, ⟨ι, -, hι0, hι1, -, -⟩, ⟨p, -, hp0, hp1, -, hp3⟩, ⟨q, -, hq0, hq1, -, -⟩⟩ :=
    h4.basis.mono
  have hgb : (p * c) * b * (p * c)⁻¹ = b₂ := by
    calc (p * c) * b * (p * c)⁻¹ = p * (c * b * c⁻¹) * p⁻¹ := by group
      _ = b₂ := by rw [hc0, hp1]
  have hgb₂ : (p * c) * b₂ * (p * c)⁻¹ = b₃ := by
    calc (p * c) * b₂ * (p * c)⁻¹ = p * (c * b₂ * c⁻¹) * p⁻¹ := by group
      _ = b₃ := by rw [hc2, hp3]
  have hιb : (q * ι * q⁻¹) * b * (q * ι * q⁻¹)⁻¹ = b := by
    calc (q * ι * q⁻¹) * b * (q * ι * q⁻¹)⁻¹ = q * (ι * (q⁻¹ * b * q) * ι⁻¹) * q⁻¹ := by group
      _ = b := by rw [conj_inv_of_conj hq0, hι0, hq0]
  have hιb₂ : (q * ι * q⁻¹) * b₂ * (q * ι * q⁻¹)⁻¹ = b₂⁻¹ := by
    calc (q * ι * q⁻¹) * b₂ * (q * ι * q⁻¹)⁻¹ = q * (ι * (q⁻¹ * b₂ * q) * ι⁻¹) * q⁻¹ := by group
      _ = (q * b₁ * q⁻¹)⁻¹ := by rw [conj_inv_of_conj hq1, hι1]; group
      _ = b₂⁻¹ := by rw [hq1]
  have hx : ∀ g : G, g * (b * b₂) * g⁻¹ = (g * b * g⁻¹) * (g * b₂ * g⁻¹) := fun g => by group
  have h1 := conc_conj h0 (p * c)
  rw [hx, conjBy_closure_pair, hgb, hgb₂] at h1
  have h2 := conc_conj h0 (p * c * (q * ι * q⁻¹))
  have hg'b : (p * c * (q * ι * q⁻¹)) * b * (p * c * (q * ι * q⁻¹))⁻¹ = b₂ := by
    rw [show (p * c * (q * ι * q⁻¹)) * b * (p * c * (q * ι * q⁻¹))⁻¹ =
      (p * c) * ((q * ι * q⁻¹) * b * (q * ι * q⁻¹)⁻¹) * (p * c)⁻¹ by group, hιb, hgb]
  have hg'b₂ : (p * c * (q * ι * q⁻¹)) * b₂ * (p * c * (q * ι * q⁻¹))⁻¹ = b₃⁻¹ := by
    rw [show (p * c * (q * ι * q⁻¹)) * b₂ * (p * c * (q * ι * q⁻¹))⁻¹ =
      (p * c) * ((q * ι * q⁻¹) * b₂ * (q * ι * q⁻¹)⁻¹) * (p * c)⁻¹ by group, hιb₂]
    rw [show (p * c) * b₂⁻¹ * (p * c)⁻¹ = ((p * c) * b₂ * (p * c)⁻¹)⁻¹ by group, hgb₂]
  rw [hx, conjBy_closure_pair, hg'b, hg'b₂, closure_pair_inv] at h2
  rintro x (rfl | rfl)
  · exact h1
  · exact h2

theorem FF81Sec4.cen_ne_top : Cen (b * b₂) ≠ ⊤ := by
  intro htop
  have ht : t₀ ∈ Cen (b * b₂) := by rw [htop]; exact Subgroup.mem_top t₀
  have h1 : b * b₂ * t₀ = t₀ * (b * b₂) := (Subgroup.mem_centralizer_singleton_iff.mp ht).symm
  have h2 : b₂ * t₀ = t₀ * b₂ := Subgroup.mem_centralizer_iff.mp h4.ht₀L b₂ h4.basis.hb₂
  have h3 : t₀ * b = b⁻¹ * t₀ := by
    calc t₀ * b = t₀ * b * t₀⁻¹ * t₀ := by group
      _ = b⁻¹ * t₀ := by rw [h4.ht₀b]
  have hb : b = b⁻¹ := by
    have : b * (b₂ * t₀) = b⁻¹ * (b₂ * t₀) := by
      calc b * (b₂ * t₀) = b * b₂ * t₀ := by group
        _ = t₀ * b * b₂ := by rw [h1]; group
        _ = b⁻¹ * (t₀ * b₂) := by rw [h3]; group
        _ = b⁻¹ * (b₂ * t₀) := by rw [h2]
    exact mul_right_cancel this
  have h2b : b ^ 2 = 1 := by
    rw [sq]; nth_rewrite 2 [hb]; exact mul_inv_cancel b
  have := orderOf_dvd_of_pow_eq_one h2b
  rw [h4.basis.hyp.ord] at this
  norm_num at this

theorem FF81Sec4.kGroupNonab_Q (hKp : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) :
    KCore.KGroupNonab CFSG.Assembly.InCatalog (Q (b * b₂)) :=
  (KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hKp _
    h4.cen_ne_top).quotient CFSG.Assembly.inCatalog_isoInvariant _

end Sec4

theorem ff81_4_2K :
    KF_FS79Prop2K → KF_Sp6Levi → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G)
      (b₁ b₂ b₃ t₀ : G), CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
      FF81Sec4 b L B b₁ b₂ b₃ t₀ → FF81Conc4_2 b₂ b₃ := fun hFS hLevi _ _ _ _ _ _ _ _ _ _ hKp h4 =>
  h4.conc4_2 (hFS _ (h4.kGroupNonab_Q hKp)) hLevi

end CFSG.RankThree.PartTwo.Sec21.FF81

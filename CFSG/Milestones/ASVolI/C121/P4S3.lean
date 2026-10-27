module

public import CFSG.Milestones.ASVolI.C121.P4Glob
public import CFSG.Quasithin.Background.C1PackSL2
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped MatrixGroups Matrix

section S3

theorem burnsideC121_p4_sl2F2_gen : ∀ s x : C1Pack.SL2F2, s ^ 2 = 1 → s ≠ 1 →
    ∃ g h : C1Pack.SL2F2, x = g * s * g⁻¹ * (h * s * h⁻¹) ∨ x = g * s * g⁻¹ := by
  decide

variable {𝕎 : Type} [CommGroup 𝕎] [Finite 𝕎]

theorem burnsideC121_p4_le_stabSub_commV (G : Subgroup (MulAut 𝕎)) : G ≤ stabSub (commV G) := by
  intro g hg u
  have key : ∀ x ∈ G, ∀ v ∈ commV G, x v ∈ commV G := by
    intro x hx v hv
    induction hv using Subgroup.closure_induction with
    | mem v hv =>
      obtain ⟨y, hy, z, rfl⟩ := hv
      have h1 : x (y z * z⁻¹) = (x * y * x⁻¹) (x z) * (x z)⁻¹ := by
        simp [map_mul, map_inv]
      rw [h1]
      exact Subgroup.subset_closure ⟨_, G.mul_mem (G.mul_mem hx hy) (G.inv_mem hx), _, rfl⟩
    | one => rw [map_one]; exact (commV G).one_mem
    | mul a b _ _ ha hb => rw [map_mul]; exact (commV G).mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact (commV G).inv_mem ha
  refine ⟨fun hu => ?_, key g hg u⟩
  have := key g⁻¹ (G.inv_mem hg) _ hu
  simpa using this

theorem burnsideC121_p4_le_stabSub_bot (G : Subgroup (MulAut 𝕎)) :
    G ≤ stabSub (⊥ : Subgroup 𝕎) := by
  intro g _ u
  simp

theorem burnsideC121_p4_s3_natural (h2 : ∀ w : 𝕎, w ^ 2 = 1) {G : Subgroup (MulAut 𝕎)}
    (hG6 : Nat.card G = 6)
    (hO2 : ∀ Q : Subgroup (MulAut 𝕎), Q ≤ G → (Q.subgroupOf G).Normal → IsPGroup 2 Q → Q = ⊥)
    (hFF : IsFFModule G) :
    ∃ θ : ↥G ≃* SL(2, ZMod 2), ∃ β : 𝕎 →* Multiplicative (Fin 2 → ZMod 2),
      Function.Surjective β ∧ β.ker = fixV G ∧
      ∀ (g : ↥G) (w : 𝕎), β ((g : MulAut 𝕎) w) =
        Multiplicative.ofAdd ((θ g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (β w)) := by
  classical
  have hsolv : Group.IsSolvable ↥G :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hG6]; norm_num)
  obtain ⟨𝓗, hle, hJ, -, -, -, -, hnat, -⟩ := B1_8 h2 hsolv hO2 hFF
  obtain ⟨A₀, hA₀⟩ := ((B1_4_5 h2 G).out 1 2).1 hFF
  have hJ1 : ffJ G ≠ ⊥ := by
    intro h
    apply hA₀.2.1
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le A₀ hA₀ le_rfl
  obtain ⟨H, hH⟩ : 𝓗.Nonempty := by
    rcases Finset.eq_empty_or_nonempty 𝓗 with h | h
    · exfalso
      apply hJ1
      rw [hJ, h]
      simp
    · exact h
  have hHG : H = G := by
    obtain ⟨e, -, -⟩ := hnat H hH
    refine Subgroup.eq_of_le_of_card_ge (hle H hH) ?_
    rw [hG6, Nat.card_congr e.toEquiv, C1Pack.card_sl2F2]
  have hnatG : ActsAsNaturalL2 G (commV G) := hHG ▸ hnat H hH
  obtain ⟨e, φ, hφ⟩ := hnatG
  have hG₁ : G ≤ stabSub (commV G) := burnsideC121_p4_le_stabSub_commV G
  have hG₂ : G ≤ stabSub (⊥ : Subgroup 𝕎) := burnsideC121_p4_le_stabSub_bot G
  have hbot : (⊥ : Subgroup 𝕎).subgroupOf (commV G) = ⊥ := Subgroup.bot_subgroupOf _
  let eM : Sec (commV G) ⊥ ≃* Multiplicative (Fin 2 → ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans φ
  have heM : ∀ u : ↥(commV G), eM (QuotientGroup.mk u) = φ u := fun u => rfl
  have he : ∀ (g : ↥G) (x : Sec (commV G) ⊥), eM (B5.secHom G hG₁ hG₂ g x) =
      Multiplicative.ofAdd ((e g : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (eM x)) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [B5.secHom_mk, heM, heM]
      exact hφ g u _
  obtain ⟨A, hAG, hA1, hAe, hAFF⟩ := hFF
  refine ⟨e, burnsideC121_p4_global_of_section h2 le_rfl (by simp) e bot_le hG₁ hG₂ eM he hAG hA1
    hAe hAFF ?_⟩
  intro N hNG hN hAN
  refine le_antisymm hNG fun g hg => ?_
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hs2 : (e ⟨a, hAG haA⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, hAG haA⟩ : ↥G) ^ 2 = 1 := Subtype.ext (by simpa using hAe.2 a haA)
    rw [this, map_one]
  have hs1 : e ⟨a, hAG haA⟩ ≠ 1 := by
    intro h
    have : (⟨a, hAG haA⟩ : ↥G) = 1 := e.injective (h.trans (map_one e).symm)
    exact ha1' (congrArg Subtype.val this)
  obtain ⟨g₁, h₁, hx⟩ := burnsideC121_p4_sl2F2_gen (e ⟨a, hAG haA⟩) (e ⟨g, hg⟩) hs2 hs1
  have hconj : ∀ k : C1Pack.SL2F2, ((e.symm k : ↥G) : MulAut 𝕎) * a *
      ((e.symm k : ↥G) : MulAut 𝕎)⁻¹ ∈ N :=
    fun k => hN _ (e.symm k).2 a (hAN haA)
  rcases hx with hx | hx
  · have : (⟨g, hg⟩ : ↥G) = e.symm g₁ * ⟨a, hAG haA⟩ * (e.symm g₁)⁻¹ *
        (e.symm h₁ * ⟨a, hAG haA⟩ * (e.symm h₁)⁻¹) := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hx
    have h3 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [h3]
    exact N.mul_mem (hconj g₁) (hconj h₁)
  · have : (⟨g, hg⟩ : ↥G) = e.symm g₁ * ⟨a, hAG haA⟩ * (e.symm g₁)⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hx
    have h3 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [h3]
    exact hconj g₁

end S3

end CFSG.Quasithin

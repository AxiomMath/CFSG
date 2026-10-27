module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderField
public import CFSG.Quasithin.Background.BlueprintB2Basic

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Offender

open scoped commutatorElement Pointwise

namespace PairedSeeds

variable {H : Type*} [Group H]

section Simple

variable {S₁ S₂ : Type*} [Group S₁] [Group S₂]

theorem exists_mul_ne_mul (hS : ¬ IsMulCommutative S₁) : ∃ x y : S₁, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  exact hS ⟨⟨hcon⟩⟩

theorem exists_not_commute [IsSimpleGroup S₁] (hS : ¬ IsMulCommutative S₁) {a : S₁}
    (ha : a ≠ 1) : ∃ c : S₁, a * c ≠ c * a := by
  by_contra hcon
  push Not at hcon
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S₁) with h | h
  · have hac : a ∈ center S₁ := mem_center_iff.mpr fun g => (hcon g).symm
    rw [h, mem_bot] at hac
    exact ha hac
  · exact hS ⟨⟨fun x y => by
      have hy : y ∈ center S₁ := h ▸ mem_top y
      exact mem_center_iff.mp hy x⟩⟩

theorem inl_mem_of_normal [IsSimpleGroup S₁] (hS : ¬ IsMulCommutative S₁)
    {N : Subgroup (S₁ × S₂)} (hN : N.Normal) {a : S₁} {b : S₂} (hab : (a, b) ∈ N) (ha : a ≠ 1)
    (s : S₁) : (s, 1) ∈ N := by
  obtain ⟨c, hc⟩ := exists_not_commute hS ha
  have hN1 : (N.comap (MonoidHom.inl S₁ S₂)).Normal := hN.comap _
  have hmem : a * c * a⁻¹ * c⁻¹ ∈ N.comap (MonoidHom.inl S₁ S₂) := by
    rw [mem_comap, MonoidHom.inl_apply]
    have h2 := mul_mem hab (hN.conj_mem _ (inv_mem hab) (c, 1))
    convert h2 using 1
    ext <;> simp [mul_assoc]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl S₁ S₂)) with h | h
  · rw [h, mem_bot] at hmem
    exact absurd (calc a * c = (a * c * a⁻¹ * c⁻¹) * (c * a) := by group
      _ = c * a := by rw [hmem, one_mul]) hc
  · have hs : s ∈ N.comap (MonoidHom.inl S₁ S₂) := h ▸ mem_top s
    simpa using hs

theorem inr_mem_of_normal [IsSimpleGroup S₂] (hS : ¬ IsMulCommutative S₂)
    {N : Subgroup (S₁ × S₂)} (hN : N.Normal) {a : S₁} {b : S₂} (hab : (a, b) ∈ N) (hb : b ≠ 1)
    (t : S₂) : ((1 : S₁), t) ∈ N := by
  obtain ⟨c, hc⟩ := exists_not_commute hS hb
  have hN1 : (N.comap (MonoidHom.inr S₁ S₂)).Normal := hN.comap _
  have hmem : b * c * b⁻¹ * c⁻¹ ∈ N.comap (MonoidHom.inr S₁ S₂) := by
    rw [mem_comap, MonoidHom.inr_apply]
    have h2 := mul_mem hab (hN.conj_mem _ (inv_mem hab) (1, c))
    convert h2 using 1
    ext <;> simp [mul_assoc]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr S₁ S₂)) with h | h
  · rw [h, mem_bot] at hmem
    exact absurd (calc b * c = (b * c * b⁻¹ * c⁻¹) * (c * b) := by group
      _ = c * b := by rw [hmem, one_mul]) hc
  · have ht : t ∈ N.comap (MonoidHom.inr S₁ S₂) := h ▸ mem_top t
    simpa using ht

theorem normal_eq_ker_snd_or_ker_fst [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hS₁ : ¬ IsMulCommutative S₁) (hS₂ : ¬ IsMulCommutative S₂) {N : Subgroup (S₁ × S₂)}
    (hN : N.Normal) (h1 : N ≠ ⊥) (h2 : N ≠ ⊤) :
    N = (MonoidHom.snd S₁ S₂).ker ∨ N = (MonoidHom.fst S₁ S₂).ker := by
  have htop : ∀ {x : S₁} {y : S₂} {x' : S₁} {y' : S₂}, (x, y) ∈ N → x ≠ 1 → (x', y') ∈ N →
      y' ≠ 1 → False := fun hxy hx hxy' hy' => h2 (by
    rw [eq_top_iff]
    rintro ⟨s, t⟩ -
    have hst : ((s, t) : S₁ × S₂) = (s, 1) * (1, t) := by simp
    rw [hst]
    exact mul_mem (inl_mem_of_normal hS₁ hN hxy hx s) (inr_mem_of_normal hS₂ hN hxy' hy' t))
  rcases N.bot_or_exists_ne_one with h | ⟨⟨a, b⟩, hab, hne⟩
  · exact absurd h h1
  by_cases ha : a = 1
  · have hb : b ≠ 1 := fun hb => hne (by simp [ha, hb])
    right
    ext ⟨x, y⟩
    rw [MonoidHom.mem_ker, MonoidHom.coe_fst]
    refine ⟨fun hxy => ?_, fun hx => ?_⟩
    · by_contra hx
      exact htop hxy hx hab hb
    · change x = 1 at hx
      subst hx
      exact inr_mem_of_normal hS₂ hN hab hb y
  · left
    ext ⟨x, y⟩
    rw [MonoidHom.mem_ker, MonoidHom.coe_snd]
    refine ⟨fun hxy => ?_, fun hy => ?_⟩
    · by_contra hy
      exact htop hab ha hxy hy
    · change y = 1 at hy
      subst hy
      exact inl_mem_of_normal hS₁ hN hab ha x

end Simple

end PairedSeeds

open PairedSeeds

end CFSG.Quasithin.SteinbergBK

module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Prod
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin

namespace E217R4

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem conj_component {K₁ K₂ : Subgroup Γ} (hKn : (K₁ ⊔ K₂).Normal)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (h₁ : IsSimpleGroup ↥K₁)
    (hz₁ : ∀ x ∈ K₁, (∀ y ∈ K₁, y * x = x * y) → x = 1)
    (hz₂ : ∀ x ∈ K₂, (∀ y ∈ K₂, y * x = x * y) → x = 1) (hcard : Nat.card K₂ = Nat.card K₁)
    (s : Γ) :
    K₁.map (MulAut.conj s).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj s).toMonoidHom = K₂ := by
  set f : Γ →* Γ := (MulAut.conj s).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj s).injective
  set L : Subgroup Γ := K₁.map f with hL
  have hLN : L ≤ K₁ ⊔ K₂ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hKn.conj_mem y (Subgroup.mem_sup_left hy) s
  have hNK₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set Γ) := by
    refine sup_le Subgroup.le_normalizer ?_
    exact (show K₂ ≤ Subgroup.centralizer (K₁ : Set Γ) from fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb).trans
      (Subgroup.centralizer_le_normalizer _)
  have hNK₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set Γ) := by
    refine sup_le ?_ Subgroup.le_normalizer
    exact (show K₁ ≤ Subgroup.centralizer (K₂ : Set Γ) from fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hLs : IsSimpleGroup ↥L := (K₁.equivMapOfInjective f hfinj).symm.isSimpleGroup
  have hcardL : Nat.card L = Nat.card K₁ := Subgroup.card_map_of_injective hfinj
  have hLnorm : ∀ n ∈ K₁ ⊔ K₂, ∀ l ∈ L, n * l * n⁻¹ ∈ L := by
    intro n hn l hl
    obtain ⟨y, hy, rfl⟩ := hl
    have hn' : s⁻¹ * n * s ∈ K₁ ⊔ K₂ := by
      have := hKn.conj_mem n hn s⁻¹
      simpa using this
    refine ⟨(s⁻¹ * n * s) * y * (s⁻¹ * n * s)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hNK₁ hn') y).1 hy
    · show s * ((s⁻¹ * n * s) * y * (s⁻¹ * n * s)⁻¹) * s⁻¹ = n * (s * y * s⁻¹) * n⁻¹
      group
  have hnormal : ∀ K : Subgroup Γ, (K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set Γ)) →
      ((L ⊓ K).subgroupOf L).Normal := by
    intro K hK
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 (hK (hLN g.2)) (n : Γ)).1 hn.2
    simpa using this
  have hn₁ := hnormal K₁ hNK₁
  have hn₂ := hnormal K₂ hNK₂
  have hdec : ∀ c ∈ K₁ ⊔ K₂, ∃ x ∈ K₁, ∃ y ∈ K₂, x * y = c := fun c hc' =>
    exists_mul_of_mem_sup hc hc'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ K₁).subgroupOf L) with h₁' | h₁'
  swap
  ·
    left
    have hLK₁ : L ≤ K₁ := fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := by
        rw [h₁']
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
    exact Subgroup.eq_of_le_of_card_ge hLK₁ (by rw [hcardL])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ K₂).subgroupOf L) with h₂' | h₂'
  swap
  ·
    right
    have hLK₂ : L ≤ K₂ := fun x hx => by
      have hmem : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ K₂).subgroupOf L := by
        rw [h₂']
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hmem).2
    exact Subgroup.eq_of_le_of_card_ge hLK₂ (by rw [hcardL, hcard])
  exfalso
  have hcomm : ∀ (K : Subgroup Γ), K₁ ⊔ K₂ ≤ Subgroup.normalizer (K : Set Γ) →
      (∀ x ∈ L ⊓ K, x = 1) → K ≤ K₁ ⊔ K₂ → ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
    intro K hK hx hKN l hl k hk
    have h1 : l * k * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hK (hLN hl)) k).1 hk
    have h2 : k * l⁻¹ * k⁻¹ ∈ L := hLnorm k (hKN hk) l⁻¹ (L.inv_mem hl)
    have h3 : l * k * l⁻¹ * k⁻¹ = 1 := hx _ ⟨by
      have : l * k * l⁻¹ * k⁻¹ = l * (k * l⁻¹ * k⁻¹) := by group
      rw [this]
      exact L.mul_mem hl h2, K.mul_mem h1 (K.inv_mem hk)⟩
    calc l * k = (l * k * l⁻¹ * k⁻¹) * (k * l) := by group
      _ = k * l := by rw [h3, one_mul]
  have h1' : ∀ x ∈ L ⊓ K₁, x = 1 := fun x hx => by
    have hmem : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ K₁).subgroupOf L := hx
    rw [h₁', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h2' : ∀ x ∈ L ⊓ K₂, x = 1 := fun x hx => by
    have hmem : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ K₂).subgroupOf L := hx
    rw [h₂', Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hLK₁c := hcomm K₁ hNK₁ h1' le_sup_left
  have hLK₂c := hcomm K₂ hNK₂ h2' le_sup_right
  have hL1 : ∀ l ∈ L, l = 1 := by
    intro l hl
    obtain ⟨x, hx, y, hy, rfl⟩ := hdec l (hLN hl)
    have hx1 : x = 1 := hz₁ x hx fun k hk => by
      have h1 := hLK₁c (x * y) hl k hk
      have h2 : y * k = k * y := (hc k hk y hy).symm
      have h3 : (x * k) * y = (k * x) * y := by
        calc (x * k) * y = x * (k * y) := by rw [mul_assoc]
          _ = x * (y * k) := by rw [h2]
          _ = (x * y) * k := by rw [mul_assoc]
          _ = k * (x * y) := h1
          _ = (k * x) * y := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    have hy1 : y = 1 := hz₂ y hy fun k hk => by
      have h1 := hLK₂c (x * y) hl k hk
      have h2 : x * k = k * x := hc x hx k hk
      have h3 : x * (y * k) = x * (k * y) := by
        calc x * (y * k) = (x * y) * k := by rw [mul_assoc]
          _ = k * (x * y) := h1
          _ = (k * x) * y := by rw [mul_assoc]
          _ = (x * k) * y := by rw [h2]
          _ = x * (k * y) := by rw [mul_assoc]
      exact (mul_left_cancel h3).symm
    rw [hx1, hy1, one_mul]
  have hLn : Nontrivial ↥L := hLs.toNontrivial
  obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
  exact hl (Subtype.ext (hL1 l l.2))

end E217R4

end CFSG.Quasithin

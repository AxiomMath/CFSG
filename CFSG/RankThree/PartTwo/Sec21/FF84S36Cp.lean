module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiT
public import CFSG.LargeExtraspecial.S9FiveB

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem S36_split_comm {Q₁ Q₂ : Subgroup G}
    (hc : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) {x x' y y' : G} (hx : x ∈ Q₁) (hx' : x' ∈ Q₁)
    (hy : y ∈ Q₂) (hy' : y' ∈ Q₂) :
    x * y * (x' * y') * (x * y)⁻¹ * (x' * y')⁻¹ =
      (x * x' * x⁻¹ * x'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) := by
  have hcQ : y * y' * y⁻¹ * y'⁻¹ ∈ Q₂ :=
    Q₂.mul_mem (Q₂.mul_mem (Q₂.mul_mem hy hy') (Q₂.inv_mem hy)) (Q₂.inv_mem hy')
  have e1 : y * x' = x' * y := (hc x' hx' y hy).symm
  have e2 : x * y' = y' * x := hc x hx y' hy'
  have e2' : y' * x⁻¹ = x⁻¹ * y' := by
    calc y' * x⁻¹ = x⁻¹ * (x * y') * x⁻¹ := by group
      _ = x⁻¹ * (y' * x) * x⁻¹ := by rw [e2]
      _ = x⁻¹ * y' := by group
  have e3 : x * (y * y' * y⁻¹ * y'⁻¹) = (y * y' * y⁻¹ * y'⁻¹) * x := hc x hx _ hcQ
  have e3' : (y * y' * y⁻¹ * y'⁻¹) * x⁻¹ = x⁻¹ * (y * y' * y⁻¹ * y'⁻¹) := by
    calc (y * y' * y⁻¹ * y'⁻¹) * x⁻¹ = x⁻¹ * (x * (y * y' * y⁻¹ * y'⁻¹)) * x⁻¹ := by group
      _ = x⁻¹ * ((y * y' * y⁻¹ * y'⁻¹) * x) * x⁻¹ := by rw [e3]
      _ = x⁻¹ * (y * y' * y⁻¹ * y'⁻¹) := by group
  have e4 : x' * (y * y' * y⁻¹ * y'⁻¹) = (y * y' * y⁻¹ * y'⁻¹) * x' := hc x' hx' _ hcQ
  have e4' : (y * y' * y⁻¹ * y'⁻¹) * x'⁻¹ = x'⁻¹ * (y * y' * y⁻¹ * y'⁻¹) := by
    calc (y * y' * y⁻¹ * y'⁻¹) * x'⁻¹ = x'⁻¹ * (x' * (y * y' * y⁻¹ * y'⁻¹)) * x'⁻¹ := by group
      _ = x'⁻¹ * ((y * y' * y⁻¹ * y'⁻¹) * x') * x'⁻¹ := by rw [e4]
      _ = x'⁻¹ * (y * y' * y⁻¹ * y'⁻¹) := by group
  calc x * y * (x' * y') * (x * y)⁻¹ * (x' * y')⁻¹
      = x * (y * x') * y' * (y⁻¹ * x⁻¹) * (y'⁻¹ * x'⁻¹) := by group
    _ = x * (x' * y) * y' * (y⁻¹ * x⁻¹) * (y'⁻¹ * x'⁻¹) := by rw [e1]
    _ = x * x' * (y * y' * y⁻¹ * y'⁻¹) * (y' * x⁻¹) * (y'⁻¹ * x'⁻¹) := by group
    _ = x * x' * (y * y' * y⁻¹ * y'⁻¹) * (x⁻¹ * y') * (y'⁻¹ * x'⁻¹) := by rw [e2']
    _ = x * x' * ((y * y' * y⁻¹ * y'⁻¹) * x⁻¹) * x'⁻¹ := by group
    _ = x * x' * (x⁻¹ * (y * y' * y⁻¹ * y'⁻¹)) * x'⁻¹ := by rw [e3']
    _ = x * x' * x⁻¹ * ((y * y' * y⁻¹ * y'⁻¹) * x'⁻¹) := by group
    _ = x * x' * x⁻¹ * (x'⁻¹ * (y * y' * y⁻¹ * y'⁻¹)) := by rw [e4']
    _ = (x * x' * x⁻¹ * x'⁻¹) * (y * y' * y⁻¹ * y'⁻¹) := by group

theorem S36_ext_central_product {t : G} {T Q₁ Q₂ : Subgroup G} (hTp : IsPGroup 2 T)
    (h₁ : ExtraspecialAt Q₁ t) (h₂ : ExtraspecialAt Q₂ t)
    (hc : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x)
    (hT : ∀ g ∈ T, ∃ x ∈ Q₁, ∃ y ∈ Q₂, g = x * y) (hQ₁ : Q₁ ≤ T) (hQ₂ : Q₂ ≤ T) :
    IsExtraspecialPGroup 2 ↥T := by
  have ht2 : t * t = 1 := h₁.sq_eq
  have ht1 : t ≠ 1 := h₁.ne_one
  have htT : t ∈ T := hQ₁ h₁.mem
  have ht2' : t ^ 2 = 1 := by rw [sq]; exact ht2
  have hord : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime ht2' ht1
  have hcen₁ : ∀ x ∈ Q₁, (∀ u ∈ Q₁, x * u = u * x) → x ∈ Subgroup.zpowers t := by
    intro x hx hcx
    rcases h₁.center_le x hx hcx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have hcen₂ : ∀ x ∈ Q₂, (∀ u ∈ Q₂, x * u = u * x) → x ∈ Subgroup.zpowers t := by
    intro x hx hcx
    rcases h₂.center_le x hx hcx with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have hsqQ₁ : ∀ a ∈ Q₁, a * a ∈ Subgroup.zpowers t := by
    intro a ha
    rcases h₁.sq_mem a ha with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have hsqQ₂ : ∀ b ∈ Q₂, b * b ∈ Subgroup.zpowers t := by
    intro b hb
    rcases h₂.sq_mem b hb with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  have htc : ∀ g ∈ T, t * g = g * t := by
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hT g hg
    have ht_x : x * t = t * x := h₁.central x hx
    have ht_y : y * t = t * y := h₂.central y hy
    calc t * (x * y) = (t * x) * y := (mul_assoc _ _ _).symm
      _ = (x * t) * y := by rw [ht_x]
      _ = x * (t * y) := mul_assoc _ _ _
      _ = x * (y * t) := by rw [ht_y]
      _ = (x * y) * t := (mul_assoc _ _ _).symm
  let τ : ↥T := ⟨t, htT⟩
  have hτ2 : τ * τ = 1 := Subtype.ext ht2
  have hτ1 : τ ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hτ2' : τ ^ 2 = 1 := by rw [sq]; exact hτ2
  have hτord : Nat.card (Subgroup.zpowers τ) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_eq_prime hτ2' hτ1
  have hmemZ : ∀ v : ↥T, (v : G) ∈ Subgroup.zpowers t → v ∈ Subgroup.zpowers τ := by
    intro v hv
    rcases (S36_zpowers_two ht2 ht1 hv) with h | h
    · have hv1 : v = 1 := Subtype.ext h
      rw [hv1]; exact Subgroup.one_mem _
    · have hvτ : v = τ := Subtype.ext h
      rw [hvτ]; exact Subgroup.mem_zpowers τ
  have hzG : ∀ v : ↥T, v ∈ Subgroup.zpowers τ → (v : G) ∈ Subgroup.zpowers t := by
    intro v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have hk : ((τ ^ k : ↥T) : G) = t ^ k := by simp [τ]
    rw [hk]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  have hG : ∀ g ∈ T, ∀ h ∈ T, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.zpowers t := by
    intro g hg h hh
    obtain ⟨x, hx, y, hy, rfl⟩ := hT g hg
    obtain ⟨x', hx', y', hy', rfl⟩ := hT h hh
    rw [S36_split_comm hc hx hx' hy hy']
    apply Subgroup.mul_mem
    · rcases h₁.comm_mem x hx x' hx' with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers t
    · rcases h₂.comm_mem y hy y' hy' with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers t
  have hcommT : ∀ x y : ↥T, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers τ := by
    intro x y
    apply hmemZ
    have h := hG (x : G) x.2 (y : G) y.2
    simpa using h
  have hτc : τ ∈ Subgroup.center ↥T := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (htc (g : G) g.2).symm
  have hZc : Subgroup.zpowers τ ≤ Subgroup.center ↥T := Subgroup.zpowers_le.2 hτc
  have hsq : ∀ x : ↥T, x ^ 2 ∈ Subgroup.zpowers τ := by
    intro x
    apply hmemZ
    rw [Subgroup.coe_pow]
    obtain ⟨a, ha, b, hb, hxab⟩ := hT (x : G) x.2
    have hab : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hc a ha b hb]
        _ = (a * a) * (b * b) := by group
    rw [hxab, sq, hab]
    exact Subgroup.mul_mem _ (hsqQ₁ a ha) (hsqQ₂ b hb)
  have hcent : ∀ x : ↥T, (∀ y : ↥T, x * y = y * x) → x ∈ Subgroup.zpowers τ := by
    intro x hx
    apply hmemZ
    obtain ⟨a, ha, b, hb, hxab⟩ := hT (x : G) x.2
    have hcomm : ∀ g ∈ T, (x : G) * g = g * (x : G) := fun g hg =>
      congrArg Subtype.val (hx ⟨g, hg⟩)
    have ha' : a ∈ Subgroup.zpowers t := by
      apply hcen₁ a ha
      intro u hu
      have h := hcomm u (hQ₁ hu)
      rw [hxab] at h
      have hbu : b * u = u * b := (hc u hu b hb).symm
      have key : a * u * b = u * a * b := by
        calc a * u * b = a * (u * b) := mul_assoc _ _ _
          _ = a * (b * u) := by rw [hbu]
          _ = a * b * u := (mul_assoc _ _ _).symm
          _ = u * (a * b) := h
          _ = u * a * b := (mul_assoc _ _ _).symm
      exact mul_right_cancel key
    have hb' : b ∈ Subgroup.zpowers t := by
      apply hcen₂ b hb
      intro v hv
      have h := hcomm v (hQ₂ hv)
      rw [hxab] at h
      have hav : a * v = v * a := hc a ha v hv
      have key : a * (b * v) = a * (v * b) := by
        calc a * (b * v) = a * b * v := (mul_assoc _ _ _).symm
          _ = v * (a * b) := h
          _ = v * a * b := (mul_assoc _ _ _).symm
          _ = a * v * b := by rw [hav]
          _ = a * (v * b) := mul_assoc _ _ _
      exact mul_left_cancel key
    rw [hxab]
    exact Subgroup.mul_mem _ ha' hb'
  have hnab : ∃ x : ↥T, x ∉ Subgroup.zpowers τ := by
    by_contra hcon
    push Not at hcon
    have hQ1le : Q₁ ≤ Subgroup.zpowers t := by
      intro u hu
      exact hzG ⟨u, hQ₁ hu⟩ (hcon ⟨u, hQ₁ hu⟩)
    have hle := Subgroup.card_le_of_le hQ1le
    rw [h₁.card_eq, hord] at hle
    norm_num at hle
  exact CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hTp hτord hZc hcommT hsq hcent hnab

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end

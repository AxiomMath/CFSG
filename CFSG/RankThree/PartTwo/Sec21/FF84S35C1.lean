module

public import CFSG.RankThree.PartTwo.Sec21.FF84S31Theta

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG Equiv Equiv.Perm

@[expose] def A10Stmt : Prop :=
  (IsElemAb 2 4 U₁ ∧ IsElemAb 2 4 U₂ ∧ U₁ ⊓ U₂ = ⊥ ∧ Eo ≤ Nor U₁ ∧ Eo ≤ Nor U₂ ∧
      conjBy τ₀ U₁ = U₂) ∧
    ∀ Y : Subgroup P8, Y ≤ A8s → IsPGroup 2 Y → Eo ≤ Nor Y → Y ≤ U₁ ∨ Y ≤ U₂

section Pre

variable {G : Type} [Group G] {L : Subgroup G} {θ : G → P8}

@[expose] def preImg (P : PreTheta L θ) (W : Subgroup P8) : Subgroup G where
  carrier := {x | x ∈ L ∧ θ x ∈ W}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    rw [P.mul x (Subgroup.le_normalizer hx.1) y (Subgroup.le_normalizer hy.1)]
    exact mul_mem hx.2 hy.2⟩
  one_mem' := ⟨one_mem _, by rw [P.one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    rw [P.inv (Subgroup.le_normalizer hx.1)]
    exact inv_mem hx.2⟩

theorem theta_inj (P : PreTheta L θ) (hZ : Subgroup.center L = ⊥) {x y : G} (hx : x ∈ L)
    (hy : y ∈ L) (h : θ x = θ y) : x = y := by
  have hxy : x⁻¹ * y ∈ L := mul_mem (inv_mem hx) hy
  have h1 : θ (x⁻¹ * y) = 1 := by
    rw [P.mul _ (Subgroup.le_normalizer (inv_mem hx)) _ (Subgroup.le_normalizer hy),
      P.inv (Subgroup.le_normalizer hx), h, inv_mul_cancel]
  have h2 : x⁻¹ * y ∈ CenS L := (P.ker _ (Subgroup.le_normalizer hxy)).1 h1
  have hc : (⟨x⁻¹ * y, hxy⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)
  rw [hZ] at hc
  have h3 : x⁻¹ * y = 1 := congrArg Subtype.val (Subgroup.mem_bot.1 hc)
  exact inv_mul_eq_one.1 h3

theorem nor_preImg [Finite G] (P : PreTheta L θ) {g : G} (hg : g ∈ Nor L) {W : Subgroup P8}
    (hW : θ g ∈ Nor W) : g ∈ Nor (preImg P W) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hx' : x ∈ L ∧ θ x ∈ W := hx
  show g * x * g⁻¹ ∈ L ∧ θ (g * x * g⁻¹) ∈ W
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx'.1, ?_⟩
  rw [P.conj hg (Subgroup.le_normalizer hx'.1)]
  exact (Subgroup.mem_normalizer_iff.1 hW (θ x)).1 hx'.2

theorem isPGroup_preImg (P : PreTheta L θ) (hZ : Subgroup.center L = ⊥) {W : Subgroup P8}
    (hW : IsPGroup 2 W) : IsPGroup 2 (preImg P W) := by
  intro x
  obtain ⟨n, hn⟩ := hW ⟨θ x, x.2.2⟩
  refine ⟨n, Subtype.ext ?_⟩
  have hn' : θ x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have hxL : (x : G) ∈ L := x.2.1
  show (x : G) ^ (2 ^ n) = 1
  refine theta_inj P hZ (pow_mem hxL _) (one_mem _) ?_
  rw [P.pow (Subgroup.le_normalizer hxL), P.one]
  exact hn'

@[expose] def imgSub (P : PreTheta L θ) (Y : Subgroup G) (hY : Y ≤ Nor L) : Subgroup P8 where
  carrier := {z | ∃ y ∈ Y, θ y = z}
  mul_mem' := by
    rintro _ _ ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
    exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, P.mul _ (hY hy₁) _ (hY hy₂)⟩
  one_mem' := ⟨1, one_mem _, P.one⟩
  inv_mem' := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y⁻¹, inv_mem hy, P.inv (hY hy)⟩

theorem nor_imgSub [Finite G] (P : PreTheta L θ) (Y : Subgroup G) (hY : Y ≤ Nor L) {g : G}
    (hg : g ∈ Nor Y) (hgL : g ∈ Nor L) : θ g ∈ Nor (imgSub P Y hY) := by
  apply Subgroup.mem_normalizer_fintype
  rintro z ⟨y, hy, rfl⟩
  refine ⟨g * y * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg y).1 hy, ?_⟩
  rw [P.conj hgL (hY hy)]

theorem F5_noY_theta [Finite G] (hA10 : A10Stmt) (P : PreTheta L θ) (hZ : Subgroup.center L = ⊥)
    {b₁ b₂ t : G} (hb₁ : θ b₁ = m₁) (hb₂ : θ b₂ = m₂) (hb₁L : b₁ ∈ L) (hb₂L : b₂ ∈ L)
    (htL : t ∈ Nor L) (htθ : θ t = τ₀) (Y : Subgroup G) (hY : Y ≤ L) (hY2 : IsPGroup 2 Y)
    (h₁ : b₁ ∈ Nor Y) (h₂ : b₂ ∈ Nor Y) (ht : t ∈ Nor Y) : Y = ⊥ := by
  obtain ⟨⟨-, -, hU12, -, -, hconj⟩, hmax⟩ := hA10
  have hYN : Y ≤ Nor L := hY.trans Subgroup.le_normalizer
  set Y' := imgSub P Y hYN with hY'
  have hA : Y' ≤ A8s := by
    rintro z ⟨y, hy, rfl⟩
    exact P.mem y (hY hy)
  have hY'2 : IsPGroup 2 Y' := by
    intro z
    obtain ⟨y, hy, hyz⟩ := z.2
    obtain ⟨n, hn⟩ := hY2 ⟨y, hy⟩
    refine ⟨n, Subtype.ext ?_⟩
    have hn' : y ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    show (z : P8) ^ (2 ^ n) = 1
    rw [← hyz, ← P.pow (hYN hy), hn', P.one]
  have hEo : Eo ≤ Nor Y' := by
    rw [Eo, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [← hb₁]; exact nor_imgSub P Y hYN h₁ (Subgroup.le_normalizer hb₁L)
    · rw [← hb₂]; exact nor_imgSub P Y hYN h₂ (Subgroup.le_normalizer hb₂L)
  have hτ2 : τ₀ * τ₀ = 1 := A11_tau_centralizes.2.2.2
  have hτ : τ₀⁻¹ = τ₀ := inv_eq_of_mul_eq_one_right hτ2
  have hτN : τ₀ ∈ Nor Y' := by rw [← htθ]; exact nor_imgSub P Y hYN ht htL
  have hτc : ∀ z ∈ Y', τ₀ * z * τ₀ ∈ Y' := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.1 hτN z).1 hz
    rwa [hτ] at this
  have hbot : Y' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hw := hτc z hz
    have hzz : z = τ₀ * (τ₀ * z * τ₀) * τ₀ := by
      calc z = (τ₀ * τ₀) * z * (τ₀ * τ₀) := by rw [hτ2]; group
        _ = _ := by group
    have hz1 : z ∈ U₁ ⊓ U₂ := by
      rcases hmax Y' hA hY'2 hEo with h | h
      · refine Subgroup.mem_inf.2 ⟨h hz, ?_⟩
        rw [← hconj]
        refine Subgroup.mem_map.2 ⟨τ₀ * z * τ₀, h hw, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ]
        exact hzz.symm
      · refine Subgroup.mem_inf.2 ⟨?_, h hz⟩
        obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (hconj ▸ h hw : τ₀ * z * τ₀ ∈ conjBy τ₀ U₁)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ] at hu'
        have : z = u := by
          calc z = τ₀ * (τ₀ * z * τ₀) * τ₀ := hzz
            _ = τ₀ * (τ₀ * u * τ₀) * τ₀ := by rw [← hu']
            _ = u := by
              calc τ₀ * (τ₀ * u * τ₀) * τ₀ = (τ₀ * τ₀) * u * (τ₀ * τ₀) := by group
                _ = u := by rw [hτ2]; group
        rw [this]; exact hu
    rw [hU12] at hz1
    exact Subgroup.mem_bot.1 hz1
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have : θ y ∈ Y' := ⟨y, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact theta_inj P hZ (hY hy) (one_mem _) (this.trans P.one.symm)

end Pre

theorem F5_t_theta {G : Type} [Group G] {L : Subgroup G} {b₁ b₂ : G} {θ : G → P8}
    (H : HasTheta L b₁ b₂ θ) (hb₁N : b₁ ∈ Nor L) (hb₂N : b₂ ∈ Nor L) {t : G} (htN : t ∈ Nor L)
    (ht2 : t * t = 1) (h₁ : t * b₁ = b₁ * t) (h₂ : t * b₂ = b₂ * t) :
    t ∈ CenS L ∨ θ t = τ₀ := by
  rcases H.two_elt hb₁N hb₂N htN h₁ h₂ (n := 1) (by rw [pow_one, pow_two]; exact ht2) with h | h
  · exact Or.inl ((H.toPreTheta.ker t htN).1 h)
  · exact Or.inr h

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

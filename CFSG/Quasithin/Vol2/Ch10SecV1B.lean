module

public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem mem_of_mem_fixRel {G : Subgroup (MulAut V)} {t₁ t₂ t₃ : MulAut V}
    (hgen : ∀ S : Subgroup (MulAut V), t₁ ∈ S → t₂ ∈ S → t₃ ∈ S → G ≤ S)
    (h₁ : t₁ ∈ G) (h₂ : t₂ ∈ G) (h₃ : t₃ ∈ G) {K : Subgroup V} (hK : K ≤ fixV G) {w : V}
    (hw₁ : t₁ w * w⁻¹ ∈ K) (hw₂ : t₂ w * w⁻¹ ∈ K) (hw₃ : t₃ w * w⁻¹ ∈ K) :
    ∀ g ∈ G, g w * w⁻¹ ∈ K := by
  let S : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ G ∧ g w * w⁻¹ ∈ K}
      one_mem' := ⟨G.one_mem, by rw [MulAut.one_apply, mul_inv_cancel]; exact K.one_mem⟩
      mul_mem' := by
        rintro g h ⟨hg, cg⟩ ⟨hh, ch⟩
        refine ⟨G.mul_mem hg hh, ?_⟩
        have e : (g * h) w * w⁻¹ = g (h w * w⁻¹) * (g w * w⁻¹) := by
          rw [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e, hK ch g hg]
        exact K.mul_mem ch cg
      inv_mem' := by
        rintro g ⟨hg, cg⟩
        refine ⟨G.inv_mem hg, ?_⟩
        have h1 : g (g⁻¹ w * w⁻¹) = (g w * w⁻¹)⁻¹ := by
          rw [map_mul, map_inv, MulAut.apply_inv_self]
          group
        have h3 := hK (K.inv_mem cg) g⁻¹ (G.inv_mem hg)
        rw [← h1, MulAut.inv_apply_self] at h3
        rw [h3, h1]
        exact K.inv_mem cg }
  intro g hg
  exact (hgen S ⟨h₁, hw₁⟩ ⟨h₂, hw₂⟩ ⟨h₃, hw₃⟩ hg).2

theorem card_sup_mul_le [Finite V] {X X' K : Subgroup V} (h : K ≤ X) (h' : K ≤ X') :
    Nat.card ↥(X ⊔ X') * Nat.card K ≤ Nat.card X * Nat.card X' := by
  rw [← card_sup_mul_card_inf X X']
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (le_inf h h'))

theorem commSub_le_sup {G : Subgroup (MulAut V)} {t₁ t₂ t₃ : MulAut V}
    (hgen : ∀ S : Subgroup (MulAut V), t₁ ∈ S → t₂ ∈ S → t₃ ∈ S → G ≤ S)
    (h₁ : t₁ ∈ G) (h₂ : t₂ ∈ G) (h₃ : t₃ ∈ G) (i₁ : ∀ v, t₁ (t₁ v) = v)
    (i₂ : ∀ v, t₂ (t₂ v) = v) (i₃ : ∀ v, t₃ (t₃ v) = v) {W K : Subgroup V}
    (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hKW : K ≤ W) :
    commSub W G ≤ (W.map (commHom t₁) ⊔ K) ⊔ (W.map (commHom t₂) ⊔ K) ⊔
      (W.map (commHom t₃) ⊔ K) := by
  set Y := (W.map (commHom t₁) ⊔ K) ⊔ (W.map (commHom t₂) ⊔ K) ⊔ (W.map (commHom t₃) ⊔ K)
    with hY
  have hmap : ∀ t ∈ G, W.map (commHom t) ⊔ K ≤ W := by
    intro t ht
    refine sup_le ?_ hKW
    rintro _ ⟨w, hw, rfl⟩
    exact W.mul_mem (hW t ht w hw) (W.inv_mem hw)
  have hYW : Y ≤ W := sup_le (sup_le (hmap t₁ h₁) (hmap t₂ h₂)) (hmap t₃ h₃)
  have l₁ : W.map (commHom t₁) ≤ Y := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have l₂ : W.map (commHom t₂) ≤ Y := le_sup_left.trans (le_sup_right.trans le_sup_left)
  have l₃ : W.map (commHom t₃) ≤ Y := le_sup_left.trans le_sup_right
  have hinv : ∀ t ∈ G, (∀ v, t (t v) = v) → W.map (commHom t) ≤ Y → ∀ y, y ∈ Y ↔ t y ∈ Y := by
    have fwd : ∀ t ∈ G, W.map (commHom t) ≤ Y → ∀ y ∈ Y, t y ∈ Y := by
      intro t ht hle y hy
      have e : t y = commHom t y * y := by rw [commHom_apply]; group
      rw [e]
      exact Y.mul_mem (hle ⟨y, hYW hy, rfl⟩) hy
    intro t ht hi hle y
    refine ⟨fwd t ht hle y, fun h => ?_⟩
    have := fwd t ht hle (t y) h
    rwa [hi] at this
  let SY : Subgroup (MulAut V) :=
    { carrier := {g | ∀ y, y ∈ Y ↔ g y ∈ Y}
      one_mem' := fun y => by rw [MulAut.one_apply]
      mul_mem' := fun {g h} hg hh y => by rw [MulAut.mul_apply, ← hg (h y), ← hh y]
      inv_mem' := fun {g} hg y => by
        have := hg (g⁻¹ y)
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hGY : G ≤ SY := hgen SY (hinv t₁ h₁ i₁ l₁) (hinv t₂ h₂ i₂ l₂) (hinv t₃ h₃ i₃ l₃)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨g, hg, w, hw, rfl⟩
  let T : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ G ∧ g w * w⁻¹ ∈ Y}
      one_mem' := ⟨G.one_mem, by rw [MulAut.one_apply, mul_inv_cancel]; exact Y.one_mem⟩
      mul_mem' := by
        rintro g h ⟨hg, cg⟩ ⟨hh, ch⟩
        refine ⟨G.mul_mem hg hh, ?_⟩
        have e : (g * h) w * w⁻¹ = g (h w * w⁻¹) * (g w * w⁻¹) := by
          rw [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [e]
        exact Y.mul_mem ((hGY hg _).1 ch) cg
      inv_mem' := by
        rintro g ⟨hg, cg⟩
        refine ⟨G.inv_mem hg, ?_⟩
        have e : g⁻¹ w * w⁻¹ = g⁻¹ ((g w * w⁻¹)⁻¹) := by
          rw [map_inv, map_mul, map_inv, MulAut.inv_apply_self]
          group
        rw [e]
        exact (hGY (G.inv_mem hg) _).1 (Y.inv_mem cg) }
  have hT : G ≤ T := hgen T ⟨h₁, l₁ ⟨w, hw, rfl⟩⟩ ⟨h₂, l₂ ⟨w, hw, rfl⟩⟩ ⟨h₃, l₃ ⟨w, hw, rfl⟩⟩
  exact (hT hg).2

theorem card_commSub_sup_le [Finite V] {G : Subgroup (MulAut V)} {t₁ t₂ t₃ : MulAut V}
    (hgen : ∀ S : Subgroup (MulAut V), t₁ ∈ S → t₂ ∈ S → t₃ ∈ S → G ≤ S)
    (h₁ : t₁ ∈ G) (h₂ : t₂ ∈ G) (h₃ : t₃ ∈ G) (i₁ : ∀ v, t₁ (t₁ v) = v)
    (i₂ : ∀ v, t₂ (t₂ v) = v) (i₃ : ∀ v, t₃ (t₃ v) = v) {W K : Subgroup V}
    (hW : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) (hKW : K ≤ W)
    (c₁ : Nat.card ↥(W.map (commHom t₁) ⊔ K) ≤ 2 * Nat.card K)
    (c₂ : Nat.card ↥(W.map (commHom t₂) ⊔ K) ≤ 2 * Nat.card K)
    (c₃ : Nat.card ↥(W.map (commHom t₃) ⊔ K) ≤ 2 * Nat.card K) :
    Nat.card ↥(commSub W G ⊔ K) ≤ 8 * Nat.card K := by
  have hle := commSub_le_sup hgen h₁ h₂ h₃ i₁ i₂ i₃ hW hKW
  have hK : 0 < Nat.card K := Nat.card_pos
  set A₁ := W.map (commHom t₁) ⊔ K
  set A₂ := W.map (commHom t₂) ⊔ K
  set A₃ := W.map (commHom t₃) ⊔ K
  have s₁ : Nat.card ↥(A₁ ⊔ A₂) ≤ 4 * Nat.card K := by
    refine Nat.le_of_mul_le_mul_right ?_ hK
    calc Nat.card ↥(A₁ ⊔ A₂) * Nat.card K ≤ Nat.card A₁ * Nat.card A₂ :=
          card_sup_mul_le le_sup_right le_sup_right
      _ ≤ (2 * Nat.card K) * (2 * Nat.card K) := Nat.mul_le_mul c₁ c₂
      _ = 4 * Nat.card K * Nat.card K := by ring
  have s₂ : Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) ≤ 8 * Nat.card K := by
    refine Nat.le_of_mul_le_mul_right ?_ hK
    calc Nat.card ↥(A₁ ⊔ A₂ ⊔ A₃) * Nat.card K ≤ Nat.card ↥(A₁ ⊔ A₂) * Nat.card A₃ :=
          card_sup_mul_le (le_sup_right.trans le_sup_left) le_sup_right
      _ ≤ (4 * Nat.card K) * (2 * Nat.card K) := Nat.mul_le_mul s₁ c₃
      _ = 8 * Nat.card K * Nat.card K := by ring
  exact (Subgroup.card_le_of_le (sup_le hle (le_sup_right.trans (le_sup_left.trans
    le_sup_left)))).trans s₂

theorem card_map_conj [Finite V] {t g : MulAut V} {W K : Subgroup V}
    (hgW : ∀ w ∈ W, g w ∈ W) (hgW' : ∀ w ∈ W, g⁻¹ w ∈ W) (hgK : ∀ k ∈ K, g k = k) :
    Nat.card ↥(W.map (commHom (g * t * g⁻¹)) ⊔ K) = Nat.card ↥(W.map (commHom t) ⊔ K) := by
  have e : (W.map (commHom t) ⊔ K).map g.toMonoidHom = W.map (commHom (g * t * g⁻¹)) ⊔ K := by
    rw [Subgroup.map_sup]
    congr 1
    · ext y
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨g w, hgW w hw, ?_⟩
        simp only [commHom_apply, MulAut.mul_apply, MulAut.inv_apply_self,
          MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      · rintro ⟨w, hw, rfl⟩
        refine ⟨commHom t (g⁻¹ w), ⟨g⁻¹ w, hgW' w hw, rfl⟩, ?_⟩
        simp only [commHom_apply, MulAut.mul_apply, MulAut.apply_inv_self,
          MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        change g k ∈ K
        rw [hgK k hk]
        exact hk
      · intro hy
        exact ⟨y, hy, hgK y hy⟩
  rw [← e, Subgroup.card_map_of_injective g.injective]

end CFSG.Quasithin.Vol2.Ch10.V1C

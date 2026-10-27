module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Model

public section

namespace CFSG.Quasithin.S146zU.UC2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Arith

theorem eq_of_le_of_mul_eq {x y X Y : ℕ} (hx : x ≤ X) (hy : y ≤ Y) (hxy : x * y = X * Y)
    (hX : 0 < X) (hY : 0 < Y) : x = X ∧ y = Y := by
  have hx' : x = X := by
    by_contra hne
    have hlt : x < X := lt_of_le_of_ne hx hne
    have h1 : x * y ≤ x * Y := Nat.mul_le_mul_left x hy
    have h2 : x * Y < X * Y := Nat.mul_lt_mul_of_pos_right hlt hY
    omega
  refine ⟨hx', ?_⟩
  by_contra hne
  have hlt : y < Y := lt_of_le_of_ne hy hne
  have h2 : X * y < X * Y := Nat.mul_lt_mul_of_pos_left hlt hX
  rw [hx'] at hxy
  omega

theorem eq_of_chain {V c q₁ q₂ a a₁ a₂ d f₁ f₂ : ℕ} (hc : 0 < c) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hf₁ : 0 < f₁) (hf₂ : 0 < f₂)
    (hV : V = c * (q₁ * q₂)) (ha : a ≤ a₁ * a₂) (hd : d ≤ c * (f₁ * f₂))
    (h₁ : a₁ * f₁ ≤ q₁) (h₂ : a₂ * f₂ ≤ q₂) (hge : V ≤ a * d) :
    a = a₁ * a₂ ∧ d = c * (f₁ * f₂) ∧ a₁ * f₁ = q₁ ∧ a₂ * f₂ = q₂ := by
  have hmul : a * d ≤ (a₁ * a₂) * (c * (f₁ * f₂)) := Nat.mul_le_mul ha hd
  have hkey : c * (q₁ * q₂) ≤ c * ((a₁ * f₁) * (a₂ * f₂)) := by
    calc c * (q₁ * q₂) = V := hV.symm
      _ ≤ a * d := hge
      _ ≤ (a₁ * a₂) * (c * (f₁ * f₂)) := hmul
      _ = c * ((a₁ * f₁) * (a₂ * f₂)) := by ring
  have hk2 : q₁ * q₂ ≤ (a₁ * f₁) * (a₂ * f₂) := Nat.le_of_mul_le_mul_left hkey hc
  have hk3 : (a₁ * f₁) * (a₂ * f₂) = q₁ * q₂ :=
    le_antisymm (Nat.mul_le_mul h₁ h₂) hk2
  obtain ⟨e₁, e₂⟩ := eq_of_le_of_mul_eq h₁ h₂ hk3 hq₁ hq₂
  have hdpos : 0 < a * d := lt_of_lt_of_le (by rw [hV]; positivity) hge
  have hapos : 0 < a := Nat.pos_of_mul_pos_right hdpos
  have hdpos' : 0 < d := Nat.pos_of_mul_pos_left hdpos
  have hk4 : a * d = (a₁ * a₂) * (c * (f₁ * f₂)) := by
    refine le_antisymm hmul ?_
    calc (a₁ * a₂) * (c * (f₁ * f₂)) = c * ((a₁ * f₁) * (a₂ * f₂)) := by ring
      _ = c * (q₁ * q₂) := by rw [hk3]
      _ = V := hV.symm
      _ ≤ a * d := hge
  obtain ⟨e₃, e₄⟩ := eq_of_le_of_mul_eq ha hd hk4 (Nat.mul_pos ha₁ ha₂)
    (Nat.mul_pos hc (Nat.mul_pos hf₁ hf₂))
  exact ⟨e₃, e₄, e₁, e₂⟩

end Arith

section Core

variable {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂] {L₁ L₂ : Subgroup (MulAut V)}
  {C : Subgroup V} {Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V}
  {Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)}

theorem IsPairModel.offender_core [Finite V] [Finite K₁] [Finite K₂]
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 16) (hK₂ : Nat.card K₂ = 16)
    (Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) (hAl : ∀ g ∈ Al, g ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ))) :
    ∃ (A₁ : Subgroup ↥(StatedSL 2 K₁)) (A₂ : Subgroup ↥(StatedSL 2 K₂)),
      (∀ g, g ∈ Al ↔ g.1 ∈ A₁ ∧ g.2 ∈ A₂) ∧ Nat.card ↥Al = Nat.card ↥A₁ * Nat.card ↥A₂ ∧
      (A₁ = ⊥ ∨ Nat.card ↥A₁ = 16) ∧ (A₂ = ⊥ ∨ Nat.card ↥A₂ = 16) ∧
      Nat.card ↥A₁ * Nat.card ↥(fixNat A₁) = 16 ^ 2 ∧
      Nat.card ↥A₂ * Nat.card ↥(fixNat A₂) = 16 ^ 2 ∧
      Nat.card ↥(fixV (Al.map Φ)) =
        Nat.card ↥C * (Nat.card ↥(fixNat A₁) * Nat.card ↥(fixNat A₂)) ∧
      A₁ = Al.map (MonoidHom.fst _ _) ∧ A₂ = Al.map (MonoidHom.snd _ _) := by
  have hK₁' : Nat.card K₁ = 2 ^ 4 := by rw [hK₁]; norm_num
  have hK₂' : Nat.card K₂ = 2 ^ 4 := by rw [hK₂]; norm_num
  set A₁ : Subgroup ↥(StatedSL 2 K₁) := Al.map (MonoidHom.fst _ _) with hA₁
  set A₂ : Subgroup ↥(StatedSL 2 K₂) := Al.map (MonoidHom.snd _ _) with hA₂
  have hsq₁ : ∀ x ∈ A₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg Prod.fst (hAl g hg)
    simpa using this
  have hsq₂ : ∀ y ∈ A₂, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have := congrArg Prod.snd (hAl g hg)
    simpa using this
  have hAl_mem : ∀ g ∈ Al, g.1 ∈ A₁ ∧ g.2 ∈ A₂ := fun g hg =>
    ⟨Subgroup.mem_map_of_mem _ hg, Subgroup.mem_map_of_mem _ hg⟩
  let f : ↥Al → ↥A₁ × ↥A₂ := fun g =>
    (⟨g.1.1, (hAl_mem g.1 g.2).1⟩, ⟨g.1.2, (hAl_mem g.1 g.2).2⟩)
  have hfinj : Function.Injective f := by
    intro g h hgh
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ =>
      ((p.1 : ↥(StatedSL 2 K₁)), (p.2 : ↥(StatedSL 2 K₂)))) hgh
    exact Subtype.ext h1
  have hAl_le : Nat.card ↥Al ≤ Nat.card ↥A₁ * Nat.card ↥A₂ := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hfinj
  have hfix := hM.card_fixV_le Al
  have h₁ := card_mul_card_fixNat_le hK₁' A₁ hsq₁
  have h₂ := card_mul_card_fixNat_le hK₂' A₂ hsq₂
  have hV := hM.card_V
  rw [hK₁, hK₂] at hV
  rw [hK₁] at h₁
  rw [hK₂] at h₂
  obtain ⟨e₁, e₂, e₃, e₄⟩ := eq_of_chain (V := Nat.card V) (c := Nat.card ↥C) (q₁ := 16 ^ 2)
    (q₂ := 16 ^ 2) (a := Nat.card ↥Al) (a₁ := Nat.card ↥A₁) (a₂ := Nat.card ↥A₂)
    (d := Nat.card ↥(fixV (Al.map Φ))) (f₁ := Nat.card ↥(fixNat A₁))
    (f₂ := Nat.card ↥(fixNat A₂)) Nat.card_pos (by norm_num) (by norm_num) Nat.card_pos
    Nat.card_pos Nat.card_pos Nat.card_pos hV hAl_le hfix h₁ h₂ hge
  refine ⟨A₁, A₂, fun g => ⟨hAl_mem g, fun hg => ?_⟩, e₁, ?_, ?_, e₃, e₄, e₂, rfl, rfl⟩
  ·
    have hbij : Function.Bijective f :=
      hfinj.bijective_of_nat_card_le (by rw [Nat.card_prod]; exact e₁.symm.le)
    obtain ⟨k, hk⟩ := hbij.2 (⟨g.1, hg.1⟩, ⟨g.2, hg.2⟩)
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ =>
      ((p.1 : ↥(StatedSL 2 K₁)), (p.2 : ↥(StatedSL 2 K₂)))) hk
    have h2 : (k : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)) = g := h1
    rw [← h2]
    exact k.2
  · by_cases hb : A₁ = ⊥
    · exact Or.inl hb
    · refine Or.inr ?_
      have := (card_eq_field_of_mul_card_fixNat hK₁' hsq₁ hb (by rw [e₃, hK₁])).1
      rwa [hK₁] at this
  · by_cases hb : A₂ = ⊥
    · exact Or.inl hb
    · refine Or.inr ?_
      have := (card_eq_field_of_mul_card_fixNat hK₂' hsq₂ hb (by rw [e₄, hK₂])).1
      rwa [hK₂] at this

end Core

section Headline

variable {V : Type} [CommGroup V] [Finite V]

theorem isSylowTwoOf_of_card {G : Type} [Group G] {S H : Subgroup G} (hSH : S ≤ H) {k m : ℕ}
    (hS : Nat.card ↥S = 2 ^ k) (hH : Nat.card ↥H = 2 ^ k * m) (hm : Odd m) :
    IsSylowTwoOf S H := by
  refine ⟨hSH, IsPGroup.of_card hS, ?_⟩
  have h1 := Subgroup.relIndex_mul_card S H
  rw [inf_of_le_left hSH, hS, hH, mul_comm (2 ^ k) m] at h1
  have h2 : (S.subgroupOf H).index = m := by
    show S.relIndex H = m
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  rw [h2]
  exact hm.not_two_dvd_nat

end Headline

end CFSG.Quasithin.S146zU.UC2

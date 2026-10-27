module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Act
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Fix
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Index

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

omit [Module (ZMod 2) M] in
theorem crossedHom_zero_on_unitri_gen
    (act : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End M)
    (f : Matrix.SpecialLinearGroup (Fin 3) F → M)
    (hf : ∀ g h, f (g * h) = f g + act g (f h))
    (hdiag : ∀ t ∈ diagSL (F := F), f t = 0)
    (hX : ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ v : M, act t v = v → v = 0)
    (hY : ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ v : M, act t v = v → v = 0)
    (hZ : ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ v : M, act t v = v → v = 0) :
    ∀ u ∈ unitriSL (F := F), f u = 0 := by
  have hX0 : ∀ a : F, f (unitriMk a 0 0) = 0 := by
    obtain ⟨t, ht, hc, hfix⟩ := hX
    exact fun a => crossedHom_eq_zero_of_commute act f hf t _ (hc a) (hdiag t ht) hfix
  have hY0 : ∀ b : F, f (unitriMk 0 b 0) = 0 := by
    obtain ⟨t, ht, hc, hfix⟩ := hY
    exact fun b => crossedHom_eq_zero_of_commute act f hf t _ (hc b) (hdiag t ht) hfix
  have hZ0 : ∀ c : F, f (unitriMk 0 0 c) = 0 := by
    obtain ⟨t, ht, hc, hfix⟩ := hZ
    exact fun c => crossedHom_eq_zero_of_commute act f hf t _ (hc c) (hdiag t ht) hfix
  intro u hu
  have hu' : IsUnitri u := hu
  rw [eq_unitriMk_of_isUnitri hu', unitriMk_factor]
  simp only [hf, hX0, hY0, hZ0, map_zero, add_zero]

theorem crossedHom_principal_of_roots_gen [Fintype F] [CharP F 2]
    (act : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End M)
    (f : Matrix.SpecialLinearGroup (Fin 3) F → M)
    (hf : ∀ g h, f (g * h) = f g + act g (f h))
    (hX : ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ v : M, act t v = v → v = 0)
    (hY : ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ v : M, act t v = v → v = 0)
    (hZ : ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ v : M, act t v = v → v = 0) :
    ∃ w : M, ∀ g, f g = w - act g w := by
  classical
  have : Fintype (diagSL (F := F)) := Fintype.ofFinite _
  have hT : Odd (Fintype.card (diagSL (F := F))) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_natCard_diagSL
  obtain ⟨w, hw⟩ := crossedHom_principal_on_odd (diagSL (F := F)) hT act f hf
  have hact : ∀ g h : Matrix.SpecialLinearGroup (Fin 3) F, ∀ x : M,
      act (g * h) x = act g (act h x) := fun g h x => by
    rw [map_mul]
    rfl
  obtain ⟨f₁, hf₁def⟩ : ∃ f₁ : Matrix.SpecialLinearGroup (Fin 3) F → M,
      ∀ g, f₁ g = f g - (w - act g w) := ⟨_, fun g => rfl⟩
  have hf₁ : ∀ g h, f₁ (g * h) = f₁ g + act g (f₁ h) := by
    intro g h
    simp only [hf₁def, hf, hact, map_sub]
    abel
  have hdiag₁ : ∀ t ∈ diagSL (F := F), f₁ t = 0 := by
    intro t ht
    rw [hf₁def]
    exact sub_eq_zero.mpr (hw ⟨t, ht⟩)
  have hroot := crossedHom_zero_on_unitri_gen act f₁ hf₁ hdiag₁ hX hY hZ
  have hK : unitriSL (F := F) ≤ crossedHomKer act f₁ hf₁ := by
    intro u hu
    exact hroot u hu
  have hKodd : Odd (crossedHomKer act f₁ hf₁).index :=
    Odd.of_dvd_nat odd_index_unitriSL (Subgroup.index_dvd_of_le hK)
  obtain ⟨w₂, hw₂⟩ :=
    crossedHom_principal_of_odd_index (crossedHomKer act f₁ hf₁) hKodd act f₁ hf₁
      (fun k hk => hk)
  refine ⟨w₂ + w, fun g => ?_⟩
  have hfg : f g = f₁ g + (w - act g w) := by
    rw [hf₁def, sub_add_cancel]
  rw [hfg, hw₂ g, map_add]
  abel

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

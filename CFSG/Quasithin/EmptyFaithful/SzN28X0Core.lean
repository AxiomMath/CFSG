module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Rank
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Z
public import CFSG.Quasithin.EmptyFaithful.SzN28X0Phi
public import CFSG.Quasithin.Background.G10Basic
public import CFSG.Quasithin.EmptyFaithful.SzN28X0T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11 CFSG.Quasithin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_ne_pair {α : Type*} [Finite α] (hα : 2 < Nat.card α) (a b : α) :
    ∃ c : α, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set α) ⊆ {a, b} := fun c _ => by
    by_cases hca : c = a
    · exact Or.inl hca
    · exact Or.inr (hcon c hca)
  have h1 : Nat.card α ≤ ({a, b} : Set α).ncard := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set α).ncard ≤ 2 := by
    calc ({a, b} : Set α).ncard ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by rw [Set.ncard_singleton]
  omega

theorem eq_of_finrank_le_one {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (hM : Module.finrank (ZMod 2) M ≤ 1) {a b : M} (ha : a ≠ 0)
    (hb : b ≠ 0) : a = b := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hM
  obtain ⟨c₁, rfl⟩ := hv a
  obtain ⟨c₂, rfl⟩ := hv b
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have h1 : c₁ ≠ 0 := fun h0 => ha (by rw [h0, zero_smul])
  have h2 : c₂ ≠ 0 := fun h0 => hb (by rw [h0, zero_smul])
  rw [key _ h1, key _ h2]

section Counting

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
  {x₀ : GLV V} {v₁ : V} {W : Submodule (ZMod 2) V} {X : Subgroup (GLV V)}

theorem exists_Zw (h : G101Hyp B Γ v₁ W X ⊥) (c : F8Form B Γ A I I' x₀) {e₀ f₀ : V} (he : e₀ ∈ I)
    (hf : f₀ ∈ I') (he0 : e₀ ≠ 0) (hf0 : f₀ ≠ 0) (hB0 : B e₀ f₀ = 0) (hv₁ : v₁ = e₀ + f₀)
    {t : GLV V} (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) {y : GLV V} (hy : y ∈ X)
    (hy1 : y ≠ 1) (hyt : y ≠ t) :
    ∃ Zw : Submodule (ZMod 2) ↥W, 3 ≤ Module.finrank (ZMod 2) Zw ∧
      (∀ w ∈ Zw, y (w : V) = (w : V)) ∧ (∀ w ∈ Zw, t (w : V) = (w : V)) := by
  have hdy : ∀ w, y w = w → B v₁ w = 0 :=
    h.centralizer_le y hy (fun hm => hy1 (Subgroup.mem_bot.1 hm))
  have hiso : ∀ a b, B (y a) (y b) = B a b := h.isometry y (h.X_le hy)
  obtain ⟨v, hv⟩ := exists_sub_eq_of_fixed_perp h.nondegenerate' h.isRefl hiso hdy
  have hv' : y v - v = e₀ + f₀ := hv.trans hv₁
  have hk4 := c.finrank_ker_le_four he hf he0 hf0 hB0 ht (h.X_le hy) hyt ⟨v, hv'⟩
  have hdim := finrank_map_add h.nondegenerate' h.point hdy
  have hV8 := c.finrank_eq_eight
  obtain ⟨Zv, hZv⟩ : ∃ Zv : Submodule (ZMod 2) V,
      Zv = (LinearMap.ker (B v₁)).map ((y : V →ₗ[ZMod 2] V) - LinearMap.id) := ⟨_, rfl⟩
  rw [← hZv] at hdim
  have hZ3 : 3 ≤ Module.finrank (ZMod 2) Zv := by omega
  have hmemZ : ∀ z ∈ Zv, ∃ u, B v₁ u = 0 ∧ z = y u - u := by
    intro z hz
    rw [hZv] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨u, hu, by simp⟩
  have hZW : Zv ≤ W := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hmemZ z hz
    exact h.commutator_le y hy u hu
  have hfix : ∀ z ∈ Zv, y z = z := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := hmemZ z hz
    have h2 : y (y u) = u := by
      have := congrArg (fun g : GLV V => g u) (h.X_sq y hy)
      simpa using this
    rw [map_sub, h2, vsub_eq_add, vsub_eq_add, add_comm]
  have hfixt : ∀ z ∈ Zv, t z = z := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hmemZ z hz
    have hyfix : y (e₀ + f₀) = e₀ + f₀ := by rw [← hv₁]; exact h.X_fixes y hy
    have hperp : B (e₀ + f₀) u = 0 := by rw [← hv₁]; exact hu
    obtain ⟨h1, h2⟩ := c.sub_perp he hf (h.X_le hy) hyfix hperp
    rw [ht, h2, h1, zero_smul, zero_smul, add_zero, add_zero]
  refine ⟨Zv.comap W.subtype, ?_, fun w hw => hfix _ hw, fun w hw => hfixt _ hw⟩
  rw [(Submodule.comapSubtypeEquivOfLe hZW).finrank_eq]
  exact hZ3

theorem false_of_t_mem (h : G101Hyp B Γ v₁ W X ⊥) (c : F8Form B Γ A I I' x₀) {e₀ f₀ : V}
    (he : e₀ ∈ I) (hf : f₀ ∈ I') (he0 : e₀ ≠ 0) (hf0 : f₀ ≠ 0) (hB0 : B e₀ f₀ = 0)
    (hv₁ : v₁ = e₀ + f₀) {t : GLV V} (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀)
    (htX : t ∈ X) (ht1 : t ≠ 1) : False := by
  have hV8 := c.finrank_eq_eight
  have hk4 : Module.finrank (ZMod 2) W ≤ 4 := by
    have := h.finrank_isotropic_le
    omega
  have hk1 : 1 ≤ Module.finrank (ZMod 2) W := by
    have : 0 < Module.finrank (ZMod 2) W :=
      Module.finrank_pos_iff_exists_ne_zero.2
        ⟨⟨v₁, h.mem_W⟩, fun h0 => h.point (congrArg Subtype.val h0)⟩
    omega
  obtain ⟨n, hn⟩ := h.exists_card_X
  have hrank := h.rank
  rw [Subgroup.relIndex_bot_left, hn, Nat.log_pow Nat.one_lt_two, hV8] at hrank
  let tX : ↥X := ⟨t, htX⟩
  have htX1 : tX ≠ 1 := fun h0 => ht1 (congrArg Subtype.val h0)
  have hZ : ∀ y : ↥X, y ≠ 1 → y ≠ tX → ∃ Zw : Submodule (ZMod 2) ↥W,
      3 ≤ Module.finrank (ZMod 2) Zw ∧ (∀ w ∈ Zw, (y : GLV V) (w : V) = (w : V)) ∧
        (∀ w ∈ Zw, t (w : V) = (w : V)) := fun y hy1 hyt =>
    exists_Zw h c he hf he0 hf0 hB0 hv₁ ht y.2 (fun h0 => hy1 (Subtype.ext h0))
      (fun h0 => hyt (Subtype.ext h0))
  have hAnn : ∀ Zw : Submodule (ZMod 2) ↥W, Module.finrank (ZMod 2) Zw +
      Module.finrank (ZMod 2) Zw.dualAnnihilator = Module.finrank (ZMod 2) ↥W := fun Zw =>
    Subspace.finrank_add_finrank_dualAnnihilator_eq Zw
  have hphi : ∀ (y : ↥X) (Zw : Submodule (ZMod 2) ↥W),
      (∀ w ∈ Zw, (y : GLV V) (w : V) = (w : V)) → phi h y ∈ Zw.dualAnnihilator :=
    fun y Zw hy => (Submodule.mem_dualAnnihilator _).2 fun w hw => phi_eq_zero_of_fix h (hy w hw)
  have hfinD : Finite (Module.Dual (ZMod 2) ↥W) := Module.finite_of_finite (ZMod 2)
  have hfinF : Finite ↥(Fsp h) :=
    Finite.of_injective (Subtype.val : ↥(Fsp h) → Module.Dual (ZMod 2) ↥W) Subtype.val_injective
  by_cases hk2 : Module.finrank (ZMod 2) W ≤ 2
  · have hcard : 2 < Nat.card X := by
      rw [hn]
      have h5 : 5 ≤ n := by omega
      calc 2 < 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
    obtain ⟨y, hy1, hyt⟩ := exists_ne_pair (α := ↥X) hcard 1 tX
    obtain ⟨Zw, hZ3, -, -⟩ := hZ y hy1 hyt
    have := Submodule.finrank_le Zw
    omega
  by_cases hk3 : Module.finrank (ZMod 2) W = 3
  · have hcardF : 2 < Nat.card (Fsp h) := by
      rw [card_Fsp, hk3]
      norm_num
    obtain ⟨f, hf0', hft⟩ := exists_ne_pair (α := ↥(Fsp h)) hcardF 0
      ⟨phi h tX, phi_mem_Fsp h tX⟩
    obtain ⟨y, hy⟩ := phi_surj h f.1 ((mem_Fsp h).1 f.2)
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hf0'
      apply Subtype.ext
      rw [← hy, phi_one]
      rfl
    have hyt : y ≠ tX := by
      rintro rfl
      exact hft (Subtype.ext hy.symm)
    obtain ⟨Zw, hZ3, hy', -⟩ := hZ y hy1 hyt
    have hmem := hphi y Zw hy'
    have hdim := hAnn Zw
    have hzero : Module.finrank (ZMod 2) Zw.dualAnnihilator = 0 := by omega
    have hbot : Zw.dualAnnihilator = ⊥ := Submodule.finrank_eq_zero.1 hzero
    rw [hbot, Submodule.mem_bot] at hmem
    apply hf0'
    apply Subtype.ext
    rw [← hy]
    exact hmem
  · have hk4' : Module.finrank (ZMod 2) W = 4 := by omega
    have hn3 : n = 3 := by omega
    have hcardX : Nat.card X = 8 := by rw [hn, hn3]; norm_num
    have hcardF : Nat.card (Fsp h) = 8 := by rw [card_Fsp, hk4']; norm_num
    let φ' : ↥X → ↥(Fsp h) := fun x => ⟨phi h x, phi_mem_Fsp h x⟩
    have hsurj : Function.Surjective φ' := fun f => by
      obtain ⟨x, hx⟩ := phi_surj h f.1 ((mem_Fsp h).1 f.2)
      exact ⟨x, Subtype.ext hx⟩
    have hbij : Function.Bijective φ' :=
      hsurj.bijective_of_nat_card_le (by rw [hcardX, hcardF])
    have hinj : ∀ a b : ↥X, phi h a = phi h b → a = b := fun a b hab =>
      hbij.1 (Subtype.ext hab)
    obtain ⟨y, hy1, hyt⟩ := exists_ne_pair (α := ↥X) (by rw [hcardX]; norm_num) 1 tX
    obtain ⟨Zw, hZ3, hy', ht'⟩ := hZ y hy1 hyt
    have hmem1 := hphi y Zw hy'
    have hmem2 := hphi tX Zw ht'
    have hdim := hAnn Zw
    have hle : Module.finrank (ZMod 2) Zw.dualAnnihilator ≤ 1 := by omega
    have hne1 : phi h y ≠ 0 := fun h0 => hy1 (hinj y 1 (h0.trans (phi_one h).symm))
    have hne2 : phi h tX ≠ 0 := fun h0 => htX1 (hinj tX 1 (h0.trans (phi_one h).symm))
    have heq := eq_of_finrank_le_one hle (a := ⟨phi h y, hmem1⟩) (b := ⟨phi h tX, hmem2⟩)
      (fun h0 => hne1 (congrArg Subtype.val h0)) (fun h0 => hne2 (congrArg Subtype.val h0))
    exact hyt (hinj y tX (congrArg Subtype.val heq))

end Counting

end CFSG.Quasithin.SzN28

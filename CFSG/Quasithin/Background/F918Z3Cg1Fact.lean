module

public import CFSG.Quasithin.Background.F918Z3Cg1Def
public import CFSG.Quasithin.Background.F918Z4d
public import CFSG.Quasithin.Background.F918Z6Symm

public section

namespace CFSG.Quasithin

namespace Z3Cg1

section Normalizers

variable {Γ : Type*} [Group Γ]

theorem map_conj_eq_of_mem {D : Subgroup Γ} {b : Γ} (h : ∀ y ∈ D, b * y * b⁻¹ ∈ D)
    (h' : ∀ y ∈ D, b⁻¹ * y * b ∈ D) : D.map (MulAut.conj b).toMonoidHom = D := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · intro y hy
    refine ⟨b⁻¹ * y * b, h' y hy, ?_⟩
    show b * (b⁻¹ * y * b) * b⁻¹ = y
    group

theorem mem_of_map_conj_eq {D : Subgroup Γ} {b : Γ} (h : D.map (MulAut.conj b).toMonoidHom = D) :
    ∀ y ∈ D, b * y * b⁻¹ ∈ D := fun y hy => by
  have : b * y * b⁻¹ ∈ D.map (MulAut.conj b).toMonoidHom := ⟨y, hy, rfl⟩
  rwa [h] at this

end Normalizers

section Facts

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}

theorem eq_one_of_central (hZ : Z37 D X G T' s) {d : MulAut V} (hd : d ∈ D)
    (hc : ∀ y ∈ D, d * y = y * d) : d = 1 := by
  have := hZ.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥D) with h | h
  · have hmem : (⟨d, hd⟩ : ↥D) ∈ Subgroup.center ↥D := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [h, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hZ.nonab
    have hmem : (⟨a, ha⟩ : ↥D) ∈ Subgroup.center ↥D := by rw [h]; trivial
    rw [Subgroup.mem_center_iff] at hmem
    exact hab (congrArg Subtype.val (hmem ⟨b, hb⟩)).symm

theorem mem_X_of_normalizes (hZ : Z37 D X G T' s) {b : MulAut V} (hbG : b ∈ G)
    (hb' : ∀ y ∈ D, b⁻¹ * y * b ∈ D) {x : MulAut V} (hx : x ∈ X) : b * x * b⁻¹ ∈ X := by
  have hz : b * x * b⁻¹ ∈ D ⊔ X := hZ.DX_norm b hbG x (Subgroup.mem_sup_right hx)
  obtain ⟨d, hd, x', hx', hz'⟩ := exists_mul_of_mem_sup hZ.comm hz
  have hdc : ∀ y ∈ D, d * y = y * d := by
    intro y hy
    have hy0 : b⁻¹ * y * b ∈ D := hb' y hy
    have hcomm : (b⁻¹ * y * b) * x = x * (b⁻¹ * y * b) := hZ.comm _ hy0 x hx
    have h1 : (b * x * b⁻¹) * y = y * (b * x * b⁻¹) := by
      calc b * x * b⁻¹ * y = b * (x * (b⁻¹ * y * b)) * b⁻¹ := by group
        _ = b * ((b⁻¹ * y * b) * x) * b⁻¹ := by rw [hcomm]
        _ = y * (b * x * b⁻¹) := by group
    rw [hz'] at h1
    have h2 : x' * y = y * x' := (hZ.comm y hy x' hx').symm
    have h3 : d * y * x' = y * d * x' := by
      calc d * y * x' = d * (y * x') := by group
        _ = d * (x' * y) := by rw [h2]
        _ = d * x' * y := by group
        _ = y * (d * x') := h1
        _ = y * d * x' := by group
    exact mul_right_cancel h3
  rw [hz', eq_one_of_central hZ hd hdc, one_mul]
  exact hx'

theorem mul_self_eq_one_of_acts (hZ : Z37 D X G T' s) {b δ : MulAut V} (hδ : δ ∈ D)
    (hb2 : b * b = 1) (hiD : ∀ y ∈ D, b * y * b⁻¹ = δ * y * δ⁻¹) : δ * δ = 1 := by
  refine eq_one_of_central hZ (D.mul_mem hδ hδ) fun y hy => ?_
  have h1 : δ * y * δ⁻¹ ∈ D := D.mul_mem (D.mul_mem hδ hy) (D.inv_mem hδ)
  have h2 : b * (b * y * b⁻¹) * b⁻¹ = y := by
    calc b * (b * y * b⁻¹) * b⁻¹ = (b * b) * y * (b * b)⁻¹ := by group
      _ = y := by rw [hb2]; group
  rw [hiD y hy, hiD _ h1] at h2
  calc δ * δ * y = (δ * (δ * y * δ⁻¹) * δ⁻¹) * (δ * δ) := by group
    _ = y * (δ * δ) := by rw [h2]

theorem eq_mul_of_acts_as_inner (hZ : Z37 D X G T' s) {b δ ξ : MulAut V} (hδ : δ ∈ D)
    (hξ : ξ ∈ X) (hb2 : b * b = 1) (hiD : ∀ y ∈ D, b * y * b⁻¹ = δ * y * δ⁻¹)
    (hiX : ∀ x ∈ X, b * x * b⁻¹ = ξ * x * ξ⁻¹) : b = δ * ξ := by
  have hδ2 : δ * δ = 1 := mul_self_eq_one_of_acts hZ hδ hb2 hiD
  have hξ2 : ξ * ξ = 1 := mul_self_eq_one_of_acts hZ.symm hξ hb2 hiX
  have hδξ : δ * ξ = ξ * δ := hZ.comm δ hδ ξ hξ
  have hεD : ∀ y ∈ D, (δ * ξ) * y * (δ * ξ)⁻¹ = δ * y * δ⁻¹ := by
    intro y hy
    have h : ξ * y = y * ξ := (hZ.comm y hy ξ hξ).symm
    calc (δ * ξ) * y * (δ * ξ)⁻¹ = δ * (ξ * y) * ξ⁻¹ * δ⁻¹ := by group
      _ = δ * (y * ξ) * ξ⁻¹ * δ⁻¹ := by rw [h]
      _ = δ * y * δ⁻¹ := by group
  have hεX : ∀ x ∈ X, (δ * ξ) * x * (δ * ξ)⁻¹ = ξ * x * ξ⁻¹ := by
    intro x hx
    have h : δ * x = x * δ := hZ.comm δ hδ x hx
    calc (δ * ξ) * x * (δ * ξ)⁻¹ = δ * (ξ * x * ξ⁻¹) * δ⁻¹ := by group
      _ = ξ * x * ξ⁻¹ := by
        have hm : ξ * x * ξ⁻¹ ∈ X := X.mul_mem (X.mul_mem hξ hx) (X.inv_mem hξ)
        have h' : δ * (ξ * x * ξ⁻¹) = (ξ * x * ξ⁻¹) * δ := hZ.comm δ hδ _ hm
        rw [h']; group
  have hbδ : b * δ * b⁻¹ = δ := by rw [hiD δ hδ]; group
  have hbξ : b * ξ * b⁻¹ = ξ := by rw [hiX ξ hξ]; group
  have hbε : b * (δ * ξ) = (δ * ξ) * b := by
    have h : b * (δ * ξ) * b⁻¹ = δ * ξ := by
      calc b * (δ * ξ) * b⁻¹ = (b * δ * b⁻¹) * (b * ξ * b⁻¹) := by group
        _ = δ * ξ := by rw [hbδ, hbξ]
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hε2 : (δ * ξ) * (δ * ξ) = 1 := by
    calc (δ * ξ) * (δ * ξ) = δ * (ξ * δ) * ξ := by group
      _ = δ * (δ * ξ) * ξ := by rw [hδξ]
      _ = (δ * δ) * (ξ * ξ) := by group
      _ = 1 := by rw [hδ2, hξ2, one_mul]
  obtain ⟨c, hc⟩ : ∃ c : MulAut V, c = (δ * ξ)⁻¹ * b := ⟨_, rfl⟩
  have hcD : ∀ y ∈ D, c * y = y * c := by
    intro y hy
    have h : c * y * c⁻¹ = y := by
      calc c * y * c⁻¹ = (δ * ξ)⁻¹ * (b * y * b⁻¹) * (δ * ξ) := by rw [hc]; group
        _ = y := by rw [hiD y hy, ← hεD y hy]; group
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hcX : ∀ x ∈ X, c * x = x * c := by
    intro x hx
    have h : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = (δ * ξ)⁻¹ * (b * x * b⁻¹) * (δ * ξ) := by rw [hc]; group
        _ = x := by rw [hiX x hx, ← hεX x hx]; group
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hc2 : c * c = 1 := by
    have hbε' : b * (δ * ξ)⁻¹ = (δ * ξ)⁻¹ * b :=
      Commute.inv_right (show Commute b (δ * ξ) from hbε)
    calc c * c = (δ * ξ)⁻¹ * (b * (δ * ξ)⁻¹) * b := by rw [hc]; group
      _ = (δ * ξ)⁻¹ * ((δ * ξ)⁻¹ * b) * b := by rw [hbε']
      _ = ((δ * ξ) * (δ * ξ))⁻¹ * (b * b) := by group
      _ = 1 := by rw [hε2, hb2]; group
  have hc1 : c = 1 := Z4d.eq_one_of_commutes hZ hc2 hcD hcX
  calc b = (δ * ξ) * c := by rw [hc]; group
    _ = δ * ξ := by rw [hc1, mul_one]

theorem exists_mem_inf_of_surj (hZ : Z37 D X G T' s) {n : ℕ} (hn : 2 ≤ n)
    (hDpsl : IsPSL 2 2 n ↥D) {A : Subgroup (MulAut V)} (hA : IsElemAb2 A)
    (hND : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D) (hNX : ∀ b ∈ A, ∀ x ∈ X, b * x * b⁻¹ ∈ X)
    (hrk : 2 ≤ rk (conjRes D A hND).range)
    (hsurj : ∀ e ∈ (conjRes D A hND).range,
      ∃ b : ↥A, conjRes D A hND b = e ∧ conjRes X A hNX b = 1) :
    ∃ g ∈ A, g ∈ D ∧ g ≠ 1 := by
  obtain ⟨g, hgE, hg1⟩ :=
    exists_inner_of_two_le_rk hn hDpsl (isElemAb2_range hA (conjRes D A hND)) hrk
  obtain ⟨b, hb, hbX⟩ := hsurj _ hgE
  have hb2 : (b : MulAut V) * b = 1 := by
    have := hA.2 b b.2
    rwa [pow_two] at this
  have hiD := (conjRes_eq_conj_iff b g).1 hb
  have hiX : ∀ x ∈ X,
      (b : MulAut V) * x * (b : MulAut V)⁻¹ = (1 : MulAut V) * x * (1 : MulAut V)⁻¹ :=
    fun x hx => by
      have h := (conjRes_eq_one_iff b).1 hbX x hx
      rw [inv_one, mul_one, one_mul, mul_inv_eq_iff_eq_mul]
      exact h
  have hbg : (b : MulAut V) = g * 1 := eq_mul_of_acts_as_inner hZ g.2 X.one_mem hb2 hiD hiX
  rw [mul_one] at hbg
  refine ⟨g, ?_, g.2, ?_⟩
  · rw [← hbg]
    exact b.2
  · intro h1
    apply hg1
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]

theorem eq_one_of_conjRes_eq_one (hZ : Z37 D X G T' s) {A : Subgroup (MulAut V)}
    (hA : IsElemAb2 A) (hND : ∀ b ∈ A, ∀ y ∈ D, b * y * b⁻¹ ∈ D)
    (hNX : ∀ b ∈ A, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (b : ↥A) (hD : conjRes D A hND b = 1)
    (hX : conjRes X A hNX b = 1) : b = 1 := by
  have hb2 : (b : MulAut V) * b = 1 := by
    have := hA.2 b b.2
    rwa [pow_two] at this
  exact Subtype.ext (Z4d.eq_one_of_commutes hZ hb2 ((conjRes_eq_one_iff b).1 hD)
    ((conjRes_eq_one_iff b).1 hX))

theorem rkIdx_fixV_zpowers_eq {a : ℕ} (hZ : Z37 D X G T' s) (hV : Nat.card V = 2 ^ (16 * a))
    {j : MulAut V} (h : Nat.card ↥(fixV (Subgroup.zpowers j)) ^ 2 = Nat.card V) :
    rkIdx (fixV (Subgroup.zpowers j)) = 8 * a := by
  have h1 := card_eq_two_pow hZ.exp (fixV (Subgroup.zpowers j))
  have hrkV : rk V = 16 * a := by
    unfold rk
    rw [hV, padicValNat.prime_pow]
  rw [h1, hV, ← pow_mul] at h
  have h2 : rk (fixV (Subgroup.zpowers j)) * 2 = 16 * a := Nat.pow_right_injective (le_refl 2) h
  have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers j))
  rw [hrkV] at h3
  omega

theorem rkIdx_fixV_le_of_mem_QhatStar {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar G) :
    IsA2 G A ∧ rkIdx (fixV A) ≤ 2 * rk A := by
  obtain ⟨r, -, hr2, ⟨⟨hA2, hAr⟩, -⟩, -⟩ := QhatStar_spec hA
  refine ⟨hA2, ?_⟩
  have h1 := hA2.rAV_mul
  rw [hAr] at h1
  have h2 : ((rkIdx (fixV A) : ℕ) : ℚ) ≤ ((2 * rk A : ℕ) : ℚ) := by
    rw [← h1]
    push_cast
    exact mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg _)
  exact_mod_cast h2

omit [Finite V] in
theorem fixV_le_fixV_of_le {A B : Subgroup (MulAut V)} (h : A ≤ B) : fixV B ≤ fixV A :=
  fun _ hv x hx => hv x (h hx)

end Facts

end Z3Cg1

end CFSG.Quasithin

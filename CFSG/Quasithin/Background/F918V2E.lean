module

public import CFSG.Quasithin.Background.F918N0
public import CFSG.Quasithin.Background.SmithB51LnTopD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Z391

open CFSG.Quasithin CFSG.Quasithin.B5.Ln CFSG.Assembly.LowTwoRank Module Matrix
open scoped Matrix

section Ranks

variable {V : Type*} [CommGroup V]

theorem v2e_card_mul_lt_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (h : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) < Nat.card V ↔ rk A < rkIdx (fixV A) := by
  rw [B1.card_eq_index_mul A, B1.index_eq_two_pow hV, B1.card_elemAbelian h,
    Nat.mul_lt_mul_right (B1.card_fixV_pos A), Nat.pow_lt_pow_iff_right (by norm_num)]

theorem v2e_card_pow_le_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (h : IsElemAbelian2 B) (c : ℕ) :
    Nat.card V * 2 ^ c ≤ Nat.card B * Nat.card (fixV B) ↔ rkIdx (fixV B) + c ≤ rk B := by
  rw [B1.card_eq_index_mul B, B1.index_eq_two_pow hV, B1.card_elemAbelian h]
  have h1 : 2 ^ rkIdx (fixV B) * Nat.card (fixV B) * 2 ^ c =
      2 ^ (rkIdx (fixV B) + c) * Nat.card (fixV B) := by ring
  rw [h1, Nat.mul_le_mul_right_iff (B1.card_fixV_pos B), Nat.pow_le_pow_iff_right (by norm_num)]

theorem v2e_exists_quadratic_below [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥) (h : 3 * rkIdx (fixV A) ≤ 2 * rk ↥A) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ B ≠ ⊥ ∧ IsElemAbelian2 B ∧ IsQuadratic B ∧
      3 * rkIdx (fixV B) ≤ 2 * rk ↥B := by
  set c : ℕ := rk ↥A - rkIdx (fixV A) with hc
  let S : Set (Subgroup (MulAut V)) :=
    {B | B ≤ A ∧ B ≠ ⊥ ∧ Nat.card V * 2 ^ c ≤ Nat.card B * Nat.card (fixV B)}
  have hAS : A ∈ S := by
    refine ⟨le_rfl, hAne, ?_⟩
    rw [v2e_card_pow_le_iff hV hAe]
    omega
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) ⟨A, hAS⟩
  obtain ⟨hBA, hBne, hBc⟩ := hB
  have hBe : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩
  have hoff : IsFFStarOffender A B := by
    refine ⟨hBA, hBne, hBe, fun B' hB' => ?_⟩
    by_cases hbot : B' = ⊥
    · subst hbot
      rw [B1.card_bot_mul_card_fixV]
      calc Nat.card V = Nat.card V * 1 := (mul_one _).symm
        _ ≤ Nat.card V * 2 ^ c := Nat.mul_le_mul_left _ (Nat.one_le_two_pow)
        _ ≤ _ := hBc
    · by_contra hlt
      push Not at hlt
      have hB'S : B' ∈ S := ⟨hB'.trans hBA, hbot, by omega⟩
      have hcard : Nat.card B ≤ Nat.card B' := hmin B' hB'S
      have : B' = B := Subgroup.eq_of_le_of_card_ge hB' hcard
      subst this
      exact lt_irrefl _ hlt
  have hFFmin : IsFFStarMin A B := by
    refine ⟨hoff, fun B' hB' hFF => ?_⟩
    obtain ⟨hB'2, -, hB'B, heq⟩ := hFF
    have hB'S : B' ∈ S := ⟨hB'B.trans hBA, hB'2.2.1, by rw [heq]; exact hBc⟩
    exact Subgroup.eq_of_le_of_card_ge hB'B (hmin B' hB'S)
  refine ⟨B, hBA, hBne, hBe, B1_4_3 hV hFFmin, ?_⟩
  have h1 := (v2e_card_pow_le_iff hV hBe c).1 hBc
  have h2 : Nat.card B ≤ Nat.card A := Subgroup.card_le_of_le hBA
  rw [B1.card_elemAbelian hBe, B1.card_elemAbelian hAe] at h2
  have h3 : rk ↥B ≤ rk ↥A := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  omega

end Ranks

theorem v2e_arith {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b ≤ n) (hn : n ≤ 5)
    (h : 3 * (a + b) ≤ 2 * (a * b)) : False := by
  have ha5 : a ≤ 4 := by omega
  have hb5 : b ≤ 4 := by omega
  interval_cases a <;> interval_cases b <;> omega

section Quadratic

variable {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}

theorem v2e_quadratic_bound {n : ℕ} (hn : n = 4 ∨ n = 5)
    {π : ↥(StatedSL n (ZMod 2)) →* ↥L} {U₁ U₂ : Subgroup V}
    (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥) (h₁ : RealM L U₁ ⊥ π mat)
    (h₂ : RealM L U₂ ⊥ π dmat) {B : Subgroup (MulAut V)} (hBL : B ≤ L) (hBne : B ≠ ⊥)
    (hBe : IsElemAbelian2 B) (hBq : IsQuadratic B) :
    2 * rk ↥B < 3 * rkIdx (fixV B) := by
  have hn5 : n ≤ 5 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hab, hrk, ha1, hb1, hD⟩ := rank_bounds h₁ hBL hBe.isPGroup hBne hBq
  have hinv1 : ∀ b ∈ B, ∀ x ∈ U₁, b x ∈ U₁ := fun b hb x hx => h₁.2.2.1 ⟨b, hBL hb⟩ x hx
  have hinv2 : ∀ b ∈ B, ∀ x ∈ U₂, b x ∈ U₂ := fun b hb x hx => h₂.2.2.1 ⟨b, hBL hb⟩ x hx
  have hsum := rkSub_sup hinv1 hinv2 hinf
  rw [hsup, rkSub_top, RealM.rkSub_eq h₁ hBL, RealM.rkSub_eq h₂ hBL, fixM_mat, fixM_dmat,
    hD] at hsum
  by_contra hcon
  push Not at hcon
  exact v2e_arith ha1 hb1 hab hn5 (by omega)

end Quadratic

section Centralizer

variable {V : Type} [CommGroup V] {n : ℕ} {L : Subgroup (MulAut V)}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L}

theorem v2e_exists_intertwiner {W₁ W₂ : Subgroup V}
    {M₁ M₂ : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    {β₁ : ↥W₁ →* Multiplicative (Fin n → ZMod 2)} {β₂ : ↥W₂ →* Multiplicative (Fin n → ZMod 2)}
    (hW₁ : ∀ l : ↥L, ∀ w ∈ W₁, (l : MulAut V) w ∈ W₁)
    (hW₂ : ∀ l : ↥L, ∀ w ∈ W₂, (l : MulAut V) w ∈ W₂)
    (hβ₂s : Function.Surjective β₂) (hβ₂k : ∀ w : ↥W₂, β₂ w = 1 ↔ (w : V) ∈ (⊥ : Subgroup V))
    (hβ₁e : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : ↥W₁)
      (hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ W₁),
      Multiplicative.toAdd (β₁ ⟨((π γ : ↥L) : MulAut V) (w : V), hw⟩) =
        M₁ γ *ᵥ Multiplicative.toAdd (β₁ w))
    (hβ₂e : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : ↥W₂)
      (hw : ((π γ : ↥L) : MulAut V) (w : V) ∈ W₂),
      Multiplicative.toAdd (β₂ ⟨((π γ : ↥L) : MulAut V) (w : V), hw⟩) =
        M₂ γ *ᵥ Multiplicative.toAdd (β₂ w))
    (T : V →* V) (hT : ∀ w ∈ W₂, T w ∈ W₁)
    (hTL : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : V),
      T (((π γ : ↥L) : MulAut V) w) = ((π γ : ↥L) : MulAut V) (T w)) :
    ∃ φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2),
      (∀ w : ↥W₂,
        φ (Multiplicative.toAdd (β₂ w)) = Multiplicative.toAdd (β₁ ⟨T w, hT w w.2⟩)) ∧
      ∀ (γ : ↥(StatedSL n (ZMod 2))) (x : Fin n → ZMod 2), φ (M₂ γ *ᵥ x) = M₁ γ *ᵥ φ x := by
  have hinj : Function.Injective β₂ := by
    intro a b hab
    have h1 : β₂ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (((a * b⁻¹ : ↥W₂)) : V) ∈ (⊥ : Subgroup V) := (hβ₂k _).1 h1
    rw [Subgroup.mem_bot] at h2
    apply Subtype.ext
    have h3 : (a : V) * (b : V)⁻¹ = 1 := h2
    exact mul_inv_eq_one.1 h3
  set e₂ := MulEquiv.ofBijective β₂ ⟨hinj, hβ₂s⟩ with he₂
  let Tm : ↥W₂ →* ↥W₁ := (T.comp W₂.subtype).codRestrict W₁ (fun w => hT w w.2)
  let φm : Multiplicative (Fin n → ZMod 2) →* Multiplicative (Fin n → ZMod 2) :=
    β₁.comp (Tm.comp e₂.symm.toMonoidHom)
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.toMultiplicative.symm φm
  have hφapp : ∀ w : ↥W₂,
      φ (Multiplicative.toAdd (β₂ w)) = Multiplicative.toAdd (β₁ ⟨T w, hT w w.2⟩) := by
    intro w
    have h1 : e₂.symm (β₂ w) = w := e₂.symm_apply_apply w
    show Multiplicative.toAdd (β₁ (Tm (e₂.symm (β₂ w)))) = _
    rw [h1]
    rfl
  refine ⟨φ, hφapp, fun γ x => ?_⟩
  obtain ⟨w, hw⟩ := hβ₂s (Multiplicative.ofAdd x)
  have hx : x = Multiplicative.toAdd (β₂ w) := by rw [hw]; rfl
  have hW2 : ((π γ : ↥L) : MulAut V) (w : V) ∈ W₂ := hW₂ (π γ) w w.2
  have hTw : T (w : V) ∈ W₁ := hT w w.2
  have hW1 : ((π γ : ↥L) : MulAut V) (T (w : V)) ∈ W₁ := hW₁ (π γ) _ hTw
  rw [hx, ← hβ₂e γ w hW2, hφapp, hφapp, ← hβ₁e γ ⟨T w, hTw⟩ hW1]
  congr 2
  exact Subtype.ext (hTL γ w)

theorem v2e_schur_end {W : Subgroup V}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : RealM L W ⊥ π M) (hM : M = mat ∨ M = dmat) (hn : 1 ≤ n)
    (T : V →* V) (hT : ∀ w ∈ W, T w ∈ W)
    (hTL : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : V),
      T (((π γ : ↥L) : MulAut V) w) = ((π γ : ↥L) : MulAut V) (T w))
    (hTi : ∀ w ∈ W, T w = 1 → w = 1) : ∀ w ∈ W, T w = w := by
  obtain ⟨-, -, hLW, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨φ, hφ1, hφ2⟩ := v2e_exists_intertwiner (π := π) (β₁ := β) (β₂ := β)
    hLW hLW hβs hβk hβe hβe T hT hTL
  have hφ0 : φ ≠ 0 := by
    intro h0
    obtain ⟨w₀, hw₀⟩ := hβs (Multiplicative.ofAdd (Pi.single ⟨0, by omega⟩ 1))
    have h1 := hφ1 w₀
    rw [h0, AddMonoidHom.zero_apply] at h1
    have h2 : β ⟨T w₀, hT w₀ w₀.2⟩ = 1 := Multiplicative.toAdd.injective h1.symm
    have h3 : T (w₀ : V) = 1 := Subgroup.mem_bot.1 ((hβk _).1 h2)
    have h4 : (w₀ : V) = 1 := hTi w₀ w₀.2 h3
    have h5 : β w₀ = 1 := (hβk w₀).2 (Subgroup.mem_bot.2 h4)
    rw [hw₀] at h5
    have h6 := congrFun (Multiplicative.toAdd.injective h5 :
      (Pi.single ⟨0, by omega⟩ 1 : Fin n → ZMod 2) = 0) ⟨0, by omega⟩
    simp at h6
  have hB : ∀ g : ↥(StatedSL n (ZMod 2)), ∃ g', M g' = mat g := by
    rcases hM with rfl | rfl
    · exact fun g => ⟨g, rfl⟩
    · intro g
      obtain ⟨g', hg'⟩ := exists_dmat_eq (g : GL (Fin n) (ZMod 2))
      exact ⟨g', hg'⟩
  obtain ⟨P, hP1, hP2⟩ := exists_conj_of_intertwine hφ0 hB hφ2
  have hP : (P : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rcases hM with rfl | rfl
    · have hz : ∀ g : ↥(StatedSL n (ZMod 2)), ofGL P * g = g * ofGL P := fun g =>
        mat_injective (by rw [mat_mul, mat_mul, mat_ofGL, hP2 g])
      have h1 := congrArg mat (eq_one_of_forall_commute hz)
      rwa [mat_ofGL, mat_one] at h1
    · obtain ⟨g₀, hg₀⟩ := exists_dmat_eq P
      have hz : ∀ g : ↥(StatedSL n (ZMod 2)), g₀ * g = g * g₀ := fun g =>
        dmat_injective (by rw [dmat_mul, dmat_mul, hg₀, hP2 g])
      rw [← hg₀, eq_one_of_forall_commute hz, dmat_one]
  have hφx : ∀ x, φ x = x := fun x => by rw [← hP1, hP, one_mulVec]
  intro w hw
  have h1 := hφ1 ⟨w, hw⟩
  rw [hφx] at h1
  have h2 : β ⟨T w, hT w hw⟩ = β ⟨w, hw⟩ := Multiplicative.toAdd.injective h1.symm
  have h3 : β (⟨T w, hT w hw⟩ * ⟨w, hw⟩⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := Subgroup.mem_bot.1 ((hβk _).1 h3)
  exact mul_inv_eq_one.1 h4

theorem v2e_hom_zero {W₁ W₂ : Subgroup V} (h₁ : RealM L W₁ ⊥ π mat) (h₂ : RealM L W₂ ⊥ π dmat)
    (hn : 3 ≤ n) (T : V →* V) (hT : ∀ w ∈ W₂, T w ∈ W₁)
    (hTL : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : V),
      T (((π γ : ↥L) : MulAut V) w) = ((π γ : ↥L) : MulAut V) (T w)) :
    ∀ w ∈ W₂, T w = 1 := by
  obtain ⟨-, -, hL₁, -, β₁, -, hβ₁k, hβ₁e⟩ := h₁
  obtain ⟨-, -, hL₂, -, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := h₂
  obtain ⟨φ, hφ1, hφ2⟩ := v2e_exists_intertwiner (π := π) (β₁ := β₁) (β₂ := β₂)
    hL₁ hL₂ hβ₂s hβ₂k hβ₁e hβ₂e T hT hTL
  have hφ0 : φ = 0 := by
    by_contra hφ
    obtain ⟨P, -, hP⟩ := exists_conj_of_intertwine hφ (A := dmat) (B := mat)
      (fun g => ⟨g, rfl⟩) hφ2
    obtain ⟨B₀, hB₀⟩ := exists_fixD_lt_fixN hn
    have hσ : ∀ g : ↥(StatedSL n (ZMod 2)),
        mat ((MulEquiv.refl ↥(StatedSL n (ZMod 2))) g) =
          (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat g *
            ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      intro g
      show mat g = _
      rw [hP g, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    have h1 := fixN_map_eq (B := B₀) (σ := MulEquiv.refl _) (M := dmat) (P := P) hσ
    rw [fixM_dmat] at h1
    have h2 : B₀.map (MulEquiv.refl ↥(StatedSL n (ZMod 2))).toMonoidHom = B₀ := Subgroup.map_id B₀
    rw [h2] at h1
    omega
  intro w hw
  have h1 := hφ1 ⟨w, hw⟩
  rw [hφ0, AddMonoidHom.zero_apply] at h1
  exact Subgroup.mem_bot.1 ((hβ₁k _).1 (Multiplicative.toAdd.injective h1.symm))

theorem v2e_exists_proj (U₁ U₂ : Subgroup V) (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥) :
    ∃ T₁ : V →* V, (∀ x, T₁ x ∈ U₁) ∧ (∀ a ∈ U₁, T₁ a = a) ∧ (∀ b ∈ U₂, T₁ b = 1) := by
  have hinj : Function.Injective (U₁.subtype.coprod U₂.subtype) := by
    intro p q hpq
    have h1 : (p.1 : V) * (p.2 : V) = (q.1 : V) * (q.2 : V) := hpq
    have h2 : (p.1 : V) * (q.1 : V)⁻¹ ∈ U₁ ⊓ U₂ := by
      refine ⟨U₁.mul_mem p.1.2 (U₁.inv_mem q.1.2), ?_⟩
      have h3 : (p.1 : V) * (q.1 : V)⁻¹ = (q.2 : V) * (p.2 : V)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, mul_comm (q.2 : V)]
        exact h1
      rw [h3]
      exact U₂.mul_mem q.2.2 (U₂.inv_mem p.2.2)
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h2
    have h3 : (p.2 : V) = (q.2 : V) := mul_left_cancel (h2 ▸ h1)
    exact Prod.ext (Subtype.ext h2) (Subtype.ext h3)
  have hsurj : Function.Surjective (U₁.subtype.coprod U₂.subtype) := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top x)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  set e := MulEquiv.ofBijective (U₁.subtype.coprod U₂.subtype) ⟨hinj, hsurj⟩ with he
  refine ⟨U₁.subtype.comp ((MonoidHom.fst ↥U₁ ↥U₂).comp e.symm.toMonoidHom),
    fun x => (e.symm x).1.2, fun a ha => ?_, fun b hb => ?_⟩
  · have h1 : e.symm a = (⟨a, ha⟩, 1) := by
      rw [MulEquiv.symm_apply_eq]
      exact (mul_one a).symm
    show (((e.symm a).1 : ↥U₁) : V) = a
    rw [h1]
  · have h1 : e.symm b = (1, ⟨b, hb⟩) := by
      rw [MulEquiv.symm_apply_eq]
      exact (one_mul b).symm
    show (((e.symm b).1 : ↥U₁) : V) = 1
    rw [h1]
    rfl

theorem v2e_proj_comm {U₁ U₂ : Subgroup V} (hsup : U₁ ⊔ U₂ = ⊤) {T₁ : V →* V}
    (h1 : ∀ a ∈ U₁, T₁ a = a) (h2 : ∀ b ∈ U₂, T₁ b = 1) {g : MulAut V}
    (hg1 : ∀ a ∈ U₁, g a ∈ U₁) (hg2 : ∀ b ∈ U₂, g b ∈ U₂) (x : V) : T₁ (g x) = g (T₁ x) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top x)
  rw [map_mul, map_mul, map_mul, h1 a ha, h2 b hb, h1 _ (hg1 a ha), h2 _ (hg2 b hb), mul_one,
    mul_one]

theorem v2e_eq_one_of_commute {U₁ U₂ : Subgroup V} (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (h₁ : RealM L U₁ ⊥ π mat) (h₂ : RealM L U₂ ⊥ π dmat) (hn : 3 ≤ n) {c : MulAut V}
    (hc : ∀ x ∈ L, c * x = x * c) (hcU : c ∈ stabSub U₁) : c = 1 := by
  obtain ⟨T₁, hT₁U, hT₁a, hT₁b⟩ := v2e_exists_proj U₁ U₂ hsup hinf
  have hLc : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : V),
      c (((π γ : ↥L) : MulAut V) w) = ((π γ : ↥L) : MulAut V) (c w) := by
    intro γ w
    exact congrArg (fun f : MulAut V => f w) (hc _ (π γ).2)
  have hT₁L : ∀ (γ : ↥(StatedSL n (ZMod 2))) (x : V),
      T₁ (((π γ : ↥L) : MulAut V) x) = ((π γ : ↥L) : MulAut V) (T₁ x) :=
    fun γ x => v2e_proj_comm hsup hT₁a hT₁b (fun a ha => h₁.2.2.1 (π γ) a ha)
      (fun b hb => h₂.2.2.1 (π γ) b hb) x
  have hc2 : ∀ w ∈ U₂, c w ∈ U₂ := by
    intro w hw
    have hTL : ∀ (γ : ↥(StatedSL n (ZMod 2))) (w : V),
        (T₁.comp c.toMonoidHom) (((π γ : ↥L) : MulAut V) w) =
          ((π γ : ↥L) : MulAut V) ((T₁.comp c.toMonoidHom) w) := by
      intro γ w
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hLc, hT₁L]
    have h0 := v2e_hom_zero h₁ h₂ hn (T₁.comp c.toMonoidHom) (fun w _ => hT₁U _) hTL w hw
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top (c w))
    have h1 : T₁ (c w) = a := by rw [← hab, map_mul, hT₁a a ha, hT₁b b hb, mul_one]
    have ha1 : a = 1 := by rw [← h1]; exact h0
    rw [← hab, ha1, one_mul]
    exact hb
  have hinjc : ∀ w : V, c w = 1 → w = 1 := fun w h => c.injective (h.trans (map_one c).symm)
  have hU₁ : ∀ w ∈ U₁, c w = w :=
    v2e_schur_end h₁ (Or.inl rfl) (by omega) c.toMonoidHom
      (fun w hw => (mem_stabSub.1 hcU w).2 hw) hLc (fun w _ h => hinjc w h)
  have hU₂ : ∀ w ∈ U₂, c w = w :=
    v2e_schur_end h₂ (Or.inr rfl) (by omega) c.toMonoidHom hc2 hLc (fun w _ h => hinjc w h)
  ext x
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top x)
  rw [map_mul, hU₁ a ha, hU₂ b hb]
  rfl

theorem v2e_mem_of_normalizer {U₁ U₂ : Subgroup V} (hsup : U₁ ⊔ U₂ = ⊤) (hinf : U₁ ⊓ U₂ = ⊥)
    (h₁ : RealM L U₁ ⊥ π mat) (h₂ : RealM L U₂ ⊥ π dmat) (hn : 3 ≤ n) {a : MulAut V}
    (haN : a ∈ Subgroup.normalizer (L : Set (MulAut V))) (haU : a ∈ stabSub U₁) : a ∈ L := by
  have hgL : ∀ x ∈ L, a * x * a⁻¹ ∈ L := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have hgL' : ∀ x ∈ L, a⁻¹ * x * a ∈ L := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (L : Set (MulAut V))).inv_mem haN) x).1 hx
    simpa using h
  obtain ⟨l, hl, hinner⟩ := RealM.exists_inner h₁ (Or.inl rfl) (by omega) hgL hgL' haU
    (stabSub_bot_le ⊤ (Subgroup.mem_top a))
  have hc : ∀ x ∈ L, (l⁻¹ * a) * x = x * (l⁻¹ * a) := by
    intro x hx
    have h := hinner x hx
    calc l⁻¹ * a * x = l⁻¹ * (a * x * a⁻¹) * a := by group
      _ = l⁻¹ * (l * x * l⁻¹) * a := by rw [h]
      _ = x * (l⁻¹ * a) := by group
  have hcU : l⁻¹ * a ∈ stabSub U₁ :=
    (stabSub U₁).mul_mem ((stabSub U₁).inv_mem (RealM.hLW h₁ hl)) haU
  have h1 := v2e_eq_one_of_commute hsup hinf h₁ h₂ hn hc hcU
  have h2 : a = l := by
    have := congrArg (fun z => l * z) h1
    simpa using this
  rw [h2]
  exact hl

end Centralizer

end CFSG.Quasithin.Z391

namespace CFSG.Quasithin

theorem sumNatDual_rank_bound {X : Type} [CommGroup X] [Finite X] (hX : ∀ x : X, x ^ 2 = 1)
    {L : Subgroup (MulAut X)} {n : ℕ} (hS : SumNatDual L (⊤ : Subgroup X) n) (i2 : D35InspSum)
    {A : Subgroup (MulAut X)} (hAe : IsElemAbelian2 A) (hAne : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut X))) :
    2 * rk ↥A < 3 * rkIdx (fixV A) := by
  obtain ⟨hn, π, U₁, U₂, ⟨hsup, hinf⟩, hR₁, hR₂⟩ := hS
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  by_cases hstab : A ≤ stabSub U₁
  · by_contra hcon
    push Not at hcon
    have h₁ := B5.Ln.realM_mat_iff.2 hR₁
    have h₂ := B5.Ln.realM_dmat_iff.2 hR₂
    have hAL : A ≤ L := fun a ha =>
      Z391.v2e_mem_of_normalizer hsup hinf h₁ h₂ hn3 (hAN ha) (hstab ha)
    obtain ⟨B, hBA, hBne, hBe, hBq, hB3⟩ := Z391.v2e_exists_quadratic_below hX hAe hAne hcon
    have := Z391.v2e_quadratic_bound hn hsup hinf h₁ h₂ (hBA.trans hAL) hBne hBe hBq
    omega
  · have h := i2 X L A n U₁ U₂ hn ⟨hsup, hinf⟩ ⟨π, hR₁, hR₂⟩ hAe hAN hstab
    have := (Z391.v2e_card_mul_lt_iff hX hAe).1 h
    omega

end CFSG.Quasithin

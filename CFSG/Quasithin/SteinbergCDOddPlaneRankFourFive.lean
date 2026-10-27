module

public import CFSG.Quasithin.SteinbergCDOddPlaneAction
public import CFSG.Quasithin.SteinbergCDOddPlaneExtraspecial
public import CFSG.GroupTheory.FrattiniQuotient

public noncomputable section

namespace CFSG.Quasithin.SteinbergCD

open Module CFSG.Quasithin.SteinbergBQ Subgroup
open scoped IsMulCommutative

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_normalizer_of_inverts {G : Type*} [Group G] {Q : Subgroup G} {t : G}
    (ht : t ^ 2 = 1) (h : ∀ x ∈ Q, t⁻¹ * x * t = x⁻¹) : t ∈ normalizer (Q : Set G) := by
  have htt : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two, ht])
  have key : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx => by
    have h1 := h x hx
    rw [htt] at h1
    rw [htt, h1]
    exact inv_mem hx
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key x, fun hx => ?_⟩
  have h2 := key _ hx
  have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
    rw [htt, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ← pow_two, ht, one_mul,
      mul_one]
  rwa [e] at h2

theorem map_mem_glFixedSpace_of_mem_normalizer
    {H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ normalizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) {v : V}
    (hv : v ∈ glFixedSpace H) : (g : V →ₗ[ZMod 2] V) v ∈ glFixedSpace H := by
  intro x hx
  have hx' : g⁻¹ * x * g ∈ H := by
    have h := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    rwa [inv_inv] at h
  have h := hv _ hx'
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply] at h
  have e := congrArg (g : V →ₗ[ZMod 2] V) h
  rw [← Module.End.mul_apply (g : V →ₗ[ZMod 2] V), ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Module.End.one_apply] at e
  exact e

theorem map_mem_ker_of_commute {g t : LinearMap.GeneralLinearGroup (ZMod 2) V} (hgt : g * t = t * g)
    {v : V} (hv : v ∈ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1)) :
    (g : V →ₗ[ZMod 2] V) v ∈ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
  rw [← Module.End.mul_apply, ← Units.val_mul, ← hgt, Units.val_mul, Module.End.mul_apply, hv]

theorem mem_glFixedSpace_sup {H K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} {v : V}
    (hH : v ∈ glFixedSpace H) (hK : v ∈ glFixedSpace K) : v ∈ glFixedSpace (H ⊔ K) := by
  let S : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    { carrier := {x | (x : V →ₗ[ZMod 2] V) v = v}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, Module.End.mul_apply] at hx hy ⊢
        rw [hy, hx]
      one_mem' := rfl
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply] }
  have hle : H ⊔ K ≤ S := sup_le (fun x hx => hH x hx) fun x hx => hK x hx
  exact fun x hx => hle hx

section Klein

theorem odd_card_of_isElementaryAbelian {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) [Fintype Q]
    [IsElementaryAbelian p Q] : Odd (Fintype.card Q) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElementaryAbelian Q (p := p))
  rw [← Nat.card_eq_fintype_card, hk]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem klein_split [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Q₁ Q₂ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    [IsElementaryAbelian p Q₁] [IsElementaryAbelian p Q₂]
    (hQ12 : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x)
    {t₁ t₂ : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht₁N₁ : t₁ ∈ normalizer (Q₁ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    (ht₂N₁ : t₂ ∈ normalizer (Q₁ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    (ht₁N₂ : t₁ ∈ normalizer (Q₂ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    (ht₂N₂ : t₂ ∈ normalizer (Q₂ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) :
    LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓ LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1) ≤
      (glFixedSpace Q₁ ⊓ LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1)) ⊔
        ((commSpan Q₁ ⊓ glFixedSpace Q₂) ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1)) ⊔
        ((commSpan Q₁ ⊓ commSpan Q₂) ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓
          LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1)) := by
  classical
  have := finite_generalLinearGroup (V := V)
  have : Fintype Q₁ := Fintype.ofFinite Q₁
  have : Fintype Q₂ := Fintype.ofFinite Q₂
  have hQ₂N₁ : ∀ y ∈ Q₂, y ∈ normalizer (Q₁ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    fun y hy => mem_normalizer_of_commute fun x hx => (hQ12 x hx y hy).symm
  have hker : ∀ (t : LinearMap.GeneralLinearGroup (ZMod 2) V) (w : V),
      (t : V →ₗ[ZMod 2] V) w = w → w ∈ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1) :=
    fun t w h => by rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, h, sub_self]
  have hfixt : ∀ (t : LinearMap.GeneralLinearGroup (ZMod 2) V) (w : V),
      w ∈ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1) → (t : V →ₗ[ZMod 2] V) w = w := fun t w h => by
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hQ₂C : ∀ y ∈ Q₂, ∀ w ∈ commSpan Q₁, (y : V →ₗ[ZMod 2] V) w ∈ commSpan Q₁ :=
    fun y hy w hw => map_mem_commSpan_of_mem_normalizer (hQ₂N₁ y hy) hw
  intro v hv
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.1 hv
  have hv₁' := hfixt t₁ v hv₁
  have hv₂' := hfixt t₂ v hv₂
  have hodd₁ := odd_card_of_isElementaryAbelian hp2 Q₁
  have hodd₂ := odd_card_of_isElementaryAbelian hp2 Q₂
  set u := v - avgOp Q₁ v with hu
  have hut₁ : (t₁ : V →ₗ[ZMod 2] V) u = u := by
    rw [hu, map_sub, hv₁', avgOp_comm Q₁ ht₁N₁, hv₁']
  have hut₂ : (t₂ : V →ₗ[ZMod 2] V) u = u := by
    rw [hu, map_sub, hv₂', avgOp_comm Q₁ ht₂N₁, hv₂']
  have huC : u ∈ commSpan Q₁ := sub_avgOp_mem Q₁ hodd₁ v
  have hv_eq : v = (avgOp Q₁ v + avgOp Q₂ u) + (u - avgOp Q₂ u) := by
    rw [hu]
    abel
  rw [hv_eq]
  refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ?_) ?_
  · exact ⟨avgOp_apply_mem Q₁ v, hker t₂ _ (by rw [avgOp_comm Q₁ ht₂N₁, hv₂'])⟩
  · exact ⟨⟨avgOp_apply_mem_of_invariant Q₂ hQ₂C huC, avgOp_apply_mem Q₂ u⟩,
      hker t₁ _ (by rw [avgOp_comm Q₂ ht₁N₂, hut₁])⟩
  · exact ⟨⟨⟨Submodule.sub_mem _ huC (avgOp_apply_mem_of_invariant Q₂ hQ₂C huC),
      sub_avgOp_mem Q₂ hodd₂ u⟩, hker t₁ _ (by rw [map_sub, avgOp_comm Q₂ ht₁N₂, hut₁])⟩,
      hker t₂ _ (by rw [map_sub, avgOp_comm Q₂ ht₂N₂, hut₂])⟩

theorem klein_arith₃ {dV dK w₁ w₂ w₃ k₁ k₂ k₃ k₃' : ℕ} (hV : dV = w₂ + (w₁ + w₃))
    (hK : dK ≤ k₂ + k₁ + k₃) (h₂ : 2 * k₂ = w₂) (h₁ : 2 * k₁ = w₁) (h₃ : 2 * k₃' = w₃)
    (h₃' : 2 * k₃ = k₃') (hcod : dV - dK ≤ 4) (hw₃ : k₃' ≠ 0 → 4 ≤ k₃') : w₃ = 0 := by
  omega

theorem klein_arith₁ {dV dK w₁ w₂ w₃ k₁ k₂ k₃ : ℕ} (hV : dV = w₂ + (w₁ + w₃))
    (hK : dK ≤ k₂ + k₁ + k₃) (h₂ : 2 * k₂ = w₂) (h₁ : 2 * k₁ = w₁) (hw₃ : w₃ = 0)
    (hk₃ : k₃ ≤ w₃) (hcod : dV - dK ≤ 4) (hw₂ : 4 ≤ w₂) : w₁ + w₃ ≤ 4 := by
  omega

end Klein

theorem finrank_commSpan_le_four_of_klein [FiniteDimensional (ZMod 2) V] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {Q₁ Q₂ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    [IsElementaryAbelian p Q₁] [IsElementaryAbelian p Q₂] (hQ₂ : Q₂ ≠ ⊥)
    (hQ12 : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x) (hfix : glFixedSpace Q₁ ⊓ glFixedSpace Q₂ = ⊥)
    {t₁ t₂ : LinearMap.GeneralLinearGroup (ZMod 2) V} (ht₁ : t₁ ^ 2 = 1) (ht₂ : t₂ ^ 2 = 1)
    (ht12 : t₁ * t₂ = t₂ * t₁) (h11 : ∀ x ∈ Q₁, t₁⁻¹ * x * t₁ = x⁻¹)
    (h12 : ∀ x ∈ Q₂, t₁ * x = x * t₁) (h21 : ∀ x ∈ Q₁, t₂ * x = x * t₂)
    (h22 : ∀ x ∈ Q₂, t₂⁻¹ * x * t₂ = x⁻¹)
    (hcod : finrank (ZMod 2) V - finrank (ZMod 2)
      (LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓ LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1) :
        Submodule (ZMod 2) V) ≤ 4) :
    finrank (ZMod 2) (commSpan Q₁) ≤ 4 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have := finite_generalLinearGroup (V := V)
  have : Fintype Q₁ := Fintype.ofFinite Q₁
  have : Fintype Q₂ := Fintype.ofFinite Q₂
  have hodd₁ := odd_card_of_isElementaryAbelian hp2 Q₁
  have hodd₂ := odd_card_of_isElementaryAbelian hp2 Q₂
  have ht₁N₁ := mem_normalizer_of_inverts ht₁ h11
  have ht₂N₂ := mem_normalizer_of_inverts ht₂ h22
  have ht₁N₂ := mem_normalizer_of_commute h12
  have ht₂N₁ := mem_normalizer_of_commute h21
  have hQ₂N₁ : ∀ y ∈ Q₂, y ∈ normalizer (Q₁ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    fun y hy => mem_normalizer_of_commute fun x hx => (hQ12 x hx y hy).symm
  have hQ₁N₂ : ∀ x ∈ Q₁, x ∈ normalizer (Q₂ : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    fun x hx => mem_normalizer_of_commute fun y hy => hQ12 x hx y hy
  have hcomm₁₀ : commSpan Q₁ ⊓ glFixedSpace Q₁ = ⊥ := by
    rw [inf_comm]
    exact glFixedSpace_inf_commSpan Q₁ hodd₁
  have hcomm₂₀ : commSpan Q₂ ⊓ glFixedSpace Q₂ = ⊥ := by
    rw [inf_comm]
    exact glFixedSpace_inf_commSpan Q₂ hodd₂
  have hdimV := finrank_eq_fixed_add_comm Q₁ hodd₁ (W := ⊤) fun _ _ _ _ => Submodule.mem_top
  rw [top_inf_eq, top_inf_eq, finrank_top] at hdimV
  have hdimC := finrank_eq_fixed_add_comm Q₂ hodd₂ (W := commSpan Q₁) fun y hy w hw =>
    map_mem_commSpan_of_mem_normalizer (hQ₂N₁ y hy) hw
  have hW₂inv : ∀ y ∈ Q₂, ∀ w ∈ glFixedSpace Q₁, (y : V →ₗ[ZMod 2] V) w ∈ glFixedSpace Q₁ :=
    fun y hy w hw => map_mem_glFixedSpace_of_mem_normalizer (hQ₂N₁ y hy) hw
  have hW₂t : ∀ w ∈ glFixedSpace Q₁, (t₂ : V →ₗ[ZMod 2] V) w ∈ glFixedSpace Q₁ :=
    fun w hw => map_mem_glFixedSpace_of_mem_normalizer ht₂N₁ hw
  have hW₂h := two_mul_finrank_inf_ker_eq hp2 ht₂ h22 hW₂inv hW₂t hfix
  have hW₁h := two_mul_finrank_inf_ker_eq hp2 ht₁ h11 (W := commSpan Q₁ ⊓ glFixedSpace Q₂)
    (fun x hx w hw => ⟨map_mem_commSpan Q₁ hx (Submodule.mem_inf.1 hw).1,
      map_mem_glFixedSpace_of_mem_normalizer (hQ₁N₂ x hx) (Submodule.mem_inf.1 hw).2⟩)
    (fun w hw => ⟨t_map_mem_commSpan Q₁ h11 (Submodule.mem_inf.1 hw).1,
      map_mem_glFixedSpace_of_mem_normalizer ht₁N₂ (Submodule.mem_inf.1 hw).2⟩)
    (eq_bot_iff.2 fun v hv => by
      rw [← hcomm₁₀]
      exact ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 hv).1).1, (Submodule.mem_inf.1 hv).2⟩)
  have hW₃inv₂ : ∀ y ∈ Q₂, ∀ w ∈ commSpan Q₁ ⊓ commSpan Q₂,
      (y : V →ₗ[ZMod 2] V) w ∈ commSpan Q₁ ⊓ commSpan Q₂ := fun y hy w hw =>
    ⟨map_mem_commSpan_of_mem_normalizer (hQ₂N₁ y hy) (Submodule.mem_inf.1 hw).1,
      map_mem_commSpan Q₂ hy (Submodule.mem_inf.1 hw).2⟩
  have hW₃h := two_mul_finrank_inf_ker_eq hp2 ht₁ h11 (W := commSpan Q₁ ⊓ commSpan Q₂)
    (fun x hx w hw => ⟨map_mem_commSpan Q₁ hx (Submodule.mem_inf.1 hw).1,
      map_mem_commSpan_of_mem_normalizer (hQ₁N₂ x hx) (Submodule.mem_inf.1 hw).2⟩)
    (fun w hw => ⟨t_map_mem_commSpan Q₁ h11 (Submodule.mem_inf.1 hw).1,
      map_mem_commSpan_of_mem_normalizer ht₁N₂ (Submodule.mem_inf.1 hw).2⟩)
    (eq_bot_iff.2 fun v hv => by
      rw [← hcomm₁₀]
      exact ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 hv).1).1, (Submodule.mem_inf.1 hv).2⟩)
  have hW₃'inv₂ : ∀ y ∈ Q₂, ∀ w ∈ commSpan Q₁ ⊓ commSpan Q₂ ⊓
      LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1), (y : V →ₗ[ZMod 2] V) w ∈
        commSpan Q₁ ⊓ commSpan Q₂ ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) :=
    fun y hy w hw => ⟨hW₃inv₂ y hy w (Submodule.mem_inf.1 hw).1,
      map_mem_ker_of_commute (h12 y hy).symm (Submodule.mem_inf.1 hw).2⟩
  have hW₃'t₂ : ∀ w ∈ commSpan Q₁ ⊓ commSpan Q₂ ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1),
      (t₂ : V →ₗ[ZMod 2] V) w ∈
        commSpan Q₁ ⊓ commSpan Q₂ ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) := fun w hw =>
    ⟨⟨map_mem_commSpan_of_mem_normalizer ht₂N₁ (Submodule.mem_inf.1 (Submodule.mem_inf.1 hw).1).1,
      t_map_mem_commSpan Q₂ h22 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hw).1).2⟩,
      map_mem_ker_of_commute ht12.symm (Submodule.mem_inf.1 hw).2⟩
  have hW₃'0 : commSpan Q₁ ⊓ commSpan Q₂ ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓
      glFixedSpace Q₂ = ⊥ := eq_bot_iff.2 fun v hv => by
    rw [← hcomm₂₀]
    exact ⟨(Submodule.mem_inf.1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv).1).1).2,
      (Submodule.mem_inf.1 hv).2⟩
  have hW₃'h := two_mul_finrank_inf_ker_eq hp2 ht₂ h22 hW₃'inv₂ hW₃'t₂ hW₃'0
  have hdimK := (Submodule.finrank_mono (klein_split hp2 hQ12 ht₁N₁ ht₂N₁ ht₁N₂ ht₂N₂)).trans
    ((Submodule.finrank_add_le_finrank_add_finrank _ _).trans
      (add_le_add_left (Submodule.finrank_add_le_finrank_add_finrank _ _) _))
  have hk₃le : (commSpan Q₁ ⊓ commSpan Q₂ ⊓ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓
      LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) ≤
        commSpan Q₁ ⊓ commSpan Q₂ := fun v hv =>
    (Submodule.mem_inf.1 (Submodule.mem_inf.1 hv).1).1
  have hk₃ := Submodule.finrank_mono hk₃le
  have hW₃0 := klein_arith₃ (hdimV.trans (by rw [hdimC])) hdimK hW₂h hW₁h hW₃h hW₃'h hcod
    fun hne => four_le_finrank hp5 ht₂ h22 hW₃'inv₂ hW₃'t₂ hW₃'0 fun h => hne (by
      rw [h, finrank_bot])
  have hW₂4 : 4 ≤ finrank (ZMod 2) (glFixedSpace Q₁) := by
    refine four_le_finrank hp5 ht₂ h22 hW₂inv hW₂t hfix fun h => hQ₂ ?_
    have hW₁top : commSpan Q₁ ⊓ glFixedSpace Q₂ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [h, finrank_bot, zero_add, hdimC, hW₃0, add_zero] at hdimV
      exact hdimV.symm
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    refine Units.ext (LinearMap.ext fun v => ?_)
    have hv : v ∈ commSpan Q₁ ⊓ glFixedSpace Q₂ := by rw [hW₁top]; exact Submodule.mem_top
    exact (Submodule.mem_inf.1 hv).2 y hy
  rw [hdimC]
  exact klein_arith₁ (hdimV.trans (by rw [hdimC])) hdimK hW₂h hW₁h hW₃0 hk₃ hcod hW₂4

section Action

variable {G : Type*} [Group G]

theorem conj_action_injective {P A : Subgroup G} (hAN : A ≤ normalizer (P : Set G))
    (hfaith : ∀ a ∈ A, (∀ x ∈ P, a * x = x * a) → a = 1) :
    Function.Injective ((normalizerMonoidHom P).comp (inclusion hAN)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine Subtype.ext (hfaith a a.2 fun x hx => ?_)
  have h := congrArg (fun α : MulAut P => ((α ⟨x, hx⟩ : P) : G)) ha
  have h' : (a : G) * x * (a : G)⁻¹ = x := h
  calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
    _ = x * a := by rw [h']

theorem conj_action_apply {P A : Subgroup G} (hAN : A ≤ normalizer (P : Set G)) (a : A)
    (x : P) : (((normalizerMonoidHom P).comp (inclusion hAN) a x : P) : G) =
      (a : G) * x * (a : G)⁻¹ :=
  rfl

theorem abelian_rank_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P A : Subgroup G} [Finite P]
    [IsElementaryAbelian p P] (hPcard : Nat.card P = p ^ 2) [Finite A]
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAN : A ≤ normalizer (P : Set G))
    (hfaith : ∀ a ∈ A, (∀ x ∈ P, a * x = x * a) → a = 1) :
    Nat.card A ≤ 4 ∧ (Nat.card A = 4 → ∃ t₁ ∈ A, ∃ t₂ ∈ A, ∃ Q₁ ≤ P, ∃ Q₂ ≤ P,
      Nat.card Q₁ = p ∧ Nat.card Q₂ = p ∧ Q₁ ⊔ Q₂ = P ∧
      (∀ x ∈ Q₁, t₁⁻¹ * x * t₁ = x⁻¹) ∧ (∀ x ∈ Q₂, t₁ * x = x * t₁) ∧
      (∀ x ∈ Q₁, t₂ * x = x * t₂) ∧ (∀ x ∈ Q₂, t₂⁻¹ * x * t₂ = x⁻¹)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative P := IsElementaryAbelian.toIsMulCommutative (p := p)
  have hA2' : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (hA2 a a.2)
  have hPexp : ∀ x : P, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) _ x.2)
  obtain ⟨hle, h4⟩ := card_le_four_of_injective hp hp2 hPexp (by rw [hPcard]) hA2' _
    (conj_action_injective hAN hfaith)
  refine ⟨hle, fun hA4 => ?_⟩
  obtain ⟨t₁, t₂, Q₁, Q₂, hQ₁c, hQ₂c, hQ₁₂, h11, h12, h21, h22⟩ := h4 hA4
  have htt : ∀ s : A, (s : G)⁻¹ = s := fun s =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hA2 s s.2)
  have hinvert : ∀ (s : A) (Q : Subgroup P),
      (∀ x ∈ Q, (normalizerMonoidHom P).comp (inclusion hAN) s x = x⁻¹) →
      ∀ x ∈ Q.map P.subtype, (s : G)⁻¹ * x * s = x⁻¹ := by
    rintro s Q hs _ ⟨x, hx, rfl⟩
    have h := congrArg Subtype.val (hs x hx)
    rw [conj_action_apply] at h
    rw [htt s]
    simpa [htt s] using h
  have hcent : ∀ (s : A) (Q : Subgroup P),
      (∀ x ∈ Q, (normalizerMonoidHom P).comp (inclusion hAN) s x = x) →
      ∀ x ∈ Q.map P.subtype, (s : G) * x = x * s := by
    rintro s Q hs _ ⟨x, hx, rfl⟩
    have h := congrArg Subtype.val (hs x hx)
    rw [conj_action_apply, mul_inv_eq_iff_eq_mul] at h
    exact h
  refine ⟨t₁, t₁.2, t₂, t₂.2, Q₁.map P.subtype, map_subtype_le _, Q₂.map P.subtype,
    map_subtype_le _, by rw [card_map_of_injective P.subtype_injective, hQ₁c],
    by rw [card_map_of_injective P.subtype_injective, hQ₂c], ?_, hinvert t₁ Q₁ h11,
    hcent t₁ Q₂ h12, hcent t₂ Q₁ h21, hinvert t₂ Q₂ h22⟩
  rw [← Subgroup.map_sup, hQ₁₂, ← MonoidHom.range_eq_map, range_subtype]

open CFSG.OrderReductions.FrattiniAutomorphisms in
theorem nonabelian_rank_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P A : Subgroup G}
    [Finite P] (hPcard : Nat.card P = p ^ 3) (hPab : ∃ x y : P, x * y ≠ y * x) [Finite A]
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAN : A ≤ normalizer (P : Set G))
    (hfaith : ∀ a ∈ A, (∀ x ∈ P, a * x = x * a) → a = 1) : Nat.card A ≤ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hA2' : ∀ a : A, a ^ 2 = 1 := fun a => Subtype.ext (hA2 a a.2)
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  obtain ⟨-, hcommQ, hpowQ, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hPp
  have hW : Nat.card (P ⧸ frattini P) ∣ p ^ 2 := by
    have hdvd : Nat.card (P ⧸ frattini P) ∣ p ^ 3 := by
      rw [← hPcard]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rw [hk']
    refine pow_dvd_pow p ?_
    by_contra hk3
    have hk3' : k = 3 := by omega
    have hΦ : frattini P = ⊥ := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini P)
      rw [hk', hk3', hPcard] at h
      exact card_eq_one.1 (by
        have hpos : 0 < p ^ 3 := pow_pos hp.pos 3
        nlinarith [Nat.card_pos (α := frattini P)])
    obtain ⟨x, y, hxy⟩ := hPab
    apply hxy
    have h2 : ((x * y : P) : P ⧸ frattini P) = ((y * x : P) : P ⧸ frattini P) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hcommQ.is_comm.comm _ _
    rw [QuotientGroup.eq, hΦ, mem_bot, inv_mul_eq_one] at h2
    exact h2
  set φ := (normalizerMonoidHom P).comp (inclusion hAN)
  have hφinj := conj_action_injective hAN hfaith
  have hφ'inj : Function.Injective ((quotientAutomorphism (frattini P)).comp φ) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply hφinj
    rw [map_one]
    have hker : φ a ∈ (quotientAutomorphism (frattini P)).ker := ha
    obtain ⟨k, hk⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hPp).2 ⟨φ a, hker⟩
    have h1 : (φ a) ^ p ^ k = 1 := congrArg Subtype.val hk
    have h2 : (φ a) ^ 2 = 1 := by rw [← map_pow, hA2' a, map_one]
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  exact (card_le_four_of_injective hp hp2 hpowQ hW hA2' _ hφ'inj).1

end Action

theorem odd_plane_two_action_bound_rank_four_five_support [FiniteDimensional (ZMod 2) V]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {Γ P : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} (hO2 : CFSG.pCore 2 Γ = ⊥)
    (hPΓ : P ≤ Γ) (hPn : (P.subgroupOf Γ).Normal) (hΓP : IsPGroup 2 (Γ ⧸ P.subgroupOf Γ))
    (hPtype : (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      ((∃ x y : P, x * y ≠ y * x) ∧ Nat.card P = p ^ 3 ∧ ∀ x : P, x ^ p = 1))
    (hVP : commSpan P = ⊤) {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    (hAΓ : A ≤ Γ) [IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥) {r : ℕ} (hr : Nat.card A = 2 ^ r)
    (hcodim : finrank (ZMod 2) (V ⧸ glFixedSpace A) ≤ 2 * r) :
    p = 5 ∧ IsElementaryAbelian 5 P ∧ Nat.card P = 25 ∧
      ∃ Q ≤ P, Nat.card Q = 5 ∧ finrank (ZMod 2) (commSpan Q) = 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have := finite_generalLinearGroup (V := V)
  have hcodA : finrank (ZMod 2) V - finrank (ZMod 2) (glFixedSpace A) ≤ 2 * r := by
    have h := Submodule.finrank_quotient_add_finrank (glFixedSpace A)
    omega
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hAN : A ≤ normalizer (P : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) :=
    hAΓ.trans ((normal_subgroupOf_iff_le_normalizer hPΓ).1 hPn)
  have hfaith : ∀ a ∈ A, (∀ x ∈ P, a * x = x * a) → a = 1 := fun a ha hax =>
    eq_one_of_commute_of_pCore_eq_bot hPΓ hPn hΓP hO2 (hAΓ ha) hax ⟨1, by
      rw [pow_one]; exact hA2 a ha⟩
  have hinv : ∀ t ∈ A, t ≠ 1 → ∃ y ∈ P, y ≠ 1 ∧ t⁻¹ * y * t = y⁻¹ := by
    intro t ht ht1
    obtain ⟨x, hx, htx⟩ : ∃ x ∈ P, t * x * t⁻¹ ≠ x := by
      by_contra h
      push Not at h
      exact ht1 (hfaith t ht fun x hx => by
        have := h x hx
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this)
    exact exists_inverted (hA2 t ht) (hAN ht) hx htx
  have hzinv : ∀ (t y : LinearMap.GeneralLinearGroup (ZMod 2) V), t⁻¹ * y * t = y⁻¹ →
      ∀ x ∈ zpowers y, t⁻¹ * x * t = x⁻¹ := by
    intro t y hty x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
    have e := conj_zpow (a := t⁻¹) (b := y) (i := n)
    rw [inv_inv] at e
    rw [← e, hty, inv_zpow]
  have hmove : ∀ t ∈ A, ∀ y : LinearMap.GeneralLinearGroup (ZMod 2) V, y ^ p = 1 →
      t⁻¹ * y * t = y⁻¹ → finrank (ZMod 2) (commSpan (zpowers y)) ≤ 4 * r := by
    intro t ht y hyp hty
    have := IsElementaryAbelian.zpowers_of_pow_eq_one hyp
    have h := finrank_commSpan_le hp2 (hA2 t ht) (hzinv t y hty)
    have hle : glFixedSpace A ≤ LinearMap.ker ((t : V →ₗ[ZMod 2] V) - 1) := fun v hv => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hv t ht, sub_self]
    have := Submodule.finrank_mono hle
    omega
  have hA4 : Nat.card A ≤ 4 := by
    rcases hPtype with ⟨hPel, hPcard⟩ | ⟨hPab, hPcard, -⟩
    · exact (abelian_rank_bound hp hp2 hPcard hA2 hAN hfaith).1
    · exact nonabelian_rank_bound hp hp2 hPcard hPab hA2 hAN hfaith
  have hr2 : r ≤ 2 := by
    rw [hr] at hA4
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨⟨t, htA⟩, ht1⟩ := ne_bot_iff_exists_ne_one.1 hA1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  rcases hPtype with ⟨hPel, hPcard⟩ | ⟨hPab, hPcard, hPexp⟩
  ·
    have hPexp : ∀ x ∈ P, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
    have hconclude : ∀ (Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)), Q ≤ P →
        p = 5 → Nat.card Q = 5 → finrank (ZMod 2) (commSpan Q) = 4 →
        p = 5 ∧ IsElementaryAbelian 5 P ∧ Nat.card P = 25 ∧
          ∃ Q ≤ P, Nat.card Q = 5 ∧ finrank (ZMod 2) (commSpan Q) = 4 := by
      rintro Q hQP rfl hQ hQd
      exact ⟨rfl, hPel, by rw [hPcard]; norm_num, Q, hQP, hQ, hQd⟩
    by_cases hr1 : r ≤ 1
    ·
      obtain ⟨y, hyP, hy1, hty⟩ := hinv t htA ht1'
      have hyp := hPexp y hyP
      have := IsElementaryAbelian.zpowers_of_pow_eq_one hyp
      have hle := hmove t htA y hyp hty
      have hQ1 : zpowers y ≠ ⊥ := fun h => hy1 (by
        have := mem_zpowers y
        rw [h, mem_bot] at this
        exact this)
      obtain ⟨-, -, -, -, h5⟩ := small_inverted_odd_binary_module_forces_cyclic_five_support
        hp5 (zpowers y) hQ1 t (hA2 t htA) (hzinv t y hty)
      obtain ⟨hp5', hcard, hdim, -⟩ := h5 (by omega)
      exact hconclude _ (zpowers_le.2 hyP) hp5' hcard hdim
    ·
      have hr2' : r = 2 := by omega
      obtain ⟨-, h4⟩ := abelian_rank_bound hp hp2 hPcard hA2 hAN hfaith
      obtain ⟨t₁, ht₁, t₂, ht₂, Q₁, hQ₁P, Q₂, hQ₂P, hQ₁c, hQ₂c, hQ₁₂, h11, h12, h21, h22⟩ :=
        h4 (by rw [hr, hr2']; norm_num)
      have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => by
        have := (IsElementaryAbelian.toIsMulCommutative (p := p) (G := P)).is_comm.comm
          ⟨a, ha⟩ ⟨b, hb⟩
        exact congrArg Subtype.val this
      have helem : ∀ Q ≤ P, IsElementaryAbelian p Q := fun Q hQ =>
        { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hPcomm _ (hQ x.2) _ (hQ y.2))⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
            Subtype.ext (by
              rw [Subgroup.coe_pow, Subgroup.coe_one]
              exact hPexp _ (hQ x.2)) }
      have := helem Q₁ hQ₁P
      have := helem Q₂ hQ₂P
      have hne : ∀ Q : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V), Nat.card Q = p →
          Q ≠ ⊥ := fun Q hQ h => by
        rw [h, card_bot] at hQ
        exact hp.one_lt.ne hQ
      have hfixP : glFixedSpace Q₁ ⊓ glFixedSpace Q₂ = ⊥ := by
        refine eq_bot_iff.2 fun v hv => ?_
        have hvP : v ∈ glFixedSpace P := by
          have h := mem_glFixedSpace_sup (Submodule.mem_inf.1 hv).1 (Submodule.mem_inf.1 hv).2
          rwa [hQ₁₂] at h
        have : Fintype P := Fintype.ofFinite P
        have hodd : Odd (Fintype.card P) := by
          rw [← Nat.card_eq_fintype_card, hPcard]
          exact (hp.odd_of_ne_two hp2).pow
        have hmem : v ∈ glFixedSpace P ⊓ commSpan P :=
          ⟨hvP, by rw [hVP]; exact Submodule.mem_top⟩
        rw [glFixedSpace_inf_commSpan P hodd] at hmem
        exact hmem
      have hcod2 : finrank (ZMod 2) V - finrank (ZMod 2)
          (LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓
            LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1) : Submodule (ZMod 2) V) ≤ 4 := by
        have hle : glFixedSpace A ≤ LinearMap.ker ((t₁ : V →ₗ[ZMod 2] V) - 1) ⊓
            LinearMap.ker ((t₂ : V →ₗ[ZMod 2] V) - 1) := fun v hv => by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩ <;>
            rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
          · exact hv _ ht₁
          · exact hv _ ht₂
        have := Submodule.finrank_mono hle
        omega
      have hQ12 : ∀ x ∈ Q₁, ∀ y ∈ Q₂, x * y = y * x := fun x hx y hy =>
        hPcomm x (hQ₁P hx) y (hQ₂P hy)
      have ht12 : t₁ * t₂ = t₂ * t₁ := congrArg Subtype.val
        (mul_comm_of_sq_eq_one (fun a : A => Subtype.ext (hA2 a a.2)) ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩)
      have hle4 := finrank_commSpan_le_four_of_klein hp5 (hne Q₂ hQ₂c) hQ12 hfixP (hA2 t₁ ht₁)
        (hA2 t₂ ht₂) ht12 h11 h12 h21 h22 hcod2
      obtain ⟨-, -, -, -, h5⟩ := small_inverted_odd_binary_module_forces_cyclic_five_support
        hp5 Q₁ (hne Q₁ hQ₁c) t₁ (hA2 t₁ ht₁) h11
      obtain ⟨hp5', hcard, hdim, -⟩ := h5 hle4
      exact hconclude Q₁ hQ₁P hp5' hcard hdim
  ·
    exfalso
    obtain ⟨y, hyP, hy1, hty⟩ := hinv t htA ht1'
    have hPexp' : ∀ x ∈ P, x ^ p = 1 := fun x hx => congrArg Subtype.val (hPexp ⟨x, hx⟩)
    have h12 := twelve_le_finrank_commSpan_zpowers hp hp5 hPcard hPab hPexp' hyP hy1
    have hle := hmove t htA y (hPexp' y hyP) hty
    omega

end CFSG.Quasithin.SteinbergCD

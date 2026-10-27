module

public import CFSG.Quasithin.Background.G11Defs
import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

open CFSG.GroupTheory.GLnTwoSplitting
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section General

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem transvection_congr {f f' : Module.Dual (ZMod 2) W} {d d' : W} (hf : f = f')
    (hd : d = d') (h : f d = 0) (h' : f' d' = 0) :
    LinearEquiv.transvection h = LinearEquiv.transvection h' := by
  subst hf; subst hd; rfl

private theorem transvection_mem_congr {N : Subgroup (W ≃ₗ[ZMod 2] W)}
    {f f' : Module.Dual (ZMod 2) W} {d d' : W} (hf : f = f') (hd : d = d') (h : f d = 0)
    (h' : f' d' = 0) (hN : LinearEquiv.transvection h' ∈ N) : LinearEquiv.transvection h ∈ N := by
  rwa [transvection_congr hf hd h h']

theorem eq_top_of_forall_transvection_mem [Finite W] (N : Subgroup (W ≃ₗ[ZMod 2] W))
    (h : ∀ (β : Module.Dual (ZMod 2) W) (a : W) (hβa : β a = 0),
      LinearEquiv.transvection hβa ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← closure_transvections_eq_top]
  exact (Subgroup.closure_le N).2 (by rintro _ ⟨β, a, hβa, rfl⟩; exact h β a hβa)

theorem exists_commutator_transvection [Finite W] (hdim : 3 ≤ Module.finrank (ZMod 2) W)
    (β : Module.Dual (ZMod 2) W) (a : W) (h : β a = 0) :
    ∃ p q : W ≃ₗ[ZMod 2] W, p * q * p⁻¹ * q⁻¹ = LinearEquiv.transvection h := by
  by_cases hβ : β = 0
  · subst hβ
    exact ⟨1, 1, by rw [transvection_zero_form]; simp⟩
  by_cases ha : a = 0
  · subst ha
    exact ⟨1, 1, by rw [transvection_eq_one]; simp⟩
  have hker := finrank_ker_add_one_ge β
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {a}) = 1 :=
    finrank_span_singleton ha
  obtain ⟨d, hdker, hd⟩ := exists_mem_notMem_of_finrank_lt (U := LinearMap.ker β)
    (S := Submodule.span (ZMod 2) {a}) (by omega)
  have hβd : β d = 0 := hdker
  obtain ⟨γ, hγ, hγd⟩ := exists_dual_eq_one_of_notMem hd
  have hγa : γ a = 0 := hγ a (Submodule.mem_span_singleton_self a)
  have hβda : β (d + a) = 0 := by rw [map_add, hβd, h, add_zero]
  have hβdad : β (d + a + d) = 0 := by rw [map_add, hβda, hβd, add_zero]
  refine ⟨LinearEquiv.transvection hγa, LinearEquiv.transvection hβd, ?_⟩
  have e1 := mul_transvection_mul_inv (LinearEquiv.transvection hγa) hβd
    (transvection_comp_apply_eq_zero _ hβd)
  have hsymm : (LinearEquiv.transvection hγa).symm = LinearEquiv.transvection hγa :=
    transvection_inv hγa
  have e2 : LinearEquiv.transvection
        (transvection_comp_apply_eq_zero (LinearEquiv.transvection hγa) hβd) =
      LinearEquiv.transvection hβda := by
    refine transvection_congr ?_ ?_ _ _
    · refine LinearMap.ext fun x => ?_
      show β ((LinearEquiv.transvection hγa).symm x) = β x
      rw [hsymm, transvection_apply, map_add, map_smul, h, smul_zero, add_zero]
    · rw [transvection_apply, hγd, one_smul]
  rw [e1, e2, transvection_inv hβd, transvection_mul_transvection_left hβda hβd hβdad]
  exact transvection_congr rfl (by rw [add_comm d a, add_assoc, two_add_self, add_zero]) _ _

private theorem exists_apply_zero_one {β₁ β₂ : Module.Dual (ZMod 2) W} (h : β₁ ≠ β₂)
    (h₂ : β₂ ≠ 0) : ∃ c, β₁ c = 0 ∧ β₂ c = 1 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.1 h
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.1 h₂
  rw [LinearMap.zero_apply] at hy
  have hy1 : β₂ y = 1 := zmod_two_eq_one_of_ne_zero hy
  rcases zmod_two_eq_zero_or_one (β₁ x) with hx0 | hx1
  · exact ⟨x, hx0, zmod_two_eq_one_of_ne_zero fun h0 => hx (hx0.trans h0.symm)⟩
  · have hx2 : β₂ x = 0 := by
      rcases zmod_two_eq_zero_or_one (β₂ x) with h0 | h1
      · exact h0
      · exact absurd (hx1.trans h1.symm) hx
    rcases zmod_two_eq_zero_or_one (β₁ y) with hy0 | hy1'
    · exact ⟨y, hy0, hy1⟩
    · refine ⟨x + y, ?_, ?_⟩
      · rw [map_add, hx1, hy1', zmod_two_add_self]
      · rw [map_add, hx2, hy1, zero_add]

private theorem transvection_mem_add {N : Subgroup (W ≃ₗ[ZMod 2] W)}
    {β₁ β₂ : Module.Dual (ZMod 2) W}
    (h₁ : ∀ (a : W) (h : β₁ a = 0), LinearEquiv.transvection h ∈ N)
    (h₂ : ∀ (a : W) (h : β₂ a = 0), LinearEquiv.transvection h ∈ N) :
    ∀ (a : W) (h : (β₁ + β₂) a = 0), LinearEquiv.transvection h ∈ N := by
  by_cases e1 : β₁ = 0
  · subst e1
    intro a h
    exact transvection_mem_congr (zero_add β₂) rfl h _ (h₂ a (by simpa using h))
  by_cases e2 : β₂ = 0
  · subst e2
    intro a h
    exact transvection_mem_congr (add_zero β₁) rfl h _ (h₁ a (by simpa using h))
  by_cases e12 : β₁ = β₂
  · subst e12
    intro a h
    have hz : β₁ + β₁ = 0 := LinearMap.ext fun x => by simp [zmod_two_add_self]
    refine transvection_mem_congr hz rfl h (by simp) ?_
    rw [transvection_zero_form]
    exact N.one_mem
  obtain ⟨c₁, hc₁0, hc₁1⟩ := exists_apply_zero_one e12 e2
  obtain ⟨c₂, hc₂0, hc₂1⟩ := exists_apply_zero_one (Ne.symm e12) e1
  have key : ∀ (a : W) (h : (β₁ + β₂) a = 0), β₁ a = 1 → LinearEquiv.transvection h ∈ N := by
    intro a h ha1
    have ha2 : β₂ a = 1 := by
      rw [LinearMap.add_apply, ha1] at h
      rcases zmod_two_eq_zero_or_one (β₂ a) with h0 | h1
      · rw [h0] at h
        exact absurd h one_ne_zero
      · exact h1
    have hs : β₂ (a + c₁) = 0 := by rw [map_add, ha2, hc₁1, zmod_two_add_self]
    have hts := N.mul_mem (N.mul_mem (h₁ c₁ hc₁0) (h₂ (a + c₁) hs)) (N.inv_mem (h₁ c₁ hc₁0))
    rw [mul_transvection_mul_inv _ hs (transvection_comp_apply_eq_zero _ hs)] at hts
    refine transvection_mem_congr ?_ ?_ h _ hts
    · refine LinearMap.ext fun x => ?_
      show (β₁ + β₂) x = β₂ ((LinearEquiv.transvection hc₁0).symm x)
      rw [show (LinearEquiv.transvection hc₁0).symm = LinearEquiv.transvection hc₁0 from
        transvection_inv hc₁0, transvection_apply, map_add, map_smul, hc₁1, smul_eq_mul, mul_one,
        LinearMap.add_apply, add_comm]
    · rw [transvection_apply, map_add, ha1, hc₁0, add_zero, one_smul, add_assoc, two_add_self,
        add_zero]
  intro a h
  rcases zmod_two_eq_zero_or_one (β₁ a) with ha | ha
  · have hw1 : β₁ (c₁ + c₂) = 1 := by rw [map_add, hc₁0, hc₂1, zero_add]
    have hw2 : β₂ (c₁ + c₂) = 1 := by rw [map_add, hc₁1, hc₂0, add_zero]
    have hwf : (β₁ + β₂) (c₁ + c₂) = 0 := by
      rw [LinearMap.add_apply, hw1, hw2, zmod_two_add_self]
    have haw : (β₁ + β₂) (a + (c₁ + c₂)) = 0 := by rw [map_add, hwf, h, add_zero]
    have hm := N.mul_mem (key _ haw (by rw [map_add, ha, hw1, zero_add])) (key _ hwf hw1)
    rw [transvection_mul_transvection_left haw hwf
      (by rw [map_add, haw, hwf, add_zero])] at hm
    exact transvection_mem_congr rfl (by rw [add_assoc, two_add_self, add_zero]) h _ hm
  · exact key a h ha

private def transvForms (N : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Submodule (ZMod 2) (Module.Dual (ZMod 2) W) where
  carrier := {β | ∀ (a : W) (h : β a = 0), LinearEquiv.transvection h ∈ N}
  add_mem' := fun {_ _} h₁ h₂ => transvection_mem_add h₁ h₂
  zero_mem' := fun a h => by rw [transvection_zero_form]; exact N.one_mem
  smul_mem' := by
    intro c β hβ
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact fun a h => by rw [transvection_zero_form]; exact N.one_mem
    · rw [one_smul]
      exact hβ

private theorem comp_symm_mem_transvForms {N : Subgroup (W ≃ₗ[ZMod 2] W)}
    {β : Module.Dual (ZMod 2) W} (hβ : β ∈ transvForms N) {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ N) :
    β ∘ₗ (g.symm : W →ₗ[ZMod 2] W) ∈ transvForms N := by
  intro a h'
  have h : β (g.symm a) = 0 := h'
  have hm := N.mul_mem (N.mul_mem hg (hβ _ h)) (N.inv_mem hg)
  rw [mul_transvection_mul_inv g h (transvection_comp_apply_eq_zero g h)] at hm
  exact transvection_mem_congr rfl (g.apply_symm_apply a).symm h' _ hm

private theorem eq_top_of_irr_of_forall_transvection_mem [Finite W]
    (N : Subgroup (W ≃ₗ[ZMod 2] W))
    (hirr : ∀ S : Submodule (ZMod 2) W, (∀ g ∈ N, ∀ s ∈ S, g s ∈ S) → S = ⊥ ∨ S = ⊤)
    (α : Module.Dual (ZMod 2) W) (hα : α ≠ 0)
    (hfull : ∀ (a : W) (h : α a = 0), LinearEquiv.transvection h ∈ N) : N = ⊤ := by
  have hαS : α ∈ transvForms N := hfull
  have hinv : ∀ g ∈ N, ∀ s ∈ (transvForms N).dualCoannihilator,
      g s ∈ (transvForms N).dualCoannihilator := by
    intro g hg s hs
    rw [Submodule.mem_dualCoannihilator]
    intro β hβ
    exact (Submodule.mem_dualCoannihilator _).1 hs _ (comp_symm_mem_transvForms hβ (N.inv_mem hg))
  have hS0 : (transvForms N).dualCoannihilator = ⊥ := by
    rcases hirr _ hinv with h | h
    · exact h
    · refine absurd (LinearMap.ext fun x => ?_) hα
      have hx : x ∈ (transvForms N).dualCoannihilator := by rw [h]; trivial
      exact (Submodule.mem_dualCoannihilator _).1 hx α hαS
  have hS : transvForms N = ⊤ := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq (transvForms N)
    rw [hS0, finrank_bot, add_zero] at h
    have h2 : Module.finrank (ZMod 2) (transvForms N) =
        Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) := by
      rw [h, Subspace.dual_finrank_eq]
    exact Submodule.eq_top_of_finrank_eq h2
  refine eq_top_of_forall_transvection_mem N fun β a h => ?_
  have hβ : β ∈ transvForms N := by rw [hS]; trivial
  exact hβ a h

end General

theorem exists_linearEquiv_fix_dual (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (a : U) (ha : a ≠ 0) (α β : Module.Dual (ZMod 2) U) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hαa : α a = 0) (hβa : β a = 0) :
    ∃ g : U ≃ₗ[ZMod 2] U, g a = a ∧ ∀ u, β (g u) = α u := by
  have _ := ha
  obtain ⟨g, hga, hg⟩ := exists_comp_eq_of_apply_eq_zero hβ hα hβa hαa
  exact ⟨g, hga, fun u => LinearMap.congr_fun hg u⟩

private def inducedSub (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    Subgroup (U ≃ₗ[ZMod 2] U) where
  carrier := {g | ∃ k ∈ K, ∀ u : U, k (u : V) = ((g u : U) : V)}
  mul_mem' := by
    rintro a b ⟨k₁, hk₁, h₁⟩ ⟨k₂, hk₂, h₂⟩
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, fun u => ?_⟩
    show k₁ (k₂ (u : V)) = ((a (b u) : U) : V)
    rw [h₂ u]
    exact h₁ (b u)
  one_mem' := ⟨1, K.one_mem, fun u => rfl⟩
  inv_mem' := by
    rintro g ⟨k, hk, h⟩
    refine ⟨k⁻¹, K.inv_mem hk, fun u => ?_⟩
    show k.symm (u : V) = _
    rw [LinearEquiv.symm_apply_eq, h (g⁻¹ u)]
    show (u : V) = (((g * g⁻¹) u : U) : V)
    rw [mul_inv_cancel]
    rfl

private theorem exists_mem_inducedSub (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hK : Invariant K U) {k : GLV V} (hk : k ∈ K) :
    ∃ g ∈ inducedSub K U, ∀ u : U, k (u : V) = ((g u : U) : V) := by
  have hmap : U.map (k : V →ₗ[ZMod 2] V) = U := by
    refine le_antisymm ?_ fun u hu => ⟨k.symm u, hK k⁻¹ (K.inv_mem hk) u hu, k.apply_symm_apply u⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hK k hk u hu
  exact ⟨LinearEquiv.ofSubmodules k U U hmap, ⟨k, hk, fun u => rfl⟩, fun u => rfl⟩

theorem autAll_of_fullTransvections [Finite V] (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hirr : IsIrr K U) (α : U →ₗ[ZMod 2] ZMod 2) (hα : α ≠ 0)
    (hfull : ∀ a : U, α a = 0 → ∃ k ∈ K, ∀ u : U, k (u : V) = (u : V) + α u • (a : V)) :
    AutAll K U := by
  have htop : inducedSub K U = ⊤ := by
    refine eq_top_of_irr_of_forall_transvection_mem _ ?_ α hα ?_
    · intro S hS
      have hJ : Invariant K (S.map U.subtype) := by
        rintro k hk _ ⟨s, hs, rfl⟩
        obtain ⟨g, hg, hkg⟩ := exists_mem_inducedSub K U hirr.1 hk
        exact ⟨g s, hS g hg s hs, (hkg s).symm⟩
      rcases hirr.2.2 _ hJ bot_le (Submodule.map_subtype_le U S) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype
          (h.trans (Submodule.map_bot _).symm)
      · right
        refine Submodule.map_injective_of_injective U.injective_subtype ?_
        rw [h, Submodule.map_top, Submodule.range_subtype]
    · intro a h
      obtain ⟨k, hk, hka⟩ := hfull a h
      exact ⟨k, hk, fun u => by rw [hka u]; rfl⟩
  intro g
  have hg : g ∈ inducedSub K U := by rw [htop]; trivial
  exact hg

theorem autAll_of_comm_quotient [Finite V] (U : Submodule (ZMod 2) V)
    (hdim : 3 ≤ Module.finrank (ZMod 2) U) (H X : Subgroup (GLV V)) (hH : Invariant H U)
    (hX : Invariant X U) (hnorm : ∀ x ∈ X, ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hall : AutAll (H ⊔ X) U) : AutAll H U := by
  have hXnorm : X ≤ Subgroup.normalizer (H : Set (GLV V)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm x hx h hh, fun hh => ?_⟩
    simpa [mul_assoc] using hnorm x⁻¹ (X.inv_mem hx) _ hh
  have hdecomp : ∀ g : U ≃ₗ[ZMod 2] U,
      ∃ n ∈ inducedSub H U, ∃ q ∈ inducedSub X U, g = n * q := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hall g
    have hk' : k ∈ (H : Set (GLV V)) * (X : Set (GLV V)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left H X hXnorm]
      exact hk
    obtain ⟨h, hh, x, hx, rfl⟩ := hk'
    obtain ⟨n, hn, hhn⟩ := exists_mem_inducedSub H U hH hh
    obtain ⟨q, hq, hxq⟩ := exists_mem_inducedSub X U hX hx
    refine ⟨n, hn, q, hq, LinearEquiv.ext fun u => Subtype.ext ?_⟩
    rw [← hkg u]
    show h (x (u : V)) = ((n (q u) : U) : V)
    rw [hxq u]
    exact hhn (q u)
  have hQcomm : ∀ q₁ ∈ inducedSub X U, ∀ q₂ ∈ inducedSub X U, q₁ * q₂ = q₂ * q₁ := by
    rintro q₁ ⟨x₁, hx₁, h₁⟩ q₂ ⟨x₂, hx₂, h₂⟩
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    have e : x₁ (x₂ (u : V)) = x₂ (x₁ (u : V)) :=
      congrArg (fun f : GLV V => f (u : V)) (hcomm x₁ hx₁ x₂ hx₂)
    have l₁ : ((q₁ (q₂ u) : U) : V) = x₁ (x₂ (u : V)) := by rw [← h₁ (q₂ u), ← h₂ u]
    have l₂ : ((q₂ (q₁ u) : U) : V) = x₂ (x₁ (u : V)) := by rw [← h₂ (q₁ u), ← h₁ u]
    show ((q₁ (q₂ u) : U) : V) = ((q₂ (q₁ u) : U) : V)
    rw [l₁, l₂]
    exact e
  have hQN : ∀ q ∈ inducedSub X U, ∀ n ∈ inducedSub H U, q * n * q⁻¹ ∈ inducedSub H U := by
    rintro q ⟨x, hx, hxq⟩ n ⟨h, hh, hhn⟩
    refine ⟨x * h * x⁻¹, hnorm x hx h hh, fun u => ?_⟩
    have hinv : (x⁻¹ : GLV V) (u : V) = ((q⁻¹ u : U) : V) := by
      show x.symm (u : V) = _
      rw [LinearEquiv.symm_apply_eq, hxq (q⁻¹ u)]
      show (u : V) = (((q * q⁻¹) u : U) : V)
      rw [mul_inv_cancel]
      rfl
    show x (h (x⁻¹ (u : V))) = ((q (n (q⁻¹ u)) : U) : V)
    rw [hinv, hhn (q⁻¹ u)]
    exact hxq (n (q⁻¹ u))
  have hNnormal : (inducedSub H U).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨n₀, hn₀, q₀, hq₀, rfl⟩ := hdecomp g
    have e : n₀ * q₀ * n * (n₀ * q₀)⁻¹ = n₀ * (q₀ * n * q₀⁻¹) * n₀⁻¹ := by group
    rw [e]
    exact (inducedSub H U).mul_mem ((inducedSub H U).mul_mem hn₀ (hQN q₀ hq₀ n hn))
      ((inducedSub H U).inv_mem hn₀)
  have hcommN : ∀ a b : U ≃ₗ[ZMod 2] U, a * b * a⁻¹ * b⁻¹ ∈ inducedSub H U := by
    intro a b
    obtain ⟨n₁, hn₁, q₁, hq₁, rfl⟩ := hdecomp a
    obtain ⟨n₂, hn₂, q₂, hq₂, rfl⟩ := hdecomp b
    rw [← QuotientGroup.eq_one_iff]
    have h₁ : ((n₁ : U ≃ₗ[ZMod 2] U) : (U ≃ₗ[ZMod 2] U) ⧸ inducedSub H U) = 1 :=
      (QuotientGroup.eq_one_iff n₁).2 hn₁
    have h₂ : ((n₂ : U ≃ₗ[ZMod 2] U) : (U ≃ₗ[ZMod 2] U) ⧸ inducedSub H U) = 1 :=
      (QuotientGroup.eq_one_iff n₂).2 hn₂
    have h₃ : ((q₁ : U ≃ₗ[ZMod 2] U) : (U ≃ₗ[ZMod 2] U) ⧸ inducedSub H U) * q₂ = q₂ * q₁ := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hQcomm q₁ hq₁ q₂ hq₂]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h₁, h₂, one_mul]
    rw [h₃]
    group
  have htop : inducedSub H U = ⊤ := by
    refine eq_top_of_forall_transvection_mem _ fun β a h => ?_
    obtain ⟨p, q, hpq⟩ := exists_commutator_transvection hdim β a h
    rw [← hpq]
    exact hcommN p q
  intro g
  have hg : g ∈ inducedSub H U := by rw [htop]; trivial
  exact hg

end G11

end CFSG.Quasithin

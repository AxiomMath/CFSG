module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

namespace FFC

namespace Sp4Off

open CFSG.Quasithin.H

variable {ι : Type} [Fintype ι] {K : Type} [Field K]

omit [Fintype ι] in
theorem toAddMap_sub (g : MulAut (StdMod ι K)) (v w : ι → K) :
    toAddMap g (v - w) = toAddMap g v - toAddMap g w := by
  have h := toAddMap_add g (v - w) w
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

omit [Fintype ι] in
theorem toAddMap_invol {a : MulAut (StdMod ι K)} (ha2 : a * a = 1) (v : ι → K) :
    toAddMap a (toAddMap a v) = v := by
  rw [← toAddMap_mul, ha2, toAddMap_one]

theorem card_fix_sq [Finite K] {a : MulAut (StdMod ι K)} {σ : K ≃+* K}
    (ha : IsSemilinear a σ) (hσ : σ ≠ RingEquiv.refl K) (ha2 : a * a = 1)
    (N : Submodule K (ι → K)) (hN : ∀ v ∈ N, toAddMap a v ∈ N) :
    Nat.card {v : ι → K // v ∈ N ∧ toAddMap a v = v} ^ 2 = Nat.card N := by
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  have hcc : c - σ c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hle : Nat.card ({v : ι → K // v ∈ N ∧ toAddMap a v = v} ×
      {v : ι → K // v ∈ N ∧ toAddMap a v = v}) ≤ Nat.card N := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨p.1.1 + c • p.2.1, N.add_mem p.1.2.1 (N.smul_mem c p.2.2.1)⟩) ?_
    rintro ⟨⟨x, hxN, hxa⟩, ⟨y, hyN, hya⟩⟩ ⟨⟨x', hx'N, hx'a⟩, ⟨y', hy'N, hy'a⟩⟩ h
    have h0 : x + c • y = x' + c • y' := congrArg Subtype.val h
    have h1 : toAddMap a (x + c • y) = toAddMap a (x' + c • y') := by rw [h0]
    rw [toAddMap_add, toAddMap_add, ha, ha, hxa, hya, hx'a, hy'a] at h1
    have hy : (c - σ c) • (y - y') = 0 := by
      linear_combination (norm := module) h0 - h1
    rw [smul_eq_zero] at hy
    have hyy : y = y' := sub_eq_zero.mp (hy.resolve_left hcc)
    subst hyy
    have hxx : x = x' := add_right_cancel h0
    subst hxx
    rfl
  have hge : Nat.card N ≤ Nat.card ({v : ι → K // v ∈ N ∧ toAddMap a v = v} ×
      {v : ι → K // v ∈ N ∧ toAddMap a v = v}) := by
    have htr : ∀ w ∈ N, w + toAddMap a w ∈ N ∧
        toAddMap a (w + toAddMap a w) = w + toAddMap a w := fun w hw =>
      ⟨N.add_mem hw (hN w hw), by rw [toAddMap_add, toAddMap_invol ha2, add_comm]⟩
    refine Nat.card_le_card_of_injective
      (fun v => (⟨v.1 + toAddMap a v.1, htr v.1 v.2⟩,
        ⟨c • v.1 + toAddMap a (c • v.1), htr _ (N.smul_mem c v.2)⟩)) ?_
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    have e1 : v + toAddMap a v = w + toAddMap a w := congrArg (fun p => p.1.1) h
    have e2 : c • v + toAddMap a (c • v) = c • w + toAddMap a (c • w) :=
      congrArg (fun p => p.2.1) h
    rw [ha, ha] at e2
    have hu : (c - σ c) • (v - w) = 0 := by
      linear_combination (norm := module) e2 - σ c • e1
    rw [smul_eq_zero] at hu
    exact Subtype.ext (sub_eq_zero.mp (hu.resolve_left hcc))
  rw [Nat.card_prod, ← sq] at hle hge
  exact le_antisymm hle hge

omit [Fintype ι] in
@[expose] def fixLin (F : Subgroup (MulAut (StdMod ι K))) (hF : F ≤ linSub) :
    Submodule K (ι → K) where
  carrier := {v | ∀ y ∈ F, toAddMap y v = v}
  add_mem' := fun {v w} hv hw y hy => by
    change toAddMap y (v + w) = v + w
    rw [toAddMap_add, hv y hy, hw y hy]
  zero_mem' := fun y _ => toAddMap_zero y
  smul_mem' := fun c v hv y hy => by
    change toAddMap y (c • v) = c • v
    rw [(hF hy : IsSemilinear y (RingEquiv.refl K)) c v, hv y hy]
    rfl

omit [Fintype ι] in
theorem mem_fixLin {F : Subgroup (MulAut (StdMod ι K))} {hF : F ≤ linSub} {v : ι → K} :
    v ∈ fixLin F hF ↔ ∀ y ∈ F, toAddMap y v = v := Iff.rfl

omit [Fintype ι] in
theorem toAddMap_mem_fixLin {F : Subgroup (MulAut (StdMod ι K))} {hF : F ≤ linSub}
    {a : MulAut (StdMod ι K)} (hcomm : ∀ x ∈ F, x * a = a * x) {v : ι → K}
    (hv : v ∈ fixLin F hF) : toAddMap a v ∈ fixLin F hF := fun y hy => by
  rw [← toAddMap_mul, hcomm y hy, toAddMap_mul, hv y hy]

omit [Fintype ι] in
theorem eq_one_of_fix_sup {z : MulAut (StdMod ι K)} (hz : IsSemilinear z (RingEquiv.refl K))
    {C : Submodule K (ι → K)} (hC : ∀ v ∈ C, toAddMap z v = v) {κ : Type*} {w : κ → ι → K}
    (hw : ∀ j, toAddMap z (w j) = w j) (hsup : C ⊔ Submodule.span K (Set.range w) = ⊤) :
    z = 1 := by
  let ℓ : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := toAddMap z
      map_add' := toAddMap_add z
      map_smul' := fun c v => hz c v }
  have hle : C ⊔ Submodule.span K (Set.range w) ≤ LinearMap.ker (ℓ - LinearMap.id) := by
    refine sup_le (fun v hv => ?_) (Submodule.span_le.mpr ?_)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact hC v hv
    · rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero]
      exact hw j
  rw [hsup, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at hle
  exact toAddMap_injective fun v => congrArg (fun f : (ι → K) →ₗ[K] (ι → K) => f v) hle

theorem card_le_pow_finrank [Finite K] {a : MulAut (StdMod ι K)} {m : ℕ}
    (b : Module.Basis (Fin m) K (ι → K)) (hb : ∀ i, toAddMap a (b i) = b i)
    {F : Subgroup (MulAut (StdMod ι K))} (hF : F ≤ linSub) (hcomm : ∀ x ∈ F, x * a = a * x)
    (hq : ∀ x ∈ F, ∀ y ∈ F, ∀ v, toAddMap a v = v →
      toAddMap y (toAddMap x v - v) = toAddMap x v - v) :
    Nat.card F ≤ Nat.card {v : ι → K // v ∈ fixLin F hF ∧ toAddMap a v = v} ^
      Module.finrank K ((ι → K) ⧸ fixLin F hF) := by
  set C := fixLin F hF with hCdef
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' K (C.mkQ ∘ b)
  have hspan0 : Submodule.span K (Set.range (C.mkQ ∘ b)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  have hspan' : Submodule.span K (Set.range ((C.mkQ ∘ b) ∘ f)) = ⊤ := by rw [hspan, hspan0]
  have : Finite κ := Finite.of_injective f hf
  have : Fintype κ := Fintype.ofFinite κ
  have hκ : Nat.card κ = Module.finrank K ((ι → K) ⧸ C) := by
    rw [Nat.card_eq_fintype_card,
      Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hspan']))]
  have hsup : C ⊔ Submodule.span K (Set.range (b ∘ f)) = ⊤ := by
    rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
    exact hspan'
  have hmem : ∀ x ∈ F, ∀ j, toAddMap x (b (f j)) - b (f j) ∈ C ∧
      toAddMap a (toAddMap x (b (f j)) - b (f j)) = toAddMap x (b (f j)) - b (f j) := by
    intro x hx j
    refine ⟨fun y hy => hq x hx y hy _ (hb _), ?_⟩
    rw [toAddMap_sub, ← toAddMap_mul, ← hcomm x hx, toAddMap_mul, hb]
  let Ψ : F → (κ → {v : ι → K // v ∈ C ∧ toAddMap a v = v}) := fun x j =>
    ⟨toAddMap x (b (f j)) - b (f j), hmem x x.2 j⟩
  have hΨ : Function.Injective Ψ := by
    intro x y hxy
    have hj : ∀ j, toAddMap x (b (f j)) = toAddMap y (b (f j)) := by
      intro j
      have := congrArg (fun z => (z j : ι → K)) hxy
      simpa [Ψ] using this
    have hz : (y : MulAut (StdMod ι K))⁻¹ * x = 1 := by
      have hzF : (y : MulAut (StdMod ι K))⁻¹ * x ∈ F := F.mul_mem (F.inv_mem y.2) x.2
      refine eq_one_of_fix_sup (C := C) (hF hzF) (fun v hv => (mem_fixLin.mp hv) _ hzF)
        (w := b ∘ f) (fun j => ?_) hsup
      rw [Function.comp_apply, toAddMap_mul, hj, toAddMap_apply_inv]
    exact Subtype.ext (inv_mul_eq_one.mp hz).symm
  calc Nat.card F ≤ Nat.card (κ → {v : ι → K // v ∈ C ∧ toAddMap a v = v}) :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = _ := by rw [Nat.card_fun, hκ]

end Sp4Off

end FFC

end CFSG.Quasithin

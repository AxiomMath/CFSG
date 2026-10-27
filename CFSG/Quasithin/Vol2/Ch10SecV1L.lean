module

public import CFSG.Quasithin.Vol2.Ch10SecV1K
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10SecV1J

public noncomputable section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.ShultStronglyClosedTI.Singer

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A] {X : Subgroup (A ≃ₗ[ZMod 2] A)}

namespace SingerModel

variable (M : SingerModel X)

@[expose] def conjHom : (A ≃ₗ[ZMod 2] A) →* (M.E ≃ₗ[ZMod 2] M.E) where
  toFun g := M.Φ.trans (g.trans M.Φ.symm)
  map_one' := LinearEquiv.ext fun e => by simp
  map_mul' g h := LinearEquiv.ext fun e => by simp

theorem conjHom_apply (g : A ≃ₗ[ZMod 2] A) (e : M.E) :
    M.conjHom g e = M.Φ.symm (g (M.Φ e)) := rfl

theorem conjHom_injective : Function.Injective M.conjHom := by
  intro g h hgh
  refine LinearEquiv.ext fun a => ?_
  obtain ⟨e, rfl⟩ := M.Φ.surjective a
  have := LinearEquiv.congr_fun hgh e
  rw [conjHom_apply, conjHom_apply] at this
  exact M.Φ.symm.injective this

theorem conjHom_eq_scalarHom {x : A ≃ₗ[ZMod 2] A} {c : M.Eˣ}
    (h : ∀ e : M.E, x (M.Φ e) = M.Φ (c * e)) : M.conjHom x = scalarHom (ZMod 2) M.E c :=
  LinearEquiv.ext fun e => by rw [conjHom_apply, h, LinearEquiv.symm_apply_apply, scalarHom_apply]

end SingerModel

theorem conj_mem_gl [Finite A] [IsCyclic X] {Y : Subgroup (A ≃ₗ[ZMod 2] A)}
    (hreg : ∀ v w : A, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, x v = w) (hXY : X ≤ Y) (hodd : Odd (Nat.card Y))
    {y : A ≃ₗ[ZMod 2] A} (hy : y ∈ Y) {x : A ≃ₗ[ZMod 2] A} (hx : x ∈ X) : y * x * y⁻¹ ∈ X := by
  by_cases hA : ∃ v₀ : A, v₀ ≠ 0
  · obtain ⟨v₀, hv₀⟩ := hA
    obtain ⟨M⟩ := nonempty_singerModel hreg hv₀
    have : CharP M.E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) M.E).injective 2
    have hS : scalars (ZMod 2) M.E ≤ Y.map M.conjHom := by
      rintro _ ⟨c, rfl⟩
      obtain ⟨x', hx', hc⟩ := M.mul_mem c
      exact ⟨x', hXY hx', M.conjHom_eq_scalarHom hc⟩
    have hodd' : Odd (Nat.card (Y.map M.conjHom)) := by
      rwa [Subgroup.card_map_of_injective M.conjHom_injective]
    obtain ⟨c, hc⟩ := M.mem_mul x hx
    obtain ⟨c', hc'⟩ := normalizes_of_odd _ (ZMod 2) rfl _ hS hodd' _ ⟨y, hy, rfl⟩ c
    obtain ⟨x', hx', hx'c⟩ := M.mul_mem c'
    have e : y * x * y⁻¹ = x' := by
      apply M.conjHom_injective
      rw [M.conjHom_eq_scalarHom hx'c, map_mul, map_mul, M.conjHom_eq_scalarHom hc]
      refine LinearEquiv.ext fun z => ?_
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, scalarHom_apply, hc', scalarHom_apply,
        ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [e]
    exact hx'
  · have h1 : ∀ g : A ≃ₗ[ZMod 2] A, g = 1 := fun g => LinearEquiv.ext fun v => by
      push Not at hA
      rw [hA (g v), hA v]
      rfl
    rw [h1 (y * x * y⁻¹)]
    exact X.one_mem

end CFSG.Quasithin.Vol2.Ch10.V1C

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Quasithin Vol2.Ch10.V1C

theorem as_A_1_12_holds : ASInputs.AS_A_1_12 := by
  intro V _ _ hV X Y _ hreg hXY hodd
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h3 : Additive.toMul (2 • x) = 1 := by
      rw [toMul_nsmul]
      exact hV _
    exact toMul_eq_one.1 h3
  let χ : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
    { toFun := fun g => LinearEquiv.ofBijective
        ((MulEquiv.toAdditive g).toAddMonoidHom.toZModLinearMap 2)
        (MulEquiv.toAdditive g).bijective
      map_one' := LinearEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl }
  have hχ : ∀ g a, χ g a = Additive.ofMul (g (Additive.toMul a)) := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    intro g h hgh
    ext v
    have := LinearEquiv.congr_fun hgh (Additive.ofMul v)
    rw [hχ, hχ] at this
    simpa using this
  have : IsCyclic (X.map χ) :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective X χ hχinj).toMonoidHom
      (Subgroup.equivMapOfInjective X χ hχinj).surjective
  have hreg' : ∀ v w : Additive V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X.map χ, x v = w := by
    intro v w hv hw
    obtain ⟨x, hx, -⟩ := hreg (Additive.toMul v) (Additive.toMul w) (by simpa using hv)
      (by simpa using hw)
    exact ⟨χ x, ⟨x, x.2, rfl⟩, by rw [hχ, hx]; rfl⟩
  have hodd' : Odd (Nat.card (Y.map χ)) := by rwa [Subgroup.card_map_of_injective hχinj]
  have key : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
    intro y hy x hx
    have h := conj_mem_gl hreg' (Subgroup.map_mono hXY) hodd' ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul] at h
    obtain ⟨x', hx', he⟩ := h
    rw [← hχinj he]
    exact hx'
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun h => ?_⟩
  have := key y⁻¹ (Y.inv_mem hy) _ h
  rwa [inv_inv, show y⁻¹ * (y * x * y⁻¹) * y = x by group] at this

end CFSG.Quasithin.Vol2.Ch10

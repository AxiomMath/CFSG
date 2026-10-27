module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneEltDefs

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Open TableB Multiplicative

theorem ggTorusFrameEltSC_hypSU_three {n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusFrameEltSC p (hypSU h 3 0) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro E hE h3 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := 3) h hp hζ hbar
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζ (by norm_num) E hE h3
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg x hx
    refine ⟨ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : E.map (MulAut.conj g).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcard, card_range_hypTorusHom h hp hζ ι hι]; exact h3)
  have hback : ι.range.map (MulAut.conj g⁻¹).toMonoidHom = E := by
    rw [← heq, Subgroup.map_map]
    have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id (hypSU h 3 0) := MonoidHom.ext fun x => by
      show g⁻¹ * (g * x * g⁻¹) * g = x
      group
    rw [hcomp, Subgroup.map_id]
  let τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0 :=
    (MulAut.conj g⁻¹).toMonoidHom.comp ι
  have hτrange : τ.range = E := by
    change ((MulAut.conj g⁻¹).toMonoidHom.comp ι).range = E
    rw [MonoidHom.range_comp]
    exact hback
  have hker : ∀ t : Fin 3 → ZMod p, ι (ofAdd t) = 1 → t = 0 := by
    intro t ht
    funext i
    have hmat : diagonal (hypEntries ζ t) =
        (1 : Matrix (HypIndex 3 0) (HypIndex 3 0) K) := by
      have h1 := (hι t).symm
      rw [ht] at h1
      simpa using h1
    have hentry := congrFun (congrFun hmat (.inl i)) (.inl i)
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hentry
    have hpow : ζ ^ (t i).val = 1 := by simpa [hypEntries] using hentry
    exact (ZMod.val_eq_zero (t i)).mp
      (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).mp hpow) (ZMod.val_lt (t i)))
  have hinj : Function.Injective ι := by
    intro x y hxy
    have hz : ι (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have hzt : (x * y⁻¹).toAdd = 0 := by
      rw [← ofAdd_toAdd (x * y⁻¹)] at hz
      exact hker _ hz
    rw [toAdd_mul, toAdd_inv] at hzt
    rw [← sub_eq_add_neg] at hzt
    exact toAdd.injective (sub_eq_zero.mp hzt)
  have hτ_apply : ∀ t : Fin 3 → ZMod p, τ (ofAdd t) = g⁻¹ * ι (ofAdd t) * g := by
    intro t
    change (MulAut.conj g⁻¹) (ι (ofAdd t)) = g⁻¹ * ι (ofAdd t) * g
    rw [MulAut.conj_apply, inv_inv]
  have hι_conj : ∀ t : Fin 3 → ZMod p, ι (ofAdd t) = g * τ (ofAdd t) * g⁻¹ := by
    intro t
    rw [hτ_apply t]
    group
  have hτinj : Function.Injective τ := by
    intro x y hxy
    apply hinj
    rw [← ofAdd_toAdd x, ← ofAdd_toAdd y] at hxy
    rw [← ofAdd_toAdd x, ← ofAdd_toAdd y, hι_conj x.toAdd, hι_conj y.toAdd, hxy]
  let ηs : Fin 3 → (ZMod p)ˣ := Function.update 1 (0 : Fin 3) (-1)
  have hηs_apply : ∀ l : Fin 3, ηs l = if l = (0 : Fin 3) then -1 else 1 := by
    intro l
    change Function.update (1 : Fin 3 → (ZMod p)ˣ) (0 : Fin 3) (-1) l =
      if l = (0 : Fin 3) then -1 else 1
    rw [Function.update_apply]
    simp
  have hηs : ∀ l, ηs l ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
    intro l
    rw [hηs_apply l]
    by_cases hl : l = 0
    · rw [if_pos hl]
      exact Subgroup.mem_zpowers (-1)
    · rw [if_neg hl]
      exact Subgroup.one_mem _
  have hsign : ∃ w : hypSU h 3 0, ∀ t : Fin 3 → ZMod p,
      w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (Function.update t 0 (-t 0))) := by
    obtain ⟨w, -, hw⟩ := exists_hypTorus_move h hp hp2 hζ hbar ι hι
      (Equiv.refl (Fin 3)) ηs hηs
    refine ⟨g⁻¹ * w * g, fun t => ?_⟩
    have hfun : (fun l : Fin 3 =>
        ((ηs l : (ZMod p)ˣ) : ZMod p) * t ((Equiv.refl (Fin 3)) l)) =
        Function.update t 0 (-t 0) := by
      funext l
      change ((ηs l : (ZMod p)ˣ) : ZMod p) * t ((Equiv.refl (Fin 3)) l) =
        Function.update t (0 : Fin 3) (-t 0) l
      rw [Function.update_apply, hηs_apply l]
      by_cases hl : l = 0
      · simp [hl]
      · simp [hl]
    calc (g⁻¹ * w * g)⁻¹ * τ (ofAdd t) * (g⁻¹ * w * g)
        = g⁻¹ * (w⁻¹ * ι (ofAdd t) * w) * g := by
          rw [hτ_apply t]
          group
      _ = g⁻¹ * ι (ofAdd fun l =>
            ((ηs l : (ZMod p)ˣ) : ZMod p) * t ((Equiv.refl (Fin 3)) l)) * g := by
          rw [hw t]
      _ = g⁻¹ * ι (ofAdd (Function.update t 0 (-t 0))) * g := by rw [hfun]
      _ = τ (ofAdd (Function.update t 0 (-t 0))) := (hτ_apply _).symm
  let ηt : Fin 3 → (ZMod p)ˣ := fun _ => 1
  have hηt : ∀ l, ηt l ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
    intro l
    change (1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ)
    exact Subgroup.one_mem _
  have htrans : ∃ w : hypSU h 3 0, ∀ t : Fin 3 → ZMod p,
      w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (t ∘ Equiv.swap (0 : Fin 3) 1)) := by
    obtain ⟨w, -, hw⟩ := exists_hypTorus_move h hp hp2 hζ hbar ι hι
      (Equiv.swap (0 : Fin 3) 1) ηt hηt
    refine ⟨g⁻¹ * w * g, fun t => ?_⟩
    have hfun : (fun l : Fin 3 => ((ηt l : (ZMod p)ˣ) : ZMod p) *
        t ((Equiv.swap (0 : Fin 3) 1) l)) = t ∘ Equiv.swap (0 : Fin 3) 1 := by
      funext l
      change ((ηt l : (ZMod p)ˣ) : ZMod p) * t ((Equiv.swap (0 : Fin 3) 1) l) =
        t ((Equiv.swap (0 : Fin 3) 1) l)
      simp [ηt]
    calc (g⁻¹ * w * g)⁻¹ * τ (ofAdd t) * (g⁻¹ * w * g)
        = g⁻¹ * (w⁻¹ * ι (ofAdd t) * w) * g := by
          rw [hτ_apply t]
          group
      _ = g⁻¹ * ι (ofAdd fun l =>
            ((ηt l : (ZMod p)ˣ) : ZMod p) * t ((Equiv.swap (0 : Fin 3) 1) l)) * g := by
          rw [hw t]
      _ = g⁻¹ * ι (ofAdd (t ∘ Equiv.swap (0 : Fin 3) 1)) * g := by rw [hfun]
      _ = τ (ofAdd (t ∘ Equiv.swap (0 : Fin 3) 1)) := (hτ_apply _).symm
  exact ⟨3, τ, hτinj, hτrange, 0, 1, by decide, hsign, htrans⟩

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitC1

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Multiplicative Matrix

theorem ggKGUs_signed_frame_hypSU {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1)
    (hr : 0 < r) (E : Subgroup (hypSU h r 0)) (hE : IsElemAbelian p E)
    (hcard : p ^ r ≤ Nat.card E) :
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* hypSU h r 0), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i : Fin k, ∃ w : hypSU h r 0, ∀ f, w * τ f * w⁻¹ = τ (SpCoord.sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : hypSU h r 0, ∀ f,
        w * τ f * w⁻¹ = τ (SpCoord.permAut σ f)) ∧
      ∀ g : hypSU h r 0, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := r) h hp hζ hbar
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hker : ∀ t : Fin r → ZMod p, ι (ofAdd t) = 1 → t = 0 := by
      intro t ht
      funext i
      have hmat : diagonal (hypEntries ζ t) = (1 : Matrix (HypIndex r 0) (HypIndex r 0) K) := by
        have h1 := (hι t).symm
        rw [ht] at h1
        simpa using h1
      have hentry := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hentry
      have hpow : ζ ^ (t i).val = 1 := by simpa [hypEntries] using hentry
      exact (ZMod.val_eq_zero (t i)).mp
        (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd _).mp hpow) (ZMod.val_lt (t i)))
    have hzt : Multiplicative.toAdd f = 0 := by
      rw [← ofAdd_toAdd f] at hf
      exact hker (Multiplicative.toAdd f) hf
    exact Multiplicative.toAdd.injective (by rw [hzt]; simp)
  obtain ⟨g₀, hg₀⟩ := exists_conj_hypEntries h hp hp2 hpq hζ hr E hE hcard
  have hle : E.map (MulAut.conj g₀).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg₀ x hx
    refine ⟨ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have hcardmap : Nat.card (E.map (MulAut.conj g₀).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g₀).injective
  have heq : E.map (MulAut.conj g₀).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [hcardmap, card_range_hypTorusHom h hp hζ ι hι]
      exact hcard)
  have hback : ι.range.map (MulAut.conj g₀⁻¹).toMonoidHom = E := by
    rw [← heq, Subgroup.map_map]
    have hcomp : (MulAut.conj g₀⁻¹).toMonoidHom.comp (MulAut.conj g₀).toMonoidHom =
        MonoidHom.id (hypSU h r 0) := MonoidHom.ext fun x => by
      show g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ = x
      group
    rw [hcomp, Subgroup.map_id]
  let e : (Fin r → Multiplicative (ZMod p)) ≃* Multiplicative (Fin r → ZMod p) :=
    MulEquiv.funMultiplicative (Fin r) (ZMod p)
  let ι' : (Fin r → Multiplicative (ZMod p)) →* hypSU h r 0 := ι.comp e.toMonoidHom
  have hι'of : ∀ f : Fin r → Multiplicative (ZMod p),
      ι' f = ι (ofAdd (fun l => toAdd (f l))) := fun f => by
    change ι (e f) = ι (ofAdd (fun l => toAdd (f l)))
    rfl
  have hι' : ∀ f, (((ι' f : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) =
      diagonal (hypEntries ζ (fun i => toAdd (f i))) := by
    intro f
    rw [hι'of f, hι]
  have hι'range : ι'.range = ι.range := by
    change (ι.comp e.toMonoidHom).range = ι.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top]
  have hι'inj : Function.Injective ι' := hιinj.comp e.injective
  let τ : (Fin r → Multiplicative (ZMod p)) →* hypSU h r 0 :=
    (MulAut.conj g₀⁻¹).toMonoidHom.comp ι'
  have hτapp : ∀ f, τ f = g₀⁻¹ * ι' f * g₀ := by
    intro f
    change (MulAut.conj g₀⁻¹) (ι' f) = g₀⁻¹ * ι' f * g₀
    rw [MulAut.conj_apply, inv_inv]
  have hτrange : τ.range = E := by
    change ((MulAut.conj g₀⁻¹).toMonoidHom.comp ι').range = E
    rw [MonoidHom.range_comp, hι'range, hback]
  have hτinj : Function.Injective τ := (MulAut.conj g₀⁻¹).injective.comp hι'inj
  refine ⟨r, τ, hτinj, hτrange, fun i => ?_, fun σ => ?_, fun g hgE => ?_⟩
  · have hηs : ∀ l, Function.update (1 : Fin r → (ZMod p)ˣ) i (-1) l ∈
        Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
      intro l
      by_cases hl : l = i
      · rw [hl, Function.update_apply, if_pos rfl]
        exact Subgroup.mem_zpowers (-1)
      · rw [Function.update_apply, if_neg hl]
        exact Subgroup.one_mem _
    obtain ⟨u, -, hu⟩ :=
      exists_hypTorus_move h hp hp2 hζ hbar ι hι (Equiv.refl (Fin r))
        (Function.update 1 i (-1)) hηs
    refine ⟨g₀⁻¹ * u⁻¹ * g₀, fun f => ?_⟩
    have hfun : (fun l : Fin r => ((Function.update 1 i (-1) : Fin r → (ZMod p)ˣ) l : ZMod p) *
        toAdd (f l)) = fun l => toAdd (SpCoord.sgnAut i f l) := by
      funext l
      rw [SpCoord.sgnAut_apply]
      by_cases hl : l = i
      · subst hl
        simp [Function.update_apply]
      · simp [Function.update_apply, hl]
    have hu' : u⁻¹ * ι' f * u = ι' (SpCoord.sgnAut i f) := by
      have h1 := hu (fun l => toAdd (f l))
      simp only [Equiv.refl_apply] at h1
      rw [hfun] at h1
      rw [hι'of f, hι'of (SpCoord.sgnAut i f)]
      exact h1
    calc (g₀⁻¹ * u⁻¹ * g₀) * τ f * (g₀⁻¹ * u⁻¹ * g₀)⁻¹
        = g₀⁻¹ * (u⁻¹ * ι' f * u) * g₀ := by rw [hτapp f]; group
      _ = g₀⁻¹ * ι' (SpCoord.sgnAut i f) * g₀ := by rw [hu']
      _ = τ (SpCoord.sgnAut i f) := (hτapp _).symm
  · obtain ⟨u, -, hu⟩ :=
      exists_hypTorus_move h hp hp2 hζ hbar ι hι σ⁻¹ (fun _ => 1) (fun i => Subgroup.one_mem _)
    refine ⟨g₀⁻¹ * u⁻¹ * g₀, fun f => ?_⟩
    have hfun : (fun l : Fin r => ((1 : (ZMod p)ˣ) : ZMod p) * toAdd (f (σ⁻¹ l))) =
        fun l => toAdd (SpCoord.permAut σ f l) := by
      funext l
      rw [SpCoord.permAut_apply]
      simp
    have hu' : u⁻¹ * ι' f * u = ι' (SpCoord.permAut σ f) := by
      have h1 := hu (fun l => toAdd (f l))
      rw [hfun] at h1
      rw [hι'of f, hι'of (SpCoord.permAut σ f)]
      exact h1
    calc (g₀⁻¹ * u⁻¹ * g₀) * τ f * (g₀⁻¹ * u⁻¹ * g₀)⁻¹
        = g₀⁻¹ * (u⁻¹ * ι' f * u) * g₀ := by rw [hτapp f]; group
      _ = g₀⁻¹ * ι' (SpCoord.permAut σ f) * g₀ := by rw [hu']
      _ = τ (SpCoord.permAut σ f) := (hτapp _).symm
  · have hgT : ∀ f, ∃ f', (g₀ * g * g₀⁻¹) * ι' f * (g₀ * g * g₀⁻¹)⁻¹ = ι' f' := by
      intro f
      have h1 : g * τ f * g⁻¹ ∈ E := hgE (τ f) (hτrange ▸ ⟨f, rfl⟩)
      have h2 : g₀ * (g * τ f * g⁻¹) * g₀⁻¹ ∈ ι.range := by
        rw [← heq]
        exact Subgroup.mem_map.mpr ⟨g * τ f * g⁻¹, h1, rfl⟩
      obtain ⟨f', hf'⟩ := h2
      refine ⟨f', ?_⟩
      calc (g₀ * g * g₀⁻¹) * ι' f * (g₀ * g * g₀⁻¹)⁻¹
          = g₀ * (g * τ f * g⁻¹) * g₀⁻¹ := by rw [hτapp f]; group
        _ = ι f' := hf'.symm
        _ = ι' f' := (hι'of f').symm
    obtain ⟨π, ε, hε, hrel⟩ := ggKGUc_normalizer h hp ζ hζ ι' hι' (g₀ * g * g₀⁻¹) hgT
    refine ⟨π, ε, hε, fun f f' hff' => ?_⟩
    have h1 : (g₀ * g * g₀⁻¹) * ι' f * (g₀ * g * g₀⁻¹)⁻¹ = ι' f' := by
      calc (g₀ * g * g₀⁻¹) * ι' f * (g₀ * g * g₀⁻¹)⁻¹
          = g₀ * (g * τ f * g⁻¹) * g₀⁻¹ := by rw [hτapp f]; group
        _ = g₀ * τ f' * g₀⁻¹ := by rw [hff']
        _ = ι' f' := by rw [hτapp]; group
    exact hrel f f' h1

end CFSG.StandardType

end

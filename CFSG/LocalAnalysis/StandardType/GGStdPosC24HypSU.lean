module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial SpCoord
  Multiplicative

theorem ggTorusSignedEltSC_hypSU_three {n p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusSignedEltSC p (hypSU h 3 0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro E hE h3 _
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_two_pow_sub_one h hp hpq
  have hbar : h.bar ζ = ζ := bar_eq_self_of_pow_eq_one h hpq hζ.pow_eq_one
  obtain ⟨ι, hι⟩ := exists_hypTorusHom (r := 3) h hp hζ hbar
  obtain ⟨g, hg⟩ := exists_conj_hypEntries h hp hp2 hpq hζ (by norm_num) E hE h3
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
  have hinj : Function.Injective ι :=
    (injective_iff_map_eq_one ι).mpr fun x hx => toAdd_eq_zero.mp (hker x.toAdd hx)
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hg x hx
    refine ⟨ofAdd t, Subtype.ext (Units.ext ?_)⟩
    rw [hι t]
    exact ht.symm
  have heq : E.map (MulAut.conj g).toMonoidHom = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        card_range_hypTorusHom h hp hζ ι hι]
      exact h3)
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ ι.range := by
    intro x
    rw [← heq]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rwa [← (MulAut.conj g).injective hyx]
  let τ : (Fin 3 → Multiplicative (ZMod p)) →* hypSU h 3 0 :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp ι).comp
      (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod p).symm.toMonoidHom
  have hτ : ∀ f, τ f = g⁻¹ * ι (ofAdd fun i => toAdd (f i)) * g := fun f => by
    change (MulAut.conj g⁻¹) (ι (ofAdd fun i => toAdd (f i))) = _
    rw [MulAut.conj_apply, inv_inv]
  have hτinj : Function.Injective τ :=
    ((MulAut.conj g⁻¹).injective.comp hinj).comp
      (MulEquiv.piMultiplicative fun _ : Fin 3 => ZMod p).symm.injective
  have hτrange : τ.range = E := by
    ext x
    rw [hmemE]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨ofAdd fun i => toAdd (f i), by rw [hτ]; group⟩
    · rintro ⟨u, hu⟩
      refine ⟨fun i => ofAdd (toAdd u i), ?_⟩
      rw [hτ]
      change g⁻¹ * ι u * g = x
      rw [hu]
      group
  have hmove : ∀ (π : Equiv.Perm (Fin 3)) (η : Fin 3 → (ZMod p)ˣ),
      (∀ l, η l ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ)) →
      ∀ F : (Fin 3 → Multiplicative (ZMod p)) → Fin 3 → Multiplicative (ZMod p),
      (∀ f l, toAdd (F f l) = (η l : ZMod p) * toAdd (f (π l))) →
      ∃ w : hypSU h 3 0, ∀ f, w * τ f * w⁻¹ = τ (F f) := by
    intro π η hη F hF
    obtain ⟨w, -, hw⟩ := exists_hypTorus_move h hp hp2 hζ hbar ι hι π η hη
    refine ⟨g⁻¹ * w⁻¹ * g, fun f => ?_⟩
    have hFf : (fun l => toAdd (F f l)) = fun l => (η l : ZMod p) * toAdd (f (π l)) :=
      funext (hF f)
    rw [hτ, hτ, hFf, ← hw fun l => toAdd (f l)]
    group
  have hpm : ∀ i l : Fin 3, Function.update (1 : Fin 3 → (ZMod p)ˣ) i (-1) l ∈
      Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
    intro i l
    by_cases hl : l = i
    · rw [hl, Function.update_self]
      exact Subgroup.mem_zpowers _
    · rw [Function.update_of_ne hl]
      exact Subgroup.one_mem _
  have hsigned : ∀ y : hypSU h 3 0, (∀ t, ∃ t', y * ι (ofAdd t) * y⁻¹ = ι (ofAdd t')) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ t t', y * ι (ofAdd t) * y⁻¹ = ι (ofAdd t') → ∀ i, t' (π i) = ε i * t i := by
    intro y hy
    obtain ⟨Y, hY⟩ : ∃ Y : Matrix (HypIndex 3 0) (HypIndex 3 0) K,
        ((y : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) = Y := ⟨_, rfl⟩
    have hent : ∀ t t', y * ι (ofAdd t) * y⁻¹ = ι (ofAdd t') → ∀ a b, Y a b ≠ 0 →
        hypEntries ζ t b = hypEntries ζ t' a := by
      intro t t' htt a b hab
      have h1 : y * ι (ofAdd t) = ι (ofAdd t') * y := by
        rw [← htt]
        group
      have h2 := congrArg (fun z : hypSU h 3 0 =>
        ((z : GL (HypIndex 3 0) K) : Matrix (HypIndex 3 0) (HypIndex 3 0) K) a b) h1
      simp only [Subgroup.coe_mul, Units.val_mul, hι, hY, mul_diagonal, diagonal_mul] at h2
      exact mul_left_cancel₀ hab (h2.trans (mul_comm _ _))
    have hrow : ∀ a, ∃ b, Y a b ≠ 0 := by
      intro a
      by_contra! h0
      have h1 := congrFun (congrFun (Units.mul_inv (y : GL (HypIndex 3 0) K)) a) a
      rw [hY, mul_apply, one_apply_eq,
        Finset.sum_eq_zero fun b _ => by rw [h0 b, zero_mul]] at h1
      exact zero_ne_one h1
    have hcoord : ∀ j : Fin 3, ∃ (i : Fin 3) (s : ZMod p), (s = 1 ∨ s = -1) ∧
        ∀ t t', y * ι (ofAdd t) * y⁻¹ = ι (ofAdd t') → t' j = s * t i := by
      intro j
      obtain ⟨b, hb⟩ := hrow (.inl j)
      rcases b with i | k | i
      · refine ⟨i, 1, Or.inl rfl, fun t t' htt => ?_⟩
        have h1 : ζ ^ (t i).val = ζ ^ (t' j).val := hent t t' htt _ _ hb
        rw [one_mul]
        exact (ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1)).symm
      · exact k.elim0
      · refine ⟨i, -1, Or.inr rfl, fun t t' htt => ?_⟩
        have h1 : (ζ ^ (t i).val)⁻¹ = ζ ^ (t' j).val := hent t t' htt _ _ hb
        have h2 : ζ ^ ((t' j).val + (t i).val) = 1 := by
          rw [pow_add, ← h1, inv_mul_cancel₀ (pow_ne_zero _ (hζ.ne_zero hp.ne_zero))]
        have h3 := (ZMod.natCast_eq_zero_iff _ p).mpr ((hζ.pow_eq_one_iff_dvd _).mp h2)
        simp only [Nat.cast_add, ZMod.natCast_zmod_val] at h3
        exact (eq_neg_of_add_eq_zero_left h3).trans (neg_one_mul _).symm
    choose ρ s hs hρ using hcoord
    have hsurj : Function.Surjective ρ := by
      intro i
      by_contra! hne
      obtain ⟨t', ht'⟩ := hy (Pi.single i 1)
      have h0 : t' = 0 := funext fun j => by
        rw [hρ j _ _ ht', Pi.single_eq_of_ne (hne j), mul_zero, Pi.zero_apply]
      rw [h0, ofAdd_zero, map_one] at ht'
      have h1 : ι (ofAdd (Pi.single i 1)) = 1 := by
        calc ι (ofAdd (Pi.single i 1))
            = y⁻¹ * (y * ι (ofAdd (Pi.single i 1)) * y⁻¹) * y := by group
          _ = 1 := by rw [ht']; group
      have h2 := congrFun (hker _ h1) i
      rw [Pi.single_eq_same, Pi.zero_apply] at h2
      exact one_ne_zero h2
    have hbij : Function.Bijective ρ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
    refine ⟨(Equiv.ofBijective ρ hbij).symm, fun i => s ((Equiv.ofBijective ρ hbij).symm i),
      fun i => hs _, fun t t' htt i => ?_⟩
    have h1 := hρ ((Equiv.ofBijective ρ hbij).symm i) t t' htt
    rwa [Equiv.ofBijective_apply_symm_apply ρ hbij i] at h1
  refine ⟨3, τ, hτinj, hτrange, fun i => hmove (Equiv.refl _) _ (hpm i) (sgnAut i) fun f l => ?_,
    fun σ => hmove σ⁻¹ 1 (fun _ => Subgroup.one_mem _) (permAut σ) fun f l => ?_,
    fun x hx => ?_⟩
  · by_cases hl : l = i
    · subst hl
      simp [sgnAut_apply]
    · simp [sgnAut_apply, Function.update_of_ne hl]
  · simp [permAut_apply]
  · have hy : ∀ t, ∃ t', g * x * g⁻¹ * ι (ofAdd t) * (g * x * g⁻¹)⁻¹ = ι (ofAdd t') := by
      intro t
      obtain ⟨u, hu⟩ := (hmemE _).mp
        (hx _ ((hmemE (g⁻¹ * ι (ofAdd t) * g)).mpr ⟨ofAdd t, by group⟩))
      exact ⟨toAdd u, by rw [ofAdd_toAdd, hu]; group⟩
    obtain ⟨π, ε, hε, hrel⟩ := hsigned _ hy
    refine ⟨π, ε, hε, fun f f' hff i =>
      hrel (fun l => toAdd (f l)) (fun l => toAdd (f' l)) ?_ i⟩
    calc g * x * g⁻¹ * ι (ofAdd fun l => toAdd (f l)) * (g * x * g⁻¹)⁻¹
        = g * (x * τ f * x⁻¹) * g⁻¹ := by rw [hτ]; group
      _ = ι (ofAdd fun l => toAdd (f' l)) := by rw [hff, hτ]; group

end CFSG.StandardType

end

module

public import CFSG.Quasithin.Background.SmithB45ExcEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4Wrap

public section

namespace CFSG.Quasithin.B45Exc

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.ComponentClassification.OuterAutomorphisms

variable {W : Type} [CommGroup W] [Finite W]

theorem weight2_lt_of_outer_odd_cover (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {r ρ : ℕ} (hρ : 2 * r < ρ)
    (hOut : Odd (Nat.card (Outer S)))
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hRank : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hMoved : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : S →* MulAut W, Function.Injective σ → ∀ t : S, t ≠ 1 → t * t = 1 →
        2 ^ ρ ≤ (fixV (Subgroup.zpowers (σ t))).index) :
    Nat.card E ^ 2 * Nat.card (fixV E) < Nat.card W := by
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hker1 : (redHom L e).ker = ⊥ :=
    hCover ↥L (redHom L e) (redHom_surjective L e) (by rw [hker]) (by rw [hker]; exact hZodd)
  have hinj : Function.Injective (redHom L e) := (MonoidHom.ker_eq_bot_iff _).1 hker1
  let eqv : ↥L ≃* S := MulEquiv.ofBijective (redHom L e) ⟨hinj, redHom_surjective L e⟩
  let σ : S →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσinj : Function.Injective σ := by
    intro x y hxy
    exact eqv.symm.injective (Subtype.ext hxy)
  have hσ : ∀ l : ↥L, σ (redHom L e l) = (l : MulAut W) := by
    intro l
    show ((eqv.symm (redHom L e l) : ↥L) : MulAut W) = l
    have : eqv.symm (redHom L e l) = l := eqv.symm_apply_apply l
    rw [this]
  have hEL : E ≤ L :=
    le_of_autInner_invol hW hperf hirr hE hEel e (autInner_of_outer_odd hOut)
  have hcard : Nat.card E ≤ 2 ^ r := card_le_two_pow_of_le hW hirr hEL hEel e hRank
  refine weight2_lt_of_rank hEne hρ hcard fun b hbE hb1 => ?_
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  let l : ↥L := ⟨b, hEL hbE⟩
  have hl1 : l ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hl2 : l * l = 1 := Subtype.ext hb2
  have hrank := hMoved W hW σ hσinj (redHom L e l) (fun h => hl1 (hinj (by rw [h, map_one])))
    (by rw [← map_mul, hl2, map_one])
  rwa [hσ] at hrank

omit [Finite W] in
theorem moved_of_mulEquiv_pow {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {ρ : ℕ}
    (hY : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : Y →* MulAut W, Function.Injective σ → ∀ t : Y, t ≠ 1 → t * t = 1 →
        2 ^ ρ ≤ (fixV (Subgroup.zpowers (σ t))).index)
    (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (σ : X →* MulAut W)
    (hσ : Function.Injective σ) (t : X) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    2 ^ ρ ≤ (fixV (Subgroup.zpowers (σ t))).index := by
  have hinj : Function.Injective (σ.comp e.symm.toMonoidHom) := by
    intro x y hxy
    exact e.symm.injective (hσ hxy)
  have h := hY W hW (σ.comp e.symm.toMonoidHom) hinj (e t)
    (fun h => ht1 (e.injective (by rw [h, map_one])))
    (by rw [← map_mul, ht2, map_one])
  simpa using h

end CFSG.Quasithin.B45Exc

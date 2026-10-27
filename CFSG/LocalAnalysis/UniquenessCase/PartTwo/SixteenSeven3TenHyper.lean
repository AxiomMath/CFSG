module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG

theorem s16c167_commSub_stable {W : Type} [CommGroup W] {C : Subgroup W}
    {X : Subgroup (MulAut W)} {g : MulAut W} (hgC : ∀ c ∈ C, g c ∈ C)
    (hgX : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {u : W} (hu : u ∈ commSub C X) : g u ∈ commSub C X := by
  have hle : (commSub C X).map g.toMonoidHom ≤ commSub C X := by
    unfold commSub
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨c, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨g * x * g⁻¹, hgX x hx, g w, hgC w hw, ?_⟩
    simp [MulAut.mul_apply, MulAut.inv_apply]
  exact hle ⟨u, hu, rfl⟩

theorem s16c167_mem_stabSub_of_forward {W : Type} [CommGroup W] {U : Subgroup W} {g : MulAut W}
    (h : ∀ u ∈ U, g u ∈ U) (h' : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  have := h' _ hu
  rwa [MulAut.inv_apply_self] at this

theorem s16c167b_hyperplane_fixed_moved {W : Type} [CommGroup W] [Finite W]
    (hsq : ∀ w : W, w * w = 1) {T : Subgroup (MulAut W)} (hT7 : ∀ t ∈ T, t ^ 7 = 1)
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hT1 : T ≠ ⊥) {E : Subgroup W}
    (hTE : ∀ t ∈ T, ∀ e ∈ E, t e ∈ E) (hfaith : ∀ t ∈ T, (∀ e ∈ E, t e = e) → t = 1) :
    ∃ B : Subgroup (MulAut W), B ≤ T ∧ Nat.card B * 7 = Nat.card T ∧
      ∃ e ∈ E, (∀ b ∈ B, b e = e) ∧ ∃ t ∈ T, t e ≠ e := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsElementaryAbelian 7 ↥T :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hTc _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a =>
        Subtype.ext (hT7 _ a.2) }
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  haveI : CFSG.IsInvariant ↥T W E :=
    SolvableHall.isInvariant_of_forall_smul_mem (fun a x hx => hTE _ a.2 x hx)
  have hsq' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hsq w
  have hp : ¬ 7 ∣ Nat.card ↥E := by
    intro h
    rw [card_eq_two_pow hsq' E] at h
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h : 7 ∣ 2)
    omega
  have hgen := SolvableHall.abelian_hyperplane_generation (p := 7) (A := ↥T) (H := ↥E) hp
  by_contra hcon
  have hall : ∀ B : Subgroup ↥T, B.index = 7 → ∀ e : ↥E, (∀ b : ↥B, (b : ↥T) • e = e) →
      ∀ a : ↥T, a • e = e := by
    intro B hB e he a
    by_contra hae
    apply hcon
    refine ⟨B.map T.subtype, Subgroup.map_subtype_le B, ?_, (e : W), e.2, ?_,
      (a : MulAut W), a.2, fun h => hae (Subtype.ext h)⟩
    · rw [Subgroup.card_map_of_injective T.subtype_injective]
      have := B.card_mul_index
      rwa [hB] at this
    · rintro _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (he ⟨b, hb⟩)
  have hle : (⨆ (B : Subgroup ↥T) (_ : B.index = 7), fixedPointSubgroup ↥B ↥E) ≤
      fixedPointSubgroup ↥T ↥E := by
    refine iSup₂_le fun B hB e he => ?_
    exact fun a => hall B hB e he a
  rw [hgen] at hle
  apply hT1
  rw [eq_bot_iff]
  intro t ht
  refine Subgroup.mem_bot.2 (hfaith t ht fun e he => ?_)
  exact congrArg Subtype.val (hle (Subgroup.mem_top (⟨e, he⟩ : ↥E)) ⟨t, ht⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

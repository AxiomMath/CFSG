module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Abstract

variable {V : Type} [CommGroup V] [Finite V]

theorem s16h_e3_rank_le_of_inf_map_le (hV : ∀ v : V, v ^ 2 = 1) (Wt Z : Subgroup V)
    (τ : MulAut V) (hτ2 : τ ^ 2 = 1)
    (hker : Wt ⊓ Wt.map τ.toMonoidHom ≤ Z) :
    rk ↥Wt ≤ rk ↥Z + rk ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers τ)) := by
  have hττ : τ * τ = 1 := by simpa [pow_two] using hτ2
  let φ : ↥Wt →* V :=
    { toFun := fun w => τ (w : V) * (w : V)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        show τ ((a : V) * (b : V)) * ((a : V) * (b : V))⁻¹ =
          τ (a : V) * (a : V)⁻¹ * (τ (b : V) * (b : V)⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hrange : φ.range ≤ commSub (⊤ : Subgroup V) (Subgroup.zpowers τ) := by
    rintro _ ⟨w, rfl⟩
    exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, (w : V), Subgroup.mem_top _, rfl⟩
  have hker_le : Nat.card φ.ker ≤ Nat.card ↥Z := by
    have hmem : ∀ x : φ.ker, ((x : ↥Wt) : V) ∈ Z := by
      intro x
      have hxker : φ (x : ↥Wt) = 1 := MonoidHom.mem_ker.mp x.2
      have hτx : τ ((x : ↥Wt) : V) = ((x : ↥Wt) : V) := by
        simpa using (mul_inv_eq_one.mp hxker)
      have hxmap : ((x : ↥Wt) : V) ∈ Wt.map τ.toMonoidHom :=
        Subgroup.mem_map.2 ⟨(x : ↥Wt), (x : ↥Wt).2, hτx⟩
      exact hker (Subgroup.mem_inf.mpr ⟨(x : ↥Wt).2, hxmap⟩)
    refine Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : ↥Wt) : V), hmem x⟩ : ↥Z)) ?_
    intro x y h
    have h2 : ((x : ↥Wt) : V) = ((y : ↥Wt) : V) := congrArg (fun z : ↥Z => (z : V)) h
    exact Subtype.ext (Subtype.ext h2)
  have hrange_le : Nat.card φ.range ≤
      Nat.card ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers τ)) :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)
  have hdecomp : Nat.card ↥Wt = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hbound : Nat.card ↥Wt ≤
      Nat.card ↥Z * Nat.card ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers τ)) :=
    calc Nat.card ↥Wt = Nat.card φ.range * Nat.card φ.ker := hdecomp
      _ ≤ Nat.card ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers τ)) * Nat.card ↥Z :=
        Nat.mul_le_mul hrange_le hker_le
      _ = Nat.card ↥Z * Nat.card ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers τ)) :=
        mul_comm _ _
  have hcW := card_eq_two_pow hV Wt
  have hcZ := card_eq_two_pow hV Z
  have hcC := card_eq_two_pow hV (commSub (⊤ : Subgroup V) (Subgroup.zpowers τ))
  rw [hcW, hcZ, hcC, ← pow_add] at hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hbound

theorem s16h_e3_two_inf_map_le_fixV {W : Type} [CommGroup W]
    (A L : Subgroup (MulAut W)) (t : MulAut W) (τ : MulAut W)
    (hW : Conc4_136W A t L) (hτ : τ ∈ A) (hτ2 : τ ^ 2 = 1)
    (hτn : τ ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    commSub (⊤ : Subgroup W) L ⊓ (commSub (⊤ : Subgroup W) L).map τ.toMonoidHom ≤ fixV L := by
  have hττ : τ * τ = 1 := by simpa [pow_two] using hτ2
  have hbot : commSub (commSub (⊤ : Subgroup W) L)
      (L.map (MulAut.conj τ).toMonoidHom) = ⊥ := (hW.2.1 τ hτ hτn).2
  have hfix : commSub (⊤ : Subgroup W) L ≤ fixV (L.map (MulAut.conj τ).toMonoidHom) :=
    commSub_eq_bot_iff.1 hbot
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu.2
  rw [mem_fixV]
  intro l hl
  change l (τ w) = τ w
  have hconj : τ * l * τ ∈ L.map (MulAut.conj τ).toMonoidHom := by
    have h1 : (MulAut.conj τ) l = τ * l * τ := by
      rw [MulAut.conj_apply]
      simp [inv_eq_of_mul_eq_one_right hττ]
    rw [← h1]
    exact Subgroup.mem_map_of_mem (MulAut.conj τ).toMonoidHom hl
  have hfixw : (τ * l * τ) w = w := (mem_fixV.mp (hfix hw)) _ hconj
  have hcalc : l (τ w) = τ ((τ * l * τ) w) := by
    have h2 : τ (τ (l (τ w))) = l (τ w) := by
      rw [← MulAut.mul_apply, hττ, MulAut.one_apply]
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact h2.symm
  rw [hcalc, hfixw]

end Abstract

section Setting

theorem s16h_e3_l3_two_outside_swap_rank
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    {τ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτ : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hτ2 : τ ^ 2 = 1)
    (hτn : τ ∉ Subgroup.normalizer (lBar ⊥ V h.hyp151.isElemAbelian L :
      Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) :
    rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
        (lBar ⊥ V h.hyp151.isElemAbelian L)) ≤
      rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
          (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) +
      rk ↥(commSub (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian))
        (Subgroup.zpowers τ)) := by
  have hV := h.hyp151.isElemAbelian
  have hfix := s16h_e3_two_inf_map_le_fixV (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t τ hW hτ hτ2
    (by simpa using hτn)
  exact s16h_e3_rank_le_of_inf_map_le (s15_Infra_vtil_sq_eq_one ⊥ V hV)
    (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L))
    (commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L))
    τ hτ2 (le_inf inf_le_left hfix)

end Setting

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

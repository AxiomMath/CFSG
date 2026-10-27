module

public import CFSG.Quasithin.Background.HSL3S77Bridge
public import CFSG.Quasithin.Background.HSL3S77Fix

public section

namespace CFSG.Quasithin.H.S77

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H.SL3Pair
  CFSG.Quasithin.H.SL3One

theorem congrHom_eq_conj (f y : MulAut (PairMod (ZMod 2))) : congrHom f y = f * y * f⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem map_congrHom_eq {f : MulAut (PairMod (ZMod 2))} (hf : f ∈ pairNorm (ZMod 2))
    {X : Subgroup (MulAut (PairMod (ZMod 2)))}
    (hX : X = pairSL (ZMod 2) ∨ X = pairNorm (ZMod 2)) : X.map (congrHom f) = X := by
  have h : X.map (MulAut.conj f).toMonoidHom = X := by
    rcases hX with rfl | rfl
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hf
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hf)
  have hc : (congrHom f : MulAut (PairMod (ZMod 2)) →* MulAut (PairMod (ZMod 2))) =
      (MulAut.conj f).toMonoidHom := MonoidHom.ext fun y => congrHom_eq_conj f y
  rw [hc]
  exact h

theorem model_trans {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {e : V ≃* PairMod (ZMod 2)} (he : H.map (congrHom e) = pairSL (ZMod 2))
    (hN : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) = pairNorm (ZMod 2))
    {f : MulAut (PairMod (ZMod 2))} (hf : f ∈ pairNorm (ZMod 2)) :
    H.map (congrHom (e.trans f)) = pairSL (ZMod 2) ∧
      (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom (e.trans f)) =
        pairNorm (ZMod 2) := by
  have hc : ∀ X : Subgroup (MulAut V), X.map (congrHom (e.trans f)) =
      (X.map (congrHom e)).map (congrHom f) := fun X => by
    rw [Subgroup.map_map]
    rfl
  rw [hc, hc, he, hN]
  exact ⟨map_congrHom_eq hf (Or.inl rfl), map_congrHom_eq hf (Or.inr rfl)⟩

theorem map_rho_V₁ (h : SL32) : (V₁ (ZMod 2)).map (rho h).toMonoidHom = V₁ (ZMod 2) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ V₁ (ZMod 2) := hv
    rw [mem_V₁] at hv'
    change rho h v ∈ V₁ (ZMod 2)
    rw [mem_V₁]
    apply Multiplicative.toAdd.injective
    rw [rho_apply_snd', hv']
    simp
  · intro v hv
    refine ⟨rho h⁻¹ v, ?_, ?_⟩
    · rw [mem_V₁] at hv
      change rho h⁻¹ v ∈ V₁ (ZMod 2)
      rw [mem_V₁]
      apply Multiplicative.toAdd.injective
      rw [rho_apply_snd', hv]
      simp
    · change rho h (rho h⁻¹ v) = v
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem exists_model_th0 {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁' : Subgroup V} (hreal : BinaryNaturalSL H V₁' ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁' ⊓ V₁'.map φ.toMonoidHom = ⊥) (hsup : V₁' ⊔ V₁'.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁' (V₁'.map φ.toMonoidHom)) {θ : MulAut V} (hθH : θ ∈ H)
    (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1) :
    ∃ e : V ≃* PairMod (ZMod 2), H.map (congrHom e) = pairSL (ZMod 2) ∧
      (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) = pairNorm (ZMod 2) ∧
      V₁'.map e.toMonoidHom = V₁ (ZMod 2) ∧
      (congrHom e θ = rho th0 ∨ congrHom e θ = rho (th0 * th0)) := by
  classical
  have hreal' := hreal
  obtain ⟨K, _, _, hK, hR⟩ := hreal'
  obtain ⟨π, hπ⟩ := hR
  have hU : Pair.IsInv H V₁' := fun l hl w hw => hπ.2.2.2.1 ⟨l, hl⟩ w hw
  obtain ⟨e₀, he₀, hN₀⟩ := exists_model hreal hφ hinf hsup hniso
  have hinv : Pair.IsInv (pairSL (ZMod 2)) (V₁'.map e₀.toMonoidHom) := by
    rintro y hy _ ⟨w, hw, rfl⟩
    rw [← he₀] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x w, hU x hx w hw, by
      change e₀ (x w) = e₀ (x (e₀.symm (e₀ w)))
      rw [MulEquiv.symm_apply_apply]⟩
  have hcardV : Nat.card V = 2 ^ 6 := by
    rw [Nat.card_congr e₀.toEquiv]
    exact card_pairMod_two card_zmod_two
  have h12 : V₁'.map e₀.toMonoidHom = V₁ (ZMod 2) ∨ V₁'.map e₀.toMonoidHom = V₂ (ZMod 2) := by
    rcases isInv_eq hinv with h | h | h | h
    · exfalso
      have h1 : V₁' = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        have := (SetLike.ext_iff.mp h (e₀ v)).mp ⟨v, hv, rfl⟩
        rw [Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
        rw [this]
        exact Subgroup.one_mem _
      rw [h1, Subgroup.map_bot, bot_sup_eq] at hsup
      have := Subgroup.card_top (G := V)
      rw [← hsup, Subgroup.card_bot, hcardV] at this
      norm_num at this
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have h1 : V₁' = ⊤ := by
        rw [eq_top_iff]
        intro v _
        obtain ⟨u, hu, hue⟩ := (SetLike.ext_iff.mp h (e₀ v)).mpr (Subgroup.mem_top _)
        rw [← e₀.injective hue]
        exact hu
      rw [h1, Subgroup.map_top_of_surjective _ φ.surjective, inf_top_eq] at hinf
      have := Subgroup.card_top (G := V)
      rw [hinf, Subgroup.card_bot, hcardV] at this
      norm_num at this
  obtain ⟨e₁, he₁, hN₁, hV₁⟩ : ∃ e₁ : V ≃* PairMod (ZMod 2), H.map (congrHom e₁) = pairSL (ZMod 2) ∧
      (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e₁) = pairNorm (ZMod 2) ∧
      V₁'.map e₁.toMonoidHom = V₁ (ZMod 2) := by
    rcases h12 with h | h
    · exact ⟨e₀, he₀, hN₀, h⟩
    · obtain ⟨h1, h2⟩ := model_trans he₀ hN₀ (swapAut_mem_pairNorm (K := ZMod 2))
      refine ⟨e₀.trans (swapAut (ZMod 2)), h1, h2, ?_⟩
      have : V₁'.map (e₀.trans (swapAut (ZMod 2))).toMonoidHom =
          (V₁'.map e₀.toMonoidHom).map (swapAut (ZMod 2)).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      rw [this, h, map_V₂_swapAut]
  have hθe : congrHom e₁ θ ∈ pairSL (ZMod 2) := he₁ ▸ ⟨θ, hθH, rfl⟩
  obtain ⟨g, hg⟩ := exists_rho_of_mem hθe
  have hg3 : g ^ 3 = 1 := rho_injective ((map_pow rho g 3).trans
    ((congrArg (· ^ 3) hg).trans ((map_pow (congrHom e₁) θ 3).symm.trans
      ((congrArg (congrHom e₁) hθ3).trans ((map_one (congrHom e₁)).trans (map_one rho).symm)))))
  have hg1 : g ≠ 1 := fun h1 => hθ1 (congrHom_injective e₁
    ((hg.symm.trans (by rw [h1, map_one])).trans (map_one _).symm))
  obtain ⟨h, hh⟩ := exists_conj_th0 hg3 hg1
  have hrho : rho h ∈ pairNorm (ZMod 2) := pairSL_le_pairNorm (rho_mem_pairSL h)
  obtain ⟨h1, h2⟩ := model_trans he₁ hN₁ hrho
  refine ⟨e₁.trans (rho h), h1, h2, ?_, ?_⟩
  · have : V₁'.map (e₁.trans (rho h)).toMonoidHom =
        (V₁'.map e₁.toMonoidHom).map (rho h).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, hV₁, map_rho_V₁]
  · have hc : congrHom (e₁.trans (rho h)) θ = rho (h * g * h⁻¹) :=
      ((congrArg (congrHom (rho h)) hg.symm).trans (congrHom_eq_conj _ _)).trans (by
        rw [map_mul, map_mul, map_inv])
    rcases hh with hh | hh
    · left
      exact hc.trans (by rw [hh])
    · right
      exact hc.trans (by rw [hh])

end CFSG.Quasithin.H.S77
